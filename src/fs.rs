use std::{
  fs::{File, OpenOptions},
  io::{self, BufReader, Read, Write},
  path::PathBuf,
};

use super::*;

const CURRENT_VERSION: u16 = 0;

/// Errors for append-only file.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error<M: Manifest> {
  /// Manifest has bad magic.
  #[error("append-only has bad magic text")]
  BadMagicText,
  /// Cannot open append-only because the external magic doesn't match.
  #[error("cannot open append-only because the external magic doesn't match. expected {expected}, found {found}")]
  BadExternalMagic {
    /// Expected external magic.
    expected: u16,
    /// Found external magic.
    found: u16,
  },
  /// Cannot open append-only because the magic doesn't match.
  #[error(
    "cannot open append-only because the magic doesn't match. expected {expected}, found {found}"
  )]
  BadMagic {
    /// Expected magic.
    expected: u16,
    /// Found magic.
    found: u16,
  },

  /// Corrupted append-only file: entry checksum mismatch.
  #[error("entry checksum mismatch")]
  ChecksumMismatch,

  /// Corrupted append-only file: not enough bytes to decode append-only entry.
  #[error("entry data len {len} is greater than the remaining file size {remaining}, append-only file might be corrupted")]
  EntryTooLarge {
    /// Entry data len.
    len: u32,
    /// Remaining file size.
    remaining: u32,
  },

  /// Encode/decode data error.
  #[error(transparent)]
  Data(<M::Data as Data>::Error),

  /// Manifest error.
  #[error(transparent)]
  Manifest(M::Error),

  /// I/O error.
  #[error(transparent)]
  IO(#[from] io::Error),
}

impl<M: Manifest> Error<M> {
  /// Create a new `Error` from an I/O error.
  #[inline]
  pub const fn io(err: io::Error) -> Self {
    Self::IO(err)
  }

  /// Create a new `Error` from a data error.
  #[inline]
  pub const fn data(err: <M::Data as Data>::Error) -> Self {
    Self::Data(err)
  }

  /// Create a new `Error` from an unknown append-only event.
  #[inline]
  pub const fn manifest(err: M::Error) -> Self {
    Self::Manifest(err)
  }

  /// Create a new `Corrupted` error.
  #[inline]
  pub(crate) const fn entry_corrupted(len: u32, remaining: u32) -> Self {
    Self::EntryTooLarge { len, remaining }
  }
}

/// The manifest trait, manifest should contains the information about the append-only log,
/// which is the minimum memory representation of the append-only log, which can be used to
/// rewrite the append-only log.
pub trait Manifest: Sized {
  /// The data type.
  type Data: Data;

  /// The options type used to create a new manifest.
  type Options: Clone;

  /// The error type.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// The error type.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Open a new manifest.
  fn open(opts: Self::Options) -> Result<Self, Self::Error>;

  /// Returns the options.
  fn options(&self) -> &Self::Options;

  /// Returns `true` if the manifest should trigger rewrite.
  ///
  /// `size` is the current size of the append-only log.
  fn should_rewrite(&self, size: u64) -> bool;

  /// Insert a new entry.
  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  /// Insert a batch of entries.
  fn insert_batch(
    &mut self,
    entries: Vec<Entry<Self::Data>>,
  ) -> Result<(), Self::Error>;

  /// Iterate over the entries.
  fn into_iter(self) -> impl Iterator<Item = Entry<Self::Data>>;
}

/// Options for the manifest file.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  magic_version: u16,
  sync_on_write: bool,
}

impl Default for Options {
  /// Returns the default options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::default();
  /// ```
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Options {
  /// Create a new Options with the given file options
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::new();
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      magic_version: 0,
      sync_on_write: true,
    }
  }

  /// Get the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.magic_version(), 0);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Get whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.sync_on_write(), true);
  /// ```
  #[inline]
  pub const fn sync_on_write(&self) -> bool {
    self.sync_on_write
  }

  /// Set the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Set whether flush the data to disk after write.
  ///
  ///  Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::new().with_sync_on_write(false);
  ///
  /// assert_eq!(opts.sync_on_write(), false);
  /// ```
  #[inline]
  pub const fn with_sync_on_write(mut self, sync_on_write: bool) -> Self {
    self.sync_on_write = sync_on_write;
    self
  }
}

/// Generic append-only log implementation based on [`std::fs::File`].
///
/// Compared to [`arena::AppendLog`](crate::arena::AppendLog):
/// 
/// - Pros:
///   - It is growable, do not require pre-allocated.
///   - Support automatic rewrite.
/// 
/// - Cons:
///   - Read and write may require extra allocations for encoding and decoding.
///   - Each write requires an I/O system call.
///   - To use it in concurrent environment, `Mutex` or `RwLock` is required.
///   - Do not support in-memory mode.
///   - Cannot be used in `no_std` environment.
/// 
/// It is good for:
/// - Append-only log which size cannot reach `4GB`.
/// - End-users who can manage the grow and rewrite by themselves.
/// 
/// File structure:
///
/// ```text
/// +----------------------+--------------------------+-----------------------+
/// | magic text (4 bytes) | external magic (2 bytes) | magic (2 bytes)       |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | op (1 bit)           | custom flag (7 bits)     | len (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | op (1 bit)           | custom flag (7 bits)     | len (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | ...                  | ...                      | ...                   | ...                   | ...                   |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// ```
#[derive(Debug)]
pub struct AppendLog<M, C = Crc32> {
  opts: Options,
  filename: PathBuf,
  rewrite_filename: PathBuf,
  file: Option<File>,
  len: u64,
  manifest: M,
  _checksumer: core::marker::PhantomData<C>,
}

impl<M, C> AppendLog<M, C> {
  /// Returns the options of the manifest file.
  #[inline]
  pub const fn options(&self) -> &Options {
    &self.opts
  }

  /// Returns the current manifest.
  #[inline]
  pub const fn manifest(&self) -> &M {
    &self.manifest
  }
}

impl<M: Manifest, C> AppendLog<M, C> {
  /// Flush the manifest file.
  #[inline]
  pub fn flush(&mut self) -> Result<(), Error<M>> {
    // unwrap is ok, because this log cannot be used in concurrent environment
    self.file.as_mut().unwrap().flush().map_err(Error::io)
  }

  /// Sync the manifest file.
  #[inline]
  pub fn sync_all(&self) -> Result<(), Error<M>> {
    // unwrap is ok, because this log cannot be used in concurrent environment
    self.file.as_ref().unwrap().sync_all().map_err(Error::io)
  }
}

impl<M: Manifest, C: Checksumer> AppendLog<M, C> {
  /// Open and replay the manifest file.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open<P: AsRef<std::path::Path>>(
    path: P,
    manifest_opts: M::Options,
    file_opts: OpenOptions,
    opts: Options,
  ) -> Result<Self, Error<M>> {
    let existing = path.as_ref().exists();
    let path = path.as_ref();
    let mut rewrite_path = path.to_path_buf();
    rewrite_path.set_extension("rewrite");
    let file = file_opts.open(path).map_err(Error::io)?;
    Self::open_in(
      path.to_path_buf(),
      rewrite_path,
      file,
      existing,
      opts,
      manifest_opts,
    )
  }

  /// Returns the path to the append-only file.
  #[inline]
  pub fn path(&self) -> &std::path::Path {
    &self.filename
  }

  /// Append an entry to the append-only file.
  #[inline]
  pub fn append(&mut self, ent: Entry<M::Data>) -> Result<(), Error<M>> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(&mut self, entries: Vec<Entry<M::Data>>) -> Result<(), Error<M>> {
    if self.manifest.should_rewrite(self.len) {
      self.rewrite()?;
    }

    let total_encoded_size = entries
      .iter()
      .map(|ent| ent.data.encoded_size())
      .sum::<usize>()
      + entries.len() * FIXED_MANIFEST_ENTRY_SIZE;

    macro_rules! encode_batch {
      ($buf:ident) => {{
        let mut cursor = 0;
        for ent in &entries {
          cursor += ent
            .encode::<C>(ent.data.encoded_size(), &mut $buf[cursor..])
            .map_err(Error::data)?;
        }
      }};
    }

    // unwrap is ok, because this log cannot be used in concurrent environment
    let file = self.file.as_mut().unwrap();

    if total_encoded_size > MAX_INLINE_SIZE {
      let mut buf = std::vec![0; total_encoded_size];
      encode_batch!(buf);
      file
        .write_all(&buf)
        .map_err(Error::io)
        .and_then(|_| {
          self.len += total_encoded_size as u64;
          self.manifest.insert_batch(entries).map_err(Error::manifest)?;
          if self.opts.sync_on_write {
            file.flush().map_err(Error::io)
          } else {
            Ok(())
          }
        })
    } else {
      let mut buf = [0; MAX_INLINE_SIZE];
      let buf = &mut buf[..total_encoded_size];
      encode_batch!(buf);

      file
        .write_all(buf)
        .map_err(Error::io)
        .and_then(|_| {
          self.len += total_encoded_size as u64;
          self.manifest.insert_batch(entries).map_err(Error::manifest)?;
          if self.opts.sync_on_write {
            file.flush().map_err(Error::io)
          } else {
            Ok(())
          }
        })
    }
  }

  fn open_in(
    filename: PathBuf,
    rewrite_filename: PathBuf,
    mut file: File,
    existing: bool,
    opts: Options,
    manifest_opts: M::Options,
  ) -> Result<Self, Error<M>> {
    let Options { magic_version, .. } = opts;

    if !existing {
      Self::write_header(&mut file, magic_version)?;

      let len = file.metadata().map_err(Error::io)?.len();
      return Ok(Self {
        filename,
        rewrite_filename,
        file: Some(file),
        manifest: M::open(manifest_opts).map_err(Error::manifest)?,
        _checksumer: core::marker::PhantomData,
        opts,
        len,
      });
    }

    let size = file.metadata().map_err(Error::io)?.len();

    let mut header = [0; MANIFEST_HEADER_SIZE];

    let mut file = BufReader::new(file);
    file.read_exact(&mut header).map_err(Error::io)?;

    if &header[..MAGIC_TEXT_LEN] != MAGIC_TEXT {
      return Err(Error::BadMagicText);
    }

    let external = u16::from_le_bytes(
      header[MAGIC_TEXT_LEN..MAGIC_TEXT_LEN + MAGIC_VERSION_LEN]
        .try_into()
        .unwrap(),
    );
    if external != magic_version {
      return Err(Error::BadExternalMagic {
        expected: magic_version,
        found: external,
      });
    }

    let version = u16::from_le_bytes(
      header[MAGIC_TEXT_LEN + MAGIC_VERSION_LEN..MANIFEST_HEADER_SIZE]
        .try_into()
        .unwrap(),
    );
    if version != CURRENT_VERSION {
      return Err(Error::BadMagic {
        expected: CURRENT_VERSION,
        found: version,
      });
    }

    let mut manifest = M::open(manifest_opts).map_err(Error::manifest)?;

    let mut curosr = 0;
    loop {
      let mut header_buf = [0; ENTRY_HEADER_SIZE];
      match file.read_exact(&mut header_buf) {
        Ok(()) => {
          curosr += ENTRY_HEADER_SIZE;

          let len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
          let entry_size = FIXED_MANIFEST_ENTRY_SIZE + len;

          let remaining = size - MANIFEST_HEADER_SIZE as u64 - curosr as u64;
          let needed = len + CHECKSUM_SIZE;
          if needed as u64 > remaining {
            return Err(Error::entry_corrupted(needed as u32, remaining as u32));
          }

          if entry_size > MAX_INLINE_SIZE {
            let mut buf = std::vec![0; entry_size];
            buf[..ENTRY_HEADER_SIZE].copy_from_slice(&header_buf);
            file
              .read_exact(&mut buf[ENTRY_HEADER_SIZE..])
              .map_err(Error::io)?;
            let ent = Entry::decode::<C>(&buf).map_err(|e| match e {
              Some(e) => Error::data(e),
              None => Error::ChecksumMismatch,
            })?;
            manifest.insert(ent).map_err(Error::manifest)?;
          } else {
            let mut buf = [0; MAX_INLINE_SIZE];
            buf[..ENTRY_HEADER_SIZE].copy_from_slice(&header_buf);
            let buf = &mut buf[ENTRY_HEADER_SIZE..ENTRY_HEADER_SIZE + len + CHECKSUM_SIZE];
            file.read_exact(buf).map_err(Error::io)?;
            let ent = Entry::decode::<C>(buf).map_err(|e| match e {
              Some(e) => Error::data(e),
              None => Error::ChecksumMismatch,
            })?;
            manifest.insert(ent).map_err(Error::manifest)?;
          }
          curosr += len + CHECKSUM_SIZE;
        }
        Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
        Err(e) => return Err(Error::io(e)),
      }
    }

    let mut this = Self {
      filename,
      rewrite_filename,
      file: Some(file.into_inner()),
      manifest,
      len: size,
      _checksumer: core::marker::PhantomData,
      opts,
    };

    if this.manifest.should_rewrite(this.len) {
      return this.rewrite().map(|_| this);
    }

    Ok(this)
  }

  #[inline]
  fn write_header(file: &mut File, magic_version: u16) -> Result<(), Error<M>> {
    let mut buf = [0; MANIFEST_HEADER_SIZE];
    let mut cur = 0;
    buf[..MAGIC_TEXT_LEN].copy_from_slice(MAGIC_TEXT);
    cur += MAGIC_TEXT_LEN;
    buf[cur..cur + MAGIC_VERSION_LEN].copy_from_slice(&magic_version.to_le_bytes());
    cur += MAGIC_VERSION_LEN;
    buf[cur..MANIFEST_HEADER_SIZE].copy_from_slice(&CURRENT_VERSION.to_le_bytes());
    file.write_all(&buf).map_err(Error::io)?;
    file.flush().map_err(Error::io)
  }

  #[inline]
  fn append_in(&mut self, entry: Entry<M::Data>) -> Result<(), Error<M>> {
    if self.manifest.should_rewrite(self.len) {
      self.rewrite()?;
    }

    // unwrap is ok, because this log cannot be used in concurrent environment
    append::<M, C>(self.file.as_mut().unwrap(), &entry, self.opts.sync_on_write).and_then(|len| {
      self.len += len as u64;
      self.manifest.insert(entry).map_err(Error::manifest)
    })
  }

  fn rewrite(&mut self) -> Result<(), Error<M>> {
    thread_local! {
      static REWRITE_FILE_NAME: core::cell::RefCell<Option<std::path::PathBuf>> = core::cell::RefCell::new(None);
    }

    let manifest_opts = self.manifest.options().clone();
    let manifest = M::open(manifest_opts).map_err(Error::manifest)?;
    let old = mem::replace(&mut self.manifest, manifest);

    let _ = self.file.take().unwrap();

    let mut new_file = OpenOptions::new()
      .create(true)
      .read(true)
      .write(true)
      .truncate(true)
      .open(&self.rewrite_filename)
      .map_err(Error::io)?;

    Self::write_header(&mut new_file, self.opts.magic_version)?;

    for ent in old.into_iter() {
      if ent.flag.is_creation() {
        append::<M, C>(&mut new_file, &ent, false)
          .and_then(|_| self.manifest.insert(ent).map_err(Error::manifest))?;
      }
    }

    new_file.flush().map_err(Error::io)?;
    new_file.sync_all().map_err(Error::io)?;
    drop(new_file);
    std::fs::rename(&self.rewrite_filename, &self.filename).map_err(Error::io)?;

    let file = OpenOptions::new()
      .create(false)
      .read(true)
      .append(true)
      .open(&self.filename)
      .map_err(Error::io)?;
    self.file = Some(file);
    let len = self
      .file
      .as_ref()
      .unwrap()
      .metadata()
      .map_err(Error::io)?
      .len();
    self.len = len;
    Ok(())
  }
}

fn append<M: Manifest, C: Checksumer>(
  file: &mut File,
  ent: &Entry<M::Data>,
  sync: bool,
) -> Result<usize, Error<M>> {
  let encoded_len = ent.data.encoded_size();
  if encoded_len + FIXED_MANIFEST_ENTRY_SIZE > MAX_INLINE_SIZE {
    let mut buf = Vec::with_capacity(encoded_len + FIXED_MANIFEST_ENTRY_SIZE);
    ent
      .encode::<C>(encoded_len, &mut buf)
      .map_err(Error::data)?;
    let len = buf.len();
    file
      .write_all(&buf)
      .and_then(|_| {
        if sync {
          file.flush().map(|_| len)
        } else {
          Ok(len)
        }
      })
      .map_err(Error::io)
  } else {
    let mut buf = [0; MAX_INLINE_SIZE];
    let buf = &mut buf[..encoded_len + FIXED_MANIFEST_ENTRY_SIZE];
    ent.encode::<C>(encoded_len, buf).map_err(Error::data)?;
    let len = buf.len();
    file
      .write_all(buf)
      .and_then(|_| {
        if sync {
          file.flush().map(|_| len)
        } else {
          Ok(len)
        }
      })
      .map_err(Error::io)
  }
}
