use std::{
  fs::{File, OpenOptions},
  io::{self, Write},
  path::PathBuf,
};

use super::*;

const CURRENT_VERSION: u16 = 0;
const HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_LEN + MAGIC_VERSION_LEN; // magic text + external magic + magic

/// Errors for append-only file.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error<S: Snapshot> {
  /// Missing corrupted append-only log header.
  #[error("missing append-only log header, log may be corrupted")]
  CorruptedHeader,

  /// Snapshot has bad magic.
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
  Data(<S::Data as Data>::Error),

  /// Snapshot error.
  #[error(transparent)]
  Snapshot(S::Error),

  /// I/O error.
  #[error(transparent)]
  IO(#[from] io::Error),
}

impl<S: Snapshot> Error<S> {
  /// Create a new `Error` from an I/O error.
  #[inline]
  pub const fn io(err: io::Error) -> Self {
    Self::IO(err)
  }

  /// Create a new `Error` from a data error.
  #[inline]
  pub const fn data(err: <S::Data as Data>::Error) -> Self {
    Self::Data(err)
  }

  /// Create a new `Error` from an unknown append-only event.
  #[inline]
  pub const fn snapshot(err: S::Error) -> Self {
    Self::Snapshot(err)
  }

  /// Create a new `Corrupted` error.
  #[inline]
  pub(crate) const fn entry_corrupted(len: u32, remaining: u32) -> Self {
    Self::EntryTooLarge { len, remaining }
  }
}

/// The snapshot trait, snapshot may contain some in-memory information about the append-only log.
pub trait Snapshot: Sized {
  /// The data type.
  type Data: Data;

  /// The options type used to create a new snapshot.
  type Options: Clone;

  /// The error type.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// The error type.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Create a new snapshot.
  fn new(opts: Self::Options) -> Result<Self, Self::Error>;

  /// Returns the options.
  fn options(&self) -> &Self::Options;

  /// Returns `true` if the snapshot should trigger rewrite.
  ///
  /// `size` is the current size of the append-only log.
  fn should_rewrite(&self, size: u64) -> bool;

  /// Insert a new entry.
  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  /// Insert a batch of entries.
  fn insert_batch(&mut self, entries: Vec<Entry<Self::Data>>) -> Result<(), Self::Error>;
}

/// Options for the append only log.
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
///   - No holes in the file.
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
pub struct AppendLog<S, C = Crc32> {
  opts: Options,
  filename: PathBuf,
  rewrite_filename: PathBuf,
  file: Option<File>,
  len: u64,
  snapshot: S,
  _checksumer: core::marker::PhantomData<C>,
}

impl<S, C> AppendLog<S, C> {
  /// Returns the options of the append only log.
  #[inline]
  pub const fn options(&self) -> &Options {
    &self.opts
  }

  /// Returns the current snapshot.
  #[inline]
  pub const fn snapshot(&self) -> &S {
    &self.snapshot
  }
}

impl<S: Snapshot, C> AppendLog<S, C> {
  /// Flush the append only log.
  #[inline]
  pub fn flush(&mut self) -> Result<(), Error<S>> {
    // unwrap is ok, because this log cannot be used in concurrent environment
    self.file.as_mut().unwrap().flush().map_err(Error::io)
  }

  /// Sync the append only log.
  #[inline]
  pub fn sync_all(&self) -> Result<(), Error<S>> {
    // unwrap is ok, because this log cannot be used in concurrent environment
    self.file.as_ref().unwrap().sync_all().map_err(Error::io)
  }
}

impl<S: Snapshot, C: Checksumer> AppendLog<S, C> {
  /// Open and replay the append only log.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open<P: AsRef<std::path::Path>>(
    path: P,
    snapshot_opts: S::Options,
    file_opts: OpenOptions,
    opts: Options,
  ) -> Result<Self, Error<S>> {
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
      snapshot_opts,
    )
  }

  /// Returns the path to the append-only file.
  #[inline]
  pub fn path(&self) -> &std::path::Path {
    &self.filename
  }

  /// Append an entry to the append-only file.
  #[inline]
  pub fn append(&mut self, ent: Entry<S::Data>) -> Result<(), Error<S>> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(&mut self, entries: Vec<Entry<S::Data>>) -> Result<(), Error<S>> {
    if self.snapshot.should_rewrite(self.len) {
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
      file.write_all(&buf).map_err(Error::io).and_then(|_| {
        self.len += total_encoded_size as u64;
        self
          .snapshot
          .insert_batch(entries)
          .map_err(Error::snapshot)?;
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

      file.write_all(buf).map_err(Error::io).and_then(|_| {
        self.len += total_encoded_size as u64;
        self
          .snapshot
          .insert_batch(entries)
          .map_err(Error::snapshot)?;
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
    snapshot_opts: S::Options,
  ) -> Result<Self, Error<S>> {
    let Options { magic_version, .. } = opts;

    let size = file.metadata().map_err(Error::io)?.len();

    if !existing || size == 0 {
      Self::write_header(&mut file, magic_version)?;

      let len = file.metadata().map_err(Error::io)?.len();
      return Ok(Self {
        filename,
        rewrite_filename,
        file: Some(file),
        snapshot: S::new(snapshot_opts).map_err(Error::snapshot)?,
        _checksumer: core::marker::PhantomData,
        opts,
        len,
      });
    }

    if size < HEADER_SIZE as u64 {
      return Err(Error::CorruptedHeader);
    }

    let mmap = unsafe { memmap2::Mmap::map(&file)? };

    if &mmap[..MAGIC_TEXT_LEN] != MAGIC_TEXT {
      return Err(Error::BadMagicText);
    }

    let external = u16::from_le_bytes(
      mmap[MAGIC_TEXT_LEN..MAGIC_TEXT_LEN + MAGIC_VERSION_LEN]
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
      mmap[MAGIC_TEXT_LEN + MAGIC_VERSION_LEN..HEADER_SIZE]
        .try_into()
        .unwrap(),
    );
    if version != CURRENT_VERSION {
      return Err(Error::BadMagic {
        expected: CURRENT_VERSION,
        found: version,
      });
    }

    let mut snapshot = S::new(snapshot_opts).map_err(Error::snapshot)?;

    let mut read_cursor = HEADER_SIZE;

    loop {
      if read_cursor + ENTRY_HEADER_SIZE > mmap.len() {
        break;
      }

      let mut header_buf = [0; ENTRY_HEADER_SIZE];
      header_buf.copy_from_slice(&mmap[read_cursor..read_cursor + ENTRY_HEADER_SIZE]);

      let len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
      let entry_size = FIXED_MANIFEST_ENTRY_SIZE + len;

      let remaining = size - HEADER_SIZE as u64 - read_cursor as u64;
      let needed = FIXED_MANIFEST_ENTRY_SIZE + len;
      if needed as u64 > remaining {
        return Err(Error::entry_corrupted(needed as u32, remaining as u32));
      }

      let (readed, ent) = Entry::decode::<C>(&mmap[read_cursor..read_cursor + entry_size])
        .map_err(|e| match e {
          Some(e) => Error::data(e),
          None => Error::ChecksumMismatch,
        })?;
      snapshot.insert(ent).map_err(Error::snapshot)?;
      read_cursor += readed;
    }

    drop(mmap);

    let mut this = Self {
      filename,
      rewrite_filename,
      file: Some(file),
      snapshot,
      len: size,
      _checksumer: core::marker::PhantomData,
      opts,
    };

    if this.snapshot.should_rewrite(this.len) {
      return this.rewrite().map(|_| this);
    }

    Ok(this)
  }

  #[inline]
  fn write_header(file: &mut File, magic_version: u16) -> Result<(), Error<S>> {
    let mut buf = [0; HEADER_SIZE];
    let mut cur = 0;
    buf[..MAGIC_TEXT_LEN].copy_from_slice(MAGIC_TEXT);
    cur += MAGIC_TEXT_LEN;
    buf[cur..cur + MAGIC_VERSION_LEN].copy_from_slice(&magic_version.to_le_bytes());
    cur += MAGIC_VERSION_LEN;
    buf[cur..HEADER_SIZE].copy_from_slice(&CURRENT_VERSION.to_le_bytes());
    file.write_all(&buf).map_err(Error::io)?;
    file.flush().map_err(Error::io)
  }

  #[inline]
  fn write_header_to_slice(bytes: &mut [u8], magic_version: u16) {
    let mut buf = [0; HEADER_SIZE];
    let mut cur = 0;
    buf[..MAGIC_TEXT_LEN].copy_from_slice(MAGIC_TEXT);
    cur += MAGIC_TEXT_LEN;
    buf[cur..cur + MAGIC_VERSION_LEN].copy_from_slice(&magic_version.to_le_bytes());
    cur += MAGIC_VERSION_LEN;
    buf[cur..HEADER_SIZE].copy_from_slice(&CURRENT_VERSION.to_le_bytes());
    bytes.copy_from_slice(&buf);
  }

  #[inline]
  fn append_in(&mut self, entry: Entry<S::Data>) -> Result<(), Error<S>> {
    if self.snapshot.should_rewrite(self.len) {
      self.rewrite()?;
    }

    // unwrap is ok, because this log cannot be used in concurrent environment
    append::<S, C>(self.file.as_mut().unwrap(), &entry, self.opts.sync_on_write).and_then(|len| {
      self.len += len as u64;
      self.snapshot.insert(entry).map_err(Error::snapshot)
    })
  }

  fn rewrite(&mut self) -> Result<(), Error<S>> {
    thread_local! {
      static REWRITE_FILE_NAME: core::cell::RefCell<Option<std::path::PathBuf>> = core::cell::RefCell::new(None);
    }

    let snapshot_opts = self.snapshot.options().clone();
    let snapshot = S::new(snapshot_opts).map_err(Error::snapshot)?;
    let _ = mem::replace(&mut self.snapshot, snapshot);

    let old_file = self.file.take().unwrap();

    let mut new_file = OpenOptions::new()
      .create(true)
      .read(true)
      .write(true)
      .truncate(true)
      .open(&self.rewrite_filename)
      .map_err(Error::io)?;
    new_file.set_len(self.len)?;

    // create memory map for fast read and write
    let (mut new_mmap, old_mmap) = unsafe {
      (
        memmap2::MmapMut::map_mut(&new_file).map_err(Error::io)?,
        memmap2::Mmap::map(&old_file).map_err(Error::io)?,
      )
    };

    Self::write_header_to_slice(&mut new_mmap, self.opts.magic_version);

    let mut read_cursor = HEADER_SIZE;
    let mut write_cursor = HEADER_SIZE;

    loop {
      if read_cursor + ENTRY_HEADER_SIZE > old_mmap.len() {
        break;
      }

      let mut header_buf = [0; ENTRY_HEADER_SIZE];
      header_buf.copy_from_slice(&old_mmap[read_cursor..read_cursor + ENTRY_HEADER_SIZE]);

      let len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
      let flag = EntryFlags {
        value: header_buf[0],
      };
      if flag.is_deletion() {
        read_cursor += FIXED_MANIFEST_ENTRY_SIZE + len;
        continue;
      }

      let entry_size = FIXED_MANIFEST_ENTRY_SIZE + len;

      let remaining = self.len - HEADER_SIZE as u64 - read_cursor as u64;
      let needed = FIXED_MANIFEST_ENTRY_SIZE + len;
      if needed as u64 > remaining {
        return Err(Error::entry_corrupted(needed as u32, remaining as u32));
      }

      let (readed, ent) = Entry::decode::<C>(&old_mmap[read_cursor..read_cursor + entry_size])
        .map_err(|e| match e {
          Some(e) => Error::data(e),
          None => Error::ChecksumMismatch,
        })?;
      self.snapshot.insert(ent).map_err(Error::snapshot)?;
      new_mmap[write_cursor..write_cursor + readed]
        .copy_from_slice(&old_mmap[read_cursor..read_cursor + readed]);
      read_cursor += readed;
      write_cursor += readed;
    }

    new_file.flush().map_err(Error::io)?;
    new_file.sync_all().map_err(Error::io)?;
    drop(new_mmap);
    drop(old_mmap);
    drop(new_file);
    drop(old_file);

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

fn append<S: Snapshot, C: Checksumer>(
  file: &mut File,
  ent: &Entry<S::Data>,
  sync: bool,
) -> Result<usize, Error<S>> {
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
