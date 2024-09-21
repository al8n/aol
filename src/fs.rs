use std::{
  fs::{File, OpenOptions},
  io::{self, Write},
  path::PathBuf,
};

use checksum::{BuildChecksumer, Crc32};

use super::*;

pub use super::RewritePolicy;

const CURRENT_VERSION: u16 = 0;
const MAX_INLINE_SIZE: usize = 64;

/// Errors for append-only file.
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
  Record(<S::Record as Record>::Error),

  /// Snapshot error.
  #[error(transparent)]
  Snapshot(S::Error),

  /// I/O error.
  #[error(transparent)]
  IO(#[from] io::Error),
}

impl<S: Snapshot> core::fmt::Debug for Error<S> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    core::fmt::Display::fmt(self, f)
  }
}

impl<S: Snapshot> Error<S> {
  /// Create a new `Error` from an I/O error.
  #[inline]
  pub const fn io(err: io::Error) -> Self {
    Self::IO(err)
  }

  /// Create a new `Error` from a data error.
  #[inline]
  pub const fn data(err: <S::Record as Record>::Error) -> Self {
    Self::Record(err)
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
  type Record: Record;

  /// The options type used to create a new snapshot.
  type Options;

  /// The error type.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// The error type.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Create a new snapshot.
  fn new(opts: Self::Options) -> Result<Self, Self::Error>;

  /// Returns `true` if the snapshot should trigger rewrite.
  ///
  /// `size` is the current size of the append-only log.
  fn should_rewrite(&self, size: u64) -> bool;

  /// Validate the entry, return an error if the entry is invalid.
  fn validate(&self, entry: &Entry<Self::Record>) -> Result<(), Self::Error>;

  /// Validate the batch of entries, return an error if the batch is invalid.
  #[inline]
  fn validate_batch<B: Batch<Self::Record>>(&self, entries: &B) -> Result<(), Self::Error> {
    for entry in entries.iter() {
      self.validate(entry)?;
    }
    Ok(())
  }

  /// Insert a new entry.
  fn insert(&mut self, entry: Entry<Self::Record>) -> Result<(), Self::Error>;

  /// Insert a batch of entries.
  fn insert_batch<B: Batch<Self::Record>>(&mut self, entries: B) -> Result<(), Self::Error> {
    for entry in entries.into_iter() {
      self.insert(entry)?;
    }
    Ok(())
  }

  /// Clear the snapshot.
  fn clear(&mut self) -> Result<(), Self::Error>;
}

/// Options for the append only log.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  magic_version: u16,
  sync_on_write: bool,
  rewrite_policy: RewritePolicy,
  read_only: bool,
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
  /// Create a new Options with the default values.
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
      rewrite_policy: RewritePolicy::All,
      read_only: false,
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

  /// Get whether the append-only log is read-only.
  ///
  /// Default is `false`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.read_only(), false);
  /// ```
  #[inline]
  pub const fn read_only(&self) -> bool {
    self.read_only
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

  /// Get the rewrite policy.
  ///
  /// Default is `RewritePolicy::All`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::{Options, RewritePolicy};
  ///
  /// let opts = Options::new().with_rewrite_policy(RewritePolicy::Skip(100));
  ///
  /// assert_eq!(opts.rewrite_policy(), RewritePolicy::Skip(100));
  /// ```
  #[inline]
  pub const fn rewrite_policy(&self) -> RewritePolicy {
    self.rewrite_policy
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

  /// Set whether the append-only log is read-only.
  ///
  /// Default is `false`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::Options;
  ///
  /// let opts = Options::new().with_read_only(true);
  ///
  /// assert_eq!(opts.read_only(), true);
  /// ```
  #[inline]
  pub const fn with_read_only(mut self, read_only: bool) -> Self {
    self.read_only = read_only;
    self
  }

  /// Set whether flush the data to disk after write.
  ///
  /// Default is `true`.
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

  /// Set the rewrite policy.
  ///
  /// Default is `RewritePolicy::All`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::fs::{Options, RewritePolicy};
  ///
  /// let opts = Options::new().with_rewrite_policy(RewritePolicy::Skip(100));
  /// ```
  #[inline]
  pub const fn with_rewrite_policy(mut self, rewrite_policy: RewritePolicy) -> Self {
    self.rewrite_policy = rewrite_policy;
    self
  }
}

/// Generic append-only log implementation based on [`std::fs::File`].
///
/// - It is good for:
///   - The encoded entry size is smaller than `64`.
///   - Manifest file.
///   - Write is not too frequently.
///
/// - Compared to [`memmap::AppendLog`](crate::memmap::AppendLog):
///   
///   - Pros:
///     - It is growable, do not require pre-allocated.
///
///   - Cons:
///     - Read and write may require extra allocations (if the entry encoded size is larger than `64`) for encoding and decoding.
///     - Each write requires an I/O system call.
#[derive(Debug)]
pub struct AppendLog<S, C = Crc32> {
  opts: Options,
  filename: PathBuf,
  rewrite_filename: PathBuf,
  file: Option<File>,
  len: u64,
  snapshot: S,
  checksumer: C,
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

  /// Returns the path to the append-only file.
  #[inline]
  pub fn path(&self) -> &std::path::Path {
    &self.filename
  }

  /// Sync the underlying file to disk.
  ///
  /// See [`std::fs::File::sync_all`] for more information.
  #[inline]
  pub fn sync_all(&self) -> std::io::Result<()> {
    if let Some(file) = self.file.as_ref() {
      file.sync_all()
    } else {
      Ok(())
    }
  }

  /// Sync the underlying file's data to disk.
  ///
  /// See [`std::fs::File::sync_data`] for more information.
  #[inline]
  pub fn sync_data(&self) -> std::io::Result<()> {
    if let Some(file) = self.file.as_ref() {
      file.sync_data()
    } else {
      Ok(())
    }
  }

  /// Lock the append-only log in exlusive mode.
  ///
  /// See [`fs4::FileExt::lock_exclusive`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;

    self.file.as_ref().unwrap().lock_exclusive()
  }

  /// Lock the append-only log in shared mode.
  ///
  /// See [`fs4::FileExt::lock_shared`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn lock_shared(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;

    self.file.as_ref().unwrap().lock_shared()
  }

  /// Try to lock the append-only log in exlusive mode.
  ///
  /// See [`fs4::FileExt::try_lock_exclusive`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn try_lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;

    self.file.as_ref().unwrap().try_lock_exclusive()
  }

  /// Try to lock the append-only log in shared mode.
  ///
  /// See [`fs4::FileExt::try_lock_shared`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn try_lock_shared(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;

    self.file.as_ref().unwrap().try_lock_shared()
  }

  /// Unlock the append-only log.
  ///
  /// See [`fs4::FileExt::unlock`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn unlock(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;

    self.file.as_ref().unwrap().unlock()
  }
}

impl<S: Snapshot> AppendLog<S> {
  /// Open and replay the append only log.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open<P: AsRef<std::path::Path>>(
    path: P,
    snapshot_opts: S::Options,
    opts: Options,
  ) -> Result<Self, Error<S>> {
    Self::open_with_checksumer(path, snapshot_opts, opts, Crc32::default())
  }
}

impl<S: Snapshot, C: BuildChecksumer> AppendLog<S, C> {
  /// Open and replay the append only log with the given checksumer.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open_with_checksumer<P: AsRef<std::path::Path>>(
    path: P,
    snapshot_opts: S::Options,
    opts: Options,
    cks: C,
  ) -> Result<Self, Error<S>> {
    let existing = path.as_ref().exists();
    let path = path.as_ref();
    let mut rewrite_path = path.to_path_buf();
    rewrite_path.set_extension("rewrite");
    let file = OpenOptions::new()
      .append(true)
      .create(true)
      .read(true)
      .open(path)
      .map_err(Error::io)?;
    Self::open_in(
      path.to_path_buf(),
      rewrite_path,
      file,
      existing,
      opts,
      snapshot_opts,
      cks,
    )
  }

  /// Append an entry to the append-only file.
  ///
  /// Returns the position of the entry in the append-only file.
  #[inline]
  pub fn append(&mut self, entry: Entry<S::Record>) -> Result<(), Error<S>> {
    self.snapshot.validate(&entry).map_err(Error::snapshot)?;

    if self.snapshot.should_rewrite(self.len) {
      self.rewrite()?;
    }

    self.append_in(entry)
  }

  fn append_in(&mut self, entry: Entry<S::Record>) -> Result<(), Error<S>> {
    if self.opts.read_only {
      return Err(read_only_error().into());
    }

    // unwrap is ok, because this log cannot be used in concurrent environment
    append::<S, C>(
      self.file.as_mut().unwrap(),
      &entry,
      self.opts.sync_on_write,
      &self.checksumer,
    )
    .and_then(|len| {
      self.len += len as u64;
      self.snapshot.insert(entry).map_err(Error::snapshot)
    })
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch<B: Batch<S::Record>>(&mut self, batch: B) -> Result<(), Error<S>> {
    if self.opts.read_only {
      return Err(read_only_error().into());
    }

    self
      .snapshot
      .validate_batch(&batch)
      .map_err(Error::snapshot)?;

    if self.snapshot.should_rewrite(self.len) {
      self.rewrite()?;
    }

    self.append_batch_in(batch)
  }

  fn append_batch_in<B: Batch<S::Record>>(&mut self, batch: B) -> Result<(), Error<S>> {
    let total_encoded_size = batch
      .iter()
      .map(|ent| ent.data.encoded_size())
      .fold(batch.len() * FIXED_ENTRY_LEN, |acc, val| acc + val);

    macro_rules! encode_batch {
      ($buf:ident) => {{
        let mut cursor = 0;
        for ent in batch.iter() {
          cursor += ent
            .encode(
              ent.data.encoded_size(),
              &mut $buf[cursor..],
              &self.checksumer,
            )
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
        self.snapshot.insert_batch(batch).map_err(Error::snapshot)?;
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
        self.snapshot.insert_batch(batch).map_err(Error::snapshot)?;
        if self.opts.sync_on_write {
          file.flush().map_err(Error::io)
        } else {
          Ok(())
        }
      })
    }
  }

  /// Rewrite the append-only log.
  pub fn rewrite(&mut self) -> Result<(), Error<S>> {
    if self.opts.read_only {
      return Err(read_only_error().into());
    }

    self.snapshot.clear().map_err(Error::snapshot)?;

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

    match self.opts.rewrite_policy {
      RewritePolicy::All => {}
      RewritePolicy::Skip(n) => {
        let mut skipped = 0;
        loop {
          if skipped == n {
            break;
          }

          if read_cursor + ENTRY_HEADER_SIZE > old_mmap.len() {
            break;
          }

          let mut header_buf = [0; ENTRY_HEADER_SIZE];
          header_buf.copy_from_slice(&old_mmap[read_cursor..read_cursor + ENTRY_HEADER_SIZE]);

          let len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
          let flag = EntryFlags {
            value: header_buf[0],
          };

          if !flag.is_deletion() {
            skipped += 1;
          }

          read_cursor += FIXED_ENTRY_LEN + len;
        }
      }
    }

    loop {
      if read_cursor + ENTRY_HEADER_SIZE > old_mmap.len() {
        break;
      }

      let mut header_buf = [0; ENTRY_HEADER_SIZE];
      header_buf.copy_from_slice(&old_mmap[read_cursor..read_cursor + ENTRY_HEADER_SIZE]);

      let encoded_data_len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
      let flag = EntryFlags {
        value: header_buf[0],
      };
      if flag.is_deletion() {
        read_cursor += FIXED_ENTRY_LEN + encoded_data_len;
        continue;
      }

      let entry_size = FIXED_ENTRY_LEN + encoded_data_len;

      let remaining = self.len - read_cursor as u64;
      let needed = FIXED_ENTRY_LEN + encoded_data_len;
      if needed as u64 > remaining {
        return Err(Error::entry_corrupted(needed as u32, remaining as u32));
      }

      let (_readed, ent) = Entry::decode(
        &old_mmap[read_cursor..read_cursor + entry_size],
        &self.checksumer,
      )
      .map_err(|e| match e {
        Some(e) => Error::data(e),
        None => Error::ChecksumMismatch,
      })?;
      self.snapshot.insert(ent).map_err(Error::snapshot)?;
      new_mmap[write_cursor..write_cursor + needed]
        .copy_from_slice(&old_mmap[read_cursor..read_cursor + needed]);
      read_cursor += needed;
      write_cursor += needed;
    }

    new_file.flush().map_err(Error::io)?;
    drop(new_mmap);
    new_file.set_len(write_cursor as u64).map_err(Error::io)?;
    new_file.sync_all().map_err(Error::io)?;

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

  fn open_in(
    filename: PathBuf,
    rewrite_filename: PathBuf,
    mut file: File,
    existing: bool,
    opts: Options,
    snapshot_opts: S::Options,
    cks: C,
  ) -> Result<Self, Error<S>> {
    let Options { magic_version, .. } = opts;

    let size = file.metadata().map_err(Error::io)?.len();

    if !existing || size == 0 {
      Self::write_header(&mut file, magic_version)?;

      return Ok(Self {
        filename,
        rewrite_filename,
        file: Some(file),
        snapshot: S::new(snapshot_opts).map_err(Error::snapshot)?,
        checksumer: cks,
        opts,
        len: HEADER_SIZE as u64,
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
      let entry_size = FIXED_ENTRY_LEN + len;
      let remaining = size - read_cursor as u64;
      let needed = FIXED_ENTRY_LEN + len;
      if needed as u64 > remaining {
        return Err(Error::entry_corrupted(needed as u32, remaining as u32));
      }

      let (_, ent) =
        Entry::decode(&mmap[read_cursor..read_cursor + entry_size], &cks).map_err(|e| match e {
          Some(e) => Error::data(e),
          None => Error::ChecksumMismatch,
        })?;
      snapshot.insert(ent).map_err(Error::snapshot)?;
      read_cursor += needed;
    }

    drop(mmap);

    let mut this = Self {
      filename,
      rewrite_filename,
      file: Some(file),
      snapshot,
      len: size,
      checksumer: cks,
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
    bytes[..HEADER_SIZE].copy_from_slice(&buf);
  }
}

#[inline]
fn append<S: Snapshot, C: BuildChecksumer>(
  file: &mut File,
  ent: &Entry<S::Record>,
  sync: bool,
  cks: &C,
) -> Result<usize, Error<S>> {
  let encoded_len = ent.data.encoded_size();
  if encoded_len + FIXED_ENTRY_LEN > MAX_INLINE_SIZE {
    let mut buf = std::vec![0; encoded_len + FIXED_ENTRY_LEN];
    ent
      .encode(encoded_len, &mut buf, cks)
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
    let buf = &mut buf[..encoded_len + FIXED_ENTRY_LEN];
    ent.encode(encoded_len, buf, cks).map_err(Error::data)?;
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
