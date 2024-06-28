use std::{
  fs::{File, OpenOptions},
  io::{self, Write},
  path::PathBuf,
};

use memmap2::MmapMut;

use super::*;

pub use crate::RewritePolicy;

const CURRENT_VERSION: u16 = 0;
const HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_LEN + MAGIC_VERSION_LEN; // magic text + external magic + magic

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
    len: usize,
    /// Remaining file size.
    remaining: usize,
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
  pub(crate) const fn entry_corrupted(len: usize, remaining: usize) -> Self {
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

  /// Returns `true` if the snapshot should trigger rewrite.
  ///
  /// `remaining` is the remaining size of the append-only log.
  fn should_rewrite(&self, remaining: usize) -> bool;

  /// Insert a new entry.
  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  /// Insert a batch of entries.
  fn insert_batch(&mut self, entries: Vec<Entry<Self::Data>>) -> Result<(), Self::Error>;

  /// Clear the snapshot.
  fn clear(&mut self) -> Result<(), Self::Error>;
}

/// Options for the append only log.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  magic_version: u16,
  capacity: usize,
  sync_on_write: bool,
  rewrite_on_open: bool,
  rewrite_policy: RewritePolicy,
}

impl Options {
  /// Create a new Options with the given file options
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::memmap::Options;
  ///
  /// let opts = Options::new(10_000);
  /// ```
  #[inline]
  pub const fn new(capacity: usize) -> Self {
    Self {
      magic_version: 0,
      sync_on_write: true,
      capacity,
      rewrite_on_open: true,
      rewrite_policy: RewritePolicy::All,
    }
  }

  /// Get the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::memmap::Options;
  ///
  /// let opts = Options::new(10_000);
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
  /// use aol::memmap::Options;
  ///
  /// let opts = Options::new(10_000);
  ///
  /// assert_eq!(opts.sync_on_write(), true);
  /// ```
  #[inline]
  pub const fn sync_on_write(&self) -> bool {
    self.sync_on_write
  }

  /// Get whether check if we should rewrite the append-only log on opening.
  ///
  /// Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::memmap::Options;
  ///
  /// let opts = Options::new(10_000).with_rewrite_on_open(false);
  ///
  /// assert_eq!(opts.rewrite_on_open(), false);
  /// ```
  #[inline]
  pub const fn rewrite_on_open(&self) -> bool {
    self.rewrite_on_open
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
  /// use aol::memmap::Options;
  ///
  /// let opts = Options::new(10_000).with_magic_version(1);
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
  /// use aol::memmap::Options;
  ///
  /// let opts = Options::new(10_000).with_sync_on_write(false);
  ///
  /// assert_eq!(opts.sync_on_write(), false);
  /// ```
  #[inline]
  pub const fn with_sync_on_write(mut self, sync_on_write: bool) -> Self {
    self.sync_on_write = sync_on_write;
    self
  }

  /// Set whether check if we should rewrite the append-only log on opening.
  ///
  /// Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::memmap::Options;
  ///
  /// let opts = Options::new(10_000).with_rewrite_on_open(false);
  /// ```
  #[inline]
  pub const fn with_rewrite_on_open(mut self, rewrite_on_open: bool) -> Self {
    self.rewrite_on_open = rewrite_on_open;
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

#[derive(Debug)]
enum Memmap {
  Map {
    #[allow(dead_code)]
    file: File,
    mmap: memmap2::Mmap,
  },
  MapMut {
    file: File,
    mmap: memmap2::MmapMut,
  },
  None,
}

impl core::ops::Deref for Memmap {
  type Target = [u8];

  #[inline]
  fn deref(&self) -> &Self::Target {
    match self {
      Self::Map { mmap, .. } => mmap,
      Self::MapMut { mmap, .. } => mmap,
      Self::None => unreachable!(),
    }
  }
}

impl Memmap {
  fn append_batch<S: Snapshot, C: Checksumer>(
    &mut self,
    len: usize,
    entries: &[Entry<S::Data>],
    total_encoded_size: usize,
  ) -> Result<usize, Error<S>> {
    match self {
      Memmap::Map { .. } => Err(read_only_error().into()),
      Memmap::MapMut { mmap, .. } => {
        if total_encoded_size > mmap.len() {
          return Err(Error::entry_corrupted(total_encoded_size, mmap.len()));
        }

        if total_encoded_size > mmap.len() - len {
          return Err(Error::entry_corrupted(total_encoded_size, mmap.len() - len));
        }

        let buf = &mut mmap[len..len + total_encoded_size];
        let mut cursor = 0;
        for ent in entries {
          cursor += ent
            .encode::<C>(ent.data.encoded_size(), &mut buf[cursor..])
            .map_err(Error::data)?;
        }

        Ok(len + total_encoded_size)
      }
      Memmap::None => unreachable!(),
    }
  }

  fn append<S: Snapshot, C: Checksumer>(
    &mut self,
    len: usize,
    ent: &Entry<S::Data>,
    data_encoded_len: usize,
  ) -> Result<usize, Error<S>> {
    match self {
      Memmap::Map { .. } => Err(read_only_error().into()),
      Memmap::MapMut { mmap, .. } => {
        let encoded_len = data_encoded_len + FIXED_ENTRY_LEN;

        if encoded_len > mmap.len() - len {
          return Err(Error::entry_corrupted(encoded_len, mmap.len() - len));
        }

        let buf = &mut mmap[len..len + encoded_len];
        ent
          .encode::<C>(data_encoded_len, buf)
          .map_err(Error::data)?;

        Ok(len + encoded_len)
      }
      Memmap::None => unreachable!(),
    }
  }

  fn rewrite<S: Snapshot, C: Checksumer>(
    &mut self,
    filename: &PathBuf,
    rewrite_filename: &PathBuf,
    snapshot: &mut S,
    opts: &Options,
    len: usize,
  ) -> Result<usize, Error<S>> {
    let old = mem::replace(self, Memmap::None);
    match old {
      Memmap::Map { .. } => {
        *self = old;
        Err(read_only_error().into())
      }
      Memmap::MapMut { mmap, file } => {
        let (new_len, this) =
          Self::rewrite_in::<S, C>(mmap, file, filename, rewrite_filename, snapshot, opts, len)?;

        *self = this;
        Ok(new_len)
      }
      Memmap::None => unreachable!(),
    }
  }

  fn rewrite_in<S: Snapshot, C: Checksumer>(
    old_mmap: MmapMut,
    old_file: File,
    filename: &PathBuf,
    rewrite_filename: &PathBuf,
    snapshot: &mut S,
    opts: &Options,
    len: usize,
  ) -> Result<(usize, Self), Error<S>> {
    snapshot.clear().map_err(Error::snapshot)?;

    let mut new_file = OpenOptions::new()
      .create(true)
      .read(true)
      .write(true)
      .truncate(true)
      .open(rewrite_filename)
      .map_err(Error::io)?;
    new_file.set_len(opts.capacity as u64)?;

    // create memory map for fast read and write
    let mut new_mmap = unsafe { memmap2::MmapMut::map_mut(&new_file).map_err(Error::io)? };

    write_header_to_slice(&mut new_mmap, opts.magic_version);

    let mut read_cursor = HEADER_SIZE;
    let mut write_cursor = HEADER_SIZE;

    match opts.rewrite_policy {
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
      if read_cursor + ENTRY_HEADER_SIZE > len {
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

      let remaining = len - read_cursor;
      let needed = FIXED_ENTRY_LEN + encoded_data_len;
      if needed > remaining {
        return Err(Error::entry_corrupted(needed, remaining));
      }

      let (_, ent) =
        Entry::decode::<C>(&old_mmap[read_cursor..read_cursor + needed]).map_err(|e| match e {
          Some(e) => Error::data(e),
          None => Error::ChecksumMismatch,
        })?;
      snapshot.insert(ent).map_err(Error::snapshot)?;
      new_mmap[write_cursor..write_cursor + needed]
        .copy_from_slice(&old_mmap[read_cursor..read_cursor + needed]);
      read_cursor += needed;
      write_cursor += needed;
    }

    new_file.flush().map_err(Error::io)?;
    new_file.sync_all().map_err(Error::io)?;

    drop(old_mmap);
    drop(old_file);
    drop(new_mmap);
    drop(new_file);

    std::fs::rename(rewrite_filename, filename).map_err(Error::io)?;

    let file = OpenOptions::new()
      .create(false)
      .read(true)
      .append(true)
      .open(filename)
      .map_err(Error::io)?;

    let this = Memmap::MapMut {
      mmap: unsafe { memmap2::MmapMut::map_mut(&file).map_err(Error::io)? },
      file,
    };

    Ok((write_cursor, this))
  }
}

/// Generic append-only log implementation based on [`memmap`](memmap2).
///
/// - It is good for:
///   - Any append-only log, if you do not care about pre-allocating the file and you know you data will
///     never larger than the pre-allocating size.
///
/// - Compared to [`memmap::sync::AppendLog`](crate::memmap::sync::AppendLog):
///
///   - Pros:
///     - Support automatic rewrite.
///     - No holes in the file.
///
///   - Cons:
///     - To use it in concurrent environment, `Mutex` or `RwLock` is required.
///     - Do not support in-memory mode.
///     - Cannot be used in `no_std` environment.
///
/// - Compared to [`fs::AppendLog`](crate::fs::AppendLog):
///   
///   - Pros:
///     - Read and write may require extra allocations (if the entry encoded size is larger than `64`) for encoding and decoding.
///     - Each write requires an I/O system call.
///
///   - Cons:
///     - Pre-allocated is required, automatic grow is not supported.
///
// File structure:
//
// ```text
// +----------------------+--------------------------+-----------------------+
// | magic text (4 bytes) | external magic (2 bytes) | magic (2 bytes)       |
// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
// | op (1 bit)           | custom flag (7 bits)     | len (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
// | op (1 bit)           | custom flag (7 bits)     | len (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
// | ...                  | ...                      | ...                   | ...                   | ...                   |
// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
// ```
#[derive(Debug)]
pub struct AppendLog<S, C = Crc32> {
  opts: Options,
  filename: PathBuf,
  rewrite_filename: PathBuf,
  file: Option<Memmap>,
  snapshot: S,
  len: usize,
  capacity: usize,
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

  /// Flushes outstanding memory map modifications to disk.
  ///
  /// When this method returns with a non-error result, all outstanding changes to a file-backed
  /// memory map are guaranteed to be durably stored. The file's metadata (including last
  /// modification timestamp) may not be updated. If you want to make sure file's metadata is
  /// updated, you can call [`sync_all`](Self::sync_all) after this method.
  #[inline]
  pub fn flush(&self) -> io::Result<()> {
    match self.file.as_ref() {
      Some(Memmap::Map { .. }) => Err(read_only_error()),
      Some(Memmap::MapMut { mmap, .. }) => mmap.flush(),
      _ => Ok(()),
    }
  }

  /// Asynchronously flushes outstanding memory map modifications to disk.
  ///
  /// This method initiates flushing modified pages to durable storage, but it will not wait for
  /// the operation to complete before returning. The file's metadata (including last
  /// modification timestamp) may not be updated.
  #[inline]
  pub fn flush_async(&self) -> std::io::Result<()> {
    match self.file.as_ref() {
      Some(Memmap::Map { .. }) => Err(read_only_error()),
      Some(Memmap::MapMut { mmap, .. }) => mmap.flush_async(),
      _ => Ok(()),
    }
  }

  /// Attempts to sync all OS-internal file content and metadata to disk.
  ///
  /// See [`std::fs::File::sync_all`] for more information.
  #[inline]
  pub fn sync_all(&self) -> io::Result<()> {
    match self.file.as_ref() {
      Some(Memmap::Map { .. }) => Err(read_only_error()),
      Some(Memmap::MapMut { file, .. }) => file.sync_all(),
      _ => Ok(()),
    }
  }

  /// Returns the path to the append-only file.
  #[inline]
  pub fn path(&self) -> &std::path::Path {
    &self.filename
  }

  /// Lock the append-only log in exlusive mode.
  ///
  /// See [`fs4::FileExt::lock_exclusive`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn lock_exclusive(&mut self) -> std::io::Result<()> {
    use fs4::FileExt;

    match self.file.as_ref().unwrap() {
      Memmap::Map { file, .. } => file.lock_exclusive(),
      Memmap::MapMut { file, .. } => file.lock_exclusive(),
      _ => unreachable!(),
    }
  }

  /// Lock the append-only log in shared mode.
  ///
  /// See [`fs4::FileExt::lock_shared`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn lock_shared(&mut self) -> std::io::Result<()> {
    use fs4::FileExt;

    match self.file.as_ref().unwrap() {
      Memmap::Map { file, .. } => file.lock_shared(),
      Memmap::MapMut { file, .. } => file.lock_shared(),
      _ => unreachable!(),
    }
  }

  /// Try to lock the append-only log in exlusive mode.
  ///
  /// See [`fs4::FileExt::try_lock_exclusive`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn try_lock_exclusive(&mut self) -> std::io::Result<()> {
    use fs4::FileExt;

    match self.file.as_ref().unwrap() {
      Memmap::Map { file, .. } => file.try_lock_exclusive(),
      Memmap::MapMut { file, .. } => file.try_lock_exclusive(),
      _ => unreachable!(),
    }
  }

  /// Try to lock the append-only log in shared mode.
  ///
  /// See [`fs4::FileExt::try_lock_shared`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn try_lock_shared(&mut self) -> std::io::Result<()> {
    use fs4::FileExt;

    match self.file.as_ref().unwrap() {
      Memmap::Map { file, .. } => file.try_lock_shared(),
      Memmap::MapMut { file, .. } => file.try_lock_shared(),
      _ => unreachable!(),
    }
  }

  /// Unlock the append-only log.
  ///
  /// See [`fs4::FileExt::unlock`] for more information.
  #[cfg(feature = "filelock")]
  #[cfg_attr(docsrs, doc(cfg(feature = "filelock")))]
  pub fn unlock(&mut self) -> std::io::Result<()> {
    use fs4::FileExt;

    match self.file.as_ref().unwrap() {
      Memmap::Map { file, .. } => file.unlock(),
      Memmap::MapMut { file, .. } => file.unlock(),
      _ => unreachable!(),
    }
  }
}

impl<S: Snapshot, C: Checksumer> AppendLog<S, C> {
  /// Open and replay the append only log.
  #[inline]
  pub fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    snapshot_opts: S::Options,
  ) -> Result<Self, Error<S>> {
    let existing = path.as_ref().exists();
    let path = path.as_ref();
    let mut rewrite_path = path.to_path_buf();
    rewrite_path.set_extension("rewrite");
    let file = OpenOptions::new()
      .create(true)
      .read(true)
      .append(true)
      .open(path)
      .map_err(Error::io)?;
    Self::open_in(
      path.to_path_buf(),
      rewrite_path,
      file,
      existing,
      opts,
      snapshot_opts,
      false,
    )
  }

  /// Open and replay the append only log in read-only mode.
  #[inline]
  pub fn map<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    snapshot_opts: S::Options,
  ) -> Result<Self, Error<S>> {
    let existing = path.as_ref().exists();
    let path = path.as_ref();
    let mut rewrite_path = path.to_path_buf();
    rewrite_path.set_extension("rewrite");
    let file = OpenOptions::new()
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
      true,
    )
  }

  /// Append an entry to the append-only file.
  pub fn append(&mut self, ent: Entry<S::Data>) -> Result<(), Error<S>> {
    let data_encoded_len = ent.data.encoded_size();
    if data_encoded_len > self.capacity {
      return Err(Error::entry_corrupted(
        data_encoded_len + FIXED_ENTRY_LEN,
        self.capacity - self.len,
      ));
    }

    if self.snapshot.should_rewrite(self.capacity - self.len)
      || data_encoded_len + FIXED_ENTRY_LEN > self.capacity - self.len
    {
      self.len = Memmap::rewrite::<S, C>(
        self.file.as_mut().unwrap(),
        &self.filename,
        &self.rewrite_filename,
        &mut self.snapshot,
        &self.opts,
        self.len,
      )?;
    }

    self.append_in(ent, data_encoded_len)
  }

  #[inline]
  fn append_in(&mut self, ent: Entry<S::Data>, data_encoded_len: usize) -> Result<(), Error<S>> {
    self.len = self
      .file
      .as_mut()
      .unwrap()
      .append::<S, C>(self.len, &ent, data_encoded_len)?;
    self.snapshot.insert(ent).map_err(Error::snapshot)
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(&mut self, batch: Vec<Entry<S::Data>>) -> Result<(), Error<S>> {
    let total_encoded_size = batch
      .iter()
      .map(|ent| ent.data.encoded_size())
      .fold(batch.len() * FIXED_ENTRY_LEN, |acc, val| acc + val);

    if total_encoded_size > self.capacity {
      return Err(Error::entry_corrupted(
        total_encoded_size,
        self.capacity - self.len,
      ));
    }

    if self.snapshot.should_rewrite(self.capacity - self.len)
      || total_encoded_size > self.capacity - self.len
    {
      self.len = Memmap::rewrite::<S, C>(
        self.file.as_mut().unwrap(),
        &self.filename,
        &self.rewrite_filename,
        &mut self.snapshot,
        &self.opts,
        self.len,
      )?;
    }

    self.append_batch_in(batch, total_encoded_size)
  }

  #[inline]
  fn append_batch_in(
    &mut self,
    batch: Vec<Entry<S::Data>>,
    total_encoded_len: usize,
  ) -> Result<(), Error<S>> {
    self.len =
      self
        .file
        .as_mut()
        .unwrap()
        .append_batch::<S, C>(self.len, &batch, total_encoded_len)?;
    self.snapshot.insert_batch(batch).map_err(Error::snapshot)
  }

  /// Rewrite the append-only log.
  #[inline]
  pub fn rewrite(&mut self) -> Result<(), Error<S>> {
    self.len = Memmap::rewrite::<S, C>(
      self.file.as_mut().unwrap(),
      &self.filename,
      &self.rewrite_filename,
      &mut self.snapshot,
      &self.opts,
      self.len,
    )?;
    Ok(())
  }

  fn open_in(
    filename: PathBuf,
    rewrite_filename: PathBuf,
    file: File,
    existing: bool,
    opts: Options,
    snapshot_opts: S::Options,
    read_only: bool,
  ) -> Result<Self, Error<S>> {
    let Options { magic_version, .. } = opts;

    let size = file.metadata().map_err(Error::io)?.len() as usize;

    if !existing && !read_only {
      if size < opts.capacity {
        file.set_len(opts.capacity as u64).map_err(Error::io)?;
      }

      let mut mmap = unsafe { memmap2::MmapMut::map_mut(&file)? };
      write_header_to_slice(&mut mmap, magic_version);

      return Ok(Self {
        filename,
        rewrite_filename,
        file: Some(Memmap::MapMut { file, mmap }),
        capacity: opts.capacity,
        len: size.max(HEADER_SIZE),
        snapshot: S::new(snapshot_opts).map_err(Error::snapshot)?,
        _checksumer: core::marker::PhantomData,
        opts,
      });
    }

    if size < HEADER_SIZE {
      return Err(Error::CorruptedHeader);
    }

    let mmap = if read_only {
      let mmap = unsafe { memmap2::Mmap::map(&file).map_err(Error::io)? };
      Memmap::Map { file, mmap }
    } else {
      if size < opts.capacity {
        file.set_len(opts.capacity as u64).map_err(Error::io)?;
      }

      let mmap = unsafe { memmap2::MmapMut::map_mut(&file).map_err(Error::io)? };
      Memmap::MapMut { file, mmap }
    };

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

      if header_buf == [0; ENTRY_HEADER_SIZE]
        && mmap[read_cursor + ENTRY_HEADER_SIZE..read_cursor + FIXED_ENTRY_LEN]
          == [0; FIXED_ENTRY_LEN - ENTRY_HEADER_SIZE]
      {
        break;
      }

      let encoded_data_len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
      let remaining = size - read_cursor;
      let needed = FIXED_ENTRY_LEN + encoded_data_len;
      if needed > remaining {
        return Err(Error::entry_corrupted(needed, remaining));
      }
      let (_, ent) =
        Entry::decode::<C>(&mmap[read_cursor..read_cursor + needed]).map_err(|e| match e {
          Some(e) => Error::data(e),
          None => Error::ChecksumMismatch,
        })?;
      snapshot.insert(ent).map_err(Error::snapshot)?;
      read_cursor += needed;
    }

    let mut this = Self {
      filename,
      rewrite_filename,
      file: Some(mmap),
      snapshot,
      capacity: if read_only { size } else { opts.capacity },
      len: size.max(HEADER_SIZE),
      opts,
      _checksumer: core::marker::PhantomData,
    };

    if !read_only && this.snapshot.should_rewrite(size) && this.opts.rewrite_on_open {
      this.len = this.file.as_mut().unwrap().rewrite::<S, C>(
        &this.filename,
        &this.rewrite_filename,
        &mut this.snapshot,
        &this.opts,
        this.len,
      )?;
    }

    Ok(this)
  }
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

#[inline]
fn read_only_error() -> io::Error {
  io::Error::new(io::ErrorKind::PermissionDenied, "append log read-only")
}
