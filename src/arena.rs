pub use rarena_allocator::Error as AllocatorError;
use rarena_allocator::*;

use core::slice;
use std::path::PathBuf;

use super::*;

const CURRENT_VERSION: u16 = 0;
/// Magic text for the manifest file, this will never be changed.
const MAGIC_TEXT: &[u8] = b"al8n";
const MAGIC_TEXT_LEN: usize = MAGIC_TEXT.len();
const MAGIC_VERSION_LEN: usize = mem::size_of::<u16>();
const HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_VERSION_LEN; // magic text + external magic + magic
const ENTRY_HEADER_SIZE: usize = 1 + LEN_BUF_SIZE; // flag + len
const FIXED_MANIFEST_ENTRY_SIZE: usize = ENTRY_HEADER_SIZE + CHECKSUM_SIZE; // flag + len + checksum
const CHECKSUM_SIZE: usize = mem::size_of::<u32>();
const LEN_BUF_SIZE: usize = mem::size_of::<u32>();

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

  /// Allocator error.
  #[error(transparent)]
  AllocatorError(#[from] AllocatorError),

  /// I/O error.
  #[error(transparent)]
  IO(#[from] std::io::Error),
}

impl<M: Manifest> Error<M> {
  /// Create a new `Error` from an I/O error.
  #[cfg(feature = "std")]
  #[inline]
  pub const fn io(err: std::io::Error) -> Self {
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

/// The manifest trait, manifest may contain some in-memory information about the append-only log.
pub trait Manifest: Sized {
  /// The data type.
  type Data: Data;

  /// The options type used to create a new manifest.
  type Options;

  /// The error type.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// The error type.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Open a new manifest.
  fn open(opts: Self::Options) -> Result<Self, Self::Error>;

  /// Insert a new entry.
  fn insert(&self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  /// Insert a batch of entries.
  fn insert_batch(&self, entries: Vec<Entry<Self::Data>>) -> Result<(), Self::Error>;
}

/// Options for the manifest file.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  magic_version: u16,
  sync_on_write: bool,
  capacity: u32,
}

impl Default for Options {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Options {
  /// Create a new Options with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new(10_000);
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      magic_version: 0,
      sync_on_write: true,
      capacity: 0,
    }
  }

  /// Get the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
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
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.sync_on_write(), true);
  /// ```
  #[inline]
  pub const fn sync_on_write(&self) -> bool {
    self.sync_on_write
  }

  /// Get the capacity of the append-only log.
  ///
  /// This configuration is used to pre-allocate the append-only log.
  /// When using [`AppendLog::map`], this configuration will be ignored.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new().with_capacity(10_000);
  ///
  /// assert_eq!(opts.capacity(), 0);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    self.capacity
  }

  /// Set the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
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
  /// Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
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

  /// Set the capacity of the append-only log.
  ///
  /// This configuration is used to pre-allocate the append-only log.
  /// When using [`AppendLog::map`], this configuration will be ignored.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::arena::Options;
  ///
  /// let opts = Options::new().with_capacity(10_000);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = capacity;
    self
  }
}

/// Generic append-only log implementation based on [`Arena`] (support both in-memory and on-disk).
/// 
/// Compared to [`fs::AppendLog`](crate::fs::AppendLog):
/// 
/// - Pros:
///   - As this implementation is backed by an ARENA, no allocation required for both read and write.
///   - Fast read and write performance, backed by memory map, no extra I/O required.
///   - Lock-free and concurrent-safe.
///   - Support both in-memory and on-disk.
///   - Can be used in `no_std` environment.
/// 
/// - Cons:
///   - Pre-allocated is required, grow is not supported.
///   - Does not support automatic rewrite.
///   - Maximum size is less than `u32::MAX`.
/// 
/// It is good for:
/// - Append-only log which size cannot reach `4GB`.
/// - End-users who can manage the grow and rewrite by themselves.
///
/// File structure:
///
/// ```text
/// +-----------------------+--------------------------+-------------------------+
/// | ARENA meta (n bytes)  | magic text (4 bytes)     | magic version (2 bytes) |
/// +-----------------------+--------------------------+-------------------------+-----------------------+-----------------------+
/// | op (1 bit)            | custom flag (7 bits)     | len (4 bytes)           | data (n bytes)        | checksum (4 bytes)    |
/// +-----------------------+--------------------------+-------------------------+-----------------------+-----------------------+
/// | op (1 bit)            | custom flag (7 bits)     | len (4 bytes)           | data (n bytes)        | checksum (4 bytes)    |
/// +-----------------------+--------------------------+-------------------------+-----------------------+-----------------------+
/// | ...                   | ...                      | ...                     | ...                   | ...                   |
/// +-----------------------+--------------------------+-------------------------+-----------------------+-----------------------+
/// ```
#[derive(Debug)]
pub struct AppendLog<M, C = Crc32> {
  opts: Options,
  #[cfg(feature = "std")]
  filename: Option<PathBuf>,
  arena: Arena,
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

  /// Returns the path to the append-only log.
  ///
  /// This method returns `Some(_)` only if the append-only log is backed by a file.
  #[inline]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  pub fn path(&self) -> Option<&std::path::Path> {
    self.filename.as_deref()
  }

  /// Flush the manifest file.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[inline]
  pub fn flush(&self) -> std::io::Result<()> {
    self.arena.flush()
  }
}

impl<M, C> AppendLog<M, C> {
  
}

impl<M: Manifest, C: Checksumer> AppendLog<M, C> {
  /// Open an append-only log backed by a bytes slice.
  #[inline]
  pub fn open(opts: Options, manifest_opts: M::Options) -> Result<Self, Error<M>> {
    let arena = Arena::new(arena_options(opts.capacity));

    #[cfg(not(feature = "std"))]
    return Self::open_in(arena, false, opts, manifest_opts);

    #[cfg(feature = "std")]
    Self::open_in(None, arena, false, opts, manifest_opts)
  }

  /// Open an append-only log backed by read only memory mapped file.
  #[cfg(feature = "memmap")]
  #[cfg_attr(docsrs, doc(cfg(feature = "memmap")))]
  #[inline]
  pub fn map<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    manifest_opts: M::Options,
    open_options: OpenOptions,
  ) -> Result<Self, Error<M>> {
    let path = path.as_ref();
    let arena =
      Arena::map(path, open_options, MmapOptions::new(), CURRENT_VERSION).map_err(Error::io)?;

    Self::open_in(Some(path.to_path_buf()), arena, true, opts, manifest_opts)
  }

  /// Open or create an append-only log backed by memory mapped file.
  #[cfg(feature = "memmap")]
  #[cfg_attr(docsrs, doc(cfg(feature = "memmap")))]
  #[inline]
  pub fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    manifest_opts: M::Options,
    open_options: OpenOptions,
  ) -> Result<Self, Error<M>> {
    let arena_opts = arena_options(opts.capacity);
    let path = path.as_ref();
    let arena =
      Arena::map_mut(path, arena_opts, open_options, MmapOptions::new()).map_err(Error::io)?;

    Self::open_in(
      Some(path.to_path_buf()),
      arena,
      path.exists(),
      opts,
      manifest_opts,
    )
  }

  /// Open or create an append-only log backed by anonymous memory map.
  #[cfg(feature = "memmap")]
  #[cfg_attr(docsrs, doc(cfg(feature = "memmap")))]
  #[inline]
  pub fn map_anon(opts: Options, manifest_opts: M::Options) -> Result<Self, Error<M>> {
    let arena_opts = arena_options(opts.capacity);
    let arena = Arena::map_anon(arena_opts, MmapOptions::new()).map_err(Error::io)?;

    Self::open_in(None, arena, false, opts, manifest_opts)
  }

  /// Append an entry to the append-only file.
  #[inline]
  pub fn append(&mut self, ent: Entry<M::Data>) -> Result<(), Error<M>> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(&mut self, entries: Vec<Entry<M::Data>>) -> Result<(), Error<M>> {
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

    let mut buf = self
      .arena
      .alloc_bytes(total_encoded_size as u32)
      .map_err(Error::AllocatorError)?;
    buf.detach();
    encode_batch!(buf);

    self.manifest.insert_batch(entries).map_err(Error::manifest)?;

    #[cfg(feature = "std")]
    if self.opts.sync_on_write {
      self.flush()?;
    }

    Ok(())
  }

  fn open_in(
    #[cfg(feature = "std")] filename: Option<PathBuf>,
    arena: Arena,
    existing: bool,
    opts: Options,
    manifest_opts: M::Options,
  ) -> Result<Self, Error<M>> {
    let magic_version = opts.magic_version();
    let size = arena.allocated();

    if !existing && size < HEADER_SIZE {
      Self::write_header(&arena, magic_version)?;

      return Ok(Self {
        #[cfg(feature = "std")]
        filename,
        arena,
        manifest: M::open(manifest_opts).map_err(Error::manifest)?,
        _checksumer: core::marker::PhantomData,
        opts,
      });
    }

    let mut curosr = HEADER_SIZE;
    // SAFETY: we know the header size is 6 bytes.
    let header = unsafe { arena.get_bytes(arena.data_offset(), curosr) };

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

    let version = arena.magic_version();
    if version != CURRENT_VERSION {
      return Err(Error::BadMagic {
        expected: CURRENT_VERSION,
        found: version,
      });
    }

    let manifest = M::open(manifest_opts).map_err(Error::manifest)?;
    loop {
      let remaining = size - curosr;
      if remaining < ENTRY_HEADER_SIZE {
        break;
      }

      // SAFETY: we know the remaining size is at least 5 bytes.
      let entry_header = unsafe { arena.get_bytes(curosr, curosr + ENTRY_HEADER_SIZE) };

      let data_size = u32::from_le_bytes(entry_header[1..].try_into().unwrap()) as usize;
      let needed = FIXED_MANIFEST_ENTRY_SIZE + data_size;
      if needed > remaining {
        return Err(Error::entry_corrupted(needed as u32, remaining as u32));
      }

      // SAFETY: we know the remaining size is at least `needed` bytes.
      let full_entry =
        unsafe { arena.get_bytes(curosr, curosr + data_size + FIXED_MANIFEST_ENTRY_SIZE) };

      let ent = Entry::<M::Data>::decode::<C>(full_entry).map_err(|e| match e {
        Some(e) => Error::data(e),
        None => Error::ChecksumMismatch,
      })?;
      manifest.insert(ent).map_err(Error::manifest)?;
      curosr += needed;
    }

    let this = Self {
      filename,
      arena,
      manifest,
      _checksumer: core::marker::PhantomData,
      opts,
    };

    Ok(this)
  }

  #[inline]
  fn write_header(arena: &Arena, magic_version: u16) -> Result<(), Error<M>> {
    let mut buf = arena
      .alloc_bytes(HEADER_SIZE as u32)
      .map_err(Error::AllocatorError)?;
    buf.detach();
    buf[..MAGIC_TEXT_LEN].copy_from_slice(MAGIC_TEXT);
    buf[MAGIC_TEXT_LEN..MAGIC_TEXT_LEN + MAGIC_VERSION_LEN]
      .copy_from_slice(&magic_version.to_le_bytes());
    Ok(())
  }

  #[inline]
  fn append_in(&mut self, entry: Entry<M::Data>) -> Result<(), Error<M>> {
    let len = entry.data.encoded_size() + FIXED_MANIFEST_ENTRY_SIZE;
    let mut buf = self
      .arena
      .alloc_bytes(len as u32)
      .map_err(Error::AllocatorError)?;
    buf.detach();
    // SAFETY: we know the buffer is at least `len` bytes.
    unsafe {
      buf.put_u8_unchecked(entry.flag.value);
      let data_size = entry.data.encoded_size();
      buf.put_u32_le_unchecked(data_size as u32);

      let buf = slice::from_raw_parts_mut(
        buf.as_mut_ptr().add(ENTRY_HEADER_SIZE),
        data_size + CHECKSUM_SIZE,
      );
      entry.data.encode(buf).map_err(Error::data)?;

      let checksum = C::checksum(&buf[..len - CHECKSUM_SIZE]);
      buf[data_size..].copy_from_slice(&checksum.to_le_bytes());
    }

    #[cfg(feature = "std")]
    if self.opts.sync_on_write {
      self.flush()?;
    }

    Ok(())
  }
}

#[inline]
const fn arena_options(cap: u32) -> ArenaOptions {
  ArenaOptions::new()
    .with_capacity(cap)
    .with_freelist(Freelist::None)
    .with_unify(true)
    .with_magic_version(CURRENT_VERSION)
    .with_maximum_retries(0)
}
