use skl::{either::Either, u5, Arena, Options as MapOptions, SkipMap};
pub use skl::{map::Error as MapError, options::Freelist, ArenaError};

#[cfg(feature = "std")]
use skl::{MmapOptions, OpenOptions};

use super::*;

const CURRENT_VERSION: u16 = 0;
const HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_VERSION_LEN; // magic text + external magic + magic

/// The snapshot trait, snapshot may contain some in-memory information about the append-only log.
pub trait Snapshot: Sized {
  /// The data type.
  type Data: Data;

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

  /// Insert a new entry.
  fn insert(&self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  /// Insert a batch of entries.
  fn insert_batch(&self, entries: Vec<Entry<Self::Data>>) -> Result<(), Self::Error>;
}

/// Errors for append-only file.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error<S: Snapshot> {
  /// Snapshot has bad magic.
  #[cfg(feature = "std")]
  #[error("snapshot has bad magic text")]
  BadMagicText,
  /// Cannot open snapshot because the external magic doesn't match.
  #[cfg(feature = "std")]
  #[error("cannot open snapshot because the external magic doesn't match. expected {expected}, found {found}")]
  BadExternalMagic {
    /// Expected external magic.
    expected: u16,
    /// Found external magic.
    found: u16,
  },
  /// Cannot open snapshot because the magic doesn't match.
  #[cfg(feature = "std")]
  #[error(
    "cannot open snapshot because the magic doesn't match. expected {expected}, found {found}"
  )]
  BadMagic {
    /// Expected magic.
    expected: u16,
    /// Found magic.
    found: u16,
  },

  /// Corrupted append only log: entry checksum mismatch.
  #[cfg(feature = "std")]
  #[error("entry checksum mismatch")]
  ChecksumMismatch,

  /// Encode/decode data error.
  #[cfg_attr(feature = "std", error(transparent))]
  Data(<S::Data as Data>::Error),

  /// Snapshot error.
  #[cfg_attr(feature = "std", error(transparent))]
  Snapshot(S::Error),

  /// Allocator error.
  #[cfg_attr(feature = "std", error(transparent))]
  AllocatorError(#[cfg_attr(feature = "std", from)] MapError),

  /// I/O error.
  #[cfg(feature = "std")]
  #[error(transparent)]
  IO(#[from] std::io::Error),
}

#[cfg(not(feature = "std"))]
impl<S: Snapshot> core::fmt::Display for Error<S> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Data(err) => err.fmt(f),
      Self::Snapshot(err) => err.fmt(f),
      Self::AllocatorError(err) => err.fmt(f),
    }
  }
}

impl<S: Snapshot> Error<S> {
  /// Create a new `Error` from an I/O error.
  #[cfg(feature = "std")]
  #[inline]
  pub const fn io(err: std::io::Error) -> Self {
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
}

/// Options for the append only log.
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
  /// Create a new Options with the default capacity.
  ///
  /// Default capacity is `1MB`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::memmap::sync::Options;
  ///
  /// let opts = Options::new();
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      magic_version: 0,
      sync_on_write: true,
      capacity: 10240,
    }
  }

  /// Get the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use aol::memmap::sync::Options;
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
  /// use aol::memmap::sync::Options;
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
  /// use aol::memmap::sync::Options;
  ///
  /// let opts = Options::new().with_capacity(10_000);
  ///
  /// assert_eq!(opts.capacity(), 10_000);
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
  /// use aol::memmap::sync::Options;
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
  /// use aol::memmap::sync::Options;
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
  /// use aol::memmap::sync::Options;
  ///
  /// let opts = Options::new().with_capacity(10_000);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = capacity;
    self
  }
}

/// Generic append-only log implementation based on lockfree ARENA based [`SkipMap`] (support both in-memory and on-disk).
///
/// - It is good for:
///   - Append-only log which size cannot reach `4GB`.
///   - End-users who can manage the grow and rewrite by themselves.
///
/// - Compared to [`fs::AppendLog`](crate::fs::AppendLog):
///
///   - Pros:
///     - As this implementation is backed by an ARENA, no allocation required for both read and write.
///     - Fast read and write performance, backed by memory map, no extra I/O required.
///     - Lock-free and concurrent-safe.
///     - Support both in-memory and on-disk.
///     - Can be used in `no_std` environment.
///
///   - Cons:
///     - Pre-allocated is required, automatic grow and rewrite are not supported.
///     - Maximum size is less than `u32::MAX`.
///     - May contains memory holes
///
/// - Compared to [`memmap::AppendLog`](crate::memmap::AppendLog):
///
///   - Pros:
///     - Lock-free and concurrent-safe.
///     - Support both in-memory and on-disk.
///     - Can be used in `no_std` environment.
///   
///   - Cons:
///     - Maximum size is less than `u32::MAX`.
///     - May contains memory holes
#[derive(Debug)]
pub struct AppendLog<S, C = Crc32> {
  opts: Options,
  #[cfg(feature = "std")]
  filename: Option<PathBuf>,
  map: SkipMap<()>,
  slot: AtomicU64,
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

  /// Returns the path to the append-only log.
  ///
  /// This method returns `Some(_)` only if the append-only log is backed by a file.
  #[inline]
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  pub fn path(&self) -> Option<&std::path::Path> {
    self.filename.as_deref()
  }

  /// Flush the append only log.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[inline]
  pub fn flush(&self) -> std::io::Result<()> {
    self.map.flush()
  }
}

impl<S, C> AppendLog<S, C> {}

impl<S: Snapshot, C: Checksumer> AppendLog<S, C> {
  /// Open an append-only log backed by a bytes slice.
  #[inline]
  pub fn new(opts: Options, snapshot_opts: S::Options) -> Result<Self, Error<S>> {
    let map =
      SkipMap::<()>::with_options(map_options(opts.capacity)).map_err(Error::AllocatorError)?;

    #[cfg(not(feature = "std"))]
    return Self::open_in(map, false, opts, snapshot_opts);

    #[cfg(feature = "std")]
    Self::open_in(None, map, false, opts, snapshot_opts)
  }

  /// Open an append-only log backed by read only memory mapped file.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[inline]
  pub fn map<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    snapshot_opts: S::Options,
    open_options: OpenOptions,
  ) -> Result<Self, Error<S>> {
    let path = path.as_ref();
    let map = SkipMap::<()>::map(path, open_options, MmapOptions::new(), CURRENT_VERSION)
      .map_err(Error::io)?;

    Self::open_in(Some(path.to_path_buf()), map, true, opts, snapshot_opts)
  }

  /// Open or create an append-only log backed by memory mapped file.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[inline]
  pub fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    snapshot_opts: S::Options,
    open_options: OpenOptions,
  ) -> Result<Self, Error<S>> {
    let arena_opts = map_options(opts.capacity);
    let path = path.as_ref();
    let map =
      SkipMap::<()>::map_mut_with_options(path, arena_opts, open_options, MmapOptions::new())
        .map_err(Error::io)?;

    Self::open_in(
      Some(path.to_path_buf()),
      map,
      path.exists(),
      opts,
      snapshot_opts,
    )
  }

  /// Open or create an append-only log backed by anonymous memory map.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[inline]
  pub fn map_anon(opts: Options, snapshot_opts: S::Options) -> Result<Self, Error<S>> {
    let arena_opts = map_options(opts.capacity);
    let arena =
      SkipMap::<()>::map_anon_with_options(arena_opts, MmapOptions::new()).map_err(Error::io)?;

    Self::open_in(None, arena, false, opts, snapshot_opts)
  }

  /// Append an entry to the append-only file.
  #[inline]
  pub fn append(&mut self, entry: Entry<S::Data>) -> Result<(), Error<S>> {
    let id = self.slot.fetch_add(1, Ordering::Acquire);

    let data_size = entry.data.encoded_size();
    let k = id.to_le_bytes();
    let res = self.map.insert_with_value::<<S::Data as Data>::Error>(
      (),
      &k,
      (data_size + FIXED_ENTRY_LEN) as u32,
      |buf| {
        buf.fill(0);
        entry.encode::<C>(data_size, buf)?;
        Ok(())
      },
    );

    match res {
      Ok(_) => {
        self.snapshot.insert(entry).map_err(Error::snapshot)?;
        #[cfg(feature = "std")]
        if self.opts.sync_on_write {
          self.flush()?;
        }

        Ok(())
      }
      Err(e) => {
        let _ = self
          .map
          .compare_remove((), &k, Ordering::AcqRel, Ordering::Release);
        match e {
          Either::Left(e) => Err(Error::Data(e)),
          Either::Right(e) => Err(Error::AllocatorError(e)),
        }
      }
    }
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(&mut self, entries: Vec<Entry<S::Data>>) -> Result<(), Error<S>> {
    let total_encoded_size = entries
      .iter()
      .map(|ent| ent.data.encoded_size())
      .sum::<usize>()
      + entries.len() * FIXED_ENTRY_LEN;

    macro_rules! encode_batch {
      ($buf:ident) => {{
        let mut cursor = 0;
        for ent in &entries {
          cursor += ent.encode::<C>(ent.data.encoded_size(), &mut $buf[cursor..])?;
        }
      }};
    }

    let id = self.slot.fetch_add(1, Ordering::Acquire);
    let k = id.to_le_bytes();
    let res = self.map.insert_with_value::<<S::Data as Data>::Error>(
      (),
      &k,
      total_encoded_size as u32,
      |buf| {
        buf.fill(0);
        encode_batch!(buf);
        Ok(())
      },
    );

    match res {
      Ok(_) => {
        self
          .snapshot
          .insert_batch(entries)
          .map_err(Error::snapshot)?;

        #[cfg(feature = "std")]
        if self.opts.sync_on_write {
          self.flush()?;
        }

        Ok(())
      }
      Err(e) => match e {
        Either::Left(e) => Err(Error::data(e)),
        Either::Right(e) => Err(Error::AllocatorError(e)),
      },
    }
  }

  fn open_in(
    #[cfg(feature = "std")] filename: Option<PathBuf>,
    map: SkipMap<()>,
    existing: bool,
    opts: Options,
    snapshot_opts: S::Options,
  ) -> Result<Self, Error<S>> {
    let magic_version = opts.magic_version();
    let size = map.allocated() - map.data_offset();

    if !existing || size == 0 {
      Self::write_header(map.allocator(), magic_version)?;

      return Ok(Self {
        #[cfg(feature = "std")]
        filename,
        slot: AtomicU64::new(map.max_version()),
        map,
        snapshot: S::new(snapshot_opts).map_err(Error::snapshot)?,
        _checksumer: core::marker::PhantomData,
        opts,
      });
    }

    #[cfg(not(feature = "std"))]
    unreachable!("impossible branch");

    #[cfg(feature = "std")]
    {
      // SAFETY: we know the header size is 6 bytes.
      let header = unsafe { map.allocator().get_bytes(map.data_offset(), HEADER_SIZE) };

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

      let version = map.magic_version();
      if version != CURRENT_VERSION {
        return Err(Error::BadMagic {
          expected: CURRENT_VERSION,
          found: version,
        });
      }

      let snapshot = S::new(snapshot_opts).map_err(Error::snapshot)?;

      let iter = map.iter(0);

      for ent in iter {
        let mut cursor = 0;
        let raw = ent.value();
        let len = raw.len();

        loop {
          let remaining = len - cursor;
          if remaining < ENTRY_HEADER_SIZE {
            break;
          }

          let (readed, ent) =
            Entry::<S::Data>::decode::<C>(&raw[cursor..]).map_err(|e| match e {
              Some(e) => Error::data(e),
              None => Error::ChecksumMismatch,
            })?;
          snapshot.insert(ent).map_err(Error::snapshot)?;
          cursor += readed;

          if cursor == len {
            break;
          }
        }
      }

      let this = Self {
        filename,
        slot: AtomicU64::new(map.max_version()),
        map,
        snapshot,
        _checksumer: core::marker::PhantomData,
        opts,
      };

      Ok(this)
    }
  }

  #[inline]
  fn write_header(arena: &Arena, magic_version: u16) -> Result<(), Error<S>> {
    let mut buf = arena
      .alloc_bytes(HEADER_SIZE as u32)
      .map_err(|e| Error::AllocatorError(skl::map::Error::Arena(e)))?;
    buf.detach();
    buf[..MAGIC_TEXT_LEN].copy_from_slice(MAGIC_TEXT);
    buf[MAGIC_TEXT_LEN..MAGIC_TEXT_LEN + MAGIC_VERSION_LEN]
      .copy_from_slice(&magic_version.to_le_bytes());
    Ok(())
  }
}

#[inline]
const fn map_options(cap: u32) -> MapOptions {
  MapOptions::new()
    .with_capacity(cap)
    .with_freelist(Freelist::None)
    .with_unify(true)
    .with_max_height(u5::new(1))
    .with_magic_version(CURRENT_VERSION)
}
