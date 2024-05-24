//! Generic purpose append only manifest file implementation.
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs, warnings)]
#![forbid(unsafe_code)]

#[cfg(not(any(feature = "std", feature = "alloc")))]
compile_error!("`manifile` cannot be compiled when both `std` and `alloc` are not enabled.");

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

#[cfg(not(feature = "std"))]
use std::vec::Vec;

use core::mem;

/// Errors.
pub mod error;
use error::Error;

/// The underlying file for [`ManifestFile`].
pub mod file;
pub use file::{BackedFile, BackedFileError};

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use file::{File, FileOptions};

/// Some [`Manifest`](crate::manifest::Manifest) implementations.
pub mod manifest;
pub use manifest::*;

const MANIFEST_DELETIONS_REWRITE_THRESHOLD: u64 = 10000;
const MANIFEST_DELETIONS_RATIO: u64 = 10;

/// Magic text for the manifest file, this will never be changed.
const MAGIC_TEXT: &[u8] = b"al8n";
const MAGIC_TEXT_LEN: usize = MAGIC_TEXT.len();
const MAGIC_LEN: usize = mem::size_of::<u16>();
const EXTERNAL_MAGIC_LEN: usize = mem::size_of::<u16>();
const MANIFEST_HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_LEN + EXTERNAL_MAGIC_LEN; // magic text + external magic + magic
const MANIFEST_ENTRY_HEADER_SIZE: usize = 1 + LEN_BUF_SIZE; // flag + len
const FIXED_MANIFEST_ENTRY_SIZE: usize = MANIFEST_ENTRY_HEADER_SIZE + CHECKSUM_SIZE; // flag + len + checksum
const MAX_INLINE_SIZE: usize = 64;
const CHECKSUM_SIZE: usize = mem::size_of::<u32>();
const LEN_BUF_SIZE: usize = mem::size_of::<u32>();

const DELETE_FLAG: u8 = 0b00000001;
const MASK: u8 = 0b11111110;
const CUSTOM_CORE_MASK: CustomFlagsCore = CustomFlagsCore::from_bits_retain(MASK);

bitflags::bitflags! {
  #[derive(Default, PartialEq, Eq, Copy, Clone, Hash)]
  struct CustomFlagsCore: u8 {
    const BIT1 = 0b00000010;
    const BIT2 = 0b00000100;
    const BIT3 = 0b00001000;
    const BIT4 = 0b00010000;
    const BIT5 = 0b00100000;
    const BIT6 = 0b01000000;
    const BIT7 = 0b10000000;
  }
}

/// A 7-bit custom flag.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CustomFlags(CustomFlagsCore);

impl core::fmt::Debug for CustomFlags {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("CustomFlags")
      .field(&(self.0.bits() & MASK))
      .finish()
  }
}

impl core::fmt::Display for CustomFlags {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "{}", self.0.bits() & MASK)
  }
}

macro_rules! bits_api {
  ($($num:literal), +$(,)?) => {
    $(
      paste::paste! {
        #[doc = concat!("Set the bit", $num,)]
        #[inline]
        pub fn [< set_bit $num >] (&mut self) {
          self.0.insert(CustomFlagsCore::[< BIT $num >]);
        }

        #[doc = concat!("Set the bit", $num,)]
        #[inline]
        pub fn [< with_bit $num >] (mut self) -> Self {
          self.0.insert(CustomFlagsCore::[< BIT $num >]);
          self
        }

        #[doc = concat!("Clear the bit", $num,)]
        #[inline]
        pub fn [< clear_bit $num >](&mut self) {
          self.0.remove(CustomFlagsCore::[< BIT $num >]);
        }

        #[doc = concat!("Returns `true` if the bit", $num, " is set.")]
        #[inline]
        pub const fn [< bit $num >](&self) -> bool {
          self.0.contains(CustomFlagsCore::[< BIT $num >])
        }
      }
    )*
  };
}

macro_rules! flags_api {
  ($($name:ident: $doc:literal), +$(,)?) => {
    $(
      #[doc = $doc]
      #[inline]
      pub const fn $name(&self, other: Self) -> Self {
        Self(CustomFlagsCore::from_bits_retain((self.0.$name(other.0).bits() & MASK)))
      }
    )*
  };
}

macro_rules! impl_bitwise_ops {
  ($($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident),+ $(,)?) => {
    $(
      impl core::ops::$trait for CustomFlags {
        type Output = Self;

        #[inline]
        fn $method(self, rhs: Self) -> Self::Output {
          #[allow(clippy::suspicious_arithmetic_impl)]
          Self(self.0.$method(rhs.0) & CUSTOM_CORE_MASK)
        }
      }

      impl core::ops::$assign_trait for CustomFlags {
        #[inline]
        #[allow(clippy::suspicious_op_assign_impl)]
        fn $assign_method(&mut self, rhs: Self) {
          self.0.$assign_method(rhs.0);
          self.0 &= CUSTOM_CORE_MASK;
        }
      }
    )*
  };
}

impl core::ops::Not for CustomFlags {
  type Output = Self;

  #[inline]
  fn not(self) -> Self::Output {
    Self(self.0.not() & CUSTOM_CORE_MASK)
  }
}

impl_bitwise_ops! {
  BitAnd, bitand, BitAndAssign, bitand_assign,
  BitOr, bitor, BitOrAssign, bitor_assign,
  BitXor, bitxor, BitXorAssign, bitxor_assign,
}

impl CustomFlags {
  /// Get a flags value with all known bits set.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::CustomFlags;
  ///
  /// let flags = CustomFlags::all();
  /// ```
  #[inline]
  pub const fn all() -> Self {
    Self(CustomFlagsCore::all())
  }

  /// Get a flags value with all known bits unset.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::CustomFlags;
  ///
  /// let flags = CustomFlags::empty();
  /// ```
  #[inline]
  pub const fn empty() -> Self {
    Self(CustomFlagsCore::empty())
  }

  /// Whether all set bits in a source flags value are also set in a target flags value.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::CustomFlags;
  ///
  /// let flags = CustomFlags::empty();
  ///
  /// assert_eq!(flags.contains(CustomFlags::empty()), true);
  /// ```
  #[inline]
  pub const fn contains(&self, other: Self) -> bool {
    self.0.contains(other.0)
  }

  /// The bitwise exclusive-or (`^`) of the bits in two flags values.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::CustomFlags;
  ///
  /// let mut flags = CustomFlags::all();
  /// flags.toggle(CustomFlags::all());
  ///
  /// assert_eq!(flags, CustomFlags::empty());
  /// ```
  #[inline]
  pub fn toggle(&mut self, other: Self) {
    self.0.toggle(other.0);
    self.0 &= CUSTOM_CORE_MASK;
  }

  /// The bitwise negation (`!`) of the bits in a flags value, truncating the result.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::CustomFlags;
  ///
  /// let flags = CustomFlags::all();
  ///
  /// assert_eq!(flags.complement(), CustomFlags::empty());
  /// ```
  #[inline]
  pub const fn complement(&self) -> Self {
    Self(CustomFlagsCore::from_bits_retain(
      self.0.complement().bits() & MASK,
    ))
  }

  /// Whether all bits in this flags value are unset.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::CustomFlags;
  ///
  /// let flags = CustomFlags::empty();
  ///
  /// assert_eq!(flags.is_empty(), true);
  /// ```
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.0.is_empty()
  }

  /// Whether any bits in this flags value are set.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::CustomFlags;
  ///
  /// let flags = CustomFlags::all();
  ///
  /// assert_eq!(flags.is_all(), true);
  /// ```
  #[inline]
  pub const fn is_all(&self) -> bool {
    self.0.is_all()
  }

  flags_api! {
    union: "The bitwise intersection (`|`) of the bits in two flags values.",
    intersection: "The bitwise intersection (`&`) of the bits in two flags values.",
    difference: "
    The intersection of a source flags value with the complement of a target flags value (`&!`).

    This method is not equivalent to `self & !other` when `other` has unknown bits set. difference won't truncate other, but the `!` operator will.
    ",
    symmetric_difference: "The bitwise exclusive-or (`^`) of the bits in two flags values.",
  }

  bits_api!(1, 2, 3, 4, 5, 6, 7);

  #[inline]
  const fn bits(&self) -> u8 {
    self.0.bits()
  }
}

/// Flags for the manifest entry.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
pub struct EntryFlags {
  value: u8,
}

impl core::fmt::Debug for EntryFlags {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryFlags")
      .field("custom_flag", &self.custom_flag())
      .field(
        "op",
        if self.is_deletion() {
          &"deletion"
        } else {
          &"creation"
        },
      )
      .finish()
  }
}

impl EntryFlags {
  /// Creates a new [`EntryFlags`] with the creation flag set
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::EntryFlags;
  ///
  /// let entry = EntryFlags::creation();
  ///
  /// assert_eq!(entry.is_creation(), true);
  /// ```
  #[inline]
  pub const fn creation() -> Self {
    Self::new(CustomFlags::empty())
  }

  /// Creates a new [`EntryFlags`] with the deletion flag set
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::EntryFlags;
  ///
  /// let entry = EntryFlags::deletion();
  ///
  /// assert_eq!(entry.is_deletion(), true);
  /// ```
  #[inline]
  pub const fn deletion() -> Self {
    Self::new(CustomFlags::empty())
  }

  /// Creates a new [`EntryFlags`] with the deletion flag set
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::{EntryFlags, CustomFlags};
  ///
  /// let entry = EntryFlags::deletion_with_custom_flag(CustomFlags::empty());
  ///
  /// assert_eq!(entry.is_deletion(), true);
  /// ```
  #[inline]
  pub const fn deletion_with_custom_flag(flag: CustomFlags) -> Self {
    let mut this = Self::new(flag);
    this.value |= DELETE_FLAG;
    this
  }

  /// Creates a new [`EntryFlags`] with the creation flag set
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::{EntryFlags, CustomFlags};
  ///
  /// let entry = EntryFlags::creation(CustomFlags::empty());
  ///
  /// assert_eq!(entry.is_creation(), true);
  /// ```
  #[inline]
  pub const fn creation_with_custom_flag(flag: CustomFlags) -> Self {
    let mut this = Self::new(flag);
    this.value &= !DELETE_FLAG;
    this
  }

  /// Returns the custom flag
  #[inline]
  pub const fn custom_flag(&self) -> CustomFlags {
    CustomFlags(CustomFlagsCore::from_bits_retain(self.value >> 1))
  }

  /// Set the custom flag
  #[inline]
  pub fn set_custom_flag(&mut self, flag: CustomFlags) {
    self.value = (flag.bits() << 1) & MASK | (self.value & DELETE_FLAG);
  }

  /// Returns `true`` if the entry is a deletion.
  #[inline]
  pub const fn is_deletion(&self) -> bool {
    (self.value & DELETE_FLAG) != 0
  }

  /// Returns `true`` if the entry is a creation.
  #[inline]
  pub const fn is_creation(&self) -> bool {
    (self.value & DELETE_FLAG) == 0
  }

  // Creates a new EntryFlags with initial value (excluding the first bit)
  #[inline]
  const fn new(flag: CustomFlags) -> Self {
    Self {
      value: flag.bits() & MASK,
    }
  }
}

/// Checksumer trait.
pub trait Checksumer {
  /// Calculate the checksum of the buffer.
  fn checksum(buf: &[u8]) -> u32;
}

/// CRC32 checksumer.
#[derive(Default, Debug, Copy, Clone)]
pub struct Crc32;

impl Checksumer for Crc32 {
  #[inline]
  fn checksum(buf: &[u8]) -> u32 {
    crc32fast::hash(buf)
  }
}

/// Options for the manifest file.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  external_magic: u16,
  magic: u16,
  rewrite_threshold: u64,
  deletions_ratio: u64,
  sync_on_write: bool,
}

impl Default for Options {
  /// Returns the default options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
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
  /// use manifile::Options;
  ///
  /// let opts = Options::new();
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      external_magic: 0,
      magic: 0,
      rewrite_threshold: MANIFEST_DELETIONS_REWRITE_THRESHOLD,
      deletions_ratio: MANIFEST_DELETIONS_RATIO,
      sync_on_write: true,
    }
  }

  /// Get the external magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.external_magic(), 0);
  /// ```
  #[inline]
  pub const fn external_magic(&self) -> u16 {
    self.external_magic
  }

  /// Get the magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.magic(), 0);
  /// ```
  #[inline]
  pub const fn magic(&self) -> u16 {
    self.magic
  }

  /// Get the rewrite threshold.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.rewrite_threshold(), 10000);
  /// ```
  #[inline]
  pub const fn rewrite_threshold(&self) -> u64 {
    self.rewrite_threshold
  }

  /// Get the deletions ratio.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.deletions_ratio(), 10);
  /// ```
  #[inline]
  pub const fn deletions_ratio(&self) -> u64 {
    self.deletions_ratio
  }

  /// Get whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
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
  /// use manifile::Options;
  ///
  /// let opts = Options::new().with_external_magic(1);
  ///
  /// assert_eq!(opts.external_magic(), 1);
  /// ```
  #[inline]
  pub const fn with_external_magic(mut self, external_magic: u16) -> Self {
    self.external_magic = external_magic;
    self
  }

  /// Set the magic.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
  ///
  /// let opts = Options::new().with_magic(1);
  ///
  /// assert_eq!(opts.magic(), 1);
  /// ```
  #[inline]
  pub const fn with_magic(mut self, magic: u16) -> Self {
    self.magic = magic;
    self
  }

  /// Set the rewrite threshold.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
  ///
  /// let opts = Options::new().with_rewrite_threshold(100);
  ///
  /// assert_eq!(opts.rewrite_threshold(), 100);
  ///
  /// ```
  #[inline]
  pub const fn with_rewrite_threshold(mut self, rewrite_threshold: u64) -> Self {
    self.rewrite_threshold = rewrite_threshold;
    self
  }

  /// Set the deletions ratio.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
  ///
  /// let opts = Options::new().with_deletions_ratio(100);
  ///
  /// assert_eq!(opts.deletions_ratio(), 100);
  /// ```
  #[inline]
  pub const fn with_deletions_ratio(mut self, deletions_ratio: u64) -> Self {
    self.deletions_ratio = deletions_ratio;
    self
  }

  /// Set whether flush the data to disk after write.
  ///
  ///  Default is `true`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use manifile::Options;
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

/// The default underlying file for [`ManifestFile`].
#[cfg(feature = "std")]
pub type DefaultBackedFile = File;

/// The default underlying file for [`ManifestFile`].
#[cfg(not(feature = "std"))]
pub type DefaultBackedFile = Vec<u8>;

/// Generic manifest file implementation.
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
pub struct ManifestFile<M, F = DefaultBackedFile, C = Crc32> {
  opts: Options,
  file: F,
  manifest: M,
  _checksumer: core::marker::PhantomData<C>,
}

impl<M, F, C> Clone for ManifestFile<M, F, C>
where
  F: Clone,
  M: Clone,
{
  fn clone(&self) -> Self {
    Self {
      file: self.file.clone(),
      manifest: self.manifest.clone(),
      opts: self.opts.clone(),
      _checksumer: core::marker::PhantomData,
    }
  }
}

impl<F: BackedFile, M: BackedManifest, C: Checksumer> ManifestFile<M, F, C> {
  /// Open and replay the manifest file.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open<P: AsRef<std::path::Path>>(
    path: P,
    file_opts: F::Options,
    opts: Options,
  ) -> Result<Self, Error<F, M>> {
    let (existing, file) = F::open(path, file_opts).map_err(Error::io)?;

    Self::open_in(file, existing, opts)
  }

  /// Open and replay the manifest file.
  #[cfg(not(feature = "std"))]
  #[inline]
  pub fn open(file_opts: F::Options, opts: Options) -> Result<Self, Error<F, M>> {
    let (existing, file) = F::open(file_opts).map_err(Error::io)?;

    Self::open_in(file, existing, opts)
  }

  /// Flush the manifest file.
  #[inline]
  pub fn flush(&mut self) -> Result<(), Error<F, M>> {
    self.file.flush().map_err(Error::io)
  }

  /// Sync the manifest file.
  #[inline]
  pub fn sync_all(&self) -> Result<(), Error<F, M>> {
    self.file.sync_all().map_err(Error::io)
  }

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

  /// Append an entry to the manifest file.
  #[inline]
  pub fn append(&mut self, ent: Entry<M::Data>) -> Result<(), Error<F, M>> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the manifest file.
  pub fn append_batch(&mut self, entries: Vec<Entry<M::Data>>) -> Result<(), Error<F, M>> {
    if self.should_rewrite() {
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
        for ent in entries {
          cursor += ent
            .encode::<C>(ent.data.encoded_size(), &mut $buf[cursor..])
            .map_err(Error::data)?;
        }
      }};
    }

    if total_encoded_size > MAX_INLINE_SIZE {
      let mut buf = std::vec![0; total_encoded_size];
      encode_batch!(buf);
      self
        .file
        .write_all(&buf)
        .and_then(|_| {
          if self.opts.sync_on_write {
            self.file.flush()
          } else {
            Ok(())
          }
        })
        .map_err(Error::io)
    } else {
      let mut buf = [0; MAX_INLINE_SIZE];
      let buf = &mut buf[..total_encoded_size];
      encode_batch!(buf);
      self
        .file
        .write_all(buf)
        .and_then(|_| {
          if self.opts.sync_on_write {
            self.file.flush()
          } else {
            Ok(())
          }
        })
        .map_err(Error::io)
    }
  }

  fn open_in(mut file: F, existing: bool, opts: Options) -> Result<Self, Error<F, M>> {
    let Options {
      magic,
      external_magic,
      ..
    } = opts;

    if !existing {
      let mut buf = [0; MANIFEST_HEADER_SIZE];
      buf[..MAGIC_TEXT_LEN].copy_from_slice(MAGIC_TEXT);
      buf[MAGIC_TEXT_LEN..MAGIC_TEXT_LEN + EXTERNAL_MAGIC_LEN]
        .copy_from_slice(&external_magic.to_le_bytes());
      buf[MAGIC_TEXT_LEN + EXTERNAL_MAGIC_LEN..MANIFEST_HEADER_SIZE]
        .copy_from_slice(&magic.to_le_bytes());
      file.write_all(&buf).map_err(Error::io)?;
      file.flush().map_err(Error::io)?;

      return Ok(Self {
        file,
        manifest: M::default(),
        _checksumer: core::marker::PhantomData,
        opts,
      });
    }

    let size = file.size().map_err(Error::io)?;

    let mut header = [0; MANIFEST_HEADER_SIZE];
    file.read_exact(&mut header).map_err(Error::io)?;

    if &header[..MAGIC_TEXT_LEN] != MAGIC_TEXT {
      return Err(Error::BadMagicText);
    }

    let external = u16::from_le_bytes(
      header[MAGIC_TEXT_LEN..MAGIC_TEXT_LEN + EXTERNAL_MAGIC_LEN]
        .try_into()
        .unwrap(),
    );
    if external != external_magic {
      return Err(Error::BadExternalMagic {
        expected: external_magic,
        found: external,
      });
    }

    let version = u16::from_le_bytes(
      header[MAGIC_TEXT_LEN + EXTERNAL_MAGIC_LEN..MANIFEST_HEADER_SIZE]
        .try_into()
        .unwrap(),
    );
    if version != magic {
      return Err(Error::BadMagic {
        expected: magic,
        found: version,
      });
    }

    let mut manifest = M::default();

    let mut curosr = 0;
    loop {
      let mut header_buf = [0; MANIFEST_ENTRY_HEADER_SIZE];
      match file.read_exact(&mut header_buf) {
        Ok(()) => {
          curosr += MANIFEST_ENTRY_HEADER_SIZE;

          let len = u32::from_le_bytes(header_buf[1..].try_into().unwrap()) as usize;
          let entry_size = FIXED_MANIFEST_ENTRY_SIZE + len;

          let remaining = size - MANIFEST_HEADER_SIZE as u64 - curosr as u64;
          let needed = len + CHECKSUM_SIZE;
          if needed as u64 > remaining {
            return Err(Error::entry_corrupted(needed as u32, remaining as u32));
          }

          if entry_size > MAX_INLINE_SIZE {
            let mut buf = std::vec![0; entry_size];
            buf[..MANIFEST_ENTRY_HEADER_SIZE].copy_from_slice(&header_buf);
            file
              .read_exact(&mut buf[MANIFEST_ENTRY_HEADER_SIZE..])
              .map_err(Error::io)?;
            let ent = Entry::decode::<C>(&buf).map_err(|e| match e {
              Some(e) => Error::data(e),
              None => Error::ChecksumMismatch,
            })?;
            manifest.insert(ent).map_err(Error::manifest)?;
          } else {
            let mut buf = [0; MAX_INLINE_SIZE];
            buf[..MANIFEST_ENTRY_HEADER_SIZE].copy_from_slice(&header_buf);
            let buf = &mut buf
              [MANIFEST_ENTRY_HEADER_SIZE..MANIFEST_ENTRY_HEADER_SIZE + len + CHECKSUM_SIZE];
            file.read_exact(buf).map_err(Error::io)?;
            let ent = Entry::decode::<C>(buf).map_err(|e| match e {
              Some(e) => Error::data(e),
              None => Error::ChecksumMismatch,
            })?;
            manifest.insert(ent).map_err(Error::manifest)?;
          }
          curosr += len + CHECKSUM_SIZE;
        }
        Err(e) if e.is_eof() => break,
        Err(e) => return Err(Error::io(e)),
      }
    }

    let mut this = Self {
      file,
      manifest,
      _checksumer: core::marker::PhantomData,
      opts,
    };

    if this.should_rewrite() {
      return this.rewrite().map(|_| this);
    }

    Ok(this)
  }

  #[inline]
  fn append_in(&mut self, entry: Entry<M::Data>) -> Result<(), Error<F, M>> {
    if self.should_rewrite() {
      self.rewrite()?;
    }

    append::<F, M, C>(&mut self.file, &entry, self.opts.sync_on_write)
      .and_then(|_| self.manifest.insert(entry).map_err(Error::manifest))
  }

  fn rewrite(&mut self) -> Result<(), Error<F, M>> {
    let old = mem::take(&mut self.manifest);

    // truncate the file
    self
      .file
      .truncate(MANIFEST_HEADER_SIZE as u64)
      .map_err(Error::io)?;

    for ent in old.into_iter() {
      if ent.flag.is_creation() {
        append::<F, M, C>(&mut self.file, &ent, self.opts.sync_on_write)
          .and_then(|_| self.manifest.insert(ent).map_err(Error::manifest))?;
      }
    }

    self.file.flush().map_err(Error::io)?;
    self.file.sync_all().map_err(Error::io)?;
    Ok(())
  }

  #[inline]
  fn should_rewrite(&self) -> bool {
    let deletions = self.manifest.deletions();
    let creations = self.manifest.creations();
    deletions > self.opts.rewrite_threshold
      && deletions > MANIFEST_DELETIONS_RATIO * creations.saturating_sub(deletions)
  }
}

fn append<F: BackedFile, M: BackedManifest, C: Checksumer>(
  file: &mut F,
  ent: &Entry<M::Data>,
  sync: bool,
) -> Result<(), Error<F, M>> {
  let encoded_len = ent.data.encoded_size();
  if encoded_len + FIXED_MANIFEST_ENTRY_SIZE > MAX_INLINE_SIZE {
    let mut buf = Vec::with_capacity(encoded_len + FIXED_MANIFEST_ENTRY_SIZE);
    ent
      .encode::<C>(encoded_len, &mut buf)
      .map_err(Error::data)?;
    file
      .write_all(&buf)
      .and_then(|_| if sync { file.flush() } else { Ok(()) })
      .map_err(Error::io)
  } else {
    let mut buf = [0; MAX_INLINE_SIZE];
    let buf = &mut buf[..encoded_len + FIXED_MANIFEST_ENTRY_SIZE];
    ent.encode::<C>(encoded_len, buf).map_err(Error::data)?;

    file
      .write_all(buf)
      .and_then(|_| if sync { file.flush() } else { Ok(()) })
      .map_err(Error::io)
  }
}
