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

/// In memory manifest file implementation.
pub mod memory;

/// Manifest file implementation based on [`std::fs::File`](std::fs::File).
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub mod file;

/// Manifest file implementation based on memory map.
#[cfg(feature = "memmap2")]
#[cfg_attr(docsrs, doc(cfg(feature = "memmap2")))]
pub mod memmap;

/// Some [`Manifest`](crate::manifest::Manifest) implementations.
pub mod manifest;
use manifest::Manifest;

const MANIFEST_DELETIONS_REWRITE_THRESHOLD: u64 = 10000;
const MANIFEST_DELETIONS_RATIO: u64 = 10;

/// Magic text for the manifest file, this will never be changed.
const MAGIC_TEXT: &[u8] = b"al8n";
const MAGIC_TEXT_LEN: usize = MAGIC_TEXT.len();
const MAGIC_LEN: usize = mem::size_of::<u16>();
const EXTERNAL_MAGIC_LEN: usize = mem::size_of::<u16>();
const MANIFEST_HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_LEN + EXTERNAL_MAGIC_LEN; // magic text + external magic + magic
const FIXED_MANIFEST_ENTRY_SIZE: usize = 1 + FID_SIZE + CHECKSUM_SIZE; // flag + fid + checksum
const MAX_INLINE_SIZE: usize = 64;
const FID_SIZE: usize = mem::size_of::<u32>();
const CHECKSUM_SIZE: usize = mem::size_of::<u32>();

const DELETE_FLAG: u8 = 0b00000001;
const MASK: u8 = 0b11111110;
const CUSTOM_CORE_MASK: CustomFlagCore = CustomFlagCore::from_bits_retain(MASK);

bitflags::bitflags! {
  #[derive(Default, PartialEq, Eq, Copy, Clone, Hash)]
  struct CustomFlagCore: u8 {
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
pub struct CustomFlag(CustomFlagCore);

impl core::fmt::Debug for CustomFlag {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("CustomFlag")
      .field(&(self.0.bits() & MASK))
      .finish()
  }
}

impl core::fmt::Display for CustomFlag {
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
          self.0.insert(CustomFlagCore::[< BIT $num >]);
        }

        #[doc = concat!("Clear the bit", $num,)]
        #[inline]
        pub fn [< clear_bit $num >](&mut self) {
          self.0.remove(CustomFlagCore::[< BIT $num >]);
        }

        #[doc = concat!("Returns `true` if the bit", $num, " is set.")]
        #[inline]
        pub const fn [< bit $num >](&self) -> bool {
          self.0.contains(CustomFlagCore::[< BIT $num >])
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
        Self(CustomFlagCore::from_bits_retain((self.0.$name(other.0).bits() & MASK)))
      }
    )*
  };
}

macro_rules! impl_bitwise_ops {
  ($($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident),+ $(,)?) => {
    $(
      impl core::ops::$trait for CustomFlag {
        type Output = Self;

        #[inline]
        fn $method(self, rhs: Self) -> Self::Output {
          #[allow(clippy::suspicious_arithmetic_impl)]
          Self(self.0.$method(rhs.0) & CUSTOM_CORE_MASK)
        }
      }

      impl core::ops::$assign_trait for CustomFlag {
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

impl core::ops::Not for CustomFlag {
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

impl CustomFlag {
  /// Get a flags value with all known bits set.
  #[inline]
  pub const fn all() -> Self {
    Self(CustomFlagCore::all())
  }

  /// Get a flags value with all known bits unset.
  #[inline]
  pub const fn empty() -> Self {
    Self(CustomFlagCore::empty())
  }

  /// Whether all set bits in a source flags value are also set in a target flags value.
  #[inline]
  pub const fn contains(&self, other: Self) -> bool {
    self.0.contains(other.0)
  }

  /// The bitwise exclusive-or (`^`) of the bits in two flags values.
  #[inline]
  pub fn toggle(&mut self, other: Self) {
    self.0.toggle(other.0);
    self.0 &= CUSTOM_CORE_MASK;
  }

  /// The bitwise negation (`!`) of the bits in a flags value, truncating the result.
  #[inline]
  pub const fn complement(&self) -> Self {
    Self(CustomFlagCore::from_bits_retain(
      self.0.complement().bits() & MASK,
    ))
  }

  /// Whether all bits in this flags value are unset.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.0.is_empty()
  }

  /// Whether any bits in this flags value are set.
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
  /// Creates a new [`EntryFlags`] with the deletion flag set
  #[inline]
  pub const fn deletion(flag: CustomFlag) -> Self {
    let mut this = Self::new(flag);
    this.value |= DELETE_FLAG;
    this
  }

  /// Creates a new [`EntryFlags`] with the creation flag set
  #[inline]
  pub const fn creation(flag: CustomFlag) -> Self {
    let mut this = Self::new(flag);
    this.value &= !DELETE_FLAG;
    this
  }

  /// Returns the custom flag
  #[inline]
  pub const fn custom_flag(&self) -> CustomFlag {
    CustomFlag(CustomFlagCore::from_bits_retain(self.value >> 1))
  }

  /// Set the custom flag
  #[inline]
  pub fn set_custom_flag(&mut self, flag: CustomFlag) {
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
  const fn new(flag: CustomFlag) -> Self {
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

/// Data for the [`Entry`].
pub trait Data: Sized {
  /// Maximum size of the data.
  const ENCODED_SIZE: usize;

  /// The error type returned by encoding.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// The error type returned by encoding.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Encodes the data into the buffer, returning the number of bytes written.
  fn encode(&self, buf: &mut [u8]) -> Result<usize, Self::Error>;

  /// Decodes the data from the buffer, returning the number of bytes read.
  fn decode(buf: &[u8]) -> Result<(usize, Self), Self::Error>;
}

/// The underlying file.
pub trait File {
  /// Options for opening a manifest file.
  type Options;

  /// Error type for the file.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// Error type for the file.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Open a manifest file with the given options, returning the file and whether it's a new file.
  #[cfg(feature = "std")]
  fn open<P: AsRef<std::path::Path>>(
    path: P,
    opts: Self::Options,
  ) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized;

  #[cfg(not(feature = "std"))]
  fn open(opts: Self::Options) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized;

  /// Read exactly `buf.len()` bytes into the buffer.
  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), Self::Error>;

  /// Write all the data to the file.
  fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error>;

  /// Flush the file.
  fn flush(&mut self) -> Result<(), Self::Error>;

  /// Sync the file.
  fn sync_all(&self) -> Result<(), Self::Error>;

  /// Truncate the file.
  fn truncate(&mut self, len: u64) -> Result<(), Self::Error>;

  /// Returns the size of the file.
  fn size(&self) -> Result<u64, Self::Error>;
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
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Options {
  /// Create a new Options with the given file options
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
  #[inline]
  pub const fn external_magic(&self) -> u16 {
    self.external_magic
  }

  /// Get the magic.
  #[inline]
  pub const fn magic(&self) -> u16 {
    self.magic
  }

  /// Get the rewrite threshold.
  #[inline]
  pub const fn rewrite_threshold(&self) -> u64 {
    self.rewrite_threshold
  }

  /// Get the deletions ratio.
  #[inline]
  pub const fn deletions_ratio(&self) -> u64 {
    self.deletions_ratio
  }

  /// Get whether flush the data to disk after write.
  ///
  /// Default is `true`.
  #[inline]
  pub const fn sync_on_write(&self) -> bool {
    self.sync_on_write
  }

  /// Set the external magic.
  #[inline]
  pub const fn with_external_magic(mut self, external_magic: u16) -> Self {
    self.external_magic = external_magic;
    self
  }

  /// Set the magic.
  #[inline]
  pub const fn with_magic(mut self, magic: u16) -> Self {
    self.magic = magic;
    self
  }

  /// Set the rewrite threshold.
  #[inline]
  pub const fn with_rewrite_threshold(mut self, rewrite_threshold: u64) -> Self {
    self.rewrite_threshold = rewrite_threshold;
    self
  }

  /// Set the deletions ratio.
  #[inline]
  pub const fn with_deletions_ratio(mut self, deletions_ratio: u64) -> Self {
    self.deletions_ratio = deletions_ratio;
    self
  }

  /// Set whether flush the data to disk after write.
  ///
  ///  Default is `true`.
  #[inline]
  pub const fn with_sync_on_write(mut self, sync_on_write: bool) -> Self {
    self.sync_on_write = sync_on_write;
    self
  }
}

/// The entry in the manifest file.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Entry<D> {
  flag: EntryFlags,
  fid: u32,
  data: D,
}

impl<D> Entry<D> {
  /// Get the flag.
  #[inline]
  pub const fn flag(&self) -> EntryFlags {
    self.flag
  }

  /// Get the file id.
  #[inline]
  pub const fn fid(&self) -> u32 {
    self.fid
  }

  /// Get the data.
  #[inline]
  pub const fn data(&self) -> &D {
    &self.data
  }

  #[inline]
  fn encode<C>(&self, buf: &mut [u8]) -> Result<usize, D::Error>
  where
    C: Checksumer,
    D: Data,
  {
    let mut cursor = 0;
    buf[cursor] = self.flag.value;
    cursor += 1;
    buf[cursor..cursor + FID_SIZE].copy_from_slice(&self.fid.to_le_bytes());
    cursor += FID_SIZE;
    let encoded = self.data.encode(&mut buf[cursor..])?;
    let cks = C::checksum(&buf[..cursor + encoded]).to_le_bytes();
    cursor += D::ENCODED_SIZE;
    buf[cursor..cursor + CHECKSUM_SIZE].copy_from_slice(&cks);
    cursor += CHECKSUM_SIZE;

    debug_assert_eq!(
      cursor,
      FIXED_MANIFEST_ENTRY_SIZE + D::ENCODED_SIZE,
      "invalid encoded size, expected {} got {}",
      cursor,
      FIXED_MANIFEST_ENTRY_SIZE + D::ENCODED_SIZE
    );
    Ok(cursor)
  }

  #[inline]
  fn decode<C>(buf: &[u8]) -> Result<Self, Option<D::Error>>
  where
    C: Checksumer,
    D: Data,
  {
    let flag = EntryFlags { value: buf[0] };

    let mut cursor = 1;
    let fid = u32::from_le_bytes(buf[cursor..cursor + FID_SIZE].try_into().unwrap());
    cursor += FID_SIZE;
    let (read, data) = D::decode(&buf[cursor..cursor + D::ENCODED_SIZE]).map_err(Some)?;
    let cks = C::checksum(&buf[..cursor + read]).to_le_bytes();
    cursor += D::ENCODED_SIZE;
    if cks != buf[cursor..cursor + CHECKSUM_SIZE] {
      return Err(None);
    }

    Ok(Self { flag, fid, data })
  }
}

/// Generic manifest file implementation.
///
/// File structure:
///
/// ```text
/// +----------------------+--------------------------+-----------------------+
/// | magic text (4 bytes) | external magic (2 bytes) | magic (2 bytes)       |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | op (1 bit)           | custom flag (7 bits)     | fid (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | op (1 bit)           | custom flag (7 bits)     | fid (4 bytes)         | data (n bytes)        | checksum (4 bytes)    |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// | ...                  | ...                      | ...                   | ...                   | ...                   |
/// +----------------------+--------------------------+-----------------------+-----------------------+-----------------------+
/// ```
#[derive(Debug)]
pub struct ManifestFile<F: File, M, C = Crc32> {
  opts: Options,
  file: F,
  manifest: M,
  _checksumer: core::marker::PhantomData<C>,
}

impl<F, M, C> Clone for ManifestFile<F, M, C>
where
  F::Options: Clone,
  F: File + Clone,
  M: Clone,
  C: Clone,
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

impl<F: File, M: Manifest, C: Checksumer> ManifestFile<F, M, C> {
  /// Open and replay the manifest file.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open<P: AsRef<std::path::Path>>(
    path: P,
    file_opts: F::Options,
    opts: Options,
  ) -> Result<Self, Error<F, M::Data>> {
    let (existing, file) = F::open(path, file_opts).map_err(Error::io)?;

    Self::open_in(file, existing, opts)
  }

  /// Open and replay the manifest file.
  #[cfg(not(feature = "std"))]
  #[inline]
  pub fn open(file_opts: F::Options, opts: Options) -> Result<Self, Error<F, M::Data>> {
    let (existing, file) = F::open(file_opts).map_err(Error::io)?;

    Self::open_in(file, existing, opts)
  }

  /// Flush the manifest file.
  #[inline]
  pub fn flush(&mut self) -> Result<(), Error<F, M::Data>> {
    self.file.flush().map_err(Error::io)
  }

  /// Sync the manifest file.
  #[inline]
  pub fn sync_all(&self) -> Result<(), Error<F, M::Data>> {
    self.file.sync_all().map_err(Error::io)
  }

  /// Returns the options of the manifest file.
  #[inline]
  pub const fn options(&self) -> &Options {
    &self.opts
  }

  /// Returns the latest fid.
  #[inline]
  pub fn latest(&self) -> u32 {
    self.manifest.latest()
  }

  /// Returns the next fid.
  #[inline]
  pub fn next(&self) -> u32 {
    self.manifest.next()
  }

  /// Append an entry to the manifest file.
  #[inline]
  pub fn append(&mut self, ent: Entry<M::Data>) -> Result<(), Error<F, M::Data>> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the manifest file.
  #[inline]
  pub fn append_batch(&mut self, entries: Vec<Entry<M::Data>>) -> Result<(), Error<F, M::Data>> {
    if self.should_rewrite() {
      self.rewrite()?;
    }

    let total_encoded_size = M::Data::ENCODED_SIZE * entries.len();

    macro_rules! encode_batch {
      ($buf:ident) => {{
        let mut cursor = 0;
        for ent in entries {
          cursor += ent.encode::<C>(&mut $buf[cursor..]).map_err(Error::data)?;
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

  fn open_in(mut file: F, existing: bool, opts: Options) -> Result<Self, Error<F, M::Data>> {
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

    let encoded_entry_size = FIXED_MANIFEST_ENTRY_SIZE + M::Data::ENCODED_SIZE;

    let num_entries = (size - MANIFEST_HEADER_SIZE as u64) / encoded_entry_size as u64;
    let remaining = (size - MANIFEST_HEADER_SIZE as u64) % encoded_entry_size as u64;
    if remaining != 0 {
      return Err(Error::Corrupted);
    }

    let mut manifest = M::default();

    for _ in 0..num_entries {
      let ent = if encoded_entry_size > MAX_INLINE_SIZE {
        let mut buf = std::vec![0; encoded_entry_size];
        file.read_exact(&mut buf).map_err(Error::io)?;
        Entry::decode::<C>(&buf).map_err(|e| match e {
          Some(e) => Error::data(e),
          None => Error::ChecksumMismatch,
        })?
      } else {
        let mut buf = [0; MAX_INLINE_SIZE];
        file.read_exact(&mut buf).map_err(Error::io)?;

        Entry::decode::<C>(&buf[..FIXED_MANIFEST_ENTRY_SIZE + M::Data::ENCODED_SIZE]).map_err(
          |e| match e {
            Some(e) => Error::data(e),
            None => Error::ChecksumMismatch,
          },
        )?
      };

      manifest.insert(ent);
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
  fn append_in(&mut self, entry: Entry<M::Data>) -> Result<(), Error<F, M::Data>> {
    if self.should_rewrite() {
      self.rewrite()?;
    }

    append::<F, M, C>(&mut self.file, &entry, self.opts.sync_on_write)
      .map(|_| self.manifest.insert(entry))
  }

  fn rewrite(&mut self) -> Result<(), Error<F, M::Data>> {
    let old = mem::take(&mut self.manifest);

    // truncate the file
    self
      .file
      .truncate(MANIFEST_HEADER_SIZE as u64)
      .map_err(Error::io)?;

    for ent in old.into_iter() {
      if ent.flag.is_creation() {
        append::<F, M, C>(&mut self.file, &ent, self.opts.sync_on_write).map(|_| {
          self.manifest.insert(ent);
        })?;
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

fn append<F: File, M: Manifest, C: Checksumer>(
  file: &mut F,
  ent: &Entry<M::Data>,
  sync: bool,
) -> Result<(), Error<F, M::Data>> {
  if M::Data::ENCODED_SIZE + FIXED_MANIFEST_ENTRY_SIZE > MAX_INLINE_SIZE {
    let mut buf = Vec::with_capacity(M::Data::ENCODED_SIZE + FIXED_MANIFEST_ENTRY_SIZE);
    ent.encode::<C>(&mut buf).map_err(Error::data)?;
    file
      .write_all(&buf)
      .and_then(|_| if sync { file.flush() } else { Ok(()) })
      .map_err(Error::io)
  } else {
    let mut buf = [0; MAX_INLINE_SIZE];
    let encoded = ent
      .encode::<C>(&mut buf[..FIXED_MANIFEST_ENTRY_SIZE + M::Data::ENCODED_SIZE])
      .map_err(Error::data)?;
    file
      .write_all(&buf[..encoded])
      .and_then(|_| if sync { file.flush() } else { Ok(()) })
      .map_err(Error::io)
  }
}
