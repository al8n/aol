#![doc = include_str!("../README.md")]
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs, warnings)]
#![allow(clippy::type_complexity)]

#[cfg(not(any(feature = "std", feature = "alloc")))]
compile_error!("`aol` cannot be compiled when both `std` is disabled.");

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "std")]
use core::mem;

mod types;
pub use types::*;

mod impls;

pub use dbutils::{checksum, leb128};
pub use either;

/// A vacant buffer that can be filled with bytes.
pub mod buffer {
  pub use dbutils::{buffer::VacantBuffer, error::*};
}

/// Append-only log implementation based on [`std::fs`].
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod fs;
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use fs::*;

#[cfg(feature = "std")]
const MAGIC_LEN: usize = mem::size_of::<u16>();

/// Magic text for the append only log, this will never be changed.
#[cfg(feature = "std")]
const MAGIC_TEXT: &[u8] = b"aol!";
#[cfg(feature = "std")]
const MAGIC_TEXT_LEN: usize = MAGIC_TEXT.len();
#[cfg(feature = "std")]
const MAGIC_VERSION_LEN: usize = mem::size_of::<u16>();
#[cfg(feature = "std")]
const ENTRY_HEADER_SIZE: usize = 1 + LEN_BUF_SIZE; // flag + len
#[cfg(feature = "std")]
const FIXED_ENTRY_LEN: usize = ENTRY_HEADER_SIZE + CHECKSUM_SIZE; // flag + len + checksum
#[cfg(feature = "std")]
const CHECKSUM_SIZE: usize = mem::size_of::<u64>();
#[cfg(feature = "std")]
const LEN_BUF_SIZE: usize = mem::size_of::<u32>();
#[cfg(feature = "std")]
const HEADER_SIZE: usize = MAGIC_TEXT_LEN + MAGIC_LEN + MAGIC_VERSION_LEN; // magic text + external magic + magic

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
        ///
        /// ## Example
        ///
        /// ```rust
        /// use aol::CustomFlags;
        ///
        /// let mut flags = CustomFlags::empty();
        ///
        #[doc = concat!("flags.set_bit", $num, "();")]
        /// ```
        #[inline]
        pub fn [< set_bit $num >] (&mut self) {
          self.0.insert(CustomFlagsCore::[< BIT $num >]);
        }

        #[doc = concat!("Set the bit", $num,)]
        ///
        /// ## Example
        ///
        /// ```rust
        /// use aol::CustomFlags;
        ///
        /// let flags = CustomFlags::empty();
        ///
        #[doc = concat!("let flags = flags.with_bit", $num, "();")]
        #[doc = concat!("assert!(flags.bit", $num, "());")]
        /// ```
        #[inline]
        pub const fn [< with_bit $num >] (self) -> Self {
          Self(self.0.union(CustomFlagsCore::[< BIT $num >]))
        }

        #[doc = concat!("Clear the bit", $num)]
        ///
        /// ## Example
        ///
        /// ```rust
        /// use aol::CustomFlags;
        ///
        /// let mut flags = CustomFlags::all();
        ///
        #[doc = concat!("flags.clear_bit", $num, "();")]
        #[doc = concat!("assert_eq!(flags.bit", $num, "(), false);")]
        /// ```
        #[inline]
        pub fn [< clear_bit $num >](&mut self) {
          self.0.remove(CustomFlagsCore::[< BIT $num >]);
        }

        #[doc = concat!("Returns `true` if the bit", $num, " is set.")]
        ///
        /// ## Example
        ///
        /// ```rust
        /// use aol::CustomFlags;
        ///
        /// let flags = CustomFlags::all();
        ///
        #[doc = concat!("assert_eq!(flags.bit", $num, "(), true);")]
        /// ```
        #[inline]
        pub const fn [< bit $num >](&self) -> bool {
          self.0.contains(CustomFlagsCore::[< BIT $num >])
        }
      }
    )*
  };
}

macro_rules! flags_api {
  ($($name:ident: #[$doc:meta]), +$(,)?) => {
    $(
      paste::paste! {
        #[$doc]
        ///
        /// ## Example
        ///
        /// ```rust
        /// use aol::CustomFlags;
        ///
        /// let flags1 = CustomFlags::all();
        /// let flags2 = CustomFlags::empty();
        ///
        #[doc = "let flags = flags1." $name "(flags2);"]
        /// ```
        #[inline]
        pub const fn $name(&self, other: Self) -> Self {
          Self(CustomFlagsCore::from_bits_retain((self.0.$name(other.0).bits() & MASK)))
        }
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
  /// ## Example
  ///
  /// ```rust
  /// use aol::CustomFlags;
  ///
  /// let flags = CustomFlags::all();
  /// ```
  #[inline]
  pub const fn all() -> Self {
    Self(CustomFlagsCore::from_bits_retain(
      CustomFlagsCore::all().bits() & MASK,
    ))
  }

  /// Get a flags value with all known bits unset.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::CustomFlags;
  ///
  /// let flags = CustomFlags::empty();
  /// ```
  #[inline]
  pub const fn empty() -> Self {
    Self(CustomFlagsCore::empty())
  }

  /// Whether all set bits in a source flags value are also set in a target flags value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::CustomFlags;
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
  /// ## Example
  ///
  /// ```rust
  /// use aol::CustomFlags;
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
  /// ## Example
  ///
  /// ```rust
  /// use aol::CustomFlags;
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
  /// ## Example
  ///
  /// ```rust
  /// use aol::CustomFlags;
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
  /// ## Example
  ///
  /// ```rust
  /// use aol::CustomFlags;
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
    union: #[doc = "The bitwise intersection (`|`) of the bits in two flags values."],
    intersection: #[doc = "The bitwise intersection (`&`) of the bits in two flags values."],
    difference: #[doc = concat!("The intersection of a source flags value with the complement of a target flags value (`&!`).", "\n\n",
    "This method is not equivalent to `self & !other` when `other` has unknown bits set. difference won't truncate other, but the `!` operator will.")],
    symmetric_difference: #[doc = "The bitwise exclusive-or (`^`) of the bits in two flags values."],
  }

  bits_api!(1, 2, 3, 4, 5, 6, 7);

  #[inline]
  const fn bits(&self) -> u8 {
    self.0.bits()
  }
}

/// Flags for the snapshot entry.
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
  /// ## Example
  ///
  /// ```rust
  /// use aol::EntryFlags;
  ///
  /// let entry = EntryFlags::creation();
  ///
  /// assert_eq!(entry.is_creation(), true);
  /// ```
  #[inline]
  pub const fn creation() -> Self {
    Self::creation_with_custom_flag(CustomFlags::empty())
  }

  /// Creates a new [`EntryFlags`] with the deletion flag set
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::EntryFlags;
  ///
  /// let entry = EntryFlags::deletion();
  ///
  /// assert_eq!(entry.is_deletion(), true);
  /// ```
  #[inline]
  pub const fn deletion() -> Self {
    Self::deletion_with_custom_flag(CustomFlags::empty())
  }

  /// Creates a new [`EntryFlags`] with the deletion flag set
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{EntryFlags, CustomFlags};
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
  /// ## Example
  ///
  /// ```rust
  /// use aol::{EntryFlags, CustomFlags};
  ///
  /// let entry = EntryFlags::creation_with_custom_flag(CustomFlags::empty());
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
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{EntryFlags, CustomFlags};
  ///
  /// let entry = EntryFlags::creation_with_custom_flag(CustomFlags::empty());
  ///
  /// assert_eq!(entry.custom_flag(), CustomFlags::empty());
  /// ```
  #[inline]
  pub const fn custom_flag(&self) -> CustomFlags {
    CustomFlags(CustomFlagsCore::from_bits_retain(self.value & MASK))
  }

  /// Set the custom flag
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{EntryFlags, CustomFlags};
  ///
  /// let mut entry = EntryFlags::creation_with_custom_flag(CustomFlags::empty());
  ///
  /// entry.set_custom_flag(CustomFlags::all());
  ///
  /// assert_eq!(entry.custom_flag(), CustomFlags::all());
  /// ```
  #[inline]
  pub fn set_custom_flag(&mut self, flag: CustomFlags) {
    // Directly set the custom flags without shifting.
    self.value = (flag.bits() & MASK) | (self.value & DELETE_FLAG);
  }

  /// Returns `true` if the entry is a deletion.
  #[inline]
  pub const fn is_deletion(&self) -> bool {
    (self.value & DELETE_FLAG) != 0
  }

  /// Returns `true` if the entry is a creation.
  #[inline]
  pub const fn is_creation(&self) -> bool {
    (self.value & DELETE_FLAG) == 0
  }

  /// Get the underlying bits value.
  ///
  /// The returned value is exactly the bits set in this flags value.
  #[inline]
  pub const fn bits(&self) -> u8 {
    self.value
  }

  // Creates a new EntryFlags with initial value (excluding the first bit)
  #[inline]
  const fn new(flag: CustomFlags) -> Self {
    Self {
      value: flag.bits() & MASK,
    }
  }
}

/// Rewrite policy.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum RewritePolicy {
  /// Keep all entries which are not marked as deleted. When using this policy,
  /// after the rewrite, the append-only log will be compacted, which only contains
  /// the entries that are not marked as deleted.
  #[default]
  All,
  /// Skip the first `usize` entries.
  /// This policy is useful when you want to keep the latest entries.
  ///
  /// e.g. If the a log contains 10 entries, and you set the policy to `Skip(5)`,
  /// and the first 3 entries are marked as deleted, the remaining is in good state,
  /// after the rewrite, the log will only contain 2 entries.
  Skip(usize),
}

/// A batch of entries.
pub trait Batch<I, R> {
  /// The iterator type which yields references to the entries.
  type Iter<'a>: Iterator<Item = &'a I>
  where
    Self: 'a,
    R: 'a,
    I: AsRef<Entry<R>> + 'a;

  /// The iterator type which yields owned entries.
  type IntoIter: Iterator<Item = I>
  where
    I: Into<Entry<R>>;

  /// Returns the number of entries in the batch.
  fn len(&self) -> usize;

  /// Returns `true` if the batch is empty.
  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns an iterator which yields references to the entries.
  fn iter<'a>(&'a self) -> Self::Iter<'a>
  where
    R: 'a,
    I: AsRef<Entry<R>> + 'a;

  /// Returns an iterator which yields owned entries.
  fn into_iter(self) -> Self::IntoIter
  where
    I: Into<Entry<R>>;
}

macro_rules! batch_impl {
  ($ty:ty) => {
    type Iter<'a>
      = ::core::slice::Iter<'a, I>
    where
      R: 'a,
      Self: 'a,
      I: AsRef<Entry<R>> + 'a;
    type IntoIter
      = <$ty as ::core::iter::IntoIterator>::IntoIter
    where
      I: Into<Entry<R>>;

    #[inline]
    fn len(&self) -> usize {
      <[I]>::len(self)
    }

    #[inline]
    fn is_empty(&self) -> bool {
      <[I]>::is_empty(self)
    }

    #[inline]
    fn iter<'a>(&'a self) -> Self::Iter<'a>
    where
      R: 'a,
      I: AsRef<Entry<R>> + 'a,
    {
      <[I]>::iter(self)
    }

    #[inline]
    fn into_iter(self) -> Self::IntoIter
    where
      I: Into<Entry<R>>,
    {
      ::core::iter::IntoIterator::into_iter(self)
    }
  };
}

macro_rules! impl_batch_for_vec {
  ($($ty:ty), +$(,)?) => {
    $(
      impl<I, R> $crate::Batch<I, R> for $ty
      where
        I: AsRef<I> + Into<I>,
      {
        batch_impl!($ty);
      }
    )*
  };
}

impl_batch_for_vec!(::std::vec::Vec<I>, ::std::boxed::Box<[I]>,);

#[cfg(feature = "smallvec-wrapper")]
mod sw {
  use smallvec_wrapper::*;

  use super::Entry;

  impl_batch_for_vec!(
    OneOrMore<I>,
    TinyVec<I>,
    TriVec<I>,
    SmallVec<I>,
    MediumVec<I>,
    LargeVec<I>,
    XLargeVec<I>,
    XXLargeVec<I>,
    XXXLargeVec<I>,
  );
}

macro_rules! impl_batch_for_array {
  ($($ty:ty), +$(,)?) => {
    $(
      impl<I, R, const N: usize> $crate::Batch<I, R> for $ty {
        batch_impl!($ty);
      }
    )*
  };
}

impl_batch_for_array!([I; N]);

#[cfg(feature = "smallvec")]
impl_batch_for_array!(::smallvec::SmallVec<[I; N]>);

#[cfg(feature = "std")]
#[inline]
fn read_only_error() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::PermissionDenied, "append log read-only")
}
