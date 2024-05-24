/// [`Manifest`](crate::manifest::Manifest) implementors for Wisckey WALs.
#[cfg(any(feature = "std", feature = "hashbrown"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "hashbrown"))))]
pub mod wiscask;

/// [`Manifest`](crate::manifest::Manifest) implementors for Wisckey WALs based on LSM model.
pub mod lsm;

use super::*;

/// The manifest trait.
pub trait Manifest: Default {
  /// The data type.
  type Data: Data;

  /// The error type.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// The error type.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Insert a new entry.
  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  /// Iterate over the entries.
  fn into_iter(self) -> impl Iterator<Item = Entry<Self::Data>>;

  /// Returns the number of deletions.
  fn deletions(&self) -> u64;

  /// Returns the number of creations.
  fn creations(&self) -> u64;
}
