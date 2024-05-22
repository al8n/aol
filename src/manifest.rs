/// [`Manifest`](crate::manifest::Manifest) implementors for Wisckey WALs.
#[cfg(any(feature = "std", feature = "hashbrown"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "hashbrown"))))]
pub mod wisckey;

use super::*;

/// The manifest trait.
pub trait Manifest: Default {
  /// The data type.
  type Data: Data;

  /// Insert a new entry.
  fn insert(&mut self, entry: Entry<Self::Data>);

  /// Iterate over the entries.
  fn into_iter(self) -> impl Iterator<Item = Entry<Self::Data>>;

  /// Returns the number of deletions.
  fn deletions(&self) -> u64;

  /// Returns the number of creations.
  fn creations(&self) -> u64;

  /// Returns the latest file id.
  /// 
  /// The semantics of this method is similar to `AtomicU32::load(ordering)`.
  fn latest(&self) -> u32;

  /// Returns the next file id.
  /// 
  /// The semantics of this method is similar to `AtomicU32::fetch_add(1, ordering)`.
  fn next(&self) -> u32;
}
