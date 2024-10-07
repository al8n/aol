use either::Either;

use super::{Entry, MaybeEntryRef, Record};

/// The snapshot trait, snapshot may contain some in-memory information about the append-only log.
pub trait Snapshot: Sized {
  /// The data type.
  type Record: Record;

  /// The options type used to create a new snapshot.
  type Options: Clone;

  /// The error type.
  type Error;

  /// Create a new snapshot.
  fn new(opts: Self::Options) -> Result<Self, Self::Error>;

  /// Returns `true` if the snapshot should trigger rewrite.
  ///
  /// `size` is the current size of the append-only log.
  fn should_rewrite(&self, size: u64) -> bool;

  /// Validate the entry, return an error if the entry is invalid.
  ///
  /// This method will be run before persisting entry to the underlying append-only log.
  fn validate(
    &self,
    entry: &Entry<Self::Record>,
  ) -> Result<(), Either<<Self::Record as Record>::Error, Self::Error>>;

  /// Validate the batch of entries, return an error if the batch is invalid.
  ///
  /// This method will be run before persisting batch to the underlying append-only log.
  #[inline]
  fn validate_batch<I, B>(
    &self,
    entries: &B,
  ) -> Result<(), Either<<Self::Record as Record>::Error, Self::Error>>
  where
    B: Batch<I, Self::Record>,
    I: AsRef<Entry<Self::Record>> + Into<Entry<Self::Record>>,
  {
    for entry in entries.iter() {
      self.validate(entry.as_ref())?;
    }
    Ok(())
  }

  /// Returns `true` if the current snapshot contains the entry.
  fn contains(&self, entry: &Entry<<Self::Record as Record>::Ref<'_>>) -> bool;

  /// Insert a new entry.
  ///
  /// Inserting an entry should not fail, the validation should be done in the [`validate`](Snapshot::validate) method.
  fn insert(&mut self, entry: MaybeEntryRef<'_, Self::Record>);

  /// Insert a batch of entries.
  ///
  /// Inserting a batch of entries should not fail, the validation should be done in the [`validate_batch`](Snapshot::validate_batch) method.
  fn insert_batch<I, B>(&mut self, entries: B)
  where
    B: Batch<I, Self::Record>,
    I: AsRef<Entry<Self::Record>> + Into<Entry<Self::Record>>,
  {
    for entry in entries.into_iter() {
      self.insert(MaybeEntryRef::right(entry.into()));
    }
  }

  /// Clear the snapshot.
  fn clear(&mut self) -> Result<(), Self::Error>;
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
