use super::*;

/// Options for the append-only log.
#[derive(Debug, Clone, Copy)]
pub struct Options {
  minimum_capacity: usize,
}

impl Options {
  /// Create a new `Options`.
  #[inline]
  pub const fn new(minimum_capacity: usize) -> Self {
    Self { minimum_capacity }
  }

  /// Returns the minimum capacity.
  #[inline]
  pub const fn minimum_capacity(&self) -> usize {
    self.minimum_capacity
  }
}

/// The snapshot trait, which contains the information about the append-only log.
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

  /// Open a new snapshot.
  fn open(opts: Self::Options) -> Result<Self, Self::Error>;

  /// Returns the options.
  fn options(&self) -> &Self::Options;

  /// Returns `true` if the snapshot should trigger rewrite.
  ///
  /// `size` is the current size of the append-only log.
  fn should_rewrite(&self) -> bool;

  /// Insert a new entry.
  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;

  /// Insert a batch of entries.
  fn insert_batch(
    &mut self,
    entries: impl Iterator<Item = Entry<Self::Data>>,
  ) -> Result<(), Self::Error>;

  /// Iterate over the entries.
  fn into_iter(self) -> impl Iterator<Item = Entry<Self::Data>>;
}

/// In-memory generic append-only log implementation.
#[derive(Debug)]
pub struct AppendLog<S> {
  snapshot: S,
}

impl<S> AppendLog<S> {
  /// Returns the current snapshot.
  #[inline]
  pub const fn snapshot(&self) -> &S {
    &self.snapshot
  }
}

impl<S: Snapshot> AppendLog<S> {
  /// Open and replay the append only log.
  #[inline]
  pub fn open(snapshot_opts: S::Options) -> Result<Self, S::Error> {
    Ok(Self {
      snapshot: S::open(snapshot_opts)?,
    })
  }

  /// Append an entry to the append-only file.
  #[inline]
  pub fn append(&mut self, ent: Entry<S::Data>) -> Result<(), S::Error> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(
    &mut self,
    entries: impl Iterator<Item = Entry<S::Data>>,
  ) -> Result<(), S::Error> {
    if self.snapshot.should_rewrite() {
      self.rewrite()?;
    }

    self.snapshot.insert_batch(entries)
  }

  #[inline]
  fn append_in(&mut self, entry: Entry<S::Data>) -> Result<(), S::Error> {
    if self.snapshot.should_rewrite() {
      self.rewrite()?;
    }

    self.snapshot.insert(entry)
  }

  #[inline]
  fn rewrite(&mut self) -> Result<(), S::Error> {
    let snapshot_opts = self.snapshot.options().clone();
    let snapshot = S::open(snapshot_opts)?;
    let old = mem::replace(&mut self.snapshot, snapshot);

    for ent in old.into_iter() {
      if ent.flag.is_creation() {
        self.snapshot.insert(ent)?;
      }
    }

    Ok(())
  }
}
