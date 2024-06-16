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

/// The manifest trait, which contains the information about the append-only log.
pub trait Manifest: Sized {
  /// The data type.
  type Data: Data;

  /// The options type used to create a new manifest.
  type Options: Clone;

  /// The error type.
  #[cfg(feature = "std")]
  type Error: std::error::Error;

  /// The error type.
  #[cfg(not(feature = "std"))]
  type Error: core::fmt::Debug + core::fmt::Display;

  /// Open a new manifest.
  fn open(opts: Self::Options) -> Result<Self, Self::Error>;

  /// Returns the options.
  fn options(&self) -> &Self::Options;

  /// Returns `true` if the manifest should trigger rewrite.
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
pub struct AppendLog<M> {
  manifest: M,
}

impl<M> AppendLog<M> {
  /// Returns the current manifest.
  #[inline]
  pub const fn manifest(&self) -> &M {
    &self.manifest
  }
}

impl<M: Manifest> AppendLog<M> {
  /// Open and replay the manifest file.
  #[cfg(feature = "std")]
  #[inline]
  pub fn open(manifest_opts: M::Options) -> Result<Self, M::Error> {
    Ok(Self {
      manifest: M::open(manifest_opts)?,
    })
  }

  /// Append an entry to the append-only file.
  #[inline]
  pub fn append(&mut self, ent: Entry<M::Data>) -> Result<(), M::Error> {
    self.append_in(ent)
  }

  /// Append a batch of entries to the append-only file.
  pub fn append_batch(
    &mut self,
    entries: impl Iterator<Item = Entry<M::Data>>,
  ) -> Result<(), M::Error> {
    if self.manifest.should_rewrite() {
      self.rewrite()?;
    }

    self.manifest.insert_batch(entries)
  }

  #[inline]
  fn append_in(&mut self, entry: Entry<M::Data>) -> Result<(), M::Error> {
    if self.manifest.should_rewrite() {
      self.rewrite()?;
    }

    self.manifest.insert(entry)
  }

  #[inline]
  fn rewrite(&mut self) -> Result<(), M::Error> {
    let manifest_opts = self.manifest.options().clone();
    let manifest = M::open(manifest_opts)?;
    let old = mem::replace(&mut self.manifest, manifest);

    for ent in old.into_iter() {
      if ent.flag.is_creation() {
        self.manifest.insert(ent)?;
      }
    }

    Ok(())
  }
}
