use std::path::Path;

use among::Among;
use dbutils::checksum::{BuildChecksumer, Crc32};

use super::{AppendLog, Error, Options, Record, RewritePolicy, Snapshot};

/// A builder used to create a [`AppendLog`](super::AppendLog).
pub struct Builder<S = (), C = Crc32>
where
  S: Snapshot,
{
  opts: Options,
  cks: C,
  snapshot_opts: S::Options,
}

impl<S, C> Default for Builder<S, C>
where
  S: Snapshot,
  S::Options: Default,
  C: Default,
{
  #[inline]
  fn default() -> Self {
    Self {
      opts: Options::default(),
      cks: C::default(),
      snapshot_opts: S::Options::default(),
    }
  }
}

impl<S> Builder<S>
where
  S: Snapshot,
{
  /// Creates a new builder with the default options.
  #[inline]
  pub fn new(snapshot_opts: S::Options) -> Self {
    Builder {
      opts: Options::new(),
      cks: Crc32::new(),
      snapshot_opts,
    }
  }
}

impl<S, C> Builder<S, C>
where
  S: Snapshot,
{
  /// Returns a new map builder with the new [`BuildChecksumer`](crate::checksum::BuildChecksumer).
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::{Builder, checksum::Crc32};
  ///
  /// let builder = Builder::default().with_checksumer(Crc32::new());
  /// ```
  #[inline]
  pub fn with_checksumer<NC>(self, cks: NC) -> Builder<S, NC> {
    Builder {
      cks,
      opts: self.opts,
      snapshot_opts: self.snapshot_opts,
    }
  }

  /// Returns a new map builder with the new snapshot options.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let builder = Builder::default().with_snapshot_options(new_snapshot_options);
  /// ```
  #[inline]
  pub fn with_snapshot_options<NS>(self, snapshot_opts: NS::Options) -> Builder<NS, C>
  where
    NS: Snapshot,
  {
    Builder {
      cks: self.cks,
      opts: self.opts,
      snapshot_opts,
    }
  }

  /// Returns the current snapshot options.
  #[inline]
  pub const fn snapshot_options(&self) -> &S::Options {
    &self.snapshot_opts
  }

  /// Returns a new map builder with the new [`Builder`].
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::{Builder, Builder};
  ///
  /// let builder = Builder::default().with_options(Builder::default().with_capacity(1024));
  /// ```
  #[inline]
  pub const fn with_options(mut self, opts: Options) -> Self {
    self.opts = opts;
    self
  }

  /// Get the external magic.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default();
  ///
  /// assert_eq!(opts.magic_version(), 0);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.opts.magic_version
  }

  /// Get whether the append-only log is read-only.
  ///
  /// Default is `false`.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default();
  ///
  /// assert_eq!(opts.read_only(), false);
  /// ```
  #[inline]
  pub const fn read_only(&self) -> bool {
    self.opts.read_only
  }

  /// Get whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default();
  ///
  /// assert_eq!(opts.sync(), true);
  /// ```
  #[inline]
  pub const fn sync(&self) -> bool {
    self.opts.sync
  }

  /// Get the rewrite policy.
  ///
  /// Default is `RewritePolicy::All`.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::{Builder, RewritePolicy};
  ///
  /// let opts = Builder::default().with_rewrite_policy(RewritePolicy::Skip(100));
  ///
  /// assert_eq!(opts.rewrite_policy(), RewritePolicy::Skip(100));
  /// ```
  #[inline]
  pub const fn rewrite_policy(&self) -> RewritePolicy {
    self.opts.rewrite_policy
  }

  /// Set the external magic.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.opts.magic_version = magic_version;
    self
  }

  /// Set whether the append-only log is read-only.
  ///
  /// Default is `false`.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_read_only(true);
  ///
  /// assert_eq!(opts.read_only(), true);
  /// ```
  #[inline]
  pub const fn with_read_only(mut self, read_only: bool) -> Self {
    self.opts.read_only = read_only;
    self
  }

  /// Set whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_sync(false);
  ///
  /// assert_eq!(opts.sync(), false);
  /// ```
  #[inline]
  pub const fn with_sync(mut self, sync: bool) -> Self {
    self.opts.sync = sync;
    self
  }

  /// Set the rewrite policy.
  ///
  /// Default is `RewritePolicy::All`.
  ///
  /// ## Example
  ///
  /// ```rust,ignore
  /// use aol::{Builder, RewritePolicy};
  ///
  /// let opts = Builder::default().with_rewrite_policy(RewritePolicy::Skip(100));
  /// ```
  #[inline]
  pub const fn with_rewrite_policy(mut self, rewrite_policy: RewritePolicy) -> Self {
    self.opts.rewrite_policy = rewrite_policy;
    self
  }
}

impl<S, C> Builder<S, C>
where
  S: Snapshot,
{
  /// Sets the option for read access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `read`-able if opened.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_read(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_read(mut self, read: bool) -> Self {
    self.opts.read = read;
    self
  }

  /// Sets the option for write access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `write`-able if opened.
  ///
  /// If the file already exists, any write calls on it will overwrite its
  /// contents, without truncating it.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_write(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_write(mut self, write: bool) -> Self {
    self.opts.write = write;
    self
  }

  /// Sets the option for the append mode.
  ///
  /// This option, when true, means that writes will append to a file instead
  /// of overwriting previous contents.
  /// Note that setting `.write(true).append(true)` has the same effect as
  /// setting only `.append(true)`.
  ///
  /// For most filesystems, the operating system guarantees that all writes are
  /// atomic: no writes get mangled because another process writes at the same
  /// time.
  ///
  /// One maybe obvious note when using append-mode: make sure that all data
  /// that belongs together is written to the file in one operation. This
  /// can be done by concatenating strings before passing them to [`write()`],
  /// or using a buffered writer (with a buffer of adequate size),
  /// and calling [`flush()`] when the message is complete.
  ///
  /// If a file is opened with both read and append access, beware that after
  /// opening, and after every write, the position for reading may be set at the
  /// end of the file. So, before writing, save the current position (using
  /// <code>[seek]\([SeekFrom](std::io::SeekFrom)::[Current]\(opts))</code>), and restore it before the next read.
  ///
  /// ## Note
  ///
  /// This function doesn't create the file if it doesn't exist. Use the
  /// [`Builder::with_create`] method to do so.
  ///
  /// [`write()`]: std::io::Write::write "io::Write::write"
  /// [`flush()`]: std::io::Write::flush "io::Write::flush"
  /// [seek]: std::io::Seek::seek "io::Seek::seek"
  /// [Current]: std::io::SeekFrom::Current "io::SeekFrom::Current"
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_append(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_append(mut self, append: bool) -> Self {
    self.opts.write = true;
    self.opts.append = append;
    self
  }

  /// Sets the option for truncating a previous file.
  ///
  /// If a file is successfully opened with this option set it will truncate
  /// the file to opts length if it already exists.
  ///
  /// The file must be opened with write access for truncate to work.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_write(true).with_truncate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_truncate(mut self, truncate: bool) -> Self {
    self.opts.truncate = truncate;
    self.opts.write = true;
    self
  }

  /// Sets the option to create a new file, or open it if it already exists.
  /// If the file does not exist, it is created and set the lenght of the file to the given size.
  ///
  /// In order for the file to be created, [`Builder::with_write`] or
  /// [`Builder::with_append`] access must be used.
  ///
  /// See also [`std::fs::write()`][std::fs::write] for a simple function to
  /// create a file with some given data.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_write(true).with_create(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_create(mut self, val: bool) -> Self {
    self.opts.create = val;
    self
  }

  /// Sets the option to create a new file and set the file length to the given value, failing if it already exists.
  ///
  /// No file is allowed to exist at the target location, also no (dangling) symlink. In this
  /// way, if the call succeeds, the file returned is guaranteed to be new.
  ///
  /// This option is useful because it is atomic. Otherwise between checking
  /// whether a file exists and creating a new one, the file may have been
  /// created by another process (a TOCTOU race condition / attack).
  ///
  /// If `.with_create_new(true)` is set, [`.with_create()`](Builder::with_create) and [`.with_truncate()`](Builder::with_truncate) are
  /// ignored.
  ///
  /// The file must be opened with write or append access in order to create
  /// a new file.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let file = Builder::default()
  ///   .with_write(true)
  ///   .with_create_new(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_create_new(mut self, val: bool) -> Self {
    self.opts.create_new = val;
    self
  }

  /// Returns `true` if the file should be opened with read access.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_read(true);
  /// assert_eq!(opts.read(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn read(&self) -> bool {
    self.opts.read
  }

  /// Returns `true` if the file should be opened with write access.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_write(true);
  /// assert_eq!(opts.write(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn write(&self) -> bool {
    self.opts.write
  }

  /// Returns `true` if the file should be opened with append access.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_append(true);
  /// assert_eq!(opts.append(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn append(&self) -> bool {
    self.opts.append
  }

  /// Returns `true` if the file should be opened with truncate access.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_truncate(true);
  /// assert_eq!(opts.truncate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn truncate(&self) -> bool {
    self.opts.truncate
  }

  /// Returns `true` if the file should be created if it does not exist.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_create(true);
  /// assert_eq!(opts.create(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn create(&self) -> bool {
    self.opts.create
  }

  /// Returns `true` if the file should be created if it does not exist and fail if it does.
  ///
  /// ## Examples
  ///
  /// ```rust,ignore
  /// use aol::Builder;
  ///
  /// let opts = Builder::default().with_create_new(true);
  /// assert_eq!(opts.create_new(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn create_new(&self) -> bool {
    self.opts.create_new
  }
}

impl<S, C> Builder<S, C>
where
  C: BuildChecksumer,
  S: Snapshot,
{
  /// Consumes the builder, and constructs a [`AppendLog`].
  pub fn build<P>(
    self,
    path: P,
  ) -> Result<AppendLog<S, C>, Among<<S::Record as Record>::Error, S::Error, Error>>
  where
    P: AsRef<Path>,
  {
    let existing = path.as_ref().exists();
    let path = path.as_ref();
    let mut rewrite_path = path.to_path_buf();
    rewrite_path.set_extension("rewrite");
    let file = self.opts.to_open_options().open(path).map_err(Error::io)?;
    AppendLog::open_in(
      path.to_path_buf(),
      rewrite_path,
      file,
      existing,
      self.opts,
      self.snapshot_opts,
      self.cks,
    )
  }
}
