use super::RewritePolicy;

/// Options for the append only log.
#[viewit::viewit(vis_all = "pub(super)", getters(skip), setters(skip))]
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  magic_version: u16,
  sync: bool,
  rewrite_policy: RewritePolicy,
  read_only: bool,

  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  create_new: bool,
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  create: bool,
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  read: bool,
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  write: bool,
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  append: bool,
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  truncate: bool,
}

impl Default for Options {
  /// Returns the default options.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::default();
  /// ```
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Options {
  /// Create a new Options with the default values.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new();
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      magic_version: 0,
      sync: true,
      rewrite_policy: RewritePolicy::All,
      read_only: false,

      #[cfg(all(feature = "std", not(target_family = "wasm")))]
      create_new: false,
      #[cfg(all(feature = "std", not(target_family = "wasm")))]
      create: false,
      #[cfg(all(feature = "std", not(target_family = "wasm")))]
      read: false,
      #[cfg(all(feature = "std", not(target_family = "wasm")))]
      write: false,
      #[cfg(all(feature = "std", not(target_family = "wasm")))]
      append: false,
      #[cfg(all(feature = "std", not(target_family = "wasm")))]
      truncate: false,
    }
  }

  /// Get the external magic.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.magic_version(), 0);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Get whether the append-only log is read-only.
  ///
  /// Default is `false`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.read_only(), false);
  /// ```
  #[inline]
  pub const fn read_only(&self) -> bool {
    self.read_only
  }

  /// Get whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new();
  ///
  /// assert_eq!(opts.sync(), true);
  /// ```
  #[inline]
  pub const fn sync(&self) -> bool {
    self.sync
  }

  /// Get the rewrite policy.
  ///
  /// Default is `RewritePolicy::All`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{Options, RewritePolicy};
  ///
  /// let opts = Options::new().with_rewrite_policy(RewritePolicy::Skip(100));
  ///
  /// assert_eq!(opts.rewrite_policy(), RewritePolicy::Skip(100));
  /// ```
  #[inline]
  pub const fn rewrite_policy(&self) -> RewritePolicy {
    self.rewrite_policy
  }

  /// Set the external magic.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
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

  /// Set whether the append-only log is read-only.
  ///
  /// Default is `false`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_read_only(true);
  ///
  /// assert_eq!(opts.read_only(), true);
  /// ```
  #[inline]
  pub const fn with_read_only(mut self, read_only: bool) -> Self {
    self.read_only = read_only;
    self
  }

  /// Set whether flush the data to disk after write.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_sync(false);
  ///
  /// assert_eq!(opts.sync(), false);
  /// ```
  #[inline]
  pub const fn with_sync(mut self, sync: bool) -> Self {
    self.sync = sync;
    self
  }

  /// Set the rewrite policy.
  ///
  /// Default is `RewritePolicy::All`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use aol::{Options, RewritePolicy};
  ///
  /// let opts = Options::new().with_rewrite_policy(RewritePolicy::Skip(100));
  /// ```
  #[inline]
  pub const fn with_rewrite_policy(mut self, rewrite_policy: RewritePolicy) -> Self {
    self.rewrite_policy = rewrite_policy;
    self
  }
}

impl Options {
  /// Returns `true` if the file should be opened with read access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_read(true);
  /// assert_eq!(opts.read(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn read(&self) -> bool {
    self.read
  }

  /// Returns `true` if the file should be opened with write access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_write(true);
  /// assert_eq!(opts.write(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn write(&self) -> bool {
    self.write
  }

  /// Returns `true` if the file should be opened with append access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_append(true);
  /// assert_eq!(opts.append(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn append(&self) -> bool {
    self.append
  }

  /// Returns `true` if the file should be opened with truncate access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_truncate(true);
  /// assert_eq!(opts.truncate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn truncate(&self) -> bool {
    self.truncate
  }

  /// Returns `true` if the file should be created if it does not exist.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_create(true);
  /// assert_eq!(opts.create(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn create(&self) -> bool {
    self.create
  }

  /// Returns `true` if the file should be created if it does not exist and fail if it does.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_create_new(true);
  /// assert_eq!(opts.create_new(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub const fn create_new(&self) -> bool {
    self.create_new
  }

  /// Sets the option for read access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `read`-able if opened.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_read(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_read(mut self, read: bool) -> Self {
    self.read = read;
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
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_write(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_write(mut self, write: bool) -> Self {
    self.write = write;
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
  /// [`Options::with_create`] method to do so.
  ///
  /// [`write()`]: std::io::Write::write "io::Write::write"
  /// [`flush()`]: std::io::Write::flush "io::Write::flush"
  /// [seek]: std::io::Seek::seek "io::Seek::seek"
  /// [Current]: std::io::SeekFrom::Current "io::SeekFrom::Current"
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_append(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_append(mut self, append: bool) -> Self {
    self.write = true;
    self.append = append;
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
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_write(true).with_truncate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_truncate(mut self, truncate: bool) -> Self {
    self.truncate = truncate;
    self.write = true;
    self
  }

  /// Sets the option to create a new file, or open it if it already exists.
  /// If the file does not exist, it is created and set the lenght of the file to the given size.
  ///
  /// In order for the file to be created, [`Options::with_write`] or
  /// [`Options::with_append`] access must be used.
  ///
  /// See also [`std::fs::write()`][std::fs::write] for a simple function to
  /// create a file with some given data.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let opts = Options::new().with_write(true).with_create(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_create(mut self, val: bool) -> Self {
    self.create = val;
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
  /// If `.with_create_new(true)` is set, [`.with_create()`](Options::with_create) and [`.with_truncate()`](Options::with_truncate) are
  /// ignored.
  ///
  /// The file must be opened with write or append access in order to create
  /// a new file.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use aol::Options;
  ///
  /// let file = Options::new()
  ///   .with_write(true)
  ///   .with_create_new(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "std", not(target_family = "wasm")))))]
  pub fn with_create_new(mut self, val: bool) -> Self {
    self.create_new = val;
    self
  }

  #[inline]
  #[cfg(all(feature = "std", not(target_family = "wasm")))]
  pub(super) fn to_open_options(&self) -> std::fs::OpenOptions {
    let mut opts = std::fs::OpenOptions::new();
    opts
      .read(self.read)
      .write(self.write)
      .append(self.append)
      .truncate(self.truncate)
      .create(self.create)
      .create_new(self.create_new);

    opts
  }
}
