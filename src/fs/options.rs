use super::RewritePolicy;

/// Options for the append only log.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Options {
  pub(super) magic_version: u16,
  pub(super) sync_on_write: bool,
  pub(super) rewrite_policy: RewritePolicy,
  pub(super) read_only: bool,
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
      sync_on_write: true,
      rewrite_policy: RewritePolicy::All,
      read_only: false,
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
  /// assert_eq!(opts.sync_on_write(), true);
  /// ```
  #[inline]
  pub const fn sync_on_write(&self) -> bool {
    self.sync_on_write
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
  /// let opts = Options::new().with_sync_on_write(false);
  ///
  /// assert_eq!(opts.sync_on_write(), false);
  /// ```
  #[inline]
  pub const fn with_sync_on_write(mut self, sync_on_write: bool) -> Self {
    self.sync_on_write = sync_on_write;
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
