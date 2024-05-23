#[cfg(feature = "std")]
use std::collections::HashSet;

#[cfg(not(feature = "std"))]
use hashbrown::HashSet;

/// [`Manifest`](crate::manifest::Manifest) implementors for Wisckey WALs based on bitcask model.
pub mod bitcask;

/// [`Manifest`](crate::manifest::Manifest) implementors for Wisckey WALs based on LSM model.
pub mod lsm;
