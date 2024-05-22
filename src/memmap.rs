use core::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "std")]
use std::path::PathBuf;

use super::*;

/// Lock-free concurrent safe append-only log based on memory-map.
pub mod sync;

/// Append-only log based on memory-map.
#[cfg(feature = "std")]
mod unsync;
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use unsync::*;
