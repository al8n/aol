use core::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "std")]
use std::path::PathBuf;

use super::*;

/// Lock-free concurrent safe append-only log based on memory-map.
pub mod sync;

/// Append-only log based on memory-map.
mod unsync;
pub use unsync::*;