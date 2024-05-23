use crate::{CustomFlags, Entry, EntryFlags};

use super::*;

/// Manifest for Wisckey WALs based on bitcask model.
///
/// The first bit of the [`CustomFlags`] is used to differentiate between log and value log files.
/// If the bit is set, then it's a value log file, otherwise it's a log file.
#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Manifest {
  vlogs: HashSet<u32>,
  logs: HashSet<u32>,

  // Contains total number of creation and deletion changes in the manifest -- used to compute
  // whether it'd be useful to rewrite the manifest.
  creations: u64,
  deletions: u64,
}

impl Manifest {
  /// Create a new manifest.
  #[inline]
  pub fn new() -> Self {
    Self {
      vlogs: HashSet::new(),
      logs: HashSet::new(),
      creations: 0,
      deletions: 0,
    }
  }
}

impl crate::Manifest for Manifest {
  type Data = ();

  type Error = core::convert::Infallible;

  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error> {
    if entry.flag().is_deletion() {
      self.deletions += 1;
    } else {
      self.creations += 1;
    }

    if entry.flag().custom_flag().bit1() {
      self.vlogs.insert(entry.fid());
    } else {
      self.logs.insert(entry.fid());
    }
    Ok(())
  }

  fn into_iter(self) -> impl Iterator<Item = Entry<Self::Data>> {
    self
      .logs
      .into_iter()
      .map(|e| Entry {
        fid: e,
        data: (),
        flag: EntryFlags::creation(CustomFlags::empty()),
      })
      .chain(self.vlogs.into_iter().map(|fid| Entry {
        fid,
        data: (),
        flag: EntryFlags::creation(CustomFlags::empty().with_bit1()),
      }))
  }

  #[inline]
  fn deletions(&self) -> u64 {
    self.deletions
  }

  fn creations(&self) -> u64 {
    self.creations
  }
}
