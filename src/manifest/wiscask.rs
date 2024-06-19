#[cfg(feature = "std")]
use std::collections::HashSet;

#[cfg(not(feature = "std"))]
use hashbrown::HashSet;

use super::*;

/// The file ID.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
pub struct Fid(u32);

impl From<u32> for Fid {
  #[inline]
  fn from(fid: u32) -> Self {
    Self(fid)
  }
}

impl From<Fid> for u32 {
  #[inline]
  fn from(fid: Fid) -> Self {
    fid.0
  }
}

impl core::fmt::Display for Fid {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl crate::Data for Fid {
  type Error = core::convert::Infallible;

  fn encoded_size(&self) -> usize {
    mem::size_of::<u32>()
  }

  fn encode(&self, buf: &mut [u8]) -> Result<usize, Self::Error> {
    buf.copy_from_slice(&self.0.to_le_bytes());
    Ok(mem::size_of::<u32>())
  }

  fn decode(buf: &[u8]) -> Result<(usize, Self), Self::Error> {
    let fid = u32::from_le_bytes(buf.try_into().unwrap());
    Ok((mem::size_of::<u32>(), Self(fid)))
  }
}

/// Snapshot represents the contents of the MANIFEST file in a store based on bitcask + wisckey.
///
/// The MANIFEST file describes the startup state of the db -- all logs files.
///
/// It consists of a sequence of [`Fid`]. Each of these is treated atomically,
/// and contains a sequence of [`Fid`]'s (file creations/deletions) which we use to
/// reconstruct the append-only at startup.
///
/// The first bit of the [`CustomFlags`] is used to differentiate between log and value log files.
/// If the bit is set, then it's a value log file, otherwise it's a log file.
#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Snapshot {
  vlogs: HashSet<Fid>,
  logs: HashSet<Fid>,

  // Contains total number of creation and deletion changes in the append-only -- used to compute
  // whether it'd be useful to rewrite the append-only.
  creations: u64,
  deletions: u64,
}

impl Snapshot {
  /// Create a new append-only.
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

impl crate::Snapshot for Snapshot {
  type Data = Fid;

  type Error = core::convert::Infallible;

  fn insert(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error> {
    if entry.flag().is_deletion() {
      self.deletions += 1;
    } else {
      self.creations += 1;
    }

    if entry.flag().custom_flag().bit1() {
      self.vlogs.insert(entry.data);
    } else {
      self.logs.insert(entry.data);
    }
    Ok(())
  }

  fn into_iter(self) -> impl Iterator<Item = Entry<Self::Data>> {
    self
      .logs
      .into_iter()
      .map(|fid| Entry {
        data: fid,
        flag: EntryFlags::creation(),
      })
      .chain(self.vlogs.into_iter().map(|fid| Entry {
        data: fid,
        flag: EntryFlags::creation_with_custom_flag(CustomFlags::empty().with_bit1()),
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
