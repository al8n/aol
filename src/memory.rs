// #[cfg(feature = "std")]
// use std::collections::HashSet;

// #[cfg(not(feature = "std"))]
// use hashbrown::HashSet;

// use super::{ManifestEvent, ManifestEventKind};

use super::*;

impl File for Vec<u8> {
  type Options = usize;

  type Error = core::convert::Infallible;

  fn open(opts: &Self::Options) -> Result<(bool, Self), Self::Error>
  where
    Self: Sized,
  {
    Ok((true, Vec::with_capacity(*opts)))
  }

  fn read_exact(&mut self, _buf: &mut [u8]) -> Result<(), Self::Error> {
    unreachable!()
  }

  fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
    self.extend_from_slice(data);
    Ok(())
  }

  fn flush(&mut self) -> Result<(), Self::Error> {
    Ok(())
  }

  fn sync_all(&self) -> Result<(), Self::Error> {
    Ok(())
  }

  fn truncate(&mut self, len: u64) -> Result<(), Self::Error> {
    Vec::truncate(self, len as usize);
    Ok(())
  }

  fn size(&self) -> Result<u64, Self::Error> {
    unreachable!()
  }
}

// pub struct MemoryManifest {
//   vlogs: HashSet<u32>,
//   logs: HashSet<u32>,
//   last_fid: u32,
// }

// impl MemoryManifest {
//   pub fn new() -> Self {
//     Self {
//       vlogs: HashSet::new(),
//       logs: HashSet::new(),
//       last_fid: 0,
//     }
//   }

//   pub fn append(&mut self, event: ManifestEvent) {
//     match event.kind {
//       ManifestEventKind::AddVlog => {
//         self.vlogs.insert(event.fid);
//         self.last_fid = self.last_fid.max(event.fid);
//       }
//       ManifestEventKind::AddLog => {
//         self.logs.insert(event.fid);
//         self.last_fid = self.last_fid.max(event.fid);
//       }
//       ManifestEventKind::RemoveVlog => {
//         self.vlogs.remove(&event.fid);
//       }
//       ManifestEventKind::RemoveLog => {
//         self.logs.remove(&event.fid);
//       }
//     }
//   }

//   #[inline]
//   pub const fn last_fid(&self) -> u32 {
//     self.last_fid
//   }
// }
