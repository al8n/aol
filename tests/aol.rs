use aol::{fs::AppendLog as FileAppendLog, memmap::AppendLog as MmapAppendLog, Entry};

trait AppendLog {
  type Data: aol::Data;
  type Error: std::error::Error;

  fn append(&mut self, entry: Entry<Self::Data>) -> Result<(), Self::Error>;
}
