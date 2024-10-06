fn main() {
  if std::env::var("AOL_GITHUB_CI").is_ok() {
    copy_bitcask_manifest_example();
  }
}

fn copy_bitcask_manifest_example() {
  use std::{
    env::current_dir,
    fs::{File, OpenOptions},
  };

  let current_dir = current_dir().unwrap();
  let mut example = current_dir.join("examples").join("bitcask_manifest");
  example.set_extension("rs");

  let mut integration_test = OpenOptions::new()
    .create(true)
    .read(true)
    .write(true)
    .truncate(true)
    .open(current_dir.join("tests").join("integration.rs"))
    .unwrap();

  let mut file = File::open(&example).unwrap();

  std::io::copy(&mut file, &mut integration_test).unwrap();
}
