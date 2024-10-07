use std::{
  env::current_dir,
  fs::{File, OpenOptions},
};

fn main() {
  println!("{}", std::env::current_dir().unwrap().display());

  let current_dir = current_dir().unwrap();
  let parent = current_dir.parent().unwrap();
  let mut example = parent.join("examples").join("bitcask_manifest");
  example.set_extension("rs");

  let mut main = OpenOptions::new()
    .read(true)
    .write(true)
    .truncate(true)
    .open(current_dir.join("src").join("main.rs"))
    .unwrap();

  let mut file = File::open(&example).unwrap();

  std::io::copy(&mut file, &mut main).unwrap();
}
