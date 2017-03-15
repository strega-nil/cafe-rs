extern crate pom;

mod parser;
mod mir;

use std::io::Read;

use parser::Ast;
use mir::Mir;

fn main() {
  let filename = std::env::args_os().nth(1).expect("requires a filename");
  let mut file = vec![];
  std::fs::File::open(filename).unwrap().read_to_end(&mut file).unwrap();
  let parsed = Ast::parse(&file);
  println!("{:#?}", parsed);
  let mir = Mir::lower(parsed);
  println!("-------------------------------");
  println!("{}", mir);
  println!("-------------------------------");
  if let Some(ret) = mir.run("main") {
    println!("main returned {}", ret);
  } else {
    println!("no main function");
  }
}
