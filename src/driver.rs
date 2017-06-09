extern crate clap;
extern crate typed_arena;

#[macro_use]
mod macros;

mod ast;
mod containers;
mod mir;
mod parse;

use std::fs::File;

use ast::Ast;
use mir::Mir;

fn main() {
  use clap::{App, Arg};
  use std::io::Read;

  let matches = App::new("cfc")
    .version("0.1.0")
    .author("Nicole Mazzuca <npmazzuca@gmail.com>")
    .about("\
      A compiler for the café language.\n\
      Written in Rust.")
    .arg(Arg::with_name("input")
      .required(true))
    .arg(Arg::with_name("print-ast")
      .long("print-ast")
      .help("print the generated AST"))
    .arg(Arg::with_name("print-mir")
      .long("print-mir")
      .help("print the generated MIR"))
    .get_matches();

  let name = matches.value_of("input").unwrap();
  let print_ast = matches.is_present("print-ast");
  let print_mir = matches.is_present("print-mir");

  let mut file = Vec::new();
  File::open(&name)
    .expect(&name)
    .read_to_end(&mut file)
    .unwrap();
  let file = String::from_utf8(file).unwrap();

  let ast = Ast::new(&file);
  if print_ast {
    ast.print();
  }
  let ctxt = mir::MirCtxt::new();
  let mir = Mir::new(&ctxt, ast);
  if print_mir {
    mir.print();
  }
  println!("{:?}", mir.run());
}
