#![allow(unused)]

extern crate argparse;
extern crate typed_arena;

#[macro_use]
mod macros;

mod ast;
mod mir;
mod parse;
mod ty;

use std::fs::File;

use ast::Ast;
use parse::Lexer;

// TODO(ubsan): unify parameter ordering
enum Either<L, R> {
  Left(L),
  Right(R),
}

// NOTE(ubsan): this should *not* be public
pub enum DebugPrint {
  Print,
  NoPrint,
}

impl From<bool> for DebugPrint {
  fn from(x: bool) -> DebugPrint {
    if x { DebugPrint::Print } else { DebugPrint::NoPrint }
  }
}

fn main() {
  use std::io::Read;

  let mut name = "".to_owned();
  let mut output = None;
  let mut print_ast = false;
  let mut print_mir = false;
  let mut print_llir = false;
  let mut opt = false;
  {
    use argparse::{ArgumentParser, Store, StoreOption, StoreTrue, List};

    let mut ap = ArgumentParser::new();
    ap.set_description("\
      The pinkc compiler for the pink language.\n\
      Written in Rust.\
    ");
    ap.refer(&mut name).required().add_argument(
      "name", Store, "The file to compile"
    );
    ap.refer(&mut output).add_option(
      &["-o", "--output"], StoreOption, "The file to output to"
    );
    ap.refer(&mut print_ast).add_option(
      &["--print-ast"], StoreTrue,
      "Pass if you would like to print the generated AST",
    );
    ap.refer(&mut print_mir).add_option(
      &["--print-mir"], StoreTrue,
      "Pass if you would like to print the generated MIR",
    );
    ap.refer(&mut print_llir).add_option(
      &["--print-llir"], StoreTrue,
      "Pass if you would like to print the generated LLVM IR",
    );
    ap.refer(&mut opt).add_option(
      &["--opt", "-O"], StoreTrue,
      "Pass if you would like to optimize the generated LLVM IR",
    );

    ap.parse_args_or_exit();
  }

  let print_ast = DebugPrint::from(print_ast);
  let print_mir = DebugPrint::from(print_mir);
  let print_llir = DebugPrint::from(print_llir);

  let output = output.unwrap_or(get_output_from_name(&name));

  let mut file = Vec::new();
  File::open(&name).expect(&name).read_to_end(&mut file).unwrap();
  let file = String::from_utf8(file).unwrap();

  let lexer = Lexer::new(&file);
  let tyctxt = ty::TypeContext::new();
  let ast = match Ast::create(lexer, &tyctxt) {
    Ok(ast) => ast,
    Err(e) => panic!("\n{:#?}", e),
  };

  let mir = match ast.typeck(print_ast, opt) {
    Ok(mir) => mir,
    Err(e) => panic!("\n{:#?}", e),
  };

  if let DebugPrint::Print = print_mir {
    println!("{}", mir);
  }

  mir.build_and_write(&output, print_llir)
}

// TODO(ubsan): take off the ".pnk" of the input file
fn get_output_from_name(name: &str) -> String {
  format!("{}.s", name)
}
