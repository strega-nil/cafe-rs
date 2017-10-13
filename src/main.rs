#![allow(unused_parens)] // this lint is stupid

extern crate clap;

mod ast;
mod containers;
mod mir;
mod parse;

use std::fs::File;
use std::fmt;

use ast::Ast;
use mir::Mir;

fn write_indent(f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
    const INDENT_SIZE: usize = 2;
    for _ in 0..(indent * INDENT_SIZE) {
        write!(f, " ")?;
    }
    Ok(())
}



macro_rules! user_error {
  ($($args:expr),* $(,)*) => ({
    eprintln!($($args),*);
    ::std::panic::set_hook(Box::new(|_| {}));
    panic!();
  })
}

fn main() {
    use clap::{App, Arg};
    use std::io::Read;

    let matches = App::new("cfc")
        .version("0.1.0")
        .author("Nicole Mazzuca <npmazzuca@gmail.com>")
        .about(
            "A compiler for the café language.\n\
             Written in Rust.",
        )
        .arg(Arg::with_name("input").required(true))
        .arg(
            Arg::with_name("print-ast")
                .long("print-ast")
                .help("print the generated AST"),
        )
        .arg(
            Arg::with_name("print-mir")
                .long("print-mir")
                .help("print the generated MIR"),
        )
        .arg(
            Arg::with_name("no-output")
                .long("no-output")
                .help("do not print the output of the run"),
        )
        .arg(
            Arg::with_name("no-run")
                .long("no-run")
                .help("do not actually run the resulting mir")
                .conflicts_with("no-output"),
        )
        .get_matches();

    let name = matches.value_of("input").unwrap();
    let print_ast = matches.is_present("print-ast");
    let print_mir = matches.is_present("print-mir");
    let print_run = !matches.is_present("no-output");
    let do_run = !matches.is_present("no-run");

    let mut file = Vec::new();
    match File::open(&name) {
        Ok(mut o) => {
            o.read_to_end(&mut file).unwrap();
        }
        Err(e) => {
            user_error!("Failure to open file '{}': {}", name, e);
        }
    }
    let file = String::from_utf8(file).unwrap();

    let ast = match Ast::new(&file) {
        Ok(ast) => ast,
        Err(e) => user_error!("error: {}", e),
    };
    if print_ast {
        println!("    ===   AST   ===    ");
        println!("{}", ast);
    }
    let ctxt = mir::MirCtxt::new();
    let mir = match Mir::new(&ctxt, ast) {
        Ok(mir) => mir,
        Err(e) => user_error!("error: {}", e),
    };
    if print_mir {
        println!("    ===   MIR   ===    ");
        println!("{}", mir);
    }

    if do_run {
        if print_run {
            if print_ast || print_mir {
                println!("    ===   RUN   ===    ");
            }
            mir.run();
        } else {
            mir.run();
        }
    }
}
