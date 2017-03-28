use std;
use std::collections::HashMap;
use parse;
use ty::{self, Type};
use mir;

pub mod expr;
use self::expr::{Stmt, Expr};

pub struct Ast<'t> {
  functions: HashMap<String, (Function<'t>, Block<'t>)>,
  function_types: HashMap<String, ty::Function<'t>>,
  ctxt: &'t ty::TypeContext<'t>
}

impl<'t> Ast<'t> {
  pub fn create(
    lexer: parse::Lexer,
    ctxt: &'t ty::TypeContext<'t>,
  ) -> Result<Self, parse::ParserError> {
    let mut parser = parse::Parser::new(lexer);
    let mut functions = HashMap::new();
    let mut function_types = HashMap::new();

    loop {
      match parser.item(ctxt) {
        Ok(Item::Function {
          name,
          ret,
          args,
          body,
        }) => {
          let ty = ty::Function::new(
            args.iter().map(|&(_, t)| t).collect(), ret);
          let f = Function::new(name.clone(), ret, args)?;
          function_types.insert(name.clone(), ty);
          if let Some(_) =
              functions.insert(name.clone(), (f, body)) {
            return Err(parse::ParserError::DuplicatedFunction {
              function: name,
              compiler: fl!(),
            });
          }
        }

        Err(parse::ParserError::ExpectedEof) => break,
        Err(e) => return Err(e),
      }
    }

    Ok(Ast {
      functions: functions,
      function_types: function_types,
      ctxt: ctxt,
    })
  }

  pub fn typeck(
    mut self,
    print_ast: ::DebugPrint,
  ) -> Result<mir::Mir<'t>, AstError<'t>> {
    for (_, &mut (ref func, ref mut body))
        in self.functions.iter_mut() {
      let mut uf = ty::UnionFind::new();
      let mut vars = HashMap::<String, Type>::new();
      Expr::typeck_block(body, &self.ctxt, func.ret_ty,
        &mut uf, &mut vars, func, &self.function_types)?;
      Expr::finalize_block_ty(body, &mut uf, func, &self.ctxt)?;
    }
    if let Some(&(ref f, _)) = self.functions.get("main") {
      if *f.ret_ty.0 != ty::TypeVariant::Unit ||
          f.params.len() != 0 {
        let mut input = Vec::new();
        for (_, &(_, ty)) in &f.params {
          input.push(ty);
        }
        return Err(AstError::IncorrectMainType {
          input: input,
          output: f.ret_ty,
          compiler: fl!(),
        })
      }
    } else {
      return Err(AstError::FunctionDoesntExist {
        function: "main".to_owned(),
        compiler: fl!(),
      })
    }
    let mut mir = mir::Mir::new(self.ctxt);
    let functions = std::mem::replace(&mut self.functions, HashMap::new());
    for (name, (func, body)) in functions {
      if let ::DebugPrint::Print = print_ast {
        println!("{}: {:#?}\n", name, body);
      }
      let mir_func = func.add_body(body, &mir, &self);
      mir.add_function(name, mir_func);
    }
    Ok(mir)
  }
}

#[derive(Debug)]
pub enum AstError<'t> {
  IncorrectNumberOfArguments {
    passed: usize,
    expected: usize,
    callee: String,
    caller: String,
    compiler: (&'static str, u32),
  },
  UndefinedVariableName {
    name: String,
    function: String,
    compiler: (&'static str, u32),
  },
  FunctionDoesntExist {
    function: String,
    compiler: (&'static str, u32),
  },
  IncorrectMainType {
    input: Vec<Type<'t>>,
    output: Type<'t>,
    compiler: (&'static str, u32),
  },
  UnopUnsupported {
    op: parse::Operand,
    inner: Type<'t>,
    function: String,
    compiler: (&'static str, u32),
  },
  CouldNotUnify {
    first: Type<'t>,
    second: Type<'t>,
    function: String,
    compiler: (&'static str, u32),
  },
  NoActualType {
    function: String,
    compiler: (&'static str, u32),
  },
  StatementsAfterReturn {
    function: String,
    compiler: (&'static str, u32),
  },
  NotAnLvalue {
    expr: String,
    function: String,
    compiler: (&'static str, u32),
  },
  BinopUnsupported {
    op: parse::Operand,
    lhs: Type<'t>,
    rhs: Type<'t>,
    function: String,
    compiler: (&'static str, u32),
  },
}

#[derive(Debug)]
pub enum Item<'t> {
  Function {
    name: String,
    ret: Type<'t>,
    args: Vec<(String, Type<'t>)>,
    body: Block<'t>,
  }
}

#[derive(Debug)]
pub struct Function<'t> {
  name: String,
  ret_ty: Type<'t>,
  params: HashMap<String, (usize, Type<'t>)>,
  raw: mir::Function<'t>,
}

impl<'t> Function<'t> {
  fn new(
    name: String,
    ret_ty: Type<'t>,
    params: Vec<(String, Type<'t>)>,
  ) -> Result<Function<'t>, parse::ParserError> {
    let mut param_tys = vec![];
    let mut param_names = vec![];
    let mut param_hashmap = HashMap::new();
    let mut param_index = 0;


    for (param_name, param_ty) in params {
      if !param_hashmap.contains_key(&param_name) {
        param_names.push(param_name.clone());
        param_tys.push(param_ty);
        debug_assert!(
          param_hashmap.insert(param_name, (param_index, param_ty))
          .is_none());
        param_index += 1;
      } else {
        return Err(parse::ParserError::DuplicatedFunctionParameter {
          parameter: param_name,
          function: name,
          compiler: fl!(),
        });
      }
    }

    let raw = mir::Function::new(
      ty::Function::new(param_tys, ret_ty),
      param_names,
    );

    Ok(Function {
      name: name,
      ret_ty: ret_ty,
      params: param_hashmap,
      raw: raw,
    })
  }

  fn add_body(mut self, body: Block<'t>, mir: &mir::Mir<'t>, ast: &Ast<'t>)
      -> mir::Function<'t> {
    let block = self.raw.start_block();
    let mut locals = HashMap::new();
    let (ret, blk) = Expr::translate_block(body, mir, &mut self, block,
        &mut locals, &ast.function_types);
    if let Some(blk) = blk {
      blk.finish(&mut self.raw, ret);
    }
    self.raw
  }
}

#[derive(Debug)]
pub struct Block<'t> {
  stmts: Vec<Stmt<'t>>,
  expr: Option<Expr<'t>>,
}

impl<'t> Block<'t> {
  pub fn new(stmts: Vec<Stmt<'t>>, expr: Option<Expr<'t>>) -> Self {
    Block {
      stmts: stmts,
      expr: expr,
    }
  }

  pub fn expr(e: Expr) -> Block {
    Block {
      stmts: vec![],
      expr: Some(e),
    }
  }
}
