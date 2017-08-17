use std::collections::HashMap;
use std::fmt::{self, Display};

use mir::{self, Mir};
use parse::{ItemVariant, Parser, ParserError,
            ParserErrorVariant, Spanned};
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum Category {
  Raw,
  Shared,
  Mut,
  Own,
}

// user defined types will be strings
#[derive(Clone, Debug)]
pub enum StringlyType {
  #[allow(dead_code)]
  Reference(Category, Box<StringlyType>),
  #[allow(dead_code)]
  Pointer(Category, Box<StringlyType>),
  UserDefinedType(String),
  Unit,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinOp {
  Plus,
  LessEq,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOpPrecedence {
  Addition,
  Comparison,
}

impl BinOp {
  pub fn precedence(self) -> BinOpPrecedence {
    match self {
      BinOp::Plus => BinOpPrecedence::Addition,
      BinOp::LessEq => BinOpPrecedence::Comparison,
    }
  }
}

#[derive(Debug)]
pub enum ExpressionVariant {
  Nullary,
  IntLiteral(u64),
  BoolLiteral(bool),
  Variable(String),
  IfElse {
    cond: Box<Expression>,
    then: Box<Expression>,
    els: Box<Expression>,
  },
  BinOp {
    lhs: Box<Expression>,
    rhs: Box<Expression>,
    op: BinOp,
  },
  Call {
    callee: String,
    args: Vec<Expression>,
  },
}
impl ExpressionVariant {
  fn ty<'ctx>(&self, mir: &Mir<'ctx>) -> mir::Type<'ctx> {
    match *self {
      ExpressionVariant::Nullary => {
        panic!("nil type is unimplemented")
      },
      ExpressionVariant::IntLiteral(_) => {
        mir.get_builtin_type(
          mir::BuiltinType::SInt(mir::IntSize::I32)
        )
      },
      ExpressionVariant::BoolLiteral(_) => {
        mir.get_builtin_type(mir::BuiltinType::Bool)
      },
      ExpressionVariant::Variable(_) => {
        unimplemented!()
      },
      ExpressionVariant::IfElse { .. } => {
        unimplemented!()
      },
      ExpressionVariant::BinOp { .. } => {
        unimplemented!()
      },
      ExpressionVariant::Call { .. } => {
        unimplemented!()
      },
    }
  }

  fn mir_binop(
    op: BinOp,
    lhs: mir::Reference,
    rhs: mir::Reference,
  ) -> mir::Value {
    match op {
      BinOp::Plus => mir::Value::Add(lhs, rhs),
      BinOp::LessEq => mir::Value::LessEq(lhs, rhs),
    }
  }
  fn to_mir<'ctx>(
    &self,
    dst: mir::Reference,
    // TODO(ubsan): this state should probably all be in a struct
    mir: &mut Mir<'ctx>,
    builder: &mut mir::FunctionBuilder<'ctx>,
    block: mir::Block,
    funcs: &HashMap<String, mir::FunctionDecl>,
    locals: &HashMap<String, mir::Reference>,
  ) -> mir::Block {
    let s32 = mir.get_builtin_type(
      mir::BuiltinType::SInt(mir::IntSize::I32)
    );
    let bool = mir.get_builtin_type(
      mir::BuiltinType::Bool
    );
    match *self {
      ExpressionVariant::IntLiteral(i) => {
        builder.add_stmt(
          block,
          dst,
          mir::Value::int_lit(i as i32),
        )
      }
      ExpressionVariant::BoolLiteral(b) => {
        builder.add_stmt(block, dst, mir::Value::bool_lit(b))
      }
      ExpressionVariant::Variable(ref name) => {
        // will panic for now - should be caught in typeck
        if let Some(&loc) = locals.get(name) {
          builder.add_stmt(
            block,
            dst,
            mir::Value::Reference(loc),
          );
        } else {
          panic!("no `{}` name found", name);
        }
      }
      ExpressionVariant::IfElse {
        ref cond,
        ref then,
        ref els,
      } => {
        let cond = {
          let var = builder.add_anonymous_local(bool);
          cond.to_mir(var, mir, builder, block, funcs, locals);
          var
        };
        let (then_bb, els_bb, final_bb) =
          builder.term_if_else(block, cond);
        then.to_mir(dst, mir, builder, then_bb, funcs, locals);
        els.to_mir(dst, mir, builder, els_bb, funcs, locals);
        return final_bb;
      }
      ExpressionVariant::BinOp {
        ref lhs,
        ref rhs,
        ref op,
      } => {
        let lhs = {
          let var = builder.add_anonymous_local(s32);
          lhs.to_mir(var, mir, builder, block, funcs, locals);
          var
        };
        let rhs = {
          let var = builder.add_anonymous_local(s32);
          rhs.to_mir(var, mir, builder, block, funcs, locals);
          var
        };
        builder.add_stmt(
          block,
          dst,
          Self::mir_binop(*op, lhs, rhs),
        );
      }
      ExpressionVariant::Call {
        ref callee,
        ref args,
      } => {
        let args: Vec<_> = args
          .iter()
          .map(|v| {
            let var = builder.add_anonymous_local(s32);
            v.to_mir(var, mir, builder, block, funcs, locals);
            var
          })
          .collect();
        if let Some(&callee) = funcs.get(callee) {
          builder.add_stmt(
            block,
            dst,
            mir::Value::Call { callee, args }
          )
        } else {
          panic!("function `{}` doesn't exist", callee);
        }
      }
      ExpressionVariant::Nullary => {
        panic!("nullary types not yet supported")
      }
    }

    block
  }
}
pub type Expression = Spanned<ExpressionVariant>;
#[derive(Debug)]
pub enum StatementVariant {
  Expr(Expression),
  Local {
    name: String,
    ty: StringlyType,
    initializer: Expression,
  },
}
pub type Statement = Spanned<StatementVariant>;


#[derive(Debug)]
pub struct Block_ {
  pub statements: Vec<Statement>,
  pub expr: Expression,
}
pub type Block = Spanned<Block_>;

#[derive(Debug)]
pub struct FunctionValue {
  pub params: Vec<(String, StringlyType)>,
  pub ret_ty: StringlyType,
  pub blk: Block_,
}
pub type Function = Spanned<FunctionValue>;

impl Function {
  fn build_mir<'ctx>(
    &self,
    decl: mir::FunctionDecl,
    funcs: &HashMap<String, mir::FunctionDecl>,
    mir: &mut Mir<'ctx>,
  ) {
    let mir_params = self
      .params
      .iter()
      .map(|&(_, ref ty)| mir.get_type(ty).unwrap())
      .collect();

    let ret_ty = mir.get_type(&self.ret_ty).unwrap();
    let mut builder =
      mir.get_function_builder(decl, mir_params, ret_ty);

    let mut locals = HashMap::new();
    for (i, param) in self.params.iter().enumerate() {
      locals
        .insert(param.0.clone(), builder.get_param(i as u32));
    }

    let block = builder.entrance();
    for stmt in &self.blk.statements {
      match **stmt {
        StatementVariant::Expr(ref e) => {
          let tmp = builder.add_anonymous_local(
            e.ty(mir)
          );
          e.to_mir(
            tmp,
            mir,
            &mut builder,
            block,
            funcs,
            &locals,
          );
        }
        StatementVariant::Local {
          ref name,
          ref ty,
          ref initializer,
        } => {
          let ty = mir.get_type(ty).unwrap();
          let var = builder.add_local(name.clone(), ty);
          initializer.to_mir(
            var,
            mir,
            &mut builder,
            block,
            funcs,
            &locals,
          );
          locals.insert(name.clone(), var);
        }
      };
    }
    let ret = mir::Reference::ret();
    self
      .blk
      .expr
      .to_mir(ret, mir, &mut builder, block, funcs, &locals);
    mir.add_function_definition(builder)
  }
}

#[derive(Debug)]
pub enum AstErrorVariant {
  Parser(ParserErrorVariant),
  MultipleValueDefinitions {
    name: String,
    original: Spanned<()>,
  },
}
pub type AstError = Spanned<AstErrorVariant>;
pub type AstResult<T> = Result<T, AstError>;

impl From<ParserError> for AstError {
  fn from(pe: ParserError) -> AstError {
    Spanned {
      thing: AstErrorVariant::Parser(pe.thing),
      start: pe.start,
      end: pe.end,
    }
  }
}

#[derive(Debug)]
pub struct Ast {
  funcs: HashMap<String, Function>,
}

impl Ast {
  pub fn new(file: &str) -> AstResult<Self> {
    let mut parse = Parser::new(file);
    let mut funcs = HashMap::<String, Function>::new();
    loop {
      match parse.next_item() {
        Ok((
          name,
          Spanned {
            thing: ItemVariant::Function(thing),
            start,
            end,
          },
        )) => {
          if let Some(orig) = funcs.get(&name) {
            return Err(Spanned {
              thing: AstErrorVariant::MultipleValueDefinitions {
                name: name.clone(),
                original: Spanned {
                  thing: (),
                  start: orig.start,
                  end: orig.end,
                },
              },
              start,
              end,
            });
          };
          funcs.insert(name, Spanned { thing, start, end });
        }
        Err(Spanned {
          thing: ParserErrorVariant::ExpectedEof,
          ..
        }) => break,
        Err(e) => return Err(e.into()),
      }
    }
    Ok(Ast { funcs })
  }
}

impl Ast {
  pub fn build_mir<'ctx>(&mut self, mir: &mut Mir<'ctx>) {
    Self::prelude_types(mir);
    let mut mir_funcs: HashMap<String, mir::FunctionDecl> =
      HashMap::new();
    for (name, _) in &self.funcs {
      let decl = mir.add_function_decl(Some(name.to_owned()));
      mir_funcs.insert(name.to_owned(), decl);
    }
    for (name, func) in &self.funcs {
      let decl = mir_funcs[name];
      func.build_mir(decl, &mir_funcs, mir);
    }
  }

  fn prelude_types(mir: &Mir) {
    mir.insert_type(
      Some(String::from("s32")),
      mir::TypeVariant::s32(),
    );
    mir.insert_type(
      Some(String::from("bool")),
      mir::TypeVariant::bool(),
    );
  }
}

impl Display for StringlyType {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      StringlyType::UserDefinedType(ref s) => write!(f, "{}", s),
      _ => panic!(),
    }
  }
}

impl Display for StatementVariant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      StatementVariant::Expr(ref e) => write!(f, "{}", **e),
      StatementVariant::Local {
        ref name,
        ref ty,
        ref initializer,
      } => write!(f, "let {}: {} = {}", name, ty, **initializer),
    }
  }
}

impl Display for BinOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      BinOp::Plus => write!(f, "+"),
      BinOp::LessEq => write!(f, "<="),
    }
  }
}

impl Display for ExpressionVariant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      ExpressionVariant::IntLiteral(i) => write!(f, "{}", i),
      ExpressionVariant::BoolLiteral(b) => write!(f, "{}", b),
      ExpressionVariant::Variable(ref s) => write!(f, "{}", s),
      ExpressionVariant::BinOp {
        ref lhs,
        ref rhs,
        ref op,
      } => write!(f, "{} {} {}", lhs.thing, op, rhs.thing),
      ExpressionVariant::IfElse {
        ref cond,
        ref then,
        ref els,
      } => {
        write!(f,
r"if {} {{
    {}
  }} else {{
    {}
  }}",
          cond.thing,
          then.thing,
          els.thing,
        )
      }
      ExpressionVariant::Call {
        ref callee,
        ref args,
      } => {
        write!(f, "{}(", callee)?;
        if !args.is_empty() {
          for arg in &args[..args.len() - 1] {
            write!(f, "{}, ", **arg)?;
          }
          write!(f, "{})", *args[args.len() - 1])
        } else {
          write!(f, ")")
        }
      }
      ExpressionVariant::Nullary => write!(f, "()"),
    }
  }
}

impl Display for Ast {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    for (name, func) in &self.funcs {
      let ref func = func.thing;
      write!(f, "func {}(", name)?;
      if !func.params.is_empty() {
        for p in &func.params[..func.params.len() - 1] {
          let (ref name, ref ty) = *p;
          write!(f, "{}: {}, ", name, ty)?;
        }
        let (ref name, ref ty) =
          func.params[func.params.len() - 1];
        write!(f, "{}: {}", name, ty)?;
      }
      writeln!(f, "): {} = {{", func.ret_ty)?;
      for stmt in &func.blk.statements {
        writeln!(f, "  {};", stmt.thing)?;
      }
      writeln!(f, "  {}", func.blk.expr.thing)?;
      writeln!(f, "}}")?;
    }
    Ok(())
  }
}
