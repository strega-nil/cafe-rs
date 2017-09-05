use std::collections::HashMap;
use std::fmt::{self, Display};

use mir::{self, Mir, TypeError};
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
  UnitLiteral,
  IntLiteral(u64),
  BoolLiteral(bool),
  Variable(String),
  Negative(Box<Expression>),
  Block(Box<Block>),
  IfElse {
    cond: Box<Expression>,
    then: Box<Block>,
    els: Box<Block>,
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
  Log(Box<Expression>),
}
impl ExpressionVariant {
  fn ty<'ctx>(
    &self,
    funcs: &HashMap<String, mir::FunctionDecl>,
    locals: &HashMap<String, mir::Reference>,
    builder: &mir::FunctionBuilder<'ctx>,
    mir: &Mir<'ctx>,
  ) -> mir::Type<'ctx> {
    match *self {
      ExpressionVariant::UnitLiteral => mir.get_builtin_type(
        mir::BuiltinType::Unit,
      ),
      ExpressionVariant::IntLiteral(_) => mir.get_builtin_type(
        mir::BuiltinType::SInt(mir::IntSize::I32),
      ),
      ExpressionVariant::BoolLiteral(_) => {
        mir.get_builtin_type(mir::BuiltinType::Bool)
      }
      ExpressionVariant::Variable(ref name) => {
        builder.get_binding_type(locals[name])
      }
      ExpressionVariant::Negative(ref e) => {
        e.ty(funcs, locals, builder, mir)
      }
      ExpressionVariant::Block(ref b) => b.ty(funcs, locals, builder, mir),
      ExpressionVariant::IfElse { ref then, .. } => {
        then.ty(funcs, locals, builder, mir)
      }
      ExpressionVariant::BinOp {
        op: BinOp::Plus,
        ref lhs,
        ..
      } => {
        lhs.ty(funcs, locals, builder, mir)
      },
      ExpressionVariant::BinOp { op: BinOp::LessEq, ..  } => {
        mir.get_builtin_type(mir::BuiltinType::Bool)
      },
      ExpressionVariant::Call { ref callee, .. } => {
        mir.get_function_type(funcs[callee]).ret
      }
      ExpressionVariant::Log(_) => {
        mir.get_builtin_type(mir::BuiltinType::Unit)
      }
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
    block: &mut mir::Block,
    funcs: &HashMap<String, mir::FunctionDecl>,
    locals: &mut HashMap<String, mir::Reference>,
  ) -> Result<(), TypeError<'ctx>> {
    let bool = mir.get_builtin_type(mir::BuiltinType::Bool);
    match *self {
      ExpressionVariant::IntLiteral(i) => {
        builder.add_stmt(
          mir,
          *block,
          dst,
          mir::Value::int_lit(i as i32),
        )?
      }
      ExpressionVariant::UnitLiteral => {
        builder.add_stmt(
          mir,
          *block,
          dst,
          mir::Value::unit_lit(),
        )?
      }
      ExpressionVariant::BoolLiteral(b) => {
        builder.add_stmt(
          mir,
          *block,
          dst,
          mir::Value::bool_lit(b),
        )?
      }
      ExpressionVariant::Negative(ref e) => {
        let ty = e.ty(funcs, locals, builder, mir);
        let var = builder.add_anonymous_local(ty);
        e.to_mir(var, mir, builder, block, funcs, locals)?;
        builder.add_stmt(
          mir,
          *block,
          dst,
          mir::Value::Negative(var),
        )?
      }
      ExpressionVariant::Variable(ref name) => {
        // NOTE(ubsan): typeck is currently in the mir pass
        // once we put it into a HIR or AST pass, it will catch
        // this
        if let Some(&loc) = locals.get(name) {
          builder.add_stmt(
            mir,
            *block,
            dst,
            mir::Value::Reference(loc),
          )?;
        } else {
          panic!("no `{}` name found", name);
        }
      }
      ExpressionVariant::Block(ref blk) => {
        blk.to_mir(dst, mir, builder, block, funcs, locals)?;
      }
      ExpressionVariant::IfElse {
        ref cond,
        ref then,
        ref els,
      } => {
        let cond = {
          let var = builder.add_anonymous_local(bool);
          cond.to_mir(var, mir, builder, block, funcs, locals)?;
          var
        };
        let (mut then_bb, mut els_bb, final_bb) =
          builder.term_if_else(*block, cond);
        then.to_mir(
          dst,
          mir,
          builder,
          &mut then_bb,
          funcs,
          locals,
        )?;
        els.to_mir(
          dst,
          mir,
          builder,
          &mut els_bb,
          funcs,
          locals,
        )?;
        *block = final_bb;
      }
      ExpressionVariant::BinOp {
        ref lhs,
        ref rhs,
        ref op,
      } => {
        let lhs = {
          let ty = lhs.ty(funcs, locals, builder, mir);
          let var = builder.add_anonymous_local(ty);
          lhs.to_mir(var, mir, builder, block, funcs, locals)?;
          var
        };
        let rhs = {
          let ty = rhs.ty(funcs, locals, builder, mir);
          let var = builder.add_anonymous_local(ty);
          rhs.to_mir(var, mir, builder, block, funcs, locals)?;
          var
        };
        builder.add_stmt(
          mir,
          *block,
          dst,
          Self::mir_binop(*op, lhs, rhs),
        )?;
      }
      ExpressionVariant::Call {
        ref callee,
        ref args,
      } => {
        let args = args
          .iter()
          .map(|v| {
            let ty = v.ty(funcs, locals, builder, mir);
            let var = builder.add_anonymous_local(ty);
            v.to_mir(var, mir, builder, block, funcs, locals)?;
            Ok(var)
          })
          .collect::<Result<_, _>>()?;
        if let Some(&callee) = funcs.get(callee) {
          builder.add_stmt(
            mir,
            *block,
            dst,
            mir::Value::Call { callee, args },
          )?
        } else {
          panic!("function `{}` doesn't exist", callee);
        }
      }
      ExpressionVariant::Log(ref arg) => {
        let ty = arg.ty(funcs, locals, builder, mir);
        let var = builder.add_anonymous_local(ty);
        arg.to_mir(var, mir, builder, block, funcs, locals)?;
        builder.add_stmt(
          mir,
          *block,
          dst,
          mir::Value::Log(var),
        )?;
      }
    }

    Ok(())
  }
}
pub type Expression = Spanned<ExpressionVariant>;
#[derive(Debug)]
pub enum StatementVariant {
  Expr(Expression),
  Local {
    name: String,
    ty: Option<StringlyType>,
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

impl Block_ {
  fn ty<'ctx>(
    &self,
    funcs: &HashMap<String, mir::FunctionDecl>,
    locals: &HashMap<String, mir::Reference>,
    builder: &mir::FunctionBuilder<'ctx>,
    mir: &Mir<'ctx>,
  ) -> mir::Type<'ctx> {
    // NOTE(ubsan): this will be different when we get void
    self.expr.ty(funcs, locals, builder, mir)
  }
  fn to_mir<'ctx>(
    &self,
    dst: mir::Reference,
    // TODO(ubsan): this state should probably all be in a struct
    mir: &mut Mir<'ctx>,
    builder: &mut mir::FunctionBuilder<'ctx>,
    block: &mut mir::Block,
    funcs: &HashMap<String, mir::FunctionDecl>,
    locals: &mut HashMap<String, mir::Reference>,
  ) -> Result<(), TypeError<'ctx>> {
    for stmt in &self.statements {
      match **stmt {
        StatementVariant::Expr(ref e) => {
          let ty = e.ty(funcs, locals, builder, mir);
          let tmp = builder.add_anonymous_local(ty);
          e.to_mir(tmp, mir, builder, block, funcs, locals)?;
        }
        StatementVariant::Local {
          ref name,
          ref ty,
          ref initializer,
        } => {
          let ty = if let Some(ref ty) = *ty {
            mir.get_type(ty).unwrap()
          } else {
            initializer.ty(funcs, &locals, &builder, mir)
          };
          let var = builder.add_local(name.clone(), ty);
          initializer.to_mir(
            var,
            mir,
            builder,
            block,
            funcs,
            locals,
          )?;
          locals.insert(name.clone(), var);
        }
      };
    }
    self.expr.to_mir(
      dst,
      mir,
      builder,
      block,
      funcs,
      locals,
    )
  }
}

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
  ) -> Result<(), TypeError<'ctx>> {
    let mut builder =
      mir.get_function_builder(decl);

    let mut locals = HashMap::new();
    for (i, param) in self.params.iter().enumerate() {
      locals
        .insert(param.0.clone(), builder.get_param(i as u32));
    }

    let mut block = builder.entrance();
    let ret = mir::Reference::ret();
    self.blk.to_mir(
      ret,
      mir,
      &mut builder,
      &mut block,
      funcs,
      &mut locals,
    )?;
    Ok(mir.add_function_definition(builder))
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
  pub fn build_mir<'ctx>(
    &mut self,
    mir: &mut Mir<'ctx>,
  ) -> Result<(), TypeError<'ctx>> {
    Self::prelude_types(mir);
    let mut mir_funcs: HashMap<String, mir::FunctionDecl> =
      HashMap::new();

    for (name, func) in &self.funcs {
      let params = {
        let tmp = func
          .params
          .iter()
          .map(|&(_, ref ty)| mir.get_type(ty).unwrap())
          .collect();
        mir::TypeList::from_existing(tmp)
      };
      let ret = mir.get_type(&func.ret_ty).unwrap();

      let decl = mir.add_function_decl(
        Some(name.to_owned()),
        mir::FunctionType {
          ret,
          params,
        },
      );
      mir_funcs.insert(name.to_owned(), decl);
    }
    for (name, func) in &self.funcs {
      let decl = mir_funcs[name];
      func.build_mir(decl, &mir_funcs, mir)?;
    }
    Ok(())
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
    mir.insert_type(
      Some(String::from("unit")),
      mir::TypeVariant::unit(),
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

impl Display for BinOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      BinOp::Plus => write!(f, "+"),
      BinOp::LessEq => write!(f, "<="),
    }
  }
}

fn write_indent(
  f: &mut fmt::Formatter,
  indent: usize,
) -> fmt::Result {
  for _ in 0..indent {
    write!(f, " ")?;
  }
  Ok(())
}

impl ExpressionVariant {
  fn fmt(
    &self,
    f: &mut fmt::Formatter,
    indent: usize,
  ) -> fmt::Result {
    match *self {
      ExpressionVariant::IntLiteral(i) => write!(f, "{}", i),
      ExpressionVariant::BoolLiteral(b) => write!(f, "{}", b),
      ExpressionVariant::UnitLiteral => write!(f, "()"),
      ExpressionVariant::Variable(ref s) => write!(f, "{}", s),
      ExpressionVariant::Negative(ref e) => {
        write!(f, "-")?;
        e.fmt(f, indent)
      }
      ExpressionVariant::BinOp {
        ref lhs,
        ref rhs,
        ref op,
      } => {
        lhs.fmt(f, indent)?;
        write!(f, " {} ", op)?;
        rhs.fmt(f, indent)
      }
      ExpressionVariant::Block(ref b) => b.fmt(f, indent),
      ExpressionVariant::IfElse {
        ref cond,
        ref then,
        ref els,
      } => {
        write!(f, "if ")?;
        cond.fmt(f, indent)?;
        write!(f, " ")?;
        then.fmt(f, indent)?;
        write!(f, " else ")?;
        els.fmt(f, indent)
      }
      ExpressionVariant::Call {
        ref callee,
        ref args,
      } => {
        write!(f, "{}(", callee)?;
        if !args.is_empty() {
          for arg in &args[..args.len() - 1] {
            arg.fmt(f, indent)?;
            write!(f, ", ")?;
          }
          args[args.len() - 1].fmt(f, indent)?;
          write!(f, ")")
        } else {
          write!(f, ")")
        }
      }
      ExpressionVariant::Log(ref arg) => {
        write!(f, "log(")?;
        arg.fmt(f, indent)?;
        write!(f, ")")
      }
    }
  }
}

impl StatementVariant {
  fn fmt(
    &self,
    f: &mut fmt::Formatter,
    indent: usize,
  ) -> fmt::Result {
    match *self {
      StatementVariant::Expr(ref e) => e.fmt(f, indent),
      StatementVariant::Local {
        ref name,
        ref ty,
        ref initializer,
      } => {
        if let Some(ref ty) = *ty {
          write!(f, "let {}: {} = ", name, ty)?;
          initializer.fmt(f, indent)
        } else {
          write!(f, "let {} = ", name)?;
          initializer.fmt(f, indent)
        }
      }
    }
  }
}



impl Block_ {
  fn fmt(
    &self,
    f: &mut fmt::Formatter,
    indent: usize,
  ) -> fmt::Result {
    writeln!(f, "{{")?;
    for stmt in &self.statements {
      write_indent(f, indent + 2)?;
      stmt.thing.fmt(f, indent + 2)?;
      writeln!(f, ";")?;
    }
    write_indent(f, indent + 2)?;
    self.expr.fmt(f, indent + 2)?;
    writeln!(f, "")?;
    write_indent(f, indent)?;
    write!(f, "}}")
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
      write!(f, "): {} ", func.ret_ty)?;
      func.blk.fmt(f, 0)?;
    }
    Ok(())
  }
}
