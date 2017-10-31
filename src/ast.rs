use std::collections::HashMap;
use std::fmt::{self, Display};

use containers::Scope;
use mir::{self, Mir, TypeError};
use parse::{ItemVariant, Parser, ParserError, ParserErrorVariant, Spanned};

// user defined types will be strings
#[derive(Clone, Debug)]
pub enum StringlyType {
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

#[derive(Debug)]
pub enum ExpressionVariant {
    UnitLiteral,
    IntLiteral { is_negative: bool, value: u64 },
    BoolLiteral(bool),
    Variable(String),
    Negative(Box<Expression>),
    Block {
        statements: Vec<Statement>,
        expr: Box<Expression>,
    },
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
    Log(Box<Expression>),
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
pub struct FunctionValue {
    pub params: Vec<(String, StringlyType)>,
    pub ret_ty: StringlyType,
    pub expr: Expression,
}
pub type Function = Spanned<FunctionValue>;

#[derive(Debug)]
pub struct StructValue {
    pub members: Vec<(String, StringlyType)>,
}
pub type Struct = Spanned<StructValue>;

#[derive(Debug)]
pub enum AstErrorVariant {
    Parser(ParserErrorVariant),
    MultipleValueDefinitions { name: String, original: Spanned<()> },
}
impl Display for AstErrorVariant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::AstErrorVariant::*;
        match *self {
            Parser(ref p) => p.fmt(f),
            MultipleValueDefinitions {
                ref name,
                ref original,
            } => write!(
                f,
                "found multiple definitions for '{}' - original definition at {}",
                name,
                original.span,
            ),
        }
    }
}
pub type AstError = Spanned<AstErrorVariant>;
pub type AstResult<T> = Result<T, AstError>;

#[derive(Debug)]
pub struct Ast {
    funcs: HashMap<String, Function>,
}

struct Types<'ctx> {
    inner: HashMap<String, mir::Type<'ctx>>,
}


impl BinOp {
    pub fn precedence(self) -> BinOpPrecedence {
        match self {
            BinOp::Plus => BinOpPrecedence::Addition,
            BinOp::LessEq => BinOpPrecedence::Comparison,
        }
    }
}

impl Expression {
    fn ty<'ctx>(
        &self,
        tys: &Types<'ctx>,
        funcs: &HashMap<String, mir::FunctionDecl>,
        locals: &Scope<(mir::Type<'ctx>, mir::Reference)>,
        builder: &mir::FunctionBuilder<'ctx>,
        mir: &Mir<'ctx>,
    ) -> Result<mir::Type<'ctx>, TypeError<'ctx>> {
        match **self {
            ExpressionVariant::UnitLiteral => Ok(mir.get_builtin_type(mir::BuiltinType::Unit)),
            ExpressionVariant::BoolLiteral(_) => Ok(mir.get_builtin_type(mir::BuiltinType::Bool)),
            ExpressionVariant::IntLiteral { .. } => {
                Ok(mir.get_builtin_type(mir::BuiltinType::SInt(mir::IntSize::I32)))
            }
            ExpressionVariant::Variable(ref name) => if let Some(local) = locals.get(name) {
                Ok(local.0)
            } else {
                Err(TypeError::binding_not_found(name.clone(), self.span))
            },
            ExpressionVariant::Negative(ref e) => e.ty(tys, funcs, locals, builder, mir),
            ExpressionVariant::Block { ref expr, .. } => expr.ty(tys, funcs, locals, builder, mir),
            ExpressionVariant::IfElse { ref then, .. } => then.ty(tys, funcs, locals, builder, mir),
            ExpressionVariant::BinOp {
                op: BinOp::Plus,
                ref lhs,
                ..
            } => lhs.ty(tys, funcs, locals, builder, mir),
            ExpressionVariant::BinOp {
                op: BinOp::LessEq, ..
            } => Ok(mir.get_builtin_type(mir::BuiltinType::Bool)),
            ExpressionVariant::Call { ref callee, .. } => if let Some(func) = funcs.get(callee) {
                Ok(mir.get_function_type(*func).ret)
            } else {
                Err(TypeError::binding_not_found(callee.clone(), self.span))
            },
            ExpressionVariant::Log(_) => Ok(mir.get_builtin_type(mir::BuiltinType::Unit)),
        }
    }
}

impl Expression {
    fn mir_binop(op: BinOp, lhs: mir::Reference, rhs: mir::Reference) -> mir::Value {
        match op {
            BinOp::Plus => mir::Value::Add(lhs, rhs),
            BinOp::LessEq => mir::Value::LessEq(lhs, rhs),
        }
    }

    fn to_mir<'ctx>(
        &self,
        dst: mir::Reference,
        // TODO(ubsan): this state should probably all be in a struct
        tys: &Types<'ctx>,
        mir: &mut Mir<'ctx>,
        builder: &mut mir::FunctionBuilder<'ctx>,
        block: &mut mir::Block,
        funcs: &HashMap<String, mir::FunctionDecl>,
        locals: &Scope<(mir::Type<'ctx>, mir::Reference)>,
    ) -> Result<(), TypeError<'ctx>> {
        let bool = mir.get_builtin_type(mir::BuiltinType::Bool);
        let span = self.span;
        match **self {
            ExpressionVariant::IntLiteral { is_negative, value } => {
                let mul = if is_negative { -1 } else { 1 };
                builder.add_stmt(
                    mir,
                    *block,
                    dst,
                    mir::Value::int_lit((value as i32) * mul),
                    span,
                )?
            }
            ExpressionVariant::UnitLiteral => {
                builder.add_stmt(mir, *block, dst, mir::Value::unit_lit(), span)?
            }
            ExpressionVariant::BoolLiteral(b) => {
                builder.add_stmt(mir, *block, dst, mir::Value::bool_lit(b), span)?
            }
            ExpressionVariant::Negative(ref e) => {
                let ty = e.ty(tys, funcs, locals, builder, mir)?;
                let var = builder.add_anonymous_local(ty);
                e.to_mir(var, tys, mir, builder, block, funcs, locals)?;
                builder.add_stmt(mir, *block, dst, mir::Value::Negative(var), span)?
            }
            ExpressionVariant::Variable(ref name) => if let Some(&loc) = locals.get(name) {
                builder.add_stmt(mir, *block, dst, mir::Value::Reference(loc.1), span)?;
            } else {
                return Err(TypeError::binding_not_found(name.clone(), span));
            },
            ExpressionVariant::Block {
                ref statements,
                ref expr,
            } => {
                let mut locals = Scope::with_parent(locals);
                for stmt in statements {
                    match **stmt {
                        StatementVariant::Expr(ref e) => {
                            let ty = e.ty(tys, funcs, &locals, builder, mir)?;
                            let tmp = builder.add_anonymous_local(ty);
                            e.to_mir(tmp, tys, mir, builder, block, funcs, &locals)?;
                        }
                        StatementVariant::Local {
                            ref name,
                            ref ty,
                            ref initializer,
                        } => {
                            let ty = if let Some(ref ty) = *ty {
                                match tys.get(ty) {
                                    Some(mir_ty) => mir_ty,
                                    None => {
                                        let str_ty = match *ty {
                                            StringlyType::UserDefinedType(ref s) => s.clone(),
                                            StringlyType::Unit => unreachable!(),
                                        };
                                        return Err(TypeError::type_not_found(str_ty, stmt.span));
                                    }
                                }
                            } else {
                                initializer.ty(tys, funcs, &locals, &builder, mir)?
                            };
                            let var = builder.add_local(name.clone(), ty);
                            initializer.to_mir(var, tys, mir, builder, block, funcs, &locals)?;
                            locals.insert(name.clone(), (ty, var));
                        }
                    };
                }
                expr.to_mir(dst, tys, mir, builder, block, funcs, &locals)?
            }
            ExpressionVariant::IfElse {
                ref cond,
                ref then,
                ref els,
            } => {
                let cond = {
                    let var = builder.add_anonymous_local(bool);
                    cond.to_mir(var, tys, mir, builder, block, funcs, locals)?;
                    var
                };
                let (mut then_bb, mut els_bb, final_bb) = builder.term_if_else(*block, cond);
                then.to_mir(dst, tys, mir, builder, &mut then_bb, funcs, locals)?;
                els.to_mir(dst, tys, mir, builder, &mut els_bb, funcs, locals)?;
                *block = final_bb;
            }
            ExpressionVariant::BinOp {
                ref lhs,
                ref rhs,
                ref op,
            } => {
                let lhs = {
                    let ty = lhs.ty(tys, funcs, locals, builder, mir)?;
                    let var = builder.add_anonymous_local(ty);
                    lhs.to_mir(var, tys, mir, builder, block, funcs, locals)?;
                    var
                };
                let rhs = {
                    let ty = rhs.ty(tys, funcs, locals, builder, mir)?;
                    let var = builder.add_anonymous_local(ty);
                    rhs.to_mir(var, tys, mir, builder, block, funcs, locals)?;
                    var
                };
                builder.add_stmt(mir, *block, dst, Self::mir_binop(*op, lhs, rhs), span)?;
            }
            ExpressionVariant::Call {
                ref callee,
                ref args,
            } => {
                let args = args.iter()
                    .map(|v| {
                        let ty = v.ty(tys, funcs, locals, builder, mir)?;
                        let var = builder.add_anonymous_local(ty);
                        v.to_mir(var, tys, mir, builder, block, funcs, locals)?;
                        Ok(var)
                    })
                    .collect::<Result<_, _>>()?;
                if let Some(&callee) = funcs.get(callee) {
                    builder.add_stmt(mir, *block, dst, mir::Value::Call { callee, args }, span)?
                } else {
                    panic!("function `{}` doesn't exist", callee);
                }
            }
            ExpressionVariant::Log(ref arg) => {
                let ty = arg.ty(tys, funcs, locals, builder, mir)?;
                let var = builder.add_anonymous_local(ty);
                arg.to_mir(var, tys, mir, builder, block, funcs, locals)?;
                builder.add_stmt(mir, *block, dst, mir::Value::Log(var), span)?;
            }
        }

        Ok(())
    }
}

impl Function {
    fn build_mir<'ctx>(
        &self,
        tys: &Types<'ctx>,
        decl: mir::FunctionDecl,
        funcs: &HashMap<String, mir::FunctionDecl>,
        mir: &mut Mir<'ctx>,
    ) -> Result<(), TypeError<'ctx>> {
        let mut builder = mir.get_function_builder(decl);

        let mut locals = Scope::new();
        for (i, param) in self.params.iter().enumerate() {
            locals.insert(
                param.0.clone(),
                (tys.get(&param.1).unwrap(), builder.get_param(i as u32)),
            );
        }

        let mut block = builder.entrance();
        let ret = mir::Reference::ret();
        self.expr
            .to_mir(ret, tys, mir, &mut builder, &mut block, funcs, &mut locals)?;
        Ok(mir.add_function_definition(builder))
    }
}

impl From<ParserError> for AstError {
    fn from(pe: ParserError) -> AstError {
        Spanned {
            thing: AstErrorVariant::Parser(pe.thing),
            span: pe.span,
        }
    }
}

impl<'ctx> Types<'ctx> {
    fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn insert(&mut self, name: String, ty: mir::Type<'ctx>) {
        self.inner.insert(name, ty);
    }
    pub fn get(&self, name: &StringlyType) -> Option<mir::Type<'ctx>> {
        match *name {
            StringlyType::UserDefinedType(ref name) => self.inner.get(name).map(|x| *x),
            StringlyType::Unit => self.inner.get("unit").map(|x| *x),
        }
    }
}

impl Ast {
    pub fn new(file: &str) -> AstResult<Self> {
        let mut parse = Parser::new(file);
        let mut funcs = HashMap::<String, Function>::new();
        let mut types = HashMap::<String, Struct>::new();
        loop {
            let tmp = parse.next_item();
            if let Err(Spanned {
                thing: ParserErrorVariant::ExpectedEof,
                ..
            }) = tmp
            {
                break;
            }
            let (name, Spanned { thing, span }) = tmp?;
            match thing {
                ItemVariant::Function(thing) => {
                    if let Some(orig) = funcs.get(&name) {
                        return Err(Spanned {
                            thing: AstErrorVariant::MultipleValueDefinitions {
                                name: name.clone(),
                                original: Spanned {
                                    thing: (),
                                    span: orig.span,
                                },
                            },
                            span,
                        });
                    };
                    funcs.insert(name, Spanned { thing, span });
                }
                ItemVariant::StructDecl(members) => {
                    let thing = StructValue { members };
                    types.insert(name, Spanned { thing, span });
                }
            }
        }
        Ok(Ast { funcs })
    }
}

impl Ast {
    pub fn build_mir<'ctx>(&mut self, mir: &mut Mir<'ctx>) -> Result<(), TypeError<'ctx>> {
        let mut mir_funcs: HashMap<String, mir::FunctionDecl> = HashMap::new();
        let mut tys = Types::new();

        Self::prelude_types(mir, &mut tys);

        for (name, func) in &self.funcs {
            let params = {
                let tmp = func.params
                    .iter()
                    // TODO(ubsan): should return a TypeError, not unwrap
                    .map(|&(_, ref ty)| tys.get(ty).unwrap())
                    .collect();
                mir::TypeList::from_existing(tmp)
            };
            let ret = tys.get(&func.ret_ty).unwrap();

            let decl = mir.add_function_decl(
                Some(name.to_owned()),
                mir::FunctionType { ret, params },
                func.span,
            )?;
            mir_funcs.insert(name.to_owned(), decl);
        }
        for (name, func) in &self.funcs {
            let decl = mir_funcs[name];
            func.build_mir(&tys, decl, &mir_funcs, mir)?;
        }
        Ok(())
    }

    fn prelude_types<'ctx>(mir: &Mir<'ctx>, tys: &mut Types<'ctx>) {
        use mir::BuiltinType::*;
        use mir::IntSize::*;
        tys.insert("unit".to_owned(), mir.get_builtin_type(Unit));
        tys.insert("bool".to_owned(), mir.get_builtin_type(Bool));
        tys.insert("s32".to_owned(), mir.get_builtin_type(SInt(I32)));
    }
}

impl Display for StringlyType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            StringlyType::UserDefinedType(ref s) => write!(f, "{}", s),
            StringlyType::Unit => write!(f, "unit"),
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

impl ExpressionVariant {
    fn is_nullary(&self) -> bool {
        if let ExpressionVariant::UnitLiteral = *self {
            true
        } else {
            false
        }
    }

    fn fmt_as_block(&self, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
        if let ExpressionVariant::Block { .. } = *self {
            self.fmt(f, indent)
        } else {
            writeln!(f, "{{")?;
            ::write_indent(f, indent + 1)?;
            self.fmt(f, indent + 1)?;
            writeln!(f, "")?;
            ::write_indent(f, indent)?;
            write!(f, "}}")
        }
    }
    fn fmt(&self, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
        match *self {
            ExpressionVariant::IntLiteral { is_negative, value } => if is_negative {
                write!(f, "-{}", value)
            } else {
                write!(f, "{}", value)
            },
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
            ExpressionVariant::Block {
                ref statements,
                ref expr,
            } => {
                writeln!(f, "{{")?;
                for stmt in statements {
                    ::write_indent(f, indent + 1)?;
                    stmt.thing.fmt(f, indent + 1)?;
                    writeln!(f, ";")?;
                }
                if !expr.is_nullary() {
                    ::write_indent(f, indent + 1)?;
                    expr.fmt(f, indent + 1)?;
                    writeln!(f, "")?;
                }
                ::write_indent(f, indent)?;
                write!(f, "}}")
            }
            ExpressionVariant::IfElse {
                ref cond,
                ref then,
                ref els,
            } => {
                write!(f, "if ")?;
                cond.fmt(f, indent)?;
                write!(f, " ")?;
                then.fmt_as_block(f, indent)?;
                //if !els.is_nullary() {
                write!(f, " else ")?;
                els.fmt_as_block(f, indent)?;
                //}
                Ok(())
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
    fn fmt(&self, f: &mut fmt::Formatter, indent: usize) -> fmt::Result {
        match *self {
            StatementVariant::Expr(ref e) => e.fmt(f, indent),
            StatementVariant::Local {
                ref name,
                ref ty,
                ref initializer,
            } => if let Some(ref ty) = *ty {
                write!(f, "let {}: {} = ", name, ty)?;
                initializer.fmt(f, indent)
            } else {
                write!(f, "let {} = ", name)?;
                initializer.fmt(f, indent)
            },
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
                let (ref name, ref ty) = func.params[func.params.len() - 1];
                write!(f, "{}: {}", name, ty)?;
            }
            write!(f, "): {} ", func.ret_ty)?;
            func.expr.fmt_as_block(f, 0)?;
            writeln!(f, "")?;
        }
        Ok(())
    }
}
