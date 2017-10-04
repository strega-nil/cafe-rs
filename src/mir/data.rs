use super::*;

use parse::{Location, Spanned};

#[derive(Copy, Clone, Debug)]
pub struct Reference(pub(super) u32);

impl Reference {
    pub fn ret() -> Self {
        Reference(0)
    }

    pub(super) fn param(n: u32) -> Self {
        Reference(n + 1)
    }
}

#[derive(Debug)]
pub enum Literal {
    Int(i32),
    Bool(bool),
    Unit,
}

impl Literal {
    fn ty<'ctx>(&self, mir: &Mir<'ctx>) -> Type<'ctx> {
        match *self {
            Literal::Int(_) => mir.get_builtin_type(BuiltinType::SInt(IntSize::I32)),
            Literal::Bool(_) => mir.get_builtin_type(BuiltinType::Bool),
            Literal::Unit => mir.get_builtin_type(BuiltinType::Unit),
        }
    }
}

#[derive(Debug)]
pub enum Value {
    Literal(Literal),
    Reference(Reference),
    Negative(Reference),
    Add(Reference, Reference),
    LessEq(Reference, Reference),
    Call {
        callee: FunctionDecl,
        args: Vec<Reference>,
    },
    Log(Reference),
}

impl Value {
    pub fn int_lit(i: i32) -> Self {
        Value::Literal(Literal::Int(i))
    }
    pub fn bool_lit(b: bool) -> Self {
        Value::Literal(Literal::Bool(b))
    }
    pub fn unit_lit() -> Self {
        Value::Literal(Literal::Unit)
    }

    pub fn ty<'ctx>(
        &self,
        builder: &FunctionBuilder<'ctx>,
        mir: &Mir<'ctx>,
        start: Location,
        end: Option<Location>,
    ) -> Result<Type<'ctx>, TypeError<'ctx>> {
        match *self {
            Value::Literal(ref lit) => Ok(lit.ty(mir)),
            Value::Negative(ref_) => {
                let ty = builder.bindings[ref_.0 as usize].ty;
                let s32 = mir.get_builtin_type(BuiltinType::SInt(IntSize::I32));
                assert!(ty == s32, "negative must be done on s32");
                Ok(builder.bindings[ref_.0 as usize].ty)
            }
            Value::Reference(ref_) => Ok(builder.bindings[ref_.0 as usize].ty),
            Value::Add(rhs, lhs) => {
                let ty_lhs = builder.bindings[lhs.0 as usize].ty;
                let ty_rhs = builder.bindings[rhs.0 as usize].ty;
                if ty_rhs != ty_lhs {
                    Err(Spanned {
                        thing: TypeErrorVariant::Mismatched {
                            lhs: ty_lhs,
                            rhs: ty_rhs,
                        },
                        start,
                        end,
                    })
                } else {
                    let s32 = mir.get_builtin_type(BuiltinType::SInt(IntSize::I32));
                    assert!(ty_lhs == s32, "addition must be done on s32");
                    Ok(ty_lhs)
                }
            }
            Value::LessEq(rhs, lhs) => {
                let ty_lhs = builder.bindings[lhs.0 as usize].ty;
                let ty_rhs = builder.bindings[rhs.0 as usize].ty;
                if ty_rhs != ty_lhs {
                    Err(Spanned {
                        thing: TypeErrorVariant::Mismatched {
                            lhs: ty_lhs,
                            rhs: ty_rhs,
                        },
                        start,
                        end,
                    })
                } else {
                    Ok(mir.get_builtin_type(BuiltinType::Bool))
                }
            }
            Value::Call {
                callee: ref decl,
                ref args,
            } => {
                let callee = &mir.funcs[decl.0];
                let params = &callee.ty.params;
                if args.len() != (params.number_of_types() as usize) {
                    return Err(Spanned {
                        thing: TypeErrorVariant::NumberOfArgs {
                            name: mir.funcs[decl.0]
                                .name
                                .clone()
                                .unwrap_or("<anonymous function>".to_owned()),
                            args_expected: callee.ty.params.number_of_types() as u32,
                            args_found: args.len() as u32,
                        },
                        start,
                        end,
                    });
                }

                for (arg, parm) in args.iter().zip(params) {
                    let arg_ty = builder.bindings[arg.0 as usize].ty;
                    if arg_ty != parm {
                        return Err(Spanned {
                            thing: TypeErrorVariant::Mismatched {
                                lhs: parm,
                                rhs: arg_ty,
                            },
                            start,
                            end,
                        });
                    }
                }

                Ok(callee.ty.ret)
            }
            Value::Log(_) => Ok(mir.get_builtin_type(BuiltinType::Unit)),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub(super) enum BindingKind {
    Param(u32),
    Local(u32),
    Return,
}

#[derive(Debug)]
pub(super) struct Binding<'ctx> {
    pub(super) name: Option<String>,
    pub(super) ty: Type<'ctx>,
    pub(super) kind: BindingKind,
}

#[derive(Copy, Clone, Debug)]
pub struct Block(pub(super) u32);

#[derive(Copy, Clone, Debug)]
pub enum Terminator {
    IfElse {
        cond: Reference,
        then: Block,
        els: Block,
    },
    Goto(Block),
    Return,
}

#[derive(Debug)]
pub(super) struct Statement {
    pub(super) lhs: Reference,
    pub(super) rhs: Value,
}

#[derive(Debug)]
pub(super) struct BlockData {
    pub(super) stmts: Vec<Statement>,
    pub(super) term: Terminator,
}
