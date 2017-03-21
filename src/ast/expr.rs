use ast::{AstError, Block, Function};
use std::collections::HashMap;
use ty::{self, TypeContext, Type, TypeVariant};
use parse::Operand;
use mir;

#[derive(Debug)]
pub enum Stmt<'t> {
  Let {
    name: String,
    ty: Type<'t>,
    value: Option<Box<Expr<'t>>>,
  },
  Expr(Expr<'t>),
}

#[derive(Debug)]
pub enum ExprKind<'t> {
  Call {
    callee: String,
    args: Vec<Expr<'t>>
  },
  If {
    condition: Box<Expr<'t>>,
    then_value: Box<Block<'t>>,
    else_value: Box<Block<'t>>,
  },
  Block(Box<Block<'t>>),
  Binop {
    op: Operand,
    lhs: Box<Expr<'t>>,
    rhs: Box<Expr<'t>>,
  },
  Pos(Box<Expr<'t>>), // unary plus
  Neg(Box<Expr<'t>>), // unary minus
  Not(Box<Expr<'t>>), // !expr
  Ref(Box<Expr<'t>>), // &expr
  Deref(Box<Expr<'t>>),
  Variable(String),
  IntLiteral(u64),
  BoolLiteral(bool),
  UnitLiteral,
  Return(Box<Expr<'t>>),
  Assign {
    dst: Box<Expr<'t>>,
    src: Box<Expr<'t>>
  },
  Field {
    lhs: Box<Expr<'t>>,
    field: u16,
  },
}

#[derive(Debug)]
pub struct Expr<'t> {
  pub kind: ExprKind<'t>,
  pub ty: Type<'t>,
}

// constructors
impl<'t> Expr<'t> {
  pub fn call(
    callee: String, args: Vec<Expr<'t>>, ctxt: &'t TypeContext<'t>
  ) -> Self {
    Expr {
      kind: ExprKind::Call {
        callee: callee,
        args: args,
      },
      ty: Type::infer(ctxt),
    }
  }

  pub fn var(name: String, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Variable(name),
      ty: Type::infer(ctxt),
    }
  }

  pub fn if_else(
    cond: Expr<'t>,
    then: Block<'t>,
    else_: Block<'t>,
    ctxt: &'t TypeContext<'t>,
  ) -> Self {
    Expr {
      kind: ExprKind::If {
        condition: Box::new(cond),
        then_value: Box::new(then),
        else_value: Box::new(else_),
      },
      ty: Type::infer(ctxt),
    }
  }

  pub fn block(inner: Block<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Block(Box::new(inner)),
      ty: Type::infer(ctxt),
    }
  }

  pub fn int_lit(value: u64, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::IntLiteral(value),
      ty: Type::infer_int(ctxt),
    }
  }

  pub fn int_lit_with_ty(value: u64, ty: Type<'t>) -> Self {
    Expr {
      kind: ExprKind::IntLiteral(value),
      ty: ty,
    }
  }

  pub fn bool_lit(value: bool, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::BoolLiteral(value),
      ty: Type::bool(ctxt),
    }
  }

  pub fn unit_lit(ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::UnitLiteral,
      ty: Type::unit(ctxt),
    }
  }

  pub fn neg(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Neg(Box::new(inner)),
      ty: Type::infer(ctxt),
    }
  }

  pub fn pos(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Pos(Box::new(inner)),
      ty: Type::infer(ctxt),
    }
  }

  pub fn not(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Not(Box::new(inner)),
      ty: Type::infer(ctxt),
    }
  }

  pub fn ref_(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Ref(Box::new(inner)),
      ty: Type::ref_(Type::infer(ctxt), ctxt),
    }
  }

  pub fn deref(inner: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Deref(Box::new(inner)),
      ty: Type::infer(ctxt),
    }
  }

  pub fn ret(ret: Expr<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Expr {
      kind: ExprKind::Return(Box::new(ret)),
      ty: Type::diverging(ctxt),
    }
  }

  pub fn assign(dst: Expr<'t>, src: Expr<'t>, ctxt: &'t TypeContext<'t>)
      -> Self {
    Expr {
      kind: ExprKind::Assign {
        dst: Box::new(dst),
        src: Box::new(src),
      },
      ty: Type::unit(ctxt),
    }
  }

  pub fn field_access(
    lhs: Expr<'t>, field: u16, ctxt: &'t TypeContext<'t>,
  ) -> Self {
    Expr {
      kind: ExprKind::Field {
        lhs: Box::new(lhs),
        field: field,
      },
      ty: Type::infer(ctxt),
    }
  }
}

// parsing
impl<'t> Expr<'t> {
  pub fn is_block(&self) -> bool {
    match self.kind {
      ExprKind::If {..} | ExprKind::Block(_) => true,
      ExprKind::Call {..}
      | ExprKind::Binop {..}
      | ExprKind::Pos(_)
      | ExprKind::Neg(_)
      | ExprKind::Not(_)
      | ExprKind::Variable(_)
      | ExprKind::Ref(_)
      | ExprKind::Deref(_)
      | ExprKind::IntLiteral(_)
      | ExprKind::BoolLiteral(_)
      | ExprKind::UnitLiteral
      | ExprKind::Return(_)
      | ExprKind::Assign {..}
      | ExprKind::Field {..}
        => false,
    }
  }
}

// typechecking
impl<'t> Expr<'t> {
  pub fn typeck_block(
    block: &mut Block<'t>,
    ctxt: &'t TypeContext<'t>,
    to_unify: Type<'t>,
    uf: &mut ty::UnionFind<'t>,
    variables: &mut HashMap<String, Type<'t>>,
    function: &Function<'t>,
    functions: &HashMap<String, ty::Function<'t>>,
  ) -> Result<(), AstError<'t>> {
    let mut live_blk = true;
    for stmt in block.stmts.iter_mut() {
      match *stmt {
        Stmt::Let {
          ref name,
          ref mut ty,
          ref mut value,
        } => {
          ty.generate_inference_id(uf, ctxt);
          if let Some(ref mut v) = *value {
            v.unify_type(ctxt, *ty, uf, variables, function, functions)?;
          }
          variables.insert(name.to_owned(), *ty);
        }
        Stmt::Expr(ref mut e @ Expr {
          kind: ExprKind::Return(_),
          ..
        }) => {
          e.unify_type(ctxt, Type::diverging(ctxt),
            uf, variables, function, functions)?;
          live_blk = false;
          break;
        }
        Stmt::Expr(ref mut e) => {
          let mut ty = Type::infer(ctxt);
          ty.generate_inference_id(uf, ctxt);
          e.unify_type(ctxt, ty, uf, variables, function, functions)?;
        }
      }
    }
    if live_blk {
      match block.expr {
        Some(ref mut expr) => {
          expr.unify_type(ctxt, to_unify, uf, variables, function,
            functions)?
        },
        None => {
          uf.unify(to_unify, Type::unit(ctxt))
            .map_err(|()| AstError::CouldNotUnify {
              first: Type::unit(ctxt),
              second: to_unify,
              function: function.name.clone(),
              compiler: fl!(),
            }
          )?
        },
      };
    }
    Ok(())
  }

  pub fn unify_type(
    &mut self,
    ctxt: &'t TypeContext<'t>,
    to_unify: Type<'t>,
    uf: &mut ty::UnionFind<'t>,
    variables: &mut HashMap<String, Type<'t>>,
    function: &Function<'t>,
    functions: &HashMap<String, ty::Function<'t>>,
  ) -> Result<(), AstError<'t>> {
    self.ty.generate_inference_id(uf, ctxt);
    match self.kind {
      ExprKind::IntLiteral(_)
      | ExprKind::BoolLiteral(_)
      | ExprKind::UnitLiteral => {
        uf.unify(self.ty, to_unify).map_err(|()|
          AstError::CouldNotUnify {
            first: self.ty,
            second: to_unify,
            function: function.name.clone(),
            compiler: fl!(),
          }
        )
      }
      ExprKind::Variable(ref name) => {
        if let Some(ty) = variables.get(name) {
          self.ty = *ty;
          uf.unify(*ty, to_unify).map_err(|()|
            AstError::CouldNotUnify {
              first: *ty,
              second: to_unify,
              function: function.name.clone(),
              compiler: fl!(),
            }
          )
        } else if let Some(&(_, ty)) = function.args.get(name) {
          self.ty = ty;
          uf.unify(ty, to_unify).map_err(|()|
            AstError::CouldNotUnify {
              first: ty,
              second: to_unify,
              function: function.name.clone(),
              compiler: fl!(),
            }
          )
        } else {
          Err(AstError::UndefinedVariableName {
            name: name.clone(),
            function: function.name.clone(),
            compiler: fl!(),
          })
        }
      }
      ExprKind::Pos(ref mut inner) | ExprKind::Neg(ref mut inner)
      | ExprKind::Not(ref mut inner) => {
        inner.unify_type(ctxt, to_unify,
            uf, variables, function, functions)?;
        let self_ty = self.ty;
        let inner_ty = inner.ty;
        uf.unify(self.ty, inner.ty).map_err(|()|
          AstError::CouldNotUnify {
            first: self_ty,
            second: inner_ty,
            function: function.name.clone(),
            compiler: fl!(),
          }
        )
      }
      ExprKind::Ref(ref mut inner) => {
        let mut inner_ty = Type::infer(ctxt);
        inner_ty.generate_inference_id(uf, ctxt);
        inner.unify_type(ctxt, inner_ty,
          uf, variables, function, functions)?;
        let ref_ty = Type::ref_(inner_ty, ctxt);
        uf.unify(to_unify, ref_ty).map_err(|()|
          AstError::CouldNotUnify {
            first: to_unify,
            second: inner.ty,
            function: function.name.clone(),
            compiler: fl!(),
        })?;
        uf.unify(to_unify, ref_ty).map_err(|()|
          AstError::CouldNotUnify {
            first: to_unify,
            second: ref_ty,
            function: function.name.clone(),
            compiler: fl!(),
        })?;
        let self_ty = self.ty;
        uf.unify(self.ty, ref_ty).map_err(|()|
          AstError::CouldNotUnify {
            first: self_ty,
            second: ref_ty,
            function: function.name.clone(),
            compiler: fl!(),
        })
      }
      ExprKind::Deref(ref mut inner) => {
        let mut outer_ty = Type::infer(ctxt);
        outer_ty.generate_inference_id(uf, ctxt);
        let self_ty = self.ty;
        uf.unify(self.ty, outer_ty).map_err(|()|
          AstError::CouldNotUnify {
            first: self_ty,
            second: outer_ty,
            function: function.name.clone(),
            compiler: fl!(),
        })?;
        uf.unify(to_unify, outer_ty).map_err(|()|
          AstError::CouldNotUnify {
            first: to_unify,
            second: outer_ty,
            function: function.name.clone(),
            compiler: fl!(),
        })?;

        let inner_ty = Type::ref_(outer_ty, ctxt);
        inner.unify_type(ctxt, inner_ty, uf, variables, function, functions)
      }
      ExprKind::Field {
        ..
      } => {
        unimplemented!()
      }
      ExprKind::Binop {
        op,
        ref mut lhs,
        ref mut rhs,
      } => {
        match op {
          Operand::Mul
          | Operand::Div
          | Operand::Rem
          | Operand::Plus
          | Operand::Minus
          | Operand::Shl
          | Operand::Shr
          | Operand::And
          | Operand::Xor
          | Operand::Or
          => {
            let ty = self.ty;
            lhs.unify_type(ctxt, self.ty, uf, variables, function, functions)?;
            match rhs.unify_type(
              ctxt, lhs.ty, uf, variables, function, functions
            ) {
              Err(AstError::CouldNotUnify {
                first, second, function, ..
              }) => return Err(AstError::BinopUnsupported {
                  op: op,
                  lhs: second,
                  rhs: first,
                  function: function,
                  compiler: fl!(),
                }),
              Err(e) => return Err(e),
              Ok(()) => {},
            }
            uf.unify(self.ty, to_unify).map_err(|()|
              AstError::CouldNotUnify {
                first: ty,
                second: to_unify,
                function: function.name.clone(),
                compiler: fl!(),
              }
            )
          }

          Operand::EqualsEquals
          | Operand::NotEquals
          | Operand::LessThan
          | Operand::LessThanEquals
          | Operand::GreaterThan
          | Operand::GreaterThanEquals => {
            self.ty = Type::bool(ctxt);
            rhs.ty.generate_inference_id(uf, ctxt);
            lhs.unify_type(ctxt, rhs.ty,
              uf, variables, function, functions)?;
            match rhs.unify_type(ctxt, lhs.ty,
                uf, variables, function, functions) {
              Err(AstError::CouldNotUnify {
                first, second, function, ..
              }) => return Err(AstError::BinopUnsupported {
                  op: op,
                  lhs: second,
                  rhs: first,
                  function: function,
                  compiler: fl!(),
                }),
              Err(e) => return Err(e),
              Ok(()) => {},
            }
            uf.unify(self.ty, to_unify).map_err(|()|
              AstError::CouldNotUnify {
                first: Type::bool(ctxt),
                second: to_unify,
                function: function.name.clone(),
                compiler: fl!(),
              }
            )
          }

          Operand::AndAnd | Operand::OrOr => {
            rhs.ty.generate_inference_id(uf, ctxt);
            match lhs.unify_type(ctxt, rhs.ty,
                uf, variables, function, functions) {
              Err(AstError::CouldNotUnify {
                first, second, function, ..
              }) => return Err(AstError::BinopUnsupported {
                  op: op,
                  lhs: first,
                  rhs: second,
                  function: function,
                  compiler: fl!(),
                }),
              Err(e) => return Err(e),
              Ok(()) => {},
            }
            match rhs.unify_type(ctxt, Type::bool(ctxt),
                uf, variables, function, functions) {
              Err(AstError::CouldNotUnify {
                first, function, ..
              }) => return Err(AstError::BinopUnsupported {
                  op: op,
                  lhs: lhs.ty,
                  rhs: first,
                  function: function,
                  compiler: fl!(),
                }),
              Err(e) => return Err(e),
              Ok(()) => {},
            }

            uf.unify(self.ty, to_unify).map_err(|()|
              AstError::CouldNotUnify {
                first: to_unify,
                second: Type::bool(ctxt),
                function: function.name.clone(),
                compiler: fl!(),
              }
            )
          }

          Operand::Not => {
            panic!("ICE: Not (`!`) is not a binop")
          }
        }
      }
      ExprKind::Call {
        ref callee,
        ref mut args,
      } => {
        match functions.get(callee) {
          Some(f) => {
            if f.input().len() != args.len() {
              return Err(AstError::IncorrectNumberOfArguments {
                passed: args.len(),
                expected: f.input().len(),
                callee: callee.clone(),
                caller: function.name.clone(),
                compiler: fl!(),
              })
            }

            self.ty = f.output();
            for (arg_ty, expr) in f.input().iter().zip(args) {
              expr.unify_type(ctxt, *arg_ty,
                uf, variables, function, functions)?;
            }
            let ty = self.ty;
            uf.unify(self.ty, to_unify).map_err(|()|
              AstError::CouldNotUnify {
                first: ty,
                second: to_unify,
                function: function.name.clone(),
                compiler: fl!(),
              }
            )
          }
          None => return Err(AstError::FunctionDoesntExist {
            function: callee.clone(),
            compiler: fl!(),
          })
        }
      }
      ExprKind::If {
        ref mut condition,
        ref mut then_value,
        ref mut else_value,
      } => {
        condition.unify_type(
          ctxt, Type::bool(ctxt), uf, variables, function, functions
        )?;
        Self::typeck_block(
          then_value, ctxt, to_unify, uf, variables, function, functions
        )?;
        Self::typeck_block(
          else_value, ctxt, to_unify, uf, variables, function, functions
        )?;
        let ty = self.ty;
        uf.unify(self.ty, to_unify).map_err(|()|
          AstError::CouldNotUnify {
            first: ty,
            second: to_unify,
            function: function.name.clone(),
            compiler: fl!(),
          }
        )
      }
      ExprKind::Block(ref mut blk) => {
        Self::typeck_block(
          blk, ctxt, to_unify, uf, variables, function, functions
        )?;
        let ty = self.ty;
        uf.unify(self.ty, to_unify).map_err(|()|
          AstError::CouldNotUnify {
            first: ty,
            second: to_unify,
            function: function.name.clone(),
            compiler: fl!(),
          }
        )
      }
      ExprKind::Return(ref mut ret) => {
        self.ty = Type::diverging(ctxt);
        ret.unify_type(
          ctxt, function.ret_ty, uf, variables, function, functions
        )
      }
      ExprKind::Assign {
        ref mut dst,
        ref mut src,
      } => {
        debug_assert!(self.ty == Type::unit(ctxt));
        match dst.kind {
          ExprKind::Variable(ref name) => {
            if let Some(&ty) = variables.get(name) {
              src.unify_type(ctxt, ty, uf, variables, function, functions)?;
            } else {
              return Err(AstError::UndefinedVariableName {
                name: name.clone(),
                function: function.name.clone(),
                compiler: fl!(),
              })
            }
          }
          ExprKind::Deref(ref mut dst) => {
            let mut inner_ty = Type::infer(ctxt);
            inner_ty.generate_inference_id(uf, ctxt);
            dst.unify_type(
              ctxt,
              Type::ref_(inner_ty, ctxt),
              uf,
              variables,
              function,
              functions
            )?;
            src.unify_type(ctxt, inner_ty, uf, variables, function, functions)?;
          }
          _ => return Err(AstError::NotAnLvalue {
            expr: format!("{:?}", dst),
            function: function.name.clone(),
            compiler: fl!(),
          })
        }
        uf.unify(self.ty, Type::unit(ctxt)).map_err(|()|
          AstError::CouldNotUnify {
            first: Type::unit(ctxt),
            second: to_unify,
            function: function.name.clone(),
            compiler: fl!(),
          }
        )
      }
    }
  }

  pub fn finalize_block_ty(
    block: &mut Block<'t>,
    uf: &mut ty::UnionFind<'t>,
    function: &Function<'t>,
    ctxt: &'t TypeContext<'t>
  ) -> Result<(), AstError<'t>> {
    let mut live_blk = true;

    for stmt in block.stmts.iter_mut() {
      if !live_blk {
        return Err(AstError::StatementsAfterReturn {
          function: function.name.clone(),
          compiler: fl!(),
        });
      }
      match *stmt {
        Stmt::Let {
          ref mut ty,
          ref mut value,
          ..
        } => {
          ty.finalize(uf, ctxt).map_err(|()|
            AstError::NoActualType {
              compiler: fl!(),
              function: function.name.clone(),
            })?;
          if let Some(ref mut v) = *value {
            v.finalize_type(uf, function, ctxt)?;
          }
        },
        Stmt::Expr(ref mut e @ Expr {
          kind: ExprKind::Return(_),
          ..
        }) => {
          e.finalize_type(uf, function, ctxt)?;
          live_blk = false;
        },
        Stmt::Expr(ref mut e) => {
          e.finalize_type(uf, function, ctxt)?;
        },
      }
    }

    if let Some(ref mut expr) = block.expr {
      if !live_blk {
        return Err(AstError::StatementsAfterReturn {
          function: function.name.clone(),
          compiler: fl!(),
        });
      }
      expr.finalize_type(uf, function, ctxt)?;
    }
    Ok(())
  }

  pub fn finalize_type(
    &mut self,
    uf: &mut ty::UnionFind<'t>,
    function: &Function<'t>,
    ctxt: &'t TypeContext<'t>
  ) -> Result<(), AstError<'t>> {
    self.ty.finalize(uf, ctxt).map_err(|()|
       AstError::NoActualType {
        compiler: fl!(),
        function: function.name.clone(),
      }
    )?;

    match self.kind {
      ExprKind::IntLiteral(_)
      | ExprKind::BoolLiteral(_)
      | ExprKind::Variable(_)
      | ExprKind::UnitLiteral
      => Ok(()),
      ExprKind::Pos(ref mut inner) => {
        inner.finalize_type(uf, function, ctxt)?;
        assert!(self.ty == inner.ty);
        match *self.ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) => Ok(()),
          _ => {
            Err(AstError::UnopUnsupported {
              op: Operand::Plus,
              inner: self.ty,
              function: function.name.clone(),
              compiler: fl!(),
            })
          }
        }
      }
      ExprKind::Neg(ref mut inner) => {
        inner.finalize_type(uf, function, ctxt)?;
        assert!(self.ty == inner.ty);
        match *self.ty.0 {
          TypeVariant::SInt(_) => Ok(()),
          _ => {
            Err(AstError::UnopUnsupported {
              op: Operand::Minus,
              inner: self.ty,
              function: function.name.clone(),
              compiler: fl!(),
            })
          }
        }
      }
      ExprKind::Not(ref mut inner) => {
        inner.finalize_type(uf, function, ctxt)?;
        assert!(self.ty == inner.ty);
        match *self.ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_)
          | TypeVariant::Bool => Ok(()),
          _ => {
            Err(AstError::UnopUnsupported {
              op: Operand::Not,
              inner: self.ty,
              function: function.name.clone(),
              compiler: fl!(),
            })
          }
        }
      }
      ExprKind::Ref(ref mut inner) => {
        inner.finalize_type(uf, function, ctxt)?;
        assert!(self.ty == Type::ref_(inner.ty, ctxt),
          "self: {:?}, inner: &{:?}", self.ty, inner.ty);
        Ok(())
      }
      ExprKind::Deref(ref mut inner) => {
        inner.finalize_type(uf, function, ctxt)?;
        assert!(Type::ref_(self.ty, ctxt) == inner.ty,
          "self: {:?}, inner: *{:?}", self.ty, inner.ty);
        Ok(())
      }
      ExprKind::Field {
        ..
      } => {
        unimplemented!()
      }
      ExprKind::Binop {
        ref mut lhs,
        ref mut rhs,
        ..
      } => {
        lhs.finalize_type(uf, function, ctxt)?;
        rhs.finalize_type(uf, function, ctxt)
      }
      ExprKind::Call {
        ref mut args,
        ..
      } => {
        for arg in args {
          arg.finalize_type(uf, function, ctxt)?;
        }
        Ok(())
      }
      ExprKind::If {
        ref mut condition,
        ref mut then_value,
        ref mut else_value,
      } => {
        condition.finalize_type(uf, function, ctxt)?;
        Self::finalize_block_ty(then_value, uf, function, ctxt)?;
        Self::finalize_block_ty(else_value, uf, function, ctxt)
      }
      ExprKind::Block(ref mut blk) => {
        Self::finalize_block_ty(blk, uf, function, ctxt)
      }
      ExprKind::Return(ref mut ret) => {
        assert!(*self.ty.0 == TypeVariant::Diverging);
        ret.finalize_type(uf, function, ctxt)
      }
      ExprKind::Assign {
        ref mut src,
        ..
      } => {
        assert!(*self.ty.0 == TypeVariant::Unit);
        src.finalize_type(uf, function, ctxt)
      }
    }
  }
}

// into mir
impl<'t> Expr<'t> {
  pub fn translate(
    self,
    mir: &mir::Mir<'t>,
    function: &mut Function<'t>,
    mut block: mir::Block,
    locals: &mut HashMap<String, mir::Local>,
    fn_types: &HashMap<String, ty::Function<'t>>
  ) -> (mir::Value, Option<mir::Block>) {
    assert!(self.ty.is_final_type(), "not final type: {:?}", self);
    match self.kind {
      ExprKind::IntLiteral(n) => {
        let (int_ty, signed) = match *self.ty.0 {
          TypeVariant::SInt(t) => (t, true),
          TypeVariant::UInt(t) => (t, false),
          _ => panic!("ICE: not a valid int literal type: {:?}", self.ty)
        };
        (mir::Value::int_literal(n, int_ty, signed), Some(block))
      }
      ExprKind::BoolLiteral(b) => {
        (mir::Value::bool_literal(b), Some(block))
      }
      ExprKind::UnitLiteral => {
        (mir::Value::unit_literal(), Some(block))
      }
      ExprKind::Variable(name) => {
        if let Some(var) = locals.get(&name) {
          (mir::Value::local(*var), Some(block))
        } else if let Some(&(num, _)) = function.args.get(&name) {
          (mir::Value::param(num as u32, &mut function.raw),
            Some(block))
        } else {
          panic!("ICE: unknown variable: {}", name)
        }
      }
      ExprKind::Pos(e) => {
        let (inner, blk) =
          e.translate(mir, function, block, locals, fn_types);
        if let Some(mut blk) = blk {
          (mir::Value::pos(inner, mir, &mut function.raw, &mut blk,
            fn_types), Some(blk))
        } else {
          (mir::Value::unit_literal(), None)
        }
      }
      ExprKind::Neg(e) => {
        let (inner, blk) =
          e.translate(mir, function, block, locals, fn_types);
        if let Some(mut blk) = blk {
          (mir::Value::neg(inner, mir, &mut function.raw, &mut blk,
            fn_types), Some(blk))
        } else {
          (mir::Value::unit_literal(), None)
        }
      }
      ExprKind::Not(e) => {
        let (inner, blk) =
          e.translate(mir, function, block, locals, fn_types);
        if let Some(mut blk) = blk {
          (mir::Value::not(inner, mir, &mut function.raw, &mut blk,
            fn_types), Some(blk))
        } else {
          (mir::Value::unit_literal(), None)
        }
      }
      ExprKind::Ref(e) => {
        let (inner, blk) =
          e.translate(mir, function, block, locals, fn_types);
        if let Some(mut blk) = blk {
          (mir::Value::ref_(inner, mir, &mut function.raw, &mut blk,
            fn_types),
          Some(blk))
        } else {
          (mir::Value::unit_literal(), None)
        }
      }
      ExprKind::Deref(e) => {
        let (inner, blk) =
          e.translate(mir, function, block, locals, fn_types);
        if let Some(mut blk) = blk {
          (mir::Value::deref(inner, mir, &mut function.raw, &mut blk,
            fn_types),
          Some(blk))
        } else {
          (mir::Value::unit_literal(), None)
        }
      }
      ExprKind::Field {
        ..
      } => {
        unimplemented!()
      }
      ExprKind::Binop {
        op: Operand::AndAnd,
        lhs,
        rhs,
      } => {
        let then = Block::expr(Expr::bool_lit(false, mir.ty_ctxt()));
        Expr {
          kind: ExprKind::If {
            condition: Box::new(Expr::not(*lhs, mir.ty_ctxt())),
            then_value: Box::new(then),
            else_value: Box::new(Block::expr(*rhs)),
          },
          ty: self.ty,
        }.translate(mir, function, block, locals, fn_types)
      }
      ExprKind::Binop {
        op: Operand::OrOr,
        lhs,
        rhs,
      } => {
        let then = Block::expr(Expr::bool_lit(true, mir.ty_ctxt()));
        Expr {
          kind: ExprKind::If {
            condition: lhs,
            then_value: Box::new(then),
            else_value: Box::new(Block::expr(*rhs)),
          },
          ty: self.ty,
        }.translate(mir, function, block, locals, fn_types)
      }
      ExprKind::Binop {
        op,
        lhs,
        rhs,
      } => {
        let (lhs, blk) = {
          let (lhs, blk) =
            lhs.translate(mir, function, block, locals, fn_types);
          if let Some(blk) = blk {
            (lhs, blk)
          } else {
            return (lhs, None);
          }
        };
        let (rhs, mut blk) = {
          let (rhs, blk) =
            rhs.translate(mir, function, blk, locals, fn_types);
          if let Some(blk) = blk {
            (rhs, blk)
          } else {
            return (rhs, None);
          }
        };
        (match op {
          Operand::Plus => mir::Value::add(
            lhs, rhs, mir, &mut function.raw, &mut blk, fn_types
          ),
          Operand::Minus => mir::Value::sub(
            lhs, rhs, mir, &mut function.raw, &mut blk, fn_types
          ),

          Operand::Mul => mir::Value::mul(
            lhs, rhs, mir, &mut function.raw, &mut blk, fn_types
          ),
          Operand::Div => mir::Value::div(
            lhs, rhs, mir, &mut function.raw, &mut blk, fn_types
          ),
          Operand::Rem => mir::Value::rem(
            lhs, rhs, mir, &mut function.raw, &mut blk, fn_types
          ),

          Operand::And =>
            mir::Value::and(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::Xor =>
            mir::Value::xor(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::Or =>
            mir::Value::or(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),

          Operand::Shl =>
            mir::Value::shl(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::Shr =>
            mir::Value::shr(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),

          Operand::EqualsEquals =>
            mir::Value::eq(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::NotEquals =>
            mir::Value::neq(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::LessThan =>
            mir::Value::lt(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::LessThanEquals =>
            mir::Value::lte(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::GreaterThan =>
            mir::Value::gt(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),
          Operand::GreaterThanEquals =>
            mir::Value::gte(lhs, rhs, mir,
              &mut function.raw, &mut blk, fn_types),

          Operand::AndAnd => unreachable!(),
          Operand::OrOr => unreachable!(),
          Operand::Not => panic!("ICE: Not (`!`) is not a binop"),
        }, Some(blk))
      }
      ExprKind::Call {
        callee,
        args,
      } => {
        let mut mir_args = Vec::new();
        for arg in args {
          let (arg, blk) = arg.translate(mir, function, block, locals,
            fn_types);
          if let Some(blk) = blk {
            block = blk;
          } else {
            return (mir::Value::unit_literal(), None);
          }
          mir_args.push(arg);
        }
        (mir::Value::call(callee, mir_args, mir,
          &mut function.raw, &mut block, fn_types),
        Some(block))
      }
      ExprKind::If {
        condition,
        then_value,
        else_value,
      } => {
        let (cond, blk) = condition.translate(mir, function, block,
          locals, fn_types);
        let (then_blk, else_blk, join, res) = if let Some(blk) = blk {
          blk.if_else(self.ty, cond,
            mir, &mut function.raw, fn_types)
        } else {
          return (mir::Value::unit_literal(), None);
        };

        let (expr, then_blk) = Self::translate_block(*then_value, mir,
          function, then_blk, locals, fn_types);
        if let Some(then_blk) = then_blk {
          then_blk.finish(&mut function.raw, expr);
        }

        let (expr, else_blk) = Self::translate_block(*else_value, mir,
          function, else_blk, locals, fn_types);
        if let Some(else_blk) = else_blk {
          else_blk.finish(&mut function.raw, expr);
        }
        (res, Some(join))
      }
      ExprKind::Return(ret) => {
        let (value, block) = ret.translate(mir, function, block, locals,
          fn_types);
        if let Some(block) = block {
          block.early_ret(&mut function.raw, value);
        }
        (mir::Value::unit_literal(), None)
      }
      ExprKind::Assign {
        dst,
        src,
      } => {
        let (value, blk) =
          src.translate(mir, function, block, locals, fn_types);
        let blk = if let Some(mut blk) = blk {
          match dst.kind {
            ExprKind::Variable(name) => {
              let var = if let Some(var) = locals.get(&name) {
                *var
              } else if let Some(&(num, _)) =
                  function.args.get(&name) {
                function.raw.get_param_local(num as u32)
              } else {
                panic!("ICE: unknown variable: {}", name)
              };
              blk.set(var, value, &mut function.raw);
              Some(blk)
            }
            ExprKind::Deref(inner) => {
              let (ptr, mut blk) =
                inner.translate(mir, function, blk, locals,
                  fn_types);
              if let Some(ref mut blk) = blk {
                blk.store(ptr, value, mir,
                  &mut function.raw, fn_types);
              }
              blk
            }
            e => panic!("ICE: unsupported lvalue: {:?}", e),
          }
        } else { None };
        (mir::Value::unit_literal(), blk)
      }
      ExprKind::Block(body) => {
        Self::translate_block(*body, mir, function, block, locals,
          fn_types)
      }
    }
  }

  pub fn translate_block(body: Block<'t>, mir: &mir::Mir<'t>,
      function: &mut Function<'t>, block: mir::Block,
      locals: &mut HashMap<String, mir::Local>,
      fn_types: &HashMap<String, ty::Function<'t>>)
      -> (mir::Value, Option<mir::Block>) {
    let mut block = Some(block);
    for stmt in body.stmts {
      if let Some(blk) = block.take() {
        match stmt {
          Stmt::Let {
            name,
            ty,
            value,
          } => {
            let var = function.raw.new_local(ty);
            locals.insert(name, var);
            if let Some(value) = value {
              let (value, blk) =
                value.translate(mir, function, blk,
                  locals, fn_types);
              if let Some(mut blk) = blk {
                blk.set(var, value,
                  &mut function.raw);
                block = Some(blk);
              }
            } else {
              block = Some(blk);
            }
          }
          Stmt::Expr(e) => {
            let (value, blk) = e.translate(mir, function, blk,
              locals, fn_types);
            if let Some(mut blk) = blk {
              blk.set_tmp(value,
                mir, &mut function.raw, fn_types);
              block = Some(blk);
            }
          }
        }
      } else {
        break;
      }
    }
    if let Some(e) = body.expr {
      if let Some(blk) = block {
        e.translate(mir, function, blk, locals, fn_types)
      } else {
        (mir::Value::unit_literal(), None)
      }
    } else {
      (mir::Value::unit_literal(), block)
    }
  }
}
