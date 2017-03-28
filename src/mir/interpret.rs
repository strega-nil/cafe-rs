use mir::{self, Mir};
use ty;

const READ_FROM_UNINIT: &'static str =
  "Attempt to read from an uninitialized value";

// TODO(ubsan): represent uninit data
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Value {
  S8(i8),
  S16(i16),
  S32(i32),
  S64(i64),
  U8(u8),
  U16(u16),
  U32(u32),
  U64(u64),
  Bool(bool),
  Unit,
}

#[derive(Copy, Clone)]
struct Reference(pub usize);

impl mir::Literal {
  fn to_interp_value(&self) -> Value {
    use mir::Literal::*;
    match *self {
      Unit => Value::Unit,
      Bool(b) => Value::Bool(b),
      Int { value, signed: true, ty: ty::Int::I8 } => Value::S8(value as _),
      Int { value, signed: true, ty: ty::Int::I16 } => Value::S16(value as _),
      Int { value, signed: true, ty: ty::Int::I32 } => Value::S32(value as _),
      Int { value, signed: true, ty: ty::Int::I64 } => Value::S64(value as _),
      Int { value, signed: false, ty: ty::Int::I8 } => Value::U8(value as _),
      Int { value, signed: false, ty: ty::Int::I16 } => Value::U16(value as _),
      Int { value, signed: false, ty: ty::Int::I32 } => Value::U32(value as _),
      Int { value, signed: false, ty: ty::Int::I64 } => Value::U64(value as _),
    }
  }
}

macro_rules! from_impl {
  ($($typ:ty => $cnstr:path),*$(,)*) => (
    $(impl From<$typ> for Value {
      fn from(x: $typ) -> Value {
        $cnstr(x)
      }
    })*
  )
}

from_impl!{
  bool => Value::Bool,
  u8 => Value::U8,
  u16 => Value::U16,
  u32 => Value::U32,
  u64 => Value::U64,
  i8 => Value::S8,
  i16 => Value::S16,
  i32 => Value::S32,
  i64 => Value::S64,
}

struct Runner<'a, 't> where 't: 'a {
  mir: &'a Mir<'t>,
  stack: Vec<Option<Value>>,
}

impl<'a, 't> Runner<'a, 't> {
  fn new(mir: &'a Mir<'t>) -> Self {
    Runner {
      mir,
      stack: vec![],
    }
  }

  fn call(&mut self, name: &str, params: Vec<Reference>) -> Value {
    use mir::Lvalue as Lv;
    use mir::Terminator as Tm;

    let func = self.mir.functions.get(name).expect("D:");
    let mut cur_block = &func.blocks[0];

    let base = self.stack.len();
    for _ in &func.locals { self.stack.push(None) }
    let locals = func.locals
      .iter()
      .enumerate()
      .map(|(i, _)| Reference(i + base))
      .collect::<Vec<_>>();

    loop {
      for &mir::Statement(ref lv, ref rv) in &cur_block.statements {
        let val = rv.to_interp_value(self, &params, &locals);
        match *lv {
          Lv::Local(loc) => self.stack[locals[loc.0 as usize].0] = Some(val),
        }
      }
      match cur_block.terminator {
        Tm::Goto(mir::Block(n)) => cur_block = &func.blocks[n],
        Tm::If {
          cond,
          then_blk,
          else_blk,
        } => {
          let tmp = match self.stack[base + cond.0 as usize] {
            Some(ref stk) => stk,
            None => panic!("{}", READ_FROM_UNINIT),
          };
          if let Value::Bool(cond) = *tmp {
            if cond {
              cur_block = &func.blocks[then_blk.0];
            } else {
              cur_block = &func.blocks[else_blk.0];
            }
          } else {
            unreachable!()
          }
        },
        Tm::Return => {
          return self
            .stack[base]
            .expect("return never written to");
        },
      }
    }
  }
}

impl<'t> Mir<'t> {
  pub fn run(&self) {
    Runner::new(self).call("main", vec![]);
  }
}

impl mir::Value {
  fn to_interp_value(
    &self,
    runner: &mut Runner,
    params: &[Reference],
    locals: &[Reference],
  ) -> Value {
    use mir::ValueKind as Vk;
    use mir::{Local, Parameter};
    use std::ops::{Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr};
    macro_rules! cmp {
      ($runner:ident[$locals:ident] => $func:path {$lhs:expr, $rhs:expr}) => (
        match (
          &$runner.stack[$locals[$lhs as usize].0],
          &$runner.stack[$locals[$rhs as usize].0],
        ) {
          (&Some(Value::S8(ref lhs)), &Some(Value::S8(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S16(ref lhs)), &Some(Value::S16(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S32(ref lhs)), &Some(Value::S32(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S64(ref lhs)), &Some(Value::S64(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U8(ref lhs)), &Some(Value::U8(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U16(ref lhs)), &Some(Value::U16(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U32(ref lhs)), &Some(Value::U32(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U64(ref lhs)), &Some(Value::U64(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::Bool(ref lhs)), &Some(Value::Bool(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::Unit), &Some(Value::Unit)) =>
            Value::from($func(&(), &())),
          (&None, _) | (_, &None) =>
            panic!("{}", READ_FROM_UNINIT),
          _ => unreachable!(),
        }
      )
    }
    macro_rules! op {
    ($runner:ident[$locals:ident] => $func:path {$lhs:expr, $rhs:expr}) => (
        match (
          &$runner.stack[$locals[$lhs as usize].0],
          &$runner.stack[$locals[$rhs as usize].0],
        ) {
          (&Some(Value::S8(ref lhs)), &Some(Value::S8(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S16(ref lhs)), &Some(Value::S16(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S32(ref lhs)), &Some(Value::S32(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S64(ref lhs)), &Some(Value::S64(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U8(ref lhs)), &Some(Value::U8(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U16(ref lhs)), &Some(Value::U16(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U32(ref lhs)), &Some(Value::U32(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U64(ref lhs)), &Some(Value::U64(ref rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::Bool(_)), &Some(Value::Bool(_))) => unreachable!(),
          (&Some(Value::Unit), &Some(Value::Unit)) => unreachable!(),
          (&None, _) | (_, &None) =>
            panic!("{}", READ_FROM_UNINIT),
          _ => unreachable!(),
        }
      )
    }
    macro_rules! bitop {
    ($runner:ident[$locals:ident] => $func:path {$lhs:expr, $rhs:expr}) => (
        match (
          &$runner.stack[$locals[$lhs as usize].0],
          &$runner.stack[$locals[$rhs as usize].0],
        ) {
          (&Some(Value::S8(lhs)), &Some(Value::S8(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S16(lhs)), &Some(Value::S16(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S32(lhs)), &Some(Value::S32(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::S64(lhs)), &Some(Value::S64(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U8(lhs)), &Some(Value::U8(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U16(lhs)), &Some(Value::U16(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U32(lhs)), &Some(Value::U32(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::U64(lhs)), &Some(Value::U64(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::Bool(lhs)), &Some(Value::Bool(rhs))) =>
            Value::from($func(lhs, rhs)),
          (&Some(Value::Unit), &Some(Value::Unit)) => unreachable!(),
          (&None, _) | (_, &None) =>
            panic!("{}", READ_FROM_UNINIT),
          _ => unreachable!(),
        }
      )
    }
    macro_rules! shift_rhs {
      ($lhs:expr, $runner:ident[$locals:ident] => $func:path {$rhs:expr}) => (
        match $runner.stack[$locals[$rhs as usize].0] {
          Some(Value::U8(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::U16(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::U32(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::U64(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::S8(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::S16(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::S32(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::S64(rhs)) => Value::from($func($lhs, rhs)),
          Some(Value::Bool(_)) | Some(Value::Unit) => unreachable!(),
          None => panic!("{}", READ_FROM_UNINIT),
        }
      )
    }
    macro_rules! shift {
      ($runner:ident[$locals:ident] => $func:path {$lhs:expr, $rhs:expr}) => (
        match runner.stack[locals[$lhs as usize].0] {
          Some(Value::U8(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::U16(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::U32(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::U64(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::S8(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::S16(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::S32(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::S64(lhs))
          => shift_rhs!(lhs, runner[locals] => $func{$rhs}),
          Some(Value::Bool(_)) | Some(Value::Unit) => unreachable!(),
          None => panic!("{}", READ_FROM_UNINIT),
        }
      )
    }
    match self.0 {
      Vk::Literal(ref lit) => {
        lit.to_interp_value()
      },
      Vk::Local(Local(n)) => {
        runner.stack[locals[n as usize].0]
          .clone()
          .expect(READ_FROM_UNINIT)
      },
      Vk::Parameter(Parameter(n)) => {
        runner.stack[params[n as usize].0].clone().expect(READ_FROM_UNINIT)
      },
      Vk::Call {
        ref callee,
        ref args,
      } => {
        let args = args
          .iter()
          .map(|&mir::Local(n)| locals[n as usize])
          .collect();
        runner.call(callee, args)
      },
      Vk::Pos(Local(inner)) => {
        match runner.stack[locals[inner as usize].0] {
          Some(Value::S8(inner)) => Value::from(inner),
          Some(Value::S16(inner)) => Value::from(inner),
          Some(Value::S32(inner)) => Value::from(inner),
          Some(Value::S64(inner)) => Value::from(inner),
          Some(Value::U8(inner)) => Value::from(inner),
          Some(Value::U16(inner)) => Value::from(inner),
          Some(Value::U32(inner)) => Value::from(inner),
          Some(Value::U64(inner)) => Value::from(inner),
          Some(Value::Bool(_)) | Some(Value::Unit) => unreachable!(),
          None => panic!(READ_FROM_UNINIT),
        }
      },
      Vk::Neg(Local(inner)) => {
        match runner.stack[locals[inner as usize].0] {
          Some(Value::S8(inner)) => Value::from(-inner),
          Some(Value::S16(inner)) => Value::from(-inner),
          Some(Value::S32(inner)) => Value::from(-inner),
          Some(Value::S64(inner)) => Value::from(-inner),
          Some(Value::U8(_))
          | Some(Value::U16(_))
          | Some(Value::U32(_))
          | Some(Value::U64(_))
          | Some(Value::Bool(_))
          | Some(Value::Unit)
          => unreachable!(),
          None => panic!(READ_FROM_UNINIT),
        }
      },
      Vk::Not(Local(inner)) => {
        match runner.stack[locals[inner as usize].0] {
          Some(Value::S8(inner)) => Value::from(!inner),
          Some(Value::S16(inner)) => Value::from(!inner),
          Some(Value::S32(inner)) => Value::from(!inner),
          Some(Value::S64(inner)) => Value::from(!inner),
          Some(Value::U8(inner)) => Value::from(!inner),
          Some(Value::U16(inner)) => Value::from(!inner),
          Some(Value::U32(inner)) => Value::from(!inner),
          Some(Value::U64(inner)) => Value::from(!inner),
          Some(Value::Bool(inner)) => Value::from(!inner),
          Some(Value::Unit) => unreachable!(),
          None => panic!(READ_FROM_UNINIT),
        }
      },
      Vk::Eq(Local(lhs), Local(rhs)) => {
        cmp!(runner[locals] => PartialEq::eq{lhs, rhs})
      },
      Vk::Neq(Local(lhs), Local(rhs)) => {
        cmp!(runner[locals] => PartialEq::ne{lhs, rhs})
      },
      Vk::Lte(Local(lhs), Local(rhs)) => {
        cmp!(runner[locals] => PartialOrd::le{lhs, rhs})
      },
      Vk::Gte(Local(lhs), Local(rhs)) => {
        cmp!(runner[locals] => PartialOrd::ge{lhs, rhs})
      },
      Vk::Lt(Local(lhs), Local(rhs)) => {
        cmp!(runner[locals] => PartialOrd::lt{lhs, rhs})
      },
      Vk::Gt(Local(lhs), Local(rhs)) => {
        cmp!(runner[locals] => PartialOrd::gt{lhs, rhs})
      },
      Vk::Add(Local(lhs), Local(rhs)) => {
        op!(runner[locals] => Add::add{lhs, rhs})
      },
      Vk::Sub(Local(lhs), Local(rhs)) => {
        op!(runner[locals] => Sub::sub{lhs, rhs})
      },
      Vk::Mul(Local(lhs), Local(rhs)) => {
        op!(runner[locals] => Mul::mul{lhs, rhs})
      },
      Vk::Div(Local(lhs), Local(rhs)) => {
        op!(runner[locals] => Div::div{lhs, rhs})
      },
      Vk::Rem(Local(lhs), Local(rhs)) => {
        op!(runner[locals] => Rem::rem{lhs, rhs})
      },
      Vk::Shl(Local(lhs), Local(rhs)) => {
        shift!(runner[locals] => Shl::shl{lhs, rhs})
      },
      Vk::Shr(Local(lhs), Local(rhs)) => {
        shift!(runner[locals] => Shr::shr{lhs, rhs})
      },
      Vk::And(Local(lhs), Local(rhs)) => {
        bitop!(runner[locals] => BitAnd::bitand{lhs, rhs})
      },
      Vk::Or(Local(lhs), Local(rhs)) => {
        bitop!(runner[locals] => BitOr::bitor{lhs, rhs})
      },
      Vk::Xor(Local(lhs), Local(rhs)) => {
        bitop!(runner[locals] => BitXor::bitxor{lhs, rhs})
      },
      Vk::Log(Local(n)) => {
        if let Some(logged) = runner.stack[locals[n as usize].0] {
          println!("{:?}", logged);
        } else {
          println!("[uninitialized]");
        }
        Value::Unit
      },
    }
  }
}

