use super::{
  Mir,
  Function,
  Terminator,
  Statement,
  Lvalue,
  Literal,
  Value,
  ValueKind,
  Local,
  Parameter,
};
use std::fmt::{Debug, Display, Formatter, Error};

struct Displayer<'a, 't, T>(&'a T, &'a Function<'t>) where 't: 'a, T: 'a;

impl<'t> Display for Function<'t> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    for (i, var) in self.locals.iter().enumerate() {
      writeln!(f, "  let {}_{}: {};", self.local_names[i], i, var)?;
    }
    for (i, block) in self.blocks.iter().enumerate() {
      writeln!(f, "bb{}:", i)?;
      for stmt in &block.statements {
        writeln!(f, "  {};", Displayer(stmt, self))?;
      }
      writeln!(f, "  {};", Displayer(&block.terminator, self))?;
    }
    Ok(())
  }
}

impl<'a, 't> Display for Displayer<'a, 't, Terminator> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    match *self.0 {
      Terminator::Goto(ref b) => write!(f, "goto -> bb{}", b.0),
      Terminator::Return => write!(f, "return"),
      Terminator::If {
        ref cond,
        ref then_blk,
        ref else_blk,
      } => write!(f,
        "if({}) -> [true: bb{}, false: bb{}]",
        Displayer(cond, self.1),
        then_blk.0,
        else_blk.0,
      ),
    }
  }
}

impl<'a, 't> Display for Displayer<'a, 't, Statement> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    write!(f,
      "{} = {}",
      Displayer(&(self.0).0, self.1),
      Displayer(&(self.0).1, self.1),
    )
  }
}

impl<'a, 't> Display for Displayer<'a, 't, Lvalue> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    match *self.0 {
      Lvalue::Local(ref loc) => write!(f, "{}", Displayer(loc, self.1)),
    }
  }
}

impl Display for Literal {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    match *self {
      Literal::Int {
        signed,
        value,
        ..
      } => {
        if signed {
          write!(f, "{}", value as i64)
        } else {
          write!(f, "{}", value as u64)
        }
      }
      Literal::Bool(ref value) => write!(f, "{}", value),
      Literal::Unit => {
        write!(f, "()")
      }
    }
  }
}

impl<'a, 't> Display for Displayer<'a, 't, Value> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    macro_rules! binop {
      ($f:expr, $name:ident($lhs:expr, $rhs:expr)) => (
        write!($f,
          concat!(stringify!($name), "({}, {})"),
          Displayer($lhs, self.1),
          Displayer($rhs, self.1),
        )
      )
    }
    match (self.0).0 {
      ValueKind::Literal(ref lit) => write!(f, "lit {}", lit),
      ValueKind::Parameter(ref par) => write!(f, "{}", par),
      ValueKind::Local(ref loc) => write!(f, "{}", Displayer(loc, self.1)),
      ValueKind::Pos(ref inner)
      => write!(f, "Pos({})", Displayer(inner, self.1)),
      ValueKind::Neg(ref inner)
      => write!(f, "Neg({})", Displayer(inner, self.1)),
      ValueKind::Not(ref inner)
      => write!(f, "Not({})", Displayer(inner, self.1)),
      ValueKind::Add(ref lhs, ref rhs) => binop!(f, Add(lhs, rhs)),
      ValueKind::Sub(ref lhs, ref rhs) => binop!(f, Sub(lhs, rhs)),
      ValueKind::Mul(ref lhs, ref rhs) => binop!(f, Mul(lhs, rhs)),
      ValueKind::Div(ref lhs, ref rhs) => binop!(f, Div(lhs, rhs)),
      ValueKind::Rem(ref lhs, ref rhs) => binop!(f, Rem(lhs, rhs)),
      ValueKind::And(ref lhs, ref rhs) => binop!(f, And(lhs, rhs)),
      ValueKind::Xor(ref lhs, ref rhs) => binop!(f, Xor(lhs, rhs)),
      ValueKind::Or(ref lhs, ref rhs) => binop!(f, Or(lhs, rhs)),
      ValueKind::Shl(ref lhs, ref rhs) => binop!(f, Shl(lhs, rhs)),
      ValueKind::Shr(ref lhs, ref rhs) => binop!(f, Shr(lhs, rhs)),

      ValueKind::Eq(ref lhs, ref rhs) => binop!(f, Eq(lhs, rhs)),
      ValueKind::Neq(ref lhs, ref rhs) => binop!(f, Neq(lhs, rhs)),
      ValueKind::Lt(ref lhs, ref rhs) => binop!(f, Lt(lhs, rhs)),
      ValueKind::Lte(ref lhs, ref rhs) => binop!(f, Lte(lhs, rhs)),
      ValueKind::Gt(ref lhs, ref rhs) => binop!(f, Gt(lhs, rhs)),
      ValueKind::Gte(ref lhs, ref rhs) => binop!(f, Gte(lhs, rhs)),

      ValueKind::Log(ref val) => write!(f, "log({})", Displayer(val, self.1)),
      ValueKind::Call {
        ref callee,
        ref args,
      } => {
        write!(f, "{}(", callee)?;
        if args.len() != 0 {
          for arg in &args[..args.len() - 1] {
            write!(f, "{}, ", Displayer(arg, self.1))?;
          }
          write!(f, "{}", Displayer(&args[args.len() - 1], self.1))?;
        }
        write!(f, ")")
      }
    }
  }
}

impl<'a, 't> Display for Displayer<'a, 't, Local> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    write!(f, "{}_{}", (self.1).local_names[(self.0).0 as usize], (self.0).0)
  }
}

impl Display for Parameter {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    write!(f, "par{}", self.0)
  }
}

impl<'t> Display for Mir<'t> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    for (name, function) in &self.functions {
      write!(f, "fn {}(", name)?;
      let inputs = function.ty.input();
      if inputs.len() != 0 {
        for input in &inputs[..inputs.len() - 1] {
          write!(f, "{}, ", input)?;
        }
        write!(f, "{}", inputs[inputs.len() - 1])?;
      }
      writeln!(f, ") -> {} {{", function.ty.output())?;
      write!(f, "{}", function)?;
      writeln!(f, "}}\n")?;
    }
    Ok(())
  }
}
impl<'t> Debug for Mir<'t> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    write!(f, "{}", self)
  }
}
