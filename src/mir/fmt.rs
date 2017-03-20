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

impl<'t> Display for Function<'t> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    for (i, var) in self.locals.iter().enumerate() {
      writeln!(f, "  let v{}: {};", i, var)?;
    }
    for (i, tmp) in self.temporaries.iter().enumerate() {
      writeln!(f, "  let tmp{}: {};", i, tmp)?;
    }
    for (i, block) in self.blocks.iter().enumerate() {
      writeln!(f, "bb{}:", i)?;
      for stmt in &block.statements {
        writeln!(f, "  {};", stmt)?;
      }
      writeln!(f, "  {};", block.terminator)?;
    }
    Ok(())
  }
}

impl Display for Terminator {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    match *self {
      Terminator::Goto(ref b) => write!(f, "goto -> bb{}", b.0),
      Terminator::Return => write!(f, "return"),
      Terminator::If {
        ref cond,
        ref then_blk,
        ref else_blk,
      } => write!(
        f, "if({}) -> [true: bb{}, false: bb{}]", cond, then_blk.0, else_blk.0,
      ),
    }
  }
}

impl Display for Statement {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    write!(f, "{} = {}", self.0, self.1)
  }
}

impl Display for Lvalue {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    match *self {
      Lvalue::Return => write!(f, "return"),
      Lvalue::Local(ref loc) => write!(f, "{}", loc),
      Lvalue::Deref(ref ptr) => write!(f, "*{}", ptr),
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
      Literal::Tuple(ref v) => {
        write!(f, "(")?;
        if v.len() == 0 {
          write!(f, ")")
        } else {
          for el in &v[..v.len() - 1] {
            write!(f, "{}, ", el)?;
          }
          write!(f, "{})", v[v.len() - 1])
        }
      }
    }
  }
}

impl Display for Value {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    match self.0 {
      ValueKind::Literal(ref lit) => write!(f, "lit {}", lit),
      ValueKind::Parameter(ref par) => write!(f, "{}", par),
      ValueKind::Lvalue(ref lv) => write!(f, "{}", lv),
      ValueKind::Pos(ref inner) => write!(f, "Pos({})", inner),
      ValueKind::Neg(ref inner) => write!(f, "Neg({})", inner),
      ValueKind::Not(ref inner) => write!(f, "Not({})", inner),
      ValueKind::Ref(ref inner) => write!(f, "&{}", inner),
      ValueKind::Add(ref lhs, ref rhs) => write!(f, "Add({}, {})", lhs, rhs),
      ValueKind::Sub(ref lhs, ref rhs) => write!(f, "Sub({}, {})", lhs, rhs),
      ValueKind::Mul(ref lhs, ref rhs) => write!(f, "Mul({}, {})", lhs, rhs),
      ValueKind::Div(ref lhs, ref rhs) => write!(f, "Div({}, {})", lhs, rhs),
      ValueKind::Rem(ref lhs, ref rhs) => write!(f, "Rem({}, {})", lhs, rhs),
      ValueKind::And(ref lhs, ref rhs) => write!(f, "And({}, {})", lhs, rhs),
      ValueKind::Xor(ref lhs, ref rhs) => write!(f, "And({}, {})", lhs, rhs),
      ValueKind::Or(ref lhs, ref rhs) => write!(f, "And({}, {})", lhs, rhs),
      ValueKind::Shl(ref lhs, ref rhs) => write!(f, "Shl({}, {})", lhs, rhs),
      ValueKind::Shr(ref lhs, ref rhs) => write!(f, "Shr({}, {})", lhs, rhs),

      ValueKind::Eq(ref lhs, ref rhs) => write!(f, "Eq({}, {})", lhs, rhs),
      ValueKind::Neq(ref lhs, ref rhs) => write!(f, "Neq({}, {})", lhs, rhs),
      ValueKind::Lt(ref lhs, ref rhs) => write!(f, "Lt({}, {})", lhs, rhs),
      ValueKind::Lte(ref lhs, ref rhs) => write!(f, "Lte({}, {})", lhs, rhs),
      ValueKind::Gt(ref lhs, ref rhs) => write!(f, "Gt({}, {})", lhs, rhs),
      ValueKind::Gte(ref lhs, ref rhs) => write!(f, "Gte({}, {})", lhs, rhs),

      ValueKind::Call {
        ref callee,
        ref args,
      } => {
        write!(f, "{}(", callee)?;
        if args.len() != 0 {
          for arg in &args[..args.len() - 1] {
            write!(f, "{}, ", arg)?;
          }
          write!(f, "{}", args[args.len() - 1])?;
        }
        write!(f, ")")
      }
    }
  }
}

impl Display for Local {
  fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
    write!(f, "v{}", self.0)
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
