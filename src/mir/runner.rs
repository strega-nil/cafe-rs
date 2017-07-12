use super::Mir;

pub struct Runner {
}

impl Runner {
  pub fn new(_mir: &Mir) -> Self {
    Runner {}
  }

  pub fn call(&mut self, _name: &str) -> i32 {
    0
  }
}
