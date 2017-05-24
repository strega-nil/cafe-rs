use parse::{Item, Parser, ParserErrorVariant, Spanned};

pub struct Ast {
  items: Vec<Item>,
}

impl Ast {
  pub fn new(file: &str) -> Self {
    let mut parse = Parser::new(file);
    let mut items = vec![];
    loop {
      match parse.next_item() {
        Ok(item) => items.push(item),
        Err(Spanned {
          thing: ParserErrorVariant::ExpectedEof,
          ..
        }) => break,
        Err(e) => panic!("error: {:?}", e),
      }
    }
    Ast {
      items
    }
  }

  pub fn print(&self) {
    for item in &self.items {
      println!("{:#?}", item.thing);
    }
  }
}
