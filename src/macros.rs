macro_rules! fl {
  () => ((file!(), line!()));
  ($line:expr) => ((file!(), $line));
}

macro_rules! span {
  ($tok:expr, $loc:expr $(,)*) => (
    $crate::parse::Spanned {
      thing: $tok,
      start: $loc,
      end: Some($loc),
    }
  );
  ($tok:expr, $loc:expr, None $(,)*) => (
    $crate::parse::Spanned {
      thing: $tok,
      start: $loc,
      end: None,
    }
  );
  ($tok:expr, $loc:expr, $end_loc:expr $(,)*) => (
    $crate::parse::Spanned {
      thing: $tok,
      start: $loc,
      end: Some($end_loc),
    }
  );
}
