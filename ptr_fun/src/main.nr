
fn foo(x: Field) -> Field {
  x + 1
}


fn main(x: pub u32, y: pub u32) {
  let z = foo(10);

  let x = if (z == 11) {
    10
  } else {
    10
  };

  let y = if (z == 12) {
    11
  } else {
    x
  };

  assert(x == y);
}
