fn main(mut x: Field, y: pub Field) {
  let mut r = 1;
  for i in 0..3 {
    r *= x;
  }
  assert(r == y);
}
