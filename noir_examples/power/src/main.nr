fn main(mut x: Field, y: pub Field) {
  let mut r = 1;
  for i in 0..1000000 {
    r *= x;
  }
  assert(r == y);
}
