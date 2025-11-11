fn main(mut x: [Field; 3], y: pub Field) {
  let r = x[0] * x[1] * x[2];
  assert(r == y);
}
