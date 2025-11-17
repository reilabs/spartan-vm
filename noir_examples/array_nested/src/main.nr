fn main(x: [[[Field; 2]; 2]; 2], y: pub Field) {
  assert_eq(x[0][0][0] * x[0][0][1], y);
  assert_eq(x[0][1][0] * x[0][1][1], y);
  assert_eq(x[1][0][0] * x[1][0][1], y);
  assert_eq(x[1][1][0] * x[1][1][1], y);
}
