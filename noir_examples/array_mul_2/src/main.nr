fn main(a: Field, b: Field, y: pub Field) {
  let arr = [a, b];
  assert_eq(arr[0] * arr[1], y);
}
