fn main(claimed_be: pub [Field; 8], result: pub Field) {
  let mut result_recovered = 0;
  for i in 0..8 {
    result_recovered *= 2;
    result_recovered += claimed_be[i];
  }
  assert(result == result_recovered);
}
