fn main(claimed_be: pub [Field; 8], result: pub Field) {
  let mut result_recovered = 0;

  let mut this_is_silly = 0;

  for i in 0..8 {
    this_is_silly *= 2;
    this_is_silly += claimed_be[i];
  }

  for i in 0..8 {
    result_recovered *= 2;
    result_recovered += claimed_be[i];
  }
  assert(result == result_recovered);
}
