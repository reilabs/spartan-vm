use poseidon2::bn254::perm;

fn main(x: Field) {
  let r = perm::x5_16([x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x]);
  assert_eq(r[0], x);
}
