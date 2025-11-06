use poseidon2::bn254::perm;

fn main(x: Field) {
  //let r = perm::x5_2([x,x]);
  //let r = perm::x5_3([x,x,x]);
  //let r = perm::x5_4([x,x,x,x]);
  //let r = perm::x5_8([x,x,x,x,x,x,x,x]);
  let r = perm::x5_16([x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x]);
  assert_eq(r[0], x);
}
