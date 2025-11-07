use poseidon2::bn254::perm;

fn main(x: Field, y: Field, z: Field, w: Field) {
  //let r = perm::x5_2([x,x]);
  //let r = perm::x5_3([x,x,x]);
  let r = perm::x5_4([x,y,z,w]);
  //let r = perm::x5_8([x,x,x,x,x,x,x,x]);
  //let r = perm::x5_16([x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x]);
}
