use skyscraper_noir::compress;

fn main(x: Field, z: pub Field) {
  let mut r = x;
  for i in 0..1 {
    r = compress(r, r);
  }
}
