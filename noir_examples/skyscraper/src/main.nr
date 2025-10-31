use skyscraper_noir::compress;

fn main(x: Field, y: pub Field, z: pub Field) {
  assert(compress(x, y) == z);
}
