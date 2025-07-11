use poseidon::poseidon::bn254;

pub trait BinaryHasher<F> {
    fn hash(a: F, b: F) -> F;
}

struct Poseidon;

impl BinaryHasher<Field> for Poseidon {
    fn hash(a: Field, b: Field) -> Field {
        bn254::hash_2([a, b])
    }

}

struct DummyHasher;


struct x {
    x : &mut u32
}

impl BinaryHasher<Field> for DummyHasher {
    fn hash(a: Field, b: Field) -> Field {
        (a + 2) * b // Simple addition as a placeholder for hashing
    }
}

pub fn mtree_recover<H, let N: u32>(idx: [bool; N], p: [Field; N], item: Field) -> Field
where
    H: BinaryHasher<Field>,
{
    let mut curr_h = item;
    for i in 0..N {
        let dir = idx[i];
        let sibling_root = p[i];
        curr_h = if dir {
            H::hash(sibling_root, curr_h)
        } else {
            H::hash(curr_h, sibling_root)
        }
    }
    curr_h
}

fn main(root: pub Field, proof: pub [Field; 4], item: pub Field, idx: [bool; 4]) {
    let calculated_root = mtree_recover::<DummyHasher, _>(idx, proof, item);
    assert_eq(root, calculated_root);
    // assert(root != item)
}
