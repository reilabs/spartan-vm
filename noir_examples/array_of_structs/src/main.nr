pub struct IDData {
    pub age: Field,
    pub id: Field,
}


fn main(x: [IDData; 2], ind: u32) {
    assert_eq(x[ind].age, 18);
}