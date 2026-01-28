pub struct IDData {
    pub age: Field,
    pub id: Field,
}


fn main(x: [IDData; 1]) {
    assert_eq(x[0].age, x[0].age);
}