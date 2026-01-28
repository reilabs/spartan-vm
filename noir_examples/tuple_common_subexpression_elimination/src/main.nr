pub struct IDData {
    pub age: Field,
    pub id: Field,
}


fn main(x: [IDData; 1]) {
    assert_eq(x[0].age, 1);
    assert_eq(x[0].age, 2);
    assert_eq(x[0].age, 3);
    assert_eq(x[0].age, 4);
    assert_eq(x[0].age, 5);
    assert_eq(x[0].age, 6);
}