pub struct IDData {
    pub lucky_numbers: [Field; 2],
    pub age: Field,
}


fn main(x: [IDData; 1]) {
    assert_eq(x[0].age, x[0].lucky_numbers[0] * x[0].lucky_numbers[1]);
}