pub struct IDData {
    pub lucky_number: Field,
    pub age: Field,
}


fn main(x: IDData) {
    assert_eq(2 * x.age, x.lucky_number);
}