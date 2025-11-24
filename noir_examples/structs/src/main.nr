pub struct IDData {
    age: Field,
    lucky_number: Field,
}

fn main(bat: IDData) {
    assert_eq(bat.age, bat.lucky_number + 1);
}