pub struct IDData {
    age: u8,
    lucky_number: Field,
}

fn main(x: [IDData; 1]) {
    assert(x[0].age < 100, "Age must be less than 100");
}