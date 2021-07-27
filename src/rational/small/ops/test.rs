use crate::R16;

#[test]
fn mul() {
    let mut x = R16!(21, 1);
    x *= &R16!(1, 7);
    assert_eq!(x, R16!(3));
}
