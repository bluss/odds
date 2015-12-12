
#[test]
fn parse_dot_is_ok_0_0() {
    assert_eq!(".".parse::<f64>(), Ok(0.0));
}
