use super::check_types;

#[test]
fn diverging_fallback_to_unit_1() {
    check_types(
        r#"
fn test() {
    let t = if true {
        Default::default()
    } else {
        return;
    };
    t;
} //^ ()
"#,
    );
}

#[test]
fn diverging_fallback_to_unit_2() {
    check_types(
        r#"
fn test() -> i32 {
    let t = match () {
        _ => { return 3; },
        _ => Default::default(),
    };
    t;
    2
} //^ ()
"#,
    );
}

#[test]
fn diverging_fallback_to_unit_3() {
    check_types(
        r#"
fn test() {
    let t = Default::default();
      //^ ()
    let a = [t, return];
      //^ [(); 2]
}
"#,
    );
}

#[test]
fn diverging_fallback_to_unit_4() {
    check_types(
        r#"
fn g<T: Default>() -> Result<T, ()> {
    Ok(T::default())
}

fn test() -> Result<(), ()> {
    let t = g()?;
      //^ ()
    Ok(())
}
"#,
    );
}
