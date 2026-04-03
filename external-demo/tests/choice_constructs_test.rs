use external_demo::compile_choreography;

#[test]
fn modern_choice_constructs_compile_and_project() {
    let compiled = compile_choreography(
        r#"
protocol Purchase =
  roles Buyer, Seller
  choice Seller at
    | Accept =>
      Seller -> Buyer : Confirmation
    | Reject =>
      Seller -> Buyer : Rejection
"#,
    )
    .expect("compile choreography");

    assert_eq!(compiled.role_names(), vec!["Buyer", "Seller"]);
    assert!(compiled.local_type("Buyer").is_some());
    assert!(compiled.local_type("Seller").is_some());
}

#[test]
fn nested_choices_still_go_through_the_shared_frontend() {
    let compiled = compile_choreography(
        r#"
protocol MultiPath =
  roles Alice, Bob, Carol
  choice Alice at
    | RouteBob =>
      Alice -> Bob : Ping
      choice Bob at
        | Forward =>
          Bob -> Carol : Relay
        | Abort =>
          Bob -> Alice : Abort
    | RouteCarol =>
      Alice -> Carol : Direct
"#,
    )
    .expect("compile choreography");

    assert_eq!(compiled.role_names(), vec!["Alice", "Bob", "Carol"]);
    assert_eq!(compiled.local_types.len(), 3);
}
