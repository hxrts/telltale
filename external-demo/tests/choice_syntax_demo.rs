use external_demo::compile_choreography;

#[test]
fn modern_choice_syntax_is_accepted() {
    let compiled = compile_choreography(
        r#"
protocol TestChoice =
  roles Alice, Bob
  choice Alice at
    | Option1 =>
      Alice -> Bob : Message1
    | Option2 =>
      Alice -> Bob : Message2
"#,
    )
    .expect("compile choreography");

    assert_eq!(compiled.role_names(), vec!["Alice", "Bob"]);
}

#[test]
fn legacy_brace_protocol_syntax_is_rejected() {
    let legacy = r#"
protocol PingPong = {
    roles Alice, Bob
    Alice -> Bob : Ping
    Bob -> Alice : Pong
}
"#;

    assert!(compile_choreography(legacy).is_err());
}

#[test]
fn legacy_choice_block_syntax_is_rejected() {
    let legacy = r#"
protocol TestChoice = {
    roles Alice, Bob
    choice at Alice {
        Option1 -> {
            Alice -> Bob : Message1
        }
        Option2 -> {
            Alice -> Bob : Message2
        }
    }
}
"#;

    assert!(compile_choreography(legacy).is_err());
}
