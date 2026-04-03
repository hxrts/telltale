use external_demo::{compile_choreography, AnnotationScope};

#[test]
fn ordered_annotations_are_extracted_from_the_authoritative_ast() {
    let compiled = compile_choreography(
        r#"
protocol AuditFlow =
  roles Alice, Bob
  Alice { guard_capability : "chat:send", leak : external, leak : neighbor } -> Bob : Msg
"#,
    )
    .expect("compile choreography");

    let sender_annotations = compiled
        .annotation_records()
        .into_iter()
        .filter(|record| {
            record.path == "root"
                && record.scope == AnnotationScope::Sender
                && record.role.as_deref() == Some("Alice")
        })
        .collect::<Vec<_>>();

    assert_eq!(
        sender_annotations
            .iter()
            .map(|record| record.key.as_str())
            .collect::<Vec<_>>(),
        vec!["guard_capability", "leak", "leak"]
    );
    assert_eq!(
        sender_annotations
            .iter()
            .map(|record| record.value.as_str())
            .collect::<Vec<_>>(),
        vec!["chat:send", "external", "neighbor"]
    );
}

#[test]
fn theory_artifacts_come_from_compiled_choreography() {
    let compiled = compile_choreography(
        r#"
protocol ClientServer =
  roles Client, Server
  Client -> Server : Request
  Server -> Client : Response
"#,
    )
    .expect("compile choreography");

    let global_json = compiled.global_type_json().expect("global json");
    let local_json = compiled.local_type_r_json().expect("local json");

    assert!(global_json.contains("Client"));
    assert!(global_json.contains("Server"));
    assert!(local_json.contains("Client"));
    assert!(local_json.contains("Server"));
}
