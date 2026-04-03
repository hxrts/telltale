//! Modern downstream integration demo.

use external_demo::{compile_choreography, AnnotationScope, Contentable, DefaultContentId};
use std::error::Error;

const INTEGRATION_DSL: &str = r#"
protocol AuditFlow =
  roles Alice, Bob
  Alice { guard_capability : "chat:send", leak : (External, Neighbor), leakage_budget : [1, 0, 0] } -> Bob : AuditRequest
  Bob -> Alice : AuditResponse
"#;

fn main() -> Result<(), Box<dyn Error>> {
    let compiled = compile_choreography(INTEGRATION_DSL)?;
    let global = compiled.try_global_type()?;
    let global_id: DefaultContentId = global.content_id_default()?;

    let sender_annotations = compiled
        .annotation_records()
        .into_iter()
        .filter(|record| {
            record.path == "root"
                && record.scope == AnnotationScope::Sender
                && record.role.as_deref() == Some("Alice")
        })
        .collect::<Vec<_>>();

    println!("role order: {:?}", compiled.role_names());
    println!(
        "ordered sender annotations: {:?}",
        sender_annotations
            .iter()
            .map(|record| format!("{}={}", record.key, record.value))
            .collect::<Vec<_>>()
    );
    println!("global type json: {}", compiled.global_type_json()?);
    println!("local types json: {}", compiled.local_type_r_json()?);
    println!("default content id: {}", global_id);

    Ok(())
}
