//! Pretty-printer for the choreography DSL.
//!
//! Emits layout-sensitive syntax for the choreography language.

use crate::ast::{Annotations, Branch, Choreography, Condition, MessageType, Protocol, Role, RoleParam};
use crate::compiler::parser::parse_choreography_str;

#[derive(Debug, Clone)]
pub struct PrettyConfig {
    pub indent: usize,
}

impl Default for PrettyConfig {
    fn default() -> Self {
        Self { indent: 2 }
    }
}

pub fn format_choreography(choreo: &Choreography) -> String {
    format_choreography_with_config(choreo, &PrettyConfig::default())
}

pub fn format_choreography_with_config(choreo: &Choreography, config: &PrettyConfig) -> String {
    let mut out = String::new();

    if let Some(namespace) = &choreo.namespace {
        out.push_str(&format!(
            "module {} exposing ({})\n\n",
            namespace, choreo.name
        ));
    }

    out.push_str(&format!("protocol {} =\n", choreo.name));
    write_line(
        &mut out,
        config.indent,
        &format!("roles {}", format_role_list(&choreo.roles)),
    );
    format_protocol(&choreo.protocol, config.indent, config, &mut out);

    out
}

pub fn format_choreography_str(input: &str) -> Result<String, crate::compiler::parser::ParseError> {
    let choreo = parse_choreography_str(input)?;
    Ok(format_choreography(&choreo))
}

// RECURSION_SAFE: structural recursion over finite protocol AST depth.
fn format_protocol(protocol: &Protocol, indent: usize, config: &PrettyConfig, out: &mut String) {
    match protocol {
        Protocol::End => {}
        Protocol::Send {
            from,
            to,
            message,
            annotations,
            from_annotations,
            continuation,
            ..
        } => format_send_protocol(
            from,
            annotations,
            from_annotations,
            to,
            message,
            continuation,
            indent,
            config,
            out,
        ),
        Protocol::Broadcast {
            from,
            message,
            annotations,
            from_annotations,
            continuation,
            ..
        } => format_broadcast_protocol(
            from,
            annotations,
            from_annotations,
            message,
            continuation,
            indent,
            config,
            out,
        ),
        Protocol::Choice { role, branches, .. } => {
            format_choice_protocol(role, branches, indent, config, out)
        }
        Protocol::Loop { condition, body } => {
            format_loop_protocol(condition, body, indent, config, out)
        }
        Protocol::Parallel { protocols } => {
            format_parallel_protocol(protocols, indent, config, out)
        }
        Protocol::Rec { label, body } => format_rec_protocol(label, body, indent, config, out),
        Protocol::Var(label) => {
            write_line(out, indent, &format!("continue {}", label));
        }
        Protocol::Extension {
            extension,
            continuation,
            ..
        } => format_extension_protocol(extension.type_name(), continuation, indent, config, out),
    }
}

fn format_send_protocol(
    from: &Role,
    annotations: &Annotations,
    from_annotations: &Annotations,
    to: &Role,
    message: &MessageType,
    continuation: &Protocol,
    indent: usize,
    config: &PrettyConfig,
    out: &mut String,
) {
    let sender_annotations = merge_sender_annotations(from_annotations, annotations);
    write_line(out, indent, &format_sender_term(from, &sender_annotations));
    write_line(
        out,
        indent + config.indent,
        &format!("-> {} : {}", format_role_ref(to), format_message(message)),
    );
    format_protocol(continuation, indent, config, out);
}

fn format_broadcast_protocol(
    from: &Role,
    annotations: &Annotations,
    from_annotations: &Annotations,
    message: &MessageType,
    continuation: &Protocol,
    indent: usize,
    config: &PrettyConfig,
    out: &mut String,
) {
    let sender_annotations = merge_sender_annotations(from_annotations, annotations);
    write_line(out, indent, &format_sender_term(from, &sender_annotations));
    write_line(
        out,
        indent + config.indent,
        &format!("->* : {}", format_message(message)),
    );
    format_protocol(continuation, indent, config, out);
}

fn format_choice_protocol(
    role: &Role,
    branches: &[Branch],
    indent: usize,
    config: &PrettyConfig,
    out: &mut String,
) {
    write_line(
        out,
        indent,
        &format!("choice at {}", format_role_ref(role)),
    );
    for branch in branches {
        format_branch(branch, indent + config.indent, config, out);
    }
}

fn format_loop_protocol(
    condition: &Option<Condition>,
    body: &Protocol,
    indent: usize,
    config: &PrettyConfig,
    out: &mut String,
) {
    let header = format_loop_header(condition);
    if is_end(body) {
        write_line(out, indent, &format!("{} {{}}", header));
    } else {
        write_line(out, indent, &header);
        format_protocol(body, indent + config.indent, config, out);
    }
}

fn format_parallel_protocol(
    protocols: &[Protocol],
    indent: usize,
    config: &PrettyConfig,
    out: &mut String,
) {
    write_line(out, indent, "par");
    for branch in protocols {
        if is_end(branch) {
            write_line(out, indent + config.indent, "| {}");
        } else {
            write_line(out, indent + config.indent, "|");
            format_protocol(branch, indent + (2 * config.indent), config, out);
        }
    }
}

fn format_rec_protocol(
    label: &proc_macro2::Ident,
    body: &Protocol,
    indent: usize,
    config: &PrettyConfig,
    out: &mut String,
) {
    if is_end(body) {
        write_line(out, indent, &format!("rec {} {{}}", label));
    } else {
        write_line(out, indent, &format!("rec {}", label));
        format_protocol(body, indent + config.indent, config, out);
    }
}

fn format_extension_protocol(
    extension_type_name: &str,
    continuation: &Protocol,
    indent: usize,
    config: &PrettyConfig,
    out: &mut String,
) {
    write_line(out, indent, &format!("// extension: {extension_type_name}"));
    format_protocol(continuation, indent, config, out);
}

fn format_branch(branch: &Branch, indent: usize, config: &PrettyConfig, out: &mut String) {
    let mut header = format!("| {}", branch.label);
    if let Some(guard) = &branch.guard {
        let guard_str = guard.to_string();
        header.push_str(&format!(" when ({})", guard_str));
    }

    if is_end(&branch.protocol) {
        write_line(out, indent, &format!("{} -> {{}}", header));
    } else {
        write_line(out, indent, &format!("{} ->", header));
        format_protocol(&branch.protocol, indent + config.indent, config, out);
    }
}

fn format_loop_header(condition: &Option<Condition>) -> String {
    match condition {
        Some(Condition::RoleDecides(role)) => {
            format!("loop decide by {}", format_role_ref(role))
        }
        Some(Condition::Count(count)) => format!("loop repeat {}", count),
        Some(Condition::Custom(tokens)) => format!("loop while {}", tokens),
        Some(Condition::Fuel(count)) => format!("loop while \"fuel:{}\"", count),
        Some(Condition::YieldAfter(count)) => format!("loop while \"yield_after:{}\"", count),
        Some(Condition::YieldWhen(label)) => format!("loop while \"yield_when:{}\"", label),
        None => "loop forever".to_string(),
    }
}

fn format_role_list(roles: &[Role]) -> String {
    roles
        .iter()
        .map(|role| {
            let mut out = role.name().to_string();
            if let Some(param) = role.param() {
                out.push('[');
                out.push_str(&format_role_param(param));
                out.push(']');
            }
            out
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_role_param(param: &RoleParam) -> String {
    param.to_string()
}

fn format_role_ref(role: &Role) -> String {
    let mut out = role.name().to_string();
    if let Some(index) = role.index() {
        out.push('[');
        out.push_str(&index.to_string());
        out.push(']');
    }
    out
}

fn format_sender_term(role: &Role, annotations: &Annotations) -> String {
    let mut out = format_role_ref(role);
    let mut entries: Vec<_> = annotations.to_map().into_iter().collect();
    entries.sort_by(|(key_a, _), (key_b, _)| key_a.cmp(key_b));
    if !entries.is_empty() {
        let formatted = entries
            .into_iter()
            .map(|(key, value)| format!("{key} = {value}"))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(" { ");
        out.push_str(&formatted);
        out.push_str(" }");
    }
    out
}

fn merge_sender_annotations(
    sender_annotations: &Annotations,
    statement_annotations: &Annotations,
) -> Annotations {
    let mut merged = sender_annotations.to_map();
    for (key, value) in statement_annotations.to_map() {
        merged.entry(key).or_insert(value);
    }
    Annotations::from_map(&merged)
}

fn normalize_surface_type_string(s: &str) -> String {
    s.replace(" :: ", ".").replace("::", ".")
}

fn format_message(message: &MessageType) -> String {
    let mut out = message.name.to_string();
    if let Some(payload) = &message.payload {
        let payload_str = payload.to_string();
        if payload_str.starts_with('(') {
            out.push(' ');
            out.push_str(&payload_str);
        } else {
            out.push_str(" of ");
            out.push_str(&normalize_surface_type_string(&payload_str));
        }
    } else if let Some(type_annotation) = &message.type_annotation {
        out.push_str(" of ");
        out.push_str(&normalize_surface_type_string(&type_annotation.to_string()));
    }
    out
}

fn is_end(protocol: &Protocol) -> bool {
    matches!(protocol, Protocol::End)
}

fn write_line(out: &mut String, indent: usize, text: &str) {
    out.push_str(&" ".repeat(indent));
    out.push_str(text);
    out.push('\n');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pretty_roundtrip_basic() {
        let input = "protocol PingPong =\n  roles Alice, Bob\n  Alice -> Bob : Ping\n  Bob -> Alice : Pong\n";
        let choreo = parse_choreography_str(input).expect("should parse");
        let formatted = format_choreography(&choreo);
        assert!(formatted.contains("Alice\n    -> Bob : Ping"));
        assert!(parse_choreography_str(&formatted).is_ok());
    }

    #[test]
    fn pretty_roundtrip_choice_and_loop() {
        let input = r#"
protocol Demo =
  roles Client, Server
  choice at Client
    | Buy ->
      Client -> Server : Purchase
    | Cancel -> {}
  loop repeat 2
    Client -> Server : Ping
    Server -> Client : Pong
"#;
        let choreo = parse_choreography_str(input).expect("should parse");
        let formatted = format_choreography(&choreo);
        assert!(formatted.contains("choice at Client"));
        assert!(formatted.contains("| Buy ->"));
        assert!(parse_choreography_str(&formatted).is_ok());
    }

    #[test]
    fn pretty_emits_aligned_arrows_and_sender_records() {
        let input = r#"
protocol Styled =
  roles A, B, C, D
  A { priority = high } -> B : Request of shop.Order
  par
    | C -> D : Left
    | D -> C : Right
"#;

        let choreo = parse_choreography_str(input).expect("should parse");
        let formatted = format_choreography(&choreo);
        assert!(formatted.contains("A { priority = high }\n    -> B : Request of shop.Order"));
        assert!(formatted.contains("par\n    |\n      C\n        -> D : Left"));
        assert!(parse_choreography_str(&formatted).is_ok());
    }

    #[test]
    fn pretty_is_stable_on_reformat() {
        let input = r#"
protocol Stable =
  roles A, B
  A { priority = high } -> B : Request of shop.Order
"#;

        let first = format_choreography_str(input).expect("first format should succeed");
        let second = format_choreography_str(&first).expect("second format should succeed");
        assert_eq!(first, second);
    }
}
