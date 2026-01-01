//! Pretty-printer for the choreography DSL.
//!
//! Emits the new layout-sensitive syntax described in work/syntax.md.

use crate::ast::{Branch, Choreography, Condition, MessageType, Protocol, Role, RoleParam};
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

fn format_protocol(protocol: &Protocol, indent: usize, config: &PrettyConfig, out: &mut String) {
    match protocol {
        Protocol::End => {}
        Protocol::Send {
            from,
            to,
            message,
            continuation,
            ..
        } => {
            let line = format!(
                "{} -> {} : {}",
                format_role_ref(from),
                format_role_ref(to),
                format_message(message)
            );
            write_line(out, indent, &line);
            format_protocol(continuation, indent, config, out);
        }
        Protocol::Broadcast {
            from,
            message,
            continuation,
            ..
        } => {
            let line = format!(
                "{} ->* : {}",
                format_role_ref(from),
                format_message(message)
            );
            write_line(out, indent, &line);
            format_protocol(continuation, indent, config, out);
        }
        Protocol::Choice { role, branches, .. } => {
            write_line(
                out,
                indent,
                &format!("case choose {} of", format_role_ref(role)),
            );
            for branch in branches {
                format_branch(branch, indent + config.indent, config, out);
            }
        }
        Protocol::Loop { condition, body } => {
            let header = format_loop_header(condition);
            if is_end(body) {
                write_line(out, indent, &format!("{} {{}}", header));
            } else {
                write_line(out, indent, &header);
                format_protocol(body, indent + config.indent, config, out);
            }
        }
        Protocol::Parallel { protocols } => {
            for branch in protocols {
                if is_end(branch) {
                    write_line(out, indent, "branch {}");
                } else {
                    write_line(out, indent, "branch");
                    format_protocol(branch, indent + config.indent, config, out);
                }
            }
        }
        Protocol::Rec { label, body } => {
            if is_end(body) {
                write_line(out, indent, &format!("rec {} {{}}", label));
            } else {
                write_line(out, indent, &format!("rec {}", label));
                format_protocol(body, indent + config.indent, config, out);
            }
        }
        Protocol::Var(label) => {
            write_line(out, indent, &format!("continue {}", label));
        }
        Protocol::Extension {
            extension,
            continuation,
            ..
        } => {
            write_line(
                out,
                indent,
                &format!("// extension: {}", extension.type_name()),
            );
            format_protocol(continuation, indent, config, out);
        }
    }
}

fn format_branch(branch: &Branch, indent: usize, config: &PrettyConfig, out: &mut String) {
    let mut header = branch.label.to_string();
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
            let mut out = role.name.to_string();
            if let Some(param) = &role.param {
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
    let mut out = role.name.to_string();
    if let Some(index) = &role.index {
        out.push('[');
        out.push_str(&index.to_string());
        out.push(']');
    }
    out
}

fn format_message(message: &MessageType) -> String {
    let mut out = message.name.to_string();
    if let Some(type_annotation) = &message.type_annotation {
        let type_str = type_annotation.to_string();
        out.push('<');
        out.push_str(&type_str);
        out.push('>');
    }
    if let Some(payload) = &message.payload {
        let payload_str = payload.to_string();
        out.push(' ');
        out.push_str(&payload_str);
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
        assert!(parse_choreography_str(&formatted).is_ok());
    }

    #[test]
    fn pretty_roundtrip_choice_and_loop() {
        let input = r#"
protocol Demo =
  roles Client, Server
  case choose Client of
    Buy ->
      Client -> Server : Purchase
    Cancel -> {}
  loop repeat 2
    Client -> Server : Ping
    Server -> Client : Pong
"#;
        let choreo = parse_choreography_str(input).expect("should parse");
        let formatted = format_choreography(&choreo);
        assert!(formatted.contains("case choose Client of"));
        assert!(parse_choreography_str(&formatted).is_ok());
    }
}
