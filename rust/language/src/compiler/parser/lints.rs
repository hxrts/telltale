//! Parser-level lint diagnostics and fix suggestions.

use super::*;
use crate::ast::Protocol;
use std::fmt::Write;

/// Lint level for parser diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LintLevel {
    Off,
    Warn,
    Deny,
}

/// Structured lint diagnostic with optional fix suggestion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LintDiagnostic {
    pub code: String,
    pub level: LintLevel,
    pub message: String,
    pub suggestion: Option<String>,
}

fn push_lint(
    diagnostics: &mut Vec<LintDiagnostic>,
    level: LintLevel,
    code: &str,
    message: &str,
    suggestion: impl Into<Option<String>>,
) {
    diagnostics.push(LintDiagnostic {
        code: code.to_string(),
        level,
        message: message.to_string(),
        suggestion: suggestion.into(),
    });
}

/// Collect DSL lint diagnostics for a parsed choreography.
pub fn collect_dsl_lints(choreography: &Choreography, level: LintLevel) -> Vec<LintDiagnostic> {
    if level == LintLevel::Off {
        return Vec::new();
    }

    let mut diagnostics = Vec::new();
    let inferred = choreography.inferred_required_theorem_packs();
    let required = choreography.required_theorem_packs();
    if !inferred.is_empty() && inferred == required {
        push_lint(
            &mut diagnostics,
            level,
            "dsl.inferred_requires",
            "Protocol requirements were inferred from ProtocolMachine-core capabilities",
            Some(format!(
                "Add explicit `requires {}` to the protocol header",
                inferred.join(", ")
            )),
        );
    }

    diagnostics
}

fn diagnostics_to_lsp_json(diagnostics: Vec<LintDiagnostic>) -> String {
    let diagnostics: Vec<serde_json::Value> = diagnostics
        .into_iter()
        .map(|lint| {
            serde_json::json!({
                "code": lint.code,
                "severity": match lint.level {
                    LintLevel::Off => "off",
                    LintLevel::Warn => "warning",
                    LintLevel::Deny => "error",
                },
                "message": lint.message,
                "range": {
                    "start": {"line": 0, "character": 0},
                    "end": {"line": 0, "character": 1}
                },
                "data": {
                    "quickFix": lint.suggestion
                }
            })
        })
        .collect();
    serde_json::to_string_pretty(&diagnostics).unwrap_or_else(|_| "[]".to_string())
}

/// Render lint diagnostics into a lightweight LSP-like JSON string.
pub fn render_lsp_lint_diagnostics(choreography: &Choreography, level: LintLevel) -> String {
    diagnostics_to_lsp_json(collect_dsl_lints(choreography, level))
}

#[allow(clippy::too_many_lines)]
// RECURSION_SAFE: structural recursion over finite protocol AST depth.
fn render_lowering_protocol(protocol: &Protocol, depth: usize, out: &mut String) {
    let indent = "  ".repeat(depth);
    match protocol {
        Protocol::Begin {
            operation,
            progress,
            continuation,
            ..
        } => {
            if let Some(progress) = progress {
                writeln!(
                    out,
                    "{indent}- begin {operation} progress {}",
                    progress.contract_name
                )
                .unwrap();
            } else {
                writeln!(out, "{indent}- begin {operation}").unwrap();
            }
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Await {
            operation,
            continuation,
        } => {
            writeln!(out, "{indent}- await {operation}").unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Resolve {
            operation,
            outcome,
            continuation,
        } => {
            writeln!(out, "{indent}- resolve {operation} as {outcome:?}").unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Invalidate {
            operation,
            continuation,
        } => {
            writeln!(out, "{indent}- invalidate {operation}").unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Send {
            from,
            to,
            message,
            continuation,
            ..
        } => {
            writeln!(
                out,
                "{indent}- send {} -> {} : {}",
                from.name(),
                to.name(),
                message.name
            )
            .unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Broadcast {
            from,
            message,
            continuation,
            ..
        } => {
            writeln!(
                out,
                "{indent}- broadcast {} ->* : {}",
                from.name(),
                message.name
            )
            .unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Choice { role, branches, .. } => {
            writeln!(out, "{indent}- choice {} at", role.name()).unwrap();
            for branch in branches {
                writeln!(out, "{indent}  branch {}", branch.label).unwrap();
                render_lowering_protocol(&branch.protocol, depth + 2, out);
            }
        }
        Protocol::Let {
            name, continuation, ..
        } => {
            writeln!(out, "{indent}- let {name} = ...").unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Case { branches, .. } => {
            writeln!(out, "{indent}- case/of").unwrap();
            for branch in branches {
                writeln!(out, "{indent}  branch {}", branch.pattern.constructor).unwrap();
                render_lowering_protocol(&branch.protocol, depth + 2, out);
            }
        }
        Protocol::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => {
            writeln!(out, "{indent}- timeout").unwrap();
            render_lowering_protocol(body, depth + 1, out);
            render_lowering_protocol(on_timeout, depth + 1, out);
            if let Some(on_cancel) = on_cancel.as_deref() {
                render_lowering_protocol(on_cancel, depth + 1, out);
            }
        }
        Protocol::Loop { body, .. } => {
            writeln!(out, "{indent}- loop").unwrap();
            render_lowering_protocol(body, depth + 1, out);
        }
        Protocol::Parallel { protocols } => {
            writeln!(out, "{indent}- parallel").unwrap();
            for (idx, branch) in protocols.iter().enumerate() {
                writeln!(out, "{indent}  branch#{idx}").unwrap();
                render_lowering_protocol(branch, depth + 2, out);
            }
        }
        Protocol::Rec { label, body } => {
            writeln!(out, "{indent}- rec {label}").unwrap();
            render_lowering_protocol(body, depth + 1, out);
        }
        Protocol::Var(label) => {
            writeln!(out, "{indent}- continue {label}").unwrap();
        }
        Protocol::Publish {
            event,
            arg,
            continuation,
        } => {
            if let Some(arg) = arg {
                writeln!(out, "{indent}- publish {event}{arg}").unwrap();
            } else {
                writeln!(out, "{indent}- publish {event}").unwrap();
            }
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::PublishAuthority {
            witness,
            publication_name,
            continuation,
        } => {
            writeln!(out, "{indent}- publish {witness} as {publication_name}").unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Materialize {
            proof,
            publication,
            continuation,
        } => {
            writeln!(out, "{indent}- materialize {proof} from {publication}").unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Handoff {
            operation,
            target,
            receipt,
            continuation,
        } => {
            writeln!(
                out,
                "{indent}- handoff {operation} to {} using {receipt}",
                target.name()
            )
            .unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::DependentWork {
            name,
            arg,
            required_for,
            continuation,
        } => {
            if let Some(arg) = arg {
                writeln!(
                    out,
                    "{indent}- dependent work {name}{arg} required for {required_for}"
                )
                .unwrap();
            } else {
                writeln!(
                    out,
                    "{indent}- dependent work {name} required for {required_for}"
                )
                .unwrap();
            }
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::Extension {
            annotations,
            continuation,
            ..
        } => {
            let kind = annotations
                .custom("protocol_machine_core_op")
                .or_else(|| annotations.custom("dsl_combinator"))
                .unwrap_or("extension");
            writeln!(out, "{indent}- extension {kind}").unwrap();
            render_lowering_protocol(continuation, depth + 1, out);
        }
        Protocol::End => {
            writeln!(out, "{indent}- end").unwrap();
        }
    }
}

fn render_lowering_summary(choreography: &Choreography, out: &mut String) {
    writeln!(out, "Protocol: {}", choreography.qualified_name()).unwrap();
    writeln!(
        out,
        "Roles: {}",
        choreography
            .roles
            .iter()
            .map(|r| r.name().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    )
    .unwrap();
    let bundles = choreography.theorem_packs();
    if !bundles.is_empty() {
        writeln!(
            out,
            "Proof bundles: {}",
            bundles
                .iter()
                .map(|b| b.name.clone())
                .collect::<Vec<_>>()
                .join(", ")
        )
        .unwrap();
    }
    let required = choreography.required_theorem_packs();
    if !required.is_empty() {
        writeln!(out, "Required bundles: {}", required.join(", ")).unwrap();
    }
    let inferred = choreography.inferred_required_theorem_packs();
    if !inferred.is_empty() {
        writeln!(out, "Inferred bundles: {}", inferred.join(", ")).unwrap();
    }
}

fn render_lowering_lints(lints: &[LintDiagnostic], out: &mut String) {
    if lints.is_empty() {
        return;
    }
    writeln!(out, "Lints:").unwrap();
    for lint in lints {
        writeln!(out, "- [{}] {}", lint.code, lint.message).unwrap();
        if let Some(fix) = &lint.suggestion {
            writeln!(out, "  fix: {fix}").unwrap();
        }
    }
}

/// Produce a canonical lowering report for a DSL snippet.
pub fn explain_lowering(input: &str) -> std::result::Result<String, ParseError> {
    let choreography = parse_choreography_str(input)?;
    let lints = collect_dsl_lints(&choreography, LintLevel::Warn);
    let mut out = String::new();
    render_lowering_summary(&choreography, &mut out);
    writeln!(out, "Lowering:").unwrap();
    render_lowering_protocol(&choreography.protocol, 1, &mut out);
    render_lowering_lints(&lints, &mut out);
    Ok(out)
}
