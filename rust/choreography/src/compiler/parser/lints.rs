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

/// Collect DSL lint diagnostics for a parsed choreography.
pub fn collect_dsl_lints(choreography: &Choreography, level: LintLevel) -> Vec<LintDiagnostic> {
    if level == LintLevel::Off {
        return Vec::new();
    }

    let mut diagnostics = Vec::new();
    let inferred = choreography.inferred_required_proof_bundles();
    let required = choreography.required_proof_bundles();
    if !inferred.is_empty() && inferred == required {
        diagnostics.push(LintDiagnostic {
            code: "dsl.inferred_requires".to_string(),
            level,
            message: "Protocol requirements were inferred from VM-core capabilities".to_string(),
            suggestion: Some(format!(
                "Add explicit `requires {}` to the protocol header",
                inferred.join(", ")
            )),
        });
    }

    diagnostics
}

/// Render lint diagnostics into a lightweight LSP-like JSON string.
pub fn render_lsp_lint_diagnostics(choreography: &Choreography, level: LintLevel) -> String {
    let diagnostics: Vec<serde_json::Value> = collect_dsl_lints(choreography, level)
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

#[allow(clippy::too_many_lines)]
// RECURSION_SAFE: structural recursion over finite protocol AST depth.
fn render_lowering_protocol(protocol: &Protocol, depth: usize, out: &mut String) {
    let indent = "  ".repeat(depth);
    match protocol {
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
            writeln!(out, "{indent}- choice at {}", role.name()).unwrap();
            for branch in branches {
                writeln!(out, "{indent}  branch {}", branch.label).unwrap();
                render_lowering_protocol(&branch.protocol, depth + 2, out);
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
        Protocol::Extension {
            annotations,
            continuation,
            ..
        } => {
            let kind = annotations
                .custom("vm_core_op")
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
    let bundles = choreography.proof_bundles();
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
    let required = choreography.required_proof_bundles();
    if !required.is_empty() {
        writeln!(out, "Required bundles: {}", required.join(", ")).unwrap();
    }
    let inferred = choreography.inferred_required_proof_bundles();
    if !inferred.is_empty() {
        writeln!(out, "Inferred bundles: {}", inferred.join(", ")).unwrap();
    }
}

fn render_lowering_lints(choreography: &Choreography, out: &mut String) {
    let lints = collect_dsl_lints(choreography, LintLevel::Warn);
    if lints.is_empty() {
        return;
    }
    writeln!(out, "Lints:").unwrap();
    for lint in lints {
        writeln!(out, "- [{}] {}", lint.code, lint.message).unwrap();
        if let Some(fix) = lint.suggestion {
            writeln!(out, "  fix: {fix}").unwrap();
        }
    }
}

/// Produce a canonical lowering report for a DSL snippet.
pub fn explain_lowering(input: &str) -> std::result::Result<String, ParseError> {
    let choreography = parse_choreography_str(input)?;
    let mut out = String::new();
    render_lowering_summary(&choreography, &mut out);
    writeln!(out, "Lowering:").unwrap();
    render_lowering_protocol(&choreography.protocol, 1, &mut out);
    render_lowering_lints(&choreography, &mut out);
    Ok(out)
}
