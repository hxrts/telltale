//! Choreography Exporter CLI Tool
//!
//! Exports choreography DSL files to JSON for Lean verification.
//!
//! # Usage
//!
//! ```bash
//! lean-bridge-exporter --input protocol.choreo --role Alice \
//!     --choreography-out choreo.json --program-out program.json
//! ```

use std::env;
use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};
use serde::Serialize;

use rumpsteak_aura_choreography::ast::{LocalType, Protocol};
use rumpsteak_aura_choreography::compiler::{parse_choreography_str, project};

#[derive(Serialize)]
struct SimpleAction {
    from: String,
    to: String,
    label: String,
}

#[derive(Serialize)]
struct SimpleChoreography {
    roles: Vec<String>,
    actions: Vec<SimpleAction>,
}

#[derive(Serialize, Clone)]
struct SimpleEffect {
    kind: String,
    partner: String,
    label: String,
}

#[derive(Serialize)]
struct ProgramBranch {
    branch: Option<String>,
    effects: Vec<SimpleEffect>,
}

#[derive(Serialize)]
struct ProgramExport {
    role: String,
    programs: Vec<ProgramBranch>,
}

struct Config {
    input: PathBuf,
    role: String,
    choreography_out: PathBuf,
    program_out: PathBuf,
}

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    let config = parse_args(&args)?;

    let source = fs::read_to_string(&config.input).with_context(|| {
        format!(
            "Failed to read choreography file {}",
            config.input.display()
        )
    })?;

    let choreography = parse_choreography_str(&source)?;

    let simple_choreo = SimpleChoreography {
        roles: choreography
            .roles
            .iter()
            .map(|role| role.name().to_string())
            .collect(),
        actions: flatten_protocol(&choreography.protocol),
    };

    let role = choreography
        .roles
        .iter()
        .find(|role| *role.name() == config.role)
        .ok_or_else(|| anyhow!("Unknown role {}", config.role))?;

    let local_type = project(&choreography, role)?;

    let programs = collect_branches(&local_type);
    let program = ProgramExport {
        role: role.name().to_string(),
        programs,
    };

    fs::write(
        &config.choreography_out,
        serde_json::to_string_pretty(&simple_choreo)?,
    )
    .with_context(|| format!("Failed to write {}", config.choreography_out.display()))?;

    fs::write(&config.program_out, serde_json::to_string_pretty(&program)?)
        .with_context(|| format!("Failed to write {}", config.program_out.display()))?;

    Ok(())
}

fn parse_args(args: &[String]) -> Result<Config> {
    let mut config = Config {
        input: PathBuf::new(),
        role: String::new(),
        choreography_out: PathBuf::new(),
        program_out: PathBuf::new(),
    };

    let mut iter = args.iter().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--input" => {
                config.input = iter
                    .next()
                    .map(PathBuf::from)
                    .ok_or_else(|| anyhow!("Missing value for --input"))?
            }
            "--role" => config.role.clone_from(
                iter.next()
                    .ok_or_else(|| anyhow!("Missing value for --role"))?,
            ),
            "--choreography-out" => {
                config.choreography_out = iter
                    .next()
                    .map(PathBuf::from)
                    .ok_or_else(|| anyhow!("Missing value for --choreography-out"))?
            }
            "--program-out" => {
                config.program_out = iter
                    .next()
                    .map(PathBuf::from)
                    .ok_or_else(|| anyhow!("Missing value for --program-out"))?
            }
            _ => return Err(anyhow!("Unknown argument {arg}")),
        }
    }

    if config.input.as_os_str().is_empty()
        || config.role.is_empty()
        || config.choreography_out.as_os_str().is_empty()
        || config.program_out.as_os_str().is_empty()
    {
        return Err(anyhow!(
            "Usage: lean-bridge-exporter --input <dsl> --role <role> --choreography-out <path> --program-out <path>"
        ));
    }

    Ok(config)
}

fn flatten_protocol(protocol: &Protocol) -> Vec<SimpleAction> {
    let mut actions = Vec::new();
    collect_actions(protocol, &mut actions);
    actions
}

fn collect_actions(protocol: &Protocol, actions: &mut Vec<SimpleAction>) {
    match protocol {
        Protocol::Send {
            from,
            to,
            message,
            continuation,
            ..
        } => {
            actions.push(SimpleAction {
                from: from.name().to_string(),
                to: to.name().to_string(),
                label: message.name.to_string(),
            });
            collect_actions(continuation, actions);
        }
        Protocol::Broadcast {
            from,
            to_all,
            message,
            continuation,
            ..
        } => {
            for recipient in to_all {
                actions.push(SimpleAction {
                    from: from.name().to_string(),
                    to: recipient.name().to_string(),
                    label: message.name.to_string(),
                });
            }
            collect_actions(continuation, actions);
        }
        Protocol::Choice { branches, .. } => {
            for branch in branches {
                collect_actions(&branch.protocol, actions);
            }
        }
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => collect_actions(body, actions),
        Protocol::Parallel { protocols } => {
            for p in protocols {
                collect_actions(p, actions);
            }
        }
        Protocol::Extension { continuation, .. } => collect_actions(continuation, actions),
        Protocol::Var(_) | Protocol::End => {}
    }
}

fn collect_branches(local: &LocalType) -> Vec<ProgramBranch> {
    fn go(
        local: &LocalType,
        current: Vec<SimpleEffect>,
        branch: Option<String>,
        acc: &mut Vec<ProgramBranch>,
    ) {
        match local {
            LocalType::Send {
                to,
                message,
                continuation,
                ..
            } => {
                let mut next = current.clone();
                next.push(SimpleEffect {
                    kind: "send".to_string(),
                    partner: to.name().to_string(),
                    label: message.name.to_string(),
                });
                go(continuation, next, branch.clone(), acc);
            }
            LocalType::Receive {
                from,
                message,
                continuation,
                ..
            } => {
                let mut next = current.clone();
                next.push(SimpleEffect {
                    kind: "recv".to_string(),
                    partner: from.name().to_string(),
                    label: message.name.to_string(),
                });
                go(continuation, next, branch.clone(), acc);
            }
            LocalType::Select { branches, .. }
            | LocalType::Branch { branches, .. }
            | LocalType::LocalChoice { branches } => {
                for (label, body) in branches {
                    go(body, current.clone(), Some(label.to_string()), acc);
                }
            }
            LocalType::Loop { body, .. }
            | LocalType::Rec { body, .. }
            | LocalType::Timeout { body, .. } => go(body, current, branch, acc),
            LocalType::Var(_) => {}
            LocalType::End => {
                acc.push(ProgramBranch {
                    branch: branch.clone(),
                    effects: current,
                });
            }
        }
    }

    let mut out = Vec::new();
    go(local, Vec::new(), None, &mut out);
    out
}
