//! Compile `LocalTypeR` to bytecode.
//!
//! Trivial compiler: each send/recv in the local type becomes a bytecode
//! instruction. Mu generates a loop target, Var generates a Jmp back.

use std::collections::HashMap;

use telltale_types::LocalTypeR;

use crate::instr::{Instr, PC};

/// Compile a local type to a bytecode program.
///
/// Register allocation:
/// - Reg 0: channel/endpoint (set by VM at coroutine creation)
/// - Reg 1: send value / recv destination
///
/// Returns the instruction sequence.
#[must_use]
pub fn compile(local_type: &LocalTypeR) -> Vec<Instr> {
    let mut instrs = Vec::new();
    let mut loop_targets: HashMap<String, PC> = HashMap::new();
    compile_inner(local_type, &mut instrs, &mut loop_targets);
    instrs
}

fn compile_inner(
    lt: &LocalTypeR,
    instrs: &mut Vec<Instr>,
    loop_targets: &mut HashMap<String, PC>,
) {
    match lt {
        LocalTypeR::Send { branches, .. } => {
            if branches.len() == 1 {
                if let Some((_, _vt, cont)) = branches.first() {
                    instrs.push(Instr::Send { chan: 0, val: 1 });
                    compile_inner(cont, instrs, loop_targets);
                }
            } else if branches.len() > 1 {
                compile_choice_branches(branches, instrs, loop_targets);
            }
        }
        LocalTypeR::Recv { branches, .. } => {
            if branches.len() == 1 {
                if let Some((_, _vt, cont)) = branches.first() {
                    instrs.push(Instr::Recv { chan: 0, dst: 1 });
                    compile_inner(cont, instrs, loop_targets);
                }
            } else if branches.len() > 1 {
                compile_choice_branches(branches, instrs, loop_targets);
            }
        }
        LocalTypeR::Mu { var, body } => {
            let target = instrs.len();
            loop_targets.insert(var.clone(), target);
            compile_inner(body, instrs, loop_targets);
        }
        LocalTypeR::Var(name) => {
            if let Some(&target) = loop_targets.get(name) {
                instrs.push(Instr::Jmp { target });
            } else {
                // Unbound variable — halt.
                instrs.push(Instr::Halt);
            }
        }
        LocalTypeR::End => {
            instrs.push(Instr::Halt);
        }
    }
}

/// Compile multi-branch choice: emit Offer with jump table, then each branch's code.
fn compile_choice_branches(
    branches: &[(telltale_types::Label, Option<telltale_types::ValType>, LocalTypeR)],
    instrs: &mut Vec<Instr>,
    loop_targets: &mut HashMap<String, PC>,
) {
    // Reserve slot for the Offer instruction (will be patched).
    let placeholder_idx = instrs.len();
    instrs.push(Instr::Offer {
        chan: 0,
        table: vec![],
    });

    // Compile each branch and build the jump table.
    let mut table = Vec::with_capacity(branches.len());
    for (label, _vt, cont) in branches {
        let start_pc = instrs.len();
        table.push((label.name.clone(), start_pc));
        compile_inner(cont, instrs, loop_targets);
    }

    // Patch the Offer instruction with the completed table.
    instrs[placeholder_idx] = Instr::Offer { chan: 0, table };
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::Label;

    #[test]
    fn test_compile_send_end() {
        let lt = LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        };
        let code = compile(&lt);
        assert_eq!(code, vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Halt,
        ]);
    }

    #[test]
    fn test_compile_recursive() {
        // mu step. !B:msg. var step
        let lt = LocalTypeR::mu(
            "step",
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
            },
        );
        let code = compile(&lt);
        assert_eq!(code, vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Jmp { target: 0 },
        ]);
    }

    #[test]
    fn test_compile_send_recv_loop() {
        // mu step. !B:pos. ?B:pos. var step
        let lt = LocalTypeR::mu(
            "step",
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(
                    Label::new("pos"),
                    None,
                    LocalTypeR::Recv {
                        partner: "B".into(),
                        branches: vec![(Label::new("pos"), None, LocalTypeR::var("step"))],
                    },
                )],
            },
        );
        let code = compile(&lt);
        assert_eq!(code, vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Recv { chan: 0, dst: 1 },
            Instr::Jmp { target: 0 },
        ]);
    }
}
