use super::*;

impl PartialEq for LocalType {
    #[allow(clippy::too_many_lines)]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LocalType::End, LocalType::End) => true,
            (LocalType::Var(a), LocalType::Var(b)) => a == b,
            (
                LocalType::Send {
                    to: to1,
                    message: msg1,
                    continuation: cont1,
                },
                LocalType::Send {
                    to: to2,
                    message: msg2,
                    continuation: cont2,
                },
            ) => to1 == to2 && msg1.name == msg2.name && cont1 == cont2,
            (
                LocalType::Receive {
                    from: from1,
                    message: msg1,
                    continuation: cont1,
                },
                LocalType::Receive {
                    from: from2,
                    message: msg2,
                    continuation: cont2,
                },
            ) => from1 == from2 && msg1.name == msg2.name && cont1 == cont2,
            (
                LocalType::Select {
                    to: to1,
                    branches: br1,
                },
                LocalType::Select {
                    to: to2,
                    branches: br2,
                },
            ) => {
                to1 == to2
                    && br1.len() == br2.len()
                    && br1
                        .iter()
                        .zip(br2.iter())
                        .all(|((l1, t1), (l2, t2))| l1 == l2 && t1 == t2)
            }
            (
                LocalType::Branch {
                    from: from1,
                    branches: br1,
                },
                LocalType::Branch {
                    from: from2,
                    branches: br2,
                },
            ) => {
                from1 == from2
                    && br1.len() == br2.len()
                    && br1
                        .iter()
                        .zip(br2.iter())
                        .all(|((l1, t1), (l2, t2))| l1 == l2 && t1 == t2)
            }
            (
                LocalType::LocalChoice { branches: br1 },
                LocalType::LocalChoice { branches: br2 },
            ) => {
                br1.len() == br2.len()
                    && br1
                        .iter()
                        .zip(br2.iter())
                        .all(|((l1, t1), (l2, t2))| l1 == l2 && t1 == t2)
            }
            (
                LocalType::Loop {
                    condition: c1,
                    body: b1,
                },
                LocalType::Loop {
                    condition: c2,
                    body: b2,
                },
            ) => {
                // For conditions, we compare structurally
                let cond_eq = match (c1, c2) {
                    (None, None) => true,
                    (
                        Some(crate::ast::protocol::Condition::Count(n1)),
                        Some(crate::ast::protocol::Condition::Count(n2)),
                    ) => n1 == n2,
                    (
                        Some(crate::ast::protocol::Condition::RoleDecides(r1)),
                        Some(crate::ast::protocol::Condition::RoleDecides(r2)),
                    ) => r1 == r2,
                    _ => false,
                };
                cond_eq && b1 == b2
            }
            (
                LocalType::Rec {
                    label: l1,
                    body: b1,
                },
                LocalType::Rec {
                    label: l2,
                    body: b2,
                },
            ) => l1 == l2 && b1 == b2,
            _ => false,
        }
    }
}

impl Eq for LocalType {}
