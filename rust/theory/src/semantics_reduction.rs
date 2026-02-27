use super::{can_step, step, GlobalAction};
use crate::limits::{TraversalFuel, DEFAULT_TRAVERSAL_FUEL};
use std::collections::BTreeSet;
use telltale_types::content_id::Sha256Hasher;
use telltale_types::contentable::Contentable;
use telltale_types::GlobalType;

/// Check if a global type reduces to another via one communication.
///
/// Corresponds to Lean's `GlobalTypeReduces` relation.
/// G ⟹ G' means G can reduce to G' by performing one communication.
#[must_use]
pub fn reduces(global: &GlobalType, target: &GlobalType) -> bool {
    reduces_with_fuel(global, target, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded one-step reduction reachability.
#[must_use]
pub fn reduces_with_fuel(global: &GlobalType, target: &GlobalType, fuel: TraversalFuel) -> bool {
    reduces_fuel(global, target, fuel.as_usize())
}

fn reduces_fuel(g: &GlobalType, g_prime: &GlobalType, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }

    match g {
        GlobalType::Comm { branches, .. } => {
            // Direct reduction: g_prime is one of the continuations
            for (_, cont) in branches {
                if cont == g_prime {
                    return true;
                }
            }
            false
        }
        GlobalType::Mu { var, body } => {
            // Reduce under μ-unfolding
            let unfolded = body.substitute(var, g);
            reduces_fuel(&unfolded, g_prime, fuel - 1)
        }
        _ => false,
    }
}

/// Check if g reduces to g_prime in zero or more steps.
///
/// Corresponds to Lean's `GlobalTypeReducesStar`.
#[must_use]
pub fn reduces_star(global: &GlobalType, target: &GlobalType) -> bool {
    reduces_star_with_fuel(global, target, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded multi-step reduction reachability.
#[must_use]
pub fn reduces_star_with_fuel(
    global: &GlobalType,
    target: &GlobalType,
    fuel: TraversalFuel,
) -> bool {
    reduces_star_fuel(global, target, fuel.as_usize(), &mut BTreeSet::new())
}

fn reduces_star_fuel(
    g: &GlobalType,
    g_prime: &GlobalType,
    fuel: usize,
    visited: &mut BTreeSet<String>,
) -> bool {
    if fuel == 0 {
        return false;
    }

    if g == g_prime {
        return true;
    }

    let fingerprint = global_fingerprint(g);
    if visited.contains(&fingerprint) {
        return false;
    }
    visited.insert(fingerprint);

    match g {
        GlobalType::Comm { branches, .. } => {
            for (_, cont) in branches {
                if reduces_star_fuel(cont, g_prime, fuel - 1, visited) {
                    return true;
                }
            }
            false
        }
        GlobalType::Mu { var, body } => {
            let unfolded = body.substitute(var, g);
            reduces_star_fuel(&unfolded, g_prime, fuel - 1, visited)
        }
        _ => false,
    }
}

/// Check if an action is enabled implies a step exists.
///
/// This is the "good global" condition from the ECOOP 2025 paper.
/// For well-formed types, if `can_step(g, act)` then `step(g, act).is_some()`.
#[must_use]
pub fn good_g(global: &GlobalType) -> bool {
    good_g_with_fuel(global, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded good-global check.
#[must_use]
pub fn good_g_with_fuel(global: &GlobalType, fuel: TraversalFuel) -> bool {
    good_g_fuel(global, fuel.as_usize(), &mut BTreeSet::new())
}

fn good_g_fuel(g: &GlobalType, fuel: usize, visited: &mut BTreeSet<String>) -> bool {
    if fuel == 0 {
        return true;
    }

    let fingerprint = global_fingerprint(g);
    if visited.contains(&fingerprint) {
        return true;
    }
    visited.insert(fingerprint);

    match g {
        GlobalType::End => true,
        GlobalType::Var(_) => true,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            for (l, cont) in branches {
                let act = GlobalAction::new(sender, receiver, l.clone());
                if can_step(g, &act) && step(g, &act).is_none() {
                    return false;
                }
                if !good_g_fuel(cont, fuel - 1, visited) {
                    return false;
                }
            }
            true
        }
        GlobalType::Mu { var, body } => {
            let unfolded = body.substitute(var, g);
            good_g_fuel(&unfolded, fuel - 1, visited)
        }
    }
}

fn global_fingerprint(g: &GlobalType) -> String {
    g.content_id::<Sha256Hasher>()
        .map(|cid| cid.to_hex())
        .unwrap_or_else(|_| format!("{g:?}"))
}
