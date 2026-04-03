use super::{validate_non_negative, validate_probability, Scenario};
use std::collections::BTreeSet;

pub(super) fn validate_semantics(scenario: &Scenario) -> Result<(), String> {
    let role_set = validate_roles(scenario)?;
    validate_limits(scenario)?;
    validate_network(scenario, &role_set)?;
    validate_reconfigurations(scenario, &role_set)?;
    validate_adversaries(scenario, &role_set)?;
    if scenario.property_monitor()?.is_some() {
        // Property monitor configuration is validated by construction here.
    }
    Ok(())
}

fn validate_roles(scenario: &Scenario) -> Result<BTreeSet<String>, String> {
    if scenario.roles.is_empty() {
        return Err("scenario.roles must contain at least one role".to_string());
    }
    let mut role_set = BTreeSet::new();
    for role in &scenario.roles {
        if role.trim().is_empty() {
            return Err("scenario.roles must not contain empty role names".to_string());
        }
        if !role_set.insert(role.clone()) {
            return Err(format!("duplicate role in scenario.roles: '{role}'"));
        }
    }
    Ok(role_set)
}

fn validate_limits(scenario: &Scenario) -> Result<(), String> {
    scenario.resolved_execution()?;
    if matches!(scenario.checkpoint_interval, Some(0)) {
        return Err("scenario.checkpoint_interval must be > 0 when set".to_string());
    }
    Ok(())
}

fn validate_network(scenario: &Scenario, role_set: &BTreeSet<String>) -> Result<(), String> {
    let Some(network) = &scenario.network else {
        return Ok(());
    };
    validate_non_negative("network.latency_variance", network.latency_variance)?;
    validate_probability("network.loss_probability", network.loss_probability)?;
    validate_network_links(network, role_set)?;
    Ok(())
}

fn validate_network_links(
    network: &super::NetworkSpec,
    role_set: &BTreeSet<String>,
) -> Result<(), String> {
    for (idx, link) in network.links.iter().enumerate() {
        if !role_set.contains(&link.from) {
            return Err(format!(
                "network.links[{idx}] references unknown from-role '{}'",
                link.from
            ));
        }
        if !role_set.contains(&link.to) {
            return Err(format!(
                "network.links[{idx}] references unknown to-role '{}'",
                link.to
            ));
        }
        if link.from == link.to {
            return Err(format!(
                "network.links[{idx}] has identical from/to role '{}'",
                link.from
            ));
        }
        if let Some(loss) = link.loss_probability {
            validate_probability("network.links.loss_probability", loss)?;
        }
        if let Some(variance) = link.latency_variance {
            validate_non_negative("network.links.latency_variance", variance)?;
        }
    }
    Ok(())
}

fn validate_reconfigurations(
    scenario: &Scenario,
    role_set: &BTreeSet<String>,
) -> Result<(), String> {
    for (idx, operation) in scenario.reconfigurations.iter().enumerate() {
        let _trigger = operation.trigger.to_trigger()?;
        match operation.effect.kind {
            crate::reconfiguration::ReconfigurationEffectKind::Pure
                if operation.effect.budget_cost != 0 =>
            {
                return Err(format!(
                    "reconfigurations[{idx}] pure reconfiguration must not consume transition budget"
                ));
            }
            crate::reconfiguration::ReconfigurationEffectKind::TransitionChoreography
                if operation.effect.budget_cost == 0 =>
            {
                return Err(format!(
                    "reconfigurations[{idx}] transition_choreography must declare budget_cost > 0"
                ));
            }
            _ => {}
        }
        match &operation.action {
            crate::reconfiguration::ReconfigurationAction::Link {
                from,
                to,
                latency_variance,
                loss_probability,
                ..
            } => {
                validate_known_distinct_roles(idx, "reconfigurations", from, to, role_set, "link")?;
                if let Some(loss) = loss_probability {
                    validate_probability("reconfigurations.link.loss_probability", *loss)?;
                }
                if let Some(variance) = latency_variance {
                    validate_non_negative("reconfigurations.link.latency_variance", *variance)?;
                }
            }
            crate::reconfiguration::ReconfigurationAction::Delegation {
                scope,
                from_role,
                to_role,
            } => {
                if scope.trim().is_empty() {
                    return Err(format!(
                        "reconfigurations[{idx}] delegation scope must not be empty"
                    ));
                }
                validate_known_distinct_roles(
                    idx,
                    "reconfigurations",
                    from_role,
                    to_role,
                    role_set,
                    "delegation",
                )?;
            }
            crate::reconfiguration::ReconfigurationAction::Handoff {
                handoff_id,
                from_role,
                to_role,
            } => {
                if handoff_id.trim().is_empty() {
                    return Err(format!(
                        "reconfigurations[{idx}] handoff_id must not be empty"
                    ));
                }
                validate_known_distinct_roles(
                    idx,
                    "reconfigurations",
                    from_role,
                    to_role,
                    role_set,
                    "handoff",
                )?;
            }
            crate::reconfiguration::ReconfigurationAction::Federation {
                federation,
                enabled,
                groups,
            } => {
                if federation.trim().is_empty() {
                    return Err(format!(
                        "reconfigurations[{idx}] federation name must not be empty"
                    ));
                }
                if *enabled {
                    validate_group_footprint(
                        &format!("reconfigurations[{idx}].federation"),
                        groups,
                        role_set,
                    )?;
                } else if !groups.is_empty() {
                    return Err(format!(
                        "reconfigurations[{idx}] disabled federation updates must not declare groups"
                    ));
                }
            }
            crate::reconfiguration::ReconfigurationAction::ModeTransition {
                roles,
                from_mode,
                to_mode,
            } => {
                if roles.is_empty() {
                    return Err(format!(
                        "reconfigurations[{idx}] mode_transition must list at least one role"
                    ));
                }
                if from_mode.trim().is_empty() || to_mode.trim().is_empty() {
                    return Err(format!(
                        "reconfigurations[{idx}] mode_transition modes must not be empty"
                    ));
                }
                if from_mode == to_mode {
                    return Err(format!(
                        "reconfigurations[{idx}] mode_transition must change modes"
                    ));
                }
                let mut seen = BTreeSet::new();
                for role in roles {
                    if !role_set.contains(role) {
                        return Err(format!(
                            "reconfigurations[{idx}] mode_transition references unknown role '{role}'"
                        ));
                    }
                    if !seen.insert(role.clone()) {
                        return Err(format!(
                            "reconfigurations[{idx}] mode_transition role '{role}' appears multiple times"
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

fn validate_adversaries(scenario: &Scenario, role_set: &BTreeSet<String>) -> Result<(), String> {
    let mut seen_ids = BTreeSet::new();
    for (idx, adversary) in scenario.adversaries.iter().enumerate() {
        let _trigger = adversary.trigger.to_trigger()?;
        if adversary.budget.total == 0 {
            return Err(format!("adversaries[{idx}] budget.total must be > 0"));
        }
        if let Some(id) = &adversary.id {
            if id.trim().is_empty() {
                return Err(format!("adversaries[{idx}] id must not be empty"));
            }
            if !seen_ids.insert(id.clone()) {
                return Err(format!("duplicate adversary id '{id}'"));
            }
        }
        match &adversary.budget.mode {
            super::AdversaryBudgetModeSpec::Activation => {}
            super::AdversaryBudgetModeSpec::Independent { probability } => {
                validate_probability("adversaries.budget.probability", *probability)?;
            }
            super::AdversaryBudgetModeSpec::Windowed {
                window_ticks,
                max_per_window,
            } => {
                if *window_ticks == 0 {
                    return Err(format!("adversaries[{idx}] window_ticks must be > 0"));
                }
                if *max_per_window == 0 {
                    return Err(format!("adversaries[{idx}] max_per_window must be > 0"));
                }
            }
            super::AdversaryBudgetModeSpec::Correlated {
                probability,
                burst_ticks,
            } => {
                validate_probability("adversaries.budget.probability", *probability)?;
                if *burst_ticks == 0 {
                    return Err(format!("adversaries[{idx}] burst_ticks must be > 0"));
                }
            }
        }
        match &adversary.action {
            super::AdversaryActionSpec::Withholding
            | super::AdversaryActionSpec::TimingDisturbance { .. }
            | super::AdversaryActionSpec::Corruption => {}
            super::AdversaryActionSpec::Crash { role, .. } => {
                if !role_set.contains(role) {
                    return Err(format!(
                        "adversaries[{idx}] crash references unknown role '{role}'"
                    ));
                }
                if !matches!(
                    adversary.budget.mode,
                    super::AdversaryBudgetModeSpec::Activation
                ) {
                    return Err(format!(
                        "adversaries[{idx}] crash must use budget.mode = \"activation\""
                    ));
                }
                if adversary.budget.total != 1 {
                    return Err(format!(
                        "adversaries[{idx}] crash budgets must declare total = 1"
                    ));
                }
            }
            super::AdversaryActionSpec::ByzantineInterference {
                withholding_probability,
                corruption_probability,
                delay_ticks,
            } => {
                validate_probability(
                    "adversaries.byzantine_interference.withholding_probability",
                    *withholding_probability,
                )?;
                validate_probability(
                    "adversaries.byzantine_interference.corruption_probability",
                    *corruption_probability,
                )?;
                if *withholding_probability == telltale_types::FixedQ32::zero()
                    && *corruption_probability == telltale_types::FixedQ32::zero()
                    && delay_ticks.is_none()
                {
                    return Err(format!(
                        "adversaries[{idx}] byzantine_interference must declare at least one effect"
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_known_distinct_roles(
    idx: usize,
    surface: &str,
    from: &str,
    to: &str,
    role_set: &BTreeSet<String>,
    kind: &str,
) -> Result<(), String> {
    if !role_set.contains(from) {
        return Err(format!(
            "{surface}[{idx}] {kind} references unknown role '{from}'"
        ));
    }
    if !role_set.contains(to) {
        return Err(format!(
            "{surface}[{idx}] {kind} references unknown role '{to}'"
        ));
    }
    if from == to {
        return Err(format!("{surface}[{idx}] {kind} must name distinct roles"));
    }
    Ok(())
}

fn validate_group_footprint(
    surface: &str,
    groups: &[Vec<String>],
    role_set: &BTreeSet<String>,
) -> Result<(), String> {
    if groups.is_empty() {
        return Err(format!("{surface} must define at least one group"));
    }
    let mut seen = BTreeSet::new();
    for (group_idx, group) in groups.iter().enumerate() {
        if group.is_empty() {
            return Err(format!("{surface}.groups[{group_idx}] must not be empty"));
        }
        for role in group {
            if !role_set.contains(role) {
                return Err(format!("{surface} references unknown role '{role}'"));
            }
            if !seen.insert(role.clone()) {
                return Err(format!(
                    "{surface} role '{role}' appears in multiple groups"
                ));
            }
        }
    }
    Ok(())
}
