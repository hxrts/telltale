use super::{validate_non_negative, validate_probability, Fault, Scenario};
use std::collections::BTreeSet;

pub(super) fn validate_semantics(scenario: &Scenario) -> Result<(), String> {
    let role_set = validate_roles(scenario)?;
    validate_limits(scenario)?;
    validate_network(scenario, &role_set)?;
    validate_events(scenario, &role_set)?;
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
    if scenario.concurrency == 0 {
        return Err("scenario.concurrency must be >= 1".to_string());
    }
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
    validate_network_partitions(network, role_set)?;
    validate_network_links(network, role_set)?;
    Ok(())
}

fn validate_network_partitions(
    network: &super::NetworkSpec,
    role_set: &BTreeSet<String>,
) -> Result<(), String> {
    for (idx, partition) in network.partitions.iter().enumerate() {
        if partition.start_tick > partition.end_tick {
            return Err(format!(
                "network.partitions[{idx}] has start_tick > end_tick"
            ));
        }
        if partition.groups.is_empty() {
            return Err(format!(
                "network.partitions[{idx}] must define at least one group"
            ));
        }
        let mut seen_partition_roles = BTreeSet::new();
        for (group_idx, group) in partition.groups.iter().enumerate() {
            if group.is_empty() {
                return Err(format!(
                    "network.partitions[{idx}].groups[{group_idx}] must not be empty"
                ));
            }
            for role in group {
                if !role_set.contains(role) {
                    return Err(format!(
                        "network.partitions[{idx}] references unknown role '{role}'"
                    ));
                }
                if !seen_partition_roles.insert(role.clone()) {
                    return Err(format!(
                        "network.partitions[{idx}] role '{role}' appears in multiple groups"
                    ));
                }
            }
        }
    }
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
        if let (Some(start), Some(end)) = (link.start_tick, link.end_tick) {
            if start > end {
                return Err(format!("network.links[{idx}] has start_tick > end_tick"));
            }
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

fn validate_events(scenario: &Scenario, role_set: &BTreeSet<String>) -> Result<(), String> {
    for (idx, event) in scenario.events.iter().enumerate() {
        let _trigger = event.trigger.to_trigger()?;
        match event.action.to_fault()? {
            Fault::NodeCrash { role, .. } => {
                if !role_set.contains(&role) {
                    return Err(format!(
                        "events[{idx}] node_crash references unknown role '{role}'"
                    ));
                }
            }
            Fault::NetworkPartition { groups, .. } => {
                validate_event_network_partition(idx, &groups, role_set)?;
            }
            Fault::MessageDrop { .. }
            | Fault::MessageDelay { .. }
            | Fault::MessageCorruption { .. } => {}
        }
    }
    Ok(())
}

fn validate_event_network_partition(
    idx: usize,
    groups: &[Vec<String>],
    role_set: &BTreeSet<String>,
) -> Result<(), String> {
    if groups.is_empty() {
        return Err(format!(
            "events[{idx}] network_partition must define at least one group"
        ));
    }
    let mut seen = BTreeSet::new();
    for (group_idx, group) in groups.iter().enumerate() {
        if group.is_empty() {
            return Err(format!(
                "events[{idx}] network_partition group {group_idx} must not be empty"
            ));
        }
        for role in group {
            if !role_set.contains(role) {
                return Err(format!(
                    "events[{idx}] network_partition references unknown role '{role}'"
                ));
            }
            if !seen.insert(role.clone()) {
                return Err(format!(
                    "events[{idx}] network_partition role '{role}' appears in multiple groups"
                ));
            }
        }
    }
    Ok(())
}
