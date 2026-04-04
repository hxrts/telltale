//! Reconfiguration and placement types for protocol role migration.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// Canonical placement kind used by reconfiguration and recovery artifacts.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum PlacementKind {
    /// In-process placement.
    Local,
    /// Remote endpoint placement.
    Remote,
    /// Colocated with another role.
    Colocated,
}

/// Canonical placement observation for one active role.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PlacementObservation {
    /// Stable role name.
    pub role: String,
    /// Canonical placement kind.
    pub kind: PlacementKind,
    /// Optional remote endpoint for remote roles.
    pub endpoint: Option<String>,
    /// Optional region hint.
    pub region: Option<String>,
    /// Peer role for colocated placement.
    pub colocated_with: Option<String>,
}

impl PlacementObservation {
    /// Construct a local placement observation.
    #[must_use]
    pub fn local(role: impl Into<String>) -> Self {
        Self {
            role: role.into(),
            kind: PlacementKind::Local,
            endpoint: None,
            region: None,
            colocated_with: None,
        }
    }

    /// Construct a remote placement observation.
    #[must_use]
    pub fn remote(role: impl Into<String>, endpoint: impl Into<String>) -> Self {
        Self {
            role: role.into(),
            kind: PlacementKind::Remote,
            endpoint: Some(endpoint.into()),
            region: None,
            colocated_with: None,
        }
    }

    /// Construct a colocated placement observation.
    #[must_use]
    pub fn colocated(role: impl Into<String>, peer: impl Into<String>) -> Self {
        Self {
            role: role.into(),
            kind: PlacementKind::Colocated,
            endpoint: None,
            region: None,
            colocated_with: Some(peer.into()),
        }
    }

    /// Attach a canonical region hint.
    #[must_use]
    pub fn with_region(mut self, region: impl Into<String>) -> Self {
        self.region = Some(region.into());
        self
    }
}

/// Derived transport boundary kind between two active roles.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum TransportBoundaryKind {
    /// Both roles are in the same process without an explicit colocated hop.
    InProcess,
    /// Roles share a node through explicit colocated placement.
    SharedMemory,
    /// At least one side is remote.
    Network,
}

/// Canonical transport-observable boundary derived from placement observations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TransportBoundaryObservation {
    /// Stable lower-sorted role name.
    pub from_role: String,
    /// Stable higher-sorted role name.
    pub to_role: String,
    /// Derived boundary kind.
    pub boundary: TransportBoundaryKind,
    /// Whether the two roles resolve to different explicit regions.
    pub cross_region: bool,
}

/// Canonical phase for a transition or runtime-upgrade artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TransitionArtifactPhase {
    /// Transition is staged but not yet admitted.
    Staged,
    /// Transition passed admission and compatibility checks.
    Admitted,
    /// Transition committed a new active runtime cutover.
    CommittedCutover,
    /// Transition was rolled back after staging/admission.
    RolledBack,
    /// Transition failed before commit.
    Failed,
}

/// Pending-effect treatment required for a specialized runtime upgrade.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PendingEffectTreatment {
    /// Pending effects are carried across the cutover.
    PreservePending,
    /// Blocked/invalidated effects must be made explicit before cutover.
    InvalidateBlocked,
}

/// Canonical publication continuity policy required for a runtime upgrade.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CanonicalPublicationContinuity {
    /// Existing canonical publications/handles must stay valid across the cutover.
    PreserveCanonicalTruth,
    /// Canonical publications may be invalidated and re-issued.
    ReissueCanonicalTruth,
}

/// Execution-profile constraint required for a runtime upgrade.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RuntimeUpgradeExecutionConstraint {
    /// Preserve the admitted proof-carrying bundle profile.
    PreserveBundleProfile,
    /// Requires theorem-pack/runtime support for mixed determinism profiles.
    MixedDeterminismAllowed,
}

/// Canonical compatibility contract for one specialized runtime upgrade.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RuntimeUpgradeCompatibility {
    /// Execution-profile constraint for the upgrade.
    pub execution_constraint: RuntimeUpgradeExecutionConstraint,
    /// Whether ownership continuity must be preserved across the cutover.
    pub ownership_continuity_required: bool,
    /// Pending-effect treatment policy.
    pub pending_effect_treatment: PendingEffectTreatment,
    /// Canonical publication continuity policy.
    pub canonical_publication_continuity: CanonicalPublicationContinuity,
}

/// Canonical serialized artifact for one runtime-upgrade transition phase.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RuntimeUpgradeArtifact {
    /// Stable upgrade identifier.
    pub upgrade_id: String,
    /// Phase represented by this artifact.
    pub phase: TransitionArtifactPhase,
    /// Canonical sorted members before this phase.
    pub previous_members: Vec<String>,
    /// Canonical sorted members after this phase.
    pub next_members: Vec<String>,
    /// Compatibility contract admitted for this upgrade.
    pub compatibility: RuntimeUpgradeCompatibility,
    /// Canonical publication ids carried into the new runtime.
    pub carried_publication_ids: Vec<String>,
    /// Canonical publication ids invalidated by the cutover.
    pub invalidated_publication_ids: Vec<String>,
    /// Stable obligation ids carried into the new runtime.
    pub carried_obligation_ids: Vec<String>,
    /// Stable obligation ids invalidated by the cutover.
    pub invalidated_obligation_ids: Vec<String>,
    /// Optional failure/rollback reason.
    pub reason: Option<String>,
}

#[derive(Debug, Clone)]
struct ResolvedPlacement {
    node_key: String,
    region: Option<String>,
    uses_colocation: bool,
    remote: bool,
}

fn normalize_placement_observations(
    observations: &[PlacementObservation],
) -> Result<Vec<PlacementObservation>, String> {
    let mut normalized = observations.to_vec();
    normalized.sort_by(|left, right| left.role.cmp(&right.role));

    let mut seen_roles = BTreeSet::new();
    for observation in &normalized {
        if !seen_roles.insert(observation.role.clone()) {
            return Err(format!(
                "duplicate placement observation for role {}",
                observation.role
            ));
        }
        match observation.kind {
            PlacementKind::Local => {
                if observation.endpoint.is_some() {
                    return Err(format!(
                        "local role {} must not carry a remote endpoint",
                        observation.role
                    ));
                }
                if observation.colocated_with.is_some() {
                    return Err(format!(
                        "local role {} must not carry colocated_with metadata",
                        observation.role
                    ));
                }
            }
            PlacementKind::Remote => {
                if observation.endpoint.is_none() {
                    return Err(format!(
                        "remote role {} must carry an endpoint",
                        observation.role
                    ));
                }
                if observation.colocated_with.is_some() {
                    return Err(format!(
                        "remote role {} must not carry colocated_with metadata",
                        observation.role
                    ));
                }
            }
            PlacementKind::Colocated => {
                let Some(peer) = observation.colocated_with.as_ref() else {
                    return Err(format!(
                        "colocated role {} must name its colocated peer",
                        observation.role
                    ));
                };
                if peer == &observation.role {
                    return Err(format!(
                        "role {} may not be colocated with itself",
                        observation.role
                    ));
                }
                if observation.endpoint.is_some() {
                    return Err(format!(
                        "colocated role {} must not carry a direct endpoint",
                        observation.role
                    ));
                }
            }
        }
    }

    Ok(normalized)
}

fn resolve_placement(
    role: &str,
    placements: &BTreeMap<String, PlacementObservation>,
    visiting: &mut BTreeSet<String>,
) -> Result<ResolvedPlacement, String> {
    if !visiting.insert(role.to_string()) {
        return Err(format!("cyclic colocated placement involving role {role}"));
    }

    let resolved = match placements.get(role) {
        Some(PlacementObservation {
            kind: PlacementKind::Local,
            region,
            ..
        }) => Ok(ResolvedPlacement {
            node_key: "local".to_string(),
            region: region.clone(),
            uses_colocation: false,
            remote: false,
        }),
        Some(PlacementObservation {
            kind: PlacementKind::Remote,
            endpoint,
            region,
            ..
        }) => Ok(ResolvedPlacement {
            node_key: format!("remote:{}", endpoint.clone().unwrap_or_default()),
            region: region.clone(),
            uses_colocation: false,
            remote: true,
        }),
        Some(PlacementObservation {
            kind: PlacementKind::Colocated,
            role,
            colocated_with,
            region,
            ..
        }) => {
            let peer = colocated_with
                .as_ref()
                .expect("normalized colocated observation should name its peer");
            let inherited = resolve_placement(peer, placements, visiting)?;
            if let (Some(explicit), Some(inherited_region)) =
                (region.as_ref(), inherited.region.as_ref())
            {
                if explicit != inherited_region {
                    return Err(format!(
                        "role {role} declares region {explicit} but colocated peer resolves to {inherited_region}"
                    ));
                }
            }
            Ok(ResolvedPlacement {
                node_key: inherited.node_key,
                region: region.clone().or(inherited.region),
                uses_colocation: true,
                remote: inherited.remote,
            })
        }
        None => Err(format!("placement observation is missing role {role}")),
    };

    visiting.remove(role);
    resolved
}

/// Canonicalize and validate placement observations.
///
/// # Errors
///
/// Returns a descriptive error when the observation set is internally inconsistent.
pub fn canonicalize_placement_observations(
    observations: &[PlacementObservation],
) -> Result<Vec<PlacementObservation>, String> {
    let normalized = normalize_placement_observations(observations)?;
    let placements = normalized
        .iter()
        .cloned()
        .map(|observation| (observation.role.clone(), observation))
        .collect::<BTreeMap<_, _>>();
    for role in placements.keys() {
        resolve_placement(role, &placements, &mut BTreeSet::new())?;
    }
    Ok(normalized)
}

/// Derive canonical transport-observable boundaries for a placement set.
///
/// # Errors
///
/// Returns a descriptive error when the observation set is internally inconsistent.
pub fn canonical_transport_boundaries(
    observations: &[PlacementObservation],
) -> Result<Vec<TransportBoundaryObservation>, String> {
    let normalized = canonicalize_placement_observations(observations)?;
    let placements = normalized
        .iter()
        .cloned()
        .map(|observation| (observation.role.clone(), observation))
        .collect::<BTreeMap<_, _>>();
    let mut resolved = BTreeMap::new();
    for role in placements.keys() {
        resolved.insert(
            role.clone(),
            resolve_placement(role, &placements, &mut BTreeSet::new())?,
        );
    }

    let roles = normalized
        .iter()
        .map(|observation| observation.role.clone())
        .collect::<Vec<_>>();
    let mut boundaries = Vec::new();
    for (index, left_role) in roles.iter().enumerate() {
        for right_role in roles.iter().skip(index + 1) {
            let left_resolved = resolved
                .get(left_role)
                .expect("resolved placements should exist for every role");
            let right_resolved = resolved
                .get(right_role)
                .expect("resolved placements should exist for every role");
            let boundary = if left_resolved.remote || right_resolved.remote {
                TransportBoundaryKind::Network
            } else if left_resolved.uses_colocation || right_resolved.uses_colocation {
                TransportBoundaryKind::SharedMemory
            } else {
                TransportBoundaryKind::InProcess
            };
            let cross_region = match (&left_resolved.region, &right_resolved.region) {
                (Some(left), Some(right)) => left != right,
                _ => false,
            };
            boundaries.push(TransportBoundaryObservation {
                from_role: left_role.clone(),
                to_role: right_role.clone(),
                boundary,
                cross_region,
            });
        }
    }
    Ok(boundaries)
}

#[cfg(test)]
mod tests {
    use super::{canonical_transport_boundaries, PlacementObservation, TransportBoundaryKind};

    #[test]
    fn remote_and_colocated_boundaries_are_canonical() {
        let boundaries = canonical_transport_boundaries(&[
            PlacementObservation::local("Alice").with_region("eu_central_1"),
            PlacementObservation::remote("Bob", "127.0.0.1:19801").with_region("eu_west_1"),
            PlacementObservation::colocated("Carol", "Alice").with_region("eu_central_1"),
        ])
        .expect("valid placement observations");

        assert_eq!(
            boundaries,
            vec![
                super::TransportBoundaryObservation {
                    from_role: "Alice".to_string(),
                    to_role: "Bob".to_string(),
                    boundary: TransportBoundaryKind::Network,
                    cross_region: true,
                },
                super::TransportBoundaryObservation {
                    from_role: "Alice".to_string(),
                    to_role: "Carol".to_string(),
                    boundary: TransportBoundaryKind::SharedMemory,
                    cross_region: false,
                },
                super::TransportBoundaryObservation {
                    from_role: "Bob".to_string(),
                    to_role: "Carol".to_string(),
                    boundary: TransportBoundaryKind::Network,
                    cross_region: true,
                },
            ]
        );
    }

    #[test]
    fn conflicting_colocated_regions_reject() {
        let error = canonical_transport_boundaries(&[
            PlacementObservation::local("Alice").with_region("eu_central_1"),
            PlacementObservation::colocated("Bob", "Alice").with_region("us_east_1"),
        ])
        .expect_err("conflicting colocated regions must reject");

        assert!(
            error.contains("declares region"),
            "expected explicit colocated-region conflict, got {error}"
        );
    }
}
