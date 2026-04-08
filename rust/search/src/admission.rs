//! Admission and capability vocabulary for `telltale-search`.

use serde::{Deserialize, Serialize};

/// Declared determinism profile for one search run.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchDeterminismMode {
    /// Exact search-visible trace equivalence.
    Full,
    /// Exact search-visible equivalence after erasing non-semantic effects.
    ModuloEffects,
    /// Admitted commutative reordering within certified regions.
    ModuloCommutativity,
    /// Exact replay over canonical commit artifacts.
    Replay,
}

/// Declared scheduler class for one search run.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchSchedulerProfile {
    /// Canonical single-lane host loop.
    CanonicalSerial,
    /// Threaded executor at one exact lane.
    ThreadedExactSingleLane,
    /// Batched parallel executor with exact semantics.
    BatchedParallelExact,
    /// Batched parallel executor admitted only modulo an envelope.
    BatchedParallelEnvelopeBounded,
}

/// Fairness premise bundle attached to one run or theorem claim.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchFairnessAssumption {
    /// Every legal live batch is eventually serviced.
    EventualLiveBatchService,
    /// Barriers are eventually serviced.
    EventualBarrierService,
    /// Nodes inside one legal batch window do not starve each other.
    NoStarvationWithinLegalWindow,
    /// Scheduler choice is confluent for the claimed class.
    DeterministicSchedulerConfluence,
}

/// Search-visible observable classes that can be requested or certified.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchObservableClass {
    /// Incumbent path cost.
    IncumbentCost,
    /// Canonical parent identity.
    CanonicalParentIdentity,
    /// Canonical path identity.
    CanonicalPathIdentity,
    /// Incumbent publication trace.
    IncumbentPublicationTrace,
    /// Normalized commit trace.
    NormalizedCommitTrace,
    /// Replay checkpoint trace.
    ReplayCheckpointTrace,
    /// Graph epoch trace.
    GraphEpochTrace,
    /// Scheduler profile and lane trace.
    SchedulerProfileTrace,
    /// Productive and total-step accounting.
    ProgressAccounting,
}

/// Declared commutativity region class.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum CommutativityRegionClass {
    /// No commutative relaxation beyond exact order.
    None,
    /// Reordering only within one min-key batch window.
    SameBatchMinKeyRegion,
    /// Reordering within a separately certified frontier window.
    CertifiedFrontierWindow,
}

/// User-requested determinism and replay capability.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchDUser {
    /// Required observable classes.
    pub required_observables: Vec<SearchObservableClass>,
    /// Required determinism profiles.
    pub required_profiles: Vec<SearchDeterminismMode>,
    /// Required scheduler-profile support.
    pub required_scheduler_profiles: Vec<SearchSchedulerProfile>,
    /// Required fairness-premise support.
    pub required_fairness: Vec<SearchFairnessAssumption>,
    /// Required commutativity region.
    pub required_commutativity_region: CommutativityRegionClass,
    /// Maximum admitted batch width.
    pub max_batch_width: u64,
    /// Whether replay must preserve frozen epoch identity.
    pub require_frozen_epoch_replay: bool,
    /// Whether replay support is mandatory.
    pub replay_required: bool,
}

/// Runtime/artifact-certified search capability.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchCertifiedCapability {
    /// Supported observable classes.
    pub supported_observables: Vec<SearchObservableClass>,
    /// Supported determinism profiles.
    pub supported_profiles: Vec<SearchDeterminismMode>,
    /// Supported scheduler-profile classes.
    pub supported_scheduler_profiles: Vec<SearchSchedulerProfile>,
    /// Supported fairness bundles.
    pub supported_fairness: Vec<SearchFairnessAssumption>,
    /// Supported commutativity region.
    pub supported_commutativity_region: CommutativityRegionClass,
    /// Maximum certified batch width.
    pub max_certified_batch_width: u64,
    /// Whether frozen-epoch replay is supported.
    pub supports_frozen_epoch_replay: bool,
    /// Whether replay support is available at all.
    pub supports_replay: bool,
}

/// Structured admission rejection.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum AdmissionRejectionReason {
    /// Requested observable class is unsupported.
    MissingObservable(SearchObservableClass),
    /// Requested determinism profile is unsupported.
    MissingProfile(SearchDeterminismMode),
    /// Requested scheduler profile is unsupported.
    MissingSchedulerProfile(SearchSchedulerProfile),
    /// Requested fairness assumption is unsupported.
    MissingFairness(SearchFairnessAssumption),
    /// Requested commutativity region is unsupported.
    UnsupportedCommutativityRegion(CommutativityRegionClass),
    /// Requested batch width exceeds certification.
    BatchWidthTooLarge {
        /// Requested maximum width.
        requested: u64,
        /// Certified maximum width.
        certified: u64,
    },
    /// Frozen-epoch replay was requested but not supported.
    MissingFrozenEpochReplay,
    /// Replay was requested but not supported.
    MissingReplay,
}

/// Check whether a requested capability is contained in a certified capability.
#[must_use]
pub fn check_capability_containment(
    user: &SearchDUser,
    certified: &SearchCertifiedCapability,
) -> Vec<AdmissionRejectionReason> {
    let mut reasons = Vec::new();

    for observable in &user.required_observables {
        if !certified.supported_observables.contains(observable) {
            reasons.push(AdmissionRejectionReason::MissingObservable(*observable));
        }
    }

    for profile in &user.required_profiles {
        if !certified.supported_profiles.contains(profile) {
            reasons.push(AdmissionRejectionReason::MissingProfile(*profile));
        }
    }

    for scheduler in &user.required_scheduler_profiles {
        if !certified.supported_scheduler_profiles.contains(scheduler) {
            reasons.push(AdmissionRejectionReason::MissingSchedulerProfile(
                *scheduler,
            ));
        }
    }

    for fairness in &user.required_fairness {
        if !certified.supported_fairness.contains(fairness) {
            reasons.push(AdmissionRejectionReason::MissingFairness(*fairness));
        }
    }

    if user.required_commutativity_region > certified.supported_commutativity_region {
        reasons.push(AdmissionRejectionReason::UnsupportedCommutativityRegion(
            user.required_commutativity_region,
        ));
    }

    if user.max_batch_width > certified.max_certified_batch_width {
        reasons.push(AdmissionRejectionReason::BatchWidthTooLarge {
            requested: user.max_batch_width,
            certified: certified.max_certified_batch_width,
        });
    }

    if user.require_frozen_epoch_replay && !certified.supports_frozen_epoch_replay {
        reasons.push(AdmissionRejectionReason::MissingFrozenEpochReplay);
    }

    if user.replay_required && !certified.supports_replay {
        reasons.push(AdmissionRejectionReason::MissingReplay);
    }

    reasons
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn containment_rejects_missing_profile_scheduler_and_fairness() {
        let user = SearchDUser {
            required_observables: vec![
                SearchObservableClass::IncumbentCost,
                SearchObservableClass::SchedulerProfileTrace,
            ],
            required_profiles: vec![SearchDeterminismMode::Replay],
            required_scheduler_profiles: vec![SearchSchedulerProfile::BatchedParallelExact],
            required_fairness: vec![SearchFairnessAssumption::EventualBarrierService],
            required_commutativity_region: CommutativityRegionClass::CertifiedFrontierWindow,
            max_batch_width: 4,
            require_frozen_epoch_replay: true,
            replay_required: true,
        };
        let certified = SearchCertifiedCapability {
            supported_observables: vec![SearchObservableClass::IncumbentCost],
            supported_profiles: vec![SearchDeterminismMode::Full],
            supported_scheduler_profiles: vec![SearchSchedulerProfile::CanonicalSerial],
            supported_fairness: vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
            supported_commutativity_region: CommutativityRegionClass::SameBatchMinKeyRegion,
            max_certified_batch_width: 1,
            supports_frozen_epoch_replay: false,
            supports_replay: false,
        };

        let reasons = check_capability_containment(&user, &certified);
        assert!(reasons.contains(&AdmissionRejectionReason::MissingProfile(
            SearchDeterminismMode::Replay
        )));
        assert!(
            reasons.contains(&AdmissionRejectionReason::MissingSchedulerProfile(
                SearchSchedulerProfile::BatchedParallelExact
            ))
        );
        assert!(reasons.contains(&AdmissionRejectionReason::MissingFairness(
            SearchFairnessAssumption::EventualBarrierService
        )));
        assert!(reasons.contains(&AdmissionRejectionReason::MissingReplay));
    }
}
