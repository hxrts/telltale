//! Admission and capability vocabulary for `telltale-search`.

use std::collections::BTreeSet;

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
    /// Selected-result cost.
    #[serde(alias = "IncumbentCost")]
    SelectedResultCost,
    /// Canonical parent identity.
    CanonicalParentIdentity,
    /// Selected-result witness identity.
    #[serde(alias = "CanonicalPathIdentity")]
    SelectedResultWitnessIdentity,
    /// Selected-result publication trace.
    #[serde(alias = "IncumbentPublicationTrace")]
    SelectedResultPublicationTrace,
    /// Normalized commit trace.
    NormalizedCommitTrace,
    /// Replay checkpoint trace.
    ReplayCheckpointTrace,
    /// Graph epoch trace.
    GraphEpochTrace,
    /// Scheduler profile and lane trace.
    SchedulerProfileTrace,
    /// Fairness premise bundle for theorem-shaped comparisons.
    FairnessPremiseTrace,
    /// Productive and total-step accounting.
    ProgressAccounting,
}

/// Generic alias for the selected-result cost observable.
pub const SELECTED_RESULT_COST_OBSERVABLE: SearchObservableClass =
    SearchObservableClass::SelectedResultCost;

/// Generic alias for the selected-result witness observable.
pub const SELECTED_RESULT_WITNESS_OBSERVABLE: SearchObservableClass =
    SearchObservableClass::SelectedResultWitnessIdentity;

/// Generic alias for the selected-result publication trace observable.
pub const SELECTED_RESULT_PUBLICATION_TRACE_OBSERVABLE: SearchObservableClass =
    SearchObservableClass::SelectedResultPublicationTrace;

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
    pub required_observables: BTreeSet<SearchObservableClass>,
    /// Required determinism profiles.
    pub required_profiles: BTreeSet<SearchDeterminismMode>,
    /// Required scheduler-profile support.
    pub required_scheduler_profiles: BTreeSet<SearchSchedulerProfile>,
    /// Required fairness-premise support.
    pub required_fairness: BTreeSet<SearchFairnessAssumption>,
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
    pub supported_observables: BTreeSet<SearchObservableClass>,
    /// Supported determinism profiles.
    pub supported_profiles: BTreeSet<SearchDeterminismMode>,
    /// Supported scheduler-profile classes.
    pub supported_scheduler_profiles: BTreeSet<SearchSchedulerProfile>,
    /// Supported fairness bundles.
    pub supported_fairness: BTreeSet<SearchFairnessAssumption>,
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

    reasons.extend(
        user.required_observables
            .difference(&certified.supported_observables)
            .copied()
            .map(AdmissionRejectionReason::MissingObservable),
    );

    reasons.extend(
        user.required_profiles
            .difference(&certified.supported_profiles)
            .copied()
            .map(AdmissionRejectionReason::MissingProfile),
    );

    reasons.extend(
        user.required_scheduler_profiles
            .difference(&certified.supported_scheduler_profiles)
            .copied()
            .map(AdmissionRejectionReason::MissingSchedulerProfile),
    );

    reasons.extend(
        user.required_fairness
            .difference(&certified.supported_fairness)
            .copied()
            .map(AdmissionRejectionReason::MissingFairness),
    );

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

    fn full_user() -> SearchDUser {
        SearchDUser {
            required_observables: [
                SearchObservableClass::SelectedResultCost,
                SearchObservableClass::SchedulerProfileTrace,
            ]
            .into_iter()
            .collect(),
            required_profiles: [SearchDeterminismMode::Replay].into_iter().collect(),
            required_scheduler_profiles: [SearchSchedulerProfile::BatchedParallelExact]
                .into_iter()
                .collect(),
            required_fairness: [SearchFairnessAssumption::EventualBarrierService]
                .into_iter()
                .collect(),
            required_commutativity_region: CommutativityRegionClass::CertifiedFrontierWindow,
            max_batch_width: 4,
            require_frozen_epoch_replay: true,
            replay_required: true,
        }
    }

    fn full_certified() -> SearchCertifiedCapability {
        SearchCertifiedCapability {
            supported_observables: [
                SearchObservableClass::SelectedResultCost,
                SearchObservableClass::SchedulerProfileTrace,
            ]
            .into_iter()
            .collect(),
            supported_profiles: [SearchDeterminismMode::Replay].into_iter().collect(),
            supported_scheduler_profiles: [SearchSchedulerProfile::BatchedParallelExact]
                .into_iter()
                .collect(),
            supported_fairness: [SearchFairnessAssumption::EventualBarrierService]
                .into_iter()
                .collect(),
            supported_commutativity_region: CommutativityRegionClass::CertifiedFrontierWindow,
            max_certified_batch_width: 4,
            supports_frozen_epoch_replay: true,
            supports_replay: true,
        }
    }

    #[test]
    fn containment_accepts_exact_match() {
        let reasons = check_capability_containment(&full_user(), &full_certified());
        assert!(reasons.is_empty());
    }

    #[test]
    fn containment_rejects_missing_profile_scheduler_and_fairness() {
        let user = full_user();
        let certified = SearchCertifiedCapability {
            supported_observables: [SearchObservableClass::SelectedResultCost]
                .into_iter()
                .collect(),
            supported_profiles: [SearchDeterminismMode::Full].into_iter().collect(),
            supported_scheduler_profiles: [SearchSchedulerProfile::CanonicalSerial]
                .into_iter()
                .collect(),
            supported_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
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

    #[test]
    fn containment_rejects_missing_observable_and_batch_width_boundary() {
        let mut certified = full_certified();
        certified.supported_observables = [SearchObservableClass::SelectedResultCost]
            .into_iter()
            .collect();
        certified.max_certified_batch_width = 3;
        let reasons = check_capability_containment(&full_user(), &certified);
        assert!(
            reasons.contains(&AdmissionRejectionReason::MissingObservable(
                SearchObservableClass::SchedulerProfileTrace
            ))
        );
        assert!(
            reasons.contains(&AdmissionRejectionReason::BatchWidthTooLarge {
                requested: 4,
                certified: 3,
            })
        );
    }

    #[test]
    fn containment_rejects_commutativity_and_frozen_replay_support_gaps() {
        let mut certified = full_certified();
        certified.supported_commutativity_region = CommutativityRegionClass::SameBatchMinKeyRegion;
        certified.supports_frozen_epoch_replay = false;
        let reasons = check_capability_containment(&full_user(), &certified);
        assert!(
            reasons.contains(&AdmissionRejectionReason::UnsupportedCommutativityRegion(
                CommutativityRegionClass::CertifiedFrontierWindow
            ))
        );
        assert!(reasons.contains(&AdmissionRejectionReason::MissingFrozenEpochReplay));
    }
}
