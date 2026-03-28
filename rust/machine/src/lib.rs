//! Protocol-machine and guest-runtime surfaces for choreographic session type protocols.
//!
//! This crate provides a standalone, embeddable protocol machine that executes
//! choreographic protocols projected to local session types. The protocol
//! machine validates every instruction against its session type monitor,
//! ensuring protocol conformance at runtime.
//!
//! # Architecture
//!
//! The protocol machine follows the Lean specification in `lean/Runtime/ProtocolMachine/`:
//! - **Instructions** ([`instr::Instr`]): bytecode ops for send/recv/choice/session lifecycle
//! - **Coroutines** ([`coroutine::Coroutine`]): lightweight execution units, one per role
//! - **Sessions** ([`session::SessionStore`]): manage session lifecycle and namespaces
//! - **Buffers** ([`buffer::BoundedBuffer`]): bounded message channels with backpressure
//! - **Scheduler** ([`scheduler::Scheduler`]): policy-based coroutine scheduling
//! - **Loader** ([`loader`]): dynamic choreography loading with validation
//! - **Compiler** ([`compiler`]): compile `LocalTypeR` to bytecode
//!
//! The crate exposes one canonical single-thread protocol-machine surface,
//! [`ProtocolMachine`], plus guest-runtime driver surfaces such as
//! [`GuestRuntime`]. Higher-level systems (for example `telltale-simulator`)
//! instantiate guest runtimes around the protocol machine with deterministic
//! middleware for network latency, faults, property monitoring, and
//! checkpointing.
//!
//! **Nested simulation** is supported via [`runtime::runner::NestedProtocolMachineHandler`], which
//! allows a protocol-machine coroutine to host an inner protocol machine for
//! distributed or hierarchical simulations.
//!
//! # Effect Handler Contract
//!
//! The protocol machine's [`EffectHandler`] is synchronous, deterministic, and
//! **session-local**. It must not depend on global time or shared mutable
//! state across sessions. This is distinct from the async, typed
//! `telltale_runtime::ChoreoHandler` used by generated choreography code.
//!
//! # Usage
//!
//! ```ignore
//! use telltale_machine::{
//!     GuestRuntime, OwnedSession, ProtocolMachine, ProtocolMachineConfig, loader::CodeImage
//! };
//!
//! let config = ProtocolMachineConfig::default();
//! let mut machine = ProtocolMachine::new(config);
//! let image = CodeImage::from_local_types(&local_types, &global_type);
//! let _session: OwnedSession =
//!     machine.load_choreography_owned(&image, "runtime/owner")?;
//! while machine.step(&handler)? {}
//!
//! let mut guest = GuestRuntime::new(ProtocolMachineConfig::default());
//! let _owned = guest.load_choreography_owned(&image, "runtime/owner")?;
//! guest.run(&handler, 64, 1)?;
//! ```

use cfg_if::cfg_if;

pub mod architecture;
pub mod bridge;
pub mod buffer;
pub mod clock;
pub mod commit_common;
/// Communication replay modes and consumption state for deterministic and speculatively
/// replayed session histories.
pub mod communication_replay;
pub mod compiler;
pub mod composition;
pub mod coroutine;
pub mod determinism;
pub mod driver;
mod effect;
mod engine;
pub mod envelope_diff;
pub mod exec;
mod exec_api;
pub mod faults;
pub mod guard;
pub mod identity;
pub mod instr;
pub mod instruction_semantics;
pub mod integration;
pub mod intern;
pub mod kernel;
mod loader;
mod nested;
pub mod output_condition;
pub mod owned;
pub mod persistence;
pub mod runtime_contracts;
mod scheduler;
pub mod semantic_objects;
pub mod serialization;
/// Session store and role/session bookkeeping used by protocol execution.
mod session;
pub mod trace;
pub mod transfer_semantics;
pub mod verification;

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        mod threaded;
    }
}

cfg_if! {
    if #[cfg(target_arch = "wasm32")] {
        mod wasm;
    }
}

/// Canonical protocol-machine model surface aligned with Lean `Runtime.ProtocolMachine.Model`.
pub mod model {
    /// Core execution objects and instruction vocabulary.
    pub mod core {
        pub use crate::coroutine::{CoroStatus, Coroutine, CoroutineState, KnowledgeSet, Value};
        pub use crate::instr::Instr;
    }

    /// Protocol-machine configuration and retained-state metadata.
    pub mod config {
        pub use crate::engine::{
            EffectTraceCaptureMode, MonitorMode, ObservabilityRetentionConfig,
            ObservabilityRetentionMode, PayloadValidationMode, ProtocolMachineConfig,
            ProtocolMachineMemoryUsage, ProtocolMachineRetainedBytes, ResourceState,
            RuntimeTuningProfile, ThreadedRoundSemantics,
        };
    }

    /// Program and compiled-code objects.
    pub mod program {
        pub use crate::engine::{Program, ProgramStore};
    }

    /// Effect boundary and effect algebra objects.
    pub mod effects {
        pub use crate::bridge::EffectGuardBridge;
        pub use crate::effect::{
            CorruptionType, EffectAdmissibility, EffectAgreementUse, EffectAuthorityClass,
            EffectCompositionPolicy, EffectExchangeRecord, EffectFailure, EffectFailureKind,
            EffectHandler, EffectHandlerDomain, EffectInterfaceMetadata, EffectOutcome,
            EffectOutcomeStatus, EffectReentrancyPolicy, EffectRegionScope, EffectRequest,
            EffectRequestBody, EffectResponse, EffectResponsibilityDomain, EffectResult,
            EffectRetryShape, EffectSemanticClass, EffectTimeoutPolicy, EffectTotality,
            EffectTraceEntry, EffectTraceTape, RecordingEffectHandler, ReplayEffectHandler,
            SendDecision, SendDecisionInput, TopologyPerturbation,
        };
    }

    /// Scheduler policy and scheduling-state vocabulary.
    pub mod scheduler_types {
        pub use crate::scheduler::{
            CrossLaneHandoff, LaneId, PriorityPolicy, SchedPolicy, SchedState, Scheduler,
            StepUpdate,
        };
    }

    /// State-level session, ownership, and edge objects.
    pub mod state {
        pub use crate::engine::{ObsEvent, ProtocolMachineState};
        pub use crate::session::{
            decode_edge_json, AuthorityArtifact, AuthorityAuditEvent, AuthorityAuditRecord,
            AuthorityWitnessId, CancellationWitness, ClosedSessionSummary, Edge, FragmentOwnerId,
            HandlerId, OwnershipCapability, OwnershipClaimId, OwnershipEpoch, OwnershipError,
            OwnershipReceipt, OwnershipScope, OwnershipTerminalReason, ReadinessWitness,
            SessionHostMutation, SessionId, SessionStatus, SessionStore, SessionStoreMemoryUsage,
            SessionStoreRetainedBytes, TimeoutWitness,
        };
        pub use crate::session::{unfold_if_var, unfold_mu};
    }

    /// Output-condition model surfaces.
    pub mod output_condition {
        pub use crate::output_condition::{
            verify_output_condition, OutputConditionCheck, OutputConditionHint,
            OutputConditionMeta, OutputConditionPolicy,
        };
    }

    /// Canonical protocol-machine semantic-object family.
    pub mod semantic_objects {
        pub use crate::semantic_objects::{
            protocol_machine_semantic_objects, AgreementContract, AgreementEvidence,
            AgreementEvidenceKind, AgreementLevel, AgreementProfile, AgreementRule, AgreementState,
            AuthoritativeRead, AuthoritativeReadKind, AuthoritativeReadLifecycle, CanonicalHandle,
            CanonicalHandleKind, DelegationStatus, FinalizationOutcome, MaterializationProof,
            ObservedRead, OperationInstance, OperationPhase, OperationVisibility,
            OutstandingEffect, OutstandingEffectStatus, OwnershipScope, PrestateBinding,
            ProgressContract, ProgressState, ProgressTransition, ProtocolMachineSemanticObjects,
            PublicationEvent, PublicationObserverClass, PublicationStatus, Region, SemanticHandoff,
            TransformationObligation, SEMANTIC_OBJECTS_SCHEMA_VERSION,
        };
    }
}

/// Canonical runtime surface aligned with Lean `Runtime.ProtocolMachine.Runtime`.
pub mod runtime {
    /// Runtime loading surface.
    pub mod loader {
        pub use crate::loader::CodeImage;
    }

    /// Runtime failure and admission surfaces.
    pub mod failure {
        pub use crate::faults::{classify_fault, fault_code, fault_code_of, FaultClass};
        pub use crate::runtime_contracts::{
            admit_protocol_machine_runtime, determinism_profile_supported,
            enforce_protocol_machine_runtime_gates, execution_profile_supported,
            request_determinism_profile, requires_protocol_machine_runtime_contracts,
            runtime_capability_snapshot, runtime_execution_profile, DeterminismArtifacts,
            ProtocolMachineAdmissibilityClass, ProtocolMachineEscalationWindowClass,
            ProtocolMachineExecutionProfile, ProtocolMachineFairnessAssumption,
            RuntimeAdmissionResult, RuntimeCapability, RuntimeContracts, RuntimeGateResult,
        };
    }

    /// Runtime runner and guest-runtime surfaces.
    pub mod runner {
        pub use crate::driver::NativeSingleThreadDriver as GuestRuntime;
        pub use crate::engine::{
            ProtocolMachine, ProtocolMachineError, RunStatus, SchedExecStatus, SchedStepDebug,
            StepResult,
        };
        pub use crate::kernel::ProtocolMachineKernel;
        pub use crate::nested::NestedProtocolMachineHandler;
        pub use crate::owned::OwnedSession;
        #[cfg(target_arch = "wasm32")]
        pub use crate::wasm::WasmProtocolMachine;
    }

    /// Multi-threaded runtime surface.
    pub mod threaded_runner {
        #[cfg(feature = "multi-thread")]
        pub use crate::driver::NativeThreadedDriver as ThreadedGuestRuntime;
        #[cfg(feature = "multi-thread")]
        pub use crate::threaded::ThreadedProtocolMachine;
    }
}

/// Canonical semantics surface aligned with Lean `Runtime.ProtocolMachine.Semantics`.
pub mod semantics {
    /// Instruction-step execution surfaces.
    pub mod exec {
        pub use crate::exec_api::{ExecResult, ExecStatus, StepEvent, StepPack};
        pub use crate::integration::{
            run_loaded_protocol_machine_record_replay_conformance,
            LoadedProtocolMachineReplayConformance,
        };
    }
}

pub use architecture::{
    EngineOwnership, EngineRole, CANONICAL_ENGINE, CROSS_TARGET_CONTRACT, ENGINE_OWNERSHIP,
    EQUIVALENCE_SURFACES,
};
pub use bridge::{
    EffectGuardBridge, IdentityGuardBridge, IdentityPersistenceBridge, IdentityVerificationBridge,
    PersistenceEffectBridge,
};
pub use clock::SimClock;
pub use communication_replay::{
    CommunicationConsumeResult, CommunicationConsumption, CommunicationConsumptionArtifact,
    CommunicationIdentity, CommunicationReplayError, CommunicationReplayMode,
    CommunicationReplayState, CommunicationStepKind, DefaultCommunicationConsumption,
    COMM_IDENTITY_DOMAIN_TAG, COMM_REPLAY_DUPLICATE_TAG, COMM_REPLAY_SEQUENCE_MISMATCH_TAG,
};
pub use composition::{
    ComposedRuntime, CompositionCertificate, CompositionError, DeterminismCapability, MemoryBudget,
    MemoryUsage, ProtocolBundle, ReconfigurationEvent, ReconfigurationPolicy, SchedulerCapability,
    TheoremPackCapabilities,
};
pub use coroutine::{CoroStatus, Coroutine, CoroutineState, KnowledgeSet, Value};
pub use determinism::{DeterminismMode, EffectDeterminismTier};
pub use driver::NativeSingleThreadDriver as GuestRuntime;
pub use effect::{
    CorruptionType, EffectAdmissibility, EffectAgreementUse, EffectAuthorityClass,
    EffectCompositionPolicy, EffectExchangeRecord, EffectFailure, EffectFailureKind,
    EffectHandlerDomain, EffectInterfaceMetadata, EffectOutcome, EffectOutcomeStatus,
    EffectReentrancyPolicy, EffectRegionScope, EffectRequest, EffectRequestBody, EffectResponse,
    EffectResponsibilityDomain, EffectResult, EffectRetryShape, EffectSemanticClass,
    EffectTimeoutPolicy, EffectTotality, EffectTraceEntry, EffectTraceTape, RecordingEffectHandler,
    ReplayEffectHandler, TopologyPerturbation,
};
pub use engine::{
    EffectTraceCaptureMode, MonitorMode, ObsEvent, ObservabilityRetentionConfig,
    ObservabilityRetentionMode, PayloadValidationMode, Program, ProgramStore, ProtocolMachine,
    ProtocolMachineConfig, ProtocolMachineError, ProtocolMachineMemoryUsage,
    ProtocolMachineRetainedBytes, ProtocolMachineState, ResourceState, RunStatus,
    RuntimeTuningProfile, SchedExecStatus, SchedStepDebug, StepResult, ThreadedRoundSemantics,
};
pub use engine::{FlowPolicy, FlowPredicate};
pub use envelope_diff::{
    EffectOrderingClass, EnvelopeDiff, EnvelopeDiffArtifactV1, FailureVisibleDiffClass,
    SchedulerPermutationClass, WaveWidthBound,
};
pub use exec_api::{ExecResult, ExecStatus, StepEvent, StepPack};
pub use faults::{classify_fault, fault_code, fault_code_of, FaultClass};
pub use guard::{GuardLayer, InMemoryGuardLayer, LayerId};
pub use identity::{IdentityModel, ParticipantId, SiteId as IdentitySiteId, StaticIdentityModel};
pub use instr::Instr;
pub use integration::{
    run_loaded_protocol_machine_record_replay_conformance, LoadedProtocolMachineReplayConformance,
};
pub use intern::{EdgeId, EdgeSymbol, EdgeSymbolTable, StringId, SymbolTable};
pub use kernel::ProtocolMachineKernel;
pub use nested::NestedProtocolMachineHandler;
pub use output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionHint, OutputConditionMeta,
    OutputConditionPolicy,
};
pub use owned::OwnedSession;
pub use persistence::{NoopPersistence, PersistenceModel};
pub use runtime_contracts::{
    admit_protocol_machine_runtime, determinism_profile_supported,
    enforce_protocol_machine_runtime_gates, execution_profile_supported,
    request_determinism_profile, requires_protocol_machine_runtime_contracts,
    runtime_capability_snapshot, runtime_execution_profile, DeterminismArtifacts,
    ProtocolMachineAdmissibilityClass, ProtocolMachineEscalationWindowClass,
    ProtocolMachineExecutionProfile, ProtocolMachineFairnessAssumption, RuntimeAdmissionResult,
    RuntimeCapability, RuntimeContracts, RuntimeGateResult,
};
pub use scheduler::{
    CrossLaneHandoff, LaneId as SchedulerLaneId, PriorityPolicy, SchedPolicy, SchedState,
    Scheduler, StepUpdate,
};
pub use semantic_objects::{
    protocol_machine_semantic_objects, AgreementContract, AgreementEvidence, AgreementEvidenceKind,
    AgreementLevel, AgreementProfile, AgreementRule, AgreementState, AuthoritativeRead,
    AuthoritativeReadKind, AuthoritativeReadLifecycle, CanonicalHandle, CanonicalHandleKind,
    FinalizationOutcome, MaterializationProof, ObservedRead, OperationInstance, OperationPhase,
    OperationVisibility, OutstandingEffect, OutstandingEffectStatus, PrestateBinding,
    ProgressContract, ProgressState, ProgressTransition, ProtocolMachineSemanticObjects,
    PublicationEvent, PublicationObserverClass, PublicationStatus, Region, SemanticHandoff,
    TransformationObligation, SEMANTIC_OBJECTS_SCHEMA_VERSION,
};
pub use serialization::{
    canonical_effect_trace, canonical_replay_fragment_v1, canonical_semantic_audit_log,
    canonical_trace_v1, canonicalize_protocol_machine_semantic_objects, semantic_audit_log_v1,
    CanonicalReplayFragmentV1, CanonicalTraceV1, SemanticAuditRecord,
};
pub use session::{
    decode_edge_json, AuthorityArtifact, AuthorityAuditEvent, AuthorityAuditRecord,
    AuthorityWitnessId, CancellationWitness, ClosedSessionSummary, Edge, FragmentOwnerId,
    HandlerId, OwnershipCapability, OwnershipClaimId, OwnershipEpoch, OwnershipError,
    OwnershipReceipt, OwnershipScope, OwnershipTerminalReason, ReadinessWitness,
    SessionHostMutation, SessionId, SessionStore, SessionStoreMemoryUsage,
    SessionStoreRetainedBytes, TimeoutWitness,
};
pub use trace::{
    normalize_trace, normalize_trace_v1, obs_session, strict_trace, with_tick, NormalizedTraceV1,
    TRACE_NORMALIZATION_SCHEMA_VERSION,
};
pub use transfer_semantics::{
    decode_transfer_request, delegation_receipt, delegation_scope_for_endpoint,
    move_endpoint_bundle, validate_delegation_coherence, DelegationAuditRecord, DelegationReceipt,
    DelegationStatus, TransferRequest,
};
pub use verification::{
    sign_value, verify_signed_value, AuthProof, AuthTree, Commitment, DefaultVerificationModel,
    Hash, HashTag, Nullifier, Signature, SigningKey, VerificationModel, VerifyingKey,
};

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        pub use threaded::ThreadedProtocolMachine as ThreadedProtocolMachine;
        pub use driver::NativeThreadedDriver as ThreadedGuestRuntime;
        pub use threaded::{ContentionMetrics, LaneHandoff, LaneId, LaneSchedulerState, LaneSelection};
    }
}

cfg_if! {
    if #[cfg(target_arch = "wasm32")] {
        pub use wasm::WasmProtocolMachine;
    }
}
