// Choreography struct definition and validation

use super::{ChoiceGuard, Protocol, Role, ValidationError};
use proc_macro2::Ident;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, HashMap};

const ATTR_THEOREM_PACKS: &str = "dsl.proof_bundles";
const ATTR_REQUIRED_THEOREM_PACKS: &str = "dsl.required_proof_bundles";
const ATTR_INFERRED_REQUIRED_THEOREM_PACKS: &str = "dsl.inferred_required_proof_bundles";
const ATTR_ROLE_SETS: &str = "dsl.role_sets";
const ATTR_TOPOLOGIES: &str = "dsl.topologies";
const ATTR_TYPE_DECLARATIONS: &str = "dsl.type_decls";
const ATTR_EFFECT_INTERFACE_DECLARATIONS: &str = "dsl.effect_decls";
const ATTR_PROTOCOL_USES: &str = "dsl.protocol_uses";
const ATTR_REGION_DECLARATIONS: &str = "dsl.fragment_decls";
const ATTR_OPERATION_DECLARATIONS: &str = "dsl.operation_decls";
const ATTR_GUEST_RUNTIME_DECLARATIONS: &str = "dsl.guest_runtime_decls";
const ATTR_EXECUTION_PROFILE_DECLARATIONS: &str = "dsl.execution_profile_decls";
const ATTR_PROTOCOL_EXECUTION_PROFILES: &str = "dsl.protocol_execution_profiles";
const ATTR_AGREEMENT_PROFILE_DECLARATIONS: &str = "dsl.agreement_profile_decls";

/// Typed proof-bundle declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoremPackDeclaration {
    /// Stable bundle name.
    pub name: String,
    /// Capabilities provided by this bundle.
    #[serde(default)]
    pub capabilities: Vec<String>,
    /// Optional bundle version.
    #[serde(default)]
    pub version: Option<String>,
    /// Optional bundle issuer.
    #[serde(default)]
    pub issuer: Option<String>,
    /// Optional constraints attached to the bundle.
    #[serde(default)]
    pub constraints: Vec<String>,
}

/// Typed role-set declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoleSetDeclaration {
    /// Stable role-set name.
    pub name: String,
    /// Explicit members for this role-set.
    #[serde(default)]
    pub members: Vec<String>,
    /// Optional subset selector source role-set or family.
    #[serde(default)]
    pub subset_of: Option<String>,
    /// Optional subset selector start index (inclusive).
    #[serde(default)]
    pub subset_start: Option<u32>,
    /// Optional subset selector end index (exclusive).
    #[serde(default)]
    pub subset_end: Option<u32>,
}

/// Typed topology declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TopologyDeclaration {
    /// Topology kind (`cluster`, `ring`, `mesh`).
    pub kind: String,
    /// Topology name.
    pub name: String,
    /// Referenced members.
    #[serde(default)]
    pub members: Vec<String>,
}

/// DSL type declaration metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeDeclaration {
    /// Declared type name.
    pub name: String,
    /// Whether this is a `type alias`.
    pub is_alias: bool,
    /// Right-hand side for aliases.
    #[serde(default)]
    pub alias_of: Option<String>,
    /// Union constructors for nominal sum types.
    #[serde(default)]
    pub constructors: Vec<TypeConstructorDeclaration>,
}

/// Constructor declaration for one nominal union type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeConstructorDeclaration {
    /// Constructor name.
    pub name: String,
    /// Optional payload type rendered from source syntax.
    #[serde(default)]
    pub payload_type: Option<String>,
}

/// Nominal effect interface declaration metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectInterfaceDeclaration {
    /// Effect interface name.
    pub name: String,
    /// Declared operations for this interface.
    #[serde(default)]
    pub operations: Vec<EffectOperationDeclaration>,
}

/// Authority class for one nominal effect operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum EffectAuthorityClass {
    /// Operation may produce authoritative semantic evidence.
    Authoritative,
    /// Operation performs command work without itself proving semantic truth.
    #[default]
    Command,
    /// Operation is observational only and must not be consumed via `check`.
    Observe,
}

/// One operation in a nominal effect interface.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectOperationDeclaration {
    /// Operation name.
    pub name: String,
    /// Authority class attached to this operation.
    #[serde(default)]
    pub authority_class: EffectAuthorityClass,
    /// Semantic class declared for this operation.
    pub semantic_class: String,
    /// Progress class declared for this operation.
    pub progress: String,
    /// Region scope declared for this operation.
    pub region: String,
    /// Agreement-use discipline declared for this operation.
    pub agreement_use: String,
    /// Reentrancy policy declared for this operation.
    pub reentrancy: String,
    /// Input type as declared in DSL surface syntax.
    pub input_type: String,
    /// Output type as declared in DSL surface syntax.
    pub output_type: String,
}

/// Runtime-facing effect metadata derived from one nominal effect declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectContractDeclaration {
    /// Nominal effect interface name.
    pub interface_name: String,
    /// Nominal effect operation name.
    pub operation_name: String,
    /// Authority class attached to this operation.
    pub authority_class: EffectAuthorityClass,
    /// Semantic class attached to this operation.
    pub semantic_class: String,
    /// Progress class attached to this operation.
    pub progress: String,
    /// Region scope attached to this operation.
    pub region: String,
    /// Agreement-use discipline attached to this operation.
    pub agreement_use: String,
    /// Runtime admissibility policy name.
    pub admissibility: String,
    /// Runtime totality policy name.
    pub totality: String,
    /// Runtime timeout policy name.
    pub timeout_policy: String,
    /// Runtime reentrancy policy name.
    pub reentrancy_policy: String,
    /// Runtime handler-domain name.
    pub handler_domain: String,
}

/// Fragment declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegionDeclaration {
    /// Fragment name.
    pub name: String,
    /// Named fragment parameters.
    #[serde(default)]
    pub params: Vec<String>,
}

/// Operation parameter declaration metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationParameterDeclaration {
    /// Parameter name.
    pub name: String,
    /// Parameter type rendered from source syntax.
    pub type_name: String,
}

/// Structured progress-contract attachment metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgressAttachment {
    /// Stable progress-contract name.
    pub contract_name: String,
    /// Required execution/admission profile.
    #[serde(default)]
    pub requires_profile: Option<String>,
    /// Required escalation window class.
    #[serde(default)]
    pub within_window: Option<String>,
    /// Named timeout branch or escalation action.
    #[serde(default)]
    pub on_timeout: Option<String>,
    /// Named stall branch or escalation action.
    #[serde(default)]
    pub on_stall: Option<String>,
}

/// Named reusable agreement-profile declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgreementProfileDeclaration {
    /// Stable profile name.
    pub name: String,
    /// Visibility timing fixed by this profile.
    pub visibility: String,
    /// Agreement/decision rule name.
    pub rule: String,
    /// Minimum agreement level required for provisional usability.
    pub usable_at: String,
    /// Minimum agreement level required for finalization.
    pub finalized_at: String,
    /// Required evidence kind for this profile.
    pub evidence: String,
}

/// Operation-level attachment of one named agreement profile.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationAgreementAttachment {
    /// Referenced agreement-profile name.
    pub profile_name: String,
    /// Optional named prestate binding required by the operation.
    #[serde(default)]
    pub prestate: Option<String>,
}

/// Operation declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationDeclaration {
    /// Operation name.
    pub name: String,
    /// Operation parameters.
    #[serde(default)]
    pub params: Vec<OperationParameterDeclaration>,
    /// Semantic owner role.
    pub owner_role: String,
    /// Optional fragment scope rendered from source syntax.
    #[serde(default)]
    pub within: Option<String>,
    /// Required progress contract for parity-critical execution.
    #[serde(default)]
    pub progress_contract: Option<ProgressAttachment>,
    /// Named agreement/finality attachment for the operation.
    #[serde(default)]
    pub agreement: Option<OperationAgreementAttachment>,
    /// Declared child-effect aggregation for the operation.
    #[serde(default)]
    pub child_effect_aggregation: Option<ChildEffectAggregation>,
    /// Raw operation body source.
    pub body_source: String,
}

/// Canonical child-effect aggregation policy attached below one agreement boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChildEffectAggregationPolicy {
    /// All child effects must succeed.
    All,
    /// The first successful child effect resolves the aggregation.
    First,
    /// A fixed number of successful child effects is required.
    Threshold {
        /// Required success count.
        required_successes: u64,
    },
}

/// One declared child-effect aggregation attached to an operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChildEffectAggregation {
    /// Canonical aggregation policy.
    pub policy: ChildEffectAggregationPolicy,
}

impl ChildEffectAggregationPolicy {
    /// Canonical DSL spelling for this child-effect aggregation policy.
    #[must_use]
    pub fn dsl_name(&self) -> String {
        match self {
            Self::All => "all_success".to_string(),
            Self::First => "first_success".to_string(),
            Self::Threshold { required_successes } => {
                format!("threshold_success({required_successes})")
            }
        }
    }
}

impl ChildEffectAggregation {
    /// Canonical DSL spelling for this child-effect aggregation declaration.
    #[must_use]
    pub fn dsl_name(&self) -> String {
        self.policy.dsl_name()
    }
}

/// Guest-runtime declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuestRuntimeDeclaration {
    /// Guest-runtime name.
    pub name: String,
    /// Declared effect interface uses.
    #[serde(default)]
    pub uses: Vec<String>,
    /// Entry protocol name.
    pub entry: String,
}

/// Execution-profile declaration metadata from DSL.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExecutionProfileDeclaration {
    /// Stable profile name.
    pub name: String,
    /// Fairness class fixed by the profile.
    #[serde(default)]
    pub fairness: Option<String>,
    /// Admissibility class fixed by the profile.
    #[serde(default)]
    pub admissibility: Option<String>,
    /// Escalation-window class fixed by the profile.
    #[serde(default)]
    pub escalation_window: Option<String>,
}

/// Strongest artifact tier justified by the parsed specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LanguageTier {
    FullSpec,
    SessionProjectable,
    ProtocolMachineExecutable,
    ProofOnly,
}

/// Strongest theorem story currently justified for authority-bearing constructs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthorityMetatheoryTier {
    /// No authority-specific semantic obligations beyond ordinary session coordination.
    SessionTypedCoordination,
    /// The supported authority slice lives in the protocol-machine semantic-object layer:
    /// evidence-bearing reads plus canonical publication/materialization.
    EvidencePublicationSemanticObjects,
    /// The protocol uses authority/runtime features that currently remain outside the
    /// supported authority theorem slice.
    RuntimeSemanticOnly,
}

/// Explicit authority-metatheory status for one parsed specification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorityMetatheoryStatus {
    pub strongest_tier: AuthorityMetatheoryTier,
    pub diagnostic: String,
}

/// Explicit language-tier status for one parsed specification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LanguageTierStatus {
    pub strongest_tier: LanguageTier,
    pub session_projectable: bool,
    pub protocol_machine_executable: bool,
    pub theory_convertible: bool,
    pub proof_only: bool,
    pub diagnostic: String,
}

/// A complete choreographic protocol specification
#[derive(Debug)]
pub struct Choreography {
    /// Protocol name
    pub name: Ident,
    /// Optional namespace for the protocol
    pub namespace: Option<String>,
    /// Participating roles
    pub roles: Vec<Role>,
    /// The protocol specification
    pub protocol: Protocol,
    /// Metadata and attributes
    pub attrs: HashMap<String, String>,
}

impl Choreography {
    /// Get the qualified name of the choreography (namespace::name or just name)
    #[must_use]
    pub fn qualified_name(&self) -> String {
        match &self.namespace {
            Some(ns) => format!("{}::{}", ns, self.name),
            None => self.name.to_string(),
        }
    }

    /// Validate the choreography for correctness
    ///
    /// # Errors
    ///
    /// Returns [`ValidationError`] if the choreography is invalid (unused roles,
    /// malformed protocol, duplicate/missing proof bundles, or missing capabilities).
    pub fn validate(&self) -> Result<(), ValidationError> {
        // Check all roles are used
        for role in &self.roles {
            if !self.protocol.mentions_role(role) {
                return Err(ValidationError::UnusedRole(role.name().to_string()));
            }
        }

        // Check protocol is well-formed
        self.protocol.validate(&self.roles)?;
        self.validate_proof_bundles()?;
        self.validate_effect_surface()?;
        self.validate_execution_profile_surface()?;
        self.validate_operation_surface()?;

        Ok(())
    }

    fn validate_proof_bundles(&self) -> Result<(), ValidationError> {
        let bundles = self.theorem_packs();
        let mut declared: BTreeSet<String> = BTreeSet::new();
        for bundle in &bundles {
            if !declared.insert(bundle.name.clone()) {
                return Err(ValidationError::DuplicateProofBundle(bundle.name.clone()));
            }
        }

        for required in self.required_theorem_packs() {
            if !declared.contains(&required) {
                return Err(ValidationError::MissingProofBundle(required));
            }
        }

        let required_caps = self.required_theorem_pack_capabilities();
        for capability in self.required_protocol_machine_core_capabilities() {
            if !required_caps.contains(&capability) {
                return Err(ValidationError::MissingCapability(capability));
            }
        }

        Ok(())
    }

    fn validate_effect_surface(&self) -> Result<(), ValidationError> {
        let mut effect_names = BTreeSet::new();
        let mut effect_ops: HashMap<String, HashMap<String, EffectOperationDeclaration>> =
            HashMap::new();
        for effect in self.effect_interface_declarations() {
            if !effect_names.insert(effect.name.clone()) {
                return Err(ValidationError::ExtensionError(format!(
                    "duplicate effect interface declaration `{}`",
                    effect.name
                )));
            }
            let mut ops = HashMap::new();
            for op in effect.operations {
                let semantic_class_ok = matches!(
                    op.semantic_class.as_str(),
                    "authoritative" | "observational" | "best_effort"
                );
                if !semantic_class_ok {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` has unsupported `class {}`",
                        effect.name, op.name, op.semantic_class
                    )));
                }
                let progress_ok = matches!(op.progress.as_str(), "immediate" | "may_block");
                if !progress_ok {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` has unsupported `progress {}`",
                        effect.name, op.name, op.progress
                    )));
                }
                if !matches!(op.region.as_str(), "session" | "fragment" | "global") {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` has unsupported `region {}`",
                        effect.name, op.name, op.region
                    )));
                }
                if !matches!(op.agreement_use.as_str(), "required" | "none" | "forbidden") {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` has unsupported `agreement_use {}`",
                        effect.name, op.name, op.agreement_use
                    )));
                }
                if !matches!(
                    op.reentrancy.as_str(),
                    "allow" | "reject_same_operation" | "reject_same_fragment"
                ) {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` has unsupported `reentrancy {}`",
                        effect.name, op.name, op.reentrancy
                    )));
                }
                if matches!(op.authority_class, EffectAuthorityClass::Observe)
                    && op.semantic_class != "observational"
                {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` is observational and must declare `class : observational`",
                        effect.name, op.name
                    )));
                }
                if matches!(op.authority_class, EffectAuthorityClass::Authoritative)
                    && op.semantic_class != "authoritative"
                {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` is authoritative and must declare `class : authoritative`",
                        effect.name, op.name
                    )));
                }
                if op.progress == "immediate"
                    && matches!(op.authority_class, EffectAuthorityClass::Authoritative)
                {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` may not be both `authoritative` and `progress immediate`",
                        effect.name, op.name
                    )));
                }
                if op.agreement_use == "required"
                    && matches!(op.authority_class, EffectAuthorityClass::Observe)
                {
                    return Err(ValidationError::ExtensionError(format!(
                        "effect operation `{}.{}` may not require agreement use on an observational surface",
                        effect.name, op.name
                    )));
                }
                if ops.insert(op.name.clone(), op.clone()).is_some() {
                    return Err(ValidationError::ExtensionError(format!(
                        "duplicate effect operation `{}.{}`",
                        effect.name, op.name
                    )));
                }
            }
            effect_ops.insert(effect.name, ops);
        }

        let declared = effect_names;
        let used: BTreeSet<String> = self.protocol_uses().into_iter().collect();
        for effect in &used {
            if !declared.contains(effect) {
                return Err(ValidationError::ExtensionError(format!(
                    "protocol uses undeclared effect interface `{effect}`"
                )));
            }
        }

        fn validate_expr(
            expr: &super::AuthorityExpr,
            effect_ops: &HashMap<String, HashMap<String, EffectOperationDeclaration>>,
            used: &BTreeSet<String>,
        ) -> Result<(), ValidationError> {
            match expr {
                super::AuthorityExpr::Check {
                    effect, operation, ..
                } => {
                    if !used.contains(effect) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is not allowed without `uses {effect}`"
                        )));
                    }
                    let Some(ops) = effect_ops.get(effect) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared interface `{effect}`"
                        )));
                    };
                    let Some(op_decl) = ops.get(operation) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared operation `{effect}.{operation}`"
                        )));
                    };
                    if matches!(op_decl.authority_class, EffectAuthorityClass::Observe) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is observational and may not be invoked with `check`"
                        )));
                    }
                    Ok(())
                }
                super::AuthorityExpr::Observe {
                    effect, operation, ..
                } => {
                    if !used.contains(effect) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is not allowed without `uses {effect}`"
                        )));
                    }
                    let Some(ops) = effect_ops.get(effect) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared interface `{effect}`"
                        )));
                    };
                    let Some(op_decl) = ops.get(operation) else {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation references undeclared operation `{effect}.{operation}`"
                        )));
                    };
                    if !matches!(op_decl.authority_class, EffectAuthorityClass::Observe) {
                        return Err(ValidationError::ExtensionError(format!(
                            "effect invocation `{effect}.{operation}` is not observational and may not be invoked with `observe`"
                        )));
                    }
                    Ok(())
                }
                super::AuthorityExpr::Var(_)
                | super::AuthorityExpr::Transfer { .. }
                | super::AuthorityExpr::Constructor { .. }
                | super::AuthorityExpr::Call { .. } => Ok(()),
            }
        }

        fn validate_protocol_effects(
            protocol: &Protocol,
            effect_ops: &HashMap<String, HashMap<String, EffectOperationDeclaration>>,
            used: &BTreeSet<String>,
        ) -> Result<(), ValidationError> {
            match protocol {
                Protocol::Begin { continuation, .. }
                | Protocol::Await { continuation, .. }
                | Protocol::Resolve { continuation, .. }
                | Protocol::Invalidate { continuation, .. }
                | Protocol::Send { continuation, .. }
                | Protocol::Broadcast { continuation, .. }
                | Protocol::Extension { continuation, .. }
                | Protocol::Let { continuation, .. }
                | Protocol::Publish { continuation, .. }
                | Protocol::PublishAuthority { continuation, .. }
                | Protocol::Materialize { continuation, .. }
                | Protocol::Handoff { continuation, .. }
                | Protocol::DependentWork { continuation, .. } => {
                    if let Protocol::Let { mode, expr, .. } = protocol {
                        validate_expr(expr, effect_ops, used)?;
                        match (mode, expr) {
                            (
                                super::AuthorityBindingMode::Plain,
                                super::AuthorityExpr::Check {
                                    effect, operation, ..
                                },
                            ) => {
                                let op_decl = effect_ops
                                    .get(effect)
                                    .and_then(|ops| ops.get(operation))
                                    .expect("validated effect operation should exist");
                                if matches!(
                                    op_decl.authority_class,
                                    EffectAuthorityClass::Authoritative
                                ) {
                                    return Err(ValidationError::ExtensionError(format!(
                                        "authoritative effect invocation `{effect}.{operation}` must bind through `authoritative let`"
                                    )));
                                }
                            }
                            (
                                super::AuthorityBindingMode::Plain,
                                super::AuthorityExpr::Observe { .. },
                            ) => {
                                return Err(ValidationError::ExtensionError(
                                    "`observe` expressions must bind through `observe let`"
                                        .to_string(),
                                ));
                            }
                            (
                                super::AuthorityBindingMode::Authoritative,
                                super::AuthorityExpr::Check {
                                    effect, operation, ..
                                },
                            ) => {
                                let op_decl = effect_ops
                                    .get(effect)
                                    .and_then(|ops| ops.get(operation))
                                    .expect("validated effect operation should exist");
                                if !matches!(
                                    op_decl.authority_class,
                                    EffectAuthorityClass::Authoritative
                                ) {
                                    return Err(ValidationError::ExtensionError(format!(
                                        "`authoritative let` may only bind authoritative effect invocations; `{effect}.{operation}` is {:?}",
                                        op_decl.authority_class
                                    )));
                                }
                            }
                            (
                                super::AuthorityBindingMode::Observe,
                                super::AuthorityExpr::Observe { .. },
                            ) => {}
                            (super::AuthorityBindingMode::Plain, _) => {}
                            (super::AuthorityBindingMode::Authoritative, _) => {
                                return Err(ValidationError::ExtensionError(
                                    "`authoritative let` must bind a `check` expression"
                                        .to_string(),
                                ));
                            }
                            (super::AuthorityBindingMode::Observe, _) => {
                                return Err(ValidationError::ExtensionError(
                                    "`observe let` must bind an `observe` expression".to_string(),
                                ));
                            }
                        }
                    }
                    validate_protocol_effects(continuation, effect_ops, used)
                }
                Protocol::Choice { branches, .. } => {
                    for branch in branches {
                        if let Some(ChoiceGuard::Evidence {
                            effect, operation, ..
                        }) = &branch.guard
                        {
                            if !used.contains(effect) {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard `{effect}.{operation}` is not allowed without `uses {effect}`"
                                )));
                            }
                            let Some(ops) = effect_ops.get(effect) else {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard references undeclared interface `{effect}`"
                                )));
                            };
                            let Some(op_decl) = ops.get(operation) else {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard references undeclared operation `{effect}.{operation}`"
                                )));
                            };
                            if matches!(op_decl.authority_class, EffectAuthorityClass::Observe) {
                                return Err(ValidationError::ExtensionError(format!(
                                    "effect guard `{effect}.{operation}` is observational and may not be invoked with `check`"
                                )));
                            }
                        }
                        validate_protocol_effects(&branch.protocol, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Case { expr, branches } => {
                    validate_expr(expr, effect_ops, used)?;
                    for branch in branches {
                        validate_protocol_effects(&branch.protocol, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Timeout {
                    body,
                    on_timeout,
                    on_cancel,
                    ..
                } => {
                    validate_protocol_effects(body, effect_ops, used)?;
                    validate_protocol_effects(on_timeout, effect_ops, used)?;
                    if let Some(on_cancel) = on_cancel.as_deref() {
                        validate_protocol_effects(on_cancel, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
                    validate_protocol_effects(body, effect_ops, used)
                }
                Protocol::Parallel { protocols } => {
                    for protocol in protocols {
                        validate_protocol_effects(protocol, effect_ops, used)?;
                    }
                    Ok(())
                }
                Protocol::Var(_) | Protocol::End => Ok(()),
            }
        }

        validate_protocol_effects(&self.protocol, &effect_ops, &used)
    }

    fn validate_execution_profile_surface(&self) -> Result<(), ValidationError> {
        let mut declared = BTreeSet::new();
        for profile in self.execution_profile_declarations() {
            if !declared.insert(profile.name.clone()) {
                return Err(ValidationError::ExtensionError(format!(
                    "duplicate execution profile declaration `{}`",
                    profile.name
                )));
            }
        }

        for profile in self.protocol_execution_profiles() {
            if !declared.contains(&profile) {
                return Err(ValidationError::ExtensionError(format!(
                    "protocol references undeclared execution profile `{profile}`"
                )));
            }
        }

        Ok(())
    }

    fn validate_operation_surface(&self) -> Result<(), ValidationError> {
        let declared_agreement_profiles = self
            .agreement_profile_declarations()
            .into_iter()
            .map(|profile| profile.name)
            .collect::<BTreeSet<_>>();

        for operation in self.operation_declarations() {
            if operation.progress_contract.is_none() {
                return Err(ValidationError::ExtensionError(format!(
                    "operation `{}` is parity-critical and must declare a progress contract",
                    operation.name
                )));
            }
            if !operation
                .progress_contract
                .as_ref()
                .is_some_and(|progress| progress.is_explicit())
            {
                return Err(ValidationError::ExtensionError(format!(
                    "operation `{}` must declare explicit progress metadata using `requires`, `within`, `on timeout`, or `on stall`",
                    operation.name
                )));
            }
            let Some(agreement) = operation.agreement.as_ref() else {
                return Err(ValidationError::ExtensionError(format!(
                    "operation `{}` must attach a named agreement profile",
                    operation.name
                )));
            };
            if !declared_agreement_profiles.contains(&agreement.profile_name) {
                return Err(ValidationError::ExtensionError(format!(
                    "operation `{}` references undeclared agreement profile `{}`",
                    operation.name, agreement.profile_name
                )));
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn language_tier_status(&self) -> LanguageTierStatus {
        let theory_convertible = super::convert::protocol_to_global(&self.protocol).is_ok();
        let session_blocker = find_session_projection_blocker(&self.protocol);
        let missing_progress = self
            .operation_declarations()
            .iter()
            .find(|operation| {
                operation.progress_contract.is_none()
                    || !operation
                        .progress_contract
                        .as_ref()
                        .is_some_and(|progress| progress.is_explicit())
            })
            .map(|operation| {
                format!(
                    "operation `{}` is missing the required progress contract",
                    operation.name
                )
            });

        let protocol_machine_executable = missing_progress.is_none();
        let session_projectable = session_blocker.is_none();
        let strongest_tier = match (session_projectable, protocol_machine_executable) {
            (true, true) => LanguageTier::SessionProjectable,
            (false, true) => LanguageTier::ProtocolMachineExecutable,
            (_, false) => LanguageTier::ProofOnly,
        };
        let diagnostic = if let Some(blocker) = session_blocker {
            format!(
                "full spec is valid, protocol-machine execution is available, but session projection is blocked: {blocker}"
            )
        } else if let Some(missing_progress) = missing_progress {
            format!(
                "full spec is valid for proof analysis only; protocol-machine execution is blocked: {missing_progress}"
            )
        } else if !theory_convertible {
            "full spec is valid, protocol-machine execution is available, and the protocol is session-projectable, but theory conversion remains explicitly unavailable for this surface".to_string()
        } else {
            "full spec is valid, protocol-machine execution is available, the protocol is session-projectable, and theory conversion is available".to_string()
        };

        LanguageTierStatus {
            strongest_tier,
            session_projectable,
            protocol_machine_executable,
            theory_convertible,
            proof_only: matches!(strongest_tier, LanguageTier::ProofOnly),
            diagnostic,
        }
    }

    #[must_use]
    pub fn authority_metatheory_status(&self) -> AuthorityMetatheoryStatus {
        let strongest_tier = authority_metatheory_tier(&self.protocol);
        let diagnostic = match authority_metatheory_blocker(&self.protocol) {
            Some(blocker) => format!(
                "authority-bearing constructs remain executable, but the supported theorem slice stops before this runtime semantic surface: {blocker}"
            ),
            None => match strongest_tier {
                AuthorityMetatheoryTier::SessionTypedCoordination =>
                    "the protocol stays within ordinary session-typed coordination; no authority-specific semantic proof obligations are introduced".to_string(),
                AuthorityMetatheoryTier::EvidencePublicationSemanticObjects =>
                    "the protocol stays within the supported authority theorem slice: evidence-bearing reads and canonical publication/materialization are justified at the protocol-machine semantic-object layer, while session typing continues to cover only the coordination skeleton".to_string(),
                AuthorityMetatheoryTier::RuntimeSemanticOnly =>
                    "authority-bearing runtime semantics are present, but they currently sit outside the supported theorem slice".to_string(),
            },
        };

        AuthorityMetatheoryStatus {
            strongest_tier,
            diagnostic,
        }
    }

    /// Get choreography-level attributes/annotations
    #[must_use]
    pub fn get_attributes(&self) -> &HashMap<String, String> {
        &self.attrs
    }

    /// Get mutable reference to choreography-level attributes
    pub fn get_attributes_mut(&mut self) -> &mut HashMap<String, String> {
        &mut self.attrs
    }

    /// Get a specific choreography attribute
    #[must_use]
    pub fn get_attribute(&self, key: &str) -> Option<&String> {
        self.attrs.get(key)
    }

    /// Set a choreography attribute
    pub fn set_attribute(&mut self, key: String, value: String) {
        self.attrs.insert(key, value);
    }

    /// Remove a choreography attribute
    pub fn remove_attribute(&mut self, key: &str) -> Option<String> {
        self.attrs.remove(key)
    }

    /// Check if choreography has a specific attribute
    #[must_use]
    pub fn has_attribute(&self, key: &str) -> bool {
        self.attrs.contains_key(key)
    }

    /// Get attribute as a specific type
    pub fn get_attribute_as<T>(&self, key: &str) -> Option<T>
    where
        T: std::str::FromStr,
    {
        self.get_attribute(key)?.parse().ok()
    }

    /// Get attribute as boolean
    pub fn get_attribute_as_bool(&self, key: &str) -> Option<bool> {
        let value = self.get_attribute(key)?;
        match value.to_lowercase().as_str() {
            "true" | "1" | "yes" | "on" => Some(true),
            "false" | "0" | "no" | "off" => Some(false),
            _ => None,
        }
    }

    /// Clear all choreography attributes
    pub fn clear_attributes(&mut self) {
        self.attrs.clear();
    }

    /// Count of choreography attributes
    pub fn attribute_count(&self) -> usize {
        self.attrs.len()
    }

    /// Get all attribute keys
    pub fn attribute_keys(&self) -> Vec<&String> {
        self.attrs.keys().collect()
    }

    /// Validate that required attributes are present
    pub fn validate_required_attributes(&self, required_keys: &[&str]) -> Result<(), Vec<String>> {
        let missing: Vec<String> = required_keys
            .iter()
            .filter(|&key| !self.has_attribute(key))
            .map(|&key| key.to_string())
            .collect();

        if missing.is_empty() {
            Ok(())
        } else {
            Err(missing)
        }
    }

    /// Find all protocol nodes with a specific annotation
    pub fn find_nodes_with_annotation(&self, key: &str) -> Vec<&Protocol> {
        let mut nodes = Vec::new();
        self.protocol.collect_nodes_with_annotation(key, &mut nodes);
        nodes
    }

    /// Find all protocol nodes with a specific annotation value
    pub fn find_nodes_with_annotation_value(&self, key: &str, value: &str) -> Vec<&Protocol> {
        let mut nodes = Vec::new();
        self.protocol
            .collect_nodes_with_annotation_value(key, value, &mut nodes);
        nodes
    }

    /// Count total annotations across the entire choreography
    pub fn total_annotation_count(&self) -> usize {
        self.attribute_count() + self.protocol.deep_annotation_count()
    }

    /// Set theorem-pack declarations for this choreography.
    pub fn set_theorem_packs(
        &mut self,
        theorem_packs: &[TheoremPackDeclaration],
    ) -> Result<(), String> {
        let encoded = serde_json::to_string(theorem_packs)
            .map_err(|e| format!("encode theorem packs: {e}"))?;
        self.attrs.insert(ATTR_THEOREM_PACKS.to_string(), encoded);
        Ok(())
    }

    /// Get typed theorem-pack declarations.
    #[must_use]
    pub fn theorem_packs(&self) -> Vec<TheoremPackDeclaration> {
        self.attrs
            .get(ATTR_THEOREM_PACKS)
            .and_then(|s| serde_json::from_str::<Vec<TheoremPackDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set protocol-required theorem packs.
    pub fn set_required_theorem_packs(&mut self, required: &[String]) -> Result<(), String> {
        let encoded = serde_json::to_string(required)
            .map_err(|e| format!("encode required theorem packs: {e}"))?;
        self.attrs
            .insert(ATTR_REQUIRED_THEOREM_PACKS.to_string(), encoded);
        Ok(())
    }

    /// Get protocol-required theorem packs.
    #[must_use]
    pub fn required_theorem_packs(&self) -> Vec<String> {
        self.attrs
            .get(ATTR_REQUIRED_THEOREM_PACKS)
            .and_then(|s| serde_json::from_str::<Vec<String>>(s).ok())
            .unwrap_or_default()
    }

    /// Set inferred protocol-required theorem packs.
    pub fn set_inferred_required_theorem_packs(
        &mut self,
        required: &[String],
    ) -> Result<(), String> {
        let encoded = serde_json::to_string(required)
            .map_err(|e| format!("encode inferred theorem packs: {e}"))?;
        self.attrs
            .insert(ATTR_INFERRED_REQUIRED_THEOREM_PACKS.to_string(), encoded);
        Ok(())
    }

    /// Get inferred protocol-required theorem packs.
    #[must_use]
    pub fn inferred_required_theorem_packs(&self) -> Vec<String> {
        self.attrs
            .get(ATTR_INFERRED_REQUIRED_THEOREM_PACKS)
            .and_then(|s| serde_json::from_str::<Vec<String>>(s).ok())
            .unwrap_or_default()
    }

    /// Set role-set declarations for this choreography.
    pub fn set_role_sets(&mut self, role_sets: &[RoleSetDeclaration]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(role_sets).map_err(|e| format!("encode role sets: {e}"))?;
        self.attrs.insert(ATTR_ROLE_SETS.to_string(), encoded);
        Ok(())
    }

    /// Get typed role-set declarations.
    #[must_use]
    pub fn role_sets(&self) -> Vec<RoleSetDeclaration> {
        self.attrs
            .get(ATTR_ROLE_SETS)
            .and_then(|s| serde_json::from_str::<Vec<RoleSetDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set topology declarations for this choreography.
    pub fn set_topologies(&mut self, topologies: &[TopologyDeclaration]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(topologies).map_err(|e| format!("encode topologies: {e}"))?;
        self.attrs.insert(ATTR_TOPOLOGIES.to_string(), encoded);
        Ok(())
    }

    /// Get typed topology declarations.
    #[must_use]
    pub fn topologies(&self) -> Vec<TopologyDeclaration> {
        self.attrs
            .get(ATTR_TOPOLOGIES)
            .and_then(|s| serde_json::from_str::<Vec<TopologyDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set nominal type declarations for this choreography.
    pub fn set_type_declarations(&mut self, decls: &[TypeDeclaration]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(decls).map_err(|e| format!("encode type declarations: {e}"))?;
        self.attrs
            .insert(ATTR_TYPE_DECLARATIONS.to_string(), encoded);
        Ok(())
    }

    /// Get nominal type declarations.
    #[must_use]
    pub fn type_declarations(&self) -> Vec<TypeDeclaration> {
        self.attrs
            .get(ATTR_TYPE_DECLARATIONS)
            .and_then(|s| serde_json::from_str::<Vec<TypeDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set nominal effect interface declarations for this choreography.
    pub fn set_effect_interface_declarations(
        &mut self,
        decls: &[EffectInterfaceDeclaration],
    ) -> Result<(), String> {
        let encoded =
            serde_json::to_string(decls).map_err(|e| format!("encode effect declarations: {e}"))?;
        self.attrs
            .insert(ATTR_EFFECT_INTERFACE_DECLARATIONS.to_string(), encoded);
        Ok(())
    }

    /// Get nominal effect interface declarations.
    #[must_use]
    pub fn effect_interface_declarations(&self) -> Vec<EffectInterfaceDeclaration> {
        self.attrs
            .get(ATTR_EFFECT_INTERFACE_DECLARATIONS)
            .and_then(|s| serde_json::from_str::<Vec<EffectInterfaceDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Derive runtime-facing effect metadata from nominal effect declarations
    /// and protocol `uses` dependencies.
    #[must_use]
    pub fn effect_contract_declarations(&self) -> Vec<EffectContractDeclaration> {
        let used: BTreeSet<String> = self.protocol_uses().into_iter().collect();
        self.effect_interface_declarations()
            .into_iter()
            .flat_map(|effect| {
                let is_used = used.contains(effect.name.as_str());
                effect.operations.into_iter().map(move |op| {
                    let admissibility = if is_used {
                        "declared_use_only"
                    } else {
                        "internal_only"
                    };
                    let (totality, timeout_policy) = match op.progress.as_str() {
                        "immediate" => ("immediate", "none"),
                        "may_block" => ("may_block", "required"),
                        _ => ("may_block", "required"),
                    };
                    let handler_domain = if is_used { "external" } else { "internal" };
                    EffectContractDeclaration {
                        interface_name: effect.name.clone(),
                        operation_name: op.name,
                        authority_class: op.authority_class,
                        semantic_class: op.semantic_class.clone(),
                        progress: op.progress.clone(),
                        region: op.region.clone(),
                        agreement_use: op.agreement_use.clone(),
                        admissibility: admissibility.to_string(),
                        totality: totality.to_string(),
                        timeout_policy: timeout_policy.to_string(),
                        reentrancy_policy: op.reentrancy,
                        handler_domain: handler_domain.to_string(),
                    }
                })
            })
            .collect()
    }

    /// Set explicit protocol effect dependencies.
    pub fn set_protocol_uses(&mut self, uses: &[String]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(uses).map_err(|e| format!("encode protocol uses: {e}"))?;
        self.attrs.insert(ATTR_PROTOCOL_USES.to_string(), encoded);
        Ok(())
    }

    /// Get explicit protocol effect dependencies.
    #[must_use]
    pub fn protocol_uses(&self) -> Vec<String> {
        self.attrs
            .get(ATTR_PROTOCOL_USES)
            .and_then(|s| serde_json::from_str::<Vec<String>>(s).ok())
            .unwrap_or_default()
    }

    /// Set region declarations for this choreography.
    pub fn set_region_declarations(&mut self, decls: &[RegionDeclaration]) -> Result<(), String> {
        let encoded =
            serde_json::to_string(decls).map_err(|e| format!("encode region declarations: {e}"))?;
        self.attrs
            .insert(ATTR_REGION_DECLARATIONS.to_string(), encoded);
        Ok(())
    }

    /// Get region declarations.
    #[must_use]
    pub fn region_declarations(&self) -> Vec<RegionDeclaration> {
        self.attrs
            .get(ATTR_REGION_DECLARATIONS)
            .and_then(|s| serde_json::from_str::<Vec<RegionDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set operation declarations for this choreography.
    pub fn set_operation_declarations(
        &mut self,
        decls: &[OperationDeclaration],
    ) -> Result<(), String> {
        let encoded = serde_json::to_string(decls)
            .map_err(|e| format!("encode operation declarations: {e}"))?;
        self.attrs
            .insert(ATTR_OPERATION_DECLARATIONS.to_string(), encoded);
        Ok(())
    }

    /// Get operation declarations.
    #[must_use]
    pub fn operation_declarations(&self) -> Vec<OperationDeclaration> {
        self.attrs
            .get(ATTR_OPERATION_DECLARATIONS)
            .and_then(|s| serde_json::from_str::<Vec<OperationDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set guest-runtime declarations for this choreography.
    pub fn set_guest_runtime_declarations(
        &mut self,
        decls: &[GuestRuntimeDeclaration],
    ) -> Result<(), String> {
        let encoded = serde_json::to_string(decls)
            .map_err(|e| format!("encode guest runtime declarations: {e}"))?;
        self.attrs
            .insert(ATTR_GUEST_RUNTIME_DECLARATIONS.to_string(), encoded);
        Ok(())
    }

    /// Get guest-runtime declarations.
    #[must_use]
    pub fn guest_runtime_declarations(&self) -> Vec<GuestRuntimeDeclaration> {
        self.attrs
            .get(ATTR_GUEST_RUNTIME_DECLARATIONS)
            .and_then(|s| serde_json::from_str::<Vec<GuestRuntimeDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set execution-profile declarations for this choreography.
    pub fn set_execution_profile_declarations(
        &mut self,
        decls: &[ExecutionProfileDeclaration],
    ) -> Result<(), String> {
        let encoded = serde_json::to_string(decls)
            .map_err(|e| format!("encode execution profile declarations: {e}"))?;
        self.attrs
            .insert(ATTR_EXECUTION_PROFILE_DECLARATIONS.to_string(), encoded);
        Ok(())
    }

    /// Get execution-profile declarations.
    #[must_use]
    pub fn execution_profile_declarations(&self) -> Vec<ExecutionProfileDeclaration> {
        self.attrs
            .get(ATTR_EXECUTION_PROFILE_DECLARATIONS)
            .and_then(|s| serde_json::from_str::<Vec<ExecutionProfileDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    /// Set protocol-selected execution profiles.
    pub fn set_protocol_execution_profiles(&mut self, profiles: &[String]) -> Result<(), String> {
        let encoded = serde_json::to_string(profiles)
            .map_err(|e| format!("encode protocol execution profiles: {e}"))?;
        self.attrs
            .insert(ATTR_PROTOCOL_EXECUTION_PROFILES.to_string(), encoded);
        Ok(())
    }

    /// Get protocol-selected execution profiles.
    #[must_use]
    pub fn protocol_execution_profiles(&self) -> Vec<String> {
        self.attrs
            .get(ATTR_PROTOCOL_EXECUTION_PROFILES)
            .and_then(|s| serde_json::from_str::<Vec<String>>(s).ok())
            .unwrap_or_default()
    }

    /// Set reusable agreement-profile declarations for this choreography.
    pub fn set_agreement_profile_declarations(
        &mut self,
        decls: &[AgreementProfileDeclaration],
    ) -> Result<(), String> {
        let encoded = serde_json::to_string(decls)
            .map_err(|e| format!("encode agreement profile declarations: {e}"))?;
        self.attrs
            .insert(ATTR_AGREEMENT_PROFILE_DECLARATIONS.to_string(), encoded);
        Ok(())
    }

    /// Get reusable agreement-profile declarations.
    #[must_use]
    pub fn agreement_profile_declarations(&self) -> Vec<AgreementProfileDeclaration> {
        self.attrs
            .get(ATTR_AGREEMENT_PROFILE_DECLARATIONS)
            .and_then(|s| serde_json::from_str::<Vec<AgreementProfileDeclaration>>(s).ok())
            .unwrap_or_default()
    }

    fn required_theorem_pack_capabilities(&self) -> BTreeSet<String> {
        let required = self.required_theorem_packs();
        let required_set: BTreeSet<&str> = required.iter().map(String::as_str).collect();
        self.theorem_packs()
            .into_iter()
            .filter(|bundle| required_set.contains(bundle.name.as_str()))
            .flat_map(|bundle| bundle.capabilities.into_iter())
            .collect()
    }

    fn required_protocol_machine_core_capabilities(&self) -> BTreeSet<String> {
        fn collect(protocol: &Protocol, out: &mut BTreeSet<String>) {
            if let Some(cap) = protocol.get_annotations().custom("required_capability") {
                out.insert(cap.to_string());
            }
            match protocol {
                Protocol::Begin { continuation, .. }
                | Protocol::Await { continuation, .. }
                | Protocol::Resolve { continuation, .. }
                | Protocol::Invalidate { continuation, .. }
                | Protocol::Send { continuation, .. }
                | Protocol::Broadcast { continuation, .. }
                | Protocol::Extension { continuation, .. }
                | Protocol::Publish { continuation, .. }
                | Protocol::PublishAuthority { continuation, .. }
                | Protocol::Materialize { continuation, .. }
                | Protocol::Handoff { continuation, .. }
                | Protocol::DependentWork { continuation, .. } => collect(continuation, out),
                Protocol::Choice { branches, .. } => {
                    for branch in branches {
                        collect(&branch.protocol, out);
                    }
                }
                Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => collect(body, out),
                Protocol::Let { continuation, .. } => collect(continuation, out),
                Protocol::Case { branches, .. } => {
                    for branch in branches {
                        collect(&branch.protocol, out);
                    }
                }
                Protocol::Timeout {
                    body,
                    on_timeout,
                    on_cancel,
                    ..
                } => {
                    collect(body, out);
                    collect(on_timeout, out);
                    if let Some(on_cancel) = on_cancel.as_deref() {
                        collect(on_cancel, out);
                    }
                }
                Protocol::Parallel { protocols } => {
                    for p in protocols {
                        collect(p, out);
                    }
                }
                Protocol::Var(_) | Protocol::End => {}
            }
        }

        let mut out = BTreeSet::new();
        collect(&self.protocol, &mut out);
        out
    }
}

impl ProgressAttachment {
    /// Whether this attachment carries explicit progress policy rather than a bare name.
    #[must_use]
    pub fn is_explicit(&self) -> bool {
        self.requires_profile.is_some()
            || self.within_window.is_some()
            || self.on_timeout.is_some()
            || self.on_stall.is_some()
    }
}

fn find_session_projection_blocker(protocol: &Protocol) -> Option<&'static str> {
    match protocol {
        Protocol::Begin { .. } => Some("begin requires protocol-machine commitment semantics"),
        Protocol::Await { .. } => Some("await requires protocol-machine commitment semantics"),
        Protocol::Resolve { .. } => Some("resolve requires protocol-machine commitment semantics"),
        Protocol::Invalidate { .. } => {
            Some("invalidate requires protocol-machine commitment semantics")
        }
        Protocol::Send { continuation, .. }
        | Protocol::Broadcast { continuation, .. }
        | Protocol::Let { continuation, .. }
        | Protocol::Publish { continuation, .. }
        | Protocol::PublishAuthority { continuation, .. }
        | Protocol::Materialize { continuation, .. }
        | Protocol::Handoff { continuation, .. }
        | Protocol::DependentWork { continuation, .. }
        | Protocol::Extension { continuation, .. } => find_session_projection_blocker(continuation),
        Protocol::Case { branches, .. } => branches
            .iter()
            .find_map(|branch| find_session_projection_blocker(&branch.protocol)),
        Protocol::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => find_session_projection_blocker(body)
            .or_else(|| find_session_projection_blocker(on_timeout))
            .or_else(|| {
                on_cancel
                    .as_deref()
                    .and_then(find_session_projection_blocker)
            }),
        Protocol::Choice { branches, .. } => branches
            .iter()
            .find_map(|branch| find_session_projection_blocker(&branch.protocol)),
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
            find_session_projection_blocker(body)
        }
        Protocol::Parallel { protocols } => {
            protocols.iter().find_map(find_session_projection_blocker)
        }
        Protocol::Var(_) | Protocol::End => None,
    }
}

fn authority_metatheory_tier(protocol: &Protocol) -> AuthorityMetatheoryTier {
    match protocol {
        Protocol::Begin { .. }
        | Protocol::Await { .. }
        | Protocol::Resolve { .. }
        | Protocol::Invalidate { .. }
        | Protocol::Case { .. }
        | Protocol::Timeout { .. }
        | Protocol::Handoff { .. }
        | Protocol::DependentWork { .. }
        | Protocol::Parallel { .. }
        | Protocol::Extension { .. } => AuthorityMetatheoryTier::RuntimeSemanticOnly,
        Protocol::Publish { continuation, .. }
        | Protocol::PublishAuthority { continuation, .. }
        | Protocol::Materialize { continuation, .. } => authority_metatheory_tier(continuation)
            .max(AuthorityMetatheoryTier::EvidencePublicationSemanticObjects),
        Protocol::Let {
            expr, continuation, ..
        } => {
            let expr_tier = match expr {
                super::AuthorityExpr::Check { .. } | super::AuthorityExpr::Observe { .. } => {
                    AuthorityMetatheoryTier::EvidencePublicationSemanticObjects
                }
                super::AuthorityExpr::Transfer { .. } => {
                    AuthorityMetatheoryTier::RuntimeSemanticOnly
                }
                super::AuthorityExpr::Var(_)
                | super::AuthorityExpr::Constructor { .. }
                | super::AuthorityExpr::Call { .. } => {
                    AuthorityMetatheoryTier::SessionTypedCoordination
                }
            };
            expr_tier.max(authority_metatheory_tier(continuation))
        }
        Protocol::Choice { branches, .. } => branches
            .iter()
            .map(|branch| {
                let guard_tier = match branch.guard.as_ref() {
                    Some(ChoiceGuard::Evidence { .. }) => {
                        AuthorityMetatheoryTier::EvidencePublicationSemanticObjects
                    }
                    Some(ChoiceGuard::Predicate(_)) | None => {
                        AuthorityMetatheoryTier::SessionTypedCoordination
                    }
                };
                guard_tier.max(authority_metatheory_tier(&branch.protocol))
            })
            .max()
            .unwrap_or(AuthorityMetatheoryTier::SessionTypedCoordination),
        Protocol::Send { continuation, .. } | Protocol::Broadcast { continuation, .. } => {
            authority_metatheory_tier(continuation)
        }
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => authority_metatheory_tier(body),
        Protocol::Var(_) | Protocol::End => AuthorityMetatheoryTier::SessionTypedCoordination,
    }
}

fn authority_metatheory_blocker(protocol: &Protocol) -> Option<&'static str> {
    match protocol {
        Protocol::Begin { .. }
        | Protocol::Await { .. }
        | Protocol::Resolve { .. }
        | Protocol::Invalidate { .. } => {
            Some("explicit commitment lifecycle still relies on protocol-machine semantic obligations")
        }
        Protocol::Case { .. } => Some("authority-local case/of still relies on runtime semantic obligations"),
        Protocol::Timeout { .. } => Some("timeout/cancellation still relies on runtime progress semantics"),
        Protocol::Handoff { .. } => Some("semantic handoff is still justified through protocol-machine conservation rather than the small authority theorem slice"),
        Protocol::DependentWork { .. } => Some("dependent work remains a protocol-machine semantic obligation"),
        Protocol::Parallel { .. } => Some("parallel authority composition remains outside the supported authority theorem slice"),
        Protocol::Extension { .. } => Some("extension dispatch remains outside the authority theorem slice"),
        Protocol::Let { expr, continuation, .. } => match expr {
            super::AuthorityExpr::Transfer { .. } => {
                Some(
                    "transfer receipts are first-class transition artifacts but still rely on the wider runtime authority lifecycle",
                )
            }
            _ => authority_metatheory_blocker(continuation),
        },
        Protocol::Choice { branches, .. } => branches
            .iter()
            .find_map(|branch| authority_metatheory_blocker(&branch.protocol)),
        Protocol::Send { continuation, .. }
        | Protocol::Broadcast { continuation, .. }
        | Protocol::Publish { continuation, .. }
        | Protocol::PublishAuthority { continuation, .. }
        | Protocol::Materialize { continuation, .. } => authority_metatheory_blocker(continuation),
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => authority_metatheory_blocker(body),
        Protocol::Var(_) | Protocol::End => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::format_ident;

    #[test]
    fn proof_bundle_metadata_roundtrip() {
        let mut choreo = Choreography {
            name: format_ident!("RoundTrip"),
            namespace: None,
            roles: Vec::new(),
            protocol: Protocol::End,
            attrs: HashMap::new(),
        };
        let bundles = vec![
            TheoremPackDeclaration {
                name: "Base".to_string(),
                capabilities: vec!["delegation".to_string()],
                version: None,
                issuer: None,
                constraints: Vec::new(),
            },
            TheoremPackDeclaration {
                name: "Guard".to_string(),
                capabilities: vec!["guard_tokens".to_string()],
                version: None,
                issuer: None,
                constraints: Vec::new(),
            },
        ];
        let required = vec!["Base".to_string()];

        choreo
            .set_theorem_packs(&bundles)
            .expect("set proof bundles");
        choreo
            .set_required_theorem_packs(&required)
            .expect("set required bundles");

        assert_eq!(choreo.theorem_packs(), bundles);
        assert_eq!(choreo.required_theorem_packs(), required);
    }
}
