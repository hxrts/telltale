import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.EffectAlgebra

Executable effect-algebra vocabulary for effect classification, immediate-effect
discipline, and lower-level sibling effect aggregation.

This module is intentionally secondary to the agreement/finality model in
`SemanticObjects.AgreementCore`: composition policies describe how already-
declared child effects combine, not the top-level agreement semantics of one
operation.
-/

namespace Runtime.ProtocolMachine.Model

def EffectInterfaceMetadata.isAuthoritative (metadata : EffectInterfaceMetadata) : Prop :=
  metadata.authorityClass = .authoritative

def EffectInterfaceMetadata.isCommand (metadata : EffectInterfaceMetadata) : Prop :=
  metadata.authorityClass = .command

def EffectInterfaceMetadata.isObserve (metadata : EffectInterfaceMetadata) : Prop :=
  metadata.authorityClass = .observe

def EffectInterfaceMetadata.isImmediate (metadata : EffectInterfaceMetadata) : Prop :=
  metadata.totality = .mustTerminate ∧
  metadata.timeoutPolicy = .none ∧
  metadata.retryShape = .forbidden

def EffectInterfaceMetadata.immediateAdmissible (metadata : EffectInterfaceMetadata) : Prop :=
  metadata.architecturallyLegal ∧
  metadata.isImmediate ∧
  metadata.authorityClass ≠ .authoritative

inductive EffectCompositionPolicy where
  | allSuccess
  | firstSuccess
  | quorum (requiredSuccesses : Nat)
  | fallback
  deriving Repr, DecidableEq

def EffectOutcomeStatus.isSuccess : EffectOutcomeStatus → Prop
  | .success => True
  | .blocked | .failure _ _ => False

def EffectOutcomeStatus.isTerminal : EffectOutcomeStatus → Prop
  | .blocked => False
  | .success | .failure _ _ => True

def EffectExchangeRecord.succeeded (record : EffectExchangeRecord) : Prop :=
  record.outcome.status.isSuccess

def EffectExchangeRecord.terminal (record : EffectExchangeRecord) : Prop :=
  record.outcome.status.isTerminal

def EffectOutcomeStatus.isSuccessB : EffectOutcomeStatus → Bool
  | .success => true
  | .blocked | .failure _ _ => false

def EffectOutcomeStatus.isTerminalB : EffectOutcomeStatus → Bool
  | .blocked => false
  | .success | .failure _ _ => true

def countSuccessfulEffects (records : List EffectExchangeRecord) : Nat :=
  records.foldl
    (fun acc record =>
      if record.outcome.status.isSuccessB then acc + 1 else acc)
    0

def countTerminalEffects (records : List EffectExchangeRecord) : Nat :=
  records.foldl
    (fun acc record =>
      if record.outcome.status.isTerminalB then acc + 1 else acc)
    0

def EffectCompositionPolicy.commitmentResolved
    (policy : EffectCompositionPolicy)
    (records : List EffectExchangeRecord) : Prop :=
  match policy with
  | .allSuccess =>
      records ≠ [] ∧ ∀ record ∈ records, record.succeeded
  | .firstSuccess =>
      ∃ record ∈ records, record.succeeded
  | .quorum requiredSuccesses =>
      requiredSuccesses > 0 ∧ countSuccessfulEffects records ≥ requiredSuccesses
  | .fallback =>
      (∃ record ∈ records, record.succeeded) ∨
      (records ≠ [] ∧ ∀ record ∈ records, record.terminal)

def EffectCompositionPolicy.commitmentCompatible
    (policy : EffectCompositionPolicy)
    (records : List EffectExchangeRecord) : Prop :=
  policy.commitmentResolved records →
    match policy with
    | .allSuccess =>
        ∀ record ∈ records, record.succeeded
    | .firstSuccess =>
        ∃ record ∈ records, record.succeeded
    | .quorum requiredSuccesses =>
        countSuccessfulEffects records ≥ requiredSuccesses
    | .fallback =>
        (∃ record ∈ records, record.succeeded) ∨
        (records ≠ [] ∧ ∀ record ∈ records, record.terminal)

def EffectCompositionPolicy.progressCompatible
    (policy : EffectCompositionPolicy)
    (records : List EffectExchangeRecord)
    (contract : ProgressContract) : Prop :=
  policy.commitmentResolved records →
    contract.isTerminal ∨
      ∃ next, contract.syntheticStep = some next ∧ next.progressMeasure < contract.progressMeasure

end Runtime.ProtocolMachine.Model
