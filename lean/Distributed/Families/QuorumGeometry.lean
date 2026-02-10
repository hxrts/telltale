set_option autoImplicit false

/-! # Distributed.Families.QuorumGeometry

Reusable quorum-geometry assumptions and safety theorems:
- no conflicting commits,
- fork exclusion,
- safe finality.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace QuorumGeometry

universe u v w x

/-- Minimal model interface for quorum-geometry reasoning. -/
structure Model (State : Type u) (Decision : Type v) (Certificate : Type w) (Party : Type x) where
  certified : State → Decision → Certificate → Prop
  signer : Certificate → Party → Prop
  conflicts : Decision → Decision → Prop

/-- A decision is committed at state `s` if it has a certificate at `s`. -/
def Committed
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party)
    (s : State) (d : Decision) : Prop :=
  ∃ c, M.certified s d c

/-- Finalized decisions are committed decisions in this abstraction. -/
def Finalized
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party)
    (s : State) (d : Decision) : Prop :=
  Committed M s d

/-- Fork predicate: two conflicting committed decisions coexist at one state. -/
def Forked
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party)
    (s : State) : Prop :=
  ∃ d₁ d₂, Committed M s d₁ ∧ Committed M s d₂ ∧ M.conflicts d₁ d₂

/-- Reusable quorum-geometry assumption bundle. -/
structure Assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party) : Prop where
  quorumIntersection :
    ∀ {s d₁ d₂ c₁ c₂},
      M.certified s d₁ c₁ →
      M.certified s d₂ c₂ →
      ∃ p, M.signer c₁ p ∧ M.signer c₂ p
  certificateMonotonicity :
    ∀ {s d c₁ c₂},
      M.certified s d c₁ →
      (∀ p, M.signer c₁ p → M.signer c₂ p) →
      M.certified s d c₂
  lockMonotonicity :
    ∀ {s d₁ d₂ c₁ c₂ p},
      M.certified s d₁ c₁ →
      M.certified s d₂ c₂ →
      M.signer c₁ p →
      M.signer c₂ p →
      ¬ M.conflicts d₁ d₂

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | quorumIntersection
  | certificateMonotonicity
  | lockMonotonicity
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable quorum-geometry assumption set. -/
def coreAssumptions : List Assumption :=
  [ .quorumIntersection
  , .certificateMonotonicity
  , .lockMonotonicity
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .quorumIntersection =>
      { assumption := h
      , passed := true
      , detail := "Quorum intersection assumption is provided."
      }
  | .certificateMonotonicity =>
      { assumption := h
      , passed := true
      , detail := "Certificate monotonicity assumption is provided."
      }
  | .lockMonotonicity =>
      { assumption := h
      , passed := true
      , detail := "Lock monotonicity assumption is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for assumption validation. -/
def runAssumptionValidation
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-- No conflicting commits follow from quorum intersection and lock monotonicity. -/
theorem no_conflicting_commits_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M)
    {s : State} {d₁ d₂ : Decision}
    (hCommitted₁ : Committed M s d₁)
    (hCommitted₂ : Committed M s d₂) :
    ¬ M.conflicts d₁ d₂ := by
  rcases hCommitted₁ with ⟨c₁, hCert₁⟩
  rcases hCommitted₂ with ⟨c₂, hCert₂⟩
  rcases a.quorumIntersection hCert₁ hCert₂ with ⟨p, hSign₁, hSign₂⟩
  exact a.lockMonotonicity hCert₁ hCert₂ hSign₁ hSign₂

/-- Fork exclusion follows from no-conflicting-commits. -/
theorem fork_exclusion_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M)
    (s : State) :
    ¬ Forked M s := by
  intro hFork
  rcases hFork with ⟨d₁, d₂, hCommitted₁, hCommitted₂, hConflicts⟩
  exact (no_conflicting_commits_of_assumptions a hCommitted₁ hCommitted₂) hConflicts

/-- Safe-finality corollary: finalized decisions cannot conflict with committed ones. -/
theorem safe_finality_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M)
    {s : State} {d : Decision}
    (hFinalized : Finalized M s d) :
    ∀ d', Committed M s d' → ¬ M.conflicts d d' := by
  intro d' hCommitted
  exact no_conflicting_commits_of_assumptions a hFinalized hCommitted

/-- Convenience theorem exposing certificate monotonicity for reuse. -/
theorem certificate_monotone_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M)
    {s : State} {d : Decision} {c₁ c₂ : Certificate}
    (hCert : M.certified s d c₁)
    (hSigners : ∀ p, M.signer c₁ p → M.signer c₂ p) :
    M.certified s d c₂ :=
  a.certificateMonotonicity hCert hSigners

end QuorumGeometry
end Distributed


set_option autoImplicit false

/-! # Distributed.Families.QuorumGeometry.API

High-level API for automatic quorum-geometry safety certification.
-/

namespace Distributed
namespace QuorumGeometry

universe u v w x

/-- Certified protocol package for quorum-geometry safety properties. -/
structure SafetyProtocol where
  State : Type u
  Decision : Type v
  Certificate : Type w
  Party : Type x
  model : Model State Decision Certificate Party
  assumptions : Assumptions model
  noConflictingCommits :
    ∀ {s d₁ d₂},
      Committed model s d₁ →
      Committed model s d₂ →
      ¬ model.conflicts d₁ d₂ := by
        intro s d₁ d₂ hCommitted₁ hCommitted₂
        exact no_conflicting_commits_of_assumptions assumptions hCommitted₁ hCommitted₂
  forkExclusion :
    ∀ s, ¬ Forked model s := by
      intro s
      exact fork_exclusion_of_assumptions assumptions s
  safeFinality :
    ∀ {s d},
      Finalized model s d →
      ∀ d', Committed model s d' → ¬ model.conflicts d d' := by
        intro s d hFinalized d' hCommitted
        exact safe_finality_of_assumptions assumptions hFinalized d' hCommitted

/-- Extract no-conflicting-commits theorem from a certified protocol bundle. -/
theorem noConflictingCommits_of_protocol (P : SafetyProtocol) :
    ∀ {s d₁ d₂},
      Committed P.model s d₁ →
      Committed P.model s d₂ →
      ¬ P.model.conflicts d₁ d₂ :=
  P.noConflictingCommits

/-- Extract fork-exclusion theorem from a certified protocol bundle. -/
theorem forkExclusion_of_protocol (P : SafetyProtocol) :
    ∀ s, ¬ Forked P.model s :=
  P.forkExclusion

/-- Extract safe-finality theorem from a certified protocol bundle. -/
theorem safeFinality_of_protocol (P : SafetyProtocol) :
    ∀ {s d},
      Finalized P.model s d →
      ∀ d', Committed P.model s d' → ¬ P.model.conflicts d d' :=
  P.safeFinality

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : SafetyProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end QuorumGeometry
end Distributed
