import Distributed.Families.Nakamoto.LongestChain

set_option autoImplicit false

/-! # Distributed.Families.Nakamoto

Reusable Nakamoto-style assumptions and theorem forms:
- probabilistic safety,
- settlement-depth finality,
- liveness under admissible churn.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace Nakamoto

universe u v w

/-- Minimal model interface for Nakamoto-style reasoning. -/
structure Model (State : Type u) (Block : Type v) (Party : Type w) where
  initial : State → Prop
  chain : State → List Block
  honestWeight : List Block → Nat
  failureProbabilityAtDepth : Nat → Rat
  adversarialPowerBounded : Prop
  churnWithin : (Nat → State) → Nat → Prop

/-! ## Chain Trace Semantics -/

/-- `xs` is a prefix of `ys`. -/
def PrefixOf {Block : Type v} (xs ys : List Block) : Prop :=
  ∃ suffix, ys = xs ++ suffix

/-- Common-prefix property at settlement depth `k`. -/
def CommonPrefixAtDepth
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party) (run : Nat → State) (k : Nat) : Prop :=
  ∀ i j pref,
    i ≤ j →
    PrefixOf pref (M.chain (run i)) →
    pref.length + k ≤ (M.chain (run i)).length →
    PrefixOf pref (M.chain (run j))

/-- Chain growth over a fixed window and minimum growth amount. -/
def ChainGrowth
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party) (run : Nat → State)
    (window minGrowth : Nat) : Prop :=
  ∀ i, (M.chain (run i)).length + minGrowth ≤
    (M.chain (run (i + window))).length

/-- Chain quality: enough honest weight is present in each sampled growth window. -/
def ChainQuality
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party) (run : Nat → State)
    (window minHonestWeight : Nat) : Prop :=
  ∀ i, minHonestWeight ≤ M.honestWeight (M.chain (run (i + window)))

/-! ## Probability Boundary -/

/-- Explicit probabilistic boundary consumed by the Nakamoto theorem family. -/
def ProbabilityBudget
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party) (k : Nat) (ε : Rat) : Prop :=
  M.adversarialPowerBounded ∧ M.failureProbabilityAtDepth k ≤ ε

/-- Probabilistic safety predicate at error level `ε`. -/
def ProbabilisticSafety
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party)
    (AdmissibleRun : (Nat → State) → Prop)
    (ε : Rat) : Prop :=
  ∀ run, AdmissibleRun run →
    ∃ k, ProbabilityBudget M k ε ∧ CommonPrefixAtDepth M run k

/-- Settlement-depth finality predicate at depth `k`. -/
def SettlementDepthFinality
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party)
    (AdmissibleRun : (Nat → State) → Prop)
    (k : Nat) : Prop :=
  ∀ run, AdmissibleRun run → CommonPrefixAtDepth M run k

/-- Liveness predicate under churn budget `χ`. -/
def LivenessUnderChurn
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party)
    (AdmissibleRun : (Nat → State) → Prop)
    (χ : Nat) : Prop :=
  ∀ run, AdmissibleRun run →
    M.churnWithin run χ ∧
      ∃ growthWindow minGrowth qualityWindow minHonestWeight,
        ChainGrowth M run growthWindow minGrowth ∧
        ChainQuality M run qualityWindow minHonestWeight

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core Nakamoto assumption bundle. -/
structure Assumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party) : Type (max u v w) where
  AdmissibleRun : (Nat → State) → Prop
  ε : Rat
  settlementDepth : Nat
  churnBudget : Nat
  growthWindow : Nat
  minGrowth : Nat
  qualityWindow : Nat
  minHonestWeight : Nat
  probabilityBudget : ProbabilityBudget M settlementDepth ε
  /-- Each admissible run is the public chain of a concrete longest-chain
  execution (`LongestChain.IsRun`) whose production schedule satisfies the
  window honest-majority condition at depth `settlementDepth`. This is a
  refinement link plus a combinatorial schedule condition, not common prefix;
  common prefix is proved in `LongestChain.common_prefix`. -/
  realizedByLongestChain :
    ∀ run, AdmissibleRun run →
      ∃ (sched : Nat → Bool) (mint : Nat → Block) (lc : Nat → LongestChain.LCState Block),
        LongestChain.IsRun sched mint lc ∧
        (∀ T, LongestChain.WindowHonestMajorityUpTo sched settlementDepth T) ∧
        ∀ t, M.chain (run t) = (lc t).pub
  chainGrowth :
    ∀ run, AdmissibleRun run → ChainGrowth M run growthWindow minGrowth
  chainQuality :
    ∀ run, AdmissibleRun run → ChainQuality M run qualityWindow minHonestWeight
  churnWithin :
    ∀ run, AdmissibleRun run → M.churnWithin run churnBudget

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | admissibleRuns
  | probabilityBudget
  | realizedByLongestChain
  | chainGrowth
  | chainQuality
  | churnWithin
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable Nakamoto assumption set. -/
def coreAssumptions : List Assumption :=
  [ .admissibleRuns
  , .probabilityBudget
  , .realizedByLongestChain
  , .chainGrowth
  , .chainQuality
  , .churnWithin
  ]

/-! ## Assumption Validation API -/

/-- Constant `true`: this validator performs no runtime check. It only reports
that the `Assumptions` bundle passed to it carries a proof of each field, which
the type of the bundle already guarantees. The family model has no concrete
parameters over which an assumption could be decided. -/
def proofCarriedNoRuntimeCheck : Bool :=
  true


/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .admissibleRuns =>
      { assumption := h
      , passed := proofCarriedNoRuntimeCheck
      , detail := "Admissible runs and security parameters are provided."
      }
  | .probabilityBudget =>
      { assumption := h
      , passed := proofCarriedNoRuntimeCheck
      , detail := "The explicit probability budget boundary is provided."
      }
  | .realizedByLongestChain =>
      { assumption := h
      , passed := proofCarriedNoRuntimeCheck
      , detail := "Runs refine a longest-chain execution with window honest majority \
          (decide the window condition with `LongestChain.checkWindowHonestMajority`)."
      }
  | .chainGrowth =>
      { assumption := h
      , passed := proofCarriedNoRuntimeCheck
      , detail := "Chain-growth semantics are provided for admissible runs."
      }
  | .chainQuality =>
      { assumption := h
      , passed := proofCarriedNoRuntimeCheck
      , detail := "Chain-quality semantics are provided for admissible runs."
      }
  | .churnWithin =>
      { assumption := h
      , passed := proofCarriedNoRuntimeCheck
      , detail := "Admissible runs satisfy the configured churn budget."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party}
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
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Derived Guarantees -/

/-- `PrefixOf` agrees with `List.IsPrefix`. -/
theorem prefixOf_iff {Block : Type v} (xs ys : List Block) : PrefixOf xs ys ↔ xs <+: ys :=
  ⟨fun ⟨u, h⟩ => ⟨u, h.symm⟩, fun ⟨u, h⟩ => ⟨u, h.symm⟩⟩

/-- Common prefix at the settlement depth, proved from the longest-chain
refinement and `LongestChain.common_prefix`. -/
theorem common_prefix_of_assumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party} (a : Assumptions M)
    (run : Nat → State) (hRun : a.AdmissibleRun run) :
    CommonPrefixAtDepth M run a.settlementDepth := by
  intro i j pref hij hPre hLen
  obtain ⟨sched, mint, lc, hIsRun, hW, hEq⟩ := a.realizedByLongestChain run hRun
  rw [prefixOf_iff, hEq] at hPre ⊢
  rw [hEq] at hLen
  exact LongestChain.common_prefix hIsRun (hW j) hij le_rfl ⟨hPre, hLen⟩

/-- Probabilistic safety follows from the probability boundary and common prefix. -/
theorem probabilistic_safety_of_assumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party}
    (a : Assumptions M) :
    ProbabilisticSafety M a.AdmissibleRun a.ε := by
  intro run hRun
  exact ⟨a.settlementDepth, a.probabilityBudget, common_prefix_of_assumptions a run hRun⟩

/-- Settlement-depth finality follows from common-prefix semantics. -/
theorem settlement_finality_of_assumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party}
    (a : Assumptions M) :
    SettlementDepthFinality M a.AdmissibleRun a.settlementDepth := by
  intro run hRun
  exact common_prefix_of_assumptions a run hRun

/-- Liveness-under-churn follows from churn, growth, and quality semantics. -/
theorem liveness_under_churn_of_assumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party}
    (a : Assumptions M) :
    LivenessUnderChurn M a.AdmissibleRun a.churnBudget := by
  intro run hRun
  exact
    ⟨ a.churnWithin run hRun
    , a.growthWindow
    , a.minGrowth
    , a.qualityWindow
    , a.minHonestWeight
    , a.chainGrowth run hRun
    , a.chainQuality run hRun
    ⟩

end Nakamoto
end Distributed
