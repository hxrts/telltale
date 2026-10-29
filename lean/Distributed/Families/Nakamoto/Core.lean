import Distributed.Families.Nakamoto.LongestChain

set_option autoImplicit false

/-! # Distributed.Families.Nakamoto

Reusable Nakamoto-style assumptions and theorem forms:
- probabilistic safety (common prefix plus an explicit probability boundary),
- settlement-depth finality (common prefix),
- chain growth (liveness).

Common prefix and chain growth are proved for the deterministic longest-chain
model of `LongestChain` under its combinatorial window condition, and
transported along a refinement. That model has no network delay. Chain
quality and churn are not modelled; their former premises restated the
conclusions and were removed.
-/

/-
The Problem. Earlier versions carried `chainGrowth`, `chainQuality`, and
`churnWithin` premises equal to the liveness conclusions.
Solution Structure. Prove chain growth in `LongestChain.chain_growth`, transport
it along `realizedByLongestChain`, and drop the unprovable quality/churn forms.
-/

/-! ## Core Development -/

namespace Distributed
namespace Nakamoto

universe u v w

/-- Minimal model interface for Nakamoto-style reasoning. -/
structure Model (State : Type u) (Block : Type v) (Party : Type w) where
  initial : State → Prop
  chain : State → List Block
  failureProbabilityAtDepth : Nat → Rat
  adversarialPowerBounded : Prop

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

/-- Chain-growth liveness: every admissible run grows by at least `⌈k/2⌉`
blocks in every window of `k` rounds. -/
def ChainGrowthLiveness
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party)
    (AdmissibleRun : (Nat → State) → Prop)
    (k : Nat) : Prop :=
  ∀ run, AdmissibleRun run → ChainGrowth M run k ((k + 1) / 2)

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core Nakamoto assumption bundle. -/
structure Assumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    (M : Model State Block Party) : Type (max u v w) where
  AdmissibleRun : (Nat → State) → Prop
  ε : Rat
  settlementDepth : Nat
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

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | admissibleRuns
  | probabilityBudget
  | realizedByLongestChain
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

/-- Chain growth, proved from the longest-chain refinement and
`LongestChain.chain_growth`. -/
theorem chain_growth_of_assumptions
    {State : Type u} {Block : Type v} {Party : Type w}
    {M : Model State Block Party}
    (a : Assumptions M) :
    ChainGrowthLiveness M a.AdmissibleRun a.settlementDepth := by
  intro run hRun i
  obtain ⟨sched, mint, lc, hIsRun, hW, hEq⟩ := a.realizedByLongestChain run hRun
  rw [hEq, hEq]
  exact LongestChain.chain_growth hIsRun (hW (i + a.settlementDepth)) le_rfl le_rfl

end Nakamoto
end Distributed
