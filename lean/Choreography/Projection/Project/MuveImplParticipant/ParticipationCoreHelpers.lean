import Choreography.Projection.Project.MuveImplNonPart

/-! # ParticipationCoreHelpers

Branch-size and noSelfComm membership helpers (`size_of_mem_snd_lt_comm`, `no_self_comm_of_mem`) used by `ParticipationCore`. -/

-- Core Development
/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/
/- ## Structured Block 1 -/
namespace Choreography.Projection.Project
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionTypes.Participation
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
-- Size Helpers
/-- Helper: sizeOf a member's continuation is less than sizeOf the list. -/
private theorem size_of_mem_snd_lt {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) :
    sizeOf pair.2 < sizeOf branches := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
          omega
      | tail _ hmem' =>
          have ih' := ih hmem'
          simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1] at ih' ⊢
          omega
/-- Helper: sizeOf a member's continuation is less than sizeOf the comm. -/
theorem size_of_mem_snd_lt_comm {sender receiver : String} {branches : List (Label × GlobalType)}
    {pair : Label × GlobalType} (hmem : pair ∈ branches) :
    sizeOf pair.2 < sizeOf (GlobalType.comm sender receiver branches) := by
  have h1 := size_of_mem_snd_lt hmem
  have hcomm : sizeOf (GlobalType.comm sender receiver branches) =
      1 + sizeOf sender + sizeOf receiver + sizeOf branches := by
    simp only [GlobalType.comm.sizeOf_spec]
  omega
/-- Helper: noSelfComm for a branch list implies noSelfComm for each member. -/
theorem no_self_comm_of_mem {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) (hnsc : noSelfCommBranches branches = true) :
    pair.2.noSelfComm = true := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [noSelfCommBranches, Bool.and_eq_true] at hnsc
      cases hmem with
      | head => exact hnsc.1
      | tail _ hmem' => exact ih hmem' hnsc.2

end Choreography.Projection.Project
