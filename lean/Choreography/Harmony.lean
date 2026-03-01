import Choreography.Harmony.StepHarmony
import Choreography.Harmony.Substitution
import Choreography.Harmony.ParticipantSteps
import Choreography.Harmony.NonParticipantHelpers
import Choreography.Harmony.NonParticipantSteps

/- 
The Problem. The harmony development is split across multiple focused files,
but downstream proofs need a single module exposing the full step/projection
correspondence story.

Solution Structure. Re-export the focused harmony submodules from one barrel,
keeping each proof family isolated while presenting one cohesive API.
-/

/-! ## Notes

## Projection Coherence

These lemmas establish that projection is coherent with stepping:
after a global step, the projected environment correctly reflects
the new local types for each role.

**Branch coherence follows from CProject's AllBranchesProj requirement:**

Lean's CProject definition ALREADY has Coq's coherence built-in via AllBranchesProj
(Projectb.lean:204-206). The coherence requirement is structurally present; we just need
to connect it to the trans function via c_project_implies_eq2_trans.

**Proof via wellFormedness** (outline):
Given a well-formed comm node with branches and non-participant role:
1. AllBranchesProj in CProject ensures all branches project to the same candidate
2. c_project_implies_eq2_trans connects CProject to trans
3. Transitivity gives us branch-to-branch EQ2 equivalence

**Alternative: Direct proof** (without wellFormedness):
We can prove this inductively on the branch list structure by showing that
consecutive branches project coherently, which composes to full coherence.
This approach uses only the structure of trans without requiring CProject proofs.

## Substitution Commutation

The core coinductive property: projection (via trans) commutes with global mu-substitution.

For any GlobalType g, recursion variable t, and mu-body G (where G = mu t g for some g):
  `EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role))`

This is the "projection commutes with substitution" lemma (Coq: `full_eunf_subst`).
The property requires coinductive reasoning because branch continuations recurse indefinitely.

## ProjSubstRel Postfixpoint Proof Notes

ProjSubstRel is a post-fixpoint of EQ2F (with EQ2 as accumulator).

This encapsulates the coinductive reasoning for projection-substitution commutation.
The proof proceeds by case analysis on the GlobalType witness:
- `.end`: both sides are `.end` ✓
- `.var v`: split on v = t; both sides match ✓
- `.mu s inner`:
  - s = t (shadowed): both sides identical ✓
  - s ≠ t:
    - Both guarded: mu-mu case via eq2_mu_crossed_unfold_left/right ✓
    - Mismatched guardedness: via eq2_mu_unguarded_to_end/eq2_end_to_mu_unguarded ✓
    - Both unguarded: both .end ✓
- `.comm sender receiver branches`:
  - role = sender: both .send, branches via trans_branches_proj_subst_rel ✓
  - role = receiver: both .recv, branches via trans_branches_proj_subst_rel ✓
  - non-participant:
    - empty branches: both .end ✓
    - non-empty: recursive call on continuation subterm ✓

## trans_subst_comm intent

Projection commutes with substitution.

For any GlobalType g, recursion variable t, mu-type G, and role:
  `EQ2 (projTrans (g.substitute t G) role) ((projTrans g role).substitute t (projTrans G role))`

This is semantically sound: the LHS and RHS represent the same infinite communication tree
when fully unfolded.

**Coq reference:** `full_eunf_subst` in `coLocal.v`

## EQ2 transitivity + subst_end_unguarded_eq2_end

EQ2 transitivity now uses `eq2_trans_wf` from EQ2Props (Bisim detour).
This replaces the prior `EQ2_trans` path and requires explicit
well-formedness witnesses for intermediate types.

Substituting `.end` for an unguarded variable produces something EQ2 to `.end`.

When `lt.isGuarded v = false`, the type `lt` has the structure:
- Either `lt = .var v` (directly), or
- `lt = .mu s body` where `s ≠ v` and `body.isGuarded v = false`

This is because `.send`/`.recv` always return `true` for `isGuarded`.

After substituting `.end` for `v`:
- `.var v` becomes `.end` (EQ2 .end .end)
- `.mu s body` becomes `.mu s (body.substitute v .end)`, which unfolds to `.end`
  because the inner structure eventually reaches `.var v` → `.end`

**PROVEN** in SubstEndUnguarded.lean via UnfoldsToEnd induction.
-/

/-! # Choreography.Harmony

Harmony between global steps and environment steps.

## Expose

The following definitions form the semantic interface for proofs:

- `Claims`: bundle of harmony properties
- `step_harmony`: global step induces matching env step
- `proj_trans_other_step`: non-participant projection unchanged after step

## Technical Debt Summary (legacy gaps removed; assumption-free in this file)

**MAJOR PROGRESS**: `trans_branches_coherent` ELIMINATED!
Coherence is now proven from first principles using participation structure, following Coq's proof strategy.

**Mu-unfolding (from MuUnfoldLemmas.lean):**
- `eq2_mu_crossed_unfold_left`: **PROVEN** via proj_subst + eq2_mu_self_unfold
- `eq2_mu_crossed_unfold_right`: **PROVEN** via proj_subst + eq2_mu_to_unfold
- `eq2_mu_unguarded_to_end`: **PROVEN** (vacuously true - hypotheses contradict when s ≠ t)
- `eq2_end_to_mu_unguarded`: **PROVEN** (vacuously true for closed types)

**Closedness theorems (PROVEN in GlobalType.lean):**
- `GlobalType.is_closed_substitute_mu`: **PROVEN** - mu-unfolding preserves closedness
- `GlobalType.is_closed_comm_branches`: **PROVEN** - closed comm has closed branches

**Proven coinductive theorems:**
- `subst_end_unguarded_eq2_end`: **PROVEN** in SubstEndUnguarded.lean via UnfoldsToEnd induction
- `trans_subst_comm`: **PROVEN** using paco coinduction (requires closedness)
- `eq2_trans_wf`: **PROVEN** via Bisim (EQ2Props.lean); used with explicit well-formedness witnesses

**Remaining Assumptions:** None (sender/receiver lemmas proven via head-action predicate)

**COHERENCE PROOF COMPLETE (modulo helper lemmas):**
- `trans_branches_coherent_eq2`: **PROVEN** using participation structure
  - Case 1 (non-participant): Uses `eq_end` - all branches project to .end
  - Case 2 (participant): Uses `part_of_all2` - uniform participation ✓
- `trans_produces_c_project`: Bridges trans to CProject (uses coherence)
- `branches_project_coherent`: Extracts EQ2 equivalence from AllBranchesProj

**Inherited from MuUnfoldLemmas.lean (via ProjSubst.lean):**
4. `proj_subst`: Projection-substitution commutation (Coq indProj.v:173)

**Key changes from Coq alignment:**
- `trans` now checks `(trans body role).isGuarded t` instead of `lcontractive body`
- This matches Coq's `eguarded` check on the projected type, not the global type
- Non-contractive projections are replaced with `.end` by construction
- The old `step_noncontr_impossible` assumption was removed (it was false for nested mu)
- All theorems require closedness of global types (standard for protocol verification)

**Next steps:** propagate the head-action predicate (`action_pred`) through callers
if they need sender/receiver projections beyond the head-communication case.
-/
