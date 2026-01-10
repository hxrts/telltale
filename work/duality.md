# Duality Work Plan (LocalTypeR)

Goal: implement a clean, reusable duality layer for `LocalTypeR` that preserves
closedness/contractiveness and enables code reduction by reusing send/recv proofs.

## Plan

- [x] **Audit existing dual definitions** in `LocalTypeR` and list missing lemmas.
- [x] **Create `CoTypes/Duality.lean`** with imports/namespace and core helpers.
- [x] **Expose involution helpers** (`dual_involutive`, `dualBranches_involutive`) as theorems.
- [x] **Closedness preservation**: prove `freeVars_dual` + `isClosed` invariance.
- [x] **Guardedness/contractiveness preservation**: `isGuarded_dual`, `isContractive_dual`, branch lemma.
- [x] **Observable duality**: `CanSend ↔ CanRecv` under dual; branch-map lemma.
- [x] **EQ2 compatibility**: `EQ2_dual_compat` + `BranchesRel` mapping under dual.
- [x] **Apply duality to reduce duplication**: refactor at least one recv lemma via send.
- [x] **Docs/exports**: short module docs and export hints.

## Notes

- `LocalTypeR.dual` already exists in `LocalTypeR.lean`; we should **reuse**, not duplicate.
- Aim for short mutual-recursion lemmas and `simp`-friendly statements.
- Use the new duality lemma to collapse send/recv proof duplication in `Bisim.lean`.
