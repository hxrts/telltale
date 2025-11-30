# Lean Verification

Lean 4 checks each exported choreography against its projected local types. The runner decodes JSON from `lean-exporter`, projects per-role traces, and confirms each exported branch is included in the projection by order and label.

## How to run

Use the Nix shell so Rust, Lean, and Lake match expected versions.

```bash
nix develop --command just rumpsteak-lean-check
```
This command exports the sample choreography for Chef, SousChef, and Baker from `lean/choreo/lean-sample.choreo`, builds the Lean runner, and validates each role. Text and JSON logs are written in `lean/artifacts/runner-<role>.{log,json}`.

```bash
nix develop --command just ci-dry-run
```
This command runs the full CI-equivalent sweep: Rust fmt, clippy, tests, Lean sample, Lean extended scenario, and the intentional failing check.

## What is being verified

`Rumpsteak.Choreography` checks that roles and actions decode and reference only declared roles. The predicates `hasUniqueRoles` and `hasValidActions` rule out duplicate roles and dangling endpoints before projection begins. Each action is a triple `(origin, destination, label)`; membership tests are done with `DecidableEq` on strings.

`Rumpsteak.Projection` builds per-role `LocalType` traces. Lemma `subLabelsOf_refl` proves `subLabelsOf lt lt = true`, using `List.all_eq_true` and `List.any_eq_true` to show every projected label witnesses itself. A label failure in the runner therefore means the exporter produced a label absent from the projection for that role.

`Rumpsteak.Program` maps exported effects (`Effect.send`, `Effect.recv`) into `LocalAction` values. The map is a homomorphism from the JSON schema to the projection domain, so equality checks are meaningful without coercions.

`Rumpsteak.Subtyping` defines order checks with `DecidableEq`. `isSubsequence` is a structural recursion that skips super-sequence heads until a match; `isSubtype` pairs it with a length guard. Lemmas `isSubsequence_refl` and `isSubtype_refl` show a projected trace always passes its own order check; only exporter reordering or omission can fail.

`Rumpsteak.Runner` applies three invariants per branch: (1) membership: every exported action must appear in the projection, (2) order: exported actions must be a subsequence of the projection, (3) labels: exported labels must be contained in the projection labels. Failures report the branch name plus the specific missing or out-of-order actions.

### Core Lean predicates (notation)

```lean
def subLabelsOf (lt sup : LocalType) : Bool :=
  lt.actions.all (fun a => sup.actions.any (fun b => decide (b = a)))

def isSubsequence {α} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a = b then isSubsequence as bs else isSubsequence (a :: as) bs

def isSubtype (sub sup : LocalType) : Bool :=
  sub.actions.length <= sup.actions.length ∧ isSubsequence sub.actions sup.actions
```
These definitions are the exact predicates the runner enforces. `subLabelsOf` is symmetric in label matching; `isSubsequence` is asymmetric and enforces ordering; `isSubtype` combines length and ordering to reject reordered or longer traces.

### Proven lemmas (sketch)

```lean
theorem subLabelsOf_refl (lt : LocalType) : subLabelsOf lt lt = true := by
  unfold subLabelsOf; simp [List.all_eq_true, List.any_eq_true]

theorem isSubsequence_refl {α} [DecidableEq α] (xs : List α) :
  isSubsequence xs xs = true := by induction xs <;> simp [isSubsequence, *]

theorem isSubtype_refl (lt : LocalType) : isSubtype lt lt = true := by
  simp [isSubtype, isSubsequence_refl]
```
`subLabelsOf_refl` uses the standard `all_eq_true` and `any_eq_true` characterizations to witness each element by itself. `isSubsequence_refl` and `isSubtype_refl` are structural inductions showing the order check is reflexive. These lemmas ensure that only differences between exporter output and projection can trigger failures.

Failure reporting lists the branch name, missing actions, ordering mismatches, or unexpected labels.

## Sample choreography

`lean/choreo/lean-sample.choreo` models a collaborative dinner with two meal branches (pasta, tacos) and three dessert options (cake, fruit, none). The runner checks that each branch for Chef, SousChef, and Baker is a subsequence of its projection and introduces no extra labels.

## Extended scenario

`just rumpsteak-lean-check-extended` validates `lean/choreo/lean-extended.choreo`, which adds two course cycles before dessert options. Per-role text and JSON logs are written under `lean/artifacts/runner-extended-*.{log,json}`.

## Intentional failing fixture

`just rumpsteak-lean-check-failing` exports `lean/choreo/lean-failing.choreo`, then corrupts the program label to `WrongLabel`. The runner is expected to exit non-zero and print the branch error; no logs are written on failure so CI catches the status directly.

## Editing scenarios

Update inputs in `lean/choreo/`. Change `--role` in the Just recipes to validate other roles. Regenerate and re-run the commands above to verify new scenarios.
