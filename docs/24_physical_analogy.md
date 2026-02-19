# Physical Analogies for the Telltale Runtime

This document gives intuition for the main proof structures in the runtime and theorem-pack stack.

## Scope

These analogies explain structure. They do not replace theorem statements.

| Formal surface | Analogy | Runtime role |
|---|---|---|
| Separation logic framing | extensivity and locality | modular reasoning over disjoint resources |
| MPST coherence | conservation law over communication obligations | safety preservation across steps |
| Projection and harmony | coarse-graining with consistency constraints | global to local compatibility |
| Effect runtime and spec | equation of state plus constitutive law | executable update plus typing obligation |
| Invariants | conserved quantity under legal transitions | persistent safety conditions |
| Adequacy | model-to-observation bridge | links proofs to runtime traces |

## Separation Logic as Locality

Framing captures non-interference between disjoint resources. The runtime proof style uses this property to isolate one session or one edge while keeping unrelated state unchanged.

The framing rule used in proofs is a theorem-level rule in the current Lean development. It is not treated as a standing axiom in this repository.

## Coherence as a Conservation Law

`Coherent` states that buffered edge traces remain consumable against receiver-side expectations. Send, receive, offer, and choose steps preserve this condition under stated premises.

This role matches a conservation law. The allowed transition relation is constrained so coherence is preserved by legal steps.

## Projection as Coarse-Graining

Projection removes information that a role cannot observe and keeps information that affects that role. Harmony theorems then show this reduced view still tracks valid protocol evolution.

Merge constraints are the consistency condition of this coarse-graining step. If branch views are incompatible for a non-participant, projection is rejected.

## Effect Layer as Constitutive Law

The runtime uses `EffectRuntime` for executable effect transitions and `EffectSpec` for typing obligations. This split is in `lean/Runtime/VM/Model/TypeClasses.lean`.

The analogy is a constitutive law layered on top of protocol structure. The protocol fixes allowed communication shape and the effect layer fixes how local state updates happen.

## Resource Algebras as Accounting

Authoritative and fragment resources model global state and local claims. Update rules enforce that local claims stay compatible with global ownership.

This behaves like conservation with constrained transfer. Ownership can move and split through valid updates but cannot be fabricated.

## Invariants as Persisting Constraints

An invariant packages a predicate that must be restored after each opened reasoning step. Runtime proofs use invariant opening and closing to justify local updates without losing global safety.

Cancelable invariants model scoped shutdown. Session close transitions can consume shutdown permissions and terminate future obligations for that scope.

## Adequacy as Observation Bridge

Adequacy theorems connect step semantics to observable traces and postconditions. This is the formal link from internal reduction to external behavior claims.

In this repository adequacy is theorem-backed in the runtime proof stack. The map from certified proof objects to runtime capability claims is exposed through theorem-pack APIs.

## Current Repository Status

The current Lean tree is reported as axiom-free and sorry-free in the generated code map and status metrics.

This matters for the analogy. Conservation and bridge claims in this document correspond to proved theorem surfaces and premise-scoped interfaces, not placeholder assumptions.

## Related Docs

- [Session Type Theory](06_session_type_theory.md)
- [Lean Verification](18_lean_verification.md)
- [Theorem Program](26_theorem_program.md)
