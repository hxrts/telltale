# Theorem Program

This document maps the three-paper theorem program to implemented Lean modules and runtime surfaces.

## Trilogy Structure

The theorem program is organized into three stages.

| Stage | Paper focus | Core output |
|---|---|---|
| Paper 1 | coherence and effect bridge | preservation kernel and typed VM bridge premises |
| Paper 2 | quantitative and decision dynamics | bounds, decidability packages, crash and Byzantine interfaces |
| Paper 3 | reconfiguration and envelope adequacy | harmony under reconfiguration, envelope exactness, admission and adherence |

## Paper 1 Mapping

Paper 1 centers on operational coherence and the `Consume` kernel.

| Claim family | Lean anchor modules |
|---|---|
| message-type alignment via `Consume` | `Protocol/Coherence/Consume.lean` |
| subtype replacement and coherence lift | `Protocol/Coherence/SubtypeReplacement*.lean` |
| coherence preservation stack | `Protocol/Preservation*.lean`, `Protocol/Coherence/*` |
| typed effect bridge to VM | `Runtime/Proofs/VM/BridgeStrengthening.lean`, `Runtime/Proofs/EffectBisim/*` |

Claim scope is assumption-scoped. Delivery and monitor premises remain explicit in the bridge layer.

## Paper 2 Mapping

Paper 2 adds quantitative dynamics and algorithmic decision surfaces.

| Claim family | Lean anchor modules |
|---|---|
| weighted quantitative descent and scheduler-lifted bounds | `Runtime/Proofs/WeightedMeasure/*`, `Runtime/Proofs/SchedulingBound*.lean`, `Runtime/Proofs/Lyapunov.lean` |
| regular finite-reachability decidability | `SessionCoTypes/AsyncSubtyping/*`, regular equivalence modules |
| crash-stop characterization | `Protocol/CrashTolerance.lean` |
| Byzantine exact safety interface package | distributed adapter and theorem-pack modules |

Bound classes differ by theorem. Productive-step bounds are exact under premises and scheduler-lifted totals are profile-dependent conservative bounds.

## Paper 3 Mapping

Paper 3 integrates reconfiguration, exact envelope characterization, and VM adherence.

| Claim family | Lean anchor modules |
|---|---|
| reconfiguration harmony for link and delegation | `Protocol/Deployment/Linking*.lean`, harmony and delegation modules |
| relative minimality and composed-system conservation | `Protocol/Coherence/*`, linking and Lyapunov modules |
| envelope exactness and normalization | `Runtime/Adequacy/EnvelopeCore/*` |
| adequacy and runtime adherence | `Runtime/Adequacy/*`, `Runtime/Proofs/TheoremPack/*` |
| Byzantine envelope extension | distributed adapters and theorem-pack Byzantine surfaces |

This stage ties proof objects to runtime capability and admission surfaces.

## Assumption and Boundary Model

Each theorem family is tied to explicit assumption bundles.

| Boundary class | Meaning |
|---|---|
| exact under assumptions | theorem gives iff or maximality class under declared premises |
| conservative under profile | theorem gives safe upper bound or admitted envelope class |
| interface only | package provides typed boundary and witness hooks without stronger global claim |
| out of scope | intentionally deferred claim class |

Examples include scheduler-lifted total-step bounds as conservative and Byzantine liveness outside declared timing and fairness bundles as out of scope.

## Runtime Capability Link

The theorem program is operationalized through theorem-pack inventory and admission gates.

`Runtime/Proofs/TheoremPack/API.lean` provides gate aliases. `Runtime/Proofs/TheoremPack/Inventory.lean` provides capability key extraction. `Runtime/Adequacy/EnvelopeCore/AdmissionLogic.lean` provides admission soundness, completeness, and diagnostics categories.

Rust admission paths in `rust/vm/src/runtime_contracts.rs` and `rust/vm/src/composition.rs` consume these proof-facing concepts as executable gates.

## Related Docs

- [Lean Verification](18_lean_verification.md)
- [Capability and Admission](25_capability_admission.md)
- [Distributed and Classical Families](27_distributed_classical_families.md)
