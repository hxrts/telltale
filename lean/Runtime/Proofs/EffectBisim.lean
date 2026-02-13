import Runtime.Proofs.EffectBisim.Core
import Runtime.Proofs.EffectBisim.Bridge
import Runtime.Proofs.EffectBisim.Congruence
import Runtime.Proofs.EffectBisim.ConfigEquivBridge
import Runtime.Proofs.EffectBisim.Examples
import Runtime.Proofs.EffectBisim.RationalFragment

/-! # Runtime.Proofs.EffectBisim

Boundary-facing coinductive bisimulation toolkit for effectful runtime proofs.
-/

/-
The Problem. Runtime/protocol proofs need a single stable import path for the
new coinductive effect-equivalence layer.

Solution Structure. Re-export the core relation, bridge theorems, congruence
rules, quotient compatibility lemmas, and small canonical examples.
-/
