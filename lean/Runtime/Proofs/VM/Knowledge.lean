import Runtime.VM.Model.Knowledge

set_option autoImplicit false

/-! # Runtime.Proofs.VM.Knowledge

Proof-only laws for knowledge-policy serialization roundtrips.
-/

universe u

theorem FlowPolicy.toRepr?_ofRepr (repr : FlowPolicyRepr) :
    (FlowPolicy.ofRepr repr).toRepr? = some repr := by
  cases repr <;> rfl

theorem FlowPolicy.ofRepr_toRepr?_eq (policy : FlowPolicy) :
    match policy.toRepr? with
    | some repr => FlowPolicy.ofRepr repr = policy
    | none => True := by
  cases policy <;> simp [FlowPolicy.toRepr?, FlowPolicy.ofRepr]
