import Protocol.Coherence.EdgeCoherence

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-- Sender endpoint associated with an edge. -/
def senderEndpoint (e : Edge) : Endpoint :=
  { sid := e.sid, role := e.sender }

/-- Receiver endpoint associated with an edge. -/
def receiverEndpoint (e : Edge) : Endpoint :=
  { sid := e.sid, role := e.receiver }

/-- An edge shares the given endpoint (either as sender or receiver). -/
def EdgeShares (e : Edge) (ep : Endpoint) : Prop :=
  senderEndpoint e = ep ∨ receiverEndpoint e = ep

/-- Standard 3-way case split used by preservation proofs. -/
theorem edge_case_split (e updated : Edge) (ep : Endpoint) :
    e = updated ∨ (e ≠ updated ∧ EdgeShares e ep) ∨ (e ≠ updated ∧ ¬ EdgeShares e ep) := by
  by_cases h1 : e = updated
  · exact Or.inl h1
  · by_cases h2 : EdgeShares e ep
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
