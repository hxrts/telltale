import Protocol.DeliveryModel
import Protocol.Environments

/-!
# MPST Coherence (Model-Parametric)

This module mirrors `Protocol.Coherence.EdgeCoherence` but parameterizes
coherence by an explicit delivery model.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-- Coherence for a single directed edge under a delivery model. -/
def EdgeCoherent (M : DeliveryModel) (G : GEnv) (D : DEnv) (e : Edge) : Prop :=
  let senderEp := { sid := e.sid, role := e.sender : Endpoint }
  let receiverEp := { sid := e.sid, role := e.receiver : Endpoint }
  let trace := lookupD D e
  ∀ Lrecv,
    lookupG G receiverEp = some Lrecv →
    ∃ Lsender,
      lookupG G senderEp = some Lsender ∧
      (M.consume e.sender Lrecv trace).isSome

/-! ### Active Edges -/

/-- An edge is active if both sender and receiver endpoints exist in G. -/
def ActiveEdge (G : GEnv) (e : Edge) : Prop :=
  (lookupG G { sid := e.sid, role := e.sender }).isSome ∧
  (lookupG G { sid := e.sid, role := e.receiver }).isSome

/-- Full coherence under a delivery model (active edges only). -/
def Coherent (M : DeliveryModel) (G : GEnv) (D : DEnv) : Prop :=
  ∀ e, ActiveEdge G e → EdgeCoherent M G D e

/-! ### Small Helpers -/

/-- ActiveEdge from concrete sender/receiver lookups. -/
theorem ActiveEdge_of_endpoints {G : GEnv} {e : Edge} {Lsender Lrecv : LocalType}
    (hGsender : lookupG G { sid := e.sid, role := e.sender } = some Lsender)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    ActiveEdge G e := by
  simp [ActiveEdge, hGsender, hGrecv]

/-- Extract EdgeCoherent from Coherent given sender/receiver lookups. -/
theorem Coherent_edge_of_endpoints {M : DeliveryModel} {G : GEnv} {D : DEnv} {e : Edge}
    {Lsender Lrecv : LocalType}
    (hCoh : Coherent M G D)
    (hGsender : lookupG G { sid := e.sid, role := e.sender } = some Lsender)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    EdgeCoherent M G D e := by
  exact hCoh e (ActiveEdge_of_endpoints hGsender hGrecv)

/-- Coherent gives EdgeCoherent for any active edge. -/
theorem Coherent_edge_any {M : DeliveryModel} {G : GEnv} {D : DEnv}
    (hCoh : Coherent M G D) {e : Edge} (hActive : ActiveEdge G e) :
    EdgeCoherent M G D e := by
  exact hCoh e hActive

/-- Extract the consume condition from `EdgeCoherent` given a receiver lookup. -/
theorem EdgeCoherent_consume_of_receiver {M : DeliveryModel} {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hCoh : EdgeCoherent M G D e)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    (M.consume e.sender Lrecv (lookupD D e)).isSome := by
  rcases hCoh Lrecv hGrecv with ⟨_, _, hConsume⟩
  exact hConsume

/-- Extract the sender lookup guaranteed by `EdgeCoherent` given a receiver lookup. -/
theorem EdgeCoherent_sender_of_receiver {M : DeliveryModel} {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hCoh : EdgeCoherent M G D e)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    ∃ Lsender, lookupG G { sid := e.sid, role := e.sender } = some Lsender := by
  rcases hCoh Lrecv hGrecv with ⟨Lsender, hGsender, _⟩
  exact ⟨Lsender, hGsender⟩

/-! ## EdgeCoherent Irrelevance Lemmas -/

/-- Updating G at an endpoint not involved in edge e doesn't affect EdgeCoherent at e. -/
theorem EdgeCoherent_updateG_irrelevant (M : DeliveryModel) (G : GEnv) (D : DEnv) (e : Edge)
    (ep : Endpoint) (L : LocalType)
    (hNeSender : ep ≠ { sid := e.sid, role := e.sender })
    (hNeRecv : ep ≠ { sid := e.sid, role := e.receiver })
    (hCoh : EdgeCoherent M G D e) :
    EdgeCoherent M (updateG G ep L) D e := by
  simp only [EdgeCoherent] at hCoh ⊢
  intro Lrecv hGrecv
  have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
    simpa [lookupG_update_neq _ _ _ _ hNeRecv] using hGrecv
  obtain ⟨Lsender, hGsender, hConsume⟩ := hCoh Lrecv hGrecv'
  refine ⟨Lsender, ?_, hConsume⟩
  simpa [lookupG_update_neq _ _ _ _ hNeSender] using hGsender

/-- Updating D at edge e' ≠ e doesn't affect EdgeCoherent at e. -/
theorem EdgeCoherent_updateD_irrelevant (M : DeliveryModel) (G : GEnv) (D : DEnv) (e e' : Edge)
    (ts : List ValType)
    (hNe : e' ≠ e)
    (hCoh : EdgeCoherent M G D e) :
    EdgeCoherent M G (updateD D e' ts) e := by
  simp only [EdgeCoherent] at hCoh ⊢
  intro Lrecv hGrecv
  simp only [lookupD_update_neq _ _ _ _ hNe]
  exact hCoh Lrecv hGrecv

end
