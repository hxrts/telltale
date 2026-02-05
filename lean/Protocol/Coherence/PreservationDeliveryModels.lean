import Protocol.DeliveryModel
import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Preservation
import Protocol.Coherence.SelectPreservation

/-!
# Coherence Preservation for Additional Delivery Models

These lemmas specialize the FIFO preservation theorems to the named
`CausalDelivery` and `LossyDelivery` models. The proofs are by rewriting to the
FIFO aliases.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ## CausalDelivery -/

theorem Coherent_causal_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent CausalDelivery G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv
              (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    Coherent CausalDelivery (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  have hCoh' : CoherentFifo G D := by
    simpa [CausalDelivery, CoherentFifo] using hCoh
  have h := Coherent_send_preserved (G:=G) (D:=D) (senderEp:=senderEp)
      (receiverRole:=receiverRole) (T:=T) (L:=L) hCoh' hG hRecvReady
  simpa [CausalDelivery, CoherentFifo] using h


theorem Coherent_causal_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent CausalDelivery G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent CausalDelivery (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  have hCoh' : CoherentFifo G D := by
    simpa [CausalDelivery, CoherentFifo] using hCoh
  have h := Coherent_recv_preserved (G:=G) (D:=D) (receiverEp:=receiverEp)
      (senderRole:=senderRole) (T:=T) (L:=L) hCoh' hG hTrace
  simpa [CausalDelivery, CoherentFifo] using h


theorem Coherent_causal_select_preserved
    (G : GEnv) (D : DEnv) (selectorEp : Endpoint) (targetRole : Role)
    (selectBranches : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent CausalDelivery G D)
    (hG : lookupG G selectorEp = some (.select targetRole selectBranches))
    (hFind : selectBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTargetReady : ∀ Lrecv, lookupG G { sid := selectorEp.sid, role := targetRole } = some Lrecv →
      ∃ L', Consume selectorEp.role Lrecv
              (lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole }) = some L' ∧
            (Consume selectorEp.role L' [.string]).isSome) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    Coherent CausalDelivery (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string])) := by
  have hCoh' : CoherentFifo G D := by
    simpa [CausalDelivery, CoherentFifo] using hCoh
  have h := Coherent_select_preserved (G:=G) (D:=D) (selectorEp:=selectorEp) (targetRole:=targetRole)
      (bs:=selectBranches) (ℓ:=ℓ) (L:=L) hCoh' hG hFind hTargetReady
  simpa [CausalDelivery, CoherentFifo] using h


theorem Coherent_causal_branch_preserved
    (G : GEnv) (D : DEnv) (brancherEp : Endpoint) (senderRole : Role)
    (branchOptions : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent CausalDelivery G D)
    (hG : lookupG G brancherEp = some (.branch senderRole branchOptions))
    (hFind : branchOptions.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTrace : (lookupD D { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role }).head? = some .string) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    Coherent CausalDelivery (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail) := by
  have hCoh' : CoherentFifo G D := by
    simpa [CausalDelivery, CoherentFifo] using hCoh
  have h := Coherent_branch_preserved (G:=G) (D:=D) (brancherEp:=brancherEp)
      (senderRole:=senderRole) (bs:=branchOptions) (ℓ:=ℓ) (L:=L) hCoh' hG hFind hTrace
  simpa [CausalDelivery, CoherentFifo] using h

/-! ## LossyDelivery -/

theorem Coherent_lossy_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent LossyDelivery G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv
              (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    Coherent LossyDelivery (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  have hCoh' : CoherentFifo G D := by
    simpa [LossyDelivery, CoherentFifo] using hCoh
  have h := Coherent_send_preserved (G:=G) (D:=D) (senderEp:=senderEp)
      (receiverRole:=receiverRole) (T:=T) (L:=L) hCoh' hG hRecvReady
  simpa [LossyDelivery, CoherentFifo] using h


theorem Coherent_lossy_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent LossyDelivery G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent LossyDelivery (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  have hCoh' : CoherentFifo G D := by
    simpa [LossyDelivery, CoherentFifo] using hCoh
  have h := Coherent_recv_preserved (G:=G) (D:=D) (receiverEp:=receiverEp)
      (senderRole:=senderRole) (T:=T) (L:=L) hCoh' hG hTrace
  simpa [LossyDelivery, CoherentFifo] using h


theorem Coherent_lossy_select_preserved
    (G : GEnv) (D : DEnv) (selectorEp : Endpoint) (targetRole : Role)
    (selectBranches : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent LossyDelivery G D)
    (hG : lookupG G selectorEp = some (.select targetRole selectBranches))
    (hFind : selectBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTargetReady : ∀ Lrecv, lookupG G { sid := selectorEp.sid, role := targetRole } = some Lrecv →
      ∃ L', Consume selectorEp.role Lrecv
              (lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole }) = some L' ∧
            (Consume selectorEp.role L' [.string]).isSome) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    Coherent LossyDelivery (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string])) := by
  have hCoh' : CoherentFifo G D := by
    simpa [LossyDelivery, CoherentFifo] using hCoh
  have h := Coherent_select_preserved (G:=G) (D:=D) (selectorEp:=selectorEp) (targetRole:=targetRole)
      (bs:=selectBranches) (ℓ:=ℓ) (L:=L) hCoh' hG hFind hTargetReady
  simpa [LossyDelivery, CoherentFifo] using h


theorem Coherent_lossy_branch_preserved
    (G : GEnv) (D : DEnv) (brancherEp : Endpoint) (senderRole : Role)
    (branchOptions : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent LossyDelivery G D)
    (hG : lookupG G brancherEp = some (.branch senderRole branchOptions))
    (hFind : branchOptions.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTrace : (lookupD D { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role }).head? = some .string) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    Coherent LossyDelivery (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail) := by
  have hCoh' : CoherentFifo G D := by
    simpa [LossyDelivery, CoherentFifo] using hCoh
  have h := Coherent_branch_preserved (G:=G) (D:=D) (brancherEp:=brancherEp)
      (senderRole:=senderRole) (bs:=branchOptions) (ℓ:=ℓ) (L:=L) hCoh' hG hFind hTrace
  simpa [LossyDelivery, CoherentFifo] using h

end
