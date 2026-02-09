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

section

/-! ## CausalDelivery -/

theorem Coherent_causal_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv
              (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    Coherent (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  exact Coherent_send_preserved (G:=G) (D:=D) (senderEp:=senderEp)
    (receiverRole:=receiverRole) (T:=T) (L:=L) hCoh hG hRecvReady


theorem Coherent_causal_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  exact Coherent_recv_preserved (G:=G) (D:=D) (receiverEp:=receiverEp)
    (senderRole:=senderRole) (T:=T) (L:=L) hCoh hG hTrace


theorem Coherent_causal_select_preserved
    (G : GEnv) (D : DEnv) (selectorEp : Endpoint) (targetRole : Role)
    (selectBranches : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G selectorEp = some (.select targetRole selectBranches))
    (hFind : selectBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTargetReady : ∀ Lrecv, lookupG G { sid := selectorEp.sid, role := targetRole } = some Lrecv →
      ∃ L', Consume selectorEp.role Lrecv
              (lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole }) = some L' ∧
            (Consume selectorEp.role L' [.string]).isSome) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    Coherent (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string])) := by
  exact Coherent_select_preserved (G:=G) (D:=D) (selectorEp:=selectorEp) (targetRole:=targetRole)
    (bs:=selectBranches) (ℓ:=ℓ) (L:=L) hCoh hG hFind hTargetReady


theorem Coherent_causal_branch_preserved
    (G : GEnv) (D : DEnv) (brancherEp : Endpoint) (senderRole : Role)
    (branchOptions : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G brancherEp = some (.branch senderRole branchOptions))
    (hFind : branchOptions.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTrace : (lookupD D { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role }).head? = some .string) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    Coherent (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail) := by
  exact Coherent_branch_preserved (G:=G) (D:=D) (brancherEp:=brancherEp)
    (senderRole:=senderRole) (bs:=branchOptions) (ℓ:=ℓ) (L:=L) hCoh hG hFind hTrace

/-! ## LossyDelivery -/

theorem Coherent_lossy_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv
              (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    Coherent (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  exact Coherent_send_preserved (G:=G) (D:=D) (senderEp:=senderEp)
    (receiverRole:=receiverRole) (T:=T) (L:=L) hCoh hG hRecvReady


theorem Coherent_lossy_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  exact Coherent_recv_preserved (G:=G) (D:=D) (receiverEp:=receiverEp)
    (senderRole:=senderRole) (T:=T) (L:=L) hCoh hG hTrace


theorem Coherent_lossy_select_preserved
    (G : GEnv) (D : DEnv) (selectorEp : Endpoint) (targetRole : Role)
    (selectBranches : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G selectorEp = some (.select targetRole selectBranches))
    (hFind : selectBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTargetReady : ∀ Lrecv, lookupG G { sid := selectorEp.sid, role := targetRole } = some Lrecv →
      ∃ L', Consume selectorEp.role Lrecv
              (lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole }) = some L' ∧
            (Consume selectorEp.role L' [.string]).isSome) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    Coherent (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string])) := by
  exact Coherent_select_preserved (G:=G) (D:=D) (selectorEp:=selectorEp) (targetRole:=targetRole)
    (bs:=selectBranches) (ℓ:=ℓ) (L:=L) hCoh hG hFind hTargetReady


theorem Coherent_lossy_branch_preserved
    (G : GEnv) (D : DEnv) (brancherEp : Endpoint) (senderRole : Role)
    (branchOptions : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G brancherEp = some (.branch senderRole branchOptions))
    (hFind : branchOptions.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTrace : (lookupD D { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role }).head? = some .string) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    Coherent (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail) := by
  exact Coherent_branch_preserved (G:=G) (D:=D) (brancherEp:=brancherEp)
    (senderRole:=senderRole) (bs:=branchOptions) (ℓ:=ℓ) (L:=L) hCoh hG hFind hTrace

end
