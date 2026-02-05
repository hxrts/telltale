import Protocol.Environments
import Protocol.Coherence.Consume

/-!
# Delivery Models

This module introduces a minimal abstraction layer for delivery models without
changing existing FIFO semantics. The goal is to allow new delivery models
(causal, lossy, etc.) to be defined while keeping the current code unchanged.

We provide:
- `fifo`: the current FIFO semantics, defined to be the existing `Consume`.
- `DeliveryModelLaws`: minimal algebraic laws used by coherence proofs.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ## Delivery Model Interface -/

/-- Delivery model abstraction: interpretation of in-flight traces for a sender. -/
structure DeliveryModel where
  consume : Role → LocalType → List ValType → Option LocalType

/-- Minimal laws required by the coherence proofs. -/
structure DeliveryModelLaws (M : DeliveryModel) : Prop where
  consume_nil :
    ∀ from_ (L : LocalType),
      M.consume from_ L [] = some L
  consume_append :
    ∀ from_ (L : LocalType) (ts : List ValType) (T : ValType) {L' : LocalType},
      M.consume from_ L ts = some L' →
      M.consume from_ L (ts ++ [T]) = M.consume from_ L' [T]
  consume_cons :
    ∀ from_ (L : LocalType) (T : ValType) (ts : List ValType),
      M.consume from_ L (T :: ts) =
      match M.consume from_ L [T] with
      | some L' => M.consume from_ L' ts
      | none => none
  consume_rename :
    ∀ (ρ : SessionRenaming) (from_ : Role) (L : LocalType) (ts : List ValType),
      M.consume from_ (renameLocalType ρ L) (ts.map (renameValType ρ)) =
        (M.consume from_ L ts).map (renameLocalType ρ)

/-- Stronger laws mirroring FIFO-style Consume behavior. -/
structure DeliveryModelLawsStrong (M : DeliveryModel) extends DeliveryModelLaws M : Prop where
  consume_non_recv_empty :
    ∀ {from_ : Role} {L : LocalType} {ts : List ValType} {L' : LocalType},
      (∀ r T L'', L ≠ .recv r T L'') →
      (∀ r bs, L ≠ .branch r bs) →
      M.consume from_ L ts = some L' →
      ts = []
  consume_other_empty :
    ∀ {from_ r : Role} {T : ValType} {L : LocalType} {ts : List ValType} {L' : LocalType},
      from_ ≠ r →
      M.consume from_ (.recv r T L) ts = some L' →
      ts = []
  consume_recv_single :
    ∀ (from_ : Role) (T : ValType) (L : LocalType),
      M.consume from_ (.recv from_ T L) [T] = some L
  consume_single_recv_match :
    ∀ {from_ : Role} {T T' : ValType} {L L' : LocalType},
      M.consume from_ (.recv from_ T' L) [T] = some L' →
      T = T'
  consume_single_branch_string :
    ∀ {from_ : Role} {bs : List (String × LocalType)} {T : ValType} {L' : LocalType},
      M.consume from_ (.branch from_ bs) [T] = some L' →
      T = .string
  consume_branch_nonempty_false :
    ∀ {from_ r : Role} {bs : List (String × LocalType)} {t : ValType} {ts : List ValType} {L' : LocalType},
      M.consume from_ (.branch r bs) (t :: ts) = some L' → False

/-! ## Model-Parametric Consume Lemmas -/

theorem ConsumeM_nil (M : DeliveryModel) (hLaws : DeliveryModelLaws M)
    (from_ : Role) (L : LocalType) :
    M.consume from_ L [] = some L :=
  hLaws.consume_nil from_ L

theorem ConsumeM_append (M : DeliveryModel) (hLaws : DeliveryModelLaws M)
    (from_ : Role) (L : LocalType) (ts : List ValType) (T : ValType) {L' : LocalType} :
    M.consume from_ L ts = some L' →
    M.consume from_ L (ts ++ [T]) = M.consume from_ L' [T] :=
  hLaws.consume_append from_ L ts T

theorem ConsumeM_cons (M : DeliveryModel) (hLaws : DeliveryModelLaws M)
    (from_ : Role) (L : LocalType) (T : ValType) (ts : List ValType) :
    M.consume from_ L (T :: ts) =
    match M.consume from_ L [T] with
    | some L' => M.consume from_ L' ts
    | none => none :=
  hLaws.consume_cons from_ L T ts

theorem ConsumeM_rename (M : DeliveryModel) (hLaws : DeliveryModelLaws M)
    (ρ : SessionRenaming) (from_ : Role) (L : LocalType) (ts : List ValType) :
    M.consume from_ (renameLocalType ρ L) (ts.map (renameValType ρ)) =
      (M.consume from_ L ts).map (renameLocalType ρ) :=
  hLaws.consume_rename ρ from_ L ts

namespace DeliveryModel

/-- FIFO delivery: reuse the existing Consume function. -/
def fifo : DeliveryModel :=
  { consume := Consume }

@[simp] theorem fifo_consume : fifo.consume = Consume := rfl

end DeliveryModel

/-! ## Dedicated FIFO Instance -/

/-- Named FIFO delivery model (alias of `DeliveryModel.fifo`). -/
def FIFODelivery : DeliveryModel :=
  DeliveryModel.fifo

@[simp] theorem FIFODelivery_consume : FIFODelivery.consume = Consume := rfl

/-! ## Additional Delivery Models -/

/-- Causal delivery model.
    Note: with per-edge traces, causal order coincides with FIFO for a single edge. -/
def CausalDelivery : DeliveryModel :=
  DeliveryModel.fifo

@[simp] theorem CausalDelivery_consume : CausalDelivery.consume = Consume := rfl

/-- Lossy delivery model.
    Note: loss is represented by missing trace entries; consume remains FIFO. -/
def LossyDelivery : DeliveryModel :=
  DeliveryModel.fifo

@[simp] theorem LossyDelivery_consume : LossyDelivery.consume = Consume := rfl

namespace DeliveryModelLaws

/-- FIFO satisfies the delivery model laws using existing Consume lemmas. -/
theorem fifo : DeliveryModelLaws DeliveryModel.fifo := by
  refine
    { consume_nil := ?_
      consume_append := ?_
      consume_cons := ?_
      consume_rename := ?_ }
  · intro from_ L
    rfl
  · intro from_ L ts T L' h
    simpa using (Consume_append (from_:=from_) (Lr:=L) (ts:=ts) (T:=T) (L':=L') h)
  · intro from_ L T ts
    simpa using (Consume_cons (from_:=from_) (Lr:=L) (T:=T) (ts:=ts))
  · intro ρ from_ L ts
    simpa using (Consume_rename (ρ:=ρ) (from_:=from_) (L:=L) (ts:=ts))

end DeliveryModelLaws

namespace DeliveryModelLawsStrong

/-- FIFO satisfies the strong delivery model laws using existing Consume lemmas. -/
theorem fifo : DeliveryModelLawsStrong DeliveryModel.fifo := by
  refine
    { toDeliveryModelLaws := DeliveryModelLaws.fifo
      consume_non_recv_empty := ?_
      consume_other_empty := ?_
      consume_recv_single := ?_
      consume_single_recv_match := ?_
      consume_single_branch_string := ?_
      consume_branch_nonempty_false := ?_ }
  · intro from_ L ts L' hNotRecv hNotBranch h
    exact Consume_non_recv_empty (from_:=from_) (L:=L) (ts:=ts) (L':=L') hNotRecv hNotBranch h
  · intro from_ r T L ts L' hNe h
    exact Consume_other_empty (from_:=from_) (r:=r) (T:=T) (L:=L) (ts:=ts) (L':=L') hNe h
  · intro from_ T L
    -- Consume from_ (.recv from_ T L) [T] = Consume from_ L [] = some L
    simpa using (Consume_recv_cons (from_:=from_) (T:=T) (L:=L) (ts:=[]))
  · intro from_ T T' L L' h
    exact Consume_single_recv_match (from_:=from_) (T:=T) (T':=T') (L:=L) (L':=L') h
  · intro from_ bs T L' h
    exact Consume_single_branch_string (from_:=from_) (bs:=bs) (T:=T) (L':=L') h
  · intro from_ r bs t ts L' h
    exact Consume_branch_nonempty_false (from_:=from_) (r:=r) (bs:=bs) (t:=t) (ts:=ts) (L':=L') h

end DeliveryModelLawsStrong

/-! ## FIFO Laws (Named Instance) -/

/-- FIFO laws for the named `FIFODelivery`. -/
theorem FIFODelivery_laws : DeliveryModelLaws FIFODelivery := by
  simpa [FIFODelivery] using DeliveryModelLaws.fifo

/-- Strong FIFO laws for the named `FIFODelivery`. -/
theorem FIFODeliveryStrong_laws : DeliveryModelLawsStrong FIFODelivery := by
  simpa [FIFODelivery] using DeliveryModelLawsStrong.fifo

/-! ## Causal/Lossy Laws -/

/-- Causal delivery satisfies the delivery model laws (via FIFO alias). -/
theorem CausalDelivery_laws : DeliveryModelLaws CausalDelivery := by
  simpa [CausalDelivery] using DeliveryModelLaws.fifo

/-- Lossy delivery satisfies the delivery model laws (via FIFO alias). -/
theorem LossyDelivery_laws : DeliveryModelLaws LossyDelivery := by
  simpa [LossyDelivery] using DeliveryModelLaws.fifo

/-- Strong causal delivery laws (via FIFO alias). -/
theorem CausalDeliveryStrong_laws : DeliveryModelLawsStrong CausalDelivery := by
  simpa [CausalDelivery] using DeliveryModelLawsStrong.fifo

/-- Strong lossy delivery laws (via FIFO alias). -/
theorem LossyDeliveryStrong_laws : DeliveryModelLawsStrong LossyDelivery := by
  simpa [LossyDelivery] using DeliveryModelLawsStrong.fifo
