import Protocol.LocalType

/-! # Runtime.Proofs.ProjectedProtocol

Straight-line (choice-free, recursion-free) global protocols with asynchronous
send state, and their projections to runtime `LocalType`s and edge traces.

A configuration is a list of pending messages `p → q : T`, each flagged `sent`.
A message stays in the list until it is *received*. Role `r`'s local type
(`projP r g`) receives every message addressed to it and sends every message it
owns that is not yet sent; the trace on edge `p → q` (`traceP p q g`) lists the
sent-but-unreceived payloads in order. `SentClosed` says a sent message's sender
had already completed every earlier action it is involved in.

The two operations mirror the frontier actions of `ConcreteTermination`:
`markFirst p` (p sends its head message) and `recvFirst q` (q consumes its head
message). This file proves how they act on projections and traces.

Scope (stated honestly): only `send`/`recv` are modelled. `select`/`branch` are
excluded because `frontierAction` on `select` appends to the type trace but never
enqueues the label into the signed buffer that `branch` reads, so a
select/branch pair cannot complete under the concrete step at all. `mu`/`var`
are excluded because `frontierAction` does not unfold recursion.
-/

/-
The Problem. Progress of the concrete step needs global (not local) duality.

Solution Structure. Model the protocol state as a global message list and prove
operation/projection commutation lemmas by list induction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Runtime.Proofs.Projected

/-! ## Messages and projections -/

/-- A pending message of a straight-line protocol. -/
structure PMsg where
  /-- Sending role. -/
  sender : Role
  /-- Receiving role. -/
  receiver : Role
  /-- Payload type. -/
  ty : ValType
  /-- Has the sender already performed its send? -/
  sent : Bool

/-- Projection of a configuration onto role `r` as a runtime local type. -/
def projP (r : Role) : List PMsg → LocalType
  | [] => .end_
  | m :: g =>
      if m.receiver = r then .recv m.sender m.ty (projP r g)
      else if m.sender = r ∧ m.sent = false then .send m.receiver m.ty (projP r g)
      else projP r g

/-- The trace (sent, unreceived payloads) on edge `p → q`. -/
def traceP (p q : Role) : List PMsg → List ValType
  | [] => []
  | m :: g =>
      if m.sender = p ∧ m.receiver = q ∧ m.sent = true then m.ty :: traceP p q g
      else traceP p q g

/-- Ordering constraint between an earlier message `m` and a later message `m'`:
if `m'` is sent and `m` involves its sender, then `m` was sent by that sender. -/
def SentRel (m m' : PMsg) : Prop :=
  m'.sent = true → (m.sender = m'.sender ∨ m.receiver = m'.sender) →
    m.sent = true ∧ m.sender = m'.sender

/-- Sends respect each sender's local order. -/
def SentClosed (g : List PMsg) : Prop := g.Pairwise SentRel

/-- `p` performs its head send: mark its first pending message sent. -/
def markFirst (p : Role) : List PMsg → List PMsg
  | [] => []
  | m :: g =>
      if m.receiver = p then m :: g
      else if m.sender = p ∧ m.sent = false then { m with sent := true } :: g
      else m :: markFirst p g

/-- `q` performs its head receive: drop its first pending message. -/
def recvFirst (q : Role) : List PMsg → List PMsg
  | [] => []
  | m :: g =>
      if m.receiver = q then g
      else if m.sender = q ∧ m.sent = false then m :: g
      else m :: recvFirst q g

/-! ## Basic facts -/

/-- A non-empty trace has a sent witness on that edge. -/
theorem exists_of_traceP_ne_nil {p q : Role} :
    ∀ {g : List PMsg}, traceP p q g ≠ [] →
      ∃ m ∈ g, m.sender = p ∧ m.receiver = q ∧ m.sent = true
  | [], h => absurd rfl h
  | m :: g, h => by
    unfold traceP at h
    split at h
    · next hc => exact ⟨m, List.mem_cons_self, hc⟩
    · obtain ⟨m', hm', hc⟩ := exists_of_traceP_ne_nil h
      exact ⟨m', List.mem_cons_of_mem _ hm', hc⟩

/-- Projections are never `select`, `branch`, `mu` or `var`: they are built from
`send`, `recv` and `end_` only. -/
theorem projP_cases (r : Role) :
    ∀ g : List PMsg, projP r g = .end_ ∨ (∃ t T L, projP r g = .send t T L) ∨
      (∃ s T L, projP r g = .recv s T L)
  | [] => Or.inl rfl
  | m :: g => by
    unfold projP
    split
    · exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
    · split
      · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
      · exact projP_cases r g

/-- `recvFirst` returns a sublist. -/
theorem recvFirst_sublist (q : Role) : ∀ g : List PMsg, (recvFirst q g).Sublist g
  | [] => List.Sublist.slnil
  | m :: g => by
    unfold recvFirst
    split
    · exact List.sublist_cons_self _ _
    · split
      · exact List.Sublist.refl _
      · exact (recvFirst_sublist q g).cons₂ m

/-- Every message of `markFirst p g` agrees with one of `g` on its endpoints and
is either unchanged or a (now sent) message of `p`. -/
theorem mem_markFirst {p : Role} : ∀ {g : List PMsg} {b : PMsg}, b ∈ markFirst p g →
    ∃ a ∈ g, a.sender = b.sender ∧ a.receiver = b.receiver ∧ (a = b ∨ b.sender = p)
  | [], _, h => by simp [markFirst] at h
  | m :: g, b, h => by
    unfold markFirst at h
    split at h
    · exact ⟨b, h, rfl, rfl, Or.inl rfl⟩
    · split at h
      · next hc =>
        rcases List.mem_cons.mp h with rfl | hb
        · exact ⟨m, List.mem_cons_self, rfl, rfl, Or.inr hc.1⟩
        · exact ⟨b, List.mem_cons_of_mem _ hb, rfl, rfl, Or.inl rfl⟩
      · rcases List.mem_cons.mp h with rfl | hb
        · exact ⟨b, List.mem_cons_self, rfl, rfl, Or.inl rfl⟩
        · obtain ⟨a, ha, h1, h2, h3⟩ := mem_markFirst hb
          exact ⟨a, List.mem_cons_of_mem _ ha, h1, h2, h3⟩

/-! ## `markFirst` (send) -/

/-- `markFirst` preserves `SentClosed`. -/
theorem sentClosed_markFirst (p : Role) :
    ∀ {g : List PMsg}, SentClosed g → SentClosed (markFirst p g)
  | [], _ => List.Pairwise.nil
  | m :: g, h => by
    have hcons := List.pairwise_cons.mp h
    unfold markFirst
    split
    · exact h
    · split
      · next hc =>
        refine List.pairwise_cons.mpr ⟨fun b hb hs hinv => ?_, hcons.2⟩
        have := hcons.1 b hb hs hinv
        simp [hc.2] at this
      · next hr hc =>
        refine List.pairwise_cons.mpr ⟨fun b hb hs hinv => ?_, sentClosed_markFirst p hcons.2⟩
        obtain ⟨a, ha, h1, h2, h3⟩ := mem_markFirst hb
        rcases h3 with rfl | hbp
        · exact hcons.1 a ha hs hinv
        · have hmp : m.sender = p := by
            rcases hinv with h' | h'
            · rw [h', hbp]
            · exact absurd (h'.trans hbp) hr
          refine ⟨?_, hmp.trans hbp.symm⟩
          cases hsent : m.sent
          · exact absurd ⟨hmp, hsent⟩ hc
          · rfl

/-- After `p` sends, its projection is the continuation. -/
theorem projP_markFirst_self {p q : Role} {T : ValType} {L : LocalType} :
    ∀ {g : List PMsg}, projP p g = .send q T L → projP p (markFirst p g) = L
  | [], h => by simp [projP] at h
  | m :: g, h => by
    by_cases hr : m.receiver = p
    · rw [projP, if_pos hr] at h; cases h
    rw [projP, if_neg hr] at h
    rw [markFirst, if_neg hr]
    by_cases hc : m.sender = p ∧ m.sent = false
    · rw [if_pos hc] at h
      rw [if_pos hc, projP, if_neg hr, if_neg (by simp)]
      exact (LocalType.send.inj h).2.2
    · rw [if_neg hc] at h
      rw [if_neg hc, projP, if_neg hr, if_neg hc]
      exact projP_markFirst_self h

/-- `p` sending leaves every other role's projection unchanged. -/
theorem projP_markFirst_other {p r : Role} (hne : r ≠ p) :
    ∀ g : List PMsg, projP r (markFirst p g) = projP r g
  | [] => rfl
  | m :: g => by
    rw [markFirst]
    by_cases hr : m.receiver = p
    · rw [if_pos hr]
    rw [if_neg hr]
    by_cases hc : m.sender = p ∧ m.sent = false
    · have hs : ¬ (m.sender = r) := fun h => hne (h.symm.trans hc.1)
      rw [if_pos hc, projP, projP]
      simp only [hs, false_and, if_false]
    · rw [if_neg hc, projP, projP, projP_markFirst_other hne g]

/-- `p` sending to `q` appends `T` to the `p → q` trace. -/
theorem traceP_markFirst_self {p q : Role} {T : ValType} {L : LocalType} :
    ∀ {g : List PMsg}, SentClosed g → projP p g = .send q T L →
      traceP p q (markFirst p g) = traceP p q g ++ [T]
  | [], _, h => by simp [projP] at h
  | m :: g, hC, h => by
    have hcons := List.pairwise_cons.mp hC
    by_cases hr : m.receiver = p
    · rw [projP, if_pos hr] at h; cases h
    rw [projP, if_neg hr] at h
    rw [markFirst, if_neg hr]
    by_cases hc : m.sender = p ∧ m.sent = false
    · rw [if_pos hc] at h
      obtain ⟨hq, hT, -⟩ := LocalType.send.inj h
      subst hq hT
      have hnil : traceP p m.receiver g = [] := by
        by_contra hne
        obtain ⟨b, hb, hbs, -, hbsent⟩ := exists_of_traceP_ne_nil hne
        have := hcons.1 b hb hbsent (Or.inl (hc.1.trans hbs.symm))
        simp [hc.2] at this
      rw [if_pos hc]
      simp [traceP, hc.1, hc.2, hnil]
    · rw [if_neg hc] at h
      rw [if_neg hc, traceP, traceP, traceP_markFirst_self hcons.2 h]
      split <;> simp

/-- `p` sending to `q` leaves every other edge's trace unchanged. -/
theorem traceP_markFirst_other {p q p' q' : Role} {T : ValType} {L : LocalType}
    (hne : ¬ (p' = p ∧ q' = q)) :
    ∀ {g : List PMsg}, projP p g = .send q T L →
      traceP p' q' (markFirst p g) = traceP p' q' g
  | [], h => by simp [projP] at h
  | m :: g, h => by
    by_cases hr : m.receiver = p
    · rw [projP, if_pos hr] at h; cases h
    rw [projP, if_neg hr] at h
    rw [markFirst, if_neg hr]
    by_cases hc : m.sender = p ∧ m.sent = false
    · rw [if_pos hc] at h
      obtain ⟨hq, -, -⟩ := LocalType.send.inj h
      have hx : ¬ (m.sender = p' ∧ m.receiver = q') := fun h' =>
        hne ⟨h'.1.symm.trans hc.1, h'.2.symm.trans hq⟩
      rw [if_pos hc, traceP, traceP]
      rw [if_neg (fun h' => hx ⟨h'.1, h'.2.1⟩), if_neg (fun h' => hx ⟨h'.1, h'.2.1⟩)]
    · rw [if_neg hc] at h
      rw [if_neg hc, traceP, traceP, traceP_markFirst_other hne h]

/-! ## `recvFirst` (receive) -/

/-- `recvFirst` preserves `SentClosed`. -/
theorem sentClosed_recvFirst (q : Role) {g : List PMsg} (h : SentClosed g) :
    SentClosed (recvFirst q g) :=
  List.Pairwise.sublist (recvFirst_sublist q g) h

/-- After `q` receives, its projection is the continuation. -/
theorem projP_recvFirst_self {q p : Role} {T : ValType} {L : LocalType} :
    ∀ {g : List PMsg}, projP q g = .recv p T L → projP q (recvFirst q g) = L
  | [], h => by simp [projP] at h
  | m :: g, h => by
    unfold projP at h
    unfold recvFirst
    split at h
    · cases h; simp [*]
    · next hr =>
      split at h
      · cases h
      · next hc => simp [projP, hr, hc, projP_recvFirst_self h]

/-- If `q` is at `recv p` and the `p → q` trace is non-empty, then the head
message of `q` is already sent (by `SentClosed`). -/
theorem recv_head_sent {q p : Role} {T : ValType} {L : LocalType} :
    ∀ {m : PMsg} {g : List PMsg}, SentClosed (m :: g) → projP q (m :: g) = .recv p T L →
      traceP p q (m :: g) ≠ [] → m.receiver = q → m.sent = true
  | m, g, hC, h, hT, hr => by
    have hcons := List.pairwise_cons.mp hC
    rw [projP, if_pos hr] at h
    cases h
    cases hs : m.sent
    · exfalso
      have hT' : traceP m.sender q g ≠ [] := by simpa [traceP, hs] using hT
      obtain ⟨b, hb, hbs, -, hbsent⟩ := exists_of_traceP_ne_nil hT'
      have := hcons.1 b hb hbsent (Or.inl hbs.symm)
      simp [hs] at this
    · rfl

/-- Unfolding one skipped message of `q`'s receive search. -/
theorem recv_skip {q p : Role} {T : ValType} {L : LocalType} {m : PMsg} {g : List PMsg}
    (hr : ¬ m.receiver = q) (h : projP q (m :: g) = .recv p T L) :
    ¬ (m.sender = q ∧ m.sent = false) ∧ projP q g = .recv p T L := by
  rw [projP, if_neg hr] at h
  by_cases hc : m.sender = q ∧ m.sent = false
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h; exact ⟨hc, h⟩

/-- `q` receiving leaves every other role's projection unchanged. -/
theorem projP_recvFirst_other {q p r : Role} {T : ValType} {L : LocalType} (hne : r ≠ q) :
    ∀ {g : List PMsg}, SentClosed g → projP q g = .recv p T L → traceP p q g ≠ [] →
      projP r (recvFirst q g) = projP r g
  | [], _, h, _ => by simp [projP] at h
  | m :: g, hC, h, hT => by
    by_cases hr : m.receiver = q
    · have hs := recv_head_sent hC h hT hr
      have hmr : ¬ m.receiver = r := fun h' => hne (h'.symm.trans hr)
      rw [recvFirst, if_pos hr, projP, if_neg hmr, if_neg (by simp [hs])]
    · obtain ⟨hc, h'⟩ := recv_skip hr h
      have hT' : traceP p q g ≠ [] := by
        intro hn; apply hT; rw [traceP, if_neg (fun h'' => hr h''.2.1), hn]
      rw [recvFirst, if_neg hr, if_neg hc, projP, projP,
        projP_recvFirst_other hne (List.pairwise_cons.mp hC).2 h' hT']

/-- `q` receiving from `p` pops the head of the `p → q` trace. -/
theorem traceP_recvFirst_self {q p : Role} {T : ValType} {L : LocalType} :
    ∀ {g : List PMsg}, SentClosed g → projP q g = .recv p T L → traceP p q g ≠ [] →
      traceP p q (recvFirst q g) = (traceP p q g).tail
  | [], _, h, _ => by simp [projP] at h
  | m :: g, hC, h, hT => by
    by_cases hr : m.receiver = q
    · have hs := recv_head_sent hC h hT hr
      have h' := h
      rw [projP, if_pos hr] at h'
      obtain ⟨hp, -, -⟩ := LocalType.recv.inj h'
      rw [recvFirst, if_pos hr, traceP, if_pos ⟨hp, hr, hs⟩, List.tail_cons]
    · obtain ⟨hc, h'⟩ := recv_skip hr h
      have hskip : ∀ x, traceP p q (m :: x) = traceP p q x := fun x => by
        rw [traceP, if_neg (fun h'' => hr h''.2.1)]
      have hT' : traceP p q g ≠ [] := by rw [← hskip]; exact hT
      rw [recvFirst, if_neg hr, if_neg hc, hskip, hskip,
        traceP_recvFirst_self (List.pairwise_cons.mp hC).2 h' hT']

/-- `q` receiving from `p` leaves every other edge's trace unchanged. -/
theorem traceP_recvFirst_other {q p p' q' : Role} {T : ValType} {L : LocalType}
    (hne : ¬ (p' = p ∧ q' = q)) :
    ∀ {g : List PMsg}, SentClosed g → projP q g = .recv p T L → traceP p q g ≠ [] →
      traceP p' q' (recvFirst q g) = traceP p' q' g
  | [], _, h, _ => by simp [projP] at h
  | m :: g, hC, h, hT => by
    by_cases hr : m.receiver = q
    · have h' := h
      rw [projP, if_pos hr] at h'
      obtain ⟨hp, -, -⟩ := LocalType.recv.inj h'
      rw [recvFirst, if_pos hr, traceP,
        if_neg (fun h'' => hne ⟨h''.1.symm.trans hp, h''.2.1.symm.trans hr⟩)]
    · obtain ⟨hc, h'⟩ := recv_skip hr h
      have hT' : traceP p q g ≠ [] := by
        intro hn; apply hT; rw [traceP, if_neg (fun h'' => hr h''.2.1), hn]
      rw [recvFirst, if_neg hr, if_neg hc, traceP, traceP,
        traceP_recvFirst_other hne (List.pairwise_cons.mp hC).2 h' hT']

end Runtime.Proofs.Projected
