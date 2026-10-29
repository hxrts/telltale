import Protocol.Coherence

/-! # Survivor Drain for Crash Tolerance

After crashed roles are removed from a coherent configuration, the surviving
participants can deliver every in-flight message on every surviving edge by a
finite run of receive steps, reaching a coherent, quiescent configuration.

## Expose

- `removeCrashed` : drop all endpoints owned by crashed roles
- `DeliverStep` : one receive step (head of a trace consumed by a ready receiver)
- `Quiescent` : no in-flight messages on any active edge
- `SessionCanComplete` : survivors can drain to a coherent quiescent configuration
- `survivors_can_complete` : coherence implies `SessionCanComplete`
-/

/-
The Problem. A crash-tolerance completion notion must be a genuine reachability
statement, not a restatement of coherence.

Solution Structure. Define receive-step runs on `(GEnv × DEnv)`, a Nat-valued
load measure over all key pairs, prove coherence gives an enabled step whenever
some active edge is non-empty (progress), that steps preserve coherence
(`coherent_recv_preserved`), and that the load strictly decreases. Well-founded
recursion then yields the drain run.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Survivor Configurations -/

/-- Remove every endpoint owned by a crashed role. -/
def removeCrashed (G : GEnv) (crashed : List Role) : GEnv :=
  G.filter (fun p => decide (p.1.role ∉ crashed))

/-- Lookup in the survivor environment: crashed endpoints vanish, others are unchanged. -/
theorem lookup_g_remove_crashed (G : GEnv) (crashed : List Role) (ep : Endpoint) :
    lookupG (removeCrashed G crashed) ep = if ep.role ∈ crashed then none else lookupG G ep := by
  induction G with
  | nil => simp [removeCrashed, lookupG]
  | cons hd tl ih =>
      obtain ⟨ep', L'⟩ := hd
      simp only [removeCrashed, lookupG] at ih ⊢
      by_cases hc : ep'.role ∈ crashed
      · rw [List.filter_cons_of_neg (by simp [hc]), ih]
        by_cases hr : ep.role ∈ crashed
        · simp [hr]
        · have hne : ep ≠ ep' := by rintro rfl; exact hr hc
          simp [hr, List.lookup, beq_eq_false_iff_ne.mpr hne]
      · rw [List.filter_cons_of_pos (by simp [hc])]
        by_cases he : ep = ep'
        · subst he; simp [List.lookup, hc]
        · simp only [List.lookup, beq_eq_false_iff_ne.mpr he, ih]

/-- Removing crashed roles preserves coherence. -/
theorem coherent_remove_crashed {G : GEnv} {D : DEnv} (crashed : List Role)
    (hCoh : Coherent G D) : Coherent (removeCrashed G crashed) D := by
  have hEq : ∀ ep, (lookupG (removeCrashed G crashed) ep).isSome →
      lookupG (removeCrashed G crashed) ep = lookupG G ep := by
    intro ep hs
    rw [lookup_g_remove_crashed] at hs ⊢
    split_ifs at hs ⊢ with h
    · simp at hs
    · rfl
  intro e hAct
  have hS := hEq _ hAct.1
  have hR := hEq _ hAct.2
  have hActG : ActiveEdge G e := ⟨hS ▸ hAct.1, hR ▸ hAct.2⟩
  have hEC := hCoh e hActG
  simp only [EdgeCoherent] at hEC ⊢
  intro Lrecv hRecv
  rw [hR] at hRecv
  obtain ⟨Ls, hLs, hC⟩ := hEC Lrecv hRecv
  exact ⟨Ls, hS.trans hLs, hC⟩

/-! ## Delivery Steps -/

/-- The edge on which endpoint `ep` receives from role `p`. -/
def inEdge (ep : Endpoint) (p : Role) : Edge :=
  { sid := ep.sid, sender := p, receiver := ep.role }

/-- The receive edge of an edge's receiver endpoint is the edge itself. -/
theorem in_edge_receiver (e : Edge) :
    inEdge { sid := e.sid, role := e.receiver } e.sender = e := rfl

/-- One delivery step: a receiver at `recv p T L` consumes the head `T` of its in-edge. -/
inductive DeliverStep : GEnv × DEnv → GEnv × DEnv → Prop where
  | recv (G : GEnv) (D : DEnv) (ep : Endpoint) (p : Role) (T : ValType) (L : LocalType)
      (hG : lookupG G ep = some (.recv p T L))
      (hHead : (lookupD D (inEdge ep p)).head? = some T) :
      DeliverStep (G, D) (updateG G ep L, updateD D (inEdge ep p) (lookupD D (inEdge ep p)).tail)

/-- Delivery steps preserve coherence (via `coherent_recv_preserved`). -/
theorem deliver_preserves_coherent {C C' : GEnv × DEnv} (h : DeliverStep C C')
    (hCoh : Coherent C.1 C.2) : Coherent C'.1 C'.2 := by
  cases h with
  | recv G D ep p T L hG hHead => exact coherent_recv_preserved G D ep p T L hCoh hG hHead

/-- No in-flight messages remain on any active edge. -/
def Quiescent (G : GEnv) (D : DEnv) : Prop :=
  ∀ e, ActiveEdge G e → lookupD D e = []

/-- Survivors can complete the in-flight phase: from the configuration with the
    crashed roles removed there is a finite run of delivery steps reaching a
    coherent configuration with every surviving edge empty. -/
def SessionCanComplete (G : GEnv) (D : DEnv) (crashed : List Role) : Prop :=
  ∃ G' D', Relation.ReflTransGen DeliverStep (removeCrashed G crashed, D) (G', D') ∧
    Coherent G' D' ∧ Quiescent G' D'

/-! ## Load Measure -/

/-- All edges spanned by same-session pairs of keys (first key's role sends to the second). -/
def keyEdges (ks : List Endpoint) : List Edge :=
  ks.flatMap fun a => (ks.filter fun b => decide (b.sid = a.sid)).map fun b =>
    { sid := b.sid, sender := a.role, receiver := b.role }

/-- Total in-flight load over all key-pair edges. -/
def drainMeasure (G : GEnv) (D : DEnv) : Nat :=
  ((keyEdges (G.map Prod.fst)).map fun e => (lookupD D e).length).sum

/-- Updating an existing endpoint does not change the key list. -/
theorem update_g_keys {G : GEnv} {ep : Endpoint} {L : LocalType}
    (h : (lookupG G ep).isSome) : (updateG G ep L).map Prod.fst = G.map Prod.fst := by
  induction G with
  | nil => simp [lookupG] at h
  | cons hd tl ih =>
      obtain ⟨ep', L'⟩ := hd
      by_cases he : ep = ep'
      · subst he; simp [updateG]
      · have hne : (ep == ep') = false := beq_eq_false_iff_ne.mpr he
        have h' : (lookupG tl ep).isSome := by simpa [lookupG, List.lookup, hne] using h
        simp [updateG, he, ih h']

/-- Every active edge is a key-pair edge. -/
theorem edge_mem_key_edges {G : GEnv} {e : Edge} (hAct : ActiveEdge G e) :
    e ∈ keyEdges (G.map Prod.fst) := by
  obtain ⟨Ls, hS⟩ := Option.isSome_iff_exists.mp hAct.1
  obtain ⟨Lr, hR⟩ := Option.isSome_iff_exists.mp hAct.2
  have h1 := List.mem_map_of_mem (f := Prod.fst) (lookup_g_mem _ _ _ hS)
  have h2 := List.mem_map_of_mem (f := Prod.fst) (lookup_g_mem _ _ _ hR)
  exact List.mem_flatMap.2 ⟨_, h1, List.mem_map.2 ⟨_, List.mem_filter.2 ⟨h2, by simp⟩, rfl⟩⟩

/-- A key of `G` has a lookup. -/
theorem lookup_g_some_of_key {G : GEnv} {ep : Endpoint} (h : ep ∈ G.map Prod.fst) :
    (lookupG G ep).isSome := by
  induction G with
  | nil => simp at h
  | cons hd tl ih =>
      obtain ⟨ep', L'⟩ := hd
      by_cases he : ep = ep'
      · subst he; simp [lookupG, List.lookup]
      · have hne : (ep == ep') = false := beq_eq_false_iff_ne.mpr he
        rw [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h he
        · simpa [lookupG, List.lookup, hne] using ih h

/-- Every key-pair edge is active. -/
theorem key_edge_active {G : GEnv} {e : Edge} (h : e ∈ keyEdges (G.map Prod.fst)) :
    ActiveEdge G e := by
  obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp h
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
  have hb' := List.mem_filter.mp hb
  simp only [decide_eq_true_eq] at hb'
  refine ⟨?_, lookup_g_some_of_key hb'.1⟩
  have hEq : ({ sid := b.sid, role := a.role } : Endpoint) = a := by rw [hb'.2]
  show (lookupG G { sid := b.sid, role := a.role }).isSome
  rw [hEq]
  exact lookup_g_some_of_key ha

/-- A quiescent configuration has zero load. -/
theorem drain_measure_zero_of_quiescent {G : GEnv} {D : DEnv} (hQ : Quiescent G D) :
    drainMeasure G D = 0 := by
  unfold drainMeasure
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  simp [hQ e (key_edge_active he)]

/-- Pointwise `≤` on a list gives `≤` on sums. -/
theorem sum_map_le_of_le {α : Type*} (l : List α) (f g : α → Nat)
    (hle : ∀ x ∈ l, g x ≤ f x) : (l.map g).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := hle a (by simp)
      have := ih (fun x hx => hle x (by simp [hx]))
      omega

/-- Pointwise `≤` with one strict entry gives `<` on sums. -/
theorem sum_map_lt_of_lt {α : Type*} (l : List α) (f g : α → Nat)
    (hle : ∀ x ∈ l, g x ≤ f x) (hlt : ∃ x ∈ l, g x < f x) :
    (l.map g).sum < (l.map f).sum := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hlt; cases hx
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hle' : ∀ x ∈ l, g x ≤ f x := fun x hx => hle x (by simp [hx])
      have ha := hle a (by simp)
      obtain ⟨x, hx, hxlt⟩ := hlt
      rcases List.mem_cons.mp hx with rfl | hx
      · have := sum_map_le_of_le l f g hle'; omega
      · have := ih hle' ⟨x, hx, hxlt⟩; omega

/-- Delivering the head of a non-empty active edge strictly decreases the load. -/
theorem drain_measure_lt {G : GEnv} {D : DEnv} {e : Edge} {L : LocalType}
    {T : ValType} {ts : List ValType} (hAct : ActiveEdge G e) (hTr : lookupD D e = T :: ts) :
    drainMeasure (updateG G { sid := e.sid, role := e.receiver } L) (updateD D e ts) <
      drainMeasure G D := by
  unfold drainMeasure
  rw [update_g_keys hAct.2]
  apply sum_map_lt_of_lt
  · intro x _
    by_cases hx : x = e
    · subst hx; rw [lookup_d_update_eq, hTr]; simp
    · rw [lookup_d_update_neq _ _ _ _ (Ne.symm hx)]
  · refine ⟨e, edge_mem_key_edges hAct, ?_⟩
    rw [lookup_d_update_eq, hTr]; simp

/-! ## Progress and Drain -/

/-- Inversion of a successful single consume step. -/
theorem consume_one_inv {p : Role} {T : ValType} {L L' : LocalType}
    (h : consumeOne p T L = some L') : L = .recv p T L' := by
  cases L <;> simp only [consumeOne, reduceCtorEq] at h
  rename_i r T' K
  split_ifs at h with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  cases h
  rfl

/-- A consume of a non-empty trace begins with a successful single consume. -/
theorem consume_cons_head {p : Role} {L : LocalType} {T : ValType} {ts : List ValType}
    (h : (Consume p L (T :: ts)).isSome) : ∃ L', consumeOne p T L = some L' := by
  simp only [Consume] at h
  cases hc : consumeOne p T L with
  | none => rw [hc] at h; simp at h
  | some L' => exact ⟨L', rfl⟩

/-- Progress: in a coherent, non-quiescent configuration some delivery is enabled,
    and it strictly decreases the load. -/
theorem deliver_progress {G : GEnv} {D : DEnv} (hCoh : Coherent G D)
    (hQ : ¬ Quiescent G D) :
    ∃ G₁ D₁, DeliverStep (G, D) (G₁, D₁) ∧ drainMeasure G₁ D₁ < drainMeasure G D := by
  simp only [Quiescent] at hQ
  push_neg at hQ
  obtain ⟨e, hAct, hNe⟩ := hQ
  obtain ⟨T, ts, hTr⟩ := List.exists_cons_of_ne_nil hNe
  obtain ⟨Lrecv, hRecv⟩ := Option.isSome_iff_exists.mp hAct.2
  have hEC := hCoh e hAct
  simp only [EdgeCoherent] at hEC
  obtain ⟨_, _, hCons⟩ := hEC Lrecv hRecv
  rw [hTr] at hCons
  obtain ⟨L', hOne⟩ := consume_cons_head hCons
  have hInv := consume_one_inv hOne
  subst hInv
  have hHead : (lookupD D (inEdge { sid := e.sid, role := e.receiver } e.sender)).head? = some T := by
    rw [in_edge_receiver, hTr]; rfl
  refine ⟨_, _, DeliverStep.recv G D _ e.sender T L' hRecv hHead, ?_⟩
  rw [in_edge_receiver, hTr]
  exact drain_measure_lt hAct hTr

/-- Every coherent configuration drains to a coherent quiescent one. -/
theorem drain_of_coherent (G : GEnv) (D : DEnv) (hCoh : Coherent G D) :
    ∃ G' D', Relation.ReflTransGen DeliverStep (G, D) (G', D') ∧
      Coherent G' D' ∧ Quiescent G' D' := by
  by_cases hQ : Quiescent G D
  · exact ⟨G, D, .refl, hCoh, hQ⟩
  · obtain ⟨G₁, D₁, hStep, hLt⟩ := deliver_progress hCoh hQ
    obtain ⟨G', D', hRun, hCoh', hQ'⟩ :=
      drain_of_coherent G₁ D₁ (deliver_preserves_coherent hStep hCoh)
    exact ⟨G', D', .head hStep hRun, hCoh', hQ'⟩
termination_by drainMeasure G D
decreasing_by exact hLt

/-- Survivors of any crash set can complete the in-flight phase of a coherent session. -/
theorem survivors_can_complete (G : GEnv) (D : DEnv) (crashed : List Role)
    (hCoh : Coherent G D) : SessionCanComplete G D crashed :=
  drain_of_coherent _ _ (coherent_remove_crashed crashed hCoh)

end
