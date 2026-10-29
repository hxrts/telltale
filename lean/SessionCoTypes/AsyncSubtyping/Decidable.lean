import SessionCoTypes.AsyncSubtyping.Core

/-! # Sound Semi-Decision Procedure for Async Subtyping

Asynchronous session subtyping is undecidable in general, even for regular
(finite-state) session types (Bravetti–Carbone–Zavattaro 2017; Lange–Yoshida
2017). Hence no total, sound and complete checker exists, and this module does
not claim one.

Instead it provides a *bounded, sound* exploration `checkAsync`:
- it unfolds a worklist of triples `(S, T, buffer)`, choosing one `AsyncStep`
  rule per triple (a fixed strategy, see `stepTriple`);
- cycles are closed using a caller-supplied equality test `eqb` on
  `LocalTypeC` that must be *sound* (`eqb a b = true → a = b`); the trivial
  test `fun _ _ => false` is always sound and only accepts finite derivations;
- it returns `.accepted` only if the explored set is closed under the chosen
  steps, which is a coinductive witness for `AsyncSubtypeRel`;
- `.stuck` (the strategy found no applicable rule) and `.outOfFuel` (bound
  exhausted) are *inconclusive*: neither refutes subtyping.

## Main Results

- `explore_sound` : acceptance from a `ConsistentVisited` state implies the
  relation for every visited or pending triple
- `check_async_sound` : `checkAsync eqb fuel S T = .accepted → S ≤ₐ T` -/

set_option linter.dupNamespace false

namespace SessionCoTypes.AsyncSubtyping

open SessionCoTypes.Coinductive
open SessionTypes.GlobalType

/-! ## Child Access -/

/-- Children of `t`, re-indexed along a known head equation. -/
noncomputable def childAt (t : LocalTypeC) {hd : LocalTypeHead} (h : head t = hd)
    (i : LocalTypeChild hd) : LocalTypeC :=
  children t (cast (congrArg LocalTypeChild h).symm i)

/-- Every re-indexed child is a `childRel` child. -/
theorem childRel_childAt (t : LocalTypeC) {hd : LocalTypeHead} (h : head t = hd)
    (i : LocalTypeChild hd) : childRel t (childAt t h i) :=
  ⟨head t, children t, _, rfl, rfl⟩

/-! ## Single-Rule Successor Functions

Each rule returns `some succs` only when the matching `AsyncStep`
constructor applies with exactly those successors. -/

/-- Unfold a `mu` on the subtype side. -/
noncomputable def ruleUnfoldSub (t : AsyncTriple) : Option (List AsyncTriple) :=
  match h : head t.sub with
  | .mu _ => some [⟨childAt t.sub h (), t.sup, t.buffer⟩]
  | _ => none

/-- Unfold a `mu` on the supertype side. -/
noncomputable def ruleUnfoldSup (t : AsyncTriple) : Option (List AsyncTriple) :=
  match h : head t.sup with
  | .mu _ => some [⟨t.sub, childAt t.sup h (), t.buffer⟩]
  | _ => none

/-- Both sides send to the same peer with the same labels. -/
noncomputable def ruleBothSend (t : AsyncTriple) : Option (List AsyncTriple) :=
  match hS : head t.sub, hT : head t.sup with
  | .send p ls, .send q ms =>
      if hp : q = p ∧ ms = ls then
        some (List.ofFn fun i : Fin ls.length =>
          ⟨childAt t.sub hS i,
            childAt (hd := .send p ls) t.sup (by rw [hT, hp.1, hp.2]) i, t.buffer⟩)
      else none
  | _, _ => none

/-- Both sides receive from the same peer with the same labels. -/
noncomputable def ruleBothRecv (t : AsyncTriple) : Option (List AsyncTriple) :=
  match hS : head t.sub, hT : head t.sup with
  | .recv p ls, .recv q ms =>
      if hp : q = p ∧ ms = ls then
        some (List.ofFn fun i : Fin ls.length =>
          ⟨childAt t.sub hS i,
            childAt (hd := .recv p ls) t.sup (by rw [hT, hp.1, hp.2]) i, t.buffer⟩)
      else none
  | _, _ => none

/-- The supertype receives the head of the buffer. -/
noncomputable def ruleSupRecv (t : AsyncTriple) : Option (List AsyncTriple) :=
  match hT : head t.sup, t.buffer with
  | .recv _ ls, msg :: rest =>
      match (List.finRange ls.length).find? (fun i => decide (ls.get i = msg)) with
      | some idx => some [⟨t.sub, childAt t.sup hT idx, rest⟩]
      | none => none
  | _, _ => none

/-- The subtype sends asynchronously; the label is buffered. -/
noncomputable def ruleSubSend (t : AsyncTriple) : Option (List AsyncTriple) :=
  match hS : head t.sub with
  | .send _ ls => some (List.ofFn fun i : Fin ls.length =>
      ⟨childAt t.sub hS i, t.sup, t.buffer ++ [ls.get i]⟩)
  | _ => none

/-! ## Rule Soundness -/

/-- `ruleUnfoldSub` produces an `AsyncStep`. -/
theorem ruleUnfoldSub_sound {t : AsyncTriple} {s : List AsyncTriple}
    (h : ruleUnfoldSub t = some s) : AsyncStep t s := by
  obtain ⟨S, T, buf⟩ := t
  unfold ruleUnfoldSub at h; split at h <;> cases h
  exact .unfold_sub _ ‹_› (childRel_childAt _ _ _)

/-- `ruleUnfoldSup` produces an `AsyncStep`. -/
theorem ruleUnfoldSup_sound {t : AsyncTriple} {s : List AsyncTriple}
    (h : ruleUnfoldSup t = some s) : AsyncStep t s := by
  obtain ⟨S, T, buf⟩ := t
  unfold ruleUnfoldSup at h; split at h <;> cases h
  exact .unfold_sup _ ‹_› (childRel_childAt _ _ _)

/-- `ruleBothSend` produces an `AsyncStep`. -/
theorem ruleBothSend_sound {t : AsyncTriple} {s : List AsyncTriple}
    (h : ruleBothSend t = some s) : AsyncStep t s := by
  obtain ⟨S, T, buf⟩ := t
  unfold ruleBothSend at h; split at h
  · rename_i hS hT
    split at h
    · rename_i hp
      cases h
      exact .both_send hS (by rw [← hp.1, ← hp.2]; exact hT) _ _
        (fun _ => childRel_childAt _ _ _) (fun _ => childRel_childAt _ _ _)
    · cases h
  · cases h

/-- `ruleBothRecv` produces an `AsyncStep`. -/
theorem ruleBothRecv_sound {t : AsyncTriple} {s : List AsyncTriple}
    (h : ruleBothRecv t = some s) : AsyncStep t s := by
  obtain ⟨S, T, buf⟩ := t
  unfold ruleBothRecv at h; split at h
  · rename_i hS hT
    split at h
    · rename_i hp
      cases h
      exact .both_recv hS (by rw [← hp.1, ← hp.2]; exact hT) _ _
        (fun _ => childRel_childAt _ _ _) (fun _ => childRel_childAt _ _ _)
    · cases h
  · cases h

/-- `ruleSupRecv` produces an `AsyncStep`. -/
theorem ruleSupRecv_sound {t : AsyncTriple} {s : List AsyncTriple}
    (h : ruleSupRecv t = some s) : AsyncStep t s := by
  obtain ⟨S, T, buf⟩ := t
  unfold ruleSupRecv at h; split at h
  · rename_i ls msg rest hT hB
    split at h
    · rename_i idx hFind
      cases h
      have hIdx : ls.get idx = msg := by simpa using List.find?_some hFind
      exact .sup_recv_buffer hT hB (List.mem_iff_get.mpr ⟨idx, hIdx⟩) _
        (childRel_childAt _ hT) idx hIdx
    · cases h
  · cases h

/-- `ruleSubSend` produces an `AsyncStep`. -/
theorem ruleSubSend_sound {t : AsyncTriple} {s : List AsyncTriple}
    (h : ruleSubSend t = some s) : AsyncStep t s := by
  obtain ⟨S, T, buf⟩ := t
  unfold ruleSubSend at h; split at h <;> cases h
  exact .sub_send_async ‹_› _ (fun _ => childRel_childAt _ _ _)

/-! ## Step Strategy -/

/-- The fixed rule order used by the checker. -/
noncomputable def asyncRules : List (AsyncTriple → Option (List AsyncTriple)) :=
  [ruleUnfoldSub, ruleUnfoldSup, ruleBothSend, ruleBothRecv, ruleSupRecv, ruleSubSend]

/-- Every rule in `asyncRules` is sound. -/
theorem asyncRules_sound {r : AsyncTriple → Option (List AsyncTriple)} (hr : r ∈ asyncRules)
    {t : AsyncTriple} {s : List AsyncTriple} (h : r t = some s) : AsyncStep t s := by
  simp only [asyncRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ruleUnfoldSub_sound h
  · exact ruleUnfoldSup_sound h
  · exact ruleBothSend_sound h
  · exact ruleBothRecv_sound h
  · exact ruleSupRecv_sound h
  · exact ruleSubSend_sound h

/-- Result of one strategy step on a triple. -/
inductive StepResult where
  /-- Base case: both end with an empty buffer. -/
  | accept : StepResult
  /-- Successors produced by one `AsyncStep` rule. -/
  | continue (succs : List AsyncTriple) : StepResult
  /-- No rule of the strategy applies (inconclusive, not a refutation). -/
  | reject : StepResult

/-- Apply the strategy to one triple. -/
noncomputable def stepTriple (t : AsyncTriple) : StepResult :=
  if head t.sub = .end ∧ head t.sup = .end ∧ t.buffer = [] then .accept
  else match asyncRules.findSome? (fun r => r t) with
    | some s => .continue s
    | none => .reject

/-- `.accept` is only returned in the base case. -/
theorem stepTriple_accept {t : AsyncTriple} (h : stepTriple t = .accept) :
    head t.sub = .end ∧ head t.sup = .end ∧ t.buffer = [] := by
  unfold stepTriple at h
  split at h
  · assumption
  · split at h <;> cases h

/-- `.continue succs` is only returned for a genuine `AsyncStep`. -/
theorem stepTriple_continue {t : AsyncTriple} {s : List AsyncTriple}
    (h : stepTriple t = .continue s) : AsyncStep t s := by
  unfold stepTriple at h
  split at h
  · cases h
  · split at h
    · rename_i s' hs
      cases h
      obtain ⟨r, hr, hrt⟩ := List.exists_of_findSome?_eq_some hs
      exact asyncRules_sound hr hrt
    · cases h

/-! ## Worklist Exploration -/

/-- Sound triple equality from a sound type-equality test. -/
def tripleEqb (eqb : LocalTypeC → LocalTypeC → Bool) (a b : AsyncTriple) : Bool :=
  eqb a.sub b.sub && eqb a.sup b.sup && decide (a.buffer = b.buffer)

/-- `tripleEqb` is sound whenever `eqb` is. -/
theorem tripleEqb_sound {eqb : LocalTypeC → LocalTypeC → Bool}
    (hEq : ∀ a b, eqb a b = true → a = b) {a b : AsyncTriple}
    (h : tripleEqb eqb a b = true) : a = b := by
  obtain ⟨S, T, buf⟩ := a
  obtain ⟨S', T', buf'⟩ := b
  simp only [tripleEqb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [hEq _ _ h1, hEq _ _ h2, h3]

/-- Exploration state: pending and already-processed triples. -/
structure ExploreState where
  /-- Triples yet to explore. -/
  worklist : List AsyncTriple
  /-- Triples already processed (each closed under its chosen step). -/
  visited : List AsyncTriple

/-- Exploration outcome. Only `.accepted` carries a guarantee. -/
inductive ExploreResult where
  /-- A closed witness set was found: subtyping holds. -/
  | accepted : ExploreResult
  /-- The strategy got stuck; inconclusive. -/
  | stuck : ExploreResult
  /-- The fuel bound was exhausted; inconclusive. -/
  | outOfFuel : ExploreResult
  deriving Repr, DecidableEq

/-- Bounded worklist exploration; `fuel` bounds the number of popped triples. -/
noncomputable def explore (eqb : LocalTypeC → LocalTypeC → Bool) :
    Nat → ExploreState → ExploreResult
  | 0, _ => .outOfFuel
  | _ + 1, ⟨[], _⟩ => .accepted
  | n + 1, ⟨t :: rest, vs⟩ =>
      if vs.any (tripleEqb eqb · t) then explore eqb n ⟨rest, vs⟩
      else match stepTriple t with
        | .accept => explore eqb n ⟨rest, t :: vs⟩
        | .continue succs => explore eqb n ⟨succs ++ rest, t :: vs⟩
        | .reject => .stuck

/-- Bounded sound check of `S ≤ₐ T`. See the module doc for the meaning of results. -/
noncomputable def checkAsync (eqb : LocalTypeC → LocalTypeC → Bool) (fuel : Nat)
    (S T : LocalTypeC) : ExploreResult :=
  explore eqb fuel ⟨[AsyncTriple.initial S T], []⟩

/-- Boolean form: `true` only when `checkAsync` accepted. -/
noncomputable def isAsyncSubtypeBounded (eqb : LocalTypeC → LocalTypeC → Bool) (fuel : Nat)
    (S T : LocalTypeC) : Bool :=
  checkAsync eqb fuel S T == .accepted

/-! ## Exploration Invariant -/

/-- `v` is a base case, or has an `AsyncStep` whose successors all lie in `cover`. -/
def ClosedIn (cover : List AsyncTriple) (v : AsyncTriple) : Prop :=
  (head v.sub = .end ∧ head v.sup = .end ∧ v.buffer = []) ∨
    ∃ succs, AsyncStep v succs ∧ ∀ s ∈ succs, s ∈ cover

/-- `ClosedIn` is monotone in the cover. -/
theorem ClosedIn.mono {c c' : List AsyncTriple} (hc : c ⊆ c') {v : AsyncTriple}
    (h : ClosedIn c v) : ClosedIn c' v := by
  rcases h with h | ⟨s, hs, hm⟩
  · exact .inl h
  · exact .inr ⟨s, hs, fun x hx => hc (hm x hx)⟩

/-- Every visited triple is closed w.r.t. visited ∪ worklist. -/
def ConsistentVisited (st : ExploreState) : Prop :=
  ∀ v ∈ st.visited, ClosedIn (st.visited ++ st.worklist) v

/-- A consistent state with empty worklist is a coinductive witness. -/
theorem consistent_closed_sound {vs : List AsyncTriple}
    (h : ConsistentVisited ⟨[], vs⟩) : ∀ t ∈ vs, AsyncSubtypeRel t := by
  intro t ht
  refine AsyncSubtypeRel.coinduct (· ∈ vs) (fun a ha => ?_) t ht
  rcases h a ha with hd | ⟨s, hs, hm⟩
  · exact .inl hd
  · exact .inr ⟨s, hs, fun x hx => by simpa using hm x hx⟩

/-! ## Invariant Preservation -/

/-- Skipping an already-visited triple preserves consistency. -/
theorem consistent_skip {t : AsyncTriple} {rest vs : List AsyncTriple} (ht : t ∈ vs)
    (h : ConsistentVisited ⟨t :: rest, vs⟩) : ConsistentVisited ⟨rest, vs⟩ := by
  intro v hv
  refine (h v hv).mono ?_
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  rcases hx with hx | rfl | hx
  · exact .inl hx
  · exact .inl ht
  · exact .inr hx

/-- Processing `t` with a closing step preserves consistency. -/
theorem consistent_push {t : AsyncTriple} {rest vs succs : List AsyncTriple}
    (hc : ClosedIn (t :: vs ++ (succs ++ rest)) t)
    (h : ConsistentVisited ⟨t :: rest, vs⟩) :
    ConsistentVisited ⟨succs ++ rest, t :: vs⟩ := by
  intro v hv
  simp only [List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact hc
  · refine (h v hv).mono ?_
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto

/-- Coverage grows when a triple is moved to `visited`. -/
theorem cover_push {t x : AsyncTriple} {rest vs succs : List AsyncTriple}
    (hx : x ∈ vs ++ t :: rest) : x ∈ t :: vs ++ (succs ++ rest) := by
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  tauto

/-! ## Soundness -/

/-- One step of the soundness induction for a fresh (unvisited) triple. -/
theorem explore_sound_fresh {eqb : LocalTypeC → LocalTypeC → Bool} {n : Nat}
    {t : AsyncTriple} {rest vs : List AsyncTriple}
    (ih : ∀ st, explore eqb n st = .accepted → ConsistentVisited st →
      ∀ x ∈ st.visited ++ st.worklist, AsyncSubtypeRel x)
    (hacc : (match stepTriple t with
        | .accept => explore eqb n ⟨rest, t :: vs⟩
        | .continue succs => explore eqb n ⟨succs ++ rest, t :: vs⟩
        | .reject => .stuck) = ExploreResult.accepted)
    (hc : ConsistentVisited ⟨t :: rest, vs⟩) :
    ∀ x ∈ vs ++ t :: rest, AsyncSubtypeRel x := by
  intro x hx
  split at hacc
  · rename_i hs
    have hc' := consistent_push (succs := []) (.inl (stepTriple_accept hs)) hc
    exact ih _ hacc hc' x (cover_push (succs := []) hx)
  · rename_i succs hs
    have hcl : ClosedIn (t :: vs ++ (succs ++ rest)) t :=
      .inr ⟨succs, stepTriple_continue hs, fun s hs' => by simp [hs']⟩
    exact ih _ hacc (consistent_push hcl hc) x (cover_push hx)
  · cases hacc

/-- Acceptance from a consistent state proves the relation for every covered triple. -/
theorem explore_sound {eqb : LocalTypeC → LocalTypeC → Bool}
    (hEq : ∀ a b, eqb a b = true → a = b) :
    ∀ (n : Nat) (st : ExploreState), explore eqb n st = .accepted →
      ConsistentVisited st → ∀ x ∈ st.visited ++ st.worklist, AsyncSubtypeRel x := by
  intro n
  induction n with
  | zero => intro st h; simp [explore] at h
  | succ n ih =>
    rintro ⟨_ | ⟨t, rest⟩, vs⟩ hacc hc x hx
    · exact consistent_closed_sound hc x (by simpa using hx)
    · simp only [explore] at hacc
      split at hacc
      · rename_i hseen
        obtain ⟨v, hv, hvt⟩ := List.any_eq_true.mp hseen
        have ht : t ∈ vs := tripleEqb_sound hEq hvt ▸ hv
        refine ih _ hacc (consistent_skip ht hc) x ?_
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        rcases hx with hx | rfl | hx <;> simp_all
      · exact explore_sound_fresh ih hacc hc x hx

/-- Soundness: if `checkAsync` accepts (with a sound equality test), `S ≤ₐ T`. -/
theorem check_async_sound {eqb : LocalTypeC → LocalTypeC → Bool}
    (hEq : ∀ a b, eqb a b = true → a = b) {fuel : Nat} {S T : LocalTypeC}
    (h : checkAsync eqb fuel S T = .accepted) : S ≤ₐ T :=
  explore_sound hEq fuel _ h (fun _ hv => by simp at hv) _ (by simp [AsyncTriple.initial])

/-- Boolean soundness for `isAsyncSubtypeBounded`. -/
theorem is_async_subtype_bounded_sound {eqb : LocalTypeC → LocalTypeC → Bool}
    (hEq : ∀ a b, eqb a b = true → a = b) {fuel : Nat} {S T : LocalTypeC}
    (h : isAsyncSubtypeBounded eqb fuel S T = true) : S ≤ₐ T :=
  check_async_sound hEq (by simpa [isAsyncSubtypeBounded] using h)

end SessionCoTypes.AsyncSubtyping
