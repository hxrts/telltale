import Protocol.LocalType
import Protocol.Values
import Protocol.Environments.Core

/-!
# MPST Environments

This module defines the runtime environments for multiparty session types:

- `Store`: Variable store mapping variables to runtime values
- `SEnv`: Type environment mapping variables to value types
- `GEnv`: Session environment mapping endpoints to local types
- `DEnv`: Delayed type environment for in-flight message traces per directed edge
- `Buffers`: Per-edge FIFO message buffers keyed by (sid, from, to)

The key difference from binary session types is that buffers and type traces
are keyed by **directed edges** `(sid, from, to)` rather than endpoints.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
section


/-! ## Session Renaming Infrastructure -/

/-- Session renaming: an injective function on session IDs. -/
structure SessionRenaming where
  f : SessionId → SessionId
  inj : ∀ s1 s2, f s1 = f s2 → s1 = s2

/-- Rename a value type by updating embedded session IDs. -/
def renameValType (ρ : SessionRenaming) : ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod T₁ T₂ => .prod (renameValType ρ T₁) (renameValType ρ T₂)
  | .chan sid role => .chan (ρ.f sid) role

/-- Rename an endpoint's session ID. -/
def renameEndpoint (ρ : SessionRenaming) (e : Endpoint) : Endpoint :=
  { sid := ρ.f e.sid, role := e.role }

/-- Rename an edge's session ID. -/
def renameEdge (ρ : SessionRenaming) (e : Edge) : Edge :=
  { sid := ρ.f e.sid, sender := e.sender, receiver := e.receiver }

mutual

/-- Rename a local type by renaming all value types it carries. -/
def renameLocalType (ρ : SessionRenaming) : LocalType → LocalType
  | .send r T L => .send r (renameValType ρ T) (renameLocalType ρ L)
  | .recv r T L => .recv r (renameValType ρ T) (renameLocalType ρ L)
  | .select r bs => .select r (renameBranches ρ bs)
  | .branch r bs => .branch r (renameBranches ρ bs)
  | .end_ => .end_
  | .var n => .var n
  | .mu L => .mu (renameLocalType ρ L)
termination_by L => sizeOf L

/-- Rename a list of labeled branches. -/
def renameBranches (ρ : SessionRenaming) : List (Label × LocalType) → List (Label × LocalType)
  | [] => []
  | (l, L) :: bs => (l, renameLocalType ρ L) :: renameBranches ρ bs
termination_by bs => sizeOf bs

end

/-- find? commutes with renameBranches: the label is preserved, type is renamed. -/
theorem find_renameBranches (ρ : SessionRenaming) (chosen : Label)
    (branches : List (Label × LocalType)) :
    (renameBranches ρ branches).find? (fun b => b.1 == chosen) =
    (branches.find? (fun b => b.1 == chosen)).map (fun (l, L) => (l, renameLocalType ρ L)) := by
  induction branches with
  | nil => simp [renameBranches]
  | cons hd tl ih =>
    obtain ⟨l, L⟩ := hd
    simp only [renameBranches, List.find?_cons]
    by_cases h : l == chosen
    · simp [h]
    · simp [h, ih]

/-- Rename a runtime value by updating any embedded endpoints. -/
def renameValue (ρ : SessionRenaming) : Value → Value
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .string s => .string s
  | .prod v₁ v₂ => .prod (renameValue ρ v₁) (renameValue ρ v₂)
  | .chan e => .chan (renameEndpoint ρ e)

/-- Rename all endpoints in GEnv. -/
def renameGEnv (ρ : SessionRenaming) (G : GEnv) : GEnv :=
  G.map fun (e, L) => (renameEndpoint ρ e, renameLocalType ρ L)

/-- Choose a preimage edge under renaming (if it exists). -/
def preimageEdgeImpl (_ρ : SessionRenaming) (_e : Edge) : Option Edge := none

@[implemented_by preimageEdgeImpl]
def preimageEdge (ρ : SessionRenaming) (e : Edge) : Option Edge :=
  if h : ∃ e', renameEdge ρ e' = e then
    some (Classical.choose h)
  else
    none

theorem preimageEdge_spec {ρ : SessionRenaming} {e e' : Edge} :
    preimageEdge ρ e = some e' → renameEdge ρ e' = e := by
  intro h
  by_cases hpre : ∃ e'', renameEdge ρ e'' = e
  · simp [preimageEdge, hpre] at h
    cases h
    exact Classical.choose_spec hpre
  · simp [preimageEdge, hpre] at h

/-- Renaming preserves edge equality (injective). -/
theorem renameEdge_inj (ρ : SessionRenaming) (e1 e2 : Edge) :
    renameEdge ρ e1 = renameEdge ρ e2 → e1 = e2 := by
  intro h
  have hsid : ρ.f e1.sid = ρ.f e2.sid := by
    have := congrArg Edge.sid h
    simp only [renameEdge] at this
    exact this
  have hsender : e1.sender = e2.sender := by
    have := congrArg Edge.sender h
    simp only [renameEdge] at this
    exact this
  have hrecv : e1.receiver = e2.receiver := by
    have := congrArg Edge.receiver h
    simp only [renameEdge] at this
    exact this
  have hsid' : e1.sid = e2.sid := ρ.inj _ _ hsid
  cases e1; cases e2
  simp only at hsid' hsender hrecv
  subst hsid' hsender hrecv
  rfl

def renameDEnv (ρ : SessionRenaming) (D : DEnv) : DEnv :=
  D.list.foldl
    (fun acc p => updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
    (∅ : DEnv)

private lemma lookupD_foldl_update_neq (ρ : SessionRenaming) :
    ∀ (l : List (Edge × Trace)) (acc : DEnv) (edge : Edge),
      (∀ p ∈ l, renameEdge ρ p.1 ≠ edge) →
      lookupD
          (l.foldl
            (fun acc p => updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
            acc)
          edge = lookupD acc edge := by
  intro l acc edge hne
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
      have hne_hd : renameEdge ρ hd.1 ≠ edge := hne hd (List.mem_cons.mpr (Or.inl rfl))
      have hne_tl : ∀ p ∈ tl, renameEdge ρ p.1 ≠ edge := by
        intro p hp
        exact hne p (List.mem_cons.mpr (Or.inr hp))
      have hupd : lookupD (updateD acc (renameEdge ρ hd.1)
        (hd.2.map (renameValType ρ))) edge = lookupD acc edge :=
        lookupD_update_neq (env := acc) (e := renameEdge ρ hd.1) (e' := edge)
          (ts := hd.2.map (renameValType ρ)) (hne := hne_hd)
      simpa [List.foldl, hupd] using (ih (acc := updateD acc (renameEdge ρ hd.1)
        (hd.2.map (renameValType ρ))) hne_tl)

private lemma find?_foldl_update_neq (ρ : SessionRenaming) :
    ∀ (l : List (Edge × Trace)) (acc : DEnv) (edge : Edge),
      (∀ p ∈ l, renameEdge ρ p.1 ≠ edge) →
      (l.foldl
          (fun acc p => updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
          acc).find? edge = acc.find? edge := by
  intro l acc edge hne
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
      have hne_hd : renameEdge ρ hd.1 ≠ edge :=
        hne hd (List.mem_cons.mpr (Or.inl rfl))
      have hne_tl : ∀ p ∈ tl, renameEdge ρ p.1 ≠ edge := by
        intro p hp
        exact hne p (List.mem_cons.mpr (Or.inr hp))
      have hupd :
          (updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))).find? edge =
            acc.find? edge :=
        find?_updateD_neq acc (renameEdge ρ hd.1) edge (hd.2.map (renameValType ρ)) hne_hd
      simpa [List.foldl, hupd] using
        (ih (acc := updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))) hne_tl)

/-- Rename all edges in Buffers. -/
def renameBufs (ρ : SessionRenaming) (bufs : Buffers) : Buffers :=
  bufs.map fun (e, buf) => (renameEdge ρ e, buf.map (renameValue ρ))

/-! ## Renaming Injectivity Lemmas -/

/-- Renaming preserves value type equality (injective). -/
theorem renameValType_inj (ρ : SessionRenaming) {T1 T2 : ValType} :
    renameValType ρ T1 = renameValType ρ T2 → T1 = T2 := by
  intro h
  induction T1 generalizing T2 with
  | unit =>
      cases T2 with
      | unit =>
          cases h
          rfl
      | bool => cases h
      | nat => cases h
      | string => cases h
      | prod _ _ => cases h
      | chan _ _ => cases h
  | bool =>
      cases T2 with
      | unit => cases h
      | bool =>
          cases h
          rfl
      | nat => cases h
      | string => cases h
      | prod _ _ => cases h
      | chan _ _ => cases h
  | nat =>
      cases T2 with
      | unit => cases h
      | bool => cases h
      | nat =>
          cases h
          rfl
      | string => cases h
      | prod _ _ => cases h
      | chan _ _ => cases h
  | string =>
      cases T2 with
      | unit => cases h
      | bool => cases h
      | nat => cases h
      | string =>
          cases h
          rfl
      | prod _ _ => cases h
      | chan _ _ => cases h
  | prod T1a T1b ih1 ih2 =>
      cases T2 <;> simp [renameValType] at h
      case prod T2a T2b =>
        obtain ⟨h1, h2⟩ := h
        have h1' := ih1 h1
        have h2' := ih2 h2
        subst h1' h2'
        rfl
  | chan sid role =>
      cases T2 <;> simp [renameValType] at h
      case chan sid' role' =>
        obtain ⟨hSid, hRole⟩ := h
        have hSid' : sid = sid' := ρ.inj _ _ hSid
        subst hSid' hRole
        rfl

/-- Renaming preserves value type equality tests. -/
theorem renameValType_beq (ρ : SessionRenaming) (T1 T2 : ValType) :
    (renameValType ρ T1 == renameValType ρ T2) = (T1 == T2) := by
  by_cases h : T1 = T2
  · subst h
    simp
  · have hne : renameValType ρ T1 ≠ renameValType ρ T2 := by
      intro hEq
      exact h (renameValType_inj ρ hEq)
    have hbeq1 : (renameValType ρ T1 == renameValType ρ T2) = false :=
      beq_eq_false_iff_ne.mpr hne
    have hbeq2 : (T1 == T2) = false := beq_eq_false_iff_ne.mpr h
    simp [hbeq1, hbeq2]

/-- Renaming preserves endpoint equality (injective). -/
theorem renameEndpoint_inj (ρ : SessionRenaming) (e1 e2 : Endpoint) :
    renameEndpoint ρ e1 = renameEndpoint ρ e2 → e1 = e2 := by
  intro h
  have hsid : ρ.f e1.sid = ρ.f e2.sid := by
    have := congrArg Endpoint.sid h
    simp only [renameEndpoint] at this
    exact this
  have hrole : e1.role = e2.role := by
    have := congrArg Endpoint.role h
    simp only [renameEndpoint] at this
    exact this
  have hsid' : e1.sid = e2.sid := ρ.inj _ _ hsid
  cases e1; cases e2
  simp only at hsid' hrole
  subst hsid' hrole
  rfl

theorem preimageEdge_rename (ρ : SessionRenaming) (e : Edge) :
    preimageEdge ρ (renameEdge ρ e) = some e := by
  classical
  have hpre : ∃ e', renameEdge ρ e' = renameEdge ρ e := ⟨e, rfl⟩
  have hEq : Classical.choose hpre = e := by
    apply renameEdge_inj ρ
    simpa using (Classical.choose_spec hpre)
  simp [preimageEdge, hpre, hEq]

/-! ## Renaming Lookup Lemmas -/

private lemma lookupD_eq_list_lookup (D : DEnv) (e : Edge) :
    lookupD D e = match D.list.lookup e with
      | some ts => ts
      | none => [] := by
  have hfind := DEnv_find?_eq_lookup (env := D) (e := e)
  cases h : D.list.lookup e with
  | none =>
      simp [lookupD, hfind, h]
  | some ts =>
      simp [lookupD, hfind, h]

/-- Looking up a renamed endpoint in a renamed GEnv. -/
theorem lookupG_rename (ρ : SessionRenaming) (G : GEnv) (e : Endpoint) :
    lookupG (renameGEnv ρ G) (renameEndpoint ρ e) =
      (lookupG G e).map (renameLocalType ρ) := by
  induction G with
  | nil => rfl
  | cons hd tl ih =>
    by_cases heq : e = hd.1
    case pos =>
      subst heq
      simp [renameGEnv, lookupG, List.lookup]
    case neg =>
      have hne : renameEndpoint ρ e ≠ renameEndpoint ρ hd.1 := fun h =>
        heq (renameEndpoint_inj ρ _ _ h)
      have hbeq1 : (e == hd.1) = false := beq_eq_false_iff_ne.mpr heq
      have hbeq2 : (renameEndpoint ρ e == renameEndpoint ρ hd.1) = false :=
        beq_eq_false_iff_ne.mpr hne
      simpa [renameGEnv, lookupG, List.lookup, hbeq1, hbeq2] using ih

/-- Looking up a renamed edge in a renamed DEnv. -/
theorem lookupD_rename (ρ : SessionRenaming) (D : DEnv) (e : Edge) :
    lookupD (renameDEnv ρ D) (renameEdge ρ e) =
      (lookupD D e).map (renameValType ρ) := by
  have hfold :
      lookupD (renameDEnv ρ D) (renameEdge ρ e) =
        match D.list.lookup e with
        | some ts => ts.map (renameValType ρ)
        | none => [] := by
    cases D with
    | mk l m map_eq sorted =>
        have hfold' :
            ∀ (l : List (Edge × Trace)) (sorted : l.Pairwise edgeCmpLT) (acc : DEnv) (e : Edge),
              lookupD
                  (l.foldl
                    (fun acc p =>
                      updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
                    acc)
                  (renameEdge ρ e) =
                match l.lookup e with
                | some ts => ts.map (renameValType ρ)
                | none => lookupD acc (renameEdge ρ e) := by
          intro l sorted acc e
          revert sorted
          induction l generalizing acc with
          | nil =>
              intro sorted
              simp [List.lookup]
          | cons hd tl ih =>
              intro sorted
              have hpair := (List.pairwise_cons.1 sorted)
              have hhd : ∀ p ∈ tl, edgeCmpLT hd p := hpair.1
              have htl : tl.Pairwise edgeCmpLT := hpair.2
              by_cases hEq : e = hd.1
              case pos =>
                subst hEq
                have hne : ∀ p ∈ tl, renameEdge ρ p.1 ≠ renameEdge ρ hd.1 := by
                  intro p hp hEq'
                  have hEq0 : p.1 = hd.1 := renameEdge_inj ρ _ _ hEq'
                  have hlt : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt (hhd p hp)
                  have hEqCmp : compare hd.1 p.1 = .eq :=
                    (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq0.symm
                  have : Ordering.lt = Ordering.eq := by
                    exact hlt.symm.trans hEqCmp
                  cases this
                have htail :
                    lookupD
                        (tl.foldl
                          (fun acc p =>
                            updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
                          (updateD acc (renameEdge ρ hd.1)
                            (hd.2.map (renameValType ρ))))
                        (renameEdge ρ hd.1) =
                      lookupD (updateD acc (renameEdge ρ hd.1)
                        (hd.2.map (renameValType ρ))) (renameEdge ρ hd.1) := by
                  simpa using
                    (lookupD_foldl_update_neq (ρ := ρ) (l := tl)
                      (acc := updateD acc (renameEdge ρ hd.1)
                        (hd.2.map (renameValType ρ)))
                      (edge := renameEdge ρ hd.1) hne)
                have hupd :
                    lookupD (updateD acc (renameEdge ρ hd.1)
                      (hd.2.map (renameValType ρ))) (renameEdge ρ hd.1) =
                      hd.2.map (renameValType ρ) := by
                  simpa using
                    (lookupD_update_eq (env := acc) (e := renameEdge ρ hd.1)
                      (ts := hd.2.map (renameValType ρ)))
                simp [List.lookup, htail, hupd]
              case neg =>
                have hne : renameEdge ρ hd.1 ≠ renameEdge ρ e := by
                  intro hEq'
                  exact hEq (renameEdge_inj ρ _ _ hEq').symm
                have hupd :
                    lookupD (updateD acc (renameEdge ρ hd.1)
                      (hd.2.map (renameValType ρ))) (renameEdge ρ e) =
                      lookupD acc (renameEdge ρ e) := by
                  simpa using
                    (lookupD_update_neq (env := acc) (e := renameEdge ρ hd.1)
                      (e' := renameEdge ρ e) (ts := hd.2.map (renameValType ρ)) (hne := hne))
                have hrec := ih (acc := updateD acc (renameEdge ρ hd.1)
                  (hd.2.map (renameValType ρ))) (sorted := htl)
                have hbeq : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
                simp [List.lookup, hbeq, hrec, hupd]
        have hfold'' := hfold' (l := l) (sorted := sorted) (acc := (∅ : DEnv)) (e := e)
        simpa [renameDEnv] using hfold''
  have hlookup := lookupD_eq_list_lookup (D := D) (e := e)
  cases h : D.list.lookup e <;>
    simp [hfold, hlookup, h]

private lemma find?_rename_foldl (ρ : SessionRenaming) :
    ∀ (l : List (Edge × Trace)) (sorted : l.Pairwise edgeCmpLT) (acc : DEnv) (e : Edge),
      (l.foldl
          (fun acc p => updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
          acc).find? (renameEdge ρ e) =
        match l.lookup e with
        | some ts => some (ts.map (renameValType ρ))
        | none => acc.find? (renameEdge ρ e) := by
  intro l sorted acc e
  revert sorted
  induction l generalizing acc with
  | nil =>
      intro sorted
      simp [List.lookup]
  | cons hd tl ih =>
      intro sorted
      have hpair := (List.pairwise_cons.1 sorted)
      have hhd : ∀ p ∈ tl, edgeCmpLT hd p := hpair.1
      have htl : tl.Pairwise edgeCmpLT := hpair.2
      by_cases hEq : e = hd.1
      case pos =>
        subst hEq
        have hne : ∀ p ∈ tl, renameEdge ρ p.1 ≠ renameEdge ρ hd.1 := by
          intro p hp hEq'
          have hEq0 : p.1 = hd.1 := renameEdge_inj ρ _ _ hEq'
          have hlt : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt (hhd p hp)
          have hEqCmp : compare hd.1 p.1 = .eq :=
            (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq0.symm
          have : (.lt : Ordering) = .eq := hlt.symm.trans hEqCmp
          cases this
        have htail :
            (tl.foldl
                (fun acc p => updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
                (updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ)))).find?
              (renameEdge ρ hd.1) =
            (updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))).find?
              (renameEdge ρ hd.1) := by
          simpa [List.foldl] using
            (find?_foldl_update_neq (ρ := ρ) (l := tl)
              (acc := updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ)))
              (edge := renameEdge ρ hd.1) hne)
        have hupd :
            (updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))).find?
              (renameEdge ρ hd.1) = some (hd.2.map (renameValType ρ)) :=
          find?_updateD_eq acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))
        simp [List.lookup, htail, hupd]
      case neg =>
        have hne : renameEdge ρ e ≠ renameEdge ρ hd.1 := fun h =>
          hEq (renameEdge_inj ρ _ _ h)
        have hbeq : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
        have ih' :=
          ih (acc := updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))) htl
        have hupd :
            (updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))).find?
              (renameEdge ρ e) = acc.find? (renameEdge ρ e) :=
          find?_updateD_neq acc (renameEdge ρ hd.1) (renameEdge ρ e)
            (hd.2.map (renameValType ρ)) (by
              intro h
              exact hne h.symm)
        simpa [List.lookup, hbeq, hupd] using ih'

/-- Looking up a renamed edge in renamed buffers. -/
theorem lookupBuf_rename (ρ : SessionRenaming) (bufs : Buffers) (e : Edge) :
    lookupBuf (renameBufs ρ bufs) (renameEdge ρ e) =
      (lookupBuf bufs e).map (renameValue ρ) := by
  induction bufs with
  | nil => simp only [renameBufs, lookupBuf, List.lookup, List.map, Option.getD]
  | cons hd tl ih =>
    simp only [renameBufs, List.map, lookupBuf, List.lookup, Option.getD]
    by_cases heq : e = hd.1
    case pos =>
      subst heq
      simp only [beq_self_eq_true]
    case neg =>
      have hne : renameEdge ρ e ≠ renameEdge ρ hd.1 := fun h =>
        heq (renameEdge_inj ρ _ _ h)
      have hbeq1 : (e == hd.1) = false := beq_eq_false_iff_ne.mpr heq
      have hbeq2 : (renameEdge ρ e == renameEdge ρ hd.1) = false :=
        beq_eq_false_iff_ne.mpr hne
      simp only [hbeq1, hbeq2]
      exact ih

/-! ## Inverse Lookup Lemmas -/

/-- If lookup succeeds in renamed GEnv, the preimage endpoint exists. -/
theorem lookupG_rename_inv (ρ : SessionRenaming) (G : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG (renameGEnv ρ G) e = some L →
    ∃ e' L', e = renameEndpoint ρ e' ∧ L = renameLocalType ρ L' ∧ lookupG G e' = some L' := by
  intro h
  induction G with
  | nil =>
    simp only [renameGEnv, lookupG, List.lookup, List.map] at h
    exact Option.noConfusion h
  | cons hd tl ih =>
    simp only [renameGEnv, List.map, lookupG, List.lookup] at h
    by_cases heq : e = renameEndpoint ρ hd.1
    case pos =>
      simp only [heq, beq_self_eq_true, Option.some.injEq] at h
      refine ⟨hd.1, hd.2, heq, h.symm, ?_⟩
      simp only [lookupG, List.lookup, beq_self_eq_true]
    case neg =>
      have hbeq : (e == renameEndpoint ρ hd.1) = false := beq_eq_false_iff_ne.mpr heq
      simp only [hbeq] at h
      obtain ⟨e', L', he', hL', hLookup⟩ := ih h
      refine ⟨e', L', he', hL', ?_⟩
      simp only [lookupG, List.lookup]
      have hne : e' ≠ hd.1 := by
        intro heq'
        subst heq'
        exact heq he'
      simp only [beq_eq_false_iff_ne.mpr hne]
      exact hLookup

/-- If lookup succeeds (non-empty) in renamed DEnv, the preimage edge exists. -/
theorem lookupD_rename_inv (ρ : SessionRenaming) (D : DEnv) (e : Edge) :
    lookupD (renameDEnv ρ D) e ≠ [] →
    ∃ e', e = renameEdge ρ e' ∧
      lookupD (renameDEnv ρ D) e = (lookupD D e').map (renameValType ρ) := by
  intro h
  cases hpre : preimageEdge ρ e with
  | none =>
      have hno : ∀ p ∈ D.list, renameEdge ρ p.1 ≠ e := by
        intro p hp hEq
        have hex : ∃ e', renameEdge ρ e' = e := ⟨p.1, hEq⟩
        have hsome : preimageEdge ρ e = some (Classical.choose hex) := by
          simp [preimageEdge, hex]
        have : (none : Option Edge) = some (Classical.choose hex) := by
          rw [hpre] at hsome
          exact hsome
        cases this
      have hlookup :
          lookupD (renameDEnv ρ D) e = lookupD (∅ : DEnv) e := by
        simpa [renameDEnv] using
          (lookupD_foldl_update_neq (ρ := ρ) (l := D.list) (acc := (∅ : DEnv))
            (edge := e) hno)
      have hlookup' : lookupD (∅ : DEnv) e = [] := by
        simp [lookupD_empty]
      exact (h (by simp [hlookup, hlookup'])).elim
  | some e' =>
      have heq : e = renameEdge ρ e' := by
        exact (preimageEdge_spec (ρ:=ρ) (e:=e) (e':=e') (by simp [hpre])).symm
      refine ⟨e', heq, ?_⟩
      simpa [heq] using (lookupD_rename (ρ:=ρ) (D:=D) (e:=e'))

/-- If lookup succeeds (non-empty) in renamed buffers, the preimage edge exists. -/
theorem lookupBuf_rename_inv (ρ : SessionRenaming) (bufs : Buffers) (e : Edge) :
    lookupBuf (renameBufs ρ bufs) e ≠ [] →
    ∃ e', e = renameEdge ρ e' ∧
      lookupBuf (renameBufs ρ bufs) e = (lookupBuf bufs e').map (renameValue ρ) := by
  intro h
  induction bufs with
  | nil =>
    simp only [renameBufs, lookupBuf, List.lookup, List.map, Option.getD, ne_eq,
               not_true_eq_false] at h
  | cons hd tl ih =>
    simp only [renameBufs, List.map, lookupBuf, List.lookup, Option.getD] at h ⊢
    by_cases heq : e = renameEdge ρ hd.1
    case pos =>
      refine ⟨hd.1, heq, ?_⟩
      subst heq
      simp only [beq_self_eq_true]
    case neg =>
      have hbeq : (e == renameEdge ρ hd.1) = false := beq_eq_false_iff_ne.mpr heq
      simp only [hbeq] at h ⊢
      obtain ⟨e', he', hLookup⟩ := ih h
      have hne : e' ≠ hd.1 := by
        intro heq'
        subst heq'
        exact heq he'
      refine ⟨e', he', ?_⟩
      simp only [beq_eq_false_iff_ne.mpr hne]
      exact hLookup

/-! ## Update Commutes with Renaming

These lemmas are essential for proving that instruction specs are equivariant
under session renaming (R.6 in implementation.md). -/

/-- Renaming commutes with GEnv update.

    This is the key infrastructure lemma for proving instruction equivariance.
    It states that updating then renaming equals renaming then updating. -/
theorem renameGEnv_updateG (ρ : SessionRenaming) (G : GEnv) (ep : Endpoint) (L : LocalType) :
    renameGEnv ρ (updateG G ep L) =
      updateG (renameGEnv ρ G) (renameEndpoint ρ ep) (renameLocalType ρ L) := by
  induction G with
  | nil =>
    simp [renameGEnv, updateG]
  | cons hd tl ih =>
    simp only [updateG, renameGEnv, List.map]
    by_cases heq : ep = hd.1
    case pos =>
      subst heq
      -- After substitution: ep = hd.1, so if_true applies
      simp only [ite_true, List.map]
    case neg =>
      have hne : renameEndpoint ρ ep ≠ renameEndpoint ρ hd.1 := fun h =>
        heq (renameEndpoint_inj ρ _ _ h)
      -- Unfold the if-then-else for the non-equal case
      simp only [if_neg heq, if_neg hne, List.map, List.cons.injEq, true_and]
      exact ih

/-- Renaming commutes with DEnv update.

    This lemma handles the map-based DEnv structure. The proof relies on
    the fact that renameEdge is injective (via renameEdge_inj).

    The key insight is that for any edge e':
    - If e' = renameEdge ρ e: both sides have find? = some (ts.map f)
    - If e' is not in the image of renameEdge: both sides have find? = none
    - If e' = renameEdge ρ e'' for e'' ≠ e: both sides have the same lookup as D at e''

    The proof uses DEnv_eq_of_find?_eq and case analysis on the preimage of e'. -/
theorem renameDEnv_updateD (ρ : SessionRenaming) (D : DEnv) (e : Edge) (ts : Trace) :
    renameDEnv ρ (updateD D e ts) =
      updateD (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ)) := by
  apply DEnv_eq_of_find?_eq
  intro e'
  by_cases heq : e' = renameEdge ρ e
  case pos =>
    subst heq
    have hFold :=
      find?_rename_foldl (ρ := ρ) (l := (updateD D e ts).list)
        (sorted := (updateD D e ts).sorted) (acc := (∅ : DEnv)) (e := e)
    have hFind := find?_updateD_eq D e ts
    have hLookup : (updateD D e ts).list.lookup e = some ts := by
      calc
        (updateD D e ts).list.lookup e
            = (updateD D e ts).find? e := by
                symm; exact DEnv_find?_eq_lookup (env := updateD D e ts) (e := e)
        _ = some ts := hFind
    have hLhs :
        (renameDEnv ρ (updateD D e ts)).find? (renameEdge ρ e) =
          some (ts.map (renameValType ρ)) := by
      simpa [renameDEnv, hLookup] using hFold
    have hRhs :
        (updateD (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))).find?
          (renameEdge ρ e) = some (ts.map (renameValType ρ)) :=
      find?_updateD_eq (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))
    rw [hLhs, hRhs]
  case neg =>
    have hrhs :
        (updateD (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))).find? e' =
          (renameDEnv ρ D).find? e' :=
      find?_updateD_neq (renameDEnv ρ D) (renameEdge ρ e) e' (ts.map (renameValType ρ))
        (fun h => heq h.symm)
    cases hpre : preimageEdge ρ e' with
    | none =>
        have hno_lhs : ∀ p ∈ (updateD D e ts).list, renameEdge ρ p.1 ≠ e' := by
          intro p hp hEq
          have hex : ∃ e'', renameEdge ρ e'' = e' := ⟨p.1, hEq⟩
          have hsome : preimageEdge ρ e' = some (Classical.choose hex) := by
            simp [preimageEdge, hex]
          exact Option.noConfusion (hpre ▸ hsome)
        have hLhs : (renameDEnv ρ (updateD D e ts)).find? e' = none := by
          simpa [renameDEnv] using
            (find?_foldl_update_neq (ρ := ρ) (l := (updateD D e ts).list)
              (acc := (∅ : DEnv)) (edge := e') hno_lhs)
        have hno_rhs : ∀ p ∈ D.list, renameEdge ρ p.1 ≠ e' := by
          intro p hp hEq
          have hex : ∃ e'', renameEdge ρ e'' = e' := ⟨p.1, hEq⟩
          have hsome : preimageEdge ρ e' = some (Classical.choose hex) := by
            simp [preimageEdge, hex]
          exact Option.noConfusion (hpre ▸ hsome)
        have hRhsBase : (renameDEnv ρ D).find? e' = none := by
          simpa [renameDEnv] using
            (find?_foldl_update_neq (ρ := ρ) (l := D.list)
              (acc := (∅ : DEnv)) (edge := e') hno_rhs)
        rw [hLhs, hrhs, hRhsBase]
    | some e'' =>
        have he'_eq : e' = renameEdge ρ e'' :=
          (preimageEdge_spec (by simp [hpre])).symm
        have hne : e'' ≠ e := by
          intro hc
          subst hc
          exact heq he'_eq
        have hL :=
          find?_rename_foldl (ρ := ρ) (l := (updateD D e ts).list)
            (sorted := (updateD D e ts).sorted) (acc := (∅ : DEnv)) (e := e'')
        have hEqUpd : (updateD D e ts).list.lookup e'' = (updateD D e ts).find? e'' := by
          symm
          exact DEnv_find?_eq_lookup (env := updateD D e ts) (e := e'')
        have hL' :
            (renameDEnv ρ (updateD D e ts)).find? e' =
              match (updateD D e ts).find? e'' with
              | some ts' => some (ts'.map (renameValType ρ))
              | none => none := by
          simpa [renameDEnv, he'_eq, hEqUpd] using hL
        have hFindUpd : (updateD D e ts).find? e'' = D.find? e'' :=
          find?_updateD_neq D e e'' ts hne.symm
        have hR :=
          find?_rename_foldl (ρ := ρ) (l := D.list) (sorted := D.sorted)
            (acc := (∅ : DEnv)) (e := e'')
        have hEqD : D.list.lookup e'' = D.find? e'' := by
          symm
          exact DEnv_find?_eq_lookup (env := D) (e := e'')
        have hR' :
            (renameDEnv ρ D).find? e' =
              match D.find? e'' with
              | some ts' => some (ts'.map (renameValType ρ))
              | none => none := by
          simpa [renameDEnv, he'_eq, hEqD] using hR
        have hL'' :
            (renameDEnv ρ (updateD D e ts)).find? e' =
              match D.find? e'' with
              | some ts' => some (ts'.map (renameValType ρ))
              | none => none := by
          simpa [hFindUpd] using hL'
        have hEqLR :
            (renameDEnv ρ (updateD D e ts)).find? e' = (renameDEnv ρ D).find? e' := by
          simpa [hR'] using hL''
        rw [hEqLR, hrhs]

/-- Lookup after updateG at the same endpoint (renamed version). -/
theorem lookupG_updateG_rename_eq (ρ : SessionRenaming) (G : GEnv) (ep : Endpoint) (L : LocalType) :
    lookupG (renameGEnv ρ (updateG G ep L)) (renameEndpoint ρ ep) =
      some (renameLocalType ρ L) := by
  rw [renameGEnv_updateG]
  exact lookupG_updateG_eq

/-- Lookup after updateG at a different endpoint (renamed version). -/
theorem lookupG_updateG_rename_neq (ρ : SessionRenaming) (G : GEnv) (ep ep' : Endpoint) (L : LocalType)
    (hne : ep ≠ ep') :
    lookupG (renameGEnv ρ (updateG G ep L)) (renameEndpoint ρ ep') =
      lookupG (renameGEnv ρ G) (renameEndpoint ρ ep') := by
  rw [renameGEnv_updateG]
  have hne' : renameEndpoint ρ ep ≠ renameEndpoint ρ ep' := fun h =>
    hne (renameEndpoint_inj ρ _ _ h)
  exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) (renameEndpoint ρ ep')
    (renameLocalType ρ L) hne'

/-- Lookup after updateD at the same edge (renamed version). -/
theorem lookupD_updateD_rename_eq (ρ : SessionRenaming) (D : DEnv) (e : Edge) (ts : Trace) :
    lookupD (renameDEnv ρ (updateD D e ts)) (renameEdge ρ e) =
      ts.map (renameValType ρ) := by
  rw [renameDEnv_updateD]
  exact lookupD_update_eq (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))

/-- Lookup after updateD at a different edge (renamed version). -/
theorem lookupD_updateD_rename_neq (ρ : SessionRenaming) (D : DEnv) (e e' : Edge) (ts : Trace)
    (hne : e ≠ e') :
    lookupD (renameDEnv ρ (updateD D e ts)) (renameEdge ρ e') =
      lookupD (renameDEnv ρ D) (renameEdge ρ e') := by
  rw [renameDEnv_updateD]
  have hne' : renameEdge ρ e ≠ renameEdge ρ e' := fun h =>
    hne (renameEdge_inj ρ _ _ h)
  exact lookupD_update_neq (renameDEnv ρ D) (renameEdge ρ e) (renameEdge ρ e')
    (ts.map (renameValType ρ)) hne'

end
