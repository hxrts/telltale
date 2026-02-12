import Protocol.LocalType
import Protocol.Values
import Protocol.Environments.Core
/-! # MPST Environments: Session Renaming

This module provides session renaming infrastructure for environment composition. -/
/-
The Problem. Protocol composition and linking may require renaming session IDs
to avoid conflicts. We need a principled way to rename sessions that preserves
all environment invariants.

Solution Structure. We define:
1. `SessionRenaming`: bijective session ID renaming with inverse
2. `renameValType/LocalType/GEnv/DEnv`: lifting through all structures
3. Preservation lemmas: renaming preserves lookups and coherence
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
  inv : SessionId → SessionId
  left_inv : ∀ s, inv (f s) = s
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

/-! ## Runtime and Environment Renaming Maps -/
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

/-- Compute a preimage edge under renaming when the sid is in the image of `f`. -/
def preimageEdge (ρ : SessionRenaming) (e : Edge) : Option Edge :=
  let sid' := ρ.inv e.sid
  if h : ρ.f sid' = e.sid then
    some { sid := sid', sender := e.sender, receiver := e.receiver }
  else
    none
theorem preimageEdge_spec {ρ : SessionRenaming} {e e' : Edge} :
    preimageEdge ρ e = some e' → renameEdge ρ e' = e := by
  intro h
  unfold preimageEdge at h
  dsimp at h
  split_ifs at h with hs
  · cases h
    simp [renameEdge, hs]

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
/-! ## DEnv Renaming via Fold Updates -/
def renameDEnv (ρ : SessionRenaming) (D : DEnv) : DEnv :=
  D.list.foldl
    (fun acc p => updateD acc (renameEdge ρ p.1) (p.2.map (renameValType ρ)))
    (∅ : DEnv)

lemma lookupD_foldl_update_neq (ρ : SessionRenaming) :
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

lemma find?_foldl_update_neq (ρ : SessionRenaming) :
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
/-! ## Buffer Renaming -/
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
  /-! ## ValType Injectivity: Product and Channel Cases -/
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
/-! ## ValType Equality Test Preservation -/
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

/-! ## Endpoint Injectivity under Renaming -/
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

/-! ## Preimage Edge Characterization -/
theorem preimageEdge_rename (ρ : SessionRenaming) (e : Edge) :
  preimageEdge ρ (renameEdge ρ e) = some e := by
  unfold preimageEdge
  simp [renameEdge, ρ.left_inv e.sid]

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

/-! ## DEnv Lookup under Renaming -/
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
              /-! ## lookupD_rename Fold Induction: Matching Head -/
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
              /-! ## lookupD_rename Fold Induction: Non-matching Head -/
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

/-! ## find? under Renaming Fold -/
lemma find?_rename_foldl (ρ : SessionRenaming) :
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
      /-! ## find?_rename_foldl: Matching Head Case -/
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
      /-! ## find?_rename_foldl: Non-matching Head Case -/
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

/-! ## Buffer Lookup under Renaming -/
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
end
