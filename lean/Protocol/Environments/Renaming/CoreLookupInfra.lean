import Protocol.LocalType
import Protocol.Values
import Protocol.Environments.Core

/-! # Renaming.CoreLookupInfrannSession renaming infrastructure, environment/buffer renaming maps, and renaming injectivity lemmas. Re-exported by `Protocol.Environments.Renaming.CoreLookup`. -/

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
  | .readiness => .readiness
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
theorem find_rename_branches (ρ : SessionRenaming) (chosen : Label)
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
  | .readiness witness => .readiness witness
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
theorem preimage_edge_spec {ρ : SessionRenaming} {e e' : Edge} :
    preimageEdge ρ e = some e' → renameEdge ρ e' = e := by
  intro h
  unfold preimageEdge at h
  dsimp at h
  split_ifs at h with hs
  · cases h
    simp [renameEdge, hs]

/-- Renaming preserves edge equality (injective). -/
theorem rename_edge_inj (ρ : SessionRenaming) (e1 e2 : Edge) :
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

lemma lookup_d_foldl_update_neq (ρ : SessionRenaming) :
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
        lookup_d_update_neq (env := acc) (e := renameEdge ρ hd.1) (e' := edge)
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
        find?_update_d_neq acc (renameEdge ρ hd.1) edge (hd.2.map (renameValType ρ)) hne_hd
      simpa [List.foldl, hupd] using
        (ih (acc := updateD acc (renameEdge ρ hd.1) (hd.2.map (renameValType ρ))) hne_tl)
/-! ## Buffer Renaming -/
/-- Rename all edges in Buffers. -/
def renameBufs (ρ : SessionRenaming) (bufs : Buffers) : Buffers :=
  bufs.map fun (e, buf) => (renameEdge ρ e, buf.map (renameValue ρ))
/-! ## Renaming Injectivity Lemmas -/

/-- Renaming preserves value type equality (injective). -/
theorem rename_val_type_inj (ρ : SessionRenaming) {T1 T2 : ValType} :
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
      | readiness => cases h
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
      | readiness => cases h
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
      | readiness => cases h
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
      | readiness => cases h
      | prod _ _ => cases h
      | chan _ _ => cases h
  -- ValType Injectivity: Product and Channel Cases
  | readiness =>
      cases T2 <;> simp_all [renameValType]
  | prod T1a T1b ih1 ih2 =>
      cases T2 <;> simp [renameValType] at h
      case prod T2a T2b =>
        obtain ⟨h1, h2⟩ := h
        have h1' := ih1 h1
        have h2' := ih2 h2
/- ## Structured Block 1 -/
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
-- ValType Equality Test Preservation
theorem rename_val_type_beq (ρ : SessionRenaming) (T1 T2 : ValType) :
    (renameValType ρ T1 == renameValType ρ T2) = (T1 == T2) := by
  by_cases h : T1 = T2
  · subst h
    simp
  · have hne : renameValType ρ T1 ≠ renameValType ρ T2 := by
      intro hEq
      exact h (rename_val_type_inj ρ hEq)
    have hbeq1 : (renameValType ρ T1 == renameValType ρ T2) = false :=
      beq_eq_false_iff_ne.mpr hne
    have hbeq2 : (T1 == T2) = false := beq_eq_false_iff_ne.mpr h
    simp [hbeq1, hbeq2]

end
