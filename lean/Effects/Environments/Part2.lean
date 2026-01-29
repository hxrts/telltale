import Effects.LocalType
import Effects.Values
import Effects.Environments.Part1

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
noncomputable section


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
noncomputable def preimageEdge (ρ : SessionRenaming) (e : Edge) : Option Edge :=
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

/-- Rename all edges in DEnv. -/
def renameDEnv (ρ : SessionRenaming) (D : DEnv) : DEnv :=
  fun e =>
    match preimageEdge ρ e with
    | some e' => (D.find? e').map (List.map (renameValType ρ))
    | none => none

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

theorem preimageEdge_rename (ρ : SessionRenaming) (e : Edge) :
    preimageEdge ρ (renameEdge ρ e) = some e := by
  classical
  have hpre : ∃ e', renameEdge ρ e' = renameEdge ρ e := ⟨e, rfl⟩
  have hEq : Classical.choose hpre = e := by
    apply renameEdge_inj ρ
    simpa using (Classical.choose_spec hpre)
  simp [preimageEdge, hpre, hEq]

/-! ## Renaming Lookup Lemmas -/

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
  classical
  have hpre : preimageEdge ρ (renameEdge ρ e) = some e := preimageEdge_rename ρ e
  cases hfind : D.find? e with
  | none =>
      simp [renameDEnv, lookupD, hpre, hfind]
  | some ts =>
      simp [renameDEnv, lookupD, hpre, hfind]

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
      have hlookup : lookupD (renameDEnv ρ D) e = [] := by
        simp [renameDEnv, lookupD, hpre]
      exact (h hlookup).elim
  | some e' =>
      have heq : e = renameEdge ρ e' := by
        exact (preimageEdge_spec (ρ:=ρ) (e:=e) (e':=e') (by simpa [hpre])).symm
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

end
