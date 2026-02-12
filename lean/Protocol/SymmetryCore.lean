import Protocol.Coherence.RoleSwap

/-! # Protocol.SymmetryCore

Protocol renaming definitions, renamed environments, and trace-level equivariance lemmas.
-/

/-
The Problem. Formalize protocol renaming and basic lookup/equivariance properties.

Solution Structure. Define renaming actions on types/envs and prove lookup + trace isomorphism lemmas.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
section

/-! ## Protocol Renaming -/

/-- Protocol renaming: injective maps on roles and labels.
    This generalizes session renaming (which acts on session IDs) to
    act on the protocol structure itself. -/
structure ProtocolRenaming where
  roleMap : Role → Role
  roleMap_inj : ∀ r₁ r₂, roleMap r₁ = roleMap r₂ → r₁ = r₂
  labelMap : Label → Label
  labelMap_inj : ∀ l₁ l₂, labelMap l₁ = labelMap l₂ → l₁ = l₂

namespace ProtocolRenaming

/-- Identity renaming. -/
def id : ProtocolRenaming where
  roleMap := fun r => r
  roleMap_inj := fun _ _ h => h
  labelMap := fun l => l
  labelMap_inj := fun _ _ h => h

/-- Compose two renamings. -/
def comp (σ₁ σ₂ : ProtocolRenaming) : ProtocolRenaming where
  roleMap := fun r => σ₁.roleMap (σ₂.roleMap r)
  roleMap_inj := fun r₁ r₂ h => σ₂.roleMap_inj _ _ (σ₁.roleMap_inj _ _ h)
  labelMap := fun l => σ₁.labelMap (σ₂.labelMap l)
  labelMap_inj := fun l₁ l₂ h => σ₂.labelMap_inj _ _ (σ₁.labelMap_inj _ _ h)

end ProtocolRenaming

/-! ## Renamed Types -/

/-- Rename a value type by applying the protocol renaming to roles. -/
def renameValTypePR (σ : ProtocolRenaming) : ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod T₁ T₂ => .prod (renameValTypePR σ T₁) (renameValTypePR σ T₂)
  | .chan sid role => .chan sid (σ.roleMap role)

mutual

/-- Rename a local type by applying the protocol renaming to roles and labels. -/
def renameLocalTypePR (σ : ProtocolRenaming) : LocalType → LocalType
  | .send r T L => .send (σ.roleMap r) (renameValTypePR σ T) (renameLocalTypePR σ L)
  | .recv r T L => .recv (σ.roleMap r) (renameValTypePR σ T) (renameLocalTypePR σ L)
  | .select r bs => .select (σ.roleMap r) (renameBranchesPR σ bs)
  | .branch r bs => .branch (σ.roleMap r) (renameBranchesPR σ bs)
  | .end_ => .end_
  | .var n => .var n
  | .mu L => .mu (renameLocalTypePR σ L)
termination_by L => sizeOf L

/-- Rename a list of labeled branches. -/
def renameBranchesPR (σ : ProtocolRenaming) : List (Label × LocalType) → List (Label × LocalType)
  | [] => []
  | (l, L) :: bs => (σ.labelMap l, renameLocalTypePR σ L) :: renameBranchesPR σ bs
termination_by bs => sizeOf bs

end

/-- Rename an endpoint's role. -/
def renameEndpointPR (σ : ProtocolRenaming) (ep : Endpoint) : Endpoint :=
  { sid := ep.sid, role := σ.roleMap ep.role }

/-- Rename an edge's roles. -/
def renameEdgePR (σ : ProtocolRenaming) (e : Edge) : Edge :=
  { sid := e.sid, sender := σ.roleMap e.sender, receiver := σ.roleMap e.receiver }

/-- Rename a GEnv by renaming all endpoints and local types. -/
def renameGEnvPR (σ : ProtocolRenaming) (G : GEnv) : GEnv :=
  G.map fun (ep, L) => (renameEndpointPR σ ep, renameLocalTypePR σ L)

/-- Rename a DEnv by renaming all edges (traces are unaffected). -/
def renameDEnvPR (σ : ProtocolRenaming) (D : DEnv) : DEnv :=
  D.list.foldl
    (fun acc p => updateD acc (renameEdgePR σ p.1) (p.2.map (renameValTypePR σ)))
    (∅ : DEnv)

/-! ## Lookup Lemmas -/

/-- Endpoint equality under protocol renaming is injective. -/
theorem renameEndpointPR_inj (σ : ProtocolRenaming) (e₁ e₂ : Endpoint) :
    renameEndpointPR σ e₁ = renameEndpointPR σ e₂ → e₁ = e₂ := by
  intro h
  simp only [renameEndpointPR, Endpoint.mk.injEq] at h
  obtain ⟨hsid, hrole⟩ := h
  cases e₁; cases e₂
  simp only [Endpoint.mk.injEq]
  exact ⟨hsid, σ.roleMap_inj _ _ hrole⟩

/-- Edge equality under protocol renaming is injective. -/
theorem renameEdgePR_inj (σ : ProtocolRenaming) (e₁ e₂ : Edge) :
    renameEdgePR σ e₁ = renameEdgePR σ e₂ → e₁ = e₂ := by
  intro h
  simp only [renameEdgePR, Edge.mk.injEq] at h
  obtain ⟨hsid, hsender, hrecv⟩ := h
  cases e₁; cases e₂
  simp only [Edge.mk.injEq]
  exact ⟨hsid, σ.roleMap_inj _ _ hsender, σ.roleMap_inj _ _ hrecv⟩

/-- Lookup in renamed GEnv: renaming commutes with lookup. -/
theorem lookupG_renamePR (σ : ProtocolRenaming) (G : GEnv) (ep : Endpoint) :
    lookupG (renameGEnvPR σ G) (renameEndpointPR σ ep) =
      (lookupG G ep).map (renameLocalTypePR σ) := by
  induction G with
  | nil =>
      simp [renameGEnvPR, lookupG]
  | cons hd tl ih =>
      by_cases heq : ep = hd.1
      · subst heq
        simp [renameGEnvPR, lookupG, List.lookup, renameEndpointPR]
      · have hne : renameEndpointPR σ ep ≠ renameEndpointPR σ hd.1 := by
          intro h
          exact heq (renameEndpointPR_inj σ _ _ h)
        have hbeq1 : (ep == hd.1) = false := beq_eq_false_iff_ne.mpr heq
        have hbeq2 : (renameEndpointPR σ ep == renameEndpointPR σ hd.1) = false :=
          beq_eq_false_iff_ne.mpr hne
        simpa [renameGEnvPR, lookupG, List.lookup, hbeq1, hbeq2] using ih

/-! ## Lookup Inversion -/

/-- Lookup in renamed GEnv: the preimage exists.
    For any endpoint in the renamed environment, there exists a corresponding
    endpoint in the original environment. -/
theorem lookupG_renamePR_inv (σ : ProtocolRenaming) (G : GEnv) (ep' : Endpoint) (L' : LocalType) :
    lookupG (renameGEnvPR σ G) ep' = some L' →
    ∃ ep L, lookupG G ep = some L ∧
      ep' = renameEndpointPR σ ep ∧ L' = renameLocalTypePR σ L := by
  intro h
  induction G with
  | nil =>
      simp [renameGEnvPR, lookupG] at h
  | cons hd tl ih =>
      simp only [renameGEnvPR, List.map_cons, lookupG, List.lookup] at h
      by_cases heq : ep' == renameEndpointPR σ hd.1
      · have heq' : ep' = renameEndpointPR σ hd.1 := beq_iff_eq.mp heq
        simp only [heq, Option.some.injEq] at h
        refine ⟨hd.1, hd.2, ?_, heq', h.symm⟩
        simp [lookupG, List.lookup]
      · simp [heq] at h
        have hne : ep' ≠ renameEndpointPR σ hd.1 := by
          intro hEq
          exact heq (beq_iff_eq.mpr hEq)
        obtain ⟨ep, L, hep, hep', hL'⟩ := ih h
        refine ⟨ep, L, ?_, hep', hL'⟩
        by_cases hEq' : ep == hd.1
        · have hEq'' : ep = hd.1 := beq_iff_eq.mp hEq'
          rw [hEq''] at hep'
          exact (hne hep').elim
        · simpa [lookupG, List.lookup, hEq'] using hep

/-! ## Equivariance -/

/-- Configuration renaming (for protocol renaming). -/
def renameConfigPR (σ : ProtocolRenaming) (G : GEnv) (D : DEnv) : GEnv × DEnv :=
  (renameGEnvPR σ G, renameDEnvPR σ D)

/-! ## Trace Isomorphism -/

/-- Execution traces over coherence-only states (GEnv × DEnv). -/
abbrev ExecTrace := List (GEnv × DEnv)

/-- Rename an execution trace. -/
def renameTracePR (σ : ProtocolRenaming) (t : ExecTrace) : ExecTrace :=
  t.map (fun C => renameConfigPR σ C.1 C.2)

/-- A trace predicate: consecutive states are related by `step`. -/
def IsTrace (step : (GEnv × DEnv) → (GEnv × DEnv) → Prop) : ExecTrace → Prop
  | [] => True
  | [_] => True
  | C :: C' :: t => step C C' ∧ IsTrace step (C' :: t)

/-- Trace isomorphism: if a step relation is equivariant under renaming,
    then renamed traces remain valid traces. -/
theorem trace_isomorphism (σ : ProtocolRenaming)
    {step : (GEnv × DEnv) → (GEnv × DEnv) → Prop}
    (hEquiv : ∀ {C C'}, step C C' →
      step (renameConfigPR σ C.1 C.2) (renameConfigPR σ C'.1 C'.2))
    (t : ExecTrace)
    (hTrace : IsTrace step t) :
    IsTrace step (renameTracePR σ t) := by
  induction t with
  | nil =>
      simp [renameTracePR, IsTrace] at hTrace ⊢
  | cons C t ih =>
      cases t with
      | nil =>
          simp [renameTracePR, IsTrace] at hTrace ⊢
      | cons C' t' =>
          simp [renameTracePR, IsTrace] at hTrace ⊢
          rcases hTrace with ⟨hStep, hTail⟩
          exact ⟨hEquiv hStep, ih hTail⟩


end
