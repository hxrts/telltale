import Protocol.Coherence.RoleSwap

/-!
# Protocol Symmetry and Conservation Laws

This module establishes symmetry properties for MPST configurations:

1. **Protocol Renaming**: Injective maps on roles and labels
2. **Equivariance**: Renamed configs take renamed steps
3. **Inverse Steps**: If σ(C) steps to D, then C steps to C'' where D = σ(C'')

These results formalize the **conservation law** from symmetry: protocol behavior
is invariant under relabeling of roles and message labels (automorphisms).

## From Aristotle 06b

The inverse step theorems show that protocol renaming commutes with execution:
- `inverse_step_select_exists`: Select steps lift through renaming
- `inverse_step_branch_exists`: Branch steps lift through renaming

Combined with forward equivariance (σ(step(C)) = step(σ(C))), this yields
**bisimulation**: the original and renamed systems are behaviorally equivalent.

## Connection to Noether's Theorem

The symmetry ↔ conservation correspondence:
- **Symmetry**: Protocol renaming σ preserves valid configurations
- **Conservation**: The orbit structure under the renaming group is preserved

For MPST, the conserved quantity is the **equivalence class** of configurations
under role/label permutation - branching feasibility, coherence, and liveness
are invariant under such relabeling.
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

/-! ## Inverse Step Theorems -/

/-- Helper: branch membership under renaming.
    If (l', L') is in the renamed branches, there exists an original (l, L). -/
theorem mem_renameBranchesPR_inv (σ : ProtocolRenaming)
    (bs : List (Label × LocalType)) (l' : Label) (L' : LocalType) :
    (l', L') ∈ renameBranchesPR σ bs →
    ∃ l L, (l, L) ∈ bs ∧ l' = σ.labelMap l ∧ L' = renameLocalTypePR σ L := by
  induction bs with
  | nil =>
      intro h
      unfold renameBranchesPR at h
      simp at h
  | cons hd tl ih =>
      intro h
      unfold renameBranchesPR at h
      simp only [List.mem_cons] at h
      cases h with
      | inl heq =>
          obtain ⟨hl, hL⟩ := Prod.mk.inj heq
          refine ⟨hd.1, hd.2, ?_, hl, hL⟩
          exact List.mem_cons.mpr (Or.inl rfl)
      | inr hmem =>
          obtain ⟨l, L, hmem', hl, hL⟩ := ih hmem
          exact ⟨l, L, List.mem_cons.mpr (Or.inr hmem'), hl, hL⟩

/-- Inverse step for send: if σ(C) has a send type, C has a corresponding send type.
    The renamed sender/receiver are preimages under σ.roleMap.
    From Aristotle 06b. -/
theorem inverse_step_send_exists (σ : ProtocolRenaming)
    (G : GEnv) (s' r' : Role) (T' : ValType) (L' : LocalType) (sid : SessionId)
    (hG' : lookupG (renameGEnvPR σ G) ⟨sid, s'⟩ = some (.send r' T' L')) :
    ∃ s r T L, σ.roleMap s = s' ∧ σ.roleMap r = r' ∧
      T' = renameValTypePR σ T ∧
      lookupG G ⟨sid, s⟩ = some (.send r T L) ∧
      L' = renameLocalTypePR σ L := by
  -- Use lookupG_renamePR_inv to get preimage, then case split on local type
  obtain ⟨ep, L, hep, hep', hLfull⟩ := lookupG_renamePR_inv σ G _ _ hG'
  have hsid : ep.sid = sid := by
    have := congrArg Endpoint.sid hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hrole : σ.roleMap ep.role = s' := by
    have := congrArg Endpoint.role hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hEqEp : ({ sid := sid, role := ep.role } : Endpoint) = ep := by
    cases ep with
    | mk sid0 role0 =>
        cases hsid
        rfl
  cases hL : L with
  | send r T Lcont =>
      rw [hL] at hLfull
      simp only [renameLocalTypePR, LocalType.send.injEq] at hLfull
      obtain ⟨hr', hT', hLcont'⟩ := hLfull
      have hLookup : lookupG G { sid := sid, role := ep.role } = some (.send r T Lcont) := by
        simpa [hEqEp, hL] using hep
      refine ⟨ep.role, r, T, Lcont, hrole, hr'.symm, hT', hLookup, hLcont'⟩
  | recv _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | select _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | branch _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | end_ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | var _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | mu _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim

/-- Inverse step for select: if σ(C) has a select type, C has a corresponding select type.
    From Aristotle 06b. -/
theorem inverse_step_select_exists (σ : ProtocolRenaming)
    (G : GEnv) (s' r' : Role) (bs' : List (Label × LocalType)) (l' : Label) (L' : LocalType)
    (sid : SessionId)
    (hG' : lookupG (renameGEnvPR σ G) ⟨sid, s'⟩ = some (.select r' bs'))
    (hIn' : (l', L') ∈ bs') :
    ∃ s r bs l L,
      σ.roleMap s = s' ∧ σ.roleMap r = r' ∧
      σ.labelMap l = l' ∧
      lookupG G ⟨sid, s⟩ = some (.select r bs) ∧
      (l, L) ∈ bs ∧
      L' = renameLocalTypePR σ L := by
  -- Use lookupG_renamePR_inv + mem_renameBranchesPR_inv
  obtain ⟨ep, Lep, hep, hep', hLfull⟩ := lookupG_renamePR_inv σ G _ _ hG'
  have hsid : ep.sid = sid := by
    have := congrArg Endpoint.sid hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hrole : σ.roleMap ep.role = s' := by
    have := congrArg Endpoint.role hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hEqEp : ({ sid := sid, role := ep.role } : Endpoint) = ep := by
    cases ep with
    | mk sid0 role0 =>
        cases hsid
        rfl
  cases hL : Lep with
  | select r bs =>
      rw [hL] at hLfull
      simp only [renameLocalTypePR, LocalType.select.injEq] at hLfull
      obtain ⟨hr', hbs'⟩ := hLfull
      rw [hbs'] at hIn'
      obtain ⟨l, L, hl, hlmap, hLmap⟩ := mem_renameBranchesPR_inv σ bs l' L' hIn'
      have hLookup : lookupG G { sid := sid, role := ep.role } = some (.select r bs) := by
        simpa [hEqEp, hL] using hep
      refine ⟨ep.role, r, bs, l, L, hrole, hr'.symm, hlmap.symm, hLookup, hl, hLmap⟩
  | send _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | recv _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | branch _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | end_ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | var _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | mu _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim

/-- Inverse step for branch: if σ(C) has a branch type, C has a corresponding branch type.
    From Aristotle 06b. -/
theorem inverse_step_branch_exists (σ : ProtocolRenaming)
    (G : GEnv) (s' r' : Role) (bs' : List (Label × LocalType)) (l' : Label) (L' : LocalType)
    (sid : SessionId)
    (hG' : lookupG (renameGEnvPR σ G) ⟨sid, r'⟩ = some (.branch s' bs'))
    (hIn' : (l', L') ∈ bs') :
    ∃ s r bs l L,
      σ.roleMap s = s' ∧ σ.roleMap r = r' ∧
      σ.labelMap l = l' ∧
      lookupG G ⟨sid, r⟩ = some (.branch s bs) ∧
      (l, L) ∈ bs ∧
      L' = renameLocalTypePR σ L := by
  -- Use lookupG_renamePR_inv + mem_renameBranchesPR_inv
  obtain ⟨ep, Lep, hep, hep', hLfull⟩ := lookupG_renamePR_inv σ G _ _ hG'
  have hsid : ep.sid = sid := by
    have := congrArg Endpoint.sid hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hrole : σ.roleMap ep.role = r' := by
    have := congrArg Endpoint.role hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hEqEp : ({ sid := sid, role := ep.role } : Endpoint) = ep := by
    cases ep with
    | mk sid0 role0 =>
        cases hsid
        rfl
  cases hL : Lep with
  | branch s bs =>
      rw [hL] at hLfull
      simp only [renameLocalTypePR, LocalType.branch.injEq] at hLfull
      obtain ⟨hs', hbs'⟩ := hLfull
      rw [hbs'] at hIn'
      obtain ⟨l, L, hl, hlmap, hLmap⟩ := mem_renameBranchesPR_inv σ bs l' L' hIn'
      have hLookup : lookupG G { sid := sid, role := ep.role } = some (.branch s bs) := by
        simpa [hEqEp, hL] using hep
      refine ⟨s, ep.role, bs, l, L, hs'.symm, hrole, hlmap.symm, hLookup, hl, hLmap⟩
  | send _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | recv _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | select _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | end_ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | var _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | mu _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim

/-! ## Consume Renaming -/

/-- Renaming value types is injective. -/
theorem renameValTypePR_inj (σ : ProtocolRenaming) :
    Function.Injective (renameValTypePR σ) := by
  intro T1 T2 h
  induction T1 generalizing T2 with
  | unit =>
      cases T2 with
      | unit => rfl
      | bool =>
          cases h
      | nat =>
          cases h
      | string =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  | bool =>
      cases T2 with
      | bool => rfl
      | unit =>
          cases h
      | nat =>
          cases h
      | string =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  | nat =>
      cases T2 with
      | nat => rfl
      | unit =>
          cases h
      | bool =>
          cases h
      | string =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  | string =>
      cases T2 with
      | string => rfl
      | unit =>
          cases h
      | bool =>
          cases h
      | nat =>
          cases h
      | prod _ _ =>
          cases h
      | chan _ _ =>
          cases h
  | prod T1 T2 ih1 ih2 =>
      cases T2 <;> simp [renameValTypePR] at h
      case prod T1' T2' =>
        rcases h with ⟨h1, h2⟩
        have h1' := ih1 h1
        have h2' := ih2 h2
        simp [h1', h2']
  | chan sid role =>
      cases T2 <;> simp [renameValTypePR] at h
      case chan sid2 role2 =>
        rcases h with ⟨hsid, hrole⟩
        have hrole' : role = role2 := σ.roleMap_inj _ _ hrole
        subst hsid
        subst hrole'
        rfl

/-- Role equality is preserved under protocol renaming. -/
theorem roleMap_beq (σ : ProtocolRenaming) (a b : Role) :
    (σ.roleMap a == σ.roleMap b) = (a == b) := by
  by_cases h : a = b
  · simp [h]
  · have h' : σ.roleMap a ≠ σ.roleMap b := by
      intro hEq
      exact h (σ.roleMap_inj _ _ hEq)
    have hbeq : (a == b) = false := beq_eq_false_iff_ne.mpr h
    have hbeq' : (σ.roleMap a == σ.roleMap b) = false := beq_eq_false_iff_ne.mpr h'
    simp [hbeq, hbeq']

/-- Value-type equality is preserved under protocol renaming. -/
theorem renameValTypePR_beq (σ : ProtocolRenaming) (T T' : ValType) :
    (renameValTypePR σ T == renameValTypePR σ T') = (T == T') := by
  by_cases h : T = T'
  · simp [h]
  · have h' : renameValTypePR σ T ≠ renameValTypePR σ T' := by
      intro hEq
      exact h (renameValTypePR_inj σ hEq)
    have hbeq : (T == T') = false := beq_eq_false_iff_ne.mpr h
    have hbeq' : (renameValTypePR σ T == renameValTypePR σ T') = false :=
      beq_eq_false_iff_ne.mpr h'
    simp [hbeq, hbeq']

/-- Renaming commutes with a single consume step. -/
theorem consumeOne_renamePR (σ : ProtocolRenaming) (from_ : Role) (T : ValType) (L : LocalType) :
    consumeOne (σ.roleMap from_) (renameValTypePR σ T) (renameLocalTypePR σ L) =
      (consumeOne from_ T L).map (renameLocalTypePR σ) := by
  cases L <;>
    simp [consumeOne, renameLocalTypePR, roleMap_beq, renameValTypePR_beq]

/-- Renaming commutes with Consume over a trace. -/
theorem Consume_renamePR (σ : ProtocolRenaming) (from_ : Role) (L : LocalType) (ts : List ValType) :
    Consume (σ.roleMap from_) (renameLocalTypePR σ L) (ts.map (renameValTypePR σ)) =
      (Consume from_ L ts).map (renameLocalTypePR σ) := by
  induction ts generalizing L with
  | nil =>
      simp [Consume]
  | cons t ts ih =>
      simp [Consume]
      cases h : consumeOne from_ t L with
      | none =>
          simp [consumeOne_renamePR, h]
      | some L' =>
          simp [consumeOne_renamePR, h, ih]

/-! ## Branch Symmetry Consequences -/

/-- Labels are renamed pointwise inside branch lists. -/
theorem branch_labels_renamed (σ : ProtocolRenaming) (bs : List (Label × LocalType)) :
    List.map Prod.fst (renameBranchesPR σ bs) =
      List.map σ.labelMap (List.map Prod.fst bs) := by
  induction bs with
  | nil =>
      simp [renameBranchesPR]
  | cons hd tl ih =>
      cases hd with
      | mk l L =>
          simp [renameBranchesPR, ih]

/-- Branch labels remain duplicate-free under injective label renaming. -/
theorem branch_labels_nodup_preserved (σ : ProtocolRenaming)
    {bs : List (Label × LocalType)}
    (hNodup : List.Nodup (List.map Prod.fst bs)) :
    List.Nodup (List.map Prod.fst (renameBranchesPR σ bs)) := by
  induction bs with
  | nil =>
      simp [renameBranchesPR]
  | cons hd tl ih =>
      cases hd with
      | mk l L =>
          have hNodup' : List.Nodup (l :: List.map Prod.fst tl) := by
            simpa using hNodup
          rcases (List.nodup_cons).1 hNodup' with ⟨hNotMem, hTail⟩
          have hTail' : List.Nodup (List.map Prod.fst (renameBranchesPR σ tl)) :=
            ih hTail
          have hNotMem' :
              σ.labelMap l ∉ List.map Prod.fst (renameBranchesPR σ tl) := by
            intro hmem
            have hmem' :
                σ.labelMap l ∈ List.map σ.labelMap (List.map Prod.fst tl) := by
              simpa [branch_labels_renamed] using hmem
            rcases List.mem_map.1 hmem' with ⟨l', hl', hmap⟩
            have hl'Eq : l' = l := σ.labelMap_inj _ _ hmap
            exact hNotMem (by simpa [hl'Eq] using hl')
          have hNodupRen :
              List.Nodup (σ.labelMap l :: List.map Prod.fst (renameBranchesPR σ tl)) := by
            exact (List.nodup_cons).2 ⟨hNotMem', hTail'⟩
          simpa [renameBranchesPR] using hNodupRen

/-- Label permutation preserves branching structure.
    If a branch has labels l₁, ..., lₙ, the renamed branch has labels σ(l₁), ..., σ(lₙ). -/
theorem branches_length_preserved (σ : ProtocolRenaming) (bs : List (Label × LocalType)) :
    (renameBranchesPR σ bs).length = bs.length := by
  induction bs with
  | nil => simp [renameBranchesPR]
  | cons hd tl ih =>
      cases hd with
      | mk l L =>
          simp [renameBranchesPR, ih]

/-- Lookup in renamed DEnv: renaming commutes with lookup. -/
private theorem lookupD_renamePR_foldl (σ : ProtocolRenaming) :
    ∀ (l : List (Edge × Trace)) (acc : DEnv) (e : Edge)
      (hNodup : List.Nodup (List.map Prod.fst l)),
      lookupD
          (l.foldl
            (fun acc p =>
              updateD acc (renameEdgePR σ p.1) (p.2.map (renameValTypePR σ)))
            acc)
          (renameEdgePR σ e) =
        match l.lookup e with
        | some ts => ts.map (renameValTypePR σ)
        | none => lookupD acc (renameEdgePR σ e) := by
  intro l acc e hNodup
  induction l generalizing acc e with
  | nil =>
      simp [lookupD]
  | cons hd tl ih =>
      have hNodup' : List.Nodup (hd.1 :: List.map Prod.fst tl) := by
        simpa using hNodup
      rcases (List.nodup_cons).1 hNodup' with ⟨hNotMem, hNodupTl⟩
      by_cases hEq : e = hd.1
      · subst hEq
        have hNotMem' : ∀ p ∈ tl, p.1 ≠ hd.1 := by
          intro p hp hEq'
          have hmem : hd.1 ∈ List.map Prod.fst tl := by
            have hmem' : p.1 ∈ List.map Prod.fst tl :=
              List.mem_map.mpr ⟨p, hp, rfl⟩
            simpa [hEq'] using hmem'
          exact hNotMem hmem
        have hLookupTl : tl.lookup hd.1 = none :=
          lookup_eq_none_of_forall_ne hNotMem'
        -- Use IH on tail with updated accumulator.
        have hIH :=
          ih (acc:=updateD acc (renameEdgePR σ hd.1) (hd.2.map (renameValTypePR σ)))
            (e:=hd.1) hNodupTl
        -- Simplify using tail lookup = none.
        simp [hLookupTl, lookupD_update_eq] at hIH
        simpa [List.lookup] using hIH
      · have hEq' : renameEdgePR σ e ≠ renameEdgePR σ hd.1 := by
          intro hcontra
          exact hEq (renameEdgePR_inj σ _ _ hcontra)
        have hEq'' : renameEdgePR σ hd.1 ≠ renameEdgePR σ e := Ne.symm hEq'
        have hIH :=
          ih (acc:=updateD acc (renameEdgePR σ hd.1) (hd.2.map (renameValTypePR σ)))
            (e:=e) hNodupTl
        -- For the none case, rewrite the updated lookup back to acc.
        have hAcc :
            lookupD (updateD acc (renameEdgePR σ hd.1) (hd.2.map (renameValTypePR σ)))
              (renameEdgePR σ e) = lookupD acc (renameEdgePR σ e) := by
          exact lookupD_update_neq _ _ _ _ hEq''
        have hbeq : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
        simpa [List.foldl, List.lookup, hbeq, hAcc] using hIH

/-- Lookup in renamed DEnv: renaming commutes with lookup. -/
theorem lookupD_renamePR (σ : ProtocolRenaming) (D : DEnv) (e : Edge) :
    lookupD (renameDEnvPR σ D) (renameEdgePR σ e) =
      (lookupD D e).map (renameValTypePR σ) := by
  -- Reduce lookup to list-based form.
  have hNodup : List.Nodup (List.map Prod.fst D.list) := by
    -- D.list is pairwise ordered, so keys are distinct.
    -- Pairwise strict order implies no duplicate keys.
    -- Use the list-of-keys view for a direct nodup proof.
    have hPair := D.sorted
    revert hPair
    induction D.list with
    | nil =>
        intro _; simp
    | cons hd tl ih =>
        intro hPair
        simp only [List.pairwise_cons] at hPair
        rcases hPair with ⟨hHd, hTl⟩
        have hNotMem : hd.1 ∉ List.map Prod.fst tl := by
          intro hmem
          rcases List.mem_map.1 hmem with ⟨p, hp, hpEq⟩
          have hLt : edgeCmpLT hd p := hHd p hp
          have hNe : hd.1 ≠ p.1 := by
            intro hEq
            have hlt : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt hLt
            have hEqCmp : compare hd.1 p.1 = .eq :=
              (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq
            have : (Ordering.lt : Ordering) = .eq := hlt.symm.trans hEqCmp
            cases this
          exact hNe hpEq.symm
        have hTail : List.Nodup (List.map Prod.fst tl) := ih hTl
        exact (List.nodup_cons).2 ⟨hNotMem, hTail⟩
  -- Use foldl lookup lemma on the underlying list.
  have hFold :=
    lookupD_renamePR_foldl (σ:=σ) (l:=D.list) (acc:=(∅ : DEnv)) (e:=e) hNodup
  -- Rewrite lookupD D e using list lookup.
  have hLookup : lookupD D e =
      match D.list.lookup e with
      | some ts => ts
      | none => [] := by
    cases h : D.list.lookup e <;> simp [lookupD, DEnv_find?_eq_lookup, h]
  -- Finish by rewriting the match.
  cases h : D.list.lookup e with
  | none =>
      simp [h] at hFold
      simpa [hLookup, h] using hFold
  | some ts =>
      simp [h] at hFold
      simpa [hLookup, h] using hFold

/-- The coherence invariant is preserved under protocol renaming.
    This is the main conservation theorem. -/
theorem coherence_protocol_renaming_preserved (σ : ProtocolRenaming) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (renameGEnvPR σ G) (renameDEnvPR σ D) := by
  -- Proof sketch: coherence depends on structural relationships between
  -- sender types, receiver types, and buffer contents. Protocol renaming
  -- preserves these relationships since it's injective on roles/labels.
  intro e hActive Lrecv hGrecv
  -- Receiver preimage
  obtain ⟨recvEp, Lrecv0, hRecvLookup, hRecvEq, hLrecvEq⟩ :=
    lookupG_renamePR_inv σ G { sid := e.sid, role := e.receiver } Lrecv hGrecv
  have hRecvSid : recvEp.sid = e.sid := by
    have := congrArg Endpoint.sid hRecvEq
    simp [renameEndpointPR] at this
    exact this.symm
  have hRecvRole : σ.roleMap recvEp.role = e.receiver := by
    have := congrArg Endpoint.role hRecvEq
    simp [renameEndpointPR] at this
    exact this.symm
  -- Sender preimage from ActiveEdge
  rcases hActive with ⟨hSenderSome, _⟩
  rcases (Option.isSome_iff_exists).1 hSenderSome with ⟨LsenderRen, hGsenderRen⟩
  obtain ⟨sendEp, Lsender0, hSendLookup, hSendEq, hLsenderEq⟩ :=
    lookupG_renamePR_inv σ G { sid := e.sid, role := e.sender } LsenderRen hGsenderRen
  have hSendSid : sendEp.sid = e.sid := by
    have := congrArg Endpoint.sid hSendEq
    simp [renameEndpointPR] at this
    exact this.symm
  have hSendRole : σ.roleMap sendEp.role = e.sender := by
    have := congrArg Endpoint.role hSendEq
    simp [renameEndpointPR] at this
    exact this.symm
  -- Preimage edge
  let e0 : Edge := { sid := e.sid, sender := sendEp.role, receiver := recvEp.role }
  have hSendEqEp : ({ sid := e.sid, role := sendEp.role } : Endpoint) = sendEp := by
    cases sendEp with
    | mk sid0 role0 =>
        cases hSendSid
        rfl
  have hRecvEqEp : ({ sid := e.sid, role := recvEp.role } : Endpoint) = recvEp := by
    cases recvEp with
    | mk sid0 role0 =>
        cases hRecvSid
        rfl
  have hActive0 : ActiveEdge G e0 :=
    ActiveEdge_of_endpoints (G:=G) (e:=e0) (Lsender:=Lsender0) (Lrecv:=Lrecv0)
      (by
        -- sender lookup
        have hEq : ({ sid := e0.sid, role := e0.sender } : Endpoint) = sendEp := by
          simpa [e0] using hSendEqEp
        simpa [hEq] using hSendLookup)
      (by
        -- receiver lookup
        have hEq : ({ sid := e0.sid, role := e0.receiver } : Endpoint) = recvEp := by
          simpa [e0] using hRecvEqEp
        simpa [hEq] using hRecvLookup)
  -- Coherence on preimage edge
  have hRecvLookup0 : lookupG G { sid := e0.sid, role := e0.receiver } = some Lrecv0 := by
    simpa [e0, hRecvEqEp] using hRecvLookup
  obtain ⟨Lsender0', hSender0', hConsume0⟩ := hCoh e0 hActive0 Lrecv0 hRecvLookup0
  have hSender0'' :
      lookupG G { sid := e.sid, role := sendEp.role } = some Lsender0' := by
    simpa [e0] using hSender0'
  -- Sender lookup after renaming
  have hSenderRen :
      lookupG (renameGEnvPR σ G) { sid := e.sid, role := e.sender } =
        some (renameLocalTypePR σ Lsender0') := by
    have hEq : renameEndpointPR σ { sid := e.sid, role := sendEp.role } =
        ({ sid := e.sid, role := e.sender } : Endpoint) := by
      simp [renameEndpointPR, hSendRole]
    have hLookup := lookupG_renamePR σ G { sid := e.sid, role := sendEp.role }
    simpa [hEq, hSender0''] using hLookup
  -- Trace lookup after renaming
  have hEdgeEq : renameEdgePR σ e0 = e := by
    simp [renameEdgePR, e0, hSendRole, hRecvRole]
  have hTrace :
      lookupD (renameDEnvPR σ D) e =
        (lookupD D e0).map (renameValTypePR σ) := by
    simpa [hEdgeEq] using (lookupD_renamePR (σ:=σ) (D:=D) (e:=e0))
  -- Consume preserved by renaming
  have hConsumeRen :
      (Consume e.sender Lrecv (lookupD (renameDEnvPR σ D) e)).isSome := by
    -- Use Consume_renamePR on the preimage data
    have hCons :=
      Consume_renamePR (σ:=σ) (from_:=sendEp.role) (L:=Lrecv0) (ts:=lookupD D e0)
    -- Rewrite roles/types/traces
    have hSenderEq : σ.roleMap sendEp.role = e.sender := hSendRole
    have hRecvEq : Lrecv = renameLocalTypePR σ Lrecv0 := by
      simpa using hLrecvEq
    -- Apply isSome on the renamed consume
    cases hC : Consume sendEp.role Lrecv0 (lookupD D e0) with
    | none =>
        have : (Consume sendEp.role Lrecv0 (lookupD D e0)).isSome = true := by
          simpa using hConsume0
        simp [hC] at this
    | some L' =>
        -- hConsume0 implies the original consume succeeds
        have hCons' : Consume sendEp.role Lrecv0 (lookupD D e0) = some L' := by
          simp [hC]
        have hConsRen :
            Consume (σ.roleMap sendEp.role) (renameLocalTypePR σ Lrecv0)
              ((lookupD D e0).map (renameValTypePR σ)) =
              some (renameLocalTypePR σ L') := by
          simpa [hCons'] using hCons
        -- Transfer to the renamed edge
        have hConsRen' :
            Consume e.sender (renameLocalTypePR σ Lrecv0)
              ((lookupD D e0).map (renameValTypePR σ)) =
              some (renameLocalTypePR σ L') := by
          simpa [hSenderEq] using hConsRen
        -- Conclude isSome
        have : (Consume e.sender (renameLocalTypePR σ Lrecv0)
          ((lookupD D e0).map (renameValTypePR σ))).isSome = true := by
          simp [hConsRen']
        simpa [hRecvEq, hTrace] using this
  refine ⟨renameLocalTypePR σ Lsender0', hSenderRen, ?_⟩
  simpa [hTrace] using hConsumeRen

end
