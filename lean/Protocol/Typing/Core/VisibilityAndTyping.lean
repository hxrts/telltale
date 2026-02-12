import Protocol.Typing.Core.Environments

/-! # Protocol.Typing.Core.VisibilityAndTyping

Gauge-visible environments and core typing judgments.
-/

/-
The Problem. Typing uses a gauge-invariant visible environment view and core
process typing judgments that build on the environment algebra.

Solution Structure. Defines visible/gauge views and the typing judgments.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
open Batteries

section

/-! ## Disjointness Lemmas -/

theorem DisjointS_symm {S₁ S₂ : SEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₂ S₁ := by
  intro hDisj x T₁ T₂ hL1 hL2
  exact hDisj x T₂ T₁ hL2 hL1

theorem lookupSEnv_none_of_disjoint_left {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv S₂ x = some T →
    lookupSEnv S₁ x = none := by
  intro hDisj hL2
  by_cases hNone : lookupSEnv S₁ x = none
  · exact hNone
  · cases hL1 : lookupSEnv S₁ x with
    | none => exact (hNone hL1).elim
    | some T₁ =>
        exact (hDisj x T₁ T hL1 hL2).elim

/-- Combined variable environment: shared first, then owned (right ++ left). -/
def SEnvAll (Ssh : SEnv) (Sown : OwnedEnv) : SEnv :=
  Ssh ++ Sown.right ++ Sown.left

/-! ## Gauge-Invariant View

`Sown.right` is a frame/gauge component. Typing obligations that should be
invariant under quotienting read variables through the visible view below. -/
/-- Right-gauge equivalence for owned environments.
    Two owned environments are gauge-equivalent when they agree on the local
    left component; the right component is treated as framing gauge. -/
/-! ## Gauge Equivalence Laws -/
def RightGaugeEq (S₁ S₂ : OwnedEnv) : Prop :=
  S₁.left = S₂.left

/-- Right-gauge equivalence is reflexive. -/
theorem RightGaugeEq_refl (S : OwnedEnv) : RightGaugeEq S S := by
  rfl

/-- Right-gauge equivalence is symmetric. -/
theorem RightGaugeEq_symm {S₁ S₂ : OwnedEnv} :
    RightGaugeEq S₁ S₂ → RightGaugeEq S₂ S₁ := by
  intro h
  simpa [RightGaugeEq] using h.symm

/-- Right-gauge equivalence is transitive. -/
theorem RightGaugeEq_trans {S₁ S₂ S₃ : OwnedEnv} :
    RightGaugeEq S₁ S₂ → RightGaugeEq S₂ S₃ → RightGaugeEq S₁ S₃ := by
  intro h12 h23
  simpa [RightGaugeEq] using h12.trans h23

@[simp] theorem RightGaugeEq_iff_left_eq {S₁ S₂ : OwnedEnv} :
    RightGaugeEq S₁ S₂ ↔ S₁.left = S₂.left := by
  rfl

/-- Visible variable environment for typing obligations (shared + local left). -/
/-! ## Visible Environment View -/
def SEnvVisible (Ssh : SEnv) (Sown : OwnedEnv) : SEnv :=
  Ssh ++ Sown.left

/-- Store typing through the visible variable view (`Ssh ++ Sown.left`). -/
def StoreTypedVisible (G : GEnv) (Ssh : SEnv) (Sown : OwnedEnv) (store : VarStore) : Prop :=
  StoreTyped G (SEnvVisible Ssh Sown) store

/-! ## Strong Visible Store Typing -/
@[simp] theorem StoreTypedVisible_reframe_right
    (G : GEnv) (Ssh R R' L : SEnv) (store : VarStore) :
    StoreTypedVisible G Ssh { right := R, left := L } store ↔
      StoreTypedVisible G Ssh { right := R', left := L } store := by
  simp [StoreTypedVisible, SEnvVisible]

/-- Strong store typing with domain control on the full env and type
    correspondence on the visible view. -/
structure StoreTypedStrongVisible (G : GEnv) (Ssh : SEnv) (Sown : OwnedEnv)
    (store : VarStore) : Prop where
  /-- Keep same-domain over the full environment used by runtime invariants. -/
  sameDomainAll : ∀ x, (lookupSEnv (SEnvAll Ssh Sown) x).isSome ↔ (lookupStr store x).isSome
  /-- Type correspondence is only required for visible variables. -/
  typeCorrVisible : StoreTypedVisible G Ssh Sown store

/-- Forget the strong visible structure to plain visible store typing. -/
theorem StoreTypedStrongVisible.toStoreTypedVisible
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    (h : StoreTypedStrongVisible G Ssh Sown store) :
    StoreTypedVisible G Ssh Sown store :=
  h.typeCorrVisible

/-- Visible bindings are domain-included in the full environment (`shared ++ right ++ left`). -/
/-! ## Visible-to-Full Domain Bridge -/
theorem SEnvDomSubset_visible_all {Ssh : SEnv} {Sown : OwnedEnv} :
    SEnvDomSubset (SEnvVisible Ssh Sown) (SEnvAll Ssh Sown) := by
  intro x T hVis
  cases hSh : lookupSEnv Ssh x with
  | some Tsh =>
      have hAllSh : lookupSEnv (SEnvAll Ssh Sown) x = some Tsh := by
        have hLeft :=
          lookupSEnv_append_left (S₁:=Ssh) (S₂:=Sown.right ++ Sown.left) (x:=x) (T:=Tsh) hSh
        simpa [SEnvAll, List.append_assoc] using hLeft
      exact ⟨Tsh, hAllSh⟩
  | none =>
      have hLeft : lookupSEnv Sown.left x = some T := by
        have hEq := lookupSEnv_append_right (S₁:=Ssh) (S₂:=Sown.left) (x:=x) hSh
        simpa [SEnvVisible, hEq] using hVis
      cases hR : lookupSEnv Sown.right x with
      | some Tr =>
          have hOwn : lookupSEnv (Sown.right ++ Sown.left) x = some Tr :=
            lookupSEnv_append_left (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=Tr) hR
          have hAll : lookupSEnv (SEnvAll Ssh Sown) x = some Tr := by
            have hEq := lookupSEnv_append_right (S₁:=Ssh) (S₂:=Sown.right ++ Sown.left) (x:=x) hSh
            simpa [SEnvAll, List.append_assoc, hEq] using hOwn
          exact ⟨Tr, hAll⟩
      | none =>
          have hOwn : lookupSEnv (Sown.right ++ Sown.left) x = some T := by
            have hEqR := lookupSEnv_append_right (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) hR
            simpa [hEqR] using hLeft
          have hAll : lookupSEnv (SEnvAll Ssh Sown) x = some T := by
            have hEq := lookupSEnv_append_right (S₁:=Ssh) (S₂:=Sown.right ++ Sown.left) (x:=x) hSh
            simpa [SEnvAll, List.append_assoc, hEq] using hOwn
          exact ⟨T, hAll⟩

/-- Strong-visible store typing gives runtime lookup for any visible static lookup. -/
/-! ## Visible Lookup Extraction -/
theorem store_lookup_of_visible_lookup_strongVisible
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} {x : Var} {T : ValType}
    (hStore : StoreTypedStrongVisible G Ssh Sown store)
    (hVis : lookupSEnv (SEnvVisible Ssh Sown) x = some T) :
    ∃ v, lookupStr store x = some v ∧ HasTypeVal G v T := by
  have hSub : SEnvDomSubset (SEnvVisible Ssh Sown) (SEnvAll Ssh Sown) :=
    SEnvDomSubset_visible_all (Ssh:=Ssh) (Sown:=Sown)
  obtain ⟨T', hAll⟩ := hSub hVis
  have hInStore : (lookupStr store x).isSome := by
    have hDom := hStore.sameDomainAll x
    exact (hDom.mp (by simpa [hAll]))
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hInStore
  exact ⟨v, hv, hStore.typeCorrVisible x v T hv hVis⟩

/-! ## Visible Environment Reframing Lemmas -/
@[simp] theorem SEnvVisible_reframe_right
    (Ssh R R' L : SEnv) :
    SEnvVisible Ssh { right := R, left := L } =
      SEnvVisible Ssh { right := R', left := L } := by
  simp [SEnvVisible]

theorem SEnvVisible_updateLeft_of_shared_none
    {Ssh : SEnv} {Sown : OwnedEnv} {x : Var} {T : ValType}
    (hNoSh : lookupSEnv Ssh x = none) :
    SEnvVisible Ssh (Sown.updateLeft x T) =
      updateSEnv (SEnvVisible Ssh Sown) x T := by
  -- Rewrite update through an Ssh prefix where x is known absent.
  induction Ssh with
  | nil =>
      simp [SEnvVisible, OwnedEnv.updateLeft]
  | cons hd tl ih =>
      cases hd with
      | mk y U =>
          by_cases hxy : x = y
          · subst hxy
            simp [lookupSEnv] at hNoSh
          · have hNoTl : lookupSEnv tl x = none := by
              simpa [lookupSEnv, hxy] using hNoSh
            simpa [SEnvVisible, OwnedEnv.updateLeft, updateSEnv, hxy] using ih hNoTl

theorem SEnvVisible_congr_rightGauge {Ssh : SEnv} {S₁ S₂ : OwnedEnv} :
    RightGaugeEq S₁ S₂ →
    SEnvVisible Ssh S₁ = SEnvVisible Ssh S₂ := by
  intro h
  simpa [RightGaugeEq, SEnvVisible, h]

@[simp] theorem lookupSEnv_SEnvVisible_reframe_right
    (Ssh R R' L : SEnv) (x : Var) :
    lookupSEnv (SEnvVisible Ssh { right := R, left := L }) x =
      lookupSEnv (SEnvVisible Ssh { right := R', left := L }) x := by
  simp [SEnvVisible]

@[simp] theorem SEnvVisible_ofLeft (Ssh S : SEnv) :
    SEnvVisible Ssh (S : OwnedEnv) = Ssh ++ S := by
  simp [SEnvVisible]

@[simp] theorem SEnvAll_ofLeft (Ssh S : SEnv) :
    SEnvAll Ssh (S : OwnedEnv) = Ssh ++ S := by
  simp [SEnvAll]

@[simp] theorem SEnvAll_all (Ssh : SEnv) (Sown : OwnedEnv) :
    SEnvAll Ssh Sown = Ssh ++ (Sown : SEnv) := by
  simp [SEnvAll, OwnedEnv.all, List.append_assoc]

/-- Owned env disjointness between right and left portions. -/
def OwnedDisjoint (Sown : OwnedEnv) : Prop :=
  DisjointS Sown.right Sown.left

/-! ## SEnv and GEnv Update Transport -/
theorem updateSEnv_append_left {Ssh Sown : SEnv} {x : Var} {T : ValType}
    (h : lookupSEnv Ssh x = none) :
    updateSEnv (Ssh ++ Sown) x T = Ssh ++ updateSEnv Sown x T := by
  induction Ssh with
  | nil =>
      simp
  | cons hd tl ih =>
      cases hd with
      | mk y U =>
          by_cases hxy : x = y
          · subst hxy
            simp [lookupSEnv] at h
	          · have htl : lookupSEnv tl x = none := by
	              simpa [lookupSEnv, hxy] using h
	            simp [updateSEnv, hxy, ih htl]

/-! ## GEnv Update Transport -/
theorem updateG_append_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType}
    (h : lookupG G₁ e = none) :
    updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L := by
  induction G₁ with
  | nil =>
      simp
  | cons hd tl ih =>
      cases hd with
      | mk e' L' =>
          simp
          by_cases hxe : e = e'
          · -- Contradiction: lookup would be some at head.
            have hLookup : lookupG ((e', L') :: tl) e = some L' := by
              simp [lookupG, List.lookup, hxe]
            have hNone : lookupG ((e', L') :: tl) e = none := h
            have hContr : False := by
              simpa [hNone] using hLookup
            exact hContr.elim
          · have h' : lookupG tl e = none := by
              have hbeq : (e == e') = false := by
                exact beq_eq_false_iff_ne.mpr hxe
              simpa [lookupG, List.lookup, hbeq] using h
            simp [updateG, hxe, ih h']

/-- Updating a key that is already in the left GEnv only affects the left portion. -/
theorem updateG_append_left_hit {G₁ G₂ : GEnv} {e : Endpoint} {L L' : LocalType}
    (h : lookupG G₁ e = some L) :
    updateG (G₁ ++ G₂) e L' = updateG G₁ e L' ++ G₂ := by
  -- Find the matching endpoint in the left list and rebuild the append.
  induction G₁ with
  | nil =>
      simp [lookupG] at h
  | cons hd tl ih =>
      cases hd with
      | mk e' L'' =>
          by_cases hEq : e = e'
          · simp [updateG, hEq]
          · have h' : lookupG tl e = some L := by
              have hbeq : (e == e') = false := by
                exact beq_eq_false_iff_ne.mpr hEq
              simpa [lookupG, List.lookup, hbeq] using h
            simp [updateG, hEq, ih h']

/-- Process typing judgment.
    `HasTypeProcN n S G D P` means process P is well-typed under:
    - n: upper bound on session IDs
    - S: value type environment
    - G: session type environment
    - D: delayed type environment -/
/-! ## Core Process Typing Judgment -/
inductive HasTypeProcN : SessionId → SEnv → GEnv → DEnv → Process → Prop where
  /-- Skip is always well-typed. -/
  | skip {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} : HasTypeProcN n S G D .skip

  /-- Sequential composition. -/
  | seq {n S G D P Q} :
      HasTypeProcN n S G D P →
      HasTypeProcN n S G D Q →
      HasTypeProcN n S G D (.seq P Q)

  /-- Parallel composition (simplified, without linear splitting). -/
  | par {n S G D P Q nS nG} :
      HasTypeProcN n S G D P →
      HasTypeProcN n S G D Q →
      HasTypeProcN n S G D (.par nS nG P Q)

  /-- Send: send value x through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is send to some role q with payload type T
      - x has type T
      Updates G[e] to continuation L. -/
  | send {n S G D k x e q T L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.send q T L) →
      lookupSEnv S x = some T →
      HasTypeProcN n S (updateG G e L) D (.send k x)

  /-- Recv: receive into x through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is recv from some role p with payload type T
      Updates G[e] to continuation L, S[x] to T. -/
  | recv {n S G D k x e p T L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      HasTypeProcN n (updateSEnv S x T) (updateG G e L) D (.recv k x)

  /-- Select: send label ℓ through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is select to q with label ℓ in branches
      Updates G[e] to continuation for ℓ. -/
  | select {n S G D k e q bs ℓ L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.select q bs) →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      HasTypeProcN n S (updateG G e L) D (.select k ℓ)

  /-! ## Core Process Typing: Branch Constructor -/
  /-- Branch: receive and branch on label through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is branch from p with matching labels
      - each branch process is well-typed under its continuation -/
  | branch {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv}
      {k : Var} {e : Endpoint} {p : Role} {bs : List (Label × LocalType)} {procs : List (Label × Process)} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.branch p bs) →
      bs.length = procs.length →
      -- Label matching (non-recursive, pure data)
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
      -- Process typing (recursive)
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcN n S (updateG G e (bs.get ⟨i, hi⟩).2) D (procs.get ⟨i, hip⟩).2) →
      HasTypeProcN n S G D (.branch k procs)

  /-! ## Core Process Typing: Assignment and NewSession -/
  /-- Assign: assign a non-linear value to a variable. -/
  | assign {n S G D x v T} :
      HasTypeVal G v T →
      ¬T.isLinear →
      HasTypeProcN n (updateSEnv S x T) G D (.assign x v)

  /-- NewSession: create a new session.
      Allocates fresh session ID, creates endpoints for all roles. -/
  | newSession {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv}
      {roles : RoleSet} {f : Role → Var} {P : Process} (localTypes : Role → LocalType) :
      (∀ r, r ∈ roles →
        HasTypeProcN (n + 1)
          (updateSEnv S (f r) (.chan n r))
          (updateG G ⟨n, r⟩ (localTypes r))
          D P) →
      HasTypeProcN n S G D (.newSession roles f P)



end
