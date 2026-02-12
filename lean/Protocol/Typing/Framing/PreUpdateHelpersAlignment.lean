import Protocol.Typing.Framing.PreUpdateHelpersCore

/-! # Typing Framing: Pre-Update Alignment

Alignment helpers for framed step cases built on pre-update helper foundations.
-/

/-
The Problem. Framing proofs need constructor-level alignment facts (send/recv/
select/branch) across left/right frames and framed update reconstruction.

Solution Structure.
1. Prove left-frame constructor alignment lemmas.
2. Prove symmetric right-frame alignment lemmas.
3. Add framed store-typing swap helper for owned-left reordering.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section
/-! ## Left-Frame Helpers (Step Cases) -/

/-- Helper: align the local type in a send step under a right frame. -/
lemma send_localtype_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role} {T T' : ValType}
    {L L' : LocalType} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.send q T' L') →
    lookupG G e = some (.send target T L) →
    L' = L := by
  -- Rewrite the global lookup through the left frame and compare constructors.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.send q T' L') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.send q T' L') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.send target T L) = some (LocalType.send q T' L') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the types in a recv step under a right frame. -/
lemma recv_types_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role} {T T' : ValType}
    {L L' : LocalType} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.recv p T' L') →
    lookupG G e = some (.recv source T L) →
    T' = T ∧ L' = L := by
  -- Compare the recv constructors after rewriting the left-framed lookup.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.recv p T' L') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.recv p T' L') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.recv source T L) = some (LocalType.recv p T' L') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  exact ⟨rfl, rfl⟩

/-! ## Left-Frame Alignment Helpers -/

/-- Helper: align the branches in a select step under a right frame. -/
lemma select_branches_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role}
    {bs bs' : List (Label × LocalType)} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.select q bs') →
    lookupG G e = some (.select target bs) →
    bs' = bs := by
  -- Compare the select constructors after rewriting the left-framed lookup.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.select q bs') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.select q bs') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.select target bs) = some (LocalType.select q bs') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the branches in a branch step under a right frame. -/
lemma branch_branches_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role}
    {bs bs' : List (Label × LocalType)} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.branch p bs') →
    lookupG G e = some (.branch source bs) →
    bs' = bs := by
  -- Compare the branch constructors after rewriting the left-framed lookup.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.branch p bs') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.branch p bs') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.branch source bs) = some (LocalType.branch p bs') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  rfl

/-! ## Left-Frame Branch Lookup Helpers -/

/-- Helper: align the chosen label in a select step. -/
lemma select_label_eq
    {bs bs' : List (Label × LocalType)} {ℓ : Label} {L L' : LocalType} :
    bs' = bs →
    bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L') →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    L' = L := by
  -- Rewrite the branch list and compare the `find?` results.
  intro hBs hFind' hFind
  subst hBs
  have hEq : some (ℓ, L) = some (ℓ, L') := by
    simpa [hFind] using hFind'
  cases hEq
  rfl

/-- Helper: transport branch lookup across equal branch lists. -/
lemma branch_find_eq
    {bs bs' : List (Label × LocalType)} {ℓ : Label} {L : LocalType} :
    bs' = bs →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L) := by
  -- Rewrite the branch list and reuse the original lookup.
  intro hBs hFind
  simpa [hBs] using hFind

/-! ## Right-Frame Alignment Helpers -/

/-- Helper: align the local type in a send step under a left frame. -/
lemma send_localtype_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role} {T T' : ValType}
    {L L' : LocalType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.send q T' L') →
    lookupG G e = some (.send target T L) →
    L' = L := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.send q T' L') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.send q T' L') := by
    simpa [hEq] using hLookup
  have : some (LocalType.send target T L) = some (LocalType.send q T' L') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the types in a recv step under a left frame. -/
lemma recv_types_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role} {T T' : ValType}
    {L L' : LocalType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.recv p T' L') →
    lookupG G e = some (.recv source T L) →
    T' = T ∧ L' = L := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.recv p T' L') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.recv p T' L') := by
    simpa [hEq] using hLookup
  have : some (LocalType.recv source T L) = some (LocalType.recv p T' L') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  exact ⟨rfl, rfl⟩

/-! ## Right-Frame Branch Constructor Alignment -/

/-- Helper: align the branches in a select step under a left frame. -/
lemma select_branches_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role}
    {bs bs' : List (Label × LocalType)} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.select q bs') →
    lookupG G e = some (.select target bs) →
    bs' = bs := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.select q bs') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.select q bs') := by
    simpa [hEq] using hLookup
  have : some (LocalType.select target bs) = some (LocalType.select q bs') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the branches in a branch step under a left frame. -/
lemma branch_branches_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role}
    {bs bs' : List (Label × LocalType)} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.branch p bs') →
    lookupG G e = some (.branch source bs) →
    bs' = bs := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.branch p bs') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.branch p bs') := by
    simpa [hEq] using hLookup
  have : some (LocalType.branch source bs) = some (LocalType.branch p bs') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  rfl

/-! ## Right-Frame Update And Store Helpers -/

/-- Helper: pull a right update out of a left-framed G. -/
lemma updateG_right_of_step
    {G₁ G₂ G G' G₂' : GEnv} {e : Endpoint} {L L0 : LocalType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    lookupG G₂ e = some L0 →
    updateG G e L = G' →
    G₂' = updateG G₂ e L := by
  -- Rewrite the update and cancel the shared left frame.
  intro hDisj hEq hEq' hG₂e hGout
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hUpd : updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  apply append_right_eq_of_eq
  calc
    G₁ ++ G₂' = updateG (G₁ ++ G₂) e L := by
      simpa [hEq, hEq'] using hGout.symm
    _ = G₁ ++ updateG G₂ e L := by simpa [hUpd]

/-- Helper: swap the left-owned prefix inside store typing. -/
lemma store_typed_left_swap
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} {S1 S2 : SEnv} :
    StoreTyped Gstore (SEnvAll Ssh { right := Sown.right, left := S1 ++ S2 }) store →
    DisjointS S1 S2 →
    StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ S2, left := S1 }) store := by
  -- Use the swap lemma to reorder the left-owned environment.
  intro hStore hDisj x v T hStoreX hLookup
  have hLookup' :
      lookupSEnv (Ssh ++ (Sown.right ++ (S2 ++ S1))) x = some T := by
    simpa [SEnvAll, List.append_assoc] using hLookup
  have hSwap :=
    lookupSEnv_swap_left_prefix (Ssh:=Ssh ++ Sown.right) (S₁:=S2) (S₂:=S1) (S₃:=(∅ : SEnv))
      (DisjointS_symm hDisj) x
  have hSwap' :
      lookupSEnv (Ssh ++ (Sown.right ++ (S2 ++ S1))) x =
        lookupSEnv (Ssh ++ (Sown.right ++ (S1 ++ S2))) x := by
    simpa [SEnvAll, List.append_assoc] using hSwap
  have hLookup'' :
      lookupSEnv (Ssh ++ (Sown.right ++ (S1 ++ S2))) x = some T := by
    simpa [hSwap'] using hLookup'
  exact hStore x v T hStoreX (by simpa [SEnvAll, List.append_assoc] using hLookup'')

end
