import Protocol.Coherence.EdgeCoherence
import Protocol.Environments.RoleRenaming

/-!
# Role Swap Renaming (Session-Local)

Defines a bijective (swap) role renaming inside a fixed session and proves
that coherence is preserved under this renaming. This is the minimal
role-abstraction lemma: any finite role permutation can be built from swaps.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Swap Renaming -/

/-- Swap two roles A and B, leaving all others unchanged. -/
def swapRole (A B : Role) (r : Role) : Role :=
  if r == A then B else if r == B then A else r

theorem swapRole_involutive (A B : Role) (r : Role) :
    swapRole A B (swapRole A B r) = r := by
  by_cases hA : r == A
  · have hA' : r = A := beq_iff_eq.1 hA
    subst hA
    simp [swapRole, beq_self_eq_true]
  · have hA' : r ≠ A := by
      exact (beq_eq_false_iff_ne (a:=r) (b:=A)).1 (by simpa using hA)
    by_cases hB : r == B
    · have hB' : r = B := beq_iff_eq.1 hB
      subst hB
      have hBA : (B == A) = false := beq_eq_false_iff_ne.mpr (by
        intro h; exact hA' h)
      simp [swapRole, hA, hB, hBA]
    · have hB' : r ≠ B := by
        exact (beq_eq_false_iff_ne (a:=r) (b:=B)).1 (by simpa using hB)
      simp [swapRole, hA, hB, hA', hB']

/-- Swap roles inside value types (only for endpoints in session s). -/
def swapValTypeRole (s : SessionId) (A B : Role) : ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod T₁ T₂ => .prod (swapValTypeRole s A B T₁) (swapValTypeRole s A B T₂)
  | .chan sid role =>
      if sid == s then
        .chan sid (swapRole A B role)
      else
        .chan sid role

mutual

/-- Swap roles inside a local type for session s. -/
def swapLocalTypeRole (s : SessionId) (A B : Role) : LocalType → LocalType
  | .send r T L => .send (swapRole A B r) (swapValTypeRole s A B T) (swapLocalTypeRole s A B L)
  | .recv r T L => .recv (swapRole A B r) (swapValTypeRole s A B T) (swapLocalTypeRole s A B L)
  | .select r bs => .select (swapRole A B r) (swapBranchesRole s A B bs)
  | .branch r bs => .branch (swapRole A B r) (swapBranchesRole s A B bs)
  | .end_ => .end_
  | .var n => .var n
  | .mu L => .mu (swapLocalTypeRole s A B L)
termination_by L => sizeOf L

/-- Swap roles inside branch lists for session s. -/
def swapBranchesRole (s : SessionId) (A B : Role) : List (Label × LocalType) → List (Label × LocalType)
  | [] => []
  | (l, L) :: bs => (l, swapLocalTypeRole s A B L) :: swapBranchesRole s A B bs
termination_by bs => sizeOf bs

end

/-- Swap a role in an endpoint, but only for session s. -/
def swapEndpointRole (s : SessionId) (A B : Role) (ep : Endpoint) : Endpoint :=
  if ep.sid == s then
    { sid := ep.sid, role := swapRole A B ep.role }
  else
    ep

/-- Swap roles in an edge, but only for session s. -/
def swapEdgeRole (s : SessionId) (A B : Role) (e : Edge) : Edge :=
  if e.sid == s then
    { sid := e.sid
      sender := swapRole A B e.sender
      receiver := swapRole A B e.receiver }
  else
    e

theorem swapEndpointRole_sid (s : SessionId) (A B : Role) (ep : Endpoint) :
    (swapEndpointRole s A B ep).sid = ep.sid := by
  by_cases hSid : ep.sid == s
  · simp [swapEndpointRole, hSid]
  · simp [swapEndpointRole, hSid]

theorem swapEdgeRole_sid (s : SessionId) (A B : Role) (e : Edge) :
    (swapEdgeRole s A B e).sid = e.sid := by
  by_cases hSid : e.sid == s
  · simp [swapEdgeRole, hSid]
  · simp [swapEdgeRole, hSid]

theorem swapEndpointRole_involutive (s : SessionId) (A B : Role) (ep : Endpoint) :
    swapEndpointRole s A B (swapEndpointRole s A B ep) = ep := by
  by_cases hSid : ep.sid == s
  · have hSid' : ep.sid = s := beq_iff_eq.1 hSid
    subst hSid'
    cases ep with
    | mk sid role =>
        simp [swapEndpointRole, swapRole_involutive, beq_self_eq_true]
  · have hSid' : ep.sid ≠ s := by
      exact (beq_eq_false_iff_ne (a:=ep.sid) (b:=s)).1 (by simpa using hSid)
    simp [swapEndpointRole, hSid, hSid']

theorem swapEdgeRole_involutive (s : SessionId) (A B : Role) (e : Edge) :
    swapEdgeRole s A B (swapEdgeRole s A B e) = e := by
  by_cases hSid : e.sid == s
  · have hSid' : e.sid = s := beq_iff_eq.1 hSid
    subst hSid'
    cases e with
    | mk sid sender receiver =>
        simp [swapEdgeRole, swapRole_involutive, beq_self_eq_true]
  · have hSid' : e.sid ≠ s := by
      exact (beq_eq_false_iff_ne (a:=e.sid) (b:=s)).1 (by simpa using hSid)
    simp [swapEdgeRole, hSid, hSid']

theorem swapEndpointRole_inj (s : SessionId) (A B : Role) (e1 e2 : Endpoint) :
    swapEndpointRole s A B e1 = swapEndpointRole s A B e2 → e1 = e2 := by
  intro h
  have h' := congrArg (swapEndpointRole s A B) h
  simpa [swapEndpointRole_involutive] using h'

theorem swapEdgeRole_inj (s : SessionId) (A B : Role) (e1 e2 : Edge) :
    swapEdgeRole s A B e1 = swapEdgeRole s A B e2 → e1 = e2 := by
  intro h
  have h' := congrArg (swapEdgeRole s A B) h
  simpa [swapEdgeRole_involutive] using h'

/-- Swap all endpoints and their local types for session s. -/
def swapGEnvRole (s : SessionId) (A B : Role) (G : GEnv) : GEnv :=
  G.map fun (ep, L) =>
    if ep.sid == s then
      (swapEndpointRole s A B ep, swapLocalTypeRole s A B L)
    else
      (ep, L)

/-- Swap all edges and their traces for session s. -/
def swapDEnvRole (s : SessionId) (A B : Role) (D : DEnv) : DEnv :=
  D.list.foldl
    (fun acc p =>
      if p.1.sid == s then
        updateD acc (swapEdgeRole s A B p.1) (p.2.map (swapValTypeRole s A B))
      else
        updateD acc p.1 p.2)
    (∅ : DEnv)

/-! ## Lookup Lemmas -/

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

private lemma lookupD_foldl_update_neq_swap (s : SessionId) (A B : Role) :
    ∀ (l : List (Edge × Trace)) (acc : DEnv) (edge : Edge),
      (∀ p ∈ l,
        (if p.1.sid == s then swapEdgeRole s A B p.1 else p.1) ≠ edge) →
      lookupD
          (l.foldl
            (fun acc p =>
              if p.1.sid == s then
                updateD acc (swapEdgeRole s A B p.1) (p.2.map (swapValTypeRole s A B))
              else
                updateD acc p.1 p.2)
            acc)
          edge = lookupD acc edge := by
  intro l acc edge hne
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
      have hne' : ∀ p ∈ tl,
          (if p.1.sid == s then swapEdgeRole s A B p.1 else p.1) ≠ edge := by
        intro p hp
        exact hne p (List.mem_cons.mpr (Or.inr hp))
      have hhd :
          (if hd.1.sid == s then swapEdgeRole s A B hd.1 else hd.1) ≠ edge :=
        hne hd (List.mem_cons.mpr (Or.inl rfl))
      by_cases hSid : hd.1.sid == s
      · simp [List.foldl, hSid, lookupD_update_neq _ _ _ hhd, ih hne']
      · simp [List.foldl, hSid, lookupD_update_neq _ _ _ hhd, ih hne']

/-- Looking up a swapped endpoint in a swapped GEnv. -/
theorem lookupG_swap (s : SessionId) (A B : Role) (G : GEnv) (e : Endpoint) :
    lookupG (swapGEnvRole s A B G) (swapEndpointRole s A B e) =
      if e.sid == s then (lookupG G e).map (swapLocalTypeRole s A B) else lookupG G e := by
  induction G with
  | nil =>
      by_cases hSid : e.sid == s
      · simp [swapGEnvRole, lookupG, List.lookup, hSid]
      · simp [swapGEnvRole, lookupG, List.lookup, hSid, swapEndpointRole]
  | cons hd tl ih =>
      by_cases heq : e = hd.1
      · subst heq
        by_cases hSid : hd.1.sid == s
        · simp [swapGEnvRole, lookupG, List.lookup, hSid]
        · simp [swapGEnvRole, lookupG, List.lookup, hSid]
      · have hne :
          swapEndpointRole s A B e ≠
            (if hd.1.sid == s then swapEndpointRole s A B hd.1 else hd.1) := by
          by_cases hHdSid : hd.1.sid == s
          · intro hEq
            apply heq
            apply swapEndpointRole_inj s A B
            simpa [hHdSid] using hEq
          · by_cases hSid : e.sid == s
            · intro hEq
              have hSidEq : (swapEndpointRole s A B e).sid = hd.1.sid :=
                congrArg Endpoint.sid hEq
              have hSidL : (swapEndpointRole s A B e).sid = e.sid := by
                simpa using (swapEndpointRole_sid (s:=s) (A:=A) (B:=B) (ep:=e))
              have hSidEq' : e.sid = hd.1.sid := by simpa [hSidL] using hSidEq
              have hSidNe : hd.1.sid ≠ s :=
                (beq_eq_false_iff_ne (a:=hd.1.sid) (b:=s)).1 (by simpa using hHdSid)
              have hSidEq'' : s = hd.1.sid := by
                have hSidProp : e.sid = s := beq_iff_eq.1 hSid
                simpa [hSidProp] using hSidEq'
              exact (hSidNe hSidEq'').elim
            · intro hEq
              have hSidNe : e.sid ≠ s :=
                (beq_eq_false_iff_ne (a:=e.sid) (b:=s)).1 (by simpa using hSid)
              have hSwap : swapEndpointRole s A B e = e := by
                simp [swapEndpointRole, hSid]
              exact (heq (by simpa [hSwap, hHdSid] using hEq)).elim
        have hbeq :
            (swapEndpointRole s A B e ==
              (if hd.1.sid == s then swapEndpointRole s A B hd.1 else hd.1)) = false :=
          beq_eq_false_iff_ne.mpr hne
        have hbeq' : (e == hd.1) = false := beq_eq_false_iff_ne.mpr heq
        simp [swapGEnvRole, lookupG, List.lookup, hbeq, hbeq', ih]

/-- Looking up a swapped edge in a swapped DEnv. -/
theorem lookupD_swap (s : SessionId) (A B : Role) (D : DEnv) (e : Edge) :
    lookupD (swapDEnvRole s A B D) (swapEdgeRole s A B e) =
      if e.sid == s then (lookupD D e).map (swapValTypeRole s A B) else lookupD D e := by
  have hfold :
      lookupD (swapDEnvRole s A B D) (swapEdgeRole s A B e) =
        if e.sid == s then
          match D.list.lookup e with
          | some ts => ts.map (swapValTypeRole s A B)
          | none => []
        else
          match D.list.lookup e with
          | some ts => ts
          | none => [] := by
    cases D with
    | mk l m map_eq sorted =>
        have hfold' :
            ∀ (l : List (Edge × Trace)) (sorted : l.Pairwise edgeCmpLT) (acc : DEnv) (e : Edge),
              lookupD
                  (l.foldl
                    (fun acc p =>
                      if p.1.sid == s then
                        updateD acc (swapEdgeRole s A B p.1)
                          (p.2.map (swapValTypeRole s A B))
                      else
                        updateD acc p.1 p.2)
                    acc)
                  (swapEdgeRole s A B e) =
                if e.sid == s then
                  match l.lookup e with
                  | some ts => ts.map (swapValTypeRole s A B)
                  | none => lookupD acc (swapEdgeRole s A B e)
                else
                  match l.lookup e with
                  | some ts => ts
                  | none => lookupD acc e := by
          intro l sorted acc e
          revert sorted
          induction l generalizing acc with
          | nil =>
              intro sorted
              by_cases hSid : e.sid == s
              · simp [List.lookup, hSid]
              · simp [List.lookup, hSid, swapEdgeRole]
          | cons hd tl ih =>
              intro sorted
              have hpair := (List.pairwise_cons.1 sorted)
              have hhd : ∀ p ∈ tl, edgeCmpLT hd p := hpair.1
              have htl : tl.Pairwise edgeCmpLT := hpair.2
              by_cases hSid : e.sid == s
              · by_cases hEq : e = hd.1
                · subst hEq
                  have hSidHd : hd.1.sid == s := by simpa using hSid
                  have hne :
                      ∀ p ∈ tl,
                        (if p.1.sid == s then swapEdgeRole s A B p.1 else p.1) ≠
                          swapEdgeRole s A B hd.1 := by
                    intro p hp
                    by_cases hPsid : p.1.sid == s
                    · intro hEq
                      have hEq' : p.1 = hd.1 := by
                        apply swapEdgeRole_inj (s:=s) (A:=A) (B:=B)
                        simpa [hPsid, hSidHd] using hEq
                      have hlt : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt (hhd p hp)
                      have hEqCmp : compare hd.1 p.1 = .eq :=
                        (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq'.symm
                      have : Ordering.lt = Ordering.eq := by
                        exact hlt.symm.trans hEqCmp
                      cases this
                    · intro hEq
                      have hSidNe : p.1.sid ≠ s :=
                        (beq_eq_false_iff_ne (a:=p.1.sid) (b:=s)).1 (by simpa using hPsid)
                      have hSidTarget : (swapEdgeRole s A B hd.1).sid = s := by
                        have hSidProp : hd.1.sid = s := beq_iff_eq.1 hSidHd
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=hd.1))
                      have hSidEq : p.1.sid = (swapEdgeRole s A B hd.1).sid :=
                        congrArg Edge.sid (by simpa [hPsid] using hEq)
                      exact (hSidNe (by simpa [hSidTarget] using hSidEq)).elim
                  have htail :
                      lookupD
                          (tl.foldl
                            (fun acc p =>
                              if p.1.sid == s then
                                updateD acc (swapEdgeRole s A B p.1)
                                  (p.2.map (swapValTypeRole s A B))
                              else
                                updateD acc p.1 p.2)
                            (updateD acc (swapEdgeRole s A B hd.1)
                              (hd.2.map (swapValTypeRole s A B))))
                          (swapEdgeRole s A B hd.1) =
                        lookupD
                          (updateD acc (swapEdgeRole s A B hd.1)
                            (hd.2.map (swapValTypeRole s A B)))
                          (swapEdgeRole s A B hd.1) := by
                    apply lookupD_foldl_update_neq_swap (s:=s) (A:=A) (B:=B)
                    intro p hp
                    exact hne p hp
                  simp [List.lookup, List.foldl, hSid, hSidHd, htail, lookupD_update_eq]
                · -- e ≠ hd.1
                  have hne :
                      (if hd.1.sid == s then swapEdgeRole s A B hd.1 else hd.1) ≠
                        swapEdgeRole s A B e := by
                    by_cases hHdSid : hd.1.sid == s
                    · intro hEq
                      apply heq
                      apply swapEdgeRole_inj s A B
                      simpa [hHdSid] using hEq
                    · intro hEq
                      have hSidNe : hd.1.sid ≠ s :=
                        (beq_eq_false_iff_ne (a:=hd.1.sid) (b:=s)).1 (by simpa using hHdSid)
                      have hSidTarget : (swapEdgeRole s A B e).sid = s := by
                        have hSidProp : e.sid = s := beq_iff_eq.1 hSid
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=e))
                      have hSidEq : hd.1.sid = (swapEdgeRole s A B e).sid :=
                        congrArg Edge.sid (by simpa [hHdSid] using hEq)
                      exact (hSidNe (by simpa [hSidTarget] using hSidEq)).elim
                  by_cases hHdSid : hd.1.sid == s
                  · simp [List.foldl, hSid, hHdSid, lookupD_update_neq _ _ _ hne, ih htl]
                  · simp [List.foldl, hSid, hHdSid, lookupD_update_neq _ _ _ hne, ih htl]
              · -- hSid false
                by_cases hEq : e = hd.1
                · subst hEq
                  have hSidHd : hd.1.sid ≠ s :=
                    (beq_eq_false_iff_ne (a:=hd.1.sid) (b:=s)).1 (by simpa using hSid)
                  have hne :
                      ∀ p ∈ tl,
                        (if p.1.sid == s then swapEdgeRole s A B p.1 else p.1) ≠ hd.1 := by
                    intro p hp
                    by_cases hPsid : p.1.sid == s
                    · intro hEq
                      have hSidTarget : (swapEdgeRole s A B p.1).sid = s := by
                        have hSidProp : p.1.sid = s := beq_iff_eq.1 hPsid
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=p.1))
                      have hSidEq : (swapEdgeRole s A B p.1).sid = hd.1.sid :=
                        congrArg Edge.sid (by simpa [hPsid] using hEq)
                      exact (hSidHd (by simpa [hSidTarget] using hSidEq)).elim
                    · intro hEq
                      -- p.1.sid != s, key = p.1; use edgeCmpLT to show p.1 ≠ hd.1
                      have hEq' : p.1 = hd.1 := by simpa [hPsid] using hEq
                      have hlt : compare hd.1 p.1 = .lt := edgeCmpLT_eq_lt (hhd p hp)
                      have hEqCmp : compare hd.1 p.1 = .eq :=
                        (Edge.compare_eq_iff_eq hd.1 p.1).2 hEq'.symm
                      have : Ordering.lt = Ordering.eq := by
                        exact hlt.symm.trans hEqCmp
                      cases this
                  have htail :
                      lookupD
                          (tl.foldl
                            (fun acc p =>
                              if p.1.sid == s then
                                updateD acc (swapEdgeRole s A B p.1)
                                  (p.2.map (swapValTypeRole s A B))
                              else
                                updateD acc p.1 p.2)
                            (updateD acc hd.1 hd.2))
                          hd.1 =
                        lookupD (updateD acc hd.1 hd.2) hd.1 := by
                    apply lookupD_foldl_update_neq_swap (s:=s) (A:=A) (B:=B)
                    intro p hp
                    exact hne p hp
                  simp [List.lookup, List.foldl, hSid, htail, lookupD_update_eq]
                · -- e ≠ hd.1
                  have hne :
                      (if hd.1.sid == s then swapEdgeRole s A B hd.1 else hd.1) ≠ e := by
                    by_cases hHdSid : hd.1.sid == s
                    · intro hEq
                      have hSidTarget : (swapEdgeRole s A B hd.1).sid = s := by
                        have hSidProp : hd.1.sid = s := beq_iff_eq.1 hHdSid
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=hd.1))
                      have hSidEq : (swapEdgeRole s A B hd.1).sid = e.sid :=
                        congrArg Edge.sid (by simpa [hHdSid] using hEq)
                      have hSidNe : e.sid ≠ s :=
                        (beq_eq_false_iff_ne (a:=e.sid) (b:=s)).1 (by simpa using hSid)
                      exact (hSidNe (by simpa [hSidTarget] using hSidEq)).elim
                    · intro hEq
                      exact heq (by simpa [hHdSid] using hEq)
                  by_cases hHdSid : hd.1.sid == s
                  · simp [List.foldl, hSid, hHdSid, lookupD_update_neq _ _ _ hne, ih htl]
                  · simp [List.foldl, hSid, hHdSid, lookupD_update_neq _ _ _ hne, ih htl]
        have hfold'' :
            lookupD
                (l.foldl
                  (fun acc p =>
                    if p.1.sid == s then
                      updateD acc (swapEdgeRole s A B p.1)
                        (p.2.map (swapValTypeRole s A B))
                    else
                      updateD acc p.1 p.2)
                  (∅ : DEnv))
                (swapEdgeRole s A B e) =
              if e.sid == s then
                match l.lookup e with
                | some ts => ts.map (swapValTypeRole s A B)
                | none => []
              else
                match l.lookup e with
                | some ts => ts
                | none => [] := by
          simpa using hfold' (l:=l) (sorted:=sorted) (acc:=(∅ : DEnv)) (e:=e)
        simpa [swapDEnvRole] using hfold''
  rw [lookupD_eq_list_lookup, hfold]
  by_cases hSid : e.sid == s
  · simp [hSid, lookupD_eq_list_lookup]
  · simp [hSid, lookupD_eq_list_lookup]

/-! ## Consume Preservation for Role Swap -/

/-- Consume a single step commutes with role swapping. -/
theorem consumeOne_swap (s : SessionId) (A B : Role) (from_ : Role)
    (T : ValType) (L L' : LocalType)
    (h : consumeOne from_ T L = some L') :
    consumeOne (swapRole A B from_) (swapValTypeRole s A B T) (swapLocalTypeRole s A B L) =
      some (swapLocalTypeRole s A B L') := by
  cases L with
  | recv r T' Lr =>
      by_cases hCond : from_ == r && T == T'
      · have hL : L' = Lr := by
          have : some Lr = some L' := by
            simpa [consumeOne, hCond] using h
          exact (Option.some.inj this).symm
        have hBoth := Bool.and_eq_true_iff.mp hCond
        have hRoleEq : from_ = r := eq_of_beq hBoth.1
        have hTypeEq : T = T' := eq_of_beq hBoth.2
        have hRoleEq' : swapRole A B from_ = swapRole A B r := by
          simpa [hRoleEq]
        have hTypeEq' : swapValTypeRole s A B T = swapValTypeRole s A B T' := by
          simpa [hTypeEq]
        have hBeqRole : (swapRole A B from_ == swapRole A B r) = true :=
          beq_iff_eq.2 hRoleEq'
        have hBeqType :
            (swapValTypeRole s A B T == swapValTypeRole s A B T') = true :=
          beq_iff_eq.2 hTypeEq'
        simp [consumeOne, swapLocalTypeRole, swapValTypeRole, hBeqRole, hBeqType, hL]
      · have : False := by
          simpa [consumeOne, hCond] using h
        exact (False.elim this)
  | send r T' Lr =>
      cases h
  | select r bs =>
      cases h
  | branch r bs =>
      cases h
  | end_ =>
      cases h
  | var n =>
      cases h
  | mu Lr =>
      cases h

/-- Consume commutes with role swapping. -/
theorem Consume_swap (s : SessionId) (A B : Role) (from_ : Role)
    (L : LocalType) (ts : List ValType) (L' : LocalType)
    (h : Consume from_ L ts = some L') :
    Consume (swapRole A B from_) (swapLocalTypeRole s A B L)
        (ts.map (swapValTypeRole s A B)) =
      some (swapLocalTypeRole s A B L') := by
  induction ts generalizing L L' with
  | nil =>
      simp [Consume] at h
      simp [Consume, h]
  | cons t ts ih =>
      simp [Consume] at h
      cases hOne : consumeOne from_ t L with
      | none =>
          have : False := by
            simpa [hOne] using h
          exact (False.elim this)
      | some L1 =>
          have hTail : Consume from_ L1 ts = some L' := by
            simpa [hOne] using h
          have hRen :=
            consumeOne_swap (s:=s) (A:=A) (B:=B) (from_:=from_) (T:=t) (L:=L) (L':=L1) hOne
          have hTailRen := ih (L:=L1) (L':=L') hTail
          simp [Consume, hRen, hTailRen]

/-! ## Coherence Preservation for Role Swap -/

/-- Coherence is preserved under swapping two roles within a session. -/
theorem CoherentRoleSwap (s : SessionId) (A B : Role) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (swapGEnvRole s A B G) (swapDEnvRole s A B D) := by
  intro e hActive Lrecv hGrecv
  by_cases hSid : e.sid == s
  · -- Session-local swap case.
    let e' : Edge := swapEdgeRole s A B e
    let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    let senderEp : Endpoint := { sid := e.sid, role := e.sender }
    let recvEp' : Endpoint := { sid := e'.sid, role := e'.receiver }
    let senderEp' : Endpoint := { sid := e'.sid, role := e'.sender }
    have hRecvEp : swapEndpointRole s A B recvEp' = recvEp := by
      simp [recvEp, recvEp', e', swapEdgeRole, swapEndpointRole, hSid, swapRole_involutive]
    have hSenderEp : swapEndpointRole s A B senderEp' = senderEp := by
      simp [senderEp, senderEp', e', swapEdgeRole, swapEndpointRole, hSid, swapRole_involutive]
    have hLookupRecvMap :
        lookupG (swapGEnvRole s A B G) recvEp =
          (lookupG G recvEp').map (swapLocalTypeRole s A B) := by
      have hSid' : recvEp'.sid == s := by
        simp [recvEp', e', swapEdgeRole, hSid]
      simpa [hRecvEp, hSid'] using
        (lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=recvEp'))
    have hLookupRecvEq :
        (lookupG G recvEp').map (swapLocalTypeRole s A B) = some Lrecv := by
      simpa [hLookupRecvMap] using hGrecv
    cases hLookupR : lookupG G recvEp' with
    | none =>
        have : False := by
          simpa [hLookupR] using hLookupRecvEq
        exact this.elim
    | some Lrecv0 =>
        have hLrecv : Lrecv = swapLocalTypeRole s A B Lrecv0 := by
          simpa [hLookupR] using hLookupRecvEq
        have hGrecv0 : lookupG G recvEp' = some Lrecv0 := hLookupR
        have hLookupSenderMap :
            lookupG (swapGEnvRole s A B G) senderEp =
              (lookupG G senderEp').map (swapLocalTypeRole s A B) := by
          have hSid' : senderEp'.sid == s := by
            simp [senderEp', e', swapEdgeRole, hSid]
          simpa [hSenderEp, hSid'] using
            (lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=senderEp'))
        rcases (Option.isSome_iff_exists).1 hActive.1 with ⟨LsenderSwapped, hGsenderSwapped⟩
        have hLookupSenderEq :
            (lookupG G senderEp').map (swapLocalTypeRole s A B) =
              some LsenderSwapped := by
          simpa [hLookupSenderMap] using hGsenderSwapped
        have hGsender0 : ∃ Lsender0, lookupG G senderEp' = some Lsender0 := by
          cases hLookupS : lookupG G senderEp' with
          | none =>
              have : False := by
                simpa [hLookupS] using hLookupSenderEq
              exact this.elim
          | some Lsender0 =>
              exact ⟨Lsender0, hLookupS⟩
        rcases hGsender0 with ⟨Lsender0, hGsender0⟩
        have hActive' : ActiveEdge G e' :=
          ActiveEdge_of_endpoints (e:=e') hGsender0 hGrecv0
        have hCoh' := hCoh e' hActive' Lrecv0 hGrecv0
        rcases hCoh' with ⟨Lsender1, hGsender1, hConsume⟩
        have hLookupSender' :
            lookupG (swapGEnvRole s A B G) senderEp =
              some (swapLocalTypeRole s A B Lsender1) := by
          simpa [hGsender1] using hLookupSenderMap
        rcases (Option.isSome_iff_exists).1 hConsume with ⟨Lafter, hConsumeEq⟩
        have hConsumeSwap :
            Consume (swapRole A B e'.sender) (swapLocalTypeRole s A B Lrecv0)
                ((lookupD D e').map (swapValTypeRole s A B)) =
              some (swapLocalTypeRole s A B Lafter) := by
          exact Consume_swap (s:=s) (A:=A) (B:=B) (from_:=e'.sender)
            (L:=Lrecv0) (ts:=lookupD D e') (L':=Lafter) hConsumeEq
        have hTrace :
            lookupD (swapDEnvRole s A B D) e =
              (lookupD D e').map (swapValTypeRole s A B) := by
          have hLookup :=
            lookupD_swap (s:=s) (A:=A) (B:=B) (D:=D) (e:=e')
          have hSwap : swapEdgeRole s A B e' = e := by
            simp [e', swapEdgeRole_involutive]
          have hSid' : e'.sid == s := by
            simp [e', swapEdgeRole, hSid]
          simpa [hSwap, hSid'] using hLookup
        have hSenderEq : e.sender = swapRole A B e'.sender := by
          simp [e', swapEdgeRole, hSid, swapRole_involutive]
        have hConsumeSwapped :
            Consume e.sender Lrecv (lookupD (swapDEnvRole s A B D) e) =
              some (swapLocalTypeRole s A B Lafter) := by
          simpa [hSenderEq, hLrecv, hTrace] using hConsumeSwap
        refine ⟨swapLocalTypeRole s A B Lsender1, hLookupSender', ?_⟩
        simpa [hConsumeSwapped]
  · -- Other-session edges are unchanged.
    have hSidNe : e.sid ≠ s :=
      (beq_eq_false_iff_ne (a:=e.sid) (b:=s)).1 (by simpa using hSid)
    let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    let senderEp : Endpoint := { sid := e.sid, role := e.sender }
    have hGrecv' : lookupG G recvEp = some Lrecv := by
      have hLookup :=
        lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=recvEp)
      have hSwap : swapEndpointRole s A B recvEp = recvEp := by
        simp [swapEndpointRole, hSid]
      have hMap : lookupG (swapGEnvRole s A B G) recvEp =
          lookupG G recvEp := by
        simpa [hSid, hSwap] using hLookup
      simpa [hMap] using hGrecv
    have hActive' : ActiveEdge G e := by
      have hLookupSender :=
        lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=senderEp)
      have hSwap : swapEndpointRole s A B senderEp = senderEp := by
        simp [swapEndpointRole, hSid]
      have hMap :
          lookupG (swapGEnvRole s A B G) senderEp =
            lookupG G senderEp := by
        simpa [hSid, hSwap] using hLookupSender
      have hSenderSome : (lookupG G senderEp).isSome := by
        simpa [hMap, senderEp] using hActive.1
      have hRecvSome : (lookupG G recvEp).isSome := by
        simpa [hGrecv'] using (Option.isSome_iff_exists.mpr ⟨Lrecv, hGrecv'⟩)
      exact ⟨hSenderSome, hRecvSome⟩
    have hCoh' := hCoh e hActive' Lrecv hGrecv'
    rcases hCoh' with ⟨Lsender, hGsender, hConsume⟩
    have hLookupSender' :
        lookupG (swapGEnvRole s A B G) senderEp = some Lsender := by
      have hLookup :=
        lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=senderEp)
      have hSwap : swapEndpointRole s A B senderEp = senderEp := by
        simp [swapEndpointRole, hSid]
      simpa [hSid, hSwap, hGsender] using hLookup
    have hTrace :
        lookupD (swapDEnvRole s A B D) e = lookupD D e := by
      have hLookup :=
        lookupD_swap (s:=s) (A:=A) (B:=B) (D:=D) (e:=e)
      have hSwap : swapEdgeRole s A B e = e := by
        simp [swapEdgeRole, hSid]
      simpa [hSid, hSwap] using hLookup
    refine ⟨Lsender, hLookupSender', ?_⟩
    simpa [hTrace] using hConsume

/-! ## Role Swap Sequences (Exchangeability Primitive) -/

/-- Apply a list of role swaps to a role. -/
def swapRoleList (pairs : List (Role × Role)) (r : Role) : Role :=
  pairs.foldl (fun acc p => swapRole p.1 p.2 acc) r

/-- Apply a list of role swaps to a GEnv, session-local. -/
def swapGEnvRoleList (s : SessionId) (pairs : List (Role × Role)) (G : GEnv) : GEnv :=
  pairs.foldl (fun acc p => swapGEnvRole s p.1 p.2 acc) G

/-- Apply a list of role swaps to a DEnv, session-local. -/
def swapDEnvRoleList (s : SessionId) (pairs : List (Role × Role)) (D : DEnv) : DEnv :=
  pairs.foldl (fun acc p => swapDEnvRole s p.1 p.2 acc) D

/-- Coherence is preserved under any finite sequence of role swaps in a session. -/
theorem CoherentRoleSwap_list (s : SessionId) (pairs : List (Role × Role)) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (swapGEnvRoleList s pairs G) (swapDEnvRoleList s pairs D) := by
  induction pairs generalizing G D with
  | nil =>
      simpa [swapGEnvRoleList, swapDEnvRoleList] using hCoh
  | cons hd tl ih =>
      have hCoh' : Coherent (swapGEnvRole s hd.1 hd.2 G) (swapDEnvRole s hd.1 hd.2 D) :=
        CoherentRoleSwap (s:=s) (A:=hd.1) (B:=hd.2) (G:=G) (D:=D) hCoh
      simpa [swapGEnvRoleList, swapDEnvRoleList, List.foldl] using
        ih (G:=swapGEnvRole s hd.1 hd.2 G) (D:=swapDEnvRole s hd.1 hd.2 D) hCoh'

/-- Exchangeability corollary: any finite swap sequence preserves coherence. -/
theorem Coherent_exchangeable (s : SessionId) (pairs : List (Role × Role)) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (swapGEnvRoleList s pairs G) (swapDEnvRoleList s pairs D) :=
  CoherentRoleSwap_list (s:=s) (pairs:=pairs) (G:=G) (D:=D) hCoh
