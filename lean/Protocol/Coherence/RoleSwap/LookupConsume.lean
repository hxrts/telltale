
import Protocol.Coherence.RoleSwap.Core

/-! # Protocol.Coherence.RoleSwap.LookupConsume

Lookup and consume-preservation lemmas for role swaps.
-/

/-
The Problem. Coherence preservation under role swaps needs lookup transport and
consume-commutation lemmas.

Solution Structure. Proves lookup transport and consume-preservation results.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

-- lookupD Swap Transport

theorem lookupD_swap (s : SessionId) (A B : Role) (D : DEnv) (e : Edge) :
    lookupD (swapDEnvRole s A B D) (swapEdgeRole s A B e) =
      if e.sid = s then (lookupD D e).map (swapValTypeRole s A B) else lookupD D e := by
  -- lookupD_swap: Reduce Goal to Fold Computation
  have hfold :
      lookupD (swapDEnvRole s A B D) (swapEdgeRole s A B e) =
        if e.sid = s then
          match D.list.lookup e with
          | some ts => ts.map (swapValTypeRole s A B)
          | none => []
        else
          match D.list.lookup e with
          | some ts => ts
          | none => [] := by
    -- lookupD_swap: Expand DEnv Representation
    cases D with
    | mk l m map_eq sorted =>
        -- lookupD_swap: Fold Invariant over Sorted Edge List
        have hfold' :
            ∀ (l : List (Edge × Trace)) (sorted : l.Pairwise edgeCmpLT) (acc : DEnv) (e : Edge),
              lookupD
                  (l.foldl
                    (fun acc p =>
                      if p.1.sid = s then
                        updateD acc (swapEdgeRole s A B p.1)
                          (p.2.map (swapValTypeRole s A B))
                      else
                        updateD acc p.1 p.2)
                    acc)
                  (swapEdgeRole s A B e) =
                if e.sid = s then
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
              by_cases hSid : e.sid = s
              · simp [List.lookup, hSid]
              · simp [List.lookup, hSid, swapEdgeRole]
          -- lookupD_swap: Non-Empty List Case
          | cons hd tl ih =>
              intro sorted
/- ## Structured Block 2 -/
              have hpair := (List.pairwise_cons.1 sorted)
              have hhd : ∀ p ∈ tl, edgeCmpLT hd p := hpair.1
              have htl : tl.Pairwise edgeCmpLT := hpair.2
              -- lookupD_swap: Branch on Target Session Edge
              by_cases hSid : e.sid = s
              -- lookupD_swap: Target Session, Head Match Split
              · by_cases hEq : e = hd.1
                · subst hEq
                  have hSidHd : hd.1.sid = s := by simpa using hSid
                  have hne :
                      ∀ p ∈ tl,
                        (if p.1.sid = s then swapEdgeRole s A B p.1 else p.1) ≠
                          swapEdgeRole s A B hd.1 := by
                    intro p hp
                    by_cases hPsid : p.1.sid = s
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
                      have hSidNe : p.1.sid ≠ s := hPsid
                      have hSidTarget : (swapEdgeRole s A B hd.1).sid = s := by
                        have hSidProp : hd.1.sid = s := hSidHd
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=hd.1))
                      have hSidEq : p.1.sid = (swapEdgeRole s A B hd.1).sid :=
                        congrArg Edge.sid (by simpa [hPsid] using hEq)

                      exact (hSidNe (by simpa [hSidTarget] using hSidEq)).elim
                  have htail :
                      lookupD
                          (tl.foldl
                            (fun acc p =>
                              if p.1.sid = s then
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
/- ## Structured Block 3 -/
                    exact hne p hp
                  simp [List.lookup, List.foldl, hSid, htail, lookupD_update_eq]
                -- lookupD_swap: Target Session, Distinct-Head Case
                · -- e ≠ hd.1
                  have hne :
                      (if hd.1.sid = s then swapEdgeRole s A B hd.1 else hd.1) ≠
                        swapEdgeRole s A B e := by
                    by_cases hHdSid : hd.1.sid = s
                    · intro hEqSwap
                      have hEqSwap' : swapEdgeRole s A B hd.1 = swapEdgeRole s A B e := by
                        simpa [hHdSid] using hEqSwap
                      have hEq' : hd.1 = e :=
                        swapEdgeRole_inj (s:=s) (A:=A) (B:=B) (e1:=hd.1) (e2:=e) hEqSwap'
                      exact (hEq hEq'.symm).elim
                    · intro hEq
                      have hSidNe : hd.1.sid ≠ s := hHdSid
                      have hSidTarget : (swapEdgeRole s A B e).sid = s := by
                        have hSidProp : e.sid = s := hSid
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=e))
                      have hSidEq : hd.1.sid = (swapEdgeRole s A B e).sid :=
                        congrArg Edge.sid (by simpa [hHdSid] using hEq)
                      exact (hSidNe (by simpa [hSidTarget] using hSidEq)).elim
                  have hbeq : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
                  -- lookupD_swap: Target Session Distinct-Head Inner Sid Split
                  by_cases hHdSid : hd.1.sid = s
                  · have hne' : swapEdgeRole s A B hd.1 ≠ swapEdgeRole s A B e := by
                      simpa [hHdSid] using hne
                    have ih' :=
                      ih (acc:=updateD acc (swapEdgeRole s A B hd.1)
                        (hd.2.map (swapValTypeRole s A B))) htl
                    have ih'' :
                        lookupD
                            (List.foldl
                              (fun acc p =>
                                if p.1.sid = s then
                                  updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                                else
                                  updateD acc p.1 p.2)
                              (updateD acc (swapEdgeRole s A B hd.1)
                                (hd.2.map (swapValTypeRole s A B))) tl)
                            (swapEdgeRole s A B e) =
                          match List.lookup e tl with
                          | some ts => ts.map (swapValTypeRole s A B)
                          | none => lookupD acc (swapEdgeRole s A B e) := by
                      simpa [hSid, lookupD_update_neq, hne'] using ih'
                    dsimp [List.foldl]
                    simp [hSid, hHdSid, List.lookup, hbeq, ih'']
                  · have hne' : hd.1 ≠ swapEdgeRole s A B e := by
                      simpa [hHdSid] using hne
                    have ih' := ih (acc:=updateD acc hd.1 hd.2) htl
                    have ih'' :
/- ## Structured Block 4 -/
                        lookupD
                            (List.foldl
                              (fun acc p =>
                                if p.1.sid = s then
                                  updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                                else
                                  updateD acc p.1 p.2)
                              (updateD acc hd.1 hd.2) tl)
                            (swapEdgeRole s A B e) =
                          match List.lookup e tl with
                          | some ts => ts.map (swapValTypeRole s A B)
                          | none => lookupD acc (swapEdgeRole s A B e) := by
                      simpa [hSid, lookupD_update_neq, hne'] using ih'
                    dsimp [List.foldl]
                    simp [hSid, hHdSid, List.lookup, hbeq, ih'']
              -- lookupD_swap: Non-Target Session Edge Branch
              · -- hSid false
                -- lookupD_swap: Non-Target Session, Head Match Split
                by_cases hEq : e = hd.1
                · subst hEq
                  have hSidHd : hd.1.sid ≠ s := hSid
                  have hne :
                      ∀ p ∈ tl,
                        (if p.1.sid = s then swapEdgeRole s A B p.1 else p.1) ≠ hd.1 := by
                    intro p hp
                    by_cases hPsid : p.1.sid = s
                    · intro hEq
                      have hSidTarget : (swapEdgeRole s A B p.1).sid = s := by
                        have hSidProp : p.1.sid = s := hPsid
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=p.1))
                      have hSidEq : (swapEdgeRole s A B p.1).sid = hd.1.sid :=
                        congrArg Edge.sid (by simpa [hPsid] using hEq)
                      have hSidEq' : hd.1.sid = s := by
                        simpa [eq_comm, hSidTarget] using hSidEq
                      exact (hSidHd hSidEq').elim
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
                              if p.1.sid = s then
                                updateD acc (swapEdgeRole s A B p.1)
                                  (p.2.map (swapValTypeRole s A B))
                              else
/- ## Structured Block 5 -/
                                updateD acc p.1 p.2)
                            (updateD acc hd.1 hd.2))
                          hd.1 =
                        lookupD (updateD acc hd.1 hd.2) hd.1 := by
                    apply lookupD_foldl_update_neq_swap (s:=s) (A:=A) (B:=B)
                    intro p hp
                    exact hne p hp
                  have hSwap : swapEdgeRole s A B hd.1 = hd.1 := by
                    simp [swapEdgeRole, hSidHd]
                  dsimp [List.foldl]
                  simp [List.lookup, hSid, hSwap, htail, lookupD_update_eq]
                -- lookupD_swap: Non-Target Session, Distinct-Head Case
                · -- e ≠ hd.1
                  have hne :
                      (if hd.1.sid = s then swapEdgeRole s A B hd.1 else hd.1) ≠ e := by
                    by_cases hHdSid : hd.1.sid = s
                    · intro hEq
                      have hSidTarget : (swapEdgeRole s A B hd.1).sid = s := by
                        have hSidProp : hd.1.sid = s := hHdSid
                        simpa [hSidProp] using
                          (swapEdgeRole_sid (s:=s) (A:=A) (B:=B) (e:=hd.1))
                      have hSidEq : (swapEdgeRole s A B hd.1).sid = e.sid :=
                        congrArg Edge.sid (by simpa [hHdSid] using hEq)
                      have hSidNe : e.sid ≠ s := hSid
                      have hSidEq' : e.sid = s := by
                        simpa [eq_comm, hSidTarget] using hSidEq
                      exact (hSidNe hSidEq').elim
                    · intro hEq'
                      exact hEq (by simpa [hHdSid] using hEq'.symm)
                  have hbeq : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
                  -- lookupD_swap: Non-Target Session, Inner Session-Id Split
                  by_cases hHdSid : hd.1.sid = s
                  · have hne' : swapEdgeRole s A B hd.1 ≠ e := by
                      simpa [hHdSid] using hne
                    have hne'' :
                        { sid := s, sender := swapRole A B hd.1.sender, receiver := swapRole A B hd.1.receiver } ≠ e := by
                      simpa [swapEdgeRole, hHdSid] using hne'
                    have ih' :=
                      ih (acc:=updateD acc (swapEdgeRole s A B hd.1)
                        (hd.2.map (swapValTypeRole s A B))) htl
                    have ih'' :
                        lookupD
                            (List.foldl
                              (fun acc p =>
                                if p.1.sid = s then
                                  updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                                else
                                  updateD acc p.1 p.2)
                              (updateD acc (swapEdgeRole s A B hd.1)
                                (hd.2.map (swapValTypeRole s A B))) tl)
                            e =
                          match List.lookup e tl with
/- ## Structured Block 6 -/
                          | some ts => ts
                          | none => lookupD acc e := by
                      simpa [hSid, hHdSid, swapEdgeRole, lookupD_update_neq, hne''] using ih'
                    dsimp [List.foldl]
                    simpa [List.lookup, hbeq, swapEdgeRole, hSid, hHdSid] using ih''
                  · have hne' : hd.1 ≠ e := by
                      simpa [hHdSid] using hne
                    have ih' := ih (acc:=updateD acc hd.1 hd.2) htl
                    have ih'' :
                        lookupD
                            (List.foldl
                              (fun acc p =>
                                if p.1.sid = s then
                                  updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                                else
                                  updateD acc p.1 p.2)
                              (updateD acc hd.1 hd.2) tl)
                            e =
                          match List.lookup e tl with
                          | some ts => ts
                          | none => lookupD acc e := by
                      simpa [hSid, hHdSid, swapEdgeRole, lookupD_update_neq, hne'] using ih'
                    dsimp [List.foldl]
                    simpa [List.lookup, hbeq, swapEdgeRole, hSid, hHdSid] using ih''
        -- lookupD_swap: Instantiate Invariant at Empty Accumulator
        have hfold'' :
            lookupD
                (l.foldl
                  (fun acc p =>
                    if p.1.sid = s then
                      updateD acc (swapEdgeRole s A B p.1)
                        (p.2.map (swapValTypeRole s A B))
                    else
                      updateD acc p.1 p.2)
                  (∅ : DEnv))
                (swapEdgeRole s A B e) =
              if e.sid = s then
                match l.lookup e with
                | some ts => ts.map (swapValTypeRole s A B)
                | none => []
              else
                match l.lookup e with
                | some ts => ts
                | none => [] := by
          simpa using hfold' (l:=l) (sorted:=sorted) (acc:=(∅ : DEnv)) (e:=e)
        simpa [swapDEnvRole] using hfold''
  -- lookupD_swap: Rewrite Back to lookupD
  rw [hfold]
  by_cases hSid : e.sid = s
  · cases h : D.list.lookup e <;> simp [hSid, lookupD_eq_list_lookup, h]
  · cases h : D.list.lookup e <;> simp [hSid, lookupD_eq_list_lookup, h]

-- Consume Preservation for Role Swap

/-- Consume a single step commutes with role swapping. -/
theorem consumeOne_swap (s : SessionId) (A B : Role) (from_ : Role)
/- ## Structured Block 7 -/
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
          simp [hRoleEq]
        have hTypeEq' : swapValTypeRole s A B T = swapValTypeRole s A B T' := by
          simp [hTypeEq]
        have hBeqRole : (swapRole A B from_ == swapRole A B r) = true :=
          beq_iff_eq.2 hRoleEq'
        have hBeqType :
            (swapValTypeRole s A B T == swapValTypeRole s A B T') = true :=
          beq_iff_eq.2 hTypeEq'
        simp [consumeOne, swapLocalTypeRole, hBeqRole, hBeqType, hL]
      · have : False := by
          simp [consumeOne, hCond] at h
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

-- Consume_swap: Structural Recursion on Trace

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
/- ## Structured Block 8 -/
      simp [Consume] at h
      cases hOne : consumeOne from_ t L with
      | none =>
          have : False := by
            simp [hOne] at h
          exact (False.elim this)
      | some L1 =>
          have hTail : Consume from_ L1 ts = some L' := by
            simpa [hOne] using h
          have hRen :=
            consumeOne_swap (s:=s) (A:=A) (B:=B) (from_:=from_) (T:=t) (L:=L) (L':=L1) hOne
          have hTailRen := ih (L:=L1) (L':=L') hTail
          simp [Consume, hRen, hTailRen]


end
