import SessionCoTypes.Coinductive.Roundtrip.EnvDefs

set_option linter.dupNamespace false

/-! # SessionCoTypes.Coinductive.Roundtrip.RoundtripTheorem

Main coinductive round-trip theorem `toCoind_toInductive_eq2ce`.
-/

namespace SessionCoTypes.Coinductive
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-! ## Local instances -/

/-- Local decidable equality for Finset operations on LocalTypeC. -/
local instance : DecidableEq LocalTypeC := by
  -- Use classical choice to decide equality on LocalTypeC.
  classical
  infer_instance
/-! ## Round-Trip Theorems (Axioms - proofs in progress) -/

theorem toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t := by
  classical
  let all := Set.Finite.toFinset h
  let h_closed : IsClosedSet all := reachable_is_closed_set t h
  let R : Rel := fun ρ a b =>
    ∃ (visited : Finset LocalTypeC) (h_visited : visited ⊆ all) (h_current : b ∈ all),
      (a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current) ∨
       (b ∉ visited ∧
        a = toCoind (toInductiveBody t all visited b h_closed h_visited h_current))) ∧
      EnvOfSub all ρ
  have hpost : ∀ ρ a b, R ρ a b → EQ2CE_step R ρ a b := by
    intro ρ a b hR
    rcases hR with ⟨visited, h_visited, h_current, hcase, hsub⟩
    have hsub' : EnvOfSub all ρ := hsub
    have hmem_env : b ∈ envL ρ (nameOf b all) := EnvOfSub_mem hsub' h_current
    cases hcase with
    | inl hwrap =>
        by_cases hmem : b ∈ visited
        · -- back-edge: emit var
          have hvar_body :
              toInductiveAux t all visited b h_closed h_visited h_current =
                LocalTypeR.var (nameOf b all) := by
            unfold toInductiveAux
            simp [hmem, nameOf]
            rfl
          have hvar : a = mkVar (nameOf b all) := by
            simpa [hvar_body] using hwrap
          have ha : head a = .var (nameOf b all) := by
            simp [hvar]
          have hb : b ∈ envL ρ (nameOf b all) := hmem_env
          exact EQ2CE_step.var_left ha hb
        · -- fresh node: unfold body
          have hname : String := nameOf b all
          -- unfold the aux definition
          have haux : a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current) := hwrap
          -- expose dest to drive cases
          cases hdest : PFunctor.M.dest b with
          | mk hhead f =>
              cases hhead with
              | «end» =>
                  have hb : head b = .end := by
                    exact head_of_dest hdest
                  have haux_end :
                      toInductiveAux t all visited b h_closed h_visited h_current = LocalTypeR.end := by
                    have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.end, f⟩ := mk_of_dest hdest
                    subst hb_eq
                    unfold toInductiveAux
                    simp [hmem, head, PFunctor.M.dest_mk, LocalTypeR.freeVars]
                  have ha : head a = .end := by
                    simp [haux, haux_end]
                  exact EQ2CE_step.end ha hb
              | var x =>
                  have hb : head b = .var x := by
                    exact head_of_dest hdest
                  have haux_var :
                      toInductiveAux t all visited b h_closed h_visited h_current = LocalTypeR.var x := by
                    have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.var x, f⟩ := mk_of_dest hdest
                    subst hb_eq
                    unfold toInductiveAux
                    simp [hmem, head, PFunctor.M.dest_mk]
                  have ha : head a = .var x := by
                    simp [haux, haux_var]
                  exact EQ2CE_step.var ha hb
              | mu x =>
                  have hb : head b = .mu x := by
                    exact head_of_dest hdest
                  have haux_mu :
                      toInductiveAux t all visited b h_closed h_visited h_current =
                        LocalTypeR.mu x (toInductiveBody t all visited b h_closed h_visited h_current) := by
                    have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.mu x, f⟩ := mk_of_dest hdest
                    subst hb_eq
                    unfold toInductiveAux
                    simp [hmem, head, PFunctor.M.dest_mk]
                    unfold toInductiveBody
                    simp [PFunctor.M.dest_mk]
                  have ha : PFunctor.M.dest a = ⟨LocalTypeHead.mu x, fun _ =>
                      toCoind (toInductiveBody t all visited b h_closed h_visited h_current)⟩ := by
                      rw [haux]
                      simp [haux_mu, toCoind_mu, mkMu, PFunctor.M.dest_mk]
                  have hmem' : b ∈ envL ρ x := by
                    simpa [nameOf, head, hdest] using hmem_env
                  have hcore : R (envInsertL ρ x b)
                      (toCoind (toInductiveBody t all visited b h_closed h_visited h_current)) b := by
                    refine ⟨visited, h_visited, h_current, ?_, EnvOfSub_insertL x b hsub'⟩
                    exact Or.inr ⟨hmem, rfl⟩
                  exact EQ2CE_step.mu_left ha hmem' hcore
              | send p labels =>
                  -- body is a send; decide whether to wrap in mu
                  have hb : head b = .send p labels := by
                    exact head_of_dest hdest
                  let fR : Fin labels.length → (Label × LocalTypeR) := fun i =>
                    let child := f i
                    have hchild : childRel b child := ⟨.send p labels, f, i, hdest, rfl⟩
                    have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                    (labels[i],
                      toInductiveAux t all (Insert.insert b visited) child h_closed
                        (subset_insert_of_mem h_current h_visited) hchild_mem)
                  by_cases hfv : nameOf b all ∈
                      (toInductiveBody t all visited b h_closed h_visited h_current).freeVars
                  · -- mu wrapper present
                    have haux_mu :
                        toInductiveAux t all visited b h_closed h_visited h_current =
                          LocalTypeR.mu (nameOf b all)
                            (toInductiveBody t all visited b h_closed h_visited h_current) := by
                      have hfv' :
                          nameFor b all ∈
                            (match hdest : PFunctor.M.dest b with
                            | ⟨.end, _⟩   => LocalTypeR.end
                            | ⟨.var x, _⟩ => LocalTypeR.var x
                            | ⟨.mu x, k⟩  =>
                                toInductiveAux t all (Insert.insert b visited) (k ()) h_closed
                                  (subset_insert_of_mem h_current h_visited)
                                  (mem_of_closed_child h_closed h_current
                                    ⟨.mu x, k, (), hdest, rfl⟩)
                            | ⟨.send p labels, k⟩ =>
                                LocalTypeR.send p
                                  (List.ofFn fun i =>
                                    (labels[i],
                                      toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                        (subset_insert_of_mem h_current h_visited)
                                        (mem_of_closed_child h_closed h_current
                                          ⟨.send p labels, k, i, hdest, rfl⟩)))
                            | ⟨.recv p labels, k⟩ =>
                                LocalTypeR.recv p
                                  (List.ofFn fun i =>
                                    (labels[i],
                                      toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                        (subset_insert_of_mem h_current h_visited)
                                        (mem_of_closed_child h_closed h_current
                                          ⟨.recv p labels, k, i, hdest, rfl⟩)))).freeVars := by
                        simpa [nameOf, hb, toInductiveBody, hdest] using hfv
                      have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.send p labels, f⟩ := mk_of_dest hdest
                      subst hb_eq
                      have hfv'' :
                          nameFor (PFunctor.M.mk ⟨LocalTypeHead.send p labels, f⟩) all ∈
                            (LocalTypeR.send p (List.ofFn fR)).freeVars := by
                        simpa [PFunctor.M.dest_mk, fR, list_get_coe_fin_symm] using hfv'
                      have hcond := hfv''
                      dsimp [fR] at hcond
                      unfold toInductiveAux
                      simp [hmem, head, PFunctor.M.dest_mk, nameOf, hcond, toInductiveBody]
                    have ha : PFunctor.M.dest a = ⟨LocalTypeHead.mu (nameOf b all),
                        fun _ => toCoind (toInductiveBody t all visited b h_closed h_visited h_current)⟩ := by
                      simp [haux, haux_mu, toCoind_mu, mkMu, PFunctor.M.dest_mk]
                    have hmem' : b ∈ envL ρ (nameOf b all) := hmem_env
                    have hcore : R (envInsertL ρ (nameOf b all) b)
                        (toCoind (toInductiveBody t all visited b h_closed h_visited h_current)) b := by
                      refine ⟨visited, h_visited, h_current, ?_,
                        EnvOfSub_insertL (nameOf b all) b hsub'⟩
                      exact Or.inr ⟨hmem, rfl⟩
                    exact EQ2CE_step.mu_left ha hmem' hcore
                  · -- no mu wrapper
                    have haux_send :
                        toInductiveAux t all visited b h_closed h_visited h_current =
                          LocalTypeR.send p (List.ofFn fR) := by
                      have hfv' :
                          nameFor b all ∉
                            (match hdest : PFunctor.M.dest b with
                            | ⟨.end, _⟩   => LocalTypeR.end
                            | ⟨.var x, _⟩ => LocalTypeR.var x
                            | ⟨.mu x, k⟩  =>
                                toInductiveAux t all (Insert.insert b visited) (k ()) h_closed
                                  (subset_insert_of_mem h_current h_visited)
                                  (mem_of_closed_child h_closed h_current
                                    ⟨.mu x, k, (), hdest, rfl⟩)
                            | ⟨.send p labels, k⟩ =>
                                LocalTypeR.send p
                                  (List.ofFn fun i =>
                                    (labels[i],
                                      toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                        (subset_insert_of_mem h_current h_visited)
                                        (mem_of_closed_child h_closed h_current
                                          ⟨.send p labels, k, i, hdest, rfl⟩)))
                            | ⟨.recv p labels, k⟩ =>
                                LocalTypeR.recv p
                                  (List.ofFn fun i =>
                                    (labels[i],
                                      toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                        (subset_insert_of_mem h_current h_visited)
                                        (mem_of_closed_child h_closed h_current
                                          ⟨.recv p labels, k, i, hdest, rfl⟩)))).freeVars := by
                        simpa [nameOf, hb, toInductiveBody, hdest] using hfv
                      have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.send p labels, f⟩ := mk_of_dest hdest
                      subst hb_eq
                      have hfv'' :
                          nameFor (PFunctor.M.mk ⟨LocalTypeHead.send p labels, f⟩) all ∉
                            (LocalTypeR.send p (List.ofFn fR)).freeVars := by
                        simpa [PFunctor.M.dest_mk, fR, list_get_coe_fin_symm] using hfv'
                      have hcond := hfv''
                      dsimp [fR] at hcond
                      unfold toInductiveAux
                      simp [hmem]
                      simp [head, PFunctor.M.dest_mk]
                      rw [if_neg hcond]
                      simp [fR]
                    have haux_send_coind : a = toCoind (.send p (List.ofFn fR)) := by
                      simpa [haux_send] using haux
                    have hlabels : List.ofFn (fun i => (fR i).1) = labels := by
                      simp [fR]
                    have ha' : head a = .send p (List.ofFn fun i => (fR i).1) := by
                      simpa [haux_send_coind] using (head_toCoind_send_ofFn (p := p) fR)
                    have ha : head a = .send p labels := by
                      simpa [hlabels] using ha'
                    have hbranches_a :
                        branchesOf a =
                          List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)) := by
                      simpa [haux_send_coind] using (branchesOf_toCoind_send_ofFn (p := p) fR)
                    have hbr' :
                        BranchesRelCE R ρ
                          (List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)))
                          (List.ofFn (fun i => (labels[i], f i))) := by
                      refine BranchesRelCE_ofFn ?_
                      intro i
                      constructor
                      · simp [fR]
                      · let child := f i
                        have hchild : childRel b child := ⟨.send p labels, f, i, hdest, rfl⟩
                        have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                        refine ⟨Insert.insert b visited,
                          subset_insert_of_mem h_current h_visited, hchild_mem, ?_, hsub'⟩
                        exact Or.inl rfl
                    have hbr : BranchesRelCE R ρ (branchesOf a) (branchesOf b) := by
                      rw [hbranches_a]
                      simpa [branchesOf, hdest] using hbr'
                    exact EQ2CE_step.send ha hb hbr
              | recv p labels =>
                  have hb : head b = .recv p labels := by
                    exact head_of_dest hdest
                  let fR : Fin labels.length → (Label × LocalTypeR) := fun i =>
                    let child := f i
                    have hchild : childRel b child := ⟨.recv p labels, f, i, hdest, rfl⟩
                    have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                    (labels[i],
                      toInductiveAux t all (Insert.insert b visited) child h_closed
                        (subset_insert_of_mem h_current h_visited) hchild_mem)
                  by_cases hfv : nameOf b all ∈
                      (toInductiveBody t all visited b h_closed h_visited h_current).freeVars
                  · have ha : PFunctor.M.dest a = ⟨LocalTypeHead.mu (nameOf b all),
                        fun _ => toCoind (toInductiveBody t all visited b h_closed h_visited h_current)⟩ := by
                      have haux_mu :
                          toInductiveAux t all visited b h_closed h_visited h_current =
                            LocalTypeR.mu (nameOf b all)
                              (toInductiveBody t all visited b h_closed h_visited h_current) := by
                        have hfv' :
                            nameFor b all ∈
                              (match hdest : PFunctor.M.dest b with
                              | ⟨.end, _⟩   => LocalTypeR.end
                              | ⟨.var x, _⟩ => LocalTypeR.var x
                              | ⟨.mu x, k⟩  =>
                                  toInductiveAux t all (Insert.insert b visited) (k ()) h_closed
                                    (subset_insert_of_mem h_current h_visited)
                                    (mem_of_closed_child h_closed h_current
                                      ⟨.mu x, k, (), hdest, rfl⟩)
                              | ⟨.send p labels, k⟩ =>
                                  LocalTypeR.send p
                                    (List.ofFn fun i =>
                                      (labels[i],
                                        toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                          (subset_insert_of_mem h_current h_visited)
                                          (mem_of_closed_child h_closed h_current
                                            ⟨.send p labels, k, i, hdest, rfl⟩)))
                              | ⟨.recv p labels, k⟩ =>
                                  LocalTypeR.recv p
                                    (List.ofFn fun i =>
                                      (labels[i],
                                        toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                          (subset_insert_of_mem h_current h_visited)
                                          (mem_of_closed_child h_closed h_current
                                            ⟨.recv p labels, k, i, hdest, rfl⟩)))).freeVars := by
                          simpa [nameOf, hb, toInductiveBody, hdest] using hfv
                        have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.recv p labels, f⟩ := mk_of_dest hdest
                        subst hb_eq
                        have hfv'' :
                            nameFor (PFunctor.M.mk ⟨LocalTypeHead.recv p labels, f⟩) all ∈
                              (LocalTypeR.recv p (List.ofFn fR)).freeVars := by
                          simpa [PFunctor.M.dest_mk, fR, list_get_coe_fin_symm] using hfv'
                        have hcond := hfv''
                        dsimp [fR] at hcond
                        have hcond' :
                            nameOf (PFunctor.M.mk ⟨LocalTypeHead.recv p labels, f⟩) all ∈
                              (LocalTypeR.recv p (List.ofFn fR)).freeVars := by
                          simpa [nameOf, head, PFunctor.M.dest_mk] using hcond
                        unfold toInductiveAux
                        simp [hmem]
                        simp [head, PFunctor.M.dest_mk]
                        simp [nameOf, head, PFunctor.M.dest_mk]
                        rw [if_pos hcond]
                        simp [toInductiveBody_eq_match, PFunctor.M.dest_mk]
                      simp [haux, haux_mu, toCoind_mu, mkMu, PFunctor.M.dest_mk]
                    have hmem' : b ∈ envL ρ (nameOf b all) := hmem_env
                    have hcore : R (envInsertL ρ (nameOf b all) b)
                        (toCoind (toInductiveBody t all visited b h_closed h_visited h_current)) b := by
                      refine ⟨visited, h_visited, h_current, ?_,
                        EnvOfSub_insertL (nameOf b all) b hsub'⟩
                      exact Or.inr ⟨hmem, rfl⟩
                    exact EQ2CE_step.mu_left ha hmem' hcore
                  · have haux_recv :
                        toInductiveAux t all visited b h_closed h_visited h_current =
                          LocalTypeR.recv p (List.ofFn fR) := by
                      have hfv' :
                          nameFor b all ∉
                            (match hdest : PFunctor.M.dest b with
                            | ⟨.end, _⟩   => LocalTypeR.end
                            | ⟨.var x, _⟩ => LocalTypeR.var x
                            | ⟨.mu x, k⟩  =>
                                toInductiveAux t all (Insert.insert b visited) (k ()) h_closed
                                  (subset_insert_of_mem h_current h_visited)
                                  (mem_of_closed_child h_closed h_current
                                    ⟨.mu x, k, (), hdest, rfl⟩)
                            | ⟨.send p labels, k⟩ =>
                                LocalTypeR.send p
                                  (List.ofFn fun i =>
                                    (labels[i],
                                      toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                        (subset_insert_of_mem h_current h_visited)
                                        (mem_of_closed_child h_closed h_current
                                          ⟨.send p labels, k, i, hdest, rfl⟩)))
                            | ⟨.recv p labels, k⟩ =>
                                LocalTypeR.recv p
                                  (List.ofFn fun i =>
                                    (labels[i],
                                      toInductiveAux t all (Insert.insert b visited) (k i) h_closed
                                        (subset_insert_of_mem h_current h_visited)
                                        (mem_of_closed_child h_closed h_current
                                          ⟨.recv p labels, k, i, hdest, rfl⟩)))).freeVars := by
                        simpa [nameOf, hb, toInductiveBody, hdest] using hfv
                      have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.recv p labels, f⟩ := mk_of_dest hdest
                      subst hb_eq
                      have hfv'' :
                          nameFor (PFunctor.M.mk ⟨LocalTypeHead.recv p labels, f⟩) all ∉
                            (LocalTypeR.recv p (List.ofFn fR)).freeVars := by
                        simpa [PFunctor.M.dest_mk, fR, list_get_coe_fin_symm] using hfv'
                      have hcond := hfv''
                      dsimp [fR] at hcond
                      unfold toInductiveAux
                      simp [hmem]
                      simp [head, PFunctor.M.dest_mk]
                      rw [if_neg hcond]
                      simp [fR]
                    have haux_recv_coind : a = toCoind (.recv p (List.ofFn fR)) := by
                      simpa [haux_recv] using haux
                    have ha : head a = .recv p labels := by
                      have hlabels : List.ofFn (fun i => (fR i).1) = labels := by
                        simp [fR]
                      have ha' : head a = .recv p (List.ofFn fun i => (fR i).1) := by
                        simpa [haux_recv_coind] using (head_toCoind_recv_ofFn (p := p) fR)
                      simpa [hlabels] using ha'
                    have hbranches_a :
                        branchesOf a =
                          List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)) := by
                      simpa [haux_recv_coind] using (branchesOf_toCoind_recv_ofFn (p := p) fR)
                    have hbr' :
                        BranchesRelCE R ρ
                          (List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)))
                          (List.ofFn (fun i => (labels[i], f i))) := by
                      refine BranchesRelCE_ofFn ?_
                      intro i
                      constructor
                      · simp [fR]
                      · let child := f i
                        have hchild : childRel b child := ⟨.recv p labels, f, i, hdest, rfl⟩
                        have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                        refine ⟨Insert.insert b visited,
                          subset_insert_of_mem h_current h_visited, hchild_mem, ?_, hsub'⟩
                        exact Or.inl rfl
                    have hbr : BranchesRelCE R ρ (branchesOf a) (branchesOf b) := by
                      rw [hbranches_a]
                      simpa [branchesOf, hdest] using hbr'
                    exact EQ2CE_step.recv ha hb hbr
    | inr hcore =>
        rcases hcore with ⟨hmem, hcore⟩
        cases hdest : PFunctor.M.dest b with
        | mk hhead f =>
            cases hhead with
            | «end» =>
                have hbody_end :
                    toInductiveBody t all visited b h_closed h_visited h_current = LocalTypeR.end := by
                  have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.end, f⟩ := mk_of_dest hdest
                  subst hb_eq
                  unfold toInductiveBody
                  simp [PFunctor.M.dest_mk]
                have ha : head a = .end := by
                  simp [hcore, hbody_end]
                have hb : head b = .end := by
                  exact head_of_dest hdest
                exact EQ2CE_step.end ha hb
            | var x =>
                have hbody_var :
                    toInductiveBody t all visited b h_closed h_visited h_current = LocalTypeR.var x := by
                  have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.var x, f⟩ := mk_of_dest hdest
                  subst hb_eq
                  unfold toInductiveBody
                  simp [PFunctor.M.dest_mk]
                have ha : head a = .var x := by
                  simp [hcore, hbody_var]
                have hb : head b = .var x := by
                  exact head_of_dest hdest
                exact EQ2CE_step.var ha hb
            | mu x =>
                have hb : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, f⟩ := by
                  simp [hdest]
                have hrel : R (envInsertR ρ x (mkVar x)) a (f ()) := by
                  have hchild : childRel b (f ()) := ⟨.mu x, f, (), hdest, rfl⟩
                  have hchild_mem : f () ∈ all := mem_of_closed_child h_closed h_current hchild
                  refine ⟨Insert.insert b visited, subset_insert_of_mem h_current h_visited,
                    hchild_mem, ?_, EnvOfSub_insertR x (mkVar x) hsub'⟩
                  have hcore_mu :
                      a =
                        toCoind
                          (toInductiveAux t all (Insert.insert b visited) (f ()) h_closed
                            (subset_insert_of_mem h_current h_visited) hchild_mem) := by
                    have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.mu x, f⟩ := mk_of_dest hdest
                    subst hb_eq
                    unfold toInductiveBody at hcore
                    simpa [PFunctor.M.dest_mk] using hcore
                  exact Or.inl hcore_mu
                exact EQ2CE_step.mu_right hb hrel
            | send p labels =>
                let fR : Fin labels.length → (Label × LocalTypeR) := fun i =>
                  let child := f i
                  have hchild : childRel b child := ⟨.send p labels, f, i, hdest, rfl⟩
                  have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                  (labels[i],
                    toInductiveAux t all (Insert.insert b visited) child h_closed
                      (subset_insert_of_mem h_current h_visited) hchild_mem)
                have hbody_send :
                    toInductiveBody t all visited b h_closed h_visited h_current =
                      LocalTypeR.send p (List.ofFn fR) := by
                  have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.send p labels, f⟩ := mk_of_dest hdest
                  subst hb_eq
                  unfold toInductiveBody
                  simp [PFunctor.M.dest_mk, fR]
                have hcore_send : a = toCoind (.send p (List.ofFn fR)) := by
                  simpa [hbody_send] using hcore
                have hlabels : List.ofFn (fun i => (fR i).1) = labels := by
                  simp [fR]
                have ha' : head a = .send p (List.ofFn fun i => (fR i).1) := by
                  simpa [hcore_send] using (head_toCoind_send_ofFn (p := p) fR)
                have ha : head a = .send p labels := by
                  simpa [hlabels] using ha'
                have hb : head b = .send p labels := by
                  exact head_of_dest hdest
                have hbranches_a :
                    branchesOf a =
                      List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)) := by
                  simpa [hcore_send] using (branchesOf_toCoind_send_ofFn (p := p) fR)
                have hbr' :
                    BranchesRelCE R ρ
                      (List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)))
                      (List.ofFn (fun i => (labels[i], f i))) := by
                  refine BranchesRelCE_ofFn ?_
                  intro i
                  constructor
                  · simp [fR]
                  · let child := f i
                    have hchild : childRel b child := ⟨.send p labels, f, i, hdest, rfl⟩
                    have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                    refine ⟨Insert.insert b visited,
                      subset_insert_of_mem h_current h_visited, hchild_mem, ?_, hsub'⟩
                    exact Or.inl rfl
                have hbr : BranchesRelCE R ρ (branchesOf a) (branchesOf b) := by
                  rw [hbranches_a]
                  simpa [branchesOf, hdest] using hbr'
                exact EQ2CE_step.send ha hb hbr
            | recv p labels =>
                let fR : Fin labels.length → (Label × LocalTypeR) := fun i =>
                  let child := f i
                  have hchild : childRel b child := ⟨.recv p labels, f, i, hdest, rfl⟩
                  have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                  (labels[i],
                    toInductiveAux t all (Insert.insert b visited) child h_closed
                      (subset_insert_of_mem h_current h_visited) hchild_mem)
                have hbody_recv :
                    toInductiveBody t all visited b h_closed h_visited h_current =
                      LocalTypeR.recv p (List.ofFn fR) := by
                  have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.recv p labels, f⟩ := mk_of_dest hdest
                  subst hb_eq
                  unfold toInductiveBody
                  simp [PFunctor.M.dest_mk, fR]
                have hcore_recv : a = toCoind (.recv p (List.ofFn fR)) := by
                  simpa [hbody_recv] using hcore
                have hlabels : List.ofFn (fun i => (fR i).1) = labels := by
                  simp [fR]
                have ha' : head a = .recv p (List.ofFn fun i => (fR i).1) := by
                  simpa [hcore_recv] using (head_toCoind_recv_ofFn (p := p) fR)
                have ha : head a = .recv p labels := by
                  simpa [hlabels] using ha'
                have hb : head b = .recv p labels := by
                  exact head_of_dest hdest
                have hbranches_a :
                    branchesOf a =
                      List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)) := by
                  simpa [hcore_recv] using (branchesOf_toCoind_recv_ofFn (p := p) fR)
                have hbr' :
                    BranchesRelCE R ρ
                      (List.ofFn (fun i => ((fR i).1, toCoind (fR i).2)))
                      (List.ofFn (fun i => (labels[i], f i))) := by
                  refine BranchesRelCE_ofFn ?_
                  intro i
                  constructor
                  · simp [fR]
                  · let child := f i
                    have hchild : childRel b child := ⟨.recv p labels, f, i, hdest, rfl⟩
                    have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                    refine ⟨Insert.insert b visited,
                      subset_insert_of_mem h_current h_visited, hchild_mem, ?_, hsub'⟩
                    exact Or.inl rfl
                have hbr : BranchesRelCE R ρ (branchesOf a) (branchesOf b) := by
                  rw [hbranches_a]
                  simpa [branchesOf, hdest] using hbr'
                exact EQ2CE_step.recv ha hb hbr
  -- apply coinduction with R
  have hR : R (envOf all all) (toCoind (toInductive t h)) t := by
    refine ⟨∅, ?_, ?_, ?_, envOf_sub all all⟩
    · exact Finset.empty_subset _
    · exact (Set.Finite.mem_toFinset h).2 Relation.ReflTransGen.refl
    · exact Or.inl rfl
  exact EQ2CE_coind hpost _ _ _ hR

end SessionCoTypes.Coinductive
