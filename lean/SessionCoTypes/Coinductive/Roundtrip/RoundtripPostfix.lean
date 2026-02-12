import SessionCoTypes.Coinductive.Roundtrip.RoundtripPostfixBodyCase

/-! # Roundtrip Postfix Lemma

Main roundtrip lemma showing coinductive-inductive-coinductive conversion
preserves EQ2 equivalence, using postfix reasoning for recursion. -/

/-
The Problem. The roundtrip `toCoind ∘ toInductive` must preserve EQ2.
The proof uses a parametrized bisimulation with a postfix relation that
tracks visited nodes to handle back-edges in recursive types.

Solution Structure. Define the roundtrip relation R with visited-set
tracking. Prove `roundtrip_hpost` showing R is preserved by EQ2CE steps.
Case split on wrap (aux) vs body forms and back-edge vs fresh visits.
-/

set_option linter.dupNamespace false

namespace SessionCoTypes.Coinductive
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

local instance : DecidableEq LocalTypeC := by
  classical
  infer_instance

/-! ## Main Roundtrip Lemma -/

lemma roundtrip_hpost
    (t : LocalTypeC)
    (all : Finset LocalTypeC)
    (h_closed : IsClosedSet all) :
    let R : Rel := fun ρ a b =>
      ∃ (visited : Finset LocalTypeC) (h_visited : visited ⊆ all) (h_current : b ∈ all),
        (a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current) ∨
         (b ∉ visited ∧
          a = toCoind (toInductiveBody t all visited b h_closed h_visited h_current))) ∧
        EnvOfSub all ρ
    ∀ ρ a b, R ρ a b → EQ2CE_step R ρ a b := by
  classical
  let R : Rel := roundtripRel t all h_closed
    intro ρ a b hR
    rcases hR with ⟨visited, h_visited, h_current, hcase, hsub⟩
    have hsub' : EnvOfSub all ρ := hsub
    have hmem_env : b ∈ envL ρ (nameOf b all) := EnvOfSub_mem hsub' h_current
    /-! ## `roundtrip_hpost`: Wrap vs Body Cases -/
    cases hcase with
    /-! ## `roundtrip_hpost`: Wrap Case (`toInductiveAux`) -/
    | inl hwrap =>
        /-! ## `roundtrip_hpost` Wrap: Back-Edge vs Fresh -/
        by_cases hmem : b ∈ visited
        /-! ## `roundtrip_hpost` Wrap: Back-Edge Variable -/
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
        /-! ## `roundtrip_hpost` Wrap: Fresh Node Unfolding -/
        · -- fresh node: unfold body
          have haux : a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current) := hwrap
          cases hdest : PFunctor.M.dest b with
          | mk hhead f =>
              cases hhead with
              /-! ## Fresh Wrap: `end` Head -/
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
              /-! ## Fresh Wrap: `var` Head -/
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
              /-! ## Fresh Wrap: `mu` Head -/
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
              /-! ## Fresh Wrap: `send` Head -/
              | send p labels =>
                  have hb : head b = .send p labels := by
                    exact head_of_dest hdest
                  let fR : Fin labels.length → (Label × LocalTypeR) := fun i =>
                    let child := f i
                    have hchild : childRel b child := ⟨.send p labels, f, i, hdest, rfl⟩
                    have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
                    (labels[i],
                      toInductiveAux t all (Insert.insert b visited) child h_closed
                        (subset_insert_of_mem h_current h_visited) hchild_mem)
                  /-! ## Fresh Wrap Send: Mu Wrapper vs Plain Send -/
                  by_cases hfv : nameOf b all ∈
                      (toInductiveBody t all visited b h_closed h_visited h_current).freeVars
                  /-! ## Fresh Wrap Send: Mu Wrapper Present -/
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
                    /-! ## Fresh Wrap Send Mu: Construct Left `mu` Step -/
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
                  /-! ## Fresh Wrap Send: Plain Send -/
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
                    /-! ## Fresh Wrap Send Plain: Build Send Observables -/
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
                    /-! ## Fresh Wrap Send Plain: Branch Relation Construction -/
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
              /-! ## Fresh Wrap: `recv` Head -/
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
                  /-! ## Fresh Wrap Recv: Mu Wrapper vs Plain Recv -/
                  by_cases hfv : nameOf b all ∈
                      (toInductiveBody t all visited b h_closed h_visited h_current).freeVars
                  /-! ## Fresh Wrap Recv: Mu Wrapper Present -/
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
                        /-! ## Fresh Wrap Recv Mu: Materialize Mu-Wrapped Auxiliary Form -/
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
                      /-! ## Fresh Wrap Recv Mu: Construct Left `mu` Step -/
                      simp [haux, haux_mu, toCoind_mu, mkMu, PFunctor.M.dest_mk]
                    have hmem' : b ∈ envL ρ (nameOf b all) := hmem_env
                    have hcore : R (envInsertL ρ (nameOf b all) b)
                        (toCoind (toInductiveBody t all visited b h_closed h_visited h_current)) b := by
                      refine ⟨visited, h_visited, h_current, ?_,
                        EnvOfSub_insertL (nameOf b all) b hsub'⟩
                      exact Or.inr ⟨hmem, rfl⟩
                    exact EQ2CE_step.mu_left ha hmem' hcore
                  /-! ## Fresh Wrap Recv: Plain Recv -/
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
                    /-! ## Fresh Wrap Recv Plain: Build Recv Observables -/
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
                    /-! ## Fresh Wrap Recv Plain: Branch Relation Construction -/
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
    /-! ## `roundtrip_hpost`: Body Case Delegation -/
    | inr hcore =>
        have hbody : EQ2CE_step (roundtripRel t all h_closed) ρ a b :=
          roundtrip_hpost_body_case (t := t) (all := all) (h_closed := h_closed)
            (visited := visited) (h_visited := h_visited) (h_current := h_current) hsub' hcore
        simpa [R] using hbody

end SessionCoTypes.Coinductive
