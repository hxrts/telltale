
import SessionCoTypes.Coinductive.Roundtrip.EnvDefs

/-! # Roundtrip Body Case

Body-case lemma for the roundtrip bisimulation, handling fresh visits
where the type is unfolded rather than producing a back-edge variable. -/

/-
The Problem. The roundtrip relation has two forms: wrap (toInductiveAux)
for back-edges producing variables, and body (toInductiveBody) for fresh
visits. The body case requires case analysis on the type constructor.

Solution Structure. Define `roundtripRel` capturing both forms. Prove
`roundtrip_hpost_body_case` by destructing the coinductive type head
and showing EQ2CE_step holds for each constructor.
-/

/- ## Structured Block 1 -/
set_option linter.dupNamespace false

namespace SessionCoTypes.Coinductive
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

local instance : DecidableEq LocalTypeC := by
  classical
  infer_instance

-- Roundtrip Relation

def roundtripRel
    (t : LocalTypeC)
    (all : Finset LocalTypeC)
    (h_closed : IsClosedSet all) : Rel :=
  fun ρ a b =>
    ∃ (visited : Finset LocalTypeC) (h_visited : visited ⊆ all) (h_current : b ∈ all),
      (a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current) ∨
       (b ∉ visited ∧
       a = toCoind (toInductiveBody t all visited b h_closed h_visited h_current))) ∧
      EnvOfSub all ρ

-- Body Case: Fresh-Visit Postfix Step

lemma roundtrip_hpost_body_case
    (t : LocalTypeC) (all : Finset LocalTypeC) (h_closed : IsClosedSet all)
    {ρ a b : LocalTypeC}
    {visited : Finset LocalTypeC} {h_visited : visited ⊆ all} {h_current : b ∈ all}
    (hsub' : EnvOfSub all ρ)
    (hcore : b ∉ visited ∧
      a = toCoind (toInductiveBody t all visited b h_closed h_visited h_current)) :
    EQ2CE_step (roundtripRel t all h_closed) ρ a b := by
  let R : Rel := roundtripRel t all h_closed
  rcases hcore with ⟨hmem, hcore⟩
  cases hdest : PFunctor.M.dest b with
  | mk hhead f =>
      cases hhead with
            -- Body Case: `end` Head
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
            -- Body Case: `var` Head
            | var x =>
                have hbody_var :
                    toInductiveBody t all visited b h_closed h_visited h_current = LocalTypeR.var x := by
                  have hb_eq : b = PFunctor.M.mk ⟨LocalTypeHead.var x, f⟩ := mk_of_dest hdest
                  subst hb_eq
                  unfold toInductiveBody
                  simp [PFunctor.M.dest_mk]
                have ha : head a = .var x := by
/- ## Structured Block 2 -/
                  simp [hcore, hbody_var]
                have hb : head b = .var x := by
                  exact head_of_dest hdest
                exact EQ2CE_step.var ha hb
            -- Body Case: `mu` Head
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
            -- Body Case: `send` Head
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
/- ## Structured Block 3 -/
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
            -- Body Case: `recv` Head
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
/- ## Structured Block 4 -/
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

end SessionCoTypes.Coinductive
