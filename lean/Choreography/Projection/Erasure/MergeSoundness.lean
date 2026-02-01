import Choreography.Projection.Erasure.Merge

/-! # Choreography.Projection.Erasure.MergeSoundness

Merge soundness helpers and proofs for erasure.
-/
namespace Choreography.Projection.Erasure
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
noncomputable section
open Classical
/-! ## Merge Soundness Helpers -/

private theorem mergeBranchesSend_sound
    (m : Nat)
    (hmerge : ∀ a b c, sizeOf a + sizeOf b < m → merge a b = some c → Erases a b c)
    {bs1 bs2 bs : List (Label × LocalTypeR)}
    (hm : sizeOf bs1 + sizeOf bs2 < m)
    (h : mergeBranchesSend bs1 bs2 = some bs) :
    labelsSubset bs1 bs2 ∧ labelsSubset bs1 bs ∧ labelsSubset bs bs1 ∧
    (∀ lbl t1 t2 t,
      lookupBranch lbl bs1 = some t1 →
      lookupBranch lbl bs2 = some t2 →
      lookupBranch lbl bs = some t →
      Erases t1 t2 t) := by
  induction bs1 generalizing bs with
  | nil =>
      cases hsubset : labelsSubsetb bs2 [] with
      | true =>
          simp [mergeBranchesSend, hsubset] at h
          cases h
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro lbl hIn
            have : False := by
              simp [labelIn, lookupBranch] at hIn
            exact this.elim
          · intro lbl hIn
            have : False := by
              simp [labelIn, lookupBranch] at hIn
            exact this.elim
          · intro lbl hIn
            have : False := by
              simp [labelIn, lookupBranch] at hIn
            exact this.elim
          · intro lbl t1 t2 t h1 _ _
            simp [lookupBranch] at h1
      | false =>
          have hnone : mergeBranchesSend [] bs2 = none := by
            simp [mergeBranchesSend, hsubset]
          have : False := by
            simp [hnone] at h
          exact this.elim
  | cons head tail ih =>
      cases head with
      | mk l t1 =>
          rcases mergeBranchesSend_eq_some (lbl := l) (t1 := t1)
              (rest := tail) (bs2 := bs2) (bs := bs) h with
            ⟨t2, t, rest', hlookup, hmerge', hrest, rfl⟩
          have hm_tail : sizeOf tail + sizeOf bs2 < m := by
            have htail : sizeOf tail < sizeOf ((l, t1) :: tail) := by
              simpa using (sizeOf_tail_lt_sizeOf_branches (head := (l, t1)) (tail := tail))
            have hsum : sizeOf tail + sizeOf bs2 < sizeOf ((l, t1) :: tail) + sizeOf bs2 :=
              Nat.add_lt_add_right htail _
            exact Nat.lt_trans hsum hm
          have ih' := ih hm_tail hrest
          rcases ih' with ⟨hsub12, hsub1b, hsubb1, hper⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro lbl hIn
            by_cases hlt : l = lbl
            ·
              have hlookup' : lookupBranch lbl bs2 = some t2 := by
                simpa [hlt] using hlookup
              simp [labelIn, hlookup']
            ·
              have hIn_tail : labelIn lbl tail :=
                (labelIn_tail_of_ne (lbl := lbl) (l := l) (t := t1) (rest := tail) hlt).1 hIn
              exact hsub12 lbl hIn_tail
          · intro lbl hIn
            by_cases hlt : l = lbl
            ·
              simp [labelIn, lookupBranch, hlt]
            ·
              have hIn_tail : labelIn lbl tail :=
                (labelIn_tail_of_ne (lbl := lbl) (l := l) (t := t1) (rest := tail) hlt).1 hIn
              have hIn_rest' := hsub1b lbl hIn_tail
              exact (labelIn_tail_of_ne (lbl := lbl) (l := l) (t := t) (rest := rest') hlt).2 hIn_rest'
          · intro lbl hIn
            by_cases hlt : l = lbl
            ·
              simp [labelIn, lookupBranch, hlt]
            ·
              have hIn_rest' : labelIn lbl rest' :=
                (labelIn_tail_of_ne (lbl := lbl) (l := l) (t := t) (rest := rest') hlt).1 hIn
              have hIn_tail := hsubb1 lbl hIn_rest'
              exact (labelIn_tail_of_ne (lbl := lbl) (l := l) (t := t1) (rest := tail) hlt).2 hIn_tail
          · intro lbl t1' t2' t' h1 h2 hbs
            by_cases hlt : l = lbl
            ·
              simp [lookupBranch, hlt] at h1
              cases h1
              have hlookup' : lookupBranch lbl bs2 = some t2 := by
                simpa [hlt] using hlookup
              have hmem2 : t2 ∈ bs2.map Prod.snd := by
                refine List.mem_map.2 ?_
                exact ⟨(lbl, t2), mem_of_lookupBranch hlookup', rfl⟩
              have hlt1 : sizeOf t1 < sizeOf ((lbl, t1) :: tail) :=
                sizeOf_cont_lt_sizeOf_branches lbl t1 tail
              have hlt2 : sizeOf t2 < sizeOf bs2 :=
                sizeOf_cont_lt_sizeOf_branches_mem (cont := t2) hmem2
              have hsum :
                  sizeOf t1 + sizeOf t2 < sizeOf ((lbl, t1) :: tail) + sizeOf bs2 :=
                Nat.add_lt_add hlt1 hlt2
              have hm' : sizeOf ((lbl, t1) :: tail) + sizeOf bs2 < m := by
                simpa [hlt] using hm
              have hltm : sizeOf t1 + sizeOf t2 < m := Nat.lt_trans hsum hm'
              have ht2 : t2 = t2' := by
                simpa [hlookup'] using h2
              subst ht2
              simp [lookupBranch, hlt] at hbs
              cases hbs
              exact hmerge _ _ _ hltm hmerge'
            ·
              have h1_tail : lookupBranch lbl tail = some t1' := by
                simpa [lookupBranch, hlt] using h1
              have hbs' : lookupBranch lbl rest' = some t' := by
                simpa [lookupBranch, hlt] using hbs
              exact hper lbl t1' t2' t' h1_tail h2 hbs'
private theorem mergeBranchesRecv_sound
    (m : Nat)
    (hmerge : ∀ a b c, sizeOf a + sizeOf b < m → merge a b = some c → Erases a b c)
    {bs1 bs2 bs : List (Label × LocalTypeR)}
    (hm : sizeOf bs1 + sizeOf bs2 < m)
    (h : mergeBranchesRecv bs1 bs2 = some bs) :
    (∀ lbl t1 t2 t,
      lookupBranch lbl bs1 = some t1 →
      lookupBranch lbl bs2 = some t2 →
      lookupBranch lbl bs = some t →
      Erases t1 t2 t) ∧
    (∀ lbl t1,
      lookupBranch lbl bs1 = some t1 →
      lookupBranch lbl bs2 = none →
      lookupBranch lbl bs = some t1) ∧
    (∀ lbl t2,
      lookupBranch lbl bs1 = none →
      lookupBranch lbl bs2 = some t2 →
      lookupBranch lbl bs = some t2) := by
  induction bs1 generalizing bs with
  | nil =>
      simp [mergeBranchesRecv] at h
      cases h
      refine ⟨?_, ?_, ?_⟩
      · intro lbl t1 t2 t h1 _ _
        simp [lookupBranch] at h1
      · intro lbl t1 h1 _
        simp [lookupBranch] at h1
      · intro lbl t2 h1 h2
        simp [appendMissing_nil] at h2 ⊢
        exact h2
  | cons head tail ih =>
      cases head with
      | mk l t1 =>
          rcases mergeBranchesRecv_eq_some (lbl := l) (t1 := t1)
              (rest := tail) (bs2 := bs2) (bs := bs) h with
            hnone | hsome
          · rcases hnone with ⟨hlookup, rest', hrest, rfl⟩
            have hm_tail : sizeOf tail + sizeOf bs2 < m := by
              have htail : sizeOf tail < sizeOf ((l, t1) :: tail) := by
                simpa using (sizeOf_tail_lt_sizeOf_branches (head := (l, t1)) (tail := tail))
              have hsum : sizeOf tail + sizeOf bs2 < sizeOf ((l, t1) :: tail) + sizeOf bs2 :=
                Nat.add_lt_add_right htail _
              exact Nat.lt_trans hsum hm
            have ih' := ih hm_tail hrest
            rcases ih' with ⟨hper, hleft, hright⟩
            refine ⟨?_, ?_, ?_⟩
            · intro lbl t1' t2' t' h1' h2' hbs
              by_cases hlt : l = lbl
              ·
                exfalso
                have h2'' : lookupBranch l bs2 = some t2' := by
                  simpa [hlt] using h2'
                simp [hlookup] at h2''
              ·
                have h1_tail : lookupBranch lbl tail = some t1' := by
                  simpa [lookupBranch, hlt] using h1'
                have hbs' : lookupBranch lbl rest' = some t' := by
                  simpa [lookupBranch, hlt] using hbs
                exact hper lbl t1' t2' t' h1_tail h2' hbs'
            · intro lbl t1' h1' h2'
              by_cases hlt : l = lbl
              ·
                simp [lookupBranch, hlt] at h1'
                cases h1'
                simp [lookupBranch, hlt]
              ·
                have h1_tail : lookupBranch lbl tail = some t1' := by
                  simpa [lookupBranch, hlt] using h1'
                have htail := hleft lbl t1' h1_tail h2'
                simpa [lookupBranch, hlt] using htail
            · intro lbl t2' h1' h2'
              by_cases hlt : l = lbl
              · simp [lookupBranch, hlt] at h1'
              ·
                have h1_tail : lookupBranch lbl tail = none := by
                  simpa [lookupBranch, hlt] using h1'
                have htail := hright lbl t2' h1_tail h2'
                simpa [lookupBranch, hlt] using htail
          · rcases hsome with ⟨t2, t, rest', hlookup, hmerge', hrest, rfl⟩
            have hm_tail : sizeOf tail + sizeOf bs2 < m := by
              have htail : sizeOf tail < sizeOf ((l, t1) :: tail) := by
                simpa using (sizeOf_tail_lt_sizeOf_branches (head := (l, t1)) (tail := tail))
              have hsum : sizeOf tail + sizeOf bs2 < sizeOf ((l, t1) :: tail) + sizeOf bs2 :=
                Nat.add_lt_add_right htail _
              exact Nat.lt_trans hsum hm
            have ih' := ih hm_tail hrest
            rcases ih' with ⟨hper, hleft, hright⟩
            refine ⟨?_, ?_, ?_⟩
            · intro lbl t1' t2' t' h1' h2' hbs
              by_cases hlt : l = lbl
              ·
                simp [lookupBranch, hlt] at h1'
                cases h1'
                have hlookup' : lookupBranch lbl bs2 = some t2 := by
                  simpa [hlt] using hlookup
                have hmem2 : t2 ∈ bs2.map Prod.snd := by
                  refine List.mem_map.2 ?_
                  exact ⟨(lbl, t2), mem_of_lookupBranch hlookup', rfl⟩
                have hlt1 : sizeOf t1 < sizeOf ((lbl, t1) :: tail) :=
                  sizeOf_cont_lt_sizeOf_branches lbl t1 tail
                have hlt2 : sizeOf t2 < sizeOf bs2 :=
                  sizeOf_cont_lt_sizeOf_branches_mem (cont := t2) hmem2
                have hsum :
                    sizeOf t1 + sizeOf t2 < sizeOf ((lbl, t1) :: tail) + sizeOf bs2 :=
                  Nat.add_lt_add hlt1 hlt2
                have hm' : sizeOf ((lbl, t1) :: tail) + sizeOf bs2 < m := by
                  simpa [hlt] using hm
                have hltm : sizeOf t1 + sizeOf t2 < m := Nat.lt_trans hsum hm'
                have ht2 : t2 = t2' := by
                  simpa [hlookup'] using h2'
                subst ht2
                simp [lookupBranch, hlt] at hbs
                cases hbs
                exact hmerge _ _ _ hltm hmerge'
              ·
                have h1_tail : lookupBranch lbl tail = some t1' := by
                  simpa [lookupBranch, hlt] using h1'
                have hbs' : lookupBranch lbl rest' = some t' := by
                  simpa [lookupBranch, hlt] using hbs
                exact hper lbl t1' t2' t' h1_tail h2' hbs'
            · intro lbl t1' h1' h2'
              by_cases hlt : l = lbl
              ·
                exfalso
                have h2'' : lookupBranch l bs2 = none := by
                  simpa [hlt] using h2'
                simp [hlookup] at h2''
              ·
                have h1_tail : lookupBranch lbl tail = some t1' := by
                  simpa [lookupBranch, hlt] using h1'
                have htail := hleft lbl t1' h1_tail h2'
                simpa [lookupBranch, hlt] using htail
            · intro lbl t2' h1' h2'
              by_cases hlt : l = lbl
              · simp [lookupBranch, hlt] at h1'
              ·
                have h1_tail : lookupBranch lbl tail = none := by
                  simpa [lookupBranch, hlt] using h1'
                have htail := hright lbl t2' h1_tail h2'
                simpa [lookupBranch, hlt] using htail

/-! ## Merge Soundness -/

/-- merge is sound w.r.t. Erases. -/
theorem merge_sound : ∀ a b c, merge a b = some c → Erases a b c := by
  classical
  intro a b c h
  -- Well-founded induction on sizeOf a + sizeOf b.
  refine (WellFounded.induction
    (measure (fun p : LocalTypeR × LocalTypeR => sizeOf p.1 + sizeOf p.2)).wf
    (C := fun p => ∀ c, merge p.1 p.2 = some c → Erases p.1 p.2 c)
    (a := (a, b)) ?_) c h
  intro p IH c h
  cases p with
  | mk a b =>
      let m := sizeOf a + sizeOf b
      have hmerge : ∀ a' b' c', sizeOf a' + sizeOf b' < m → merge a' b' = some c' → Erases a' b' c' := by
        intro a' b' c' hlt h'
        exact IH (a', b') hlt c' h'
      cases a with
      | «end» =>
          cases b with
          | «end» =>
              simp [merge] at h
              cases h
              exact Erases.end
          | var _ | mu _ _ | send _ _ | recv _ _ =>
              have : False := by
                simp [merge] at h
              exact this.elim
      | var v =>
          cases b with
          | var w =>
              by_cases hv : v = w
              · simp [merge, hv] at h
                cases h
                simpa [hv] using (Erases.var v)
              · have : False := by
                  simp [merge, hv] at h
                exact this.elim
          | «end» | mu _ _ | send _ _ | recv _ _ =>
              have : False := by
                simp [merge] at h
              exact this.elim
      | mu v a' =>
          cases b with
          | mu w b' =>
              by_cases hv : v = w
              · simp [merge, hv] at h
                cases h' : merge a' b' with
                | none => simp [h'] at h
                | some c' =>
                    simp [h'] at h
                    cases h
                    have hlt : sizeOf a' + sizeOf b' < m := by
                      have h1 : sizeOf a' < sizeOf (LocalTypeR.mu v a') := sizeOf_body_lt_sizeOf_mu v a'
                      have h2 : sizeOf b' < sizeOf (LocalTypeR.mu w b') := sizeOf_body_lt_sizeOf_mu w b'
                      have hsum :
                          sizeOf a' + sizeOf b' < sizeOf (LocalTypeR.mu v a') + sizeOf (LocalTypeR.mu w b') :=
                        Nat.add_lt_add h1 h2
                      simpa [m] using hsum
                    simpa [hv] using (Erases.mu v (hmerge _ _ _ hlt h'))
              ·
                have : False := by
                  simp [merge, hv] at h
                exact this.elim
          | «end» | var _ | send _ _ | recv _ _ =>
              have : False := by
                simp [merge] at h
              exact this.elim
      | send p bs =>
          cases b with
          | send q bs' =>
              by_cases hp : p = q
              · subst hp
                simp [merge] at h
                cases hmerge' : mergeBranchesSend bs bs' with
                | none =>
                    simp [hmerge'] at h
                | some bs'' =>
                    by_cases hsubset : labelsSubsetb bs' bs = true
                    · simp [hmerge', hsubset] at h
                      cases h
                      have hm : sizeOf bs + sizeOf bs' < m := by
                        have h1 : sizeOf bs < sizeOf (LocalTypeR.send p bs) :=
                          sizeOf_branches_lt_sizeOf_send p bs
                        have h2 : sizeOf bs' < sizeOf (LocalTypeR.send p bs') :=
                          sizeOf_branches_lt_sizeOf_send p bs'
                        have hsum :
                            sizeOf bs + sizeOf bs' < sizeOf (LocalTypeR.send p bs) + sizeOf (LocalTypeR.send p bs') :=
                          Nat.add_lt_add h1 h2
                        simpa [m] using hsum
                      have hsend :=
                        mergeBranchesSend_sound m hmerge (bs1 := bs) (bs2 := bs') (bs := bs'') hm hmerge'
                      rcases hsend with ⟨hsub12, hsub1b, hsubb1, hper⟩
                      have hsub21 : labelsSubset bs' bs :=
                        labelsSubset_of_labelsSubsetb (bs1 := bs') (bs2 := bs) hsubset
                      have h1 : sameLabels bs bs' := sameLabels_of_subsets hsub12 hsub21
                      have h2 : sameLabels bs bs'' := sameLabels_of_subsets hsub1b hsubb1
                      exact Erases.send h1 h2 hper
                    · simp [hmerge', hsubset] at h
              · simp [merge, hp] at h
          | «end» | var _ | mu _ _ | recv _ _ =>
              have : False := by
                simp [merge] at h
              exact this.elim
      | recv p bs =>
          cases b with
          | recv q bs' =>
              by_cases hp : p = q
              · subst hp
                simp [merge] at h
                cases hmerge' : mergeBranchesRecv bs bs' with
                | none =>
                    simp [hmerge'] at h
                | some bs'' =>
                    simp [hmerge'] at h
                    cases h
                    have hm : sizeOf bs + sizeOf bs' < m := by
                      have h1 : sizeOf bs < sizeOf (LocalTypeR.recv p bs) :=
                        sizeOf_branches_lt_sizeOf_recv p bs
                      have h2 : sizeOf bs' < sizeOf (LocalTypeR.recv p bs') :=
                        sizeOf_branches_lt_sizeOf_recv p bs'
                      have hsum :
                          sizeOf bs + sizeOf bs' < sizeOf (LocalTypeR.recv p bs) + sizeOf (LocalTypeR.recv p bs') :=
                        Nat.add_lt_add h1 h2
                      simpa [m] using hsum
                    have hrecv :=
                      mergeBranchesRecv_sound m hmerge (bs1 := bs) (bs2 := bs') (bs := bs'') hm hmerge'
                    rcases hrecv with ⟨hper, hleft, hright⟩
                    exact Erases.recv hper hleft hright
              · simp [merge, hp] at h
          | «end» | var _ | mu _ _ | send _ _ =>
              have : False := by
                simp [merge] at h
              exact this.elim
/-- mergeAll is sound w.r.t. ErasesAll. -/
theorem mergeAll_sound {ts : List LocalTypeR} {t : LocalTypeR}
    (h : mergeAll ts = some t) : ErasesAll ts t := by
  induction ts generalizing t with
  | nil => simp [mergeAll] at h
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [mergeAll] at h
          cases h
          simp [ErasesAll]
      | cons b rest' =>
          simp [mergeAll] at h
          cases hrest : mergeAll (b :: rest') with
          | none => simp [hrest] at h
          | some u =>
              simp [hrest] at h
              refine ⟨u, ?_, merge_sound _ _ _ h⟩
              exact ih hrest
end
end Choreography.Projection.Erasure
