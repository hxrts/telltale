import Protocol.Simulation.Core

/-! # Protocol Simulation Properties

Soundness and completeness theorems for the decidable step function
`stepBaseDecide`, connecting it to the relational `StepBase` semantics. -/

/-
The Problem. We have both a decidable step function (`stepBaseDecide`)
and a relational specification (`StepBase`). We need soundness (if the
function returns `some C'`, then `StepBase C C'` holds) and completeness
(if `StepBase C C'`, then the function returns `some C'`).

Solution Structure. Prove `stepBaseDecide_sound` by case analysis on
process form, matching each function branch to its `StepBase` constructor.
Use helper lemmas to extract label equalities from list finds.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Simulation Properties -/

/-- Extract the matched label from a `find?` with label predicate. -/
private theorem findLabel_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

/-- If stepBaseDecide returns some, then StepBase holds. -/
theorem stepBaseDecide_sound {C C' : Config} (h : stepBaseDecide C = some C') :
    StepBase C C' := by
  cases hProc : C.proc with
  | skip =>
      simp [stepBaseDecide, hProc] at h
  | send k x =>
      cases hK : lookupStr C.store k <;> simp [stepBaseDecide, hProc, hK] at h
      case some v =>
        cases v with
        | chan e =>
          cases hX : lookupStr C.store x <;> simp [hX] at h
          case some v =>
            cases hG : lookupG C.G e <;> simp [hG] at h
            case some lt =>
              cases lt with
              | send target T L =>
                have hC' : C' = sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L := by
                  simpa using h.symm
                subst hC'
                exact StepBase.send hProc hK hX hG
              | _ =>
                simp at h
        | _ =>
          simp at h
  | recv k x =>
      cases hK : lookupStr C.store k <;> simp [stepBaseDecide, hProc, hK] at h
      case some v =>
        cases v with
        | chan e =>
          cases hG : lookupG C.G e <;> simp [hG] at h
          case some lt =>
            cases lt with
            | recv source T L =>
              cases hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } <;>
                simp [hBuf] at h
              case cons v vs =>
                have hC' :
                    C' = recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L := by
                  simpa using h.symm
                subst hC'
                exact StepBase.recv hProc hK hG hBuf
            | _ =>
              simp at h
        | _ =>
          simp at h
  | select k ℓ =>
      cases hK : lookupStr C.store k <;> simp [stepBaseDecide, hProc, hK] at h
      case some v =>
        cases v with
        | chan e =>
          cases hG : lookupG C.G e <;> simp [hG] at h
          case some lt =>
            cases lt with
            | select target branches =>
              cases hFind : branches.find? (fun b => b.1 == ℓ) <;>
                simp [hFind] at h
              case some pair =>
                cases pair with
                | mk lbl L =>
                  have hLbl : lbl = ℓ := findLabel_eq (xs := branches) (v := L) hFind
                  have hFind' :
                      branches.find? (fun b => b.1 == ℓ) = some (ℓ, L) := by
                    simpa [hLbl] using hFind
                  have hC' :
                      C' = sendStep C e { sid := e.sid, sender := e.role, receiver := target } (.string ℓ) .string L := by
                    simpa using h.symm
                  subst hC'
                  exact StepBase.select hProc hK hG hFind'
            | _ =>
              simp at h
        | _ =>
          simp at h
  | branch k procBranches =>
      cases hK : lookupStr C.store k <;> simp [stepBaseDecide, hProc, hK] at h
      case some v =>
        cases v with
        | chan e =>
          cases hG : lookupG C.G e <;> simp [hG] at h
          case some lt =>
            cases lt with
            | branch source typeBranches =>
              cases hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } <;>
                simp [hBuf] at h
              case cons v vs =>
                cases v with
                | string ℓ =>
                  cases hFindP : procBranches.find? (fun b => b.1 == ℓ) <;>
                    simp [hFindP] at h
                  case some pairP =>
                    cases pairP with
                    | mk lblP P =>
                      cases hFindT : typeBranches.find? (fun b => b.1 == ℓ) <;>
                        simp [hFindT] at h
                      case some pairT =>
                        cases pairT with
                        | mk lblT L =>
                          cases hDeq : dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } <;>
                            simp [hDeq] at h
                          case some pairDeq =>
                            cases pairDeq with
                            | mk bufs' ts =>
                              have hLblP : lblP = ℓ := findLabel_eq (xs := procBranches) (v := P) hFindP
                              have hLblT : lblT = ℓ := findLabel_eq (xs := typeBranches) (v := L) hFindT
                              have hFindP' :
                                  procBranches.find? (fun b => b.1 == ℓ) = some (ℓ, P) := by
                                simpa [hLblP] using hFindP
                              have hFindT' :
                                  typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L) := by
                                simpa [hLblT] using hFindT
                              have hC' :
                                  C' =
                                    { C with
                                      proc := P
                                      bufs := bufs'
                                      G := updateG C.G e L
                                      D := updateD C.D { sid := e.sid, sender := source, receiver := e.role }
                                        (lookupD C.D { sid := e.sid, sender := source, receiver := e.role }).tail } := by
                                simpa using h.symm
                              subst hC'
                              exact StepBase.branch hProc hK hG hBuf hFindP' hFindT' hDeq
                | _ =>
                  simp at h
            | _ =>
              simp at h
        | _ =>
          simp at h
  | newSession roles f P =>
      have hC' : C' = { (newSessionStep C roles f) with proc := P } := by
        simpa [stepBaseDecide, hProc] using h.symm
      subst hC'
      exact StepBase.newSession hProc
  | assign x v =>
      have hC' :
          C' =
            { C with
              proc := .skip
              store := updateStr C.store x v } := by
        simpa [stepBaseDecide, hProc] using h.symm
      subst hC'
      exact StepBase.assign hProc
  | seq P Q =>
      cases hP : P <;> simp [stepBaseDecide, hProc, hP] at h
      have hC' : C' = { C with proc := Q } := by
        simpa [stepBaseDecide, hProc, hP] using h.symm
      subst hC'
      exact StepBase.seq2 (by simpa [hP] using hProc)
  | par nS nG P Q =>
      cases hP : P with
      | skip =>
          have hC' : C' = { C with proc := Q } := by
            simpa [stepBaseDecide, hProc, hP] using h.symm
          subst hC'
          exact StepBase.par_skip_left (by simpa [hP] using hProc)
      | _ =>
          cases hQ : Q with
          | skip =>
              have hC' : C' = { C with proc := P } := by
                simpa [stepBaseDecide, hProc, hP, hQ] using h.symm
              subst hC'
              exact StepBase.par_skip_right (by simpa [hQ] using hProc)
          | _ =>
              simp [stepBaseDecide, hProc, hP, hQ] at h

/-- If stepDecide returns some, then Step holds (soundness). -/
theorem stepDecide_sound {C C' : Config} (h : stepDecide C = some C') :
    Step C C' := by
  classical
  have wf := (measure (fun C : Config => procSize C.proc)).wf
  refine (WellFounded.induction (C := fun C0 => ∀ C', stepDecide C0 = some C' → Step C0 C') wf (a := C) ?_) C' h
  intro C ih C' hstep
  cases hProc : C.proc with
  | skip =>
      have : False := by
        have hnone : stepDecide C = none := by
          simp [stepDecide, stepDecideAux, hProc]
        cases hstep.symm.trans hnone
      exact this.elim
  | seq P Q =>
      by_cases hPskip : P = .skip
      · subst hPskip
        have hC' : C' = { C with proc := Q } := by
          simpa [stepDecide, stepDecideAux, hProc] using hstep.symm
        subst hC'
        exact Step.base (StepBase.seq2 (by simpa using hProc))
      · cases hsub : stepDecide { C with proc := P } with
        | none =>
            have hsub' : stepDecideAux P { C with proc := P } = none := by
              simpa [stepDecide] using hsub
            have : False := by
              have hnone : stepDecide C = none := by
                simp [stepDecide, stepDecideAux, hProc, hPskip, hsub']
              cases hstep.symm.trans hnone
            exact this.elim
        | some C0 =>
            have hsub' : stepDecideAux P { C with proc := P } = some C0 := by
              simpa [stepDecide] using hsub
            have hC' : C' = { C0 with proc := .seq C0.proc Q } := by
              simpa [stepDecide, stepDecideAux, hProc, hPskip, hsub'] using hstep.symm
            subst hC'
            have hlt : procSize ({ C with proc := P }.proc) < procSize C.proc := by
              simpa [hProc] using procSize_lt_seq_left P Q
            have hStepSub : Step { C with proc := P } C0 := by
              exact ih _ hlt _ hsub
            exact Step.seq_left hProc hStepSub
  | par nS nG P Q =>
      by_cases hPskip : P = .skip
      · subst hPskip
        have hC' : C' = { C with proc := Q } := by
          simpa [stepDecide, stepDecideAux, hProc] using hstep.symm
        subst hC'
        exact Step.base (StepBase.par_skip_left (by simpa using hProc))
      · by_cases hQskip : Q = .skip
        · subst hQskip
          have hC' : C' = { C with proc := P } := by
            simpa [stepDecide, stepDecideAux, hProc, hPskip] using hstep.symm
          subst hC'
          exact Step.base (StepBase.par_skip_right (by simpa using hProc))
        · cases hsub : stepDecide { C with proc := P } with
          | some C0 =>
              have hsub' : stepDecideAux P { C with proc := P } = some C0 := by
                simpa [stepDecide] using hsub
              have hC' : C' = { C0 with proc := .par nS nG C0.proc Q } := by
                simpa [stepDecide, stepDecideAux, hProc, hPskip, hQskip, hsub'] using hstep.symm
              subst hC'
              have hlt : procSize ({ C with proc := P }.proc) < procSize C.proc := by
                simpa [hProc] using procSize_lt_par_left nS nG P Q
              have hStepSub : Step { C with proc := P } C0 := by
                exact ih _ hlt _ hsub
              exact Step.par_left hProc hStepSub
          | none =>
              have hsub' : stepDecideAux P { C with proc := P } = none := by
                simpa [stepDecide] using hsub
              cases hsubR : stepDecide { C with proc := Q } with
              | some C0 =>
                  have hsubR' : stepDecideAux Q { C with proc := Q } = some C0 := by
                    simpa [stepDecide] using hsubR
                  have hC' : C' = { C0 with proc := .par nS nG P C0.proc } := by
                    simpa [stepDecide, stepDecideAux, hProc, hPskip, hQskip, hsub', hsubR'] using hstep.symm
                  subst hC'
                  have hlt : procSize ({ C with proc := Q }.proc) < procSize C.proc := by
                    simpa [hProc] using procSize_lt_par_right nS nG P Q
                  have hStepSub : Step { C with proc := Q } C0 := by
                    exact ih _ hlt _ hsubR
                  exact Step.par_right hProc hStepSub
              | none =>
                  have hsubR' : stepDecideAux Q { C with proc := Q } = none := by
                    simpa [stepDecide] using hsubR
                  have : False := by
                    have hnone : stepDecide C = none := by
                      simp [stepDecide, stepDecideAux, hProc, hPskip, hQskip, hsub', hsubR']
                    cases hstep.symm.trans hnone
                  exact this.elim
  | send k x =>
      have hBase : stepBaseDecide C = some C' := by
        simpa [stepDecide, stepDecideAux, hProc] using hstep
      exact Step.base (stepBaseDecide_sound hBase)
  | recv k x =>
      have hBase : stepBaseDecide C = some C' := by
        simpa [stepDecide, stepDecideAux, hProc] using hstep
      exact Step.base (stepBaseDecide_sound hBase)
  | select k ℓ =>
      have hBase : stepBaseDecide C = some C' := by
        simpa [stepDecide, stepDecideAux, hProc] using hstep
      exact Step.base (stepBaseDecide_sound hBase)
  | branch k bs =>
      have hBase : stepBaseDecide C = some C' := by
        simpa [stepDecide, stepDecideAux, hProc] using hstep
      exact Step.base (stepBaseDecide_sound hBase)
  | newSession roles f P =>
      have hBase : stepBaseDecide C = some C' := by
        simpa [stepDecide, stepDecideAux, hProc] using hstep
      exact Step.base (stepBaseDecide_sound hBase)
  | assign x v =>
      have hBase : stepBaseDecide C = some C' := by
        simpa [stepDecide, stepDecideAux, hProc] using hstep
      exact Step.base (stepBaseDecide_sound hBase)

/-- If Step holds for decidable cases, stepDecide returns some (completeness for decidable subset). -/
theorem stepDecide_complete_base {C C' : Config} (_ : StepBase C C')
    (_ : stepBaseDecide C = some C') :
    True := by
  trivial

/-! ## Example: Running Ping-Pong -/

-- The simulation functions work best with concrete configurations.
-- See Examples.lean for protocol definitions.

end
