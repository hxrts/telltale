import SessionCoTypes.EQ2.Core

/-! # EQ2 Transitivity via Base Constructors

Transitivity helpers for EQ2 when the intermediate term is a base constructor
(.end or .var v).
-/

set_option linter.dupNamespace false
set_option linter.unusedTactic false

namespace SessionCoTypes.EQ2
open SessionTypes.LocalTypeR
/-! ## Transitivity (via Bisim)

EQ2 transitivity is proved in `EQ2Props.lean` using the Bisim detour, which
avoids circular imports by placing the proof in a separate module. -/

/-! ## Transitivity via base constructors (end/var)

These helper lemmas avoid full transitivity by coinduction on relations
that fix the intermediate constructor. They are useful in places where
the middle term is `.end` or `.var v`, which need not be well-formed. -/

set_option linter.unnecessarySimpa false

private def EndRel : Rel := fun a b => EQ2 a .end ∧ EQ2 .end b

private theorem EndRel_postfix : ∀ a b, EndRel a b → EQ2F EndRel a b := by
  intro a b h
  rcases h with ⟨ha, hb⟩
  cases a with
  | «end» =>
      cases b with
      | «end» => simp [EQ2F]
      | var v =>
          have hbF : EQ2F EQ2 .end (.var v) := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | send p bs =>
          have hbF : EQ2F EQ2 .end (.send p bs) := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | recv p bs =>
          have hbF : EQ2F EQ2 .end (.recv p bs) := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | mu t lbody =>
          have hb' : EQ2 .end (lbody.substitute t (.mu t lbody)) := by
            have hbF : EQ2F EQ2 .end (.mu t lbody) := EQ2.destruct hb
            simpa [EQ2F] using hbF
          have hrel : EndRel .end (lbody.substitute t (.mu t lbody)) :=
            ⟨EQ2_refl .end, hb'⟩
          simpa [EQ2F] using hrel
  | var v =>
      have haF : EQ2F EQ2 (.var v) .end := EQ2.destruct ha
      simpa [EQ2F] using haF
  | send p bs =>
      have haF : EQ2F EQ2 (.send p bs) .end := EQ2.destruct ha
      simpa [EQ2F] using haF
  | recv p bs =>
      have haF : EQ2F EQ2 (.recv p bs) .end := EQ2.destruct ha
      simpa [EQ2F] using haF
  | mu t lbody =>
      have ha' : EQ2 (lbody.substitute t (.mu t lbody)) .end := by
        have haF : EQ2F EQ2 (.mu t lbody) .end := EQ2.destruct ha
        simpa [EQ2F] using haF
      cases b with
      | «end» =>
          have hrel : EndRel (lbody.substitute t (.mu t lbody)) .end :=
            ⟨ha', hb⟩
          simpa [EQ2F] using hrel
      | var v =>
          have hrel : EndRel (lbody.substitute t (.mu t lbody)) (.var v) :=
            ⟨ha', hb⟩
          simpa [EQ2F] using hrel
      | send p bs =>
          have hrel : EndRel (lbody.substitute t (.mu t lbody)) (.send p bs) :=
            ⟨ha', hb⟩
          simpa [EQ2F] using hrel
      | recv p bs =>
          have hrel : EndRel (lbody.substitute t (.mu t lbody)) (.recv p bs) :=
            ⟨ha', hb⟩
          simpa [EQ2F] using hrel
      | mu s lbody' =>
          have hb' : EQ2 .end (lbody'.substitute s (.mu s lbody')) := by
            have hbF : EQ2F EQ2 .end (.mu s lbody') := EQ2.destruct hb
            simpa [EQ2F] using hbF
          have hleft : EndRel (lbody.substitute t (.mu t lbody)) (.mu s lbody') :=
            ⟨ha', hb⟩
          have hright : EndRel (.mu t lbody) (lbody'.substitute s (.mu s lbody')) :=
            ⟨ha, hb'⟩
          simpa [EQ2F] using And.intro hleft hright

theorem EQ2_trans_via_end {a b : LocalTypeR} (ha : EQ2 a .end) (hb : EQ2 .end b) : EQ2 a b := by
  have hinR : EndRel a b := ⟨ha, hb⟩
  exact EQ2_coind EndRel_postfix a b hinR

private def VarRel (v : String) : Rel := fun a b => EQ2 a (.var v) ∧ EQ2 (.var v) b

private theorem VarRel_postfix (v : String) :
    ∀ a b, VarRel v a b → EQ2F (VarRel v) a b := by
  intro a b h
  rcases h with ⟨ha, hb⟩
  cases a with
  | «end» =>
      have haF : EQ2F EQ2 .end (.var v) := EQ2.destruct ha
      simpa [EQ2F] using haF
  | var v' =>
      cases b with
      | «end» =>
          have hbF : EQ2F EQ2 (.var v) .end := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | var w =>
          have ha' : v' = v := by
            have haF : EQ2F EQ2 (.var v') (.var v) := EQ2.destruct ha
            simpa [EQ2F] using haF
          have hb' : v = w := by
            have hbF : EQ2F EQ2 (.var v) (.var w) := EQ2.destruct hb
            simpa [EQ2F] using hbF
          subst ha' hb'
          simp [EQ2F]
      | send p bs =>
          have hbF : EQ2F EQ2 (.var v) (.send p bs) := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | recv p bs =>
          have hbF : EQ2F EQ2 (.var v) (.recv p bs) := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | mu t lbody =>
          have ha' : v' = v := by
            have haF : EQ2F EQ2 (.var v') (.var v) := EQ2.destruct ha
            simpa [EQ2F] using haF
          subst ha'
          have hb' : EQ2 (.var v') (lbody.substitute t (.mu t lbody)) := by
            have hbF : EQ2F EQ2 (.var v') (.mu t lbody) := EQ2.destruct hb
            simpa [EQ2F] using hbF
          have hrel : VarRel v' (.var v') (lbody.substitute t (.mu t lbody)) :=
            ⟨EQ2_refl (.var v'), hb'⟩
          simpa [EQ2F] using hrel
  | send p bs =>
      have haF : EQ2F EQ2 (.send p bs) (.var v) := EQ2.destruct ha
      simpa [EQ2F] using haF
  | recv p bs =>
      have haF : EQ2F EQ2 (.recv p bs) (.var v) := EQ2.destruct ha
      simpa [EQ2F] using haF
  | mu t lbody =>
      have ha' : EQ2 (lbody.substitute t (.mu t lbody)) (.var v) := by
        have haF : EQ2F EQ2 (.mu t lbody) (.var v) := EQ2.destruct ha
        simpa [EQ2F] using haF
      cases b with
      | «end» =>
          have hbF : EQ2F EQ2 (.var v) .end := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | var w =>
          have hb' : v = w := by
            have hbF : EQ2F EQ2 (.var v) (.var w) := EQ2.destruct hb
            simpa [EQ2F] using hbF
          subst hb'
          have hrel : VarRel v (lbody.substitute t (.mu t lbody)) (.var v) :=
            ⟨ha', EQ2_refl (.var v)⟩
          simpa [EQ2F] using hrel
      | send p bs =>
          have hbF : EQ2F EQ2 (.var v) (.send p bs) := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | recv p bs =>
          have hbF : EQ2F EQ2 (.var v) (.recv p bs) := EQ2.destruct hb
          simpa [EQ2F] using hbF
      | mu s lbody' =>
          have hb' : EQ2 (.var v) (lbody'.substitute s (.mu s lbody')) := by
            have hbF : EQ2F EQ2 (.var v) (.mu s lbody') := EQ2.destruct hb
            simpa [EQ2F] using hbF
          have hleft : VarRel v (lbody.substitute t (.mu t lbody)) (.mu s lbody') :=
            ⟨ha', hb⟩
          have hright : VarRel v (.mu t lbody) (lbody'.substitute s (.mu s lbody')) :=
            ⟨ha, hb'⟩
          simpa [EQ2F] using And.intro hleft hright

theorem EQ2_trans_via_var {a b : LocalTypeR} {v : String}
    (ha : EQ2 a (.var v)) (hb : EQ2 (.var v) b) : EQ2 a b := by
  have hinR : VarRel v a b := ⟨ha, hb⟩
  exact EQ2_coind (VarRel_postfix v) a b hinR

set_option linter.unnecessarySimpa true

end SessionCoTypes.EQ2
