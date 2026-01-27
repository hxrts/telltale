import RumpsteakV2.Protocol.CoTypes.Bisim.Part6

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace RumpsteakV2.Protocol.CoTypes.Bisim
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.CoTypes.Observable
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.CoinductiveRel
/-! ## EQ2 to Bisim (Well-Formed Witness) -/

theorem EQ2.toBisim_of_wellFormed {a b : LocalTypeR} (hWFa : LocalTypeR.WellFormed a)
    (hWFb : LocalTypeR.WellFormed b) (h : EQ2 a b) : Bisim a b := by
  exact EQ2.toBisim_raw h hWFa hWFb

theorem EQ2.toBisim {a b : LocalTypeR} (h : EQ2 a b)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) : Bisim a b := by
  exact EQ2.toBisim_raw h hWFa hWFb
/-- Bisim is reflexive (general version using EQ2).

    For any type a, Bisim a a holds because EQ2 a a holds (EQ2 is reflexive),
    and EQ2 implies Bisim.

    This version doesn't require closed or contractive hypotheses, making it
    suitable for use with arbitrary types (including those with free variables). -/
theorem Bisim_refl (a : LocalTypeR) (hWF : LocalTypeR.WellFormed a) : Bisim a a :=
  EQ2.toBisim (EQ2_refl a) hWF hWF

namespace Bisim

/-- Observable types are reflexively bisimilar. -/
theorem refl_of_observable {a : LocalTypeR} (_hobs : Observable a) (hWF : LocalTypeR.WellFormed a) :
    Bisim a a :=
  Bisim_refl a hWF

/-- Bisim is reflexive for closed, contractive types. -/
theorem refl (a : LocalTypeR)
    (hclosed : a.isClosed := by decide)
    (hcontr : a.isContractive = true := by decide) : Bisim a a :=
  Bisim_refl a ⟨hclosed, hcontr⟩

end Bisim


/-! ## EQ2 Transitivity via Bisim

The Bisim detour provides an alternative proof of EQ2 transitivity that does not
require the TransRel_postfix lemma. This eliminates the need for one of the two
private detours in EQ2.lean. -/

/-- EQ2 transitivity via the Bisim detour.

    This theorem provides an alternative proof of EQ2_trans that does not require
    the TransRel_postfix lemma. The proof goes:
    1. Convert EQ2 proofs to Bisim using EQ2.toBisim
    2. Apply Bisim.trans (fully proven)
    3. Convert back to EQ2 using Bisim.toEQ2

    This theorem can replace the Bisim-based EQ2_trans in EQ2.lean once we
    resolve the circular import issue. -/
theorem EQ2_trans_via_Bisim {a b c : LocalTypeR}
    (hab : EQ2 a b) (hbc : EQ2 b c)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) : EQ2 a c := by
  have hBisim_ab := EQ2.toBisim hab hWFa hWFb
  have hBisim_bc := EQ2.toBisim hbc hWFb hWFc
  have hBisim_ac := Bisim.trans hBisim_ab hBisim_bc
  exact Bisim.toEQ2 hBisim_ac

/-- EQ2 transitivity via Bisim, for contractive types. -/
theorem EQ2_trans_via_Bisim_of_contractive {a b c : LocalTypeR}
    (hab : EQ2 a b) (hbc : EQ2 b c)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) : EQ2 a c := by
  exact EQ2_trans_via_Bisim hab hbc hWFa hWFb hWFc

/-! ## Observable Correspondence (WF-gated toEQ2) -/

/-- Build EQ2 from compatible observables (requires well-formedness). -/
theorem ObservableRel.toEQ2 {a b : LocalTypeR} {obs_a : Observable a} {obs_b : Observable b}
    (hrel : ObservableRel EQ2 obs_a obs_b)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) : EQ2 a b := by
  cases hrel with
  | is_end =>
      rename_i ha hb
      have ha_eq : EQ2 a .end := UnfoldsToEnd.toEQ2 ha
      have hb_eq : EQ2 b .end := UnfoldsToEnd.toEQ2 hb
      exact EQ2_trans_via_end ha_eq (EQ2_symm hb_eq)
  | is_var =>
      rename_i v ha hb
      have ha_eq : EQ2 a (.var v) := UnfoldsToVar.toEQ2 ha
      have hb_eq : EQ2 b (.var v) := UnfoldsToVar.toEQ2 hb
      exact EQ2_trans_via_var ha_eq (EQ2_symm hb_eq)
  | is_send hbr =>
      rename_i p bs cs ha hb
      have hWFbs := WellFormed_branches_of_CanSend ha hWFa
      have hWFcs := WellFormed_branches_of_CanSend hb hWFb
      have hWFsend_bs : LocalTypeR.WellFormed (.send p bs) :=
        LocalTypeR.WellFormed_send hWFbs
      have hWFsend_cs : LocalTypeR.WellFormed (.send p cs) :=
        LocalTypeR.WellFormed_send hWFcs
      have ha_eq : EQ2 a (.send p bs) := CanSend.toEQ2 ha
      have hb_eq : EQ2 b (.send p cs) := CanSend.toEQ2 hb
      have hsend_eq : EQ2 (.send p bs) (.send p cs) :=
        EQ2.construct (by exact ⟨rfl, hbr⟩)
      have h1 : EQ2 a (.send p cs) :=
        EQ2_trans_via_Bisim ha_eq hsend_eq hWFa hWFsend_bs hWFsend_cs
      exact EQ2_trans_via_Bisim h1 (EQ2_symm hb_eq) hWFa hWFsend_cs hWFb
  | is_recv hbr =>
      rename_i p bs cs ha hb
      have hWFbs := WellFormed_branches_of_CanRecv ha hWFa
      have hWFcs := WellFormed_branches_of_CanRecv hb hWFb
      have hWFrecv_bs : LocalTypeR.WellFormed (.recv p bs) :=
        LocalTypeR.WellFormed_recv hWFbs
      have hWFrecv_cs : LocalTypeR.WellFormed (.recv p cs) :=
        LocalTypeR.WellFormed_recv hWFcs
      have ha_eq : EQ2 a (.recv p bs) := CanRecvD.toEQ2 (CanRecv.to_CanRecvD ha)
      have hb_eq : EQ2 b (.recv p cs) := CanRecvD.toEQ2 (CanRecv.to_CanRecvD hb)
      have hrecv_eq : EQ2 (.recv p bs) (.recv p cs) :=
        EQ2.construct (by exact ⟨rfl, hbr⟩)
      have h1 : EQ2 a (.recv p cs) :=
        EQ2_trans_via_Bisim ha_eq hrecv_eq hWFa hWFrecv_bs hWFrecv_cs
      exact EQ2_trans_via_Bisim h1 (EQ2_symm hb_eq) hWFa hWFrecv_cs hWFb

/-- EQ2 equivalence iff observables correspond (WF-gated). -/
theorem EQ2_iff_observable_correspond {a b : LocalTypeR} (obs_a : Observable a)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) :
    EQ2 a b ↔ ∃ obs_b : Observable b, ObservableRel EQ2 obs_a obs_b := by
  constructor
  · intro h
    exact EQ2_transfer_observable h obs_a hWFb
  · intro h
    obtain ⟨obs_b, hrel⟩ := h
    exact ObservableRel.toEQ2 hrel hWFa hWFb

/-- Round-trip: extract then inject recovers EQ2 (by proof irrelevance). -/
theorem extract_inject_roundtrip {a b : LocalTypeR} (h : EQ2 a b) (obs_a : Observable a)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) :
    ObservableRel.toEQ2 (EQ2_transfer_observable h obs_a hWFb).2 hWFa hWFb = h :=
  Subsingleton.elim _ _

/-- Round-trip: inject then extract recovers the observable (by proof irrelevance). -/
theorem inject_extract_roundtrip {a b : LocalTypeR} {obs_a : Observable a} {obs_b : Observable b}
    (hrel : ObservableRel EQ2 obs_a obs_b)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) :
    EQ2_transfer_observable (ObservableRel.toEQ2 hrel hWFa hWFb) obs_a hWFb = ⟨obs_b, hrel⟩ :=
  Subsingleton.elim _ _

end RumpsteakV2.Protocol.CoTypes.Bisim
