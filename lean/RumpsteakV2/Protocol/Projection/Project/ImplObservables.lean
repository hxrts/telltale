import RumpsteakV2.Protocol.Projection.Project.ImplHeadPreservation

set_option linter.unnecessarySimpa false

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props
open RumpsteakV2.Protocol.CoTypes.EQ2Paco
open Paco
open RumpsteakV2.Protocol.Participation

/-! ## Observable Preservation Lemmas for CProjectTransRelComp

CProjectTransRelComp preserves observable structure: types with incompatible
head constructors cannot be related. This is because:
1. CProject preserves head constructor (modulo mu-unfolding)
2. trans preserves head constructor (modulo mu-unfolding)
3. EQ2 preserves observable behavior (equi-recursive equivalence)

The composition of these relations cannot relate `.end` to `.var`, etc.
These lemmas are semantically sound because CProject and trans compute
the same observable behavior (just with different representation).
-/

/-- End cannot be CProjectTransRelComp-related to var. -/
theorem CProjectTransRelComp_end_not_var
    {v : String} (h : CProjectTransRelComp .end (.var v))
    (hWFa : LocalTypeR.WellFormed .end) (hWFc : LocalTypeR.WellFormed (.var v)) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_end (b := .var v) hbase)

  · cases b with
    | «end» =>
        cases (CProjectTransRel_source_end (b := .var v) hrel)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .var v) hrel with ⟨body', hEq⟩
        cases hEq
  · have hb : b = .end := CProjectTransRel_source_end hrel
    subst hb
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .end) (c := .var v) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- End cannot be CProjectTransRelComp-related to send. -/
theorem CProjectTransRelComp_end_not_send
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp .end (.send p bs))
    (hWFa : LocalTypeR.WellFormed .end) (hWFc : LocalTypeR.WellFormed (.send p bs)) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_end (b := .send p bs) hbase)
  · cases b with
    | «end» =>
        cases (CProjectTransRel_source_end (b := .send p bs) hrel)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .send p bs) hrel with ⟨body', hEq⟩
        cases hEq
  · have hb : b = .end := CProjectTransRel_source_end hrel
    subst hb
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .end) (c := .send p bs) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- End cannot be CProjectTransRelComp-related to recv. -/
theorem CProjectTransRelComp_end_not_recv
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp .end (.recv p bs))
    (hWFa : LocalTypeR.WellFormed .end) (hWFc : LocalTypeR.WellFormed (.recv p bs)) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_end (b := .recv p bs) hbase)
  · cases b with
    | «end» =>
        cases (CProjectTransRel_source_end (b := .recv p bs) hrel)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .recv p bs) hrel with ⟨body', hEq⟩
        cases hEq
  · have hb : b = .end := CProjectTransRel_source_end hrel
    subst hb
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .end) (c := .recv p bs) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Var cannot be CProjectTransRelComp-related to end. -/
theorem CProjectTransRelComp_var_not_end
    {v : String} (h : CProjectTransRelComp (.var v) .end)
    (hWFa : LocalTypeR.WellFormed (.var v)) (hWFc : LocalTypeR.WellFormed .end) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_var (v := v) (b := .end) hbase)
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var v' =>
        cases (CProjectTransRel_source_var (v := v') (b := .end) hrel)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .end) hrel with ⟨body', hEq⟩
        cases hEq
  · have hb : b = .var v := CProjectTransRel_source_var (v := v) hrel
    subst hb
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .var v) (c := .end) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Var cannot be CProjectTransRelComp-related to send. -/
theorem CProjectTransRelComp_var_not_send
    {v : String} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp (.var v) (.send p bs))
    (hWFa : LocalTypeR.WellFormed (.var v)) (hWFc : LocalTypeR.WellFormed (.send p bs)) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_var (v := v) (b := .send p bs) hbase)
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var v' =>
        cases (CProjectTransRel_source_var (v := v') (b := .send p bs) hrel)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .send p bs) hrel with ⟨body', hEq⟩
        cases hEq
  · have hb : b = .var v := CProjectTransRel_source_var (v := v) hrel
    subst hb
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .var v) (c := .send p bs) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Var cannot be CProjectTransRelComp-related to recv. -/
theorem CProjectTransRelComp_var_not_recv
    {v : String} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp (.var v) (.recv p bs))
    (hWFa : LocalTypeR.WellFormed (.var v)) (hWFc : LocalTypeR.WellFormed (.recv p bs)) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_var (v := v) (b := .recv p bs) hbase)
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var v' =>
        cases (CProjectTransRel_source_var (v := v') (b := .recv p bs) hrel)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .recv p bs) hrel with ⟨body', hEq⟩
        cases hEq
  · have hb : b = .var v := CProjectTransRel_source_var (v := v) hrel
    subst hb
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .var v) (c := .recv p bs) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Send cannot be CProjectTransRelComp-related to end. -/
theorem CProjectTransRelComp_send_not_end
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp (.send p bs) .end)
    (hWFa : LocalTypeR.WellFormed (.send p bs)) (hWFc : LocalTypeR.WellFormed .end) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_send (p := p) (bs := bs) (b := .end) hbase) with
    | intro cs hEq => cases hEq
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send p' bs' =>
        cases (CProjectTransRel_source_send (p := p') (bs := bs') (b := .end) hrel) with
        | intro cs hEq => cases hEq
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .end) hrel with ⟨body', hEq⟩
        cases hEq
  · rcases CProjectTransRel_source_send (p := p) (bs := bs) hrel with ⟨cs, hEq⟩
    cases hEq
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .send p bs) (c := .end) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Send cannot be CProjectTransRelComp-related to var. -/
theorem CProjectTransRelComp_send_not_var
    {p : String} {bs : List (Label × LocalTypeR)} {v : String}
    (h : CProjectTransRelComp (.send p bs) (.var v))
    (hWFa : LocalTypeR.WellFormed (.send p bs)) (hWFc : LocalTypeR.WellFormed (.var v)) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_send (p := p) (bs := bs) (b := .var v) hbase) with
    | intro cs hEq => cases hEq
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send p' bs' =>
        cases (CProjectTransRel_source_send (p := p') (bs := bs') (b := .var v) hrel) with
        | intro cs hEq => cases hEq
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .var v) hrel with ⟨body', hEq⟩
        cases hEq
  · rcases CProjectTransRel_source_send (p := p) (bs := bs) hrel with ⟨cs, hEq⟩
    cases hEq
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .send p bs) (c := .var v) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Send cannot be CProjectTransRelComp-related to recv. -/
theorem CProjectTransRelComp_send_not_recv
    {p1 : String} {bs1 : List (Label × LocalTypeR)}
    {p2 : String} {bs2 : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp (.send p1 bs1) (.recv p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.send p1 bs1)) (hWFc : LocalTypeR.WellFormed (.recv p2 bs2)) :
    False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_send (p := p1) (bs := bs1) (b := .recv p2 bs2) hbase) with
    | intro cs hEq => cases hEq
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send p' bs' =>
        cases (CProjectTransRel_source_send (p := p') (bs := bs') (b := .recv p2 bs2) hrel) with
        | intro cs hEq => cases hEq
    | recv _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .recv p2 bs2) hrel with ⟨body', hEq⟩
        cases hEq
  · rcases CProjectTransRel_source_send (p := p1) (bs := bs1) hrel with ⟨cs, hEq⟩
    cases hEq
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .send p1 bs1) (c := .recv p2 bs2) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Recv cannot be CProjectTransRelComp-related to end. -/
theorem CProjectTransRelComp_recv_not_end
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp (.recv p bs) .end)
    (hWFa : LocalTypeR.WellFormed (.recv p bs)) (hWFc : LocalTypeR.WellFormed .end) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_recv (p := p) (bs := bs) (b := .end) hbase) with
    | intro cs hEq => cases hEq
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv p' bs' =>
        cases (CProjectTransRel_source_recv (p := p') (bs := bs') (b := .end) hrel) with
        | intro cs hEq => cases hEq
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .end) hrel with ⟨body', hEq⟩
        cases hEq
  · rcases CProjectTransRel_source_recv (p := p) (bs := bs) hrel with ⟨cs, hEq⟩
    cases hEq
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .recv p bs) (c := .end) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Recv cannot be CProjectTransRelComp-related to var. -/
theorem CProjectTransRelComp_recv_not_var
    {p : String} {bs : List (Label × LocalTypeR)} {v : String}
    (h : CProjectTransRelComp (.recv p bs) (.var v))
    (hWFa : LocalTypeR.WellFormed (.recv p bs)) (hWFc : LocalTypeR.WellFormed (.var v)) : False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_recv (p := p) (bs := bs) (b := .var v) hbase) with
    | intro cs hEq => cases hEq
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv p' bs' =>
        cases (CProjectTransRel_source_recv (p := p') (bs := bs') (b := .var v) hrel) with
        | intro cs hEq => cases hEq
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .var v) hrel with ⟨body', hEq⟩
        cases hEq
  · rcases CProjectTransRel_source_recv (p := p) (bs := bs) hrel with ⟨cs, hEq⟩
    cases hEq
    simpa [EQ2F] using (EQ2.destruct heq)
  · have hcomp := EQ2_CProjectTransRel_EQ2_compose (a := .recv p bs) (c := .var v) heq hrel heq'
      hWFa hWFc
    simpa [EQ2F] using hcomp

/-- Recv cannot be CProjectTransRelComp-related to send. -/
theorem CProjectTransRelComp_recv_not_send
    {p1 : String} {bs1 : List (Label × LocalTypeR)}
    {p2 : String} {bs2 : List (Label × LocalTypeR)}
    (h : CProjectTransRelComp (.recv p1 bs1) (.send p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.recv p1 bs1)) (hWFc : LocalTypeR.WellFormed (.send p2 bs2)) :
    False := by
  rcases h with hbase | ⟨b, heq, hrel⟩ | ⟨b, hrel, heq⟩ | ⟨b, b', heq, hrel, heq'⟩
  · cases (CProjectTransRel_source_recv (p := p1) (bs := bs1) (b := .send p2 bs2) hbase) with
    | intro cs hEq => cases hEq
  · cases b with
    | «end» =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | var _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | send _ _ =>
        simpa [EQ2F] using (EQ2.destruct heq)
    | recv p' bs' =>
        cases (CProjectTransRel_source_recv (p := p') (bs := bs') (b := .send p2 bs2) hrel) with
        | intro cs hEq => cases hEq
    | mu t body =>
        rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .send p2 bs2) hrel with ⟨body', hEq⟩
        cases hEq
  · rcases CProjectTransRel_source_recv (p := p1) (bs := bs1) hrel with ⟨cs, hEq⟩;
      cases hEq; simpa [EQ2F] using (EQ2.destruct heq)
  · simpa [EQ2F] using
      (EQ2_CProjectTransRel_EQ2_compose (a := .recv p1 bs1) (c := .send p2 bs2) heq hrel heq'
        hWFa hWFc)


end RumpsteakV2.Protocol.Projection.Project
