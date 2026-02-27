import SessionTypes.LocalTypeConvDefs

set_option autoImplicit false

/-! # SessionTypes.LocalTypeConvProofs.PayloadParityBridge

Bridge theorems between payload-preserving and erased de Bruijn conversions.
-/

namespace SessionTypes.LocalTypeConvProofs

open SessionTypes
open SessionTypes.LocalTypeR
open SessionTypes.LocalTypeConv

/-! ## Conversion Success Parity -/

mutual
  /-- `toDBAnn?` succeeds exactly when legacy `toDB?` succeeds. -/
  theorem to_db_ann_is_some_eq_to_db_is_some (ctx : Context) :
      (t : LocalTypeR) →
      (LocalTypeR.toDBAnn? ctx t).isSome = (LocalTypeR.toDB? ctx t).isSome
    | .end => by
        simp [LocalTypeR.toDBAnn?, LocalTypeR.toDB?]
    | .var v => by
        simp [LocalTypeR.toDBAnn?, LocalTypeR.toDB?]
    | .mu v body => by
        simpa [LocalTypeR.toDBAnn?, LocalTypeR.toDB?] using
          to_db_ann_is_some_eq_to_db_is_some (SessionTypes.NameOnlyContext.cons v ctx) body
    | .send p bs => by
        simpa [LocalTypeR.toDBAnn?, LocalTypeR.toDB?] using
          branches_to_db_ann_is_some_eq_branches_to_db_is_some ctx bs
    | .recv p bs => by
        simpa [LocalTypeR.toDBAnn?, LocalTypeR.toDB?] using
          branches_to_db_ann_is_some_eq_branches_to_db_is_some ctx bs

  /-- Branch conversion success is preserved between payload and erased conversions. -/
  theorem branches_to_db_ann_is_some_eq_branches_to_db_is_some (ctx : Context) :
      (bs : List BranchR) →
      (LocalTypeR.branchesToDBAnn? ctx bs).isSome = (LocalTypeR.branchesToDB? ctx bs).isSome
    | [] => by
        simp [LocalTypeR.branchesToDBAnn?, LocalTypeR.branchesToDB?]
    | (lbl, vt, cont) :: rest => by
        have hCont := to_db_ann_is_some_eq_to_db_is_some ctx cont
        have hRest := branches_to_db_ann_is_some_eq_branches_to_db_is_some ctx rest
        cases hContAnn : LocalTypeR.toDBAnn? ctx cont <;>
          cases hRestAnn : LocalTypeR.branchesToDBAnn? ctx rest <;>
            cases hContDb : LocalTypeR.toDB? ctx cont <;>
              cases hRestDb : LocalTypeR.branchesToDB? ctx rest <;>
                simp [LocalTypeR.branchesToDBAnn?, LocalTypeR.branchesToDB?,
                  hContAnn, hRestAnn, hContDb, hRestDb] at hCont hRest ⊢
end

/-! ## Existence Bridge -/

/-- Any successful legacy `toDB?` conversion lifts to a payload-preserving conversion. -/
theorem to_db_lifts_to_db_ann
    {ctx : Context} {t : LocalTypeR} {db : SessionTypes.LocalTypeDB}
    (h : LocalTypeR.toDB? ctx t = some db) :
    ∃ dbAnn, LocalTypeR.toDBAnn? ctx t = some dbAnn := by
  have hSomeDb : (LocalTypeR.toDB? ctx t).isSome = true := by
    simp [h]
  have hSomeAnn : (LocalTypeR.toDBAnn? ctx t).isSome = true := by
    simpa [to_db_ann_is_some_eq_to_db_is_some ctx t] using hSomeDb
  cases hAnn : LocalTypeR.toDBAnn? ctx t with
  | none =>
      simp [hAnn] at hSomeAnn
  | some dbAnn =>
      exact ⟨dbAnn, rfl⟩

end SessionTypes.LocalTypeConvProofs
