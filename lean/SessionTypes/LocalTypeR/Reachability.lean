import SessionTypes.LocalTypeR.WellFormedness

/-! # SessionTypes.LocalTypeR.Reachability

Executable deadlock-automation checker for the regular practical fragment.
-/

set_option autoImplicit false

namespace SessionTypes.LocalTypeR

/-- Fully-unfolded local types that expose a communication head. -/
inductive ReachesCommunicationHead : LocalTypeR → Prop where
  | send {p : String} {bs : List BranchR} : bs ≠ [] → ReachesCommunicationHead (.send p bs)
  | recv {p : String} {bs : List BranchR} : bs ≠ [] → ReachesCommunicationHead (.recv p bs)

/-- Check whether a local type already exposes a communication head. -/
def reachesCommunicationHead : LocalTypeR → Bool
  | .send _ bs => !bs.isEmpty
  | .recv _ bs => !bs.isEmpty
  | _ => false

/-- Check whether a local type reaches a communication head after full unfolding. -/
def reachesCommunication (lt : LocalTypeR) : Bool :=
  reachesCommunicationHead lt.fullUnfold

/-- Mechanically characterized practical fragment for automatic `ReachesComm` discharge. -/
def regularPracticalFragment (lt : LocalTypeR) : Bool :=
  lt.isClosed && lt.isContractive && reachesCommunication lt

/-- Soundness witness for the regular practical fragment checker. -/
structure RegularPracticalWitness (lt : LocalTypeR) : Prop where
  wellFormed : LocalTypeR.WellFormed lt
  reachesCommunication : ReachesCommunicationHead lt.fullUnfold

/-- The head checker is sound. -/
theorem reaches_communication_head_sound {lt : LocalTypeR}
    (h : reachesCommunicationHead lt = true) : ReachesCommunicationHead lt := by
  cases lt with
  | «end» =>
      simp [reachesCommunicationHead] at h
  | var _ =>
      simp [reachesCommunicationHead] at h
  | mu _ _ =>
      simp [reachesCommunicationHead] at h
  | send p bs =>
      have hNonEmpty : bs ≠ [] := by
        intro hEmpty
        simp [reachesCommunicationHead, hEmpty] at h
      exact ReachesCommunicationHead.send (p := p) hNonEmpty
  | recv p bs =>
      have hNonEmpty : bs ≠ [] := by
        intro hEmpty
        simp [reachesCommunicationHead, hEmpty] at h
      exact ReachesCommunicationHead.recv (p := p) hNonEmpty

/-- The full-unfold communication checker is sound. -/
theorem reaches_communication_sound {lt : LocalTypeR}
    (h : reachesCommunication lt = true) : ReachesCommunicationHead lt.fullUnfold := by
  exact reaches_communication_head_sound (lt := lt.fullUnfold) h

/-- The regular practical fragment checker is sound. -/
theorem regular_practical_fragment_sound {lt : LocalTypeR}
    (h : regularPracticalFragment lt = true) : RegularPracticalWitness lt := by
  have hParts : (lt.isClosed = true ∧ lt.isContractive = true) ∧ reachesCommunication lt = true := by
    simpa [regularPracticalFragment, Bool.and_eq_true] using h
  refine ⟨?_, ?_⟩
  · refine ⟨?_, hParts.1.2⟩
    simpa [LocalTypeR.isClosed] using hParts.1.1
  · exact reaches_communication_sound hParts.2

end SessionTypes.LocalTypeR
