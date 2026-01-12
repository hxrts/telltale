import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.LocalTypeConv

/-! # RumpsteakV2.Protocol.LocalTypeRDBBridge

Bridge lemmas from de Bruijn proofs back to named-variable local types.
-/

namespace RumpsteakV2.Protocol.LocalTypeR

open RumpsteakV2.Protocol.LocalTypeConv

/-- Substituting a mu-expression preserves contractiveness.
    This specialized version requires a `Covers` witness for the bound variable. -/
theorem isContractive_substitute_mu (body : LocalTypeR) (t : String)
    (hcov : Context.Covers [t] body)
    (h_body : body.isContractive = true)
    (h_mu : (LocalTypeR.mu t body).isContractive = true) :
    (body.substitute t (LocalTypeR.mu t body)).isContractive = true := by
  simpa using
    RumpsteakV2.Protocol.LocalTypeConv.isContractive_substitute_mu_via_DB body t hcov h_body h_mu

/-- Substituting a mu-expression preserves contractiveness (for closed bodies).
    Derives the `Covers` witness from closedness. -/
theorem isContractive_substitute_mu_closed (body : LocalTypeR) (t : String)
    (hclosed : body.isClosed = true)
    (h_body : body.isContractive = true)
    (h_mu : (LocalTypeR.mu t body).isContractive = true) :
    (body.substitute t (LocalTypeR.mu t body)).isContractive = true := by
  apply isContractive_substitute_mu body t
  · exact Context.covers_of_closed_singleton t body hclosed
  · exact h_body
  · exact h_mu

/-- Substituting a mu-expression preserves contractiveness (for closed mu types).
    Derives the `Covers` witness from the mu type being closed. -/
theorem isContractive_substitute_mu_muClosed (body : LocalTypeR) (t : String)
    (hclosed : (LocalTypeR.mu t body).isClosed = true)
    (h_body : body.isContractive = true)
    (h_mu : (LocalTypeR.mu t body).isContractive = true) :
    (body.substitute t (LocalTypeR.mu t body)).isContractive = true := by
  apply isContractive_substitute_mu body t
  · exact Context.covers_of_mu_closed_singleton t body hclosed
  · exact h_body
  · exact h_mu

end RumpsteakV2.Protocol.LocalTypeR
