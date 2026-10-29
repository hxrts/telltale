import Runtime.ProtocolMachine.Model.TypeClasses
import IrisExtractionInstance


/-! # Task 13: Session Resource Algebra

Ghost map for session endpoints.

## Definitions

- `SessionMap := GhostMap LocalType` (upstream `ExtTreeMap` keyed by `Pos`)
- `session_auth γ m` — authoritative session map
- `endpoint_frag γ e L` — per-endpoint fragment
- `frag_included`, `session_advance`, `endpoint_transfer`

Keys (Endpoint) are encoded to Positive via `encodeEndpoint`.

Dependencies: IrisExtraction boundary, GhostMapSlot LocalType instance.
-/

set_option autoImplicit false
section

open Iris.Std

/-! ## Endpoint Encoding -/

/-- Encode an Endpoint to a positive ghost-map key: encode the session id and
    role separately, then encode the two-element list of positives. -/
def encodeEndpoint (e : Endpoint) : Positive :=
  Pos.Countable.encode ([Pos.Countable.encode e.sid, Pos.Countable.encode e.role] : List Pos)

/-- Endpoint encoding is injective. -/
theorem encode_endpoint_inj : Function.Injective encodeEndpoint := by
  intro ⟨sid1, role1⟩ ⟨sid2, role2⟩ h
  have h' := Pos.encode_inj h
  simp only [List.cons.injEq, and_true] at h'
  simp only [Pos.encode_inj h'.1, Pos.encode_inj h'.2]

/-! ## Session Map Type -/

variable [ti : Telltale.TelltaleIris]
variable [slot : GhostMapSlot LocalType]

/-- Session map: ghost map from encoded endpoints to local types. -/
abbrev SessionMap := GhostMap LocalType

namespace GMap

/-- Lookup an endpoint's local type from a session ghost map. -/
def lookup (m : SessionMap) (e : Endpoint) : Option LocalType :=
  Iris.Std.get? m (encodeEndpoint e)

end GMap

/-! ## Ghost State Propositions -/

/-- Authoritative ownership of the session map. -/
def session_auth (γ : GhostName) (m : SessionMap) : iProp :=
  ghost_map_auth γ m

/-- Fragment ownership of a single endpoint's local type. -/
def endpoint_frag (γ : GhostName) (e : Endpoint) (L : LocalType) : iProp :=
  ghost_map_elem γ (encodeEndpoint e) L

/-! ## Ghost State Lemmas -/

/-- Lookup: auth + fragment implies the endpoint maps to the local type. -/
def frag_included (γ : GhostName) (m : SessionMap) (e : Endpoint) (L : LocalType) :
    iProp.entails (iProp.sep (session_auth γ m) (endpoint_frag γ e L))
      (iProp.pure (get? m (encodeEndpoint e) = some L)) :=
  ghost_map_lookup γ (encodeEndpoint e) L m

/-- Update: advance an endpoint's local type. -/
def session_advance (γ : GhostName) (m : SessionMap)
    (e : Endpoint) (L L' : LocalType) :
    iProp.entails (iProp.sep (session_auth γ m) (endpoint_frag γ e L))
      (bupd (iProp.sep
        (session_auth γ (insert m (encodeEndpoint e) L'))
        (endpoint_frag γ e L'))) :=
  ghost_map_update γ (encodeEndpoint e) L L' m

/-- Delegation transfer as Iris ghost-map update.
    This is the cross-layer ownership step used by delegation:
    the receiver endpoint fragment changes from `Lold` to `Lnew` by
    a single `ghost_map_update` on the authoritative session map. -/
def delegation_ghost_map_update (γ : GhostName) (m : SessionMap)
    (receiverEp : Endpoint) (Lold Lnew : LocalType) :
    iProp.entails
      (iProp.sep (session_auth γ m) (endpoint_frag γ receiverEp Lold))
      (bupd (iProp.sep
        (session_auth γ (insert m (encodeEndpoint receiverEp) Lnew))
        (endpoint_frag γ receiverEp Lnew))) :=
  session_advance γ m receiverEp Lold Lnew

end
