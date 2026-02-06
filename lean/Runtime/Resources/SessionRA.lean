import Runtime.VM.TypeClasses
import Runtime.Compat.RA

/-!
# Task 13: Session Resource Algebra

Ghost map for session endpoints from iris_runtime_2.md §5.1.

## Definitions

- `SessionMap := GhostMap LocalType` (iris-lean's finite map with Positive keys)
- `session_auth γ m` — authoritative session map
- `endpoint_frag γ e L` — per-endpoint fragment
- `frag_included`, `session_advance`, `endpoint_transfer`

Keys (Endpoint) are encoded to Positive via `encodeEndpoint`.

Dependencies: IrisBridge, GhostMapSlot LocalType instance.
-/

set_option autoImplicit false
noncomputable section

open Iris.Std

/-! ## Endpoint Encoding -/

/-- Encode an Endpoint to Positive for use as ghost map key.
    Uses Iris's Countable encoding for Nat (SessionId) and String (Role). -/
def encodeEndpoint (e : Endpoint) : Positive :=
  [Iris.Countable.encode e.sid, Iris.Countable.encode e.role]

/-- Decode is left inverse of encode. -/
theorem encodeEndpoint_inj : Function.Injective encodeEndpoint := by
  intro ⟨sid1, role1⟩ ⟨sid2, role2⟩ h
  simp only [encodeEndpoint, List.cons.injEq, and_true] at h
  simp only [Iris.Countable.encode_inj h.1, Iris.Countable.encode_inj h.2, and_self]

/-! ## Session Map Type -/

variable [ti : Telltale.TelltaleIris]
variable [slot : GhostMapSlot LocalType]

/-- Session map: ghost map from encoded endpoints to local types. -/
abbrev SessionMap := GhostMap LocalType

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
      (iProp.pure (get? m (encodeEndpoint e) = some (Iris.LeibnizO.mk L))) :=
  ghost_map_lookup γ (encodeEndpoint e) L m

/-- Update: advance an endpoint's local type. -/
def session_advance (γ : GhostName) (m : SessionMap)
    (e : Endpoint) (L L' : LocalType) :
    iProp.entails (iProp.sep (session_auth γ m) (endpoint_frag γ e L))
      (bupd (iProp.sep
        (session_auth γ (insert m (encodeEndpoint e) (Iris.LeibnizO.mk L')))
        (endpoint_frag γ e L'))) :=
  ghost_map_update γ (encodeEndpoint e) L L' m

/-- Endpoint fragments are transferable (trivially). -/
def endpoint_transfer (γ : GhostName) (e : Endpoint) (L : LocalType) : Prop :=
  iProp.entails (endpoint_frag γ e L) (endpoint_frag γ e L)

end
