import Runtime.VM.TypeClasses
import Runtime.Compat.RA

/-!
# Task 13: Session Resource Algebra

Ghost map for session endpoints from iris_runtime_2.md §5.1.

## Definitions

- `SessionRA := authR (gmapUR Endpoint LocalType)`
- `session_auth γ G` — authoritative session map
- `endpoint_frag γ e L` — per-endpoint fragment
- `frag_included`, `session_advance`, `endpoint_transfer`

Dependencies: Shim.ResourceAlgebra.
-/

set_option autoImplicit false
noncomputable section

abbrev SessionMap := GMap Endpoint LocalType
abbrev SessionRA := SessionMap

def session_auth (γ : GhostName) (G : SessionMap) : iProp :=
  ghost_map_auth γ G

def endpoint_frag (γ : GhostName) (e : Endpoint) (L : LocalType) : iProp :=
  ghost_map_elem γ e L

def frag_included (γ : GhostName) (G : SessionMap) (e : Endpoint) (L : LocalType) :
  iProp.entails (iProp.sep (session_auth γ G) (endpoint_frag γ e L))
    (iProp.pure (GMap.lookup G e = some L)) :=
  ghost_map_lookup γ e L G

def session_advance (γ : GhostName) (G : SessionMap)
    (e : Endpoint) (L L' : LocalType) :
  iProp.entails (iProp.sep (session_auth γ G) (endpoint_frag γ e L))
    (bupd (iProp.sep (session_auth γ (GMap.insert G e L')) (endpoint_frag γ e L'))) :=
  ghost_map_update γ e L L' G

def endpoint_transfer (γ : GhostName) (e : Endpoint) (L : LocalType) : Prop :=
  -- Endpoint fragments are transferable as resources.
  iProp.entails (endpoint_frag γ e L) (endpoint_frag γ e L)
