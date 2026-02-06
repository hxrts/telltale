import Protocol.Environments.Renaming

/-!
# Role Renaming (Session-Local)

Infrastructure for renaming roles inside a fixed session. This is used by the
delegation preservation proof: when role A delegates its endpoint to role B in
session s, all local types in session s must have A renamed to B, and endpoints
in session s are redirected from A to B.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Role Renaming Primitives -/

/-- Rename a role A to B, leaving all other roles unchanged. -/
def renameRole (A B : Role) (r : Role) : Role :=
  if r == A then B else r

/-- Rename roles inside value types, but only for endpoints in session s. -/
def renameValTypeRole (s : SessionId) (A B : Role) : ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod T₁ T₂ => .prod (renameValTypeRole s A B T₁) (renameValTypeRole s A B T₂)
  | .chan sid role =>
      if sid == s then
        .chan sid (renameRole A B role)
      else
        .chan sid role

mutual

/-- Rename roles inside a local type for session s (A → B). -/
def renameLocalTypeRole (s : SessionId) (A B : Role) : LocalType → LocalType
  | .send r T L => .send (renameRole A B r) (renameValTypeRole s A B T) (renameLocalTypeRole s A B L)
  | .recv r T L => .recv (renameRole A B r) (renameValTypeRole s A B T) (renameLocalTypeRole s A B L)
  | .select r bs => .select (renameRole A B r) (renameBranchesRole s A B bs)
  | .branch r bs => .branch (renameRole A B r) (renameBranchesRole s A B bs)
  | .end_ => .end_
  | .var n => .var n
  | .mu L => .mu (renameLocalTypeRole s A B L)
termination_by L => sizeOf L

/-- Rename roles inside branch lists for session s (A → B). -/
def renameBranchesRole (s : SessionId) (A B : Role) : List (Label × LocalType) → List (Label × LocalType)
  | [] => []
  | (l, L) :: bs => (l, renameLocalTypeRole s A B L) :: renameBranchesRole s A B bs
termination_by bs => sizeOf bs

end

/-! ## Endpoint and Edge Renaming (Session-Local) -/

/-- Rename a role in an endpoint, but only for session s. -/
def renameEndpointRole (s : SessionId) (A B : Role) (ep : Endpoint) : Endpoint :=
  if ep.sid == s then
    { sid := ep.sid, role := renameRole A B ep.role }
  else
    ep

/-- Rename roles in an edge, but only for session s. -/
def renameEdgeRole (s : SessionId) (A B : Role) (e : Edge) : Edge :=
  if e.sid == s then
    { sid := e.sid
      sender := renameRole A B e.sender
      receiver := renameRole A B e.receiver }
  else
    e

/-! ## Environment Renaming Helpers -/

/-- Rename all endpoints and their local types for session s. -/
def renameGEnvRole (s : SessionId) (A B : Role) (G : GEnv) : GEnv :=
  G.map fun (ep, L) => (renameEndpointRole s A B ep, renameLocalTypeRole s A B L)

