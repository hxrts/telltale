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

section

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

/-! ## Commutation with Session Renaming -/

/-- Session renaming commutes with role renaming on value types.
    The key insight is that session renaming changes session IDs while
    role renaming changes roles within a fixed session - these are orthogonal. -/
theorem renameValType_renameValTypeRole_comm (ρ : SessionRenaming) (s : SessionId) (A B : Role) (T : ValType) :
    renameValType ρ (renameValTypeRole s A B T) = renameValTypeRole (ρ.f s) A B (renameValType ρ T) := by
  induction T with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | string => rfl
  | prod T₁ T₂ ih₁ ih₂ =>
    simp only [renameValType, renameValTypeRole, ih₁, ih₂]
  | chan sid role =>
    -- Session ID equality determines which branch is taken
    -- Since ρ is injective, sid = s ↔ ρ.f sid = ρ.f s
    simp only [renameValType, renameValTypeRole]
    by_cases h : sid = s
    · -- sid = s case: both conditions true
      simp only [beq_iff_eq, h, ↓reduceIte, renameValType]
    · -- sid ≠ s case: both conditions false (by injectivity)
      have hρne : ρ.f sid ≠ ρ.f s := fun heq => h (ρ.inj sid s heq)
      simp only [beq_iff_eq, h, ↓reduceIte, hρne, renameValType]

/-- Size lemma for branch list elements. -/
private theorem sizeOf_lt_branch (l : Label) (L : LocalType) (tl : List (Label × LocalType)) :
    sizeOf L < sizeOf ((l, L) :: tl) ∧ sizeOf tl < sizeOf ((l, L) :: tl) := by
  simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
  constructor <;> omega

mutual

/-- Session renaming commutes with role renaming on local types. -/
theorem renameLocalType_renameLocalTypeRole_comm (ρ : SessionRenaming) (s : SessionId) (A B : Role) (L : LocalType) :
    renameLocalType ρ (renameLocalTypeRole s A B L) =
      renameLocalTypeRole (ρ.f s) A B (renameLocalType ρ L) := by
  cases L with
  | send r T L =>
    simp only [renameLocalType, renameLocalTypeRole]
    congr 1
    · exact renameValType_renameValTypeRole_comm ρ s A B T
    · exact renameLocalType_renameLocalTypeRole_comm ρ s A B L
  | recv r T L =>
    simp only [renameLocalType, renameLocalTypeRole]
    congr 1
    · exact renameValType_renameValTypeRole_comm ρ s A B T
    · exact renameLocalType_renameLocalTypeRole_comm ρ s A B L
  | select r bs =>
    simp only [renameLocalType, renameLocalTypeRole]
    congr 1
    exact renameBranches_renameBranchesRole_comm ρ s A B bs
  | branch r bs =>
    simp only [renameLocalType, renameLocalTypeRole]
    congr 1
    exact renameBranches_renameBranchesRole_comm ρ s A B bs
  | end_ =>
    simp [renameLocalType, renameLocalTypeRole]
  | var n =>
    simp [renameLocalType, renameLocalTypeRole]
  | mu L =>
    simp only [renameLocalType, renameLocalTypeRole]
    congr 1
    exact renameLocalType_renameLocalTypeRole_comm ρ s A B L
termination_by sizeOf L

/-- Session renaming commutes with role renaming on branches. -/
theorem renameBranches_renameBranchesRole_comm (ρ : SessionRenaming) (s : SessionId) (A B : Role) (bs : List (Label × LocalType)) :
    renameBranches ρ (renameBranchesRole s A B bs) =
      renameBranchesRole (ρ.f s) A B (renameBranches ρ bs) := by
  cases bs with
  | nil =>
    simp [renameBranches, renameBranchesRole]
  | cons hd tl =>
    cases hd with
    | mk l L =>
      simp only [renameBranches, renameBranchesRole]
      congr 1
      · congr 1
        exact renameLocalType_renameLocalTypeRole_comm ρ s A B L
      · exact renameBranches_renameBranchesRole_comm ρ s A B tl
termination_by sizeOf bs

end

/-- Session renaming commutes with role renaming on endpoints. -/
theorem renameEndpoint_renameEndpointRole_comm (ρ : SessionRenaming) (s : SessionId) (A B : Role) (ep : Endpoint) :
    renameEndpoint ρ (renameEndpointRole s A B ep) = renameEndpointRole (ρ.f s) A B (renameEndpoint ρ ep) := by
  simp only [renameEndpoint, renameEndpointRole]
  by_cases h : ep.sid = s
  · -- ep.sid = s case: both ifs are true
    simp only [beq_iff_eq, h, ↓reduceIte]
  · -- ep.sid ≠ s case: both ifs are false (by injectivity)
    have hρne : ρ.f ep.sid ≠ ρ.f s := fun heq => h (ρ.inj ep.sid s heq)
    simp only [beq_iff_eq, h, ↓reduceIte, hρne]

/-- Session renaming commutes with role renaming on edges. -/
theorem renameEdge_renameEdgeRole_comm (ρ : SessionRenaming) (s : SessionId) (A B : Role) (e : Edge) :
    renameEdge ρ (renameEdgeRole s A B e) = renameEdgeRole (ρ.f s) A B (renameEdge ρ e) := by
  simp only [renameEdge, renameEdgeRole]
  by_cases h : e.sid = s
  · -- e.sid = s case: both ifs are true
    simp only [beq_iff_eq, h, ↓reduceIte]
  · -- e.sid ≠ s case: both ifs are false (by injectivity)
    have hρne : ρ.f e.sid ≠ ρ.f s := fun heq => h (ρ.inj e.sid s heq)
    simp only [beq_iff_eq, h, ↓reduceIte, hρne]

