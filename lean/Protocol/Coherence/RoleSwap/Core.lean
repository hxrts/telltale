import Protocol.Coherence.EdgeCoherence
import Protocol.Environments.RoleRenaming

/-! # Protocol.Coherence.RoleSwap

Coherence lemmas and invariants for session-environment evolution.
-/


/-! # Role Swap Renaming (Session-Local)

Defines a bijective (swap) role renaming inside a fixed session and proves
that coherence is preserved under this renaming. This is the minimal
role-abstraction lemma: any finite role permutation can be built from swaps.
-/

/-
The Problem. Protocol composition may require roles to be renamed. We need to
show coherence is stable under role permutations, but general permutations are
complex. Swaps are simpler and compose to form any permutation.

Solution Structure. We prove:
1. `swapRole`: bijective swap of two roles A ↔ B
2. `swapRole_involutive`: swap is its own inverse
3. Lifting lemmas for endpoints, edges, value types
4. `swapCoherent`: coherence preserved under role swap
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Swap Renaming -/

/-- Swap two roles A and B, leaving all others unchanged. -/
def swapRole (A B : Role) (r : Role) : Role :=
  if r == A then B else if r == B then A else r

theorem swapRole_involutive (A B : Role) (r : Role) :
    swapRole A B (swapRole A B r) = r := by
  by_cases hA : r == A
  · have hA' : r = A := beq_iff_eq.1 hA
    simp [swapRole, hA']
  · have hA' : r ≠ A := by
      exact (beq_eq_false_iff_ne (a:=r) (b:=A)).1 (by simpa using hA)
    by_cases hB : r == B
    · have hB' : r = B := beq_iff_eq.1 hB
      simp [swapRole, hB']
    · have hB' : r ≠ B := by
        exact (beq_eq_false_iff_ne (a:=r) (b:=B)).1 (by simpa using hB)
      simp [swapRole, hA, hB]

/-- Swap roles inside value types (only for endpoints in session s). -/
def swapValTypeRole (s : SessionId) (A B : Role) : ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod T₁ T₂ => .prod (swapValTypeRole s A B T₁) (swapValTypeRole s A B T₂)
  | .chan sid role =>
      if sid == s then
        .chan sid (swapRole A B role)
      else
        .chan sid role

mutual

/-- Swap roles inside a local type for session s. -/
def swapLocalTypeRole (s : SessionId) (A B : Role) : LocalType → LocalType
  | .send r T L => .send (swapRole A B r) (swapValTypeRole s A B T) (swapLocalTypeRole s A B L)
  | .recv r T L => .recv (swapRole A B r) (swapValTypeRole s A B T) (swapLocalTypeRole s A B L)
  | .select r bs => .select (swapRole A B r) (swapBranchesRole s A B bs)
  | .branch r bs => .branch (swapRole A B r) (swapBranchesRole s A B bs)
  | .end_ => .end_
  | .var n => .var n
  | .mu L => .mu (swapLocalTypeRole s A B L)
termination_by L => sizeOf L

/-- Swap roles inside branch lists for session s. -/
def swapBranchesRole (s : SessionId) (A B : Role) : List (Label × LocalType) → List (Label × LocalType)
  | [] => []
  | (l, L) :: bs => (l, swapLocalTypeRole s A B L) :: swapBranchesRole s A B bs
termination_by bs => sizeOf bs

end

/-- Swap a role in an endpoint, but only for session s. -/
def swapEndpointRole (s : SessionId) (A B : Role) (ep : Endpoint) : Endpoint :=
  if ep.sid = s then
    { sid := ep.sid, role := swapRole A B ep.role }
  else
    ep

/-- Swap roles in an edge, but only for session s. -/
def swapEdgeRole (s : SessionId) (A B : Role) (e : Edge) : Edge :=
  if e.sid = s then
    { sid := e.sid
      sender := swapRole A B e.sender
      receiver := swapRole A B e.receiver }
  else
    e

theorem swapEndpointRole_sid (s : SessionId) (A B : Role) (ep : Endpoint) :
    (swapEndpointRole s A B ep).sid = ep.sid := by
  by_cases hSid : ep.sid = s
  · simp [swapEndpointRole, hSid]
  · simp [swapEndpointRole, hSid]

theorem swapEdgeRole_sid (s : SessionId) (A B : Role) (e : Edge) :
    (swapEdgeRole s A B e).sid = e.sid := by
  by_cases hSid : e.sid = s
  · simp [swapEdgeRole, hSid]
  · simp [swapEdgeRole, hSid]

theorem swapEndpointRole_involutive (s : SessionId) (A B : Role) (ep : Endpoint) :
    swapEndpointRole s A B (swapEndpointRole s A B ep) = ep := by
  cases ep with
  | mk sid role =>
      by_cases hSid : sid = s
      · simp [swapEndpointRole, hSid, swapRole_involutive]
      · simp [swapEndpointRole, hSid]

theorem swapEdgeRole_involutive (s : SessionId) (A B : Role) (e : Edge) :
    swapEdgeRole s A B (swapEdgeRole s A B e) = e := by
  cases e with
  | mk sid sender receiver =>
      by_cases hSid : sid = s
      · simp [swapEdgeRole, hSid, swapRole_involutive]
      · simp [swapEdgeRole, hSid]

theorem swapEndpointRole_inj (s : SessionId) (A B : Role) (e1 e2 : Endpoint) :
    swapEndpointRole s A B e1 = swapEndpointRole s A B e2 → e1 = e2 := by
  intro h
  have h' := congrArg (swapEndpointRole s A B) h
  simpa [swapEndpointRole_involutive] using h'

theorem swapEdgeRole_inj (s : SessionId) (A B : Role) (e1 e2 : Edge) :
    swapEdgeRole s A B e1 = swapEdgeRole s A B e2 → e1 = e2 := by
  intro h
  have h' := congrArg (swapEdgeRole s A B) h
  simpa [swapEdgeRole_involutive] using h'

/-- Swap all endpoints and their local types for session s. -/
def swapGEnvRole (s : SessionId) (A B : Role) (G : GEnv) : GEnv :=
  G.map fun (ep, L) =>
    if ep.sid = s then
      (swapEndpointRole s A B ep, swapLocalTypeRole s A B L)
    else
      (ep, L)

/-- Swap all edges and their traces for session s. -/
def swapDEnvRole (s : SessionId) (A B : Role) (D : DEnv) : DEnv :=
  D.list.foldl
    (fun acc p =>
      if p.1.sid = s then
        updateD acc (swapEdgeRole s A B p.1) (p.2.map (swapValTypeRole s A B))
      else
        updateD acc p.1 p.2)
    (∅ : DEnv)

/-! ## Lookup Lemmas -/

lemma lookupD_eq_list_lookup (D : DEnv) (e : Edge) :
    lookupD D e = match D.list.lookup e with
      | some ts => ts
      | none => [] := by
  have hfind := DEnv_find?_eq_lookup (env := D) (e := e)
  cases h : D.list.lookup e with
  | none =>
      simp [lookupD, hfind, h]
  | some ts =>
      simp [lookupD, hfind, h]

lemma lookupD_foldl_update_neq_swap (s : SessionId) (A B : Role) :
    ∀ (l : List (Edge × Trace)) (acc : DEnv) (edge : Edge),
      (∀ p ∈ l,
        (if p.1.sid = s then swapEdgeRole s A B p.1 else p.1) ≠ edge) →
      lookupD
          (l.foldl
            (fun acc p =>
              if p.1.sid = s then
                updateD acc (swapEdgeRole s A B p.1) (p.2.map (swapValTypeRole s A B))
              else
                updateD acc p.1 p.2)
            acc)
          edge = lookupD acc edge := by
  intro l acc edge hne
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
      have hne' : ∀ p ∈ tl,
          (if p.1.sid = s then swapEdgeRole s A B p.1 else p.1) ≠ edge := by
        intro p hp
        exact hne p (List.mem_cons.mpr (Or.inr hp))
      have hhd :
          (if hd.1.sid = s then swapEdgeRole s A B hd.1 else hd.1) ≠ edge :=
        hne hd (List.mem_cons.mpr (Or.inl rfl))
      by_cases hSid : hd.1.sid = s
      · have hneEdge : swapEdgeRole s A B hd.1 ≠ edge := by
          simpa [hSid] using hhd
        have ih' :=
          ih (acc:=updateD acc (swapEdgeRole s A B hd.1)
                (List.map (swapValTypeRole s A B) hd.2)) hne'
        have ih'' :
            lookupD
                (List.foldl
                  (fun acc p =>
                    if p.1.sid = s then
                      updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                    else
                      updateD acc p.1 p.2)
                  (updateD acc (swapEdgeRole s A B hd.1)
                    (List.map (swapValTypeRole s A B) hd.2))
                  tl)
                edge =
              lookupD
                (updateD acc (swapEdgeRole s A B hd.1)
                  (List.map (swapValTypeRole s A B) hd.2))
                edge := by
          simpa using ih'
        dsimp [List.foldl]
        simp [hSid]
        calc
          lookupD
              (List.foldl
                (fun acc p =>
                  if p.1.sid = s then
                    updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                  else
                    updateD acc p.1 p.2)
                (updateD acc (swapEdgeRole s A B hd.1)
                  (List.map (swapValTypeRole s A B) hd.2))
                tl)
              edge =
            lookupD
              (updateD acc (swapEdgeRole s A B hd.1)
                (List.map (swapValTypeRole s A B) hd.2))
              edge := ih''
          _ = lookupD acc edge :=
            lookupD_update_neq (env:=acc) (e:=swapEdgeRole s A B hd.1) (e':=edge)
              (ts:=hd.2.map (swapValTypeRole s A B)) hneEdge
      · have hneEdge : hd.1 ≠ edge := by
          simpa [hSid] using hhd
        have ih' := ih (acc:=updateD acc hd.1 hd.2) hne'
        have ih'' :
            lookupD
                (List.foldl
                  (fun acc p =>
                    if p.1.sid = s then
                      updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                    else
                      updateD acc p.1 p.2)
                  (updateD acc hd.1 hd.2) tl)
                edge =
              lookupD (updateD acc hd.1 hd.2) edge := by
          simpa using ih'
        dsimp [List.foldl]
        simp [hSid]
        calc
          lookupD
              (List.foldl
                (fun acc p =>
                  if p.1.sid = s then
                    updateD acc (swapEdgeRole s A B p.1) (List.map (swapValTypeRole s A B) p.2)
                  else
                    updateD acc p.1 p.2)
                (updateD acc hd.1 hd.2) tl)
              edge =
            lookupD (updateD acc hd.1 hd.2) edge := ih''
          _ = lookupD acc edge :=
            lookupD_update_neq (env:=acc) (e:=hd.1) (e':=edge) (ts:=hd.2) hneEdge

/-- Looking up a swapped endpoint in a swapped GEnv. -/
theorem lookupG_swap (s : SessionId) (A B : Role) (G : GEnv) (e : Endpoint) :
    lookupG (swapGEnvRole s A B G) (swapEndpointRole s A B e) =
      if e.sid = s then (lookupG G e).map (swapLocalTypeRole s A B) else lookupG G e := by
  induction G with
  | nil =>
      by_cases hSid : e.sid = s
      · simp [swapGEnvRole, lookupG, List.lookup, hSid]
      · simp [swapGEnvRole, lookupG, List.lookup, hSid, swapEndpointRole]
  | cons hd tl ih =>
      by_cases heq : e = hd.1
      · subst heq
        by_cases hSid : hd.1.sid = s
        · simp [swapGEnvRole, lookupG, List.lookup, hSid]
        · have hSidNe : hd.1.sid ≠ s := hSid
          have hSwap : swapEndpointRole s A B hd.1 = hd.1 := by
            simp [swapEndpointRole, hSid]
          simp [swapGEnvRole, lookupG, List.lookup, hSid, hSwap]
      · have hne :
          swapEndpointRole s A B e ≠
            (if hd.1.sid = s then swapEndpointRole s A B hd.1 else hd.1) := by
          by_cases hHdSid : hd.1.sid = s
          · intro hEq
            apply heq
            apply swapEndpointRole_inj s A B
            simpa [hHdSid] using hEq
          · have hHdSidNe : hd.1.sid ≠ s := hHdSid
            by_cases hSid : e.sid = s
            · intro hEq
              have hEq' : swapEndpointRole s A B e = hd.1 := by
                simpa [hHdSid, hHdSidNe] using hEq
              have hSidEq : (swapEndpointRole s A B e).sid = hd.1.sid :=
                congrArg Endpoint.sid hEq'
              have hSidL : (swapEndpointRole s A B e).sid = e.sid := by
                simpa using (swapEndpointRole_sid (s:=s) (A:=A) (B:=B) (ep:=e))
              have hSidEq' : e.sid = hd.1.sid := by simpa [hSidL] using hSidEq
              have hSidEq'' : hd.1.sid = s := by
                exact hSidEq'.symm.trans hSid
              exact (hHdSidNe hSidEq'').elim
            · intro hEq
              have hSidNe : e.sid ≠ s := hSid
              have hSwap : swapEndpointRole s A B e = e := by
                simp [swapEndpointRole, hSid]
              exact (heq (by simpa [hSwap, hHdSid] using hEq)).elim
        have hne1 :
            swapEndpointRole s A B e ≠
              (if hd.1.sid = s then
                  (swapEndpointRole s A B hd.1, swapLocalTypeRole s A B hd.2)
                else
                  hd).1 := by
          intro hEq
          apply hne
          by_cases hHdSid : hd.1.sid = s <;> simpa [hHdSid] using hEq
        have hbeq1 :
            (swapEndpointRole s A B e ==
              (if hd.1.sid = s then
                  (swapEndpointRole s A B hd.1, swapLocalTypeRole s A B hd.2)
                else
                  hd).1) = false :=
          beq_eq_false_iff_ne.mpr hne1
        have hbeq' : (e == hd.1) = false := beq_eq_false_iff_ne.mpr heq
        have ih' :
            List.lookup (swapEndpointRole s A B e)
                (List.map
                  (fun x =>
                    if x.1.sid = s then
                      (swapEndpointRole s A B x.1, swapLocalTypeRole s A B x.2)
                    else
                      x)
                  tl) =
              if e.sid = s then
                Option.map (swapLocalTypeRole s A B) (List.lookup e tl)
              else
                List.lookup e tl := by
          simpa [swapGEnvRole, lookupG] using ih
        simpa [swapGEnvRole, lookupG, List.lookup, hbeq1, hbeq'] using ih'

end
