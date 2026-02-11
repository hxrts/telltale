import Protocol.BufferBoundedness.PhaseSharpness

/-! # Protocol.BufferBoundedness.DepthBounds

Depth and environment-size bounds along reachable executions.
-/

/-
The Problem. To compute usable buffer bounds, we need quantitative depth and
environment-size invariants along executions.

Solution Structure. Proves depth/GEnv bounds along steps and reachability.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Depth Bounds Along Steps -/

/-- Any local type depth is bounded by totalTypeDepthG. -/
theorem depth_le_totalTypeDepthG_of_mem {G : GEnv} {ep : Endpoint} {L : LocalType}
    (hmem : (ep, L) ∈ G) : L.depth ≤ totalTypeDepthG G := by
  induction G with
  | nil => cases hmem
  | cons hd tl ih =>
      cases hd with
      | mk ep' L' =>
          rcases List.mem_cons.mp hmem with hEq | hTail
          · cases hEq
            -- L'.depth ≤ L'.depth + totalTypeDepthG tl
            simp [totalTypeDepthG_cons]
          · have hle : L.depth ≤ totalTypeDepthG tl := ih hTail
            have hle' : totalTypeDepthG tl ≤ L'.depth + totalTypeDepthG tl :=
              Nat.le_add_left _ _
            exact le_trans hle (by simpa [totalTypeDepthG_cons] using hle')

/-- Any local type depth is bounded by totalTypeDepth. -/
theorem depth_le_totalTypeDepth_of_mem (C : Config) {ep : Endpoint} {L : LocalType}
    (hmem : (ep, L) ∈ C.G) : L.depth ≤ totalTypeDepth C := by
  simpa [totalTypeDepth] using depth_le_totalTypeDepthG_of_mem (G:=C.G) hmem

/-- Updating a known endpoint with a shallower type does not increase total depth. -/
theorem totalTypeDepthG_updateG_le {G : GEnv} {e : Endpoint}
    {Lold Lnew : LocalType}
    (hLookup : lookupG G e = some Lold)
    (hLe : Lnew.depth ≤ Lold.depth) :
    totalTypeDepthG (updateG G e Lnew) ≤ totalTypeDepthG G := by
  -- Induct on G to align updateG with the head position.
  induction G generalizing e Lold Lnew with
  | nil => cases hLookup
  | cons hd tl ih =>
      cases hd with
      | mk ep L =>
          by_cases hEq : e = ep
          · -- Update hits the head; depth decreases at that position.
            have hOld : L = Lold := by
              simpa [lookupG, List.lookup, hEq] using hLookup
            cases hOld
            simp [totalTypeDepthG_cons, updateG, hEq, hLe]
          · -- Update recurses on the tail; head depth unchanged.
            have hLookup' : lookupG tl e = some Lold := by
              have hEq' : (e == ep) = false := beq_eq_false_iff_ne.mpr hEq
              simpa [lookupG, List.lookup, hEq'] using hLookup
            have hTail : totalTypeDepthG (updateG tl e Lnew) ≤ totalTypeDepthG tl :=
              ih (e:=e) (Lold:=Lold) (Lnew:=Lnew) hLookup' hLe
            simp [totalTypeDepthG_cons, updateG, hEq, hTail]

/-- Send steps reduce totalTypeDepth (depth strictly decreases at sender). -/
theorem totalTypeDepth_send_le {C : Config} {e : Endpoint} {target : Role}
    {T : ValType} {L : LocalType} {v : Value}
    (hG : lookupG C.G e = some (.send target T L)) :
    totalTypeDepth (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) ≤
      totalTypeDepth C := by
  -- Use depth_advance_send for the updated endpoint.
  have hLt := LocalType.depth_advance_send target T L
  have hLe : L.depth ≤ (LocalType.send target T L).depth := Nat.le_of_lt hLt
  simpa [totalTypeDepth, totalTypeDepthG, sendStep] using
    totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.send target T L) (Lnew:=L) hG hLe

/-- Recv steps reduce totalTypeDepth (depth strictly decreases at receiver). -/
theorem totalTypeDepth_recv_le {C : Config} {e : Endpoint} {source : Role}
    {T : ValType} {L : LocalType} {x : Var} {v : Value}
    (hG : lookupG C.G e = some (.recv source T L)) :
    totalTypeDepth (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) ≤
      totalTypeDepth C := by
  -- recvStep may return C when dequeue fails; split on the buffer case.
  cases hDeq : dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } with
  | none =>
      -- No change to G, so totalTypeDepth is unchanged.
      simp [recvStep, hDeq, totalTypeDepth, totalTypeDepthG]
  | some p =>
      -- Successful dequeue updates G to the continuation, reducing depth.
      have hLt := LocalType.depth_advance_recv source T L
      have hLe : L.depth ≤ (LocalType.recv source T L).depth := Nat.le_of_lt hLt
      simpa [recvStep, hDeq, totalTypeDepth, totalTypeDepthG] using
        totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.recv source T L) (Lnew:=L) hG hLe

/-- Select steps reduce totalTypeDepth (depth decreases to chosen branch). -/
theorem totalTypeDepth_select_le {C : Config} {e : Endpoint} {target : Role}
    {branches : List (Label × LocalType)} {ℓ : Label} {L : LocalType}
    {v : Value} {T : ValType}
    (hG : lookupG C.G e = some (.select target branches))
    (hFind : branches.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    totalTypeDepth (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) ≤
      totalTypeDepth C := by
  -- Convert find? into membership, then use depth_advance_select.
  have hMem : (ℓ, L) ∈ branches := List.mem_of_find?_eq_some hFind
  have hLt := LocalType.depth_advance_select target branches ℓ L hMem
  have hLe : L.depth ≤ (LocalType.select target branches).depth := Nat.le_of_lt hLt
  simpa [totalTypeDepth, totalTypeDepthG, sendStep] using
    totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.select target branches) (Lnew:=L) hG hLe

/-- Branch steps reduce totalTypeDepth (depth decreases to chosen branch). -/
theorem totalTypeDepth_branch_le {C : Config} {e : Endpoint} {source : Role}
    {typeBranches : List (Label × LocalType)} {ℓ : Label} {L : LocalType}
    (hG : lookupG C.G e = some (.branch source typeBranches))
    (hFind : typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    totalTypeDepth { C with G := updateG C.G e L } ≤ totalTypeDepth C := by
  -- Convert find? into membership, then use depth_advance_branch.
  have hMem : (ℓ, L) ∈ typeBranches := List.mem_of_find?_eq_some hFind
  have hLt := LocalType.depth_advance_branch source typeBranches ℓ L hMem
  have hLe : L.depth ≤ (LocalType.branch source typeBranches).depth := Nat.le_of_lt hLt
  simpa [totalTypeDepth, totalTypeDepthG] using
    totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.branch source typeBranches) (Lnew:=L) hG hLe

/-- StepBase does not increase totalTypeDepth. -/
theorem totalTypeDepth_stepBase_le {C C' : Config} (h : StepBase C C') :
    totalTypeDepth C' ≤ totalTypeDepth C := by
  -- Case analysis on the head step rule.
  cases h with
  | send hProc hK hX hG =>
      -- Send case: reduce to the send helper lemma.
      simpa using totalTypeDepth_send_le (C:=C) (hG:=hG)
  | recv hProc hK hG hBuf =>
      -- Recv case: reduce to the recv helper lemma.
      simpa using totalTypeDepth_recv_le (C:=C) (hG:=hG)
  | select hProc hK hG hFind =>
      -- Select case: reduce to the select helper lemma.
      simpa using totalTypeDepth_select_le (C:=C) (hG:=hG) (hFind:=hFind)
  | branch hProc hK hG hBuf hFindP hFindT hDeq =>
      -- Branch case: reduce to the branch helper lemma.
      simpa using totalTypeDepth_branch_le (C:=C) (hG:=hG) (hFind:=hFindT)
  | newSession hProc =>
      -- newSession does not change G.
      simp [totalTypeDepth, totalTypeDepthG, newSessionStep]
  | assign hProc =>
      -- assign does not change G.
      simp [totalTypeDepth, totalTypeDepthG]
  | seq2 hProc =>
      -- seq2 does not change G.
      simp [totalTypeDepth, totalTypeDepthG]
  | par_skip_left hProc =>
      -- par_skip_left does not change G.
      simp [totalTypeDepth, totalTypeDepthG]
  | par_skip_right hProc =>
      -- par_skip_right does not change G.
      simp [totalTypeDepth, totalTypeDepthG]

/-- Step does not increase totalTypeDepth. -/
theorem totalTypeDepth_step_le {C C' : Config} (h : Step C C') :
    totalTypeDepth C' ≤ totalTypeDepth C := by
  -- Induct on the step derivation.
  induction h with
  | base hbase =>
      exact totalTypeDepth_stepBase_le hbase
  | seq_left hProc hStep ih =>
      -- seq-left only changes the process wrapper.
      simpa [totalTypeDepth] using ih
  | par_left hProc hStep ih =>
      -- par-left only changes the process wrapper.
      simpa [totalTypeDepth] using ih
  | par_right hProc hStep ih =>
      -- par-right only changes the process wrapper.
      simpa [totalTypeDepth] using ih

/-- totalTypeDepth is non-increasing along unbounded reachability. -/
theorem totalTypeDepth_reachable_le {C₀ C : Config} (h : UnboundedReachable C₀ C) :
    totalTypeDepth C ≤ totalTypeDepth C₀ := by
  -- Induct on the reachability derivation.
  induction h with
  | refl => simp
  | tail hreach hstep ih =>
      exact le_trans (totalTypeDepth_step_le hstep) ih

/-- Uniform depth bound derived from the initial totalTypeDepth. -/
theorem depth_bound_of_reachable (C₀ : Config) :
    ∃ d, ∀ C ep L, UnboundedReachable C₀ C → (ep, L) ∈ C.G → L.depth ≤ d := by
  -- Use totalTypeDepth C₀ as a global bound.
  refine ⟨totalTypeDepth C₀, ?_⟩
  intro C ep L hreach hmem
  have hLe := depth_le_totalTypeDepth_of_mem C hmem
  exact le_trans hLe (totalTypeDepth_reachable_le hreach)

/-! ## GEnv Size Bounds -/

/-- updateG preserves length when the endpoint is already present. -/
theorem length_updateG_of_lookup {G : GEnv} {e : Endpoint}
    {Lold Lnew : LocalType} (hLookup : lookupG G e = some Lold) :
    (updateG G e Lnew).length = G.length := by
  -- Induct on the environment to align the update position.
  induction G generalizing e Lold Lnew with
  | nil => cases hLookup
  | cons hd tl ih =>
      cases hd with
      | mk ep L =>
          by_cases hEq : e = ep
          · -- Update hits head: length unchanged.
            simp [updateG, hEq]
          · -- Update recurses on tail: use IH.
            have hLookup' : lookupG tl e = some Lold := by
              have hEq' : (e == ep) = false := beq_eq_false_iff_ne.mpr hEq
              simpa [lookupG, List.lookup, hEq'] using hLookup
            simp [updateG, hEq, ih (e:=e) (Lold:=Lold) (Lnew:=Lnew) hLookup']

/-- StepBase preserves GEnv length. -/
theorem G_length_stepBase_eq {C C' : Config} (h : StepBase C C') :
    C'.G.length = C.G.length := by
  -- Case analysis on the head step rule.
  cases h with
  | send hProc hK hX hG =>
      simpa [sendStep] using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | recv hProc hK hG hBuf =>
      -- recvStep reduces to a G update when the buffer is non-empty.
      simpa [recvStep, dequeueBuf, hBuf] using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | select hProc hK hG hFind =>
      simpa [sendStep] using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | branch hProc hK hG hBuf hFindP hFindT hDeq =>
      -- Branch updates G at the receiver endpoint.
      simpa using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | newSession hProc =>
      -- newSession does not change G.
      simp [newSessionStep]
  | assign hProc =>
      -- assign does not change G.
      rfl
  | seq2 hProc =>
      -- seq2 does not change G.
      rfl
  | par_skip_left hProc =>
      -- par_skip_left does not change G.
      rfl
  | par_skip_right hProc =>
      -- par_skip_right does not change G.
      rfl

/-- Step preserves GEnv length. -/
theorem G_length_step_eq {C C' : Config} (h : Step C C') :
    C'.G.length = C.G.length := by
  -- Induct on the step derivation.
  induction h with
  | base hbase =>
      exact G_length_stepBase_eq hbase
  | seq_left hProc hStep ih =>
      simpa using ih
  | par_left hProc hStep ih =>
      simpa using ih
  | par_right hProc hStep ih =>
      simpa using ih

/-- GEnv length is preserved along unbounded reachability. -/
theorem G_length_reachable_eq {C₀ C : Config} (h : UnboundedReachable C₀ C) :
    C.G.length = C₀.G.length := by
  -- Induct on the reachability derivation.
  induction h with
  | refl => rfl
  | tail hreach hstep ih =>
      exact (G_length_step_eq hstep).trans ih

/-- Uniform size bound derived from the initial GEnv length. -/
theorem G_length_bound_of_reachable (C₀ : Config) :
    ∃ m, ∀ C, UnboundedReachable C₀ C → C.G.length ≤ m := by
  -- Use the preserved initial length as a bound.
  refine ⟨C₀.G.length, ?_⟩
  intro C hreach
  exact (G_length_reachable_eq hreach).le


end
