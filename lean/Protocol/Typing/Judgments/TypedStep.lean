import Protocol.Typing.Judgments.PreTyping

/-! # TypedStep: Linear Resource Transition Typing

The `TypedStep` judgment for linear resource transitions, capturing how
process steps transform GEnv, DEnv, SEnv, store, and buffers while
maintaining type safety. -/

/-
The Problem. Process execution consumes and produces linear resources
(endpoints, buffers, variables). We need a typing judgment that tracks
these transitions precisely, ensuring each endpoint is used exactly once
and buffers evolve consistently.

Solution Structure. Define `TypedStep` inductive with constructors for
send, recv, select, branch, assign, seq_step, par_left, par_right.
Each constructor specifies the exact state transformation and its
typing preconditions.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## Parallel Index Irrelevance -/
theorem HasTypeProcPreOut_par_nG_irrel
    {Ssh Sown G P Q Sfin Gfin Wfin Δfin nS nG nG'} :
    HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin Wfin Δfin →
    HasTypeProcPreOut Ssh Sown G (.par nS nG' P Q) Sfin Gfin Wfin Δfin := by
  intro h
  cases h with
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ =>
      exact HasTypeProcPreOut.par split hSlen hSfin hGfin hW hΔ
        hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ

-- NOTE: We do not provide a general "forgetful" lemma from HasTypeProcPreOut to
-- HasTypeProcPre, because seq/par pre-out typing does not imply pre-typing for
-- the whole process without additional monotonicity assumptions.

/-! ## TypedStep Inductive Definition -/

/-- Linear resource transition typing judgment.

    **Interpretation**: Process P with state (G, D, S, store, bufs) transitions
    to process P' with state (G', D', S', store', bufs').

    **Linear Resources**:
    - Each endpoint in G is consumed exactly once and produces a continuation
    - Buffers and traces evolve consistently (append on send, pop on recv)
    - Variables are typed as they're assigned

    **Compositionality**: Parallel processes have disjoint resources -/
inductive TypedStep : GEnv → DEnv → SEnv → OwnedEnv → VarStore → Buffers → Process →
                      GEnv → DEnv → OwnedEnv → VarStore → Buffers → Process → Prop
  /-! ## Communication Constructors -/
  | send {G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupStr store x = some v →
      lookupG G e = some (.send target T L) →
      lookupSEnv (SEnvAll Ssh Sown) x = some T →
      HasTypeVal G v T →
      -- Receiver readiness: ensures coherence preservation
      (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
        ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
              (Consume e.role L' [T]).isSome) →

      -- Resource transition definitions
      sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
      G' = updateG G e L →
      D' = appendD D sendEdge T →
      bufs' = enqueueBuf bufs sendEdge v →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.send k x)
                G' D' Sown store bufs' .skip

  | recv {G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupG G e = some (.recv source T L) →
      recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
      lookupBuf bufs recvEdge = v :: vs →
      HasTypeVal G v T →  -- derived from BuffersTyped invariant
      (lookupD D recvEdge).head? = some T →  -- trace head matches (from BuffersTyped + Coherent)

      -- Resource transition definitions
      G' = updateG G e L →
      D' = updateD D recvEdge (lookupD D recvEdge).tail →
      Sown' = OwnedEnv.updateLeft Sown x T →
      store' = updateStr store x v →
      bufs' = updateBuf bufs recvEdge vs →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.recv k x)
                G' D' Sown' store' bufs' .skip

  /-! ## Choice Constructors -/

  | select {G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupG G e = some (.select target bs) →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      -- Receiver readiness for label
      (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
        ∃ L', Consume e.role Ltarget (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
              (Consume e.role L' [.string]).isSome) →

      -- Resource transition definitions
      selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
      G' = updateG G e L →
      D' = appendD D selectEdge .string →
      bufs' = enqueueBuf bufs selectEdge (.string ℓ) →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.select k ℓ)
                G' D' Sown store bufs' .skip

  | branch {G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupG G e = some (.branch source bs) →
      branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
      lookupBuf bufs branchEdge = .string ℓ :: vs →
      procs.find? (fun b => b.1 == ℓ) = some (ℓ, P) →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      (lookupD D branchEdge).head? = some .string →

      -- Resource transition definitions
      G' = updateG G e L →
      D' = updateD D branchEdge (lookupD D branchEdge).tail →
      bufs' = updateBuf bufs branchEdge vs →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.branch k procs)
                G' D' Sown store bufs' P

  /-! ## Assignment And Sequential Constructors -/

  | assign {G D Ssh Sown store bufs x v T S' store'} :
      -- Pre-condition: value is well-typed
      HasTypeVal G v T →

      -- Resource transition definitions (S and store change)
      S' = OwnedEnv.updateLeft Sown x T →
      store' = updateStr store x v →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.assign x v)
                G D S' store' bufs .skip

  | seq_step {G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q} :
      -- Resources flow through first process
      TypedStep G D Ssh Sown store bufs P
                G' D' Sown' store' bufs' P' →

      TypedStep G D Ssh Sown store bufs (.seq P Q)
                G' D' Sown' store' bufs' (.seq P' Q)

  | seq_skip {G D Ssh Sown store bufs Q} :
      -- Skip elimination (identity transition)
      TypedStep G D Ssh Sown store bufs (.seq .skip Q)
                G D Sown store bufs Q

  /-! ## Parallel Constructors -/

  | par_left {Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁' D₁' S₁' nS nG}
      (split : ParSplit Sown.left G) :
      split.S1.length = nS →
      -- Left process transitions with its resources
      TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 } store bufs P
                (G₁' ++ split.G2) (D₁' ++ D₂)
                { right := Sown.right ++ split.S2, left := S₁' } store' bufs' P' →

      -- Resources must be disjoint for parallel composition
      DisjointG split.G1 split.G2 →
      DisjointD D₁ D₂ →
      DisjointS split.S1 split.S2 →

      -- Combined transition
      TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
                (G₁' ++ split.G2) (D₁' ++ D₂) { right := Sown.right, left := S₁' ++ split.S2 }
                store' bufs' (.par S₁'.length nG P' Q)

  | par_right {Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂' D₂' S₂' nS nG}
      (split : ParSplit Sown.left G) :
      split.S1.length = nS →
      -- Right process transitions with its resources
      TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 } store bufs Q
                (split.G1 ++ G₂') (D₁ ++ D₂')
                { right := Sown.right ++ split.S1, left := S₂' } store' bufs' Q' →

      -- Resources must be disjoint
      DisjointG split.G1 split.G2 →
      DisjointD D₁ D₂ →
      DisjointS split.S1 split.S2 →

      -- Combined transition
      TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
                (split.G1 ++ G₂') (D₁ ++ D₂') { right := Sown.right, left := split.S1 ++ S₂' }
                store' bufs' (.par split.S1.length nG P Q')

  | par_skip_left {G D Ssh Sown store bufs Q nS nG}
      (split : ParSplit Sown.left G) :
      split.S1.length = nS →
      split.S1 = [] →
      -- Skip elimination from parallel (left side carries no owned-left bindings).
      TypedStep G D Ssh Sown store bufs (.par nS nG .skip Q)
                G D Sown store bufs Q

  | par_skip_right {G D Ssh Sown store bufs P nS nG}
      (split : ParSplit Sown.left G) :
      split.S1.length = nS →
      split.S2 = [] →
      -- Skip elimination from parallel (right side carries no owned-left bindings).
      TypedStep G D Ssh Sown store bufs (.par nS nG P .skip)
                G D Sown store bufs P

/-! ## Parallel Inversion View -/

/-- Inversion view for `TypedStep` on parallel processes. -/
theorem TypedStep_par_inv
    {G D Ssh Sown store bufs P Q nS nG G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs (.par nS nG P Q) G' D' Sown' store' bufs' P' →
      (∃ pw : ParWitness Sown.left G nS, ∃ D₁ D₂ G₁' D₁' S₁' Pleft',
        D = D₁ ++ D₂ ∧
        TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ pw.split.S2, left := pw.split.S1 } store bufs P
          (G₁' ++ pw.split.G2) (D₁' ++ D₂) { right := Sown.right ++ pw.split.S2, left := S₁' } store' bufs' Pleft' ∧
        DisjointG pw.split.G1 pw.split.G2 ∧
        DisjointD D₁ D₂ ∧
        DisjointS pw.split.S1 pw.split.S2 ∧
        G' = G₁' ++ pw.split.G2 ∧
        D' = D₁' ++ D₂ ∧
        Sown' = { right := Sown.right, left := S₁' ++ pw.split.S2 } ∧
        P' = .par S₁'.length nG Pleft' Q)
      ∨
      (∃ pw : ParWitness Sown.left G nS, ∃ D₁ D₂ G₂' D₂' S₂' Qright',
        D = D₁ ++ D₂ ∧
        TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ pw.split.S1, left := pw.split.S2 } store bufs Q
          (pw.split.G1 ++ G₂') (D₁ ++ D₂') { right := Sown.right ++ pw.split.S1, left := S₂' } store' bufs' Qright' ∧
        DisjointG pw.split.G1 pw.split.G2 ∧
        DisjointD D₁ D₂ ∧
        DisjointS pw.split.S1 pw.split.S2 ∧
        G' = pw.split.G1 ++ G₂' ∧
        D' = D₁ ++ D₂' ∧
        Sown' = { right := Sown.right, left := pw.split.S1 ++ S₂' } ∧
        P' = .par pw.split.S1.length nG P Qright')
      ∨
      (P = .skip ∧ G' = G ∧ D' = D ∧ Sown' = Sown ∧ store' = store ∧ bufs' = bufs ∧ P' = Q)
      ∨
      (Q = .skip ∧ G' = G ∧ D' = D ∧ Sown' = Sown ∧ store' = store ∧ bufs' = bufs ∧ P' = P) := by
  intro hTS
  cases hTS with
  | par_left split hSlen hInner hDisjG hDisjD hDisjS =>
      left
      exact ⟨⟨split, hSlen⟩, _, _, _, _, _, _, rfl, hInner, hDisjG, hDisjD, hDisjS,
        rfl, rfl, rfl, rfl⟩
  | par_right split hSlen hInner hDisjG hDisjD hDisjS =>
      right
      left
      exact ⟨⟨split, hSlen⟩, _, _, _, _, _, _, rfl, hInner, hDisjG, hDisjD, hDisjS,
        rfl, rfl, rfl, rfl⟩
  /-! ## Parallel Skip Inversion Cases -/
  | par_skip_left =>
      right
      right
      left
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | par_skip_right =>
      right
      right
      right
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


end
