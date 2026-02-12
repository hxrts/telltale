import Protocol.Typing.Core

/-! # MPST Process Typing: Judgments

This module defines advanced typing judgments including parallel split witnesses. -/

/-
The Problem. Parallel composition typing requires splitting contexts, but we
need explicit witnesses that can be transported in framed proofs. The naive
approach couples split identity to index bookkeeping.

Solution Structure. We define:
1. `ParSplit`: explicit split witness for parallel composition
2. `ParWitness`: witness-oriented inversion for par typing
3. `*_par_nG_irrel` lemmas for extensional treatment of the right index
-/

/- Par typing uses an explicit split witness (`ParSplit`) and witness-oriented
inversion (`ParWitness`) so framed proofs can transport split identity without
depending on ambient right-index bookkeeping. The right par index `nG` is
treated extensionally via `*_par_nG_irrel` lemmas. -/

/-! ## Key Judgments

- `HasTypeProcN n S G D P`: Process P is well-typed under environments S, G, D
  with maximum session ID n
- `WTConfigN n S G D C`: Configuration C is well-typed

## Typing Rules

- **Skip**: `⊢ skip` (always well-typed)
- **Seq**: `⊢ P` and `⊢ Q` implies `⊢ seq P Q`
- **Par**: `⊢ P` and `⊢ Q` with split contexts implies `⊢ par P Q`
- **Send**: If `S[k] = chan (sid, r)` and `G[sid,r] = !q(T).L` and `S[x] = T`,
            then `⊢ send k x` and G[sid,r] ↦ L
- **Recv**: If `S[k] = chan (sid, r)` and `G[sid,r] = ?p(T).L`,
            then `⊢ recv k x` and G[sid,r] ↦ L, S[x] ↦ T
- **Select**: If `S[k] = chan (sid, r)` and `G[sid,r] = ⊕q{ℓᵢ: Lᵢ}`,
              then `⊢ select k ℓⱼ` and G[sid,r] ↦ Lⱼ
- **Branch**: If `S[k] = chan (sid, r)` and `G[sid,r] = &p{ℓᵢ: Lᵢ}`,
              then `⊢ branch k [(ℓᵢ, Pᵢ)]` if each Pᵢ is typed under Lᵢ
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Well-Typed Configuration -/

/-- A configuration is well-typed if all components are consistent:
    - Session IDs in store/buffers are < nextSid
    - Store is typed by S and G
    - Buffers are typed by D
    - G and D are coherent
    - Process is typed -/
structure WTConfigN (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config) : Prop where
  /-- nextSid matches. -/
  nextSid_eq : C.nextSid = n
  /-- Store is typed. -/
  store_typed : StoreTyped G S C.store
  /-- Buffers are typed. -/
  buffers_typed : BuffersTyped G D C.bufs
  /-- Environments are coherent. -/
  coherent : Coherent G D
  /-- Process is typed. -/
  proc_typed : HasTypeProcN n S G D C.proc

/-! ## Typing Lemmas -/

/-- Skip is well-typed under any environments. -/
theorem skip_typed (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) :
    HasTypeProcN n S G D .skip :=
  HasTypeProcN.skip

/-- If P is typed and Q is typed, seq P Q is typed. -/
theorem seq_typed (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv)
    (P Q : Process)
    (hP : HasTypeProcN n S G D P)
    (hQ : HasTypeProcN n S G D Q) :
    HasTypeProcN n S G D (.seq P Q) :=
  HasTypeProcN.seq hP hQ

/-! ## Inversion Lemmas -/

/-- Inversion for send typing.
    Note: The send constructor produces a judgment with updated G,
    so we invert from the updated environment perspective. -/
theorem send_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} {k x : Var}
    (h : HasTypeProcN n S G D (.send k x)) :
    ∃ e q T L G',
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G' e = some (.send q T L) ∧
      lookupSEnv S x = some T ∧
      G = updateG G' e L := by
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, _, hk, hG, hx, rfl⟩

/-- Inversion for recv typing.
    Note: The recv constructor produces a judgment with updated S and G. -/
theorem recv_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} {k x : Var}
    (h : HasTypeProcN n S G D (.recv k x)) :
    ∃ e p T L S' G',
      lookupSEnv S' k = some (.chan e.sid e.role) ∧
      lookupG G' e = some (.recv p T L) ∧
      S = updateSEnv S' x T ∧
      G = updateG G' e L := by
  cases h with
  | recv hk hG => exact ⟨_, _, _, _, _, _, hk, hG, rfl, rfl⟩

/-- Inversion for select typing.
    Note: The select constructor produces a judgment with updated G.
    Reference: `work/effects/008.lean:287-292` -/
theorem select_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} {k : Var} {l : Label}
    (h : HasTypeProcN n S G D (.select k l)) :
    ∃ e q bs L G',
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G' e = some (.select q bs) ∧
      bs.find? (fun b => b.1 == l) = some (l, L) ∧
      G = updateG G' e L := by
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, _, _, hk, hG, hbs, rfl⟩

/-- Inversion for branch typing.
    Reference: `work/effects/008.lean:294-300` -/
theorem branch_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv}
    {k : Var} {procs : List (Label × Process)}
    (h : HasTypeProcN n S G D (.branch k procs)) :
    ∃ e p bs,
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) ∧
      bs.length = procs.length ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcN n S (updateG G e (bs.get ⟨i, hi⟩).2) D (procs.get ⟨i, hip⟩).2) := by
  cases h with
  | branch hk hG hLen hLabels hBodies =>
    exact ⟨_, _, _, hk, hG, hLen, hLabels, hBodies⟩

/-! ## Progress-Oriented Typing

For the progress theorem, we need a typing relation that uses "pre-update"
environments (the actual runtime state), not "post-update" environments.
This matches the approach in `work/effects/008.lean`.

Reference: `work/effects/008.lean:151-176` -/

/-- Pre-update style process typing for progress theorem.
    Unlike HasTypeProcN which uses post-update environments, this relation
    uses the environment as-is, making it suitable for connecting to runtime state.

    This is an alternative view of typing where:
    - HasTypeProcN says "after effects, we have these types"
    - HasTypeProcPre says "given current types, this process is well-formed" -/
inductive HasTypeProcPre : SEnv → OwnedEnv → GEnv → Process → Prop where
  /-- Skip is always well-typed. -/
  | skip {Ssh Sown G} : HasTypeProcPre Ssh Sown G .skip

  /-- Send: channel k points to endpoint e, e has send type, payload x has correct type. -/
  | send {Ssh Sown G k x e q T L} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.send q T L) →
      lookupSEnv (SEnvVisible Ssh Sown) x = some T →
      HasTypeProcPre Ssh Sown G (.send k x)

  /-- Recv: channel k points to endpoint e, e has recv type. -/
  | recv {Ssh Sown G k x e p T L} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      lookupSEnv Ssh x = none →
      HasTypeProcPre Ssh Sown G (.recv k x)

  /-- Select: channel k points to endpoint e, e has select type with label l. -/
  | select {Ssh Sown G k l e q bs L} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.select q bs) →
      bs.find? (fun b => b.1 == l) = some (l, L) →
      HasTypeProcPre Ssh Sown G (.select k l)

  /-- Branch: channel k points to endpoint e, e has branch type, all branches typed. -/
  | branch {Ssh Sown G k procs e p bs} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.branch p bs) →
      bs.length = procs.length →
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) →
      HasTypeProcPre Ssh Sown G (.branch k procs)

  /-- Sequential composition. -/
  | seq {Ssh Sown G P Q} :
      HasTypeProcPre Ssh Sown G P →
      HasTypeProcPre Ssh Sown G Q →
      HasTypeProcPre Ssh Sown G (.seq P Q)

  /-- Parallel composition. -/
  | par {Ssh Sown G P Q} {S₁ S₂ : SEnv} {nS nG : Nat} :
      DisjointS S₁ S₂ →
      Sown.left = S₁ ++ S₂ →
      HasTypeProcPre Ssh { right := Sown.right ++ S₂, left := S₁ } G P →
      HasTypeProcPre Ssh { right := Sown.right ++ S₁, left := S₂ } G Q →
      HasTypeProcPre Ssh Sown G (.par nS nG P Q)

  /-- Assignment. -/
  | assign {Ssh Sown G x v T} :
      lookupSEnv Ssh x = none →
      HasTypeVal G v T →
      HasTypeProcPre Ssh Sown G (.assign x v)

/-! ## Inversion Lemmas for Pre-Update Typing

These lemmas directly extract type information from pre-update typing judgments.
Reference: `work/effects/008.lean:274-300` -/

/-- Inversion for send (pre-update style).
    Reference: `work/effects/008.lean:274-279` -/
theorem inversion_send {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    (h : HasTypeProcPre Ssh Sown G (.send k x)) :
    ∃ e q T L,
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.send q T L) ∧
      lookupSEnv (SEnvVisible Ssh Sown) x = some T := by
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, hk, hG, hx⟩

/-- Inversion for recv (pre-update style).
    Reference: `work/effects/008.lean:281-285` -/
theorem inversion_recv {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    (h : HasTypeProcPre Ssh Sown G (.recv k x)) :
    ∃ e p T L,
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.recv p T L) ∧
      lookupSEnv Ssh x = none := by
  cases h with
  | recv hk hG hx => exact ⟨_, _, _, _, hk, hG, hx⟩

/-- Inversion for select (pre-update style).
    Reference: `work/effects/008.lean:287-292` -/
theorem inversion_select {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {l : Label}
    (h : HasTypeProcPre Ssh Sown G (.select k l)) :
    ∃ e q bs L,
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.select q bs) ∧
      bs.find? (fun b => b.1 == l) = some (l, L) := by
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, _, hk, hG, hbs⟩

/-- Inversion for branch (pre-update style).
    Reference: `work/effects/008.lean:294-300` -/
theorem inversion_branch {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {procs : List (Label × Process)}
    (h : HasTypeProcPre Ssh Sown G (.branch k procs)) :
    ∃ e p bs,
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) ∧
      bs.length = procs.length ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) := by
  cases h with
  | branch hk hG hLen hLabels hBodies =>
      exact ⟨_, _, _, hk, hG, hLen, hLabels, hBodies⟩

/-- `HasTypeProcPre` is insensitive to the right par index `nG`. -/
theorem HasTypeProcPre_par_nG_irrel
    {Ssh Sown G P Q nS nG nG'} :
    HasTypeProcPre Ssh Sown G (.par nS nG P Q) →
    HasTypeProcPre Ssh Sown G (.par nS nG' P Q) := by
  intro h
  cases h with
  | par hDisjS hSplit hP hQ =>
      exact HasTypeProcPre.par hDisjS hSplit hP hQ

/-! ## Linear Resource Transition Typing

**Core Judgment**: `TypedStep G D Ssh Sown C C' G' D' Sown'`

**Reading**: Configuration C consumes resources (G, D, S) and steps to C',
producing resources (G', D', S').

This design ensures preservation by making the pre/post-state distinction
intrinsic to the typing judgment.

**References**: Theoretical foundation: Wadler (2012) "Propositions as Sessions"

## Key Properties

1. **Preservation**: Trivial (the judgment itself proves it)
2. **Progress**: Structured case analysis on configuration
3. **Coherence**: Uses existing `Coherent_send_preserved`, `Coherent_recv_preserved`
4. **Soundness**: TypedStep refines Step -/

/-! ## Pre-Update Typing with Post Environments -/

/-- Pre-update style process typing with explicit post environments.

    This relation tracks how the session/value environments evolve after the
    *entire* process completes. It is used to avoid the sequential monotonicity
    issue in preservation: after a single step, the remaining process should
    still lead to the same final environments. -/
inductive HasTypeProcPreOut : SEnv → OwnedEnv → GEnv → Process → OwnedEnv → GEnv → Footprint → DeltaSEnv → Prop where
  /-- Skip leaves environments unchanged. -/
  | skip {Ssh Sown G} : HasTypeProcPreOut Ssh Sown G .skip Sown G [] ∅

  /-- Send advances the sender's local type. -/
  | send {Ssh Sown G k x e q T L} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.send q T L) →
      lookupSEnv (SEnvVisible Ssh Sown) x = some T →
      HasTypeProcPreOut Ssh Sown G (.send k x) Sown (updateG G e L) [] ∅

  /-- Recv advances the receiver's local type and extends S for x. -/
  | recv_new {Ssh Sown G k x e p T L} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      lookupSEnv Ssh x = none →
      lookupSEnv Sown.left x = none →
      HasTypeProcPreOut Ssh Sown G (.recv k x)
        (OwnedEnv.updateLeft Sown x T) (updateG G e L) [x] (updateSEnv ∅ x T)

  | recv_old {Ssh Sown G k x e p T L T'} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      lookupSEnv Ssh x = none →
      lookupSEnv Sown.left x = some T' →
      HasTypeProcPreOut Ssh Sown G (.recv k x)
        (OwnedEnv.updateLeft Sown x T) (updateG G e L) [x] ∅

  /-- Select advances the sender's local type. -/
  | select {Ssh Sown G k l e q bs L} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.select q bs) →
      bs.find? (fun b => b.1 == l) = some (l, L) →
      HasTypeProcPreOut Ssh Sown G (.select k l) Sown (updateG G e L) [] ∅

  /-- Branch: all branches are pre-typed; post environments follow the runtime label. -/
  | branch {Ssh Sown G k procs e p bs S' G' W Δ} :
      lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.branch p bs) →
      bs.length = procs.length →
      (∀ j (hj : j < bs.length) (hjp : j < procs.length),
        (procs.get ⟨j, hjp⟩).1 = (bs.get ⟨j, hj⟩).1) →
      (∀ j (hj : j < bs.length) (hjp : j < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨j, hj⟩).2) (procs.get ⟨j, hjp⟩).2) →
      (∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh Sown (updateG G e L) P S' G' W Δ) →
      SessionsOf G' ⊆ SessionsOf G →
      SEnvDomSubset Sown.left S'.left →
      S'.right = Sown.right →
      HasTypeProcPreOut Ssh Sown G (.branch k procs) S' G' W Δ

  /-- Sequential composition: compose post environments. -/
  | seq {Ssh Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂} :
      HasTypeProcPreOut Ssh Sown G P S₁ G₁ W₁ Δ₁ →
      HasTypeProcPreOut Ssh S₁ G₁ Q S₂ G₂ W₂ Δ₂ →
      HasTypeProcPreOut Ssh Sown G (.seq P Q) S₂ G₂ (W₁ ++ W₂) (Δ₁ ++ Δ₂)

  /-- Parallel composition with disjoint resources (explicit split witness). -/
  | par {Ssh Sown G P Q Sfin Gfin Wfin Δfin
         S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG} (split : ParSplit Sown.left G) :
      split.S1.length = nS →
      Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
      Gfin = (G₁' ++ G₂') →
      Wfin = (W₁ ++ W₂) →
      Δfin = (Δ₁ ++ Δ₂) →
      DisjointG split.G1 split.G2 →
      DisjointS split.S1 split.S2 →
      DisjointS S₁' split.S2 →
      DisjointS split.S1 S₂' →
      DisjointS S₁' S₂' →
      DisjointW W₁ W₂ →
      DisjointS Δ₁ Δ₂ →
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split.G1 P
        { right := Sown.right ++ split.S2, left := S₁' } G₁' W₁ Δ₁ →
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split.G2 Q
        { right := Sown.right ++ split.S1, left := S₂' } G₂' W₂ Δ₂ →
      HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin Wfin Δfin

  /-- Assignment updates S with x's type. -/
  | assign_new {Ssh Sown G x v T} :
      lookupSEnv Ssh x = none →
      lookupSEnv Sown.left x = none →
      HasTypeVal G v T →
      HasTypeProcPreOut Ssh Sown G (.assign x v)
        (OwnedEnv.updateLeft Sown x T) G [x] (updateSEnv ∅ x T)

  | assign_old {Ssh Sown G x v T T'} :
      lookupSEnv Ssh x = none →
      lookupSEnv Sown.left x = some T' →
      HasTypeVal G v T →
      HasTypeProcPreOut Ssh Sown G (.assign x v)
        (OwnedEnv.updateLeft Sown x T) G [x] ∅


/-! ## Inversion Helpers for Pre-Out Typing -/

/-- Frame-invariant witness for par split alignment at S-length `nS`. -/
structure ParWitness (S : SEnv) (G : GEnv) (nS : Nat) where
  split : ParSplit S G
  hSlen : split.S1.length = nS

/-- Any split of the same owned-left environment at the same `nS` has the same S components. -/
theorem ParSplit.sides_eq_of_witness
    {S : SEnv} {G : GEnv} {nS : Nat}
    (split : ParSplit S G) (pw : ParWitness S G nS)
    (hSlen : split.S1.length = nS) :
    split.S1 = pw.split.S1 ∧ split.S2 = pw.split.S2 := by
  have hSlenEq : split.S1.length = pw.split.S1.length := by
    calc
      split.S1.length = nS := hSlen
      _ = pw.split.S1.length := pw.hSlen.symm
  have hSeq : split.S1 ++ split.S2 = pw.split.S1 ++ pw.split.S2 := by
    calc
      split.S1 ++ split.S2 = S := by simpa [split.hS]
      _ = pw.split.S1 ++ pw.split.S2 := by simpa [pw.split.hS]
  exact ⟨List.append_inj_left hSeq hSlenEq, List.append_inj_right hSeq hSlenEq⟩

/-- Inversion for parallel pre-out typing with explicit environment splits. -/
theorem HasTypeProcPreOut_par_inv {Ssh Sown G P Q Sfin Gfin Wfin Δfin nS nG} :
    HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin Wfin Δfin →
    ∃ S₁ S₂ G₁ G₂ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂,
      Sown.left = (S₁ ++ S₂) ∧
      G = (G₁ ++ G₂) ∧
      Sfin.right = Sown.right ∧
      Sfin.left = (S₁' ++ S₂') ∧
      Gfin = (G₁' ++ G₂') ∧
      Wfin = (W₁ ++ W₂) ∧
      Δfin = (Δ₁ ++ Δ₂) ∧
      DisjointG G₁ G₂ ∧
      DisjointS S₁ S₂ ∧
      DisjointS S₁' S₂ ∧
      DisjointS S₁ S₂' ∧
      DisjointS S₁' S₂' ∧
      DisjointW W₁ W₂ ∧
      DisjointS Δ₁ Δ₂ ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ S₂, left := S₁ } G₁ P
        { right := Sown.right ++ S₂, left := S₁' } G₁' W₁ Δ₁ ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ S₁, left := S₂ } G₂ Q
        { right := Sown.right ++ S₁, left := S₂' } G₂' W₂ Δ₂ := by
  intro h
  cases h with
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW
      hDisjΔ hP hQ =>
      cases split with
      | mk S₁ S₂ G₁ G₂ hS hG =>
          refine ⟨S₁, S₂, G₁, G₂, _, _, _, _, _, _, _, _, hS, hG, ?_, ?_, hGfin, hW, hΔ,
            hDisjG, hDisjS, hDisjS_left, hDisjS_right, hDisjS', hDisjW, hDisjΔ, ?_, ?_⟩
          · simpa [hSfin] using rfl
          · simpa [hSfin] using rfl
          · simpa using hP
          · simpa using hQ

/-- Witness-oriented inversion for parallel pre-out typing. -/
theorem HasTypeProcPreOut_par_inv_witness {Ssh Sown G P Q Sfin Gfin Wfin Δfin nS nG} :
    HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin Wfin Δfin →
    ∃ pw : ParWitness Sown.left G nS, ∃ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂,
      Sfin = { right := Sown.right, left := S₁' ++ S₂' } ∧
      Gfin = (G₁' ++ G₂') ∧
      Wfin = (W₁ ++ W₂) ∧
      Δfin = (Δ₁ ++ Δ₂) ∧
      DisjointG pw.split.G1 pw.split.G2 ∧
      DisjointS pw.split.S1 pw.split.S2 ∧
      DisjointS S₁' pw.split.S2 ∧
      DisjointS pw.split.S1 S₂' ∧
      DisjointS S₁' S₂' ∧
      DisjointW W₁ W₂ ∧
      DisjointS Δ₁ Δ₂ ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ pw.split.S2, left := pw.split.S1 } pw.split.G1 P
        { right := Sown.right ++ pw.split.S2, left := S₁' } G₁' W₁ Δ₁ ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ pw.split.S1, left := pw.split.S2 } pw.split.G2 Q
        { right := Sown.right ++ pw.split.S1, left := S₂' } G₂' W₂ Δ₂ := by
  intro h
  cases h with
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ =>
      rename_i S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂
      exact ⟨⟨split, hSlen⟩, S₁', S₂', G₁', G₂', W₁, W₂, Δ₁, Δ₂,
        hSfin, hGfin, hW, hΔ, hDisjG, hDisjS, hDisjS_left,
        hDisjS_right, hDisjS', hDisjW, hDisjΔ, hP, hQ⟩

end
