import Protocol.Coherence.ConfigEquiv

/-! # Protocol.Coherence.Conserved

Conserved-quantity packaging for the quotient view of coherence:
- snapshot of per-edge buffers / per-session participants / edge type-trace triples
- equivalence theorem: `ConfigEquiv ↔ SameConservedQuantities`
- Noether-style statement: symmetry actions preserve coherence
- erasure/projection/resource helper definitions
-/

/-
The Problem. Coherence is defined operationally via Consume, but we want a
"conserved quantities" view for quotient/symmetry reasoning. Two configurations
should be equivalent if they have the same edge profiles.

Solution Structure. We define:
1. `EdgeTypeTrace`: per-edge snapshot of sender/receiver types and trace
2. `ConservedQuantities`: full profile of buffers, participants, and edge triples
3. Equivalence theorem: `ConfigEquiv ↔ SameConservedQuantities`
4. Noether-style corollary: symmetry actions preserve coherence
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Core Development -/

/-- Edge-local type/trace snapshot used in conserved profiles. -/
structure EdgeTypeTrace where
  senderType : Option LocalType
  receiverType : Option LocalType
  trace : Trace

/-- Rename all session-indexed payload in an edge snapshot. -/
def renameEdgeTypeTrace (ρ : SessionRenaming) (x : EdgeTypeTrace) : EdgeTypeTrace :=
  { senderType := x.senderType.map (renameLocalType ρ)
    receiverType := x.receiverType.map (renameLocalType ρ)
    trace := x.trace.map (renameValType ρ) }

/-- Coarse conserved profile used by the quotient/noether package. -/
structure ConservedQuantities where
  /-- Per-edge buffered payload profile. -/
  perEdgeBufferCompatibility : Edge → Trace
  /-- Per-session participant profile. -/
  sessionIsolation : SessionId → Set Role
  /-- Per-edge sender/receiver type + trace profile. -/
  typeTraceConsistency : Edge → EdgeTypeTrace

/-- Session-local participant projection from a configuration. -/
def sessionIsolationOf (C : CoherenceConfig) (sid : SessionId) : Set Role :=
  fun r => (lookupG C.G { sid := sid, role := r }).isSome

/-- Edge-local type/trace projection from a configuration. -/
def typeTraceConsistencyOf (C : CoherenceConfig) (e : Edge) : EdgeTypeTrace :=
  { senderType := lookupG C.G { sid := e.sid, role := e.sender }
    receiverType := lookupG C.G { sid := e.sid, role := e.receiver }
    trace := lookupD C.D e }

/-- Conserved profile extracted from a coherence configuration. -/
def conservedOf (C : CoherenceConfig) : ConservedQuantities :=
  { perEdgeBufferCompatibility := fun e => lookupD C.D e
    sessionIsolation := sessionIsolationOf C
    typeTraceConsistency := typeTraceConsistencyOf C }

/-- Two configurations have the same conserved quantities up to session renaming. -/
def SameConservedQuantities (C₁ C₂ : CoherenceConfig) : Prop :=
  ∃ σ : SessionIso,
    (∀ e,
      (conservedOf C₂).perEdgeBufferCompatibility (renameEdge (SessionIso.toRenaming σ) e) =
        ((conservedOf C₁).perEdgeBufferCompatibility e).map
          (renameValType (SessionIso.toRenaming σ))) ∧
    (∀ sid r,
      (conservedOf C₂).sessionIsolation ((SessionIso.toRenaming σ).f sid) r ↔
        (conservedOf C₁).sessionIsolation sid r) ∧
    (∀ e,
      (conservedOf C₂).typeTraceConsistency (renameEdge (SessionIso.toRenaming σ) e) =
        renameEdgeTypeTrace (SessionIso.toRenaming σ)
          ((conservedOf C₁).typeTraceConsistency e))

/-! ## Conserved/Profile Equivalence (`ConfigEquiv`) -/

/-- `ConfigEquiv` implies equality of conserved profiles. -/
theorem sameConserved_of_ConfigEquiv {C₁ C₂ : CoherenceConfig}
    (hEq : ConfigEquiv C₁ C₂) :
    SameConservedQuantities C₁ C₂ := by
  rcases hEq with ⟨σ, hG, hD⟩
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro e
    simpa [conservedOf] using hD e
  · intro sid r
    have hLookup := hG { sid := sid, role := r }
    have hSome :
        (lookupG C₂.G { sid := (SessionIso.toRenaming σ).f sid, role := r }).isSome =
          (lookupG C₁.G { sid := sid, role := r }).isSome := by
      simpa [renameEndpoint] using congrArg Option.isSome hLookup
    simpa [conservedOf, sessionIsolationOf] using hSome
  · intro e
    cases e with
    | mk sid sender receiver =>
      have hSender := hG { sid := sid, role := sender }
      have hReceiver := hG { sid := sid, role := receiver }
      have hTrace := hD { sid := sid, sender := sender, receiver := receiver }
      have hSender' :
          lookupG C₂.G { sid := (SessionIso.toRenaming σ).f sid, role := sender } =
            (lookupG C₁.G { sid := sid, role := sender }).map (renameLocalType (SessionIso.toRenaming σ)) := by
        simpa [renameEndpoint] using hSender
      have hReceiver' :
          lookupG C₂.G { sid := (SessionIso.toRenaming σ).f sid, role := receiver } =
            (lookupG C₁.G { sid := sid, role := receiver }).map (renameLocalType (SessionIso.toRenaming σ)) := by
        simpa [renameEndpoint] using hReceiver
      have hTrace' :
          lookupD C₂.D { sid := (SessionIso.toRenaming σ).f sid, sender := sender, receiver := receiver } =
            (lookupD C₁.D { sid := sid, sender := sender, receiver := receiver }).map
              (renameValType (SessionIso.toRenaming σ)) := by
        simpa [renameEdge] using hTrace
      rw [EdgeTypeTrace.mk.injEq]
      exact ⟨hSender', hReceiver', hTrace'⟩

/-! ## Reconstructing `ConfigEquiv` from Conserved Profiles -/

/-- Equality of conserved profiles implies `ConfigEquiv`. -/
theorem ConfigEquiv_of_sameConserved {C₁ C₂ : CoherenceConfig}
    (hSame : SameConservedQuantities C₁ C₂) :
    ConfigEquiv C₁ C₂ := by
  rcases hSame with ⟨σ, hBuf, _hSess, hType⟩
  refine ⟨σ, ?_, ?_⟩
  · intro ep
    let selfEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := ep.role }
    have hSelf := hType selfEdge
    have hSender := congrArg EdgeTypeTrace.senderType hSelf
    simpa [conservedOf, typeTraceConsistencyOf, renameEdgeTypeTrace, renameEdge, renameEndpoint, selfEdge]
      using hSender
  · intro e
    simpa [conservedOf] using hBuf e

/-- Main quotient theorem for the conserved-profile package. -/
theorem configEquiv_iff_sameConservedQuantities (C₁ C₂ : CoherenceConfig) :
    ConfigEquiv C₁ C₂ ↔ SameConservedQuantities C₁ C₂ := by
  constructor
  · exact sameConserved_of_ConfigEquiv
  · exact ConfigEquiv_of_sameConserved

/-! ## Symmetry Action and Noether-Style Conservation -/

/-- Symmetry action on configurations (session-ID renaming). -/
def symmetryAction (σ : SessionIso) (C : CoherenceConfig) : CoherenceConfig :=
  { G := renameGEnv (SessionIso.toRenaming σ) C.G
    D := renameDEnv (SessionIso.toRenaming σ) C.D }

/-- Noether-style conserved predicate under protocol symmetries. -/
def ConservedUnderSymmetry (I : CoherenceConfig → Prop) : Prop :=
  ∀ σ C, I C → I (symmetryAction σ C)

/-- Noether connection: protocol symmetries preserve coherence. -/
theorem noether_coherence_conservation :
    ConservedUnderSymmetry (fun C => Coherent C.G C.D) := by
  intro σ C hCoh
  simpa [symmetryAction] using
    (CoherentRenaming (ρ := SessionIso.toRenaming σ) (G := C.G) (D := C.D) hCoh)

/-! ## Observational Erasure and Quotient Invariance -/

/-- Setoid for observational erasure by `ConfigEquiv`. -/
def ConfigEquivSetoid : Setoid CoherenceConfig where
  r := ConfigEquiv
  iseqv := ConfigEquiv_equivalence

/-- Observational erasure: configuration modulo `ConfigEquiv`. -/
def observationalErasure (C : CoherenceConfig) : Quotient ConfigEquivSetoid :=
  Quotient.mk _ C

/-- Identity erasure map (explicit named map for proofs/pipelines). -/
def identityErasure : CoherenceConfig → CoherenceConfig := id

/-- Identity erasure stays in the same `ConfigEquiv` class. -/
theorem identityErasure_equiv (C : CoherenceConfig) :
    ConfigEquiv C (identityErasure C) := by
  simpa [identityErasure] using ConfigEquiv_refl C

/-- Observable invariance under the quotient relation `ConfigEquiv`. -/
def ConfigEquivInvariantObservable {α : Type} (F : CoherenceConfig → α) : Prop :=
  ∀ {C₁ C₂}, ConfigEquiv C₁ C₂ → F C₁ = F C₂

/-- Quotient-factorization property for observables:
    `F` depends only on the `observationalErasure` class. -/
def FactorsThroughObservationalErasure {α : Type} (F : CoherenceConfig → α) : Prop :=
  ∃ Fq : Quotient ConfigEquivSetoid → α,
    ∀ C, F C = Fq (observationalErasure C)

/-- Any observable that factors through `observationalErasure`
    is `ConfigEquiv`-invariant. -/
theorem configEquivInvariant_of_factorsThroughObservationalErasure
    {α : Type} {F : CoherenceConfig → α}
    (hFactor : FactorsThroughObservationalErasure F) :
    ConfigEquivInvariantObservable F := by
  rcases hFactor with ⟨Fq, hFq⟩
  intro C₁ C₂ hEq
  have hQuot : observationalErasure C₁ = observationalErasure C₂ :=
    Quotient.sound hEq
  calc
    F C₁ = Fq (observationalErasure C₁) := hFq C₁
    _ = Fq (observationalErasure C₂) := by simp [hQuot]
    _ = F C₂ := (hFq C₂).symm

/-- Any `ConfigEquiv`-invariant observable factors through `observationalErasure`. -/
theorem factorsThroughObservationalErasure_of_configEquivInvariant
    {α : Type} {F : CoherenceConfig → α}
    (hInv : ConfigEquivInvariantObservable F) :
    FactorsThroughObservationalErasure F := by
  refine ⟨Quotient.lift F (by intro C₁ C₂ hEq; exact hInv hEq), ?_⟩
  intro C
  rfl

/-! ## Quotient Universality -/

/-- Quotient universality for coherence observables:
    factorization through `observationalErasure` iff `ConfigEquiv`-invariance. -/
theorem factorsThroughObservationalErasure_iff_configEquivInvariant
    {α : Type} (F : CoherenceConfig → α) :
    FactorsThroughObservationalErasure F ↔ ConfigEquivInvariantObservable F := by
  constructor
  · exact configEquivInvariant_of_factorsThroughObservationalErasure
  · exact factorsThroughObservationalErasure_of_configEquivInvariant

/-! ## Session-Projection Helpers -/

/-- Empty edge snapshot used by out-of-session projections. -/
def emptyEdgeTypeTrace : EdgeTypeTrace :=
  { senderType := none, receiverType := none, trace := [] }

/-- Session projection of a conserved profile. -/
def projectSessionConserved (Q : ConservedQuantities) (sid₀ : SessionId) : ConservedQuantities :=
  { perEdgeBufferCompatibility := fun e => if e.sid = sid₀ then Q.perEdgeBufferCompatibility e else []
    sessionIsolation := fun sid =>
      if sid = sid₀ then Q.sessionIsolation sid else (fun _ => False)
    typeTraceConsistency := fun e => if e.sid = sid₀ then Q.typeTraceConsistency e else emptyEdgeTypeTrace }

/-- Locality: projected buffers outside the chosen session are empty. -/
theorem projectSessionConserved_local_buffers (Q : ConservedQuantities) (sid₀ : SessionId)
    {e : Edge} (hSid : e.sid ≠ sid₀) :
    (projectSessionConserved Q sid₀).perEdgeBufferCompatibility e = [] := by
  simp [projectSessionConserved, hSid]

/-- Locality: projected type/trace snapshots outside the chosen session are empty. -/
theorem projectSessionConserved_local_types (Q : ConservedQuantities) (sid₀ : SessionId)
    {e : Edge} (hSid : e.sid ≠ sid₀) :
    (projectSessionConserved Q sid₀).typeTraceConsistency e = emptyEdgeTypeTrace := by
  simp [projectSessionConserved, hSid]

/-! ## Edge Resource Conservation -/

/-- Edge-local resource mass (trace length). -/
def edgeResourceMass (Q : ConservedQuantities) (e : Edge) : Nat :=
  (Q.perEdgeBufferCompatibility e).length

/-- Resource conservation under `SameConservedQuantities`: edge masses commute with renaming. -/
theorem resource_conservation_of_sameConserved {C₁ C₂ : CoherenceConfig}
    (hSame : SameConservedQuantities C₁ C₂) :
    ∃ σ : SessionIso,
      ∀ e,
        edgeResourceMass (conservedOf C₂) (renameEdge (SessionIso.toRenaming σ) e) =
          edgeResourceMass (conservedOf C₁) e := by
  rcases hSame with ⟨σ, hBuf, _hSess, _hType⟩
  refine ⟨σ, ?_⟩
  intro e
  have hLen := congrArg List.length (hBuf e)
  simpa [edgeResourceMass] using hLen

end
