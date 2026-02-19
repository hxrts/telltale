# Physical Analogies for the Telltale Runtime

This document develops physical intuitions for the theoretical pillars underlying Telltale's session-type VM. The analogies are drawn from thermodynamics, statistical mechanics, and field theory.


## Overview

Telltale combines several formal systems into a verified runtime for choreographic programming. Each has a physical analogue that illuminates its role:

| Formal System            | Physical Analogue                         | Role in Telltale                 |
|--------------------------|-------------------------------------------|----------------------------------|
| Separation logic         | Extensivity                               | Compositional resource reasoning |
| MPST                     | Symmetry structure (coordination grammar) | Coordination structure           |
| Algebraic effects        | Equations of state                        | Internal dynamics interface      |
| Choreographic projection | Coarse-graining / partial trace           | Global → local decomposition     |
| Resource algebras        | Conserved charges                         | Ownership and accounting         |
| Invariants               | Conservation laws                         | Persistent system constraints    |
| Weakest preconditions    | Sufficient conditions for equilibrium     | Program correctness              |
| Cost metering            | Available work / fuel                     | Bounded computation              |
| Monitors                 | Safety interlocks / thermostats           | Runtime constraint checking      |


## 1. Separation Logic as Extensivity

### The Principle

Separation logic's physical analogue is extensivity, the principle that a composite system's state is the sum of its parts' states and decoupled parts do not interfere. Extensivity is one of three co-equal pillars, alongside symmetry (MPST) and conservation (invariants), connected by deep structural relationships (see §13).

### Separating Conjunction is Independent Subsystems

When two thermodynamic subsystems are decoupled, their extensive quantities add:

```
E_total = E₁ + E₂
S_total = S₁ + S₂
```

No double-counting. The energy in subsystem 1 is disjoint from the energy in subsystem 2. The separating conjunction `P ∗ Q` says exactly this: you own resource P and separately own resource Q, and they partition the total resource with no overlap.

In Telltale, when two sessions hold separate endpoint fragments:

```
endpoint_frag γ₁ e₁ L₁ ∗ endpoint_frag γ₂ e₂ L₂
```

this asserts two decoupled subsystems whose states compose independently. No operation on session γ₁ can affect session γ₂'s resources.

### The Frame Rule is Locality

The frame rule says: if `{P} c {Q}`, then `{P ∗ R} c {Q ∗ R}`. Whatever R is, it's untouched by c.

This *is* the locality principle. If a chemical reaction involves species A and B, species C's concentration is unaffected. If a protocol step advances session 1, session 2's state is unchanged. You prove the A-B interaction in isolation, and the frame rule lifts it to the full system for free.

Every theorem in Telltale that reasons about one session while others exist relies on this. The `wp_frame_l` axiom is the formal statement:

```
R ∗ wp Λ E e Φ ⊢ wp Λ E e (fun v => R ∗ Φ v)
```

The resource R passes through the computation unchanged, demonstrating locality of dynamics.

### Why This Matters

Without extensivity, you can't reason about parts independently because you'd need to consider the entire system for every local step. But extensivity alone is not sufficient: without symmetry (global types), there are no coordination constraints to preserve, and without conservation (invariants), there is nothing to verify at each step. The three pillars are mutually dependent.


## 2. Multiparty Session Types as Symmetry Structure

### The Principle

A global type G describes the full choreography: all interactions, all roles, all branches. This is a symmetry structure of the protocol: it specifies which transformations (message exchanges) are permitted and how they compose. It's closer to a coordination grammar or algebra than a literal group (steps are not invertible).

### The Symmetry Group Analogy

In physics, a symmetry group describes the invariances of a system. In Telltale, the global type plays a similar structural role, even though the protocol steps do not form a literal group:

| Physics             | MPST                                         |
|---------------------|----------------------------------------------|
| Symmetry structure  | Global type G                                |
| Transformations     | Protocol steps (send, recv, branch)          |
| Generators          | Primitive interactions (point-to-point send) |
| Composition         | Sequential and parallel composition          |
| Representations     | Role projections                             |

A crystal's symmetry group tells you every allowed transformation. A global session type tells you every allowed protocol step. Both constrain the system's evolution without specifying a particular trajectory, but the MPST structure is a coordination grammar rather than an invertible group.

### Noether-Style Link: Structure Implies Preservation

Noether's theorem says every continuous symmetry yields a conserved quantity. The MPST analogue is softer: every well-formed global type yields preservation theorems (coherence is maintained by each protocol step).

| Symmetry            | Conserved Quantity                                   |
|---------------------|------------------------------------------------------|
| Rotational symmetry | Angular momentum                                     |
| Time translation    | Energy                                               |
| Send/recv pairing   | Message conservation (every send matches a receive)  |
| Branch agreement    | Label consistency (all roles agree on chosen branch) |

The coherence invariant in `Protocol/Coherence/` is a conservation law: for every directed edge, consuming the in-flight trace from the receiver's perspective succeeds. This is "conserved" across all protocol steps, as shown by `Coherent_send_preserved`, `Coherent_recv_preserved`, `Coherent_select_preserved`, `Coherent_branch_preserved`.

### Representation Theory as Projection (Loose Analogy)

Each irreducible representation of a symmetry group gives a "local view" of how the group acts on a particular subspace. Choreographic projection does the same, in a loose sense: π_r(G) extracts role r's local view from the global type.

```
Global type G          ↔  Symmetry group
π_Alice(G) = L_Alice   ↔  Irreducible representation on Alice's subspace
π_Bob(G) = L_Bob       ↔  Irreducible representation on Bob's subspace
```

The harmony theorem (`Choreography/Harmony/`) proves that projection is sound: the local views are faithful representations of the global structure. In physics terms: representations preserve the structure of allowed transformations. This is an analogy, not a literal group representation.


## 3. Choreographic Projection as Coarse-Graining

### The Principle

A choreography describes a system from the "God's-eye view," the full joint state of all roles. Projection produces a local view by erasing interactions that don't involve a given role. This is coarse-graining (or marginalization), tracing out degrees of freedom you can't observe to produce a reduced description.

This is *not* symmetry breaking. Symmetry breaking selects a particular value from a set of equivalent options (spins choosing a direction). Projection doesn't commit to anything because it simply can't see certain interactions. The local type is still polymorphic over all branches and values, and no choice has been made.

### The Partial Trace

In statistical mechanics, if you have a composite system AB described by a density matrix ρ_AB, the reduced description of A is the partial trace: ρ_A = Tr_B(ρ_AB). You integrate out B's degrees of freedom, producing a description that captures everything A can observe.

| Statistical Mechanics                           | Session Types                                          |
|-------------------------------------------------|--------------------------------------------------------|
| Joint density matrix ρ_AB                       | Global type G                                          |
| Trace out subsystem B                           | Erase non-Alice interactions                           |
| Reduced density matrix ρ_A                      | Local type L_Alice = π_Alice(G)                        |
| Information about B is lost, not committed      | Other roles' interactions are erased, not resolved     |
| Partial trace preserves all A-local observables | Projection preserves all role-local behavior (harmony) |

The crucial distinction: the global structure is preserved (the harmony theorem proves this, and projection is faithful). Alice's local type captures exactly what Alice can observe of the protocol, but the global type still exists and still constrains the full system. Nothing is broken.

### Merge as Marginalization Constraint

When projecting a choice that Alice doesn't make, the branches must be "mergeable" from Alice's perspective:

```
π_r(r' ▷ {ℓᵢ : Gᵢ}) = &{ℓᵢ : π_r(Gᵢ)}   if r ≠ r' (observer)
```

The branches π_r(G₁), π_r(G₂), ... must agree on r's observable behavior. This is the marginalization constraint: if the full joint distribution is consistent, then marginals over non-participating variables must agree regardless of the values of the marginalized-out variables. Merge checks that the partial trace is well-defined, ensuring that erasing non-local interactions doesn't produce an inconsistent local description.


## 4. Algebraic Effects as Equations of State

### The Principle

Algebraic effects define the interface between protocol structure and internal dynamics. The protocol says "send a message" and the effect handler decides *how*. This is an equation of state: the protocol provides the thermodynamic framework (state variables, constraints, allowed transitions), and the equation of state fills in the material-specific behavior.

### The Analogy

The ideal gas law PV = nRT is an equation of state that closes the thermodynamic equations by relating pressure, volume, and temperature. Without it, the equations are underdetermined. Similarly, a session type specifies the protocol structure (send, recv, branch) but says nothing about *what values* are sent or *what computation* happens locally. The effect handler closes the system.

| Thermodynamics                 | Algebraic Effects                            |
|--------------------------------|----------------------------------------------|
| State variables (P, V, T)      | Protocol state (session type position)       |
| Equations of state (PV = nRT)  | Effect handlers (how send/recv are realized) |
| Different materials, same laws | Different handlers, same protocol            |
| Ideal gas vs van der Waals     | InMemoryHandler vs TelltaleHandler           |

### Universality

The thermodynamic framework works for any material that satisfies the equation of state interface. The session type framework works for any handler that satisfies the effect signature. This is universality: the structure is independent of the specific realization.

The `EffectModel` typeclass in the VM specification is the formal equation of state interface:

```lean
class EffectModel (ε : Type) where
  EffectAction : Type        -- what operations are available
  EffectCtx : Type           -- internal state
  exec : EffectAction → EffectCtx → EffectCtx  -- how state evolves
  pre : EffectAction → EffectCtx → iProp        -- required conditions
  post : EffectAction → EffectCtx → iProp       -- guaranteed outcomes
```

Different instantiations (Aura's journal/cap/leakage effects, a testing mock, a simulation harness) are different equations of state for the same thermodynamic framework.

### The Two-Level Architecture

This gives the two-level architecture from the Gibbs correspondence its formal teeth:

```
Session layer (Markovian)     ↔  Thermodynamic laws (universal)
Effect handlers (arbitrary)   ↔  Equations of state (material-specific)
```

The session layer is provably Markovian because separation logic guarantees that effect handler state is local to each role. The frame rule ensures that role A's equation of state doesn't contaminate role B's thermodynamics.


## 5. Resource Algebras as Conserved Charges

### The Principle

Iris resource algebras generalize ownership into an algebraic structure with composition, validity, and frame-preserving updates. Their physical analogue is conserved charges, quantities that are created, split, combined, and transferred but never fabricated from nothing.

### The Auth RA is Total Energy

The authoritative resource algebra (`Auth` in `Shim/ResourceAlgebra.lean`) has two components:

- `Auth.auth a`: the authoritative element (the "true" total)
- `Auth.frag b`: a fragment (a claim on a portion)

The inclusion rule `auth_frag_included` says fragments can't exceed the whole:

```
own γ (Auth.auth a) ∗ own γ (Auth.frag b) ⊢ ⌜Included b a⌝
```

This is conservation of energy. The auth element is total system energy. Fragments are subsystem energies. You can't claim more energy than the system has. Frame-preserving updates (`auth_update`) are energy exchanges that preserve the total, following the first law of thermodynamics.

### Ghost Maps as Microstate Ledgers

The ghost map RA (`GMap` in `Shim/ResourceAlgebra.lean`) tracks key-value ownership:

```
ghost_map_auth γ m ∗ ghost_map_elem γ k v ⊢ ⌜GMap.lookup m k = some v⌝
```

The authoritative map is the full microstate ledger, recording the state of every degree of freedom. Individual elements are local observations such as "particle k has momentum v." The lookup rule says local observations must be consistent with the global ledger. Insertion and deletion are creation and annihilation of degrees of freedom.

### Splitting and Joining

Resource algebras support splitting (`cost_credit_split`) and joining (`cost_credit_join`). This is the additivity of extensive quantities:

```
cost_credit (n + m) ⊢ cost_credit n ∗ cost_credit m    -- split
cost_credit n ∗ cost_credit m ⊢ cost_credit (n + m)    -- join
```

Energy can be partitioned among subsystems and recombined. The total is preserved.


## 6. Invariants as Conservation Laws

### The Principle

An Iris invariant `inv N P` asserts: P holds now, and will hold at every future step. Anyone can temporarily open the invariant to inspect or use P, but must restore it before closing. This is a conservation law, a quantity preserved by every allowed transition.

### The Session Invariant

The session invariant in Telltale asserts that the coherence predicate holds for a session at all times:

```
inv (sessionNs sid) (session_resources sid)
```

Every send/recv step opens the invariant, verifies coherence, advances the protocol state, and closes it. This is exactly how conservation laws work in physics: every physical process must preserve them. The coherence invariant IS the conservation law of the protocol.

### Cancelable Invariants as Boundary Condition Changes

A cancelable invariant (`cinv` in `Shim/Invariants.lean`) can be permanently destroyed by consuming its cancel token. This models a conservation law that can be terminated, representing a phase transition or boundary condition change.

Session close uses `cinv_cancel` to destroy the session invariant:

```
cinv N ct P ∗ cancel_token_own ct ⊢ |={E, E∖↑N}=> ▷P
```

Once a session is closed, its conservation law no longer holds. No further operations on that session are possible. This is a phase transition or boundary condition change: the ordered phase (active session with conservation laws) transitions to a terminal phase (closed session, no constraints).

### Masks Prevent Double-Counting

The mask mechanism tracks which invariants are currently open. You can't open the same invariant twice simultaneously:

```
inv_acc : inv N P ⊢ |={E, E∖↑N}=> ▷P ∗ (▷P -∗ |={E∖↑N, E}=> emp)
```

Opening `inv N P` removes N from the mask, preventing re-entry. This prevents double-counting because you can't extract work from the same thermal gradient twice without first restoring it. The mask is a bookkeeping device that ensures each conservation law is accounted for exactly once in any given reasoning step.


## 7. Weakest Preconditions as Sufficient Conditions for Equilibrium

### The Principle

`wp Λ E e Φ` says: given the right initial resources, executing expression e reaches a state satisfying postcondition Φ. The physical analogue is sufficient conditions for reaching equilibrium.

### The Analogy

"If initial conditions lie in the simplex and the drift satisfies Lipschitz bounds, the solution exists and converges to equilibrium." That's a weakest precondition: the minimum assumptions needed to guarantee the desired outcome.

| WP Component                      | Physical Component                                     |
|-----------------------------------|--------------------------------------------------------|
| Expression e                      | Dynamical system (ODE/PDE)                             |
| Precondition (resources consumed) | Initial conditions (simplex membership, energy bounds) |
| Postcondition Φ                   | Equilibrium properties (stability, convergence)        |
| `wp_value`                        | Trivial dynamics (system already at equilibrium)       |
| `wp_bind`                         | Sequential composition of dynamical stages             |
| `wp_lift_step`                    | One step of the dynamics (Euler step)                  |

### Adequacy is the Master Theorem

The `wp_adequacy` axiom says: if the WP holds for the initial state, then every completed execution satisfies the postcondition.

```
wp_adequacy : (emp -∗ state_interp σ -∗ wp Λ ⊤ e Φ) →
              (∀ v, Φ v ⊢ ⌜φ v⌝) →
              ∀ v σ', MultiStep e σ v σ' → φ v
```

This collapses `global_ode_exists` + `simplex_forward_invariant` + `strict_lyapunov_implies_asymptotic` into a single adequacy statement: the dynamics exist, stay in the feasible region, and every terminated execution satisfies the postcondition.

### wp_lift_step is the Euler Step

Each primitive step of the VM is verified through `wp_lift_step`:

1. Open the state interpretation (inspect current system state)
2. Prove the step is possible (dynamics are well-defined)
3. Take the step (one tick of the ODE integrator)
4. Restore the state interpretation (system still in feasible region)
5. Continue with updated state

This is exactly numerical integration with invariant checking: at each Euler step, verify the solution stays in the simplex, conservation laws hold, and the Lyapunov function hasn't increased.


## 8. Cost Metering as Fuel (or Free Energy in a Closed System)

### The Principle

Cost credits in the VM specification are consumed monotonically by computation. Their physical analogue is fuel or available work. If you want a thermodynamic mapping, treat them as free energy in a closed system (monotone dissipation).

### The Analogy

A system with fuel F can do at most F worth of work before stalling. A coroutine with budget N can take at most N/minCost steps before halting.

```
cost_credit (n + m) ⊢ cost_credit n ∗ cost_credit m    -- split available work
cost_credit 1 ⊢ |==> emp                                -- consume one unit of work
```

Each VM step is an irreversible process that dissipates computational fuel. The monotone consumption law is `cost_credit_consume`.

### Two Independent Extensive Quantities

The system has two independent "conserved-then-consumed" quantities:

| Quantity            | Physical Analogue                      | Consumed By     |
|---------------------|----------------------------------------|-----------------|
| Computation credits | Fuel / available work                  | Any VM step     |
| Flow budget         | Chemical potential (reaction capacity) | Send operations |

A `send` instruction consumes both, like an exothermic reaction that does mechanical work: it uses up both fuel (computation) and chemical potential (communication capacity). The two resources are separated in Iris (frame rule), just as energy and particle number are independent extensive quantities in thermodynamics.


## 9. Monitors as Safety Interlocks / Thermostats

### The Principle

The unified session monitor (`SessionMonitor` in the VM specification) tracks local types for all active sessions and validates every instruction against the expected protocol state. It is a safety interlock or thermostat that can measure and can also prevent unsafe transitions (depending on `ViolationPolicy`).

### The Analogy

In passive mode (`ViolationPolicy.log`), the monitor is like a weakly coupled sensor: it reads protocol state without changing execution. In enforcing modes, it's a safety interlock that can stop or fault. The `monitor_sound` theorem says the monitor accepts exactly the well-typed instructions, so its readings are faithful.

| Monitor Property                 | Interlock Property        |
|----------------------------------|---------------------------|
| Accepts well-typed instructions  | Allows safe operation     |
| Rejects ill-typed instructions   | Trips on unsafe operation |
| `ViolationPolicy.log` is passive | Passive sensing mode      |
| `monitor_sound`                  | Calibration guarantee     |

The monitor is the observability and enforcement layer. It makes the abstract type-level invariants concrete and checkable at runtime, just as a thermostat or interlock makes abstract safety limits concrete and actionable.


## 10. The Guard Chain as Activation Energy

### The Principle

A configured guard chain interposes checks before every send. Each guard must pass for the operation to proceed. This is an activation energy barrier, a sequence of energy thresholds that must be cleared for a reaction to occur.

### The Analogy

A chemical reaction has an activation energy: reactants must reach a transition state before products can form. The guard chain imposes a sequence of activation barriers:

| Guard Layer (example)     | Activation Barrier                                      |
|---------------------------|---------------------------------------------------------|
| Capability check          | Electronic energy barrier (orbital symmetry)            |
| Budget or flow check      | Entropic barrier (probability of correct configuration) |
| Atomic commit             | Transition state (committed intermediate)               |
| Privacy or leakage check  | Steric barrier (spatial accessibility)                  |

The Aura example in `lean/Runtime/Examples/Aura.lean` currently uses an empty guard chain stub. Treat the layer list above as illustrative rather than implemented.

If any barrier isn't cleared, the reaction (send) doesn't proceed. The system remains in its current state with no partial progress and no side effects. This is the `acquire`/`release` pattern: each guard opens a namespace invariant, checks a condition, and either commits or aborts cleanly.

The guard chain is composable (adding a layer doesn't break existing layers) because each layer operates on an independent namespace invariant, corresponding to independent degrees of freedom in the activation complex.


## 11. Speculation as Metastability

### The Principle

Ghost sessions in the VM specification allow speculative execution where the system tentatively advances along one path, then either commits (join) or rolls back (abort). This is metastability: the system explores a local energy minimum, then either settles into it or returns to the original state.

### The Analogy

| Speculation                 | Metastability                        |
|-----------------------------|--------------------------------------|
| Fork (create ghost session) | Excitation to metastable state       |
| Speculative execution       | Dynamics within the metastable basin |
| Join (commit speculation)   | Relaxation into the true minimum     |
| Abort (discard speculation) | Return to original basin             |
| Max speculation depth       | Basin lifetime / barrier height      |

The key property: speculation is bounded (by `maxSpeculationDepth`), just as metastable states have finite lifetimes. And abort is safe because it restores the pre-speculation state exactly, just as a system returning from a metastable excitation recovers its original configuration.


## 12. Progress Tokens as Liveness Permits (Catalytic Cycle)

### The Principle

Progress tokens in the VM specification are resources that guarantee a specific session will advance. A `recv` instruction requires a progress token, and without one, the instruction can't execute.

### The Analogy

A catalyst lowers the activation energy for a reaction, guaranteeing it will proceed. Without the catalyst, the reaction may stall indefinitely. Progress tokens are closer to liveness permits: they are *consumed* by `recv`, but the session type guarantees they can always be re-minted for well-typed sessions. If you keep the catalyst analogy, it is a catalytic cycle (consume → regenerate), not a permanently free enabler.

| Progress Token                                     | Catalyst (cycle)                                     |
|----------------------------------------------------|------------------------------------------------------|
| Guarantees recv will complete                      | Guarantees reaction will proceed                     |
| Minted from well-typed sessions                    | Available from catalytic surface                     |
| Consumed by recv instruction                       | Consumed then regenerated in catalytic cycle         |
| `session_type_mints_tokens`                        | Catalyst regeneration                                |
| Starvation freedom under progress-aware scheduling | Reaction completion under sufficient catalytic cycle |


## 13. The Full Picture

Assembling all the analogies:

```
PHYSICAL SYSTEM                          TELLTALE RUNTIME
─────────────                            ───────────────

Symmetry structure (global rules)        ←→  Global session type
Coarse-graining (local views)            ←→  Choreographic projection
Conservation laws (invariants)           ←→  Coherence, session invariants
Equations of state (material)            ←→  Effect handlers
Extensive quantities (additive)          ←→  Separating conjunction
Conserved charges (accounting)           ←→  Resource algebras (Auth, GMap)
Sufficient conditions for equil.         ←→  Weakest preconditions
Fuel / available work                    ←→  Cost credits
Chemical potential (reaction cap.)       ←→  Flow budget
Activation energy (barriers)             ←→  Guard chain
Metastability (tentative basins)         ←→  Speculative execution
Liveness permits (catalytic cycle)       ←→  Progress tokens
Safety interlocks / thermostats          ←→  Session monitor
Phase transitions (boundary change)      ←→  Session close (cinv_cancel)
Locality (non-interaction)               ←→  Frame rule, erasure
Noether link (structure → preservation)  ←→  Well-typed global type → safety invariants
```

The three foundational pillars (symmetry, conservation, and extensivity) are co-equal and mutually entangled, none more fundamental than the others:

```
        Symmetry (MPST)
           /         \
   Noether link  Coarse-graining (projection)
         /             \
Conservation ----------- Extensivity
  (Invariants)   Frame rule   (Separation logic)
```

This diagram shows the three pillars and the links between them. It summarizes how projection, invariants, and separation logic reinforce each other in the proof structure.

- Symmetry → Conservation (Noether-style link): Every well-formed global type yields safety invariants. The coherence preservation theorems are conservation laws derived from the protocol's symmetry structure.
- Conservation → Extensivity (frame rule): Conservation laws compose locally because the frame rule guarantees that preserving an invariant in one subsystem does not disturb another. Without extensivity, conservation laws could not be checked modularly.
- Extensivity → Symmetry (coarse-graining): Projection produces local views by tracing out non-local interactions, which is only well-defined because the frame rule lets each role's state be handled independently. Without extensivity, the partial trace would not produce consistent local descriptions.

Each pillar needs the other two. Symmetry without conservation gives structure with no invariants. Conservation without extensivity gives global properties with no modular reasoning. Extensivity without symmetry gives independent parts with no coordination. The three together, connected by the Noether-style link, the frame rule, and compositional projection, form the theoretical core of the runtime.


## 14. Limits of the Analogy

The analogies in this document illuminate the proof structure but do not claim a deep physical equivalence. The correspondence is partial: both domains are modeled in the same logic (Iris separation logic), and the overlap lives at that algebraic level of resource composition, frame-preserving updates, conservation, and locality. Where the analogy works, it works because the proof framework is shared, not because distributed systems are thermodynamic systems.

### What transfers: the algebraic layer

The strong correspondences are structural. Separating conjunction *is* extensivity: it's the same algebraic property (additive composition of independent parts) in both domains. The frame rule *is* locality. Resource algebras *are* conserved charges. These aren't metaphors but the same mathematical objects applied to different state spaces.

### Distributed → thermodynamic: what has no physical counterpart

- Intent and adversaries. Participants have goals and can strategically deviate. Molecules follow the Hamiltonian, and there is no "Byzantine particle." Session types enforce compliance in a way that has no thermodynamic analogue because particles do not need coercion.
- Discrete choice. Branching (select/branch) is an intentional decision by a named role. Thermodynamic systems follow gradients, not decision trees. The merge operator, subtyping, and the entire branching apparatus lack clean physical counterparts.
- Named identity and topology. Roles have persistent identity and communicate over a specific graph. In statistical mechanics, particles are typically indistinguishable and interact via fields, not named channels.
- Recursion and protocol structure. Session types have recursive structure (μ-types, unfolding). Thermodynamic evolution is continuous or Markovian, and there is no analogue of "loop back to the protocol's entry point."

### Thermodynamic → distributed: what has no protocol counterpart

- Continuum, fluctuations, and criticality. Thermodynamics operates over continuous state spaces with fluctuations, phase transitions at critical points, and universality classes. Distributed systems have discrete state, finite participants, and no thermodynamic limit. Every use of "phase transition" in this document is loose.
- Entropy and equilibrium. There is no real entropy in a session-typed system. The system does not tend toward a maximum-entropy state but instead follows a prescribed protocol to termination. "Equilibrium" in §7 means "postcondition satisfied," which is teleological, not thermodynamic.
- Intensive quantities. Temperature, pressure, chemical potential (in its full thermodynamic sense), Legendre transforms, response functions: none of this transfers. The intensive or extensive duality that structures thermodynamics has no protocol counterpart.
- Reversibility. Thermodynamic processes can be quasi-static and reversible. Protocol steps are irreversible by design (you cannot un-send a message). Cost credit consumption is monotone, matching free energy dissipation, but the broader reversibility structure does not exist.

### Why partial is enough

The analogy is useful precisely because it's scoped to the proof layer. When reasoning about Telltale's formal guarantees (that sessions compose independently, that invariants are preserved, that resources aren't fabricated), the thermodynamic intuition for *why these algebraic structures work* is genuine. The physical analogies break when you move from proof structure to domain semantics: what the resources *mean* (endpoint fragments vs energy), what drives the dynamics (protocol compliance vs Hamiltonian minimization), and what the system tends toward (termination vs equilibrium).
