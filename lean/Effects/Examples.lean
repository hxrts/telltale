import Effects.Deployment
import Effects.Decidability

/-!
# MPST Concrete Examples

This module provides concrete protocol examples to validate the Effects library.

## Examples

1. **Ping-Pong** (2 roles): Alice sends to Bob, Bob replies
2. **Two-Buyer** (3 roles): Two buyers coordinate to purchase from a seller

Each example demonstrates:
- Constructing LocalTypes for each role
- Building GEnv and DEnv
- Proving Coherent, ReachesComm
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Ping-Pong Protocol

A simple two-party protocol:
- Alice sends a unit value to Bob
- Bob sends a unit value back to Alice
- Both terminate

```
Alice                    Bob
  |                       |
  | ------- unit -------> |
  |                       |
  | <------ unit -------- |
  |                       |
 end                     end
```
-/

namespace PingPong

/-- Role names -/
def Alice : Role := "Alice"
def Bob : Role := "Bob"

/-- Session ID for our example -/
def sid : SessionId := 0

/-- All roles in the protocol -/
def roles : RoleSet := [Alice, Bob]

/-- Alice's local type: send unit to Bob, then receive unit from Bob, then end -/
def aliceType : LocalType :=
  .send Bob .unit (.recv Bob .unit .end_)

/-- Bob's local type: receive unit from Alice, then send unit to Alice, then end -/
def bobType : LocalType :=
  .recv Alice .unit (.send Alice .unit .end_)

/-- Local type assignment function -/
def localTypes : Role → LocalType
  | "Alice" => aliceType
  | "Bob" => bobType
  | _ => .end_  -- default for other roles

/-- Alice's endpoint -/
def aliceEp : Endpoint := { sid := sid, role := Alice }

/-- Bob's endpoint -/
def bobEp : Endpoint := { sid := sid, role := Bob }

/-- Edge from Alice to Bob -/
def aliceToBob : Edge := { sid := sid, sender := Alice, receiver := Bob }

/-- Edge from Bob to Alice -/
def bobToAlice : Edge := { sid := sid, sender := Bob, receiver := Alice }

/-! ### Initial Environments -/

/-- Initial GEnv: maps endpoints to their local types -/
def initG : GEnv := [
  (aliceEp, aliceType),
  (bobEp, bobType)
]

/-- Initial DEnv: all edges have empty traces -/
def initD : DEnv :=
  updateD (updateD (∅ : DEnv) aliceToBob []) bobToAlice []

/-- Initial buffers: all empty -/
def initBufs : Buffers := [
  (aliceToBob, []),
  (bobToAlice, [])
]

/-- Initial linear context: tokens for both endpoints -/
def initLin : LinCtx := [
  (aliceEp, aliceType),
  (bobEp, bobType)
]

/-! ### Coherence Proof -/

/-- Helper: lookupD initD returns [] for any edge. -/
theorem initD_all_empty : ∀ e, lookupD initD e = [] := by
  intro e
  by_cases h1 : e = aliceToBob
  · subst h1
    simp [initD, lookupD_update_eq]
  · by_cases h2 : e = bobToAlice
    · subst h2
      simp [initD, lookupD_update_neq _ _ _ _ (by symm; exact h1), lookupD_update_eq]
    · simp [initD, lookupD_update_neq _ _ _ _ h1, lookupD_update_neq _ _ _ _ h2]

/-- Initial configuration is coherent, assuming sender endpoints exist for any receiver. -/
theorem initCoherent
    (hSenders :
      ∀ e Lrecv, lookupG initG { sid := e.sid, role := e.receiver } = some Lrecv →
        ∃ Lsender, lookupG initG { sid := e.sid, role := e.sender } = some Lsender) :
    Coherent initG initD :=
  coherent_all_empty initG initD initD_all_empty hSenders

/-! ### Deadlock Freedom -/

/-- Alice's type reaches communication (starts with send) -/
theorem aliceReachesComm : ReachesComm aliceType :=
  ReachesComm.send

/-- Bob's type reaches communication (starts with recv) -/
theorem bobReachesComm : ReachesComm bobType :=
  ReachesComm.recv

/-- All roles have types that reach communication -/
theorem allReachComm : ∀ r, r ∈ roles → ReachesComm (localTypes r) := by
  intro r hr
  simp only [roles] at hr
  rcases List.mem_cons.mp hr with rfl | hr'
  · -- r = Alice
    exact aliceReachesComm
  · -- r = Bob
    simp only [List.mem_singleton] at hr'
    subst hr'
    exact bobReachesComm

/-- Decidable checker agrees for Alice -/
theorem aliceReachesCommDecide : reachesCommDecide aliceType = true := rfl

/-- Decidable checker agrees for Bob -/
theorem bobReachesCommDecide : reachesCommDecide bobType = true := rfl

/-! ### Buffer Typing -/

/-- Helper: lookupBuf initBufs returns [] for any edge. -/
theorem initBufs_all_empty : ∀ e, lookupBuf initBufs e = [] := by
  intro e
  unfold initBufs lookupBuf
  simp only [List.lookup]
  by_cases h1 : e == aliceToBob
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : e == bobToAlice
    · simp [h2]
    · simp [h2]

/-- Empty buffers are trivially typed. -/
theorem initBuffersTyped : BuffersTyped initG initD initBufs :=
  buffersTyped_all_empty initG initD initBufs initBufs_all_empty initD_all_empty

/-! ### Spatial Requirements -/

/-- Ping-pong requires network capability for both roles -/
def spatialReq : SpatialReq :=
  .conj (.netCapable Alice) (.netCapable Bob)

/-- A topology with both roles colocated satisfies the requirement -/
def localTopo : Topology :=
  Topology.allColocated "localhost"

theorem localTopo_satisfies : Satisfies localTopo spatialReq := by
  constructor
  · -- netCapable Alice: need siteHasNetwork "Alice" = true
    simp only [Satisfies, localTopo, Topology.siteHasNetwork, Topology.allColocated,
               SiteCapabilities.enabled]
  · -- netCapable Bob: need siteHasNetwork "Bob" = true
    simp only [Satisfies, localTopo, Topology.siteHasNetwork, Topology.allColocated,
               SiteCapabilities.enabled]

/-! ### Interface -/

/-- Ping-pong interface: exports both endpoints, imports nothing -/
def interface : InterfaceType := mkDefaultInterface roles sid localTypes

/-! ### Summary -/

/-- All ping-pong certificates bundled together -/
theorem all_certificates
    (hSenders :
      ∀ e Lrecv, lookupG initG { sid := e.sid, role := e.receiver } = some Lrecv →
        ∃ Lsender, lookupG initG { sid := e.sid, role := e.sender } = some Lsender) :
    Coherent initG initD ∧
    BuffersTyped initG initD initBufs ∧
    (∀ r, r ∈ roles → ReachesComm (localTypes r)) ∧
    Satisfies localTopo spatialReq :=
  ⟨initCoherent hSenders, initBuffersTyped, allReachComm, localTopo_satisfies⟩

end PingPong

/-! ## Two-Buyer Protocol

A three-party protocol for purchasing:
- Buyer1 requests a quote from Seller
- Seller sends price to both buyers
- Buyer2 sends contribution to Buyer1
- Buyer1 decides and sends decision to Seller
- Seller confirms to Buyer1

```
Buyer1              Buyer2              Seller
  |                   |                   |
  | --------------- request ------------> |
  |                   |                   |
  | <-------------- price --------------- |
  |                   | <---- price ----- |
  |                   |                   |
  | <--- contrib ---- |                   |
  |                   |                   |
  | ---------------- ok/no -------------> |
  |                   |                   |
  | <------------- confirm -------------- |
  |                   |                   |
 end                 end                 end
```
-/

namespace TwoBuyer

/-- Role names -/
def Buyer1 : Role := "Buyer1"
def Buyer2 : Role := "Buyer2"
def Seller : Role := "Seller"

/-- Session ID -/
def sid : SessionId := 0

/-- All roles -/
def roles : RoleSet := [Buyer1, Buyer2, Seller]

/-- Buyer1's local type -/
def buyer1Type : LocalType :=
  .send Seller .string (         -- send request (item name)
    .recv Seller .nat (          -- receive price
      .recv Buyer2 .nat (        -- receive contribution from Buyer2
        .select Seller [         -- select ok or no
          ("ok", .recv Seller .bool .end_),   -- receive confirmation
          ("no", .end_)
        ])))

/-- Buyer2's local type -/
def buyer2Type : LocalType :=
  .recv Seller .nat (            -- receive price
    .send Buyer1 .nat .end_)     -- send contribution

/-- Seller's local type -/
def sellerType : LocalType :=
  .recv Buyer1 .string (         -- receive request
    .send Buyer1 .nat (          -- send price to Buyer1
      .send Buyer2 .nat (        -- send price to Buyer2
        .branch Buyer1 [         -- receive decision from Buyer1
          ("ok", .send Buyer1 .bool .end_),  -- send confirmation
          ("no", .end_)
        ])))

/-- Local type assignment -/
def localTypes : Role → LocalType
  | "Buyer1" => buyer1Type
  | "Buyer2" => buyer2Type
  | "Seller" => sellerType
  | _ => .end_

/-- Endpoints -/
def buyer1Ep : Endpoint := { sid := sid, role := Buyer1 }
def buyer2Ep : Endpoint := { sid := sid, role := Buyer2 }
def sellerEp : Endpoint := { sid := sid, role := Seller }

/-- All directed edges -/
def b1ToB2 : Edge := { sid := sid, sender := Buyer1, receiver := Buyer2 }
def b1ToS : Edge := { sid := sid, sender := Buyer1, receiver := Seller }
def b2ToB1 : Edge := { sid := sid, sender := Buyer2, receiver := Buyer1 }
def b2ToS : Edge := { sid := sid, sender := Buyer2, receiver := Seller }
def sToB1 : Edge := { sid := sid, sender := Seller, receiver := Buyer1 }
def sToB2 : Edge := { sid := sid, sender := Seller, receiver := Buyer2 }

/-! ### Initial Environments -/

def initG : GEnv := [
  (buyer1Ep, buyer1Type),
  (buyer2Ep, buyer2Type),
  (sellerEp, sellerType)
]

/-! ### Initial Trace Environment -/

/-- Empty DEnv used to build the initial traces. -/
private def initD0 : DEnv := (∅ : DEnv)

/-- One-step updates for the initial trace environment. -/
private def initD1 : DEnv := updateD initD0 b1ToB2 []
private def initD2 : DEnv := updateD initD1 b1ToS []
private def initD3 : DEnv := updateD initD2 b2ToB1 []
private def initD4 : DEnv := updateD initD3 b2ToS []
private def initD5 : DEnv := updateD initD4 sToB1 []
private def initD6 : DEnv := updateD initD5 sToB2 []

/-- Initial DEnv for the two-buyer example. -/
def initD : DEnv := initD6

def initBufs : Buffers := [
  (b1ToB2, []), (b1ToS, []),
  (b2ToB1, []), (b2ToS, []),
  (sToB1, []), (sToB2, [])
]

/-! ### Coherence -/

/-- Helper: updating with an empty trace preserves “all empty” lookups. -/
private theorem lookupD_update_empty_all
    (env : DEnv) (edge : Edge)
    (hEmpty : ∀ e, lookupD env e = []) :
    ∀ e, lookupD (updateD env edge []) e = [] := by
  intro e
  -- Split on whether we updated at this edge.
  by_cases hEq : e = edge
  · -- Updated edge: lookupD_update_eq yields [].
    subst hEq
    simpa using (lookupD_update_eq (env:=env) (e:=edge) (ts:=[]))
  · -- Other edge: lookupD_update_neq + hEmpty.
    have hLookup := lookupD_update_neq (env:=env) (e:=edge) (e':=e) (ts:=[]) (Ne.symm hEq)
    simpa [hEmpty e] using hLookup

/-- Empty DEnv has empty lookups. -/
private theorem initD0_all_empty : ∀ e, lookupD initD0 e = [] := by
  intro e
  -- Empty DEnv returns the default list.
  simpa [initD0] using (lookupD_empty (e:=e))

/-- Each update step preserves empty lookups. -/
private theorem initD1_all_empty : ∀ e, lookupD initD1 e = [] := by
  -- Apply the generic update lemma.
  simpa [initD1] using (lookupD_update_empty_all initD0 b1ToB2 initD0_all_empty)

private theorem initD2_all_empty : ∀ e, lookupD initD2 e = [] := by
  -- Apply the generic update lemma.
  simpa [initD2] using (lookupD_update_empty_all initD1 b1ToS initD1_all_empty)

private theorem initD3_all_empty : ∀ e, lookupD initD3 e = [] := by
  -- Apply the generic update lemma.
  simpa [initD3] using (lookupD_update_empty_all initD2 b2ToB1 initD2_all_empty)

private theorem initD4_all_empty : ∀ e, lookupD initD4 e = [] := by
  -- Apply the generic update lemma.
  simpa [initD4] using (lookupD_update_empty_all initD3 b2ToS initD3_all_empty)

private theorem initD5_all_empty : ∀ e, lookupD initD5 e = [] := by
  -- Apply the generic update lemma.
  simpa [initD5] using (lookupD_update_empty_all initD4 sToB1 initD4_all_empty)

private theorem initD6_all_empty : ∀ e, lookupD initD6 e = [] := by
  -- Apply the generic update lemma.
  simpa [initD6] using (lookupD_update_empty_all initD5 sToB2 initD5_all_empty)

/-- Helper: lookupD initD returns [] for any edge. -/
theorem initD_all_empty : ∀ e, lookupD initD e = [] := by
  -- Unfold to the last update and reuse the chain lemma.
  simpa [initD] using initD6_all_empty

/-- Two-buyer initial state is coherent (all traces empty), assuming sender endpoints exist. -/
theorem initCoherent
    (hSenders :
      ∀ e Lrecv, lookupG initG { sid := e.sid, role := e.receiver } = some Lrecv →
        ∃ Lsender, lookupG initG { sid := e.sid, role := e.sender } = some Lsender) :
    Coherent initG initD :=
  coherent_all_empty initG initD initD_all_empty hSenders

/-! ### Deadlock Freedom -/

theorem buyer1ReachesComm : ReachesComm buyer1Type := ReachesComm.send
theorem buyer2ReachesComm : ReachesComm buyer2Type := ReachesComm.recv
theorem sellerReachesComm : ReachesComm sellerType := ReachesComm.recv

theorem allReachComm : ∀ r, r ∈ roles → ReachesComm (localTypes r) := by
  intro r hr
  simp only [roles] at hr
  rcases List.mem_cons.mp hr with rfl | hr'
  · exact buyer1ReachesComm
  · rcases List.mem_cons.mp hr' with rfl | hr''
    · exact buyer2ReachesComm
    · simp only [List.mem_singleton] at hr''
      subst hr''
      exact sellerReachesComm

/-! ### Buffer Typing -/

/-- Helper: lookupBuf initBufs returns [] for any edge. -/
theorem initBufs_all_empty : ∀ e, lookupBuf initBufs e = [] := by
  intro e
  unfold initBufs lookupBuf
  simp only [List.lookup]
  by_cases h1 : e == b1ToB2
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : e == b1ToS
    · simp [h2]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : e == b2ToB1
      · simp [h3]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : e == b2ToS
        · simp [h4]
        · simp only [h4, Bool.false_eq_true, ↓reduceIte]
          by_cases h5 : e == sToB1
          · simp [h5]
          · simp only [h5, Bool.false_eq_true, ↓reduceIte]
            by_cases h6 : e == sToB2
            · simp [h6]
            · simp [h6]

theorem initBuffersTyped : BuffersTyped initG initD initBufs :=
  buffersTyped_all_empty initG initD initBufs initBufs_all_empty initD_all_empty

/-! ### Summary -/

theorem all_certificates
    (hSenders :
      ∀ e Lrecv, lookupG initG { sid := e.sid, role := e.receiver } = some Lrecv →
        ∃ Lsender, lookupG initG { sid := e.sid, role := e.sender } = some Lsender) :
    Coherent initG initD ∧
    BuffersTyped initG initD initBufs ∧
    (∀ r, r ∈ roles → ReachesComm (localTypes r)) :=
  ⟨initCoherent hSenders, initBuffersTyped, allReachComm⟩

end TwoBuyer

end
