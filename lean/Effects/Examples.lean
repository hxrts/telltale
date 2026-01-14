import Effects.Deployment

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
def initD : DEnv := [
  (aliceToBob, []),
  (bobToAlice, [])
]

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

/-- Initial configuration is coherent.

The key insight: with empty traces (no in-flight messages),
EdgeCoherent reduces to `(Consume from L []).isSome`,
which is always true since `Consume from L [] = some L`. -/
theorem initCoherent : Coherent initG initD := by
  intro e
  unfold EdgeCoherent
  intro Lsender Lrecv _ _
  -- The trace lookupD initD e is [] for any edge (either explicitly in initD or by default)
  -- Consume from_ Lrecv [] = some Lrecv, so .isSome is true
  -- TODO: prove that lookupD returns [] for our specific initD structure
  sorry

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

/-- Empty buffers are trivially typed (empty list has length 0 = length of empty trace) -/
theorem initBuffersTyped : BuffersTyped initG initD initBufs := by
  intro e
  unfold BufferTyped
  -- For any edge, both lookupBuf and lookupD return []
  -- We need to show ∃ h : buf.length = trace.length, ...
  -- TODO: prove that lookupBuf and lookupD return [] for our specific structures
  sorry

/-! ### Spatial Requirements -/

/-- Ping-pong requires network capability for both roles -/
def spatialReq : SpatialReq :=
  .conj (.netCapable Alice) (.netCapable Bob)

/-- A topology with both roles colocated satisfies the requirement -/
def localTopo : Topology :=
  Topology.allColocated "localhost"

theorem localTopo_satisfies : Satisfies localTopo spatialReq := by
  -- Satisfies is defined recursively on SpatialReq
  -- For .conj, it requires both conjuncts to be satisfied
  -- For .netCapable site, it requires topo.siteHasNetwork site = true
  -- TODO: needs decidability instance for Topology.siteHasNetwork
  constructor <;> sorry

/-! ### Interface -/

/-- Ping-pong interface: exports both endpoints, imports nothing -/
def interface : InterfaceType := mkDefaultInterface roles sid localTypes

/-! ### Summary -/

/-- All ping-pong certificates bundled together -/
theorem all_certificates :
    Coherent initG initD ∧
    BuffersTyped initG initD initBufs ∧
    (∀ r, r ∈ roles → ReachesComm (localTypes r)) ∧
    Satisfies localTopo spatialReq :=
  ⟨initCoherent, initBuffersTyped, allReachComm, localTopo_satisfies⟩

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

def initD : DEnv := [
  (b1ToB2, []), (b1ToS, []),
  (b2ToB1, []), (b2ToS, []),
  (sToB1, []), (sToB2, [])
]

def initBufs : Buffers := [
  (b1ToB2, []), (b1ToS, []),
  (b2ToB1, []), (b2ToS, []),
  (sToB1, []), (sToB2, [])
]

/-! ### Coherence -/

/-- Two-buyer initial state is coherent (all traces empty) -/
theorem initCoherent : Coherent initG initD := by
  intro e
  unfold EdgeCoherent
  intro Lsender Lrecv _ _
  -- TODO: prove that lookupD returns [] for our specific initD structure
  sorry

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

theorem initBuffersTyped : BuffersTyped initG initD initBufs := by
  intro e
  unfold BufferTyped
  -- TODO: prove that lookupBuf and lookupD return [] for our specific structures
  sorry

/-! ### Summary -/

theorem all_certificates :
    Coherent initG initD ∧
    BuffersTyped initG initD initBufs ∧
    (∀ r, r ∈ roles → ReachesComm (localTypes r)) :=
  ⟨initCoherent, initBuffersTyped, allReachComm⟩

end TwoBuyer

end
