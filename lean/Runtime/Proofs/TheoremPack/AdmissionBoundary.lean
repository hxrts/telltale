import Runtime.Proofs.TheoremPack.Inventory

/-! # Theorem-Pack Admission Boundary

Classify transported theorem families by whether they materially influence
runtime admission, serve only as black-box verification premises, or remain
documentation/background inventory.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

/-- How one transported theorem family participates in shipped assurance. -/
inductive TransportedTheoremUsageClass where
  | blackBoxPremiseOnly
  | runtimeCriticalInstantiatedPremise
  | documentationBackgroundOnly
  deriving Repr, DecidableEq, Inhabited

/-- Deterministic ledger row for one transported theorem family. -/
structure TransportedTheoremBoundaryEntry where
  key : String
  usageClass : TransportedTheoremUsageClass
  consumedByRustRuntimeAdmission : Bool
  consumedByLeanRuntimeGate : Bool
  assumptionBoundary? : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- Canonical transported-theorem admission ledger. -/
def transportedTheoremBoundaryInventory : List TransportedTheoremBoundaryEntry :=
  [ { key := "termination"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "output_condition_soundness"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "flp_lower_bound"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "flp_impossibility"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "cap_impossibility"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "quorum_geometry_safety"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "partial_synchrony_liveness"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "responsiveness"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "nakamoto_security"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "reconfiguration_safety"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "atomic_broadcast_ordering"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "accountable_safety"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "failure_detector_boundaries"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "data_availability_retrievability"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "coordination_characterization"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "crdt_envelope_and_equivalence"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "byzantine_safety_characterization"
    , usageClass := .runtimeCriticalInstantiatedPremise
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := true
    , assumptionBoundary? :=
        some "Lean theorem-pack gate only; Rust runtime admission does not currently consume this key."
    }
  , { key := "consensus_envelope"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "failure_envelope"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "protocol_machine_envelope_adherence"
    , usageClass := .runtimeCriticalInstantiatedPremise
    , consumedByRustRuntimeAdmission := true
    , consumedByLeanRuntimeGate := true
    }
  , { key := "protocol_machine_envelope_admission"
    , usageClass := .runtimeCriticalInstantiatedPremise
    , consumedByRustRuntimeAdmission := true
    , consumedByLeanRuntimeGate := true
    }
  , { key := "protocol_envelope_bridge"
    , usageClass := .runtimeCriticalInstantiatedPremise
    , consumedByRustRuntimeAdmission := true
    , consumedByLeanRuntimeGate := true
    }
  , { key := "effect_interface_bridge"
    , usageClass := .blackBoxPremiseOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_foster"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_maxweight"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_ldp"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_mean_field"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_heavy_traffic"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_mixing"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_fluid"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_concentration"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_littles_law"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  , { key := "classical_functional_clt"
    , usageClass := .documentationBackgroundOnly
    , consumedByRustRuntimeAdmission := false
    , consumedByLeanRuntimeGate := false
    }
  ]

/-- Canonical subset of transported theorems that materially influence a shipped
runtime gate or guarantee surface. -/
def runtimeCriticalTransportedTheoremBoundaryInventory :
    List TransportedTheoremBoundaryEntry :=
  transportedTheoremBoundaryInventory.filter
    (fun entry => entry.usageClass = .runtimeCriticalInstantiatedPremise)

/-- Transported-theorem keys consumed by shipped Rust runtime admission. -/
def rustRuntimeCriticalTransportedTheoremKeys : List String :=
  (runtimeCriticalTransportedTheoremBoundaryInventory.filter
      (fun entry => entry.consumedByRustRuntimeAdmission)).map
    TransportedTheoremBoundaryEntry.key

/-- Transported-theorem keys consumed by Lean theorem-pack runtime gates. -/
def leanRuntimeCriticalTransportedTheoremKeys : List String :=
  (runtimeCriticalTransportedTheoremBoundaryInventory.filter
      (fun entry => entry.consumedByLeanRuntimeGate)).map
    TransportedTheoremBoundaryEntry.key

section

variable {ν : Type u} [VerificationModel ν]

private def inventoryEnabled
    (inventory : List (String × Bool))
    (key : String) : Bool :=
  match inventory.find? (fun entry => entry.1 = key) with
  | some (_, enabled) => enabled
  | none => false

/-- Runtime-facing snapshot pairing the theorem boundary ledger with pack-local
inventory enablement. -/
def transportedTheoremBoundarySnapshot
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : ProtocolMachineTheoremPack (space := space)) :
    List (TransportedTheoremBoundaryEntry × Bool) :=
  let inventory := theoremInventory (space := space) pack
  transportedTheoremBoundaryInventory.map (fun entry =>
    (entry, inventoryEnabled inventory entry.key))

end

/-- Every runtime-critical transported theorem either has a concrete Rust
instantiation path or an explicit assumption boundary. -/
def runtimeCriticalTransportedTheoremsExplicit : Bool :=
  runtimeCriticalTransportedTheoremBoundaryInventory.all (fun entry =>
    entry.consumedByRustRuntimeAdmission || entry.assumptionBoundary?.isSome)

theorem runtimeCriticalTransportedTheoremsExplicit_true :
    runtimeCriticalTransportedTheoremsExplicit = true := by
  native_decide

end Proofs
end Runtime
