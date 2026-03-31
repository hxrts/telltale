import Runtime.ProtocolMachine.Model
import Runtime.ProtocolMachine.Composition
import Runtime.ProtocolMachine.API
import Runtime.ProtocolMachine.Runtime
import Runtime.ProgramLogic.LanguageInstance
import Runtime.Resources.SessionRA
import Runtime.Resources.BufferRA
import Runtime.Resources.Arena
import Runtime.Invariants
import Runtime.Transport
import Runtime.Simulation
import Runtime.ProgramLogic.SessionWP
import Runtime.ProgramLogic.GhostState
import Runtime.ProgramLogic.CodeLoading
import Runtime.Adequacy.Adequacy
import Runtime.Proofs.Concurrency
import Runtime.Proofs.ConcurrencyThreaded
import Runtime.Proofs.ProgressApi
import Runtime.Proofs.SchedulerApi
import Runtime.Proofs.EffectBisim.Core
import Runtime.Proofs.EffectBisim.Bridge
import Runtime.Proofs.EffectBisim.Congruence
import Runtime.Proofs.EffectBisim.ConfigEquivBridge
import Runtime.Proofs.EffectBisim.RationalFragment
import Runtime.Proofs.BridgeStrengthening
import Runtime.Proofs.ReconfigurationObserver
import Runtime.Proofs.AuthorityMetatheory
import Runtime.Proofs.Capabilities
import Runtime.Proofs.CapabilityModel
import Runtime.Proofs.Conservation.API
import Runtime.Proofs.Lowering.API
import Runtime.Proofs.ProtocolMachine.Effects
import Runtime.Proofs.ProtocolMachine.ConcreteRefinement
import Runtime.Proofs.ProtocolMachine.Speculation
import Runtime.Proofs.InvariantSpace
import Runtime.Proofs.Adapters.Progress
import Runtime.Proofs.Adapters.Classical
import Runtime.Proofs.TheoremPack.AdmissionBoundary
import Runtime.Proofs.TheoremPack.API
import Runtime.Proofs.SchedulerTheoremPack
import IrisExtractionInstance

/- 
The Problem. Provide a single entry point that re-exports the runtime spec
and its proof layers for downstream modules and documentation.

Solution Structure. Import the protocol machine spec, resources, program logic, and
monitor/adequacy modules in one place.
-/

/-! # Runtime

protocol machine definition, Iris separation logic backend, resource algebras,
session invariants, WP rules, and adequacy.
-/
