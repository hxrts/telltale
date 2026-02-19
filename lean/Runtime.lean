import Runtime.VM.Model
import Runtime.VM.Composition
import Runtime.VM.API
import Runtime.VM.Runtime
import Runtime.ProgramLogic.LanguageInstance
import Runtime.Resources.SessionRA
import Runtime.Resources.BufferRA
import Runtime.Resources.Arena
import Runtime.Invariants.SessionInv
import Runtime.Transport
import Runtime.ProgramLogic.SessionWP
import Runtime.ProgramLogic.GhostState
import Runtime.ProgramLogic.CodeLoading
import Runtime.Adequacy.Adequacy
import Runtime.Proofs.Concurrency
import Runtime.Proofs.ConcurrencyThreaded
import Runtime.Proofs.ProgressApi
import Runtime.Proofs.SchedulerApi
import Runtime.Proofs.EffectBisim
import Runtime.Proofs.VM.BridgeStrengthening
import Runtime.Proofs.VM.Speculation
import Runtime.Proofs.InvariantSpace
import Runtime.Proofs.Adapters.Progress
import Runtime.Proofs.Adapters.Classical
import Runtime.Proofs.Adapters.Distributed
import Runtime.Proofs.TheoremPack.API
import Runtime.Proofs.SchedulerTheoremPack
import Runtime.Proofs.Examples.ComposedProofPack
import IrisExtractionInstance

/- 
The Problem. Provide a single entry point that re-exports the runtime spec
and its proof layers for downstream modules and documentation.

Solution Structure. Import the VM spec, resources, program logic, and
monitor/adequacy modules in one place.
-/

/-! # Runtime

VM definition, Iris separation logic backend, resource algebras,
session invariants, WP rules, and adequacy.

Scaffolded per work/iris_3.md — populated incrementally.
-/
