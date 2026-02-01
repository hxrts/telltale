import Runtime.Compat
import Runtime.VM.TypeClasses
import Runtime.VM.SchedulerTypes
import Runtime.VM.Violation
import Runtime.VM.Config
import Runtime.VM.Program
import Runtime.VM.Definition
import Runtime.ProgramLogic.LanguageInstance
import Runtime.Resources.SessionRA
import Runtime.Resources.BufferRA
import Runtime.Resources.Arena
import Runtime.Invariants.SessionInv
import Runtime.Scheduler.Scheduler
import Runtime.Transport.Transport
import Runtime.ProgramLogic.SessionWP
import Runtime.ProgramLogic.GhostState
import Runtime.ProgramLogic.CodeLoading
import Runtime.Adequacy.Adequacy
import Runtime.Monitor.Monitor
import Runtime.Monitor.DomainComposition

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
