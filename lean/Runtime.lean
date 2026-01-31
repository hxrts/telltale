import Runtime.Compat
import Runtime.VM.TypeClasses
import Runtime.VM.Definition
import Runtime.VM.LanguageInstance
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
import Runtime.Monitor.UnifiedMonitor
import Runtime.Monitor.DomainComposition

/-! # Runtime

VM definition, Iris separation logic backend, resource algebras,
session invariants, WP rules, and adequacy.

Scaffolded per work/iris_3.md — populated incrementally.
-/
