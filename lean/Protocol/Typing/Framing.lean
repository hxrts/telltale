import Protocol.Typing.Framing.Lemmas
import Protocol.Typing.Framing.FramedPreUpdate
import Protocol.Typing.Framing.PreUpdatePreservation
import Protocol.Typing.Framing.GEnvFrame

/-
The Problem. Provide a single entry point for framing lemmas and preservation
results so downstream files can depend on a stable module path.

Solution Structure. Re-export the four submodules in dependency order: basic
lemmas, framed pre-update preservation, full pre-update preservation, and
G-frame lifting.
-/
