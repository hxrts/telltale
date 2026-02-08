import Protocol.Typing.Framing.GEnvFramePre
import Protocol.Typing.Framing.GEnvFrameRight
import Protocol.Typing.Framing.GEnvFrameLeft

/-
The Problem. Provide a stable module path for GEnv framing lemmas used by
framing and preservation proofs across the protocol layer.

Solution Structure. Re-export the pre-, pre-out-right, and pre-out-left framing
lemmas from dedicated submodules.
-/
