import Protocol.Environments.Part1
import Protocol.Environments.Part2

/-!
# MPST Environments

This module defines the runtime environments for multiparty session types:

- `Store`: Variable store mapping variables to runtime values
- `SEnv`: Type environment mapping variables to value types
- `GEnv`: Session environment mapping endpoints to local types
- `DEnv`: Delayed type environment for in-flight message traces per directed edge
- `Buffers`: Per-edge FIFO message buffers keyed by (sid, from, to)

The key difference from binary session types is that buffers and type traces
are keyed by **directed edges** `(sid, from, to)` rather than endpoints.
-/
