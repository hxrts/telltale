import Runtime.Resources.BufferRA
import Runtime.Shim.ResourceAlgebra

/-!
# Task 18: Transport Abstraction

Transport interface, specification, and refinement from iris_runtime_2.md §8.

## Definitions

- `Transport` — abstract interface (send_raw, recv_raw, connect, disconnect)
- `TransportSpec` — specification (FIFO, reliable, bounded)
- `serialize` / `deserialize`
- `serialize_roundtrip`
- `transport_refines_buffers`
- `InMemoryTransport` — reference implementation

Dependencies: Task 14, Shim.ResourceAlgebra.
-/

set_option autoImplicit false

-- TODO: implement Task 18
