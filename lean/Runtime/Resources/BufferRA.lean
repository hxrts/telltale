import Runtime.Shim.ResourceAlgebra

/-!
# Task 14: Buffer Resource Algebra

Ghost state for bounded buffers and refinement chain from iris_runtime_2.md §6.

## Definitions

- `BufferRA` — ghost gmap from Edge to buffer state
- `BoundedBuffer`, `enqueue`, `dequeue`
- `BufferConfig` — capacity, backpressure policy
- `bounded_refines_unbounded`
- `shared_refines_reliable` / `reliable_refines_unreliable`

Dependencies: Shim.ResourceAlgebra.
-/

set_option autoImplicit false

-- TODO: implement Task 14
