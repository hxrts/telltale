import Runtime.VM.TypeClasses

/-!
# Task 11: Bytecode VM Definition

Bytecode instruction set, registers, coroutine structure, and single-step
execution from iris_runtime_2.md §3.

## Definitions

- `Reg`, `Addr`, `Imm` — register file types
- `Instr` — full instruction set
- `CodeImage` — instruction array
- `RegFile` — register contents
- `CoroutineState` — pc, registers, stack, status
- `VMState` — coroutines, arena, session store, scheduler state, buffers
- `ExecResult` — step outcomes
- `execInstr` — single instruction execution

Dependencies: Task 10.
-/

set_option autoImplicit false

-- TODO: implement Task 11
