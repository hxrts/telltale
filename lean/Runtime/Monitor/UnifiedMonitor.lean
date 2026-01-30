import Runtime.ProgramLogic.SessionWP
import Runtime.Shim.Invariants

/-!
# Task 23: Unified Monitor and Failure Model

Monitor consistency across session kinds and crash safety
from iris_runtime_2.md §§9, 14.

## Definitions

### Unified Monitor
- `SessionKind` — protocol, guard, handler, ghost
- `WellTypedInstr` — unified typing judgment
- `SessionMonitor` — monitor state tracking all session kinds
- `monitor_sound`, `unified_monitor_preserves`
- `cross_kind_interop`

### Failure Model
- `Failure`, `FStep` — failure-aware step relation
- `Recoverable` — recovery predicate
- `crash_nonparticipant_preserves`
- `participant_failover`
- `crash_close_safe`

Dependencies: Task 19, Shim.Invariants.
-/

set_option autoImplicit false

-- TODO: implement Task 23
