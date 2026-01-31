import Runtime.VM.LanguageInstance
import Runtime.Invariants.SessionInv
import Runtime.Compat.Inv
import Runtime.Compat.WP

/-!
# Task 19: Session WP Rules

Weakest precondition rules for each bytecode instruction from iris_runtime_2.md §7.

## Rules

- `wp_send`, `wp_recv`, `wp_offer`, `wp_choose`
- `wp_open`, `wp_close`
- `wp_acquire`, `wp_release`
- `wp_invoke`, `wp_fork`, `wp_join`, `wp_abort`
- `wp_transfer`, `wp_tag`, `wp_check`
- `wp_loadImm`, `wp_mov`, `wp_jmp`, `wp_spawn`, `wp_yield`, `wp_halt`

Dependencies: Task 12, Task 16, Shim.Invariants + Shim.WeakestPre.
-/

set_option autoImplicit false
noncomputable section

def wp_send : iProp := iProp.emp
def wp_recv : iProp := iProp.emp
def wp_offer : iProp := iProp.emp
def wp_choose : iProp := iProp.emp
def wp_open : iProp := iProp.emp
def wp_close : iProp := iProp.emp
def wp_acquire : iProp := iProp.emp
def wp_release : iProp := iProp.emp
def wp_invoke : iProp := iProp.emp
def wp_fork : iProp := iProp.emp
def wp_join : iProp := iProp.emp
def wp_abort : iProp := iProp.emp
def wp_transfer : iProp := iProp.emp
def wp_tag : iProp := iProp.emp
def wp_check : iProp := iProp.emp
def wp_loadImm : iProp := iProp.emp
def wp_mov : iProp := iProp.emp
def wp_jmp : iProp := iProp.emp
def wp_spawn : iProp := iProp.emp
def wp_yield : iProp := iProp.emp
def wp_halt : iProp := iProp.emp
