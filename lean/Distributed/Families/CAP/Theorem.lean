import Distributed.Families.CAP.Register
import Mathlib.Data.Nat.Find

set_option autoImplicit false

/-! # Distributed.Families.CAP.Theorem

The CAP theorem (Gilbert–Lynch 2002, Theorem 1) in the two-node register model
of `Distributed.Families.CAP.Register`: no algorithm is both available under
partition and atomic (for a register with at least two values).

Proof (the Gilbert–Lynch construction). Partition the nodes; both tick
alternately and no message is ever delivered.
1. `run1`: node `a` is asked to `write v₁`. Availability gives a first
   response at `a`, at step `j₁`.
2. `run2`: as `run1`, then node `b` is asked to `read` at step `j₁ + 1`.
   Availability gives the first response at `b`, at step `j₂`; atomicity
   (read after a completed write) forces it to be `v₁`.
3. `run3`: as `run2` but without the write. Node `b` sees exactly the same
   events, and under partition its state depends only on its own events, so
   it returns the same value; atomicity (no write) forces it to be `v₀`.
Hence `v₁ = v₀`, a contradiction.
-/

namespace Distributed
namespace CAP
namespace Register

variable {Val Msg St : Type} (A : Algorithm Val Msg St)

/-! ## The Three Executions -/

/-- Background schedule: the two nodes tick alternately. -/
def alt (k : ℕ) : Event Val :=
  .tick (if k % 2 = 0 then .a else .b)

/-- Execution 1: `write v₁` at node `a`, then alternate ticks. -/
def run1 (v₁ : Val) (k : ℕ) : Event Val :=
  if k = 0 then .invoke .a (.write v₁) else alt k

/-- Execution 2: execution 1 plus a `read` at node `b` at step `j₁ + 1`. -/
def run2 (v₁ : Val) (j₁ : ℕ) (k : ℕ) : Event Val :=
  if k = 0 then .invoke .a (.write v₁) else if k = j₁ + 1 then .invoke .b .read else alt k

/-- Execution 3: execution 2 without the write. -/
def run3 (j₁ : ℕ) (k : ℕ) : Event Val :=
  if k = j₁ + 1 then .invoke .b .read else alt k

/-- Executions that eventually follow `alt` are fair. -/
theorem fair_of_tail {e : ℕ → Event Val} (M : ℕ) (h : ∀ k, M ≤ k → e k = alt k) : Fair e := by
  intro n N
  cases n with
  | a =>
    have hm : 2 * (N + M) % 2 = 0 := by omega
    exact ⟨2 * (N + M), by omega, by rw [h _ (by omega)]; simp [alt, hm]⟩
  | b =>
    have hm : (2 * (N + M) + 1) % 2 = 1 := by omega
    exact ⟨2 * (N + M) + 1, by omega, by rw [h _ (by omega)]; simp [alt, hm]⟩

/-- Execution 1 is partitioned. -/
theorem run1_part (v₁ : Val) : Partitioned (run1 v₁) := by
  intro k n i; unfold run1 alt; split_ifs <;> simp

/-- Execution 2 is partitioned. -/
theorem run2_part (v₁ : Val) (j₁ : ℕ) : Partitioned (run2 v₁ j₁) := by
  intro k n i; unfold run2 alt; split_ifs <;> simp

/-- Execution 3 is partitioned. -/
theorem run3_part (j₁ : ℕ) : Partitioned (Val := Val) (run3 j₁) := by
  intro k n i; unfold run3 alt; split_ifs <;> simp

/-! ## First Responses -/

/-- Availability yields a *first* response when no later invocation occurs. -/
theorem exists_responds {e : ℕ → Event Val} {n : Node} {k : ℕ}
    (hinv : ∀ i, k < i → (e i).isInvoke = false)
    (h : ∃ j, k < j ∧ (e j).node = n ∧ (outAt (Msg := Msg) A e j).isSome) :
    ∃ j, Responds (Msg := Msg) A e n k j := by
  classical
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
  refine ⟨Nat.find h, h1, h2, h3, fun i hki hij hni => ⟨?_, hinv i hki⟩⟩
  exact Option.not_isSome_iff_eq_none.1 (fun hs => Nat.find_min h hij ⟨hki, hni, hs⟩)

/-- Step 1: the write at `a` gets a first response. -/
theorem run1_responds (hAv : Available A) (v₁ : Val) :
    ∃ j₁, Responds A (run1 v₁) .a 0 j₁ := by
  refine exists_responds A (fun i hi => ?_) (hAv _ (run1_part v₁)
    (fair_of_tail 1 fun k hk => by simp [run1, show k ≠ 0 by omega]) 0 .a (.write v₁) rfl)
  simp [run1, show i ≠ 0 by omega, alt, Event.isInvoke]

/-- Step 2a: execution 2 has the same first response to the write. -/
theorem run2_write_responds {v₁ : Val} {j₁ : ℕ} (hr : Responds A (run1 v₁) .a 0 j₁) :
    Responds A (run2 v₁ j₁) .a 0 j₁ := by
  have hpre : ∀ i, i < j₁ + 1 → run1 v₁ i = run2 v₁ j₁ i := by
    intro i hi
    unfold run1 run2
    split_ifs <;> first | rfl | omega
  exact responds_transfer A (fun i _ hij _ =>
    ⟨hpre i (by omega), outAt_prefix A hpre (by omega)⟩) hr

/-- Step 2b: the read at `b` in execution 2 gets a first response. -/
theorem run2_read_responds (hAv : Available A) (v₁ : Val) (j₁ : ℕ) :
    ∃ j₂, Responds A (run2 v₁ j₁) .b (j₁ + 1) j₂ := by
  refine exists_responds A (fun i hi => ?_) (hAv _ (run2_part v₁ j₁)
    (fair_of_tail (j₁ + 2) fun k hk => ?_) (j₁ + 1) .b .read (by simp [run2]))
  · simp [run2, show i ≠ 0 by omega, show i ≠ j₁ + 1 by omega, alt, Event.isInvoke]
  · simp [run2, show k ≠ 0 by omega, show k ≠ j₁ + 1 by omega]

/-- Executions 2 and 3 agree on every event of node `b`. -/
theorem run23_agree_b (v₁ : Val) (j₁ : ℕ) :
    ∀ i, (run2 v₁ j₁ i).node = .b ∨ (run3 (Val := Val) j₁ i).node = .b →
      run2 v₁ j₁ i = run3 j₁ i := by
  intro i h
  by_cases hi : i = 0
  · subst hi
    simp [run2, run3, alt, Event.node] at h
  · simp [run2, run3, hi]

/-- Step 3: execution 3 has the same first response to the read. -/
theorem run3_read_responds {v₁ : Val} {j₁ j₂ : ℕ}
    (hr : Responds A (run2 v₁ j₁) .b (j₁ + 1) j₂) : Responds A (run3 j₁) .b (j₁ + 1) j₂ := by
  refine responds_transfer A (fun i hki _ hn => ⟨run23_agree_b v₁ j₁ i hn, ?_⟩) hr
  have he : run2 v₁ j₁ i = run3 j₁ i := run23_agree_b v₁ j₁ i hn
  have hb : (run2 v₁ j₁ i).node = .b := by rcases hn with h | h; exact h; rw [he]; exact h
  exact outAt_local A .b (run2_part v₁ j₁) (run3_part j₁) (run23_agree_b v₁ j₁) hb

/-! ## The CAP Theorem -/

/-- Gilbert–Lynch Theorem 1: in the asynchronous two-node model, no register
algorithm is both available under partition and atomic, as soon as the
register has a value `v₁` different from its initial value `v₀`. -/
theorem cap_impossible (v₀ v₁ : Val) (hne : v₁ ≠ v₀) : ¬ (Available A ∧ Atomic A v₀) := by
  rintro ⟨hAv, hNW, hWR⟩
  obtain ⟨j₁, hr1⟩ := run1_responds A hAv v₁
  obtain ⟨j₂, hr2⟩ := run2_read_responds A hAv v₁ j₁
  have hw := hWR (run2 v₁ j₁) 0 j₁ (j₁ + 1) j₂ .a .b v₁ (by simp [run2])
    (fun i _ hi0 n' v' => by unfold run2 alt; split_ifs <;> simp_all)
    (run2_write_responds A hr1) (by omega) (by simp [run2]) hr2
  have hr := hNW (run3 j₁) (j₁ + 1) j₂ .b
    (fun i _ n v => by unfold run3 alt; split_ifs <;> simp) (by simp [run3])
    (run3_read_responds A hr2)
  rw [← outAt_local A .b (run2_part v₁ j₁) (run3_part j₁) (run23_agree_b v₁ j₁) hr2.2.1,
    hw] at hr
  exact hne (by simpa using hr)

end Register
end CAP
end Distributed
