import Distributed.Families.FLP.Async

set_option autoImplicit false

/-! # Distributed.Families.FLP.Runs

Runs, admissibility and the FLP correctness conditions for the asynchronous
model of `Distributed.Families.FLP.Async` (Fischer–Lynch–Paterson 1985, §2).

* A run is an infinite sequence of applicable events from a configuration.
* A process is nonfaulty in a run when it takes infinitely many steps.
* A run is admissible when at most one process is faulty and every message
  addressed to a nonfaulty process is eventually received.
* Correctness: agreement (no accessible configuration has two decision values),
  validity (unanimous input `v` forces decision `v`), and termination (every
  admissible run from an initial configuration reaches a decision).
-/

namespace Distributed
namespace FLP
namespace Async

variable {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg]
variable (P : Protocol Proc Msg St)

/-! ## Initial and Accessible Configurations -/

/-- The initial configuration for input vector `I`; the buffer is empty. -/
def initCfg (I : Proc → Bool) : Config Proc Msg St where
  st := fun p => P.init p (I p)
  buf := 0

/-- A configuration reachable by an applicable schedule from an initial one. -/
def Accessible (C : Config Proc Msg St) : Prop :=
  ∃ I σ, Appl P (initCfg P I) σ ∧ exec P (initCfg P I) σ = C

/-- Accessibility is closed under applicable schedules. -/
theorem accessible_exec {C : Config Proc Msg St} {σ : Schedule Proc Msg}
    (hC : Accessible P C) (hσ : Appl P C σ) : Accessible P (exec P C σ) := by
  obtain ⟨I, τ, hτ, rfl⟩ := hC
  exact ⟨I, τ ++ σ, (appl_append P _ _ _).2 ⟨hτ, hσ⟩, by simp⟩

/-- Initial configurations are accessible. -/
theorem accessible_init (I : Proc → Bool) : Accessible P (initCfg P I) :=
  ⟨I, [], trivial, rfl⟩

/-! ## Runs and Admissibility -/

/-- An infinite run: configurations linked by applicable events. -/
structure Run where
  cfg : ℕ → Config Proc Msg St
  ev : ℕ → Event Proc Msg
  valid : ∀ k, Applicable (cfg k) (ev k) ∧ cfg (k + 1) = apply P (cfg k) (ev k)

variable {P}

/-- A process is nonfaulty in a run when it takes infinitely many steps. -/
def Run.NonFaulty (r : Run P) (q : Proc) : Prop :=
  ∀ N, ∃ j, N ≤ j ∧ (r.ev j).1 = q

/-- FLP admissibility: at most one faulty process, and every message addressed
to a nonfaulty process is eventually received. -/
def Run.Admissible (r : Run P) : Prop :=
  (∀ q q', q ≠ q' → r.NonFaulty q ∨ r.NonFaulty q') ∧
  ∀ k (x : Proc × Msg), x ∈ (r.cfg k).buf → r.NonFaulty x.1 →
    ∃ j, k ≤ j ∧ r.ev j = (x.1, some x.2)

/-- The schedule of the `n` events of a run starting at index `a`. -/
def Run.seg (r : Run P) : ℕ → ℕ → Schedule Proc Msg
  | _, 0 => []
  | a, n + 1 => r.ev a :: r.seg (a + 1) n

/-- A run segment is an applicable schedule leading to the later configuration. -/
theorem Run.seg_spec (r : Run P) (n : ℕ) :
    ∀ a, Appl P (r.cfg a) (r.seg a n) ∧ exec P (r.cfg a) (r.seg a n) = r.cfg (a + n) := by
  induction n with
  | zero => intro a; exact ⟨trivial, rfl⟩
  | succ n ih =>
    intro a
    obtain ⟨h1, h2⟩ := ih (a + 1)
    rw [(r.valid a).2] at h1 h2
    refine ⟨⟨(r.valid a).1, h1⟩, ?_⟩
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact h2

/-- Events of a run segment are events of the run at later indices. -/
theorem Run.mem_seg (r : Run P) {e : Event Proc Msg} (n : ℕ) :
    ∀ a, e ∈ r.seg a n → ∃ j, a ≤ j ∧ r.ev j = e := by
  induction n with
  | zero => intro a h; cases h
  | succ n ih =>
    intro a h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨a, le_refl a, rfl⟩
    · obtain ⟨j, hj, hev⟩ := ih (a + 1) h
      exact ⟨j, by omega, hev⟩

/-- Configurations along a run from an accessible start are accessible. -/
theorem Run.accessible (r : Run P) (h0 : Accessible P (r.cfg 0)) (k : ℕ) :
    Accessible P (r.cfg k) := by
  obtain ⟨h1, h2⟩ := r.seg_spec k 0
  simpa [h2] using accessible_exec P h0 h1

/-- Decisions persist forward along a run. -/
theorem Run.decided_mono (r : Run P) {a b : ℕ} {v : Bool} (hab : a ≤ b)
    (h : Decided P (r.cfg a) v) : Decided P (r.cfg b) v := by
  obtain ⟨-, h2⟩ := r.seg_spec (b - a) a
  rw [show a + (b - a) = b by omega] at h2
  exact h2 ▸ decided_exec P _ h

variable (P)

/-! ## FLP Correctness Conditions -/

/-- Agreement: no accessible configuration has two different decision values. -/
def Agreement : Prop :=
  ∀ C, Accessible P C → ∀ v w, Decided P C v → Decided P C w → v = w

/-- Validity (weak, unanimity form): if every input is `v`, then every
decision reachable from that initial configuration is `v`. -/
def Validity : Prop :=
  ∀ (I : Proc → Bool) (v : Bool), (∀ p, I p = v) →
    ∀ σ w, Appl P (initCfg P I) σ → Decided P (exec P (initCfg P I) σ) w → w = v

/-- Termination: every admissible run from an initial configuration contains a
configuration in which some process has decided. -/
def Termination : Prop :=
  ∀ r : Run P, (∃ I, r.cfg 0 = initCfg P I) → r.Admissible →
    ∃ k v, Decided P (r.cfg k) v

end Async
end FLP
end Distributed
