import Distributed.Families.FLP.SchedRun
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

/-! # Distributed.Families.FLP.Valency

Valency and FLP Lemma 2 (Fischer–Lynch–Paterson 1985).

* `CanDecide P C v`: some applicable schedule from `C` reaches decision `v`.
* `Bivalent P C`: both decision values remain reachable.
* `crash_decides`: from termination, every accessible configuration reaches a
  decision by a schedule in which a chosen process `p` takes no steps (the run
  in which `p` crashes is admissible because at most one process is faulty).
* `exists_bivalent_init`: some initial configuration is bivalent (FLP Lemma 2),
  via validity and a chain of initial configurations differing in one input.
-/

namespace Distributed
namespace FLP
namespace Async

variable {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg]
variable (P : Protocol Proc Msg St)

/-! ## Valency -/

/-- Decision value `v` is reachable from `C` by an applicable schedule. -/
def CanDecide (C : Config Proc Msg St) (v : Bool) : Prop :=
  ∃ σ, Appl P C σ ∧ Decided P (exec P C σ) v

/-- `C` is bivalent: both decision values are reachable. -/
def Bivalent (C : Config Proc Msg St) : Prop :=
  CanDecide P C true ∧ CanDecide P C false

variable {P}

/-- Reachable decisions of a successor are reachable decisions of `C`. -/
theorem canDecide_of_exec {C : Config Proc Msg St} {σ : Schedule Proc Msg} {v : Bool}
    (hσ : Appl P C σ) (h : CanDecide P (exec P C σ) v) : CanDecide P C v := by
  obtain ⟨τ, hτ, hd⟩ := h
  exact ⟨σ ++ τ, (appl_append P _ _ _).2 ⟨hσ, hτ⟩, by simpa using hd⟩

/-- A decided configuration can decide its value. -/
theorem canDecide_of_decided {C : Config Proc Msg St} {v : Bool} (h : Decided P C v) :
    CanDecide P C v :=
  ⟨[], trivial, h⟩

/-- Transfer a `p`-free decision to a configuration agreeing off an undecided `p`. -/
theorem canDecide_transfer {p : Proc} {C D : Config Proc Msg St} {σ : Schedule Proc Msg}
    {v : Bool} (h : AgreeOff p C D) (hσ : PFree p σ) (ha : Appl P C σ)
    (hp : P.output (C.st p) = none) (hd : Decided P (exec P C σ) v) : CanDecide P D v := by
  obtain ⟨hA, hag⟩ := agreeOff_exec P h hσ ha
  obtain ⟨q, hq⟩ := hd
  by_cases hqp : q = p
  · subst hqp
    rw [exec_st_of_pfree P C hσ, hp] at hq
    cases hq
  · exact ⟨σ, hA, q, hag.1 q hqp ▸ hq⟩

/-! ## The Crash Scheduler -/

open Classical in
/-- Stages that never schedule `p`: serve the target if it is an applicable
event of a process other than `p`, else let `r ≠ p` take a null step. -/
noncomputable def crashSched {p r : Proc} (hr : r ≠ p) (tgt : ℕ → Event Proc Msg)
    (htgt : ∀ t N, ∃ i, N ≤ i ∧ tgt i = t) : Sched P where
  stage C t := if t.1 ≠ p ∧ Applicable C t then [t] else [(r, none)]
  tgt := tgt
  Inv _ := True
  Alive q := q ≠ p
  nonempty C t _ := by split_ifs <;> simp
  appl C t _ := by
    split_ifs with h
    · exact (appl_singleton P C t).2 h.2
    · exact (appl_singleton P C _).2 trivial
  inv _ _ _ := trivial
  serves C t _ hA hap := by rw [if_pos ⟨hA, hap⟩]; exact List.mem_singleton_self t
  tgt_inf := htgt

/-- Every crash-scheduler stage is `p`-free. -/
theorem crashSched_pfree {p r : Proc} (hr : r ≠ p) (tgt : ℕ → Event Proc Msg)
    (htgt : ∀ t N, ∃ i, N ≤ i ∧ tgt i = t) :
    ∀ C t, (crashSched (P := P) hr tgt htgt).Inv C →
      ∀ e ∈ (crashSched (P := P) hr tgt htgt).stage C t, e.1 ≠ p := by
  intro C t _ e he
  simp only [crashSched] at he
  split_ifs at he with h
  · rw [List.mem_singleton.1 he]; exact h.1
  · rw [List.mem_singleton.1 he]; exact hr

/-- The crash run is admissible: only `p` may be faulty, and `p` is faulty. -/
theorem crash_admissible {p r : Proc} (hr : r ≠ p) (tgt : ℕ → Event Proc Msg)
    (htgt : ∀ t N, ∃ i, N ≤ i ∧ tgt i = t) (pre : Schedule Proc Msg)
    (C₀ : Config Proc Msg St) (h0 : Appl P C₀ pre) :
    ((crashSched (P := P) hr tgt htgt).toRun pre C₀ ⟨h0, trivial⟩ (r, none)).Admissible := by
  set S := crashSched (P := P) hr tgt htgt
  refine ⟨fun q q' hqq => ?_, fun k x hx hNF => ?_⟩
  · by_cases hq : q = p
    · exact Or.inr (S.alive_nonFaulty pre C₀ ⟨h0, trivial⟩ _ (show q' ≠ p from hq ▸ hqq.symm))
    · exact Or.inl (S.alive_nonFaulty pre C₀ ⟨h0, trivial⟩ _ hq)
  · by_cases hxp : x.1 = p
    · obtain ⟨j, hj, hev⟩ := hNF pre.length
      exact absurd (hev.trans hxp) (S.ev_after_prefix pre C₀ ⟨h0, trivial⟩ _ _
        (crashSched_pfree hr tgt htgt) hj)
    · exact S.msg_fair pre C₀ ⟨h0, trivial⟩ _ hx hxp

/-- Turn a decision at run index `k` into a `p`-free decision from the
configuration reached after the prefix. -/
theorem decided_after_prefix (r : Run P) (M : ℕ) (p : Proc)
    (hfree : ∀ j, M ≤ j → (r.ev j).1 ≠ p) {k : ℕ} {v : Bool} (hk : Decided P (r.cfg k) v) :
    ∃ σ, PFree p σ ∧ Appl P (r.cfg M) σ ∧ ∃ v, Decided P (exec P (r.cfg M) σ) v := by
  by_cases hkM : k ≤ M
  · exact ⟨[], fun _ h => (List.not_mem_nil h).elim, trivial, v, r.decided_mono hkM hk⟩
  · obtain ⟨h1, h2⟩ := r.seg_spec (k - M) M
    refine ⟨r.seg M (k - M), fun e he => ?_, h1, v, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := r.mem_seg (k - M) M he
      exact hfree j hj
    · rw [h2, show M + (k - M) = k by omega]; exact hk

variable [Finite Proc] [Countable Msg]

/-- Termination yields, from any accessible configuration and any process `p`
(with another process present), a `p`-free schedule reaching a decision. -/
theorem crash_decides (hT : Termination P) {C : Config Proc Msg St} (hC : Accessible P C)
    {p r : Proc} (hr : r ≠ p) :
    ∃ σ, PFree p σ ∧ Appl P C σ ∧ ∃ v, Decided P (exec P C σ) v := by
  haveI : Nonempty (Event Proc Msg) := ⟨(r, none)⟩
  obtain ⟨tgt, htgt⟩ := exists_tgt (Event Proc Msg)
  obtain ⟨I, pre, hpre, rfl⟩ := hC
  set S := crashSched (P := P) hr tgt htgt
  set R := S.toRun pre (initCfg P I) ⟨hpre, trivial⟩ (r, none)
  obtain ⟨k, v, hk⟩ := hT R ⟨I, rfl⟩ (crash_admissible hr tgt htgt pre _ hpre)
  have hM : R.cfg pre.length = exec P (initCfg P I) pre := S.cfg_prefix pre _ _ _
  rw [← hM]
  exact decided_after_prefix R pre.length p
    (fun j hj => S.ev_after_prefix pre _ ⟨hpre, trivial⟩ _ _ (crashSched_pfree hr tgt htgt) hj) hk

/-! ## FLP Lemma 2: A Bivalent Initial Configuration -/

/-- Discrete intermediate value step on `ℕ`. -/
theorem nat_flip (f : ℕ → Prop) : ∀ n, ¬ f 0 → f n → ∃ k, k < n ∧ ¬ f k ∧ f (k + 1) := by
  intro n
  induction n with
  | zero => intro h0 hn; exact absurd hn h0
  | succ n ih =>
    intro h0 hn
    by_cases hf : f n
    · obtain ⟨k, hk, h⟩ := ih h0 hf
      exact ⟨k, by omega, h⟩
    · exact ⟨n, by omega, hf, hn⟩

/-- Validity: a unanimous initial configuration can only decide its input. -/
theorem unanimous_canDecide (hV : Validity P) {I : Proc → Bool} {v w : Bool}
    (hI : ∀ p, I p = v) (h : CanDecide P (initCfg P I) w) : w = v := by
  obtain ⟨σ, hσ, hd⟩ := h
  exact hV I v hI σ w hσ hd

/-- Termination: every initial configuration can decide some value. -/
theorem init_canDecide (hT : Termination P) {p r : Proc} (hr : r ≠ p) (I : Proc → Bool) :
    ∃ v, CanDecide P (initCfg P I) v := by
  obtain ⟨σ, -, hσ, v, hd⟩ := crash_decides hT (accessible_init P I) hr
  exact ⟨v, σ, hσ, hd⟩

/-- Two distinct processes give every process a different partner. -/
theorem partner (h2 : ∃ p q : Proc, p ≠ q) (p : Proc) : ∃ r, r ≠ p := by
  obtain ⟨a, b, hab⟩ := h2
  by_cases hp : a = p
  · exact ⟨b, fun h => hab (hp.trans h.symm)⟩
  · exact ⟨a, hp⟩

end Async
end FLP
end Distributed
