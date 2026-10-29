import Mathlib.Data.Multiset.AddSub
import Mathlib.Logic.Function.Basic

set_option autoImplicit false

/-! # Distributed.Families.FLP.Async

The asynchronous message-passing model of Fischer, Lynch and Paterson
("Impossibility of Distributed Consensus with One Faulty Process", JACM 1985).

* A protocol is a family of deterministic process automata. Each process has an
  input bit (fixed in its initial state), a write-once output register
  (`output`), and a transition function consuming either a message addressed to
  it or the null value `none`, producing a new local state and a finite
  multiset of sent messages.
* A configuration is the vector of local states plus the message buffer, a
  multiset of `(recipient, message)` pairs.
* An event `(p, m)` is applicable when `m = none` or `(p, m)` is in the buffer.

This file develops the purely operational facts used by the impossibility
proof: schedule execution, persistence of applicability and of decisions,
the FLP commutativity lemma, and the indistinguishability ("transfer") lemma
for schedules that do not involve a given process.
-/

/-
The Problem. The FLP family previously assumed the valency argument as a premise.
Solution Structure. Provide a concrete, textbook asynchronous model whose
operational lemmas are proved here and consumed by the valency development.
-/

namespace Distributed
namespace FLP
namespace Async

/-! ## Protocols, Configurations, Events -/

/-- A deterministic FLP consensus protocol over processes `Proc`, messages `Msg`
and local states `St`. Output registers start undecided and are write-once. -/
structure Protocol (Proc Msg St : Type) where
  /-- Initial local state of process `p` with input bit `b`. -/
  init : Proc → Bool → St
  /-- Deterministic local step: new state and the multiset of sent messages. -/
  trans : Proc → St → Option Msg → St × Multiset (Proc × Msg)
  /-- Output register (`none` is FLP's undecided value `b`). -/
  output : St → Option Bool
  /-- Output registers start undecided. -/
  init_undecided : ∀ p b, output (init p b) = none
  /-- Output registers are write-once. -/
  output_stable : ∀ p s m b, output s = some b → output (trans p s m).1 = some b

/-- A global configuration: local states and the message buffer. -/
structure Config (Proc Msg St : Type) where
  st : Proc → St
  buf : Multiset (Proc × Msg)

/-- An event: a process receiving a message (or the null message `none`). -/
abbrev Event (Proc Msg : Type) := Proc × Option Msg

/-- A schedule is a finite list of events. -/
abbrev Schedule (Proc Msg : Type) := List (Event Proc Msg)

variable {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg]

/-- The message consumed by an event is present in buffer `B`. -/
def InBuf (B : Multiset (Proc × Msg)) : Event Proc Msg → Prop
  | (_, none) => True
  | (p, some m) => (p, m) ∈ B

/-- An event is applicable when its message is in the buffer (null always is). -/
def Applicable (C : Config Proc Msg St) (e : Event Proc Msg) : Prop :=
  InBuf C.buf e

/-- Remove the message consumed by an event from the buffer. -/
def consume (B : Multiset (Proc × Msg)) : Event Proc Msg → Multiset (Proc × Msg)
  | (_, none) => B
  | (p, some m) => B.erase (p, m)

variable (P : Protocol Proc Msg St)

/-- Apply one event to a configuration. -/
def apply (C : Config Proc Msg St) (e : Event Proc Msg) : Config Proc Msg St where
  st := Function.update C.st e.1 (P.trans e.1 (C.st e.1) e.2).1
  buf := consume C.buf e + (P.trans e.1 (C.st e.1) e.2).2

/-- Execute a schedule (applicability is tracked separately by `Appl`). -/
def exec : Config Proc Msg St → Schedule Proc Msg → Config Proc Msg St
  | C, [] => C
  | C, e :: σ => exec (apply P C e) σ

/-- Every event of the schedule is applicable when it is reached. -/
def Appl : Config Proc Msg St → Schedule Proc Msg → Prop
  | _, [] => True
  | C, e :: σ => Applicable C e ∧ Appl (apply P C e) σ

/-- Configuration `C` has decision value `v` (some output register holds `v`). -/
def Decided (C : Config Proc Msg St) (v : Bool) : Prop :=
  ∃ p, P.output (C.st p) = some v

/-- The schedule contains no step of process `p`. -/
def PFree (p : Proc) (σ : Schedule Proc Msg) : Prop :=
  ∀ e ∈ σ, e.1 ≠ p

/-! ## Schedule Algebra -/

/-- Executing a concatenation executes the parts in sequence. -/
@[simp] theorem exec_append (C : Config Proc Msg St) (σ τ : Schedule Proc Msg) :
    exec P C (σ ++ τ) = exec P (exec P C σ) τ := by
  induction σ generalizing C with
  | nil => rfl
  | cons e σ ih => exact ih _

/-- Applicability of a concatenation splits into its parts. -/
theorem appl_append (C : Config Proc Msg St) (σ τ : Schedule Proc Msg) :
    Appl P C (σ ++ τ) ↔ Appl P C σ ∧ Appl P (exec P C σ) τ := by
  induction σ generalizing C with
  | nil => simp [Appl, exec]
  | cons e σ ih => simp [Appl, exec, ih, and_assoc]

/-- A singleton schedule is applicable iff its event is. -/
@[simp] theorem appl_singleton (C : Config Proc Msg St) (e : Event Proc Msg) :
    Appl P C [e] ↔ Applicable C e := by
  simp [Appl]

/-! ## Persistence -/

/-- A buffered message survives consumption by a different event. -/
theorem inBuf_consume_of_ne {B : Multiset (Proc × Msg)} {e e' : Event Proc Msg}
    (h : InBuf B e) (hne : e' ≠ e) : InBuf (consume B e') e := by
  rcases e with ⟨p, _ | m⟩
  · trivial
  rcases e' with ⟨q, _ | m'⟩
  · exact h
  have : (p, m) ≠ (q, m') := fun hq => hne (by cases hq; rfl)
  exact (Multiset.mem_erase_of_ne this).2 h

/-- Adding messages preserves buffered messages. -/
theorem inBuf_add {B : Multiset (Proc × Msg)} {e : Event Proc Msg}
    (S : Multiset (Proc × Msg)) (h : InBuf B e) : InBuf (B + S) e := by
  rcases e with ⟨p, _ | m⟩
  · trivial
  · exact Multiset.mem_add.2 (Or.inl h)

/-- FLP: an applicable event stays applicable after any other event. -/
theorem applicable_apply_of_ne {C : Config Proc Msg St} {e e' : Event Proc Msg}
    (h : Applicable C e) (hne : e' ≠ e) : Applicable (apply P C e') e :=
  inBuf_add _ (inBuf_consume_of_ne h hne)

/-- An applicable event stays applicable along any schedule avoiding it. -/
theorem applicable_exec_of_not_mem {C : Config Proc Msg St} {e : Event Proc Msg}
    {σ : Schedule Proc Msg} (h : Applicable C e) (hσ : e ∉ σ) :
    Applicable (exec P C σ) e := by
  induction σ generalizing C with
  | nil => exact h
  | cons a σ ih =>
    simp only [List.mem_cons, not_or] at hσ
    exact ih (applicable_apply_of_ne P h (Ne.symm hσ.1)) hσ.2

/-- Decision values persist across one event (write-once outputs). -/
theorem decided_apply {C : Config Proc Msg St} {v : Bool} (e : Event Proc Msg)
    (h : Decided P C v) : Decided P (apply P C e) v := by
  rcases h with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  by_cases hqe : q = e.1
  · subst hqe
    simp only [apply, Function.update_self]
    exact P.output_stable _ _ _ _ hq
  · simp only [apply, Function.update_of_ne hqe]
    exact hq

/-- Decision values persist along schedules. -/
theorem decided_exec {C : Config Proc Msg St} {v : Bool} (σ : Schedule Proc Msg)
    (h : Decided P C v) : Decided P (exec P C σ) v := by
  induction σ generalizing C with
  | nil => exact h
  | cons e σ ih => exact ih (decided_apply P e h)

/-! ## Commutativity (FLP Lemma 1) -/

/-- Consuming an applicable event commutes with adding messages. -/
theorem consume_add {B : Multiset (Proc × Msg)} {e : Event Proc Msg}
    (S : Multiset (Proc × Msg)) (h : InBuf B e) : consume (B + S) e = consume B e + S := by
  rcases e with ⟨p, _ | m⟩
  · rfl
  · exact Multiset.erase_add_left_pos S h

/-- Consumption of two events commutes. -/
theorem consume_comm (B : Multiset (Proc × Msg)) (e e' : Event Proc Msg) :
    consume (consume B e) e' = consume (consume B e') e := by
  rcases e with ⟨p, _ | m⟩ <;> rcases e' with ⟨q, _ | m'⟩ <;> simp [consume, Multiset.erase_comm]

/-- Buffer component of the diamond for two applicable events. -/
theorem buf_diamond (C : Config Proc Msg St) {e e' : Event Proc Msg}
    (hne : e.1 ≠ e'.1) (h : Applicable C e) (h' : Applicable C e') :
    (apply P (apply P C e) e').buf = (apply P (apply P C e') e).buf := by
  have hne' : e' ≠ e := fun hq => hne (by rw [hq])
  have hne'' : e ≠ e' := fun hq => hne' hq.symm
  simp only [apply, Function.update_of_ne hne.symm, Function.update_of_ne hne]
  rw [consume_add _ (inBuf_consume_of_ne h' hne''), consume_add _ (inBuf_consume_of_ne h hne'),
    consume_comm]
  rw [Multiset.add_assoc, Multiset.add_assoc]
  congr 1
  exact Multiset.add_comm _ _

/-- Configurations are equal when their states and buffers are. -/
theorem Config.ext' {C D : Config Proc Msg St} (h1 : C.st = D.st) (h2 : C.buf = D.buf) :
    C = D := by
  cases C; cases D; simp_all

/-- FLP Lemma 1 (single events): steps of distinct processes commute. -/
theorem apply_comm (C : Config Proc Msg St) {e e' : Event Proc Msg}
    (hne : e.1 ≠ e'.1) (h : Applicable C e) (h' : Applicable C e') :
    apply P (apply P C e) e' = apply P (apply P C e') e := by
  have hb := buf_diamond P C hne h h'
  have hs : (apply P (apply P C e) e').st = (apply P (apply P C e') e).st := by
    simp only [apply, Function.update_of_ne hne.symm, Function.update_of_ne hne]
    exact Function.update_comm hne _ _ _
  exact Config.ext' hs hb

/-- FLP Lemma 1: an event of `p` commutes with a `p`-free schedule. -/
theorem commute_pfree {C : Config Proc Msg St} {e : Event Proc Msg} {σ : Schedule Proc Msg}
    (hσ : PFree e.1 σ) (he : Applicable C e) (ha : Appl P C σ) :
    Appl P (apply P C e) σ ∧ exec P (apply P C e) σ = apply P (exec P C σ) e ∧
      Applicable (exec P C σ) e := by
  induction σ generalizing C with
  | nil => exact ⟨trivial, rfl, he⟩
  | cons a σ ih =>
    have hpa : a.1 ≠ e.1 := hσ a (List.mem_cons_self ..)
    have hne : a ≠ e := fun hq => hpa (by rw [hq])
    have hrest : PFree e.1 σ := fun x hx => hσ x (List.mem_cons_of_mem _ hx)
    obtain ⟨h1, h2, h3⟩ :=
      ih hrest (applicable_apply_of_ne P he hne) ha.2
    refine ⟨⟨applicable_apply_of_ne P ha.1 (Ne.symm hne), ?_⟩, ?_, h3⟩
    · rw [apply_comm P C (Ne.symm hpa) he ha.1]; exact h1
    · show exec P (apply P (apply P C e) a) σ = _
      rw [apply_comm P C (Ne.symm hpa) he ha.1]; exact h2

/-! ## Indistinguishability of `p`-free Schedules -/

/-- Two configurations agree everywhere except possibly at process `p`. -/
def AgreeOff (p : Proc) (C D : Config Proc Msg St) : Prop :=
  (∀ q, q ≠ p → C.st q = D.st q) ∧ C.buf = D.buf

/-- A step of a process other than `p` preserves agreement off `p`. -/
theorem agreeOff_apply {p : Proc} {C D : Config Proc Msg St} (h : AgreeOff p C D)
    (e : Event Proc Msg) (he : e.1 ≠ p) : AgreeOff p (apply P C e) (apply P D e) := by
  have hs : C.st e.1 = D.st e.1 := h.1 _ he
  refine ⟨fun q hq => ?_, ?_⟩
  · by_cases hqe : q = e.1
    · subst hqe; simp [apply, hs]
    · simp [apply, Function.update_of_ne hqe, h.1 q hq]
  · simp [apply, hs, h.2]

/-- Transfer lemma: a `p`-free schedule behaves identically on configurations
that agree off `p`. -/
theorem agreeOff_exec {p : Proc} {C D : Config Proc Msg St} {σ : Schedule Proc Msg}
    (h : AgreeOff p C D) (hσ : PFree p σ) (ha : Appl P C σ) :
    Appl P D σ ∧ AgreeOff p (exec P C σ) (exec P D σ) := by
  induction σ generalizing C D with
  | nil => exact ⟨trivial, h⟩
  | cons a σ ih =>
    have hap : a.1 ≠ p := hσ a (List.mem_cons_self ..)
    have hrest : PFree p σ := fun x hx => hσ x (List.mem_cons_of_mem _ hx)
    obtain ⟨h1, h2⟩ := ih (agreeOff_apply P h a hap) hrest ha.2
    refine ⟨⟨?_, h1⟩, h2⟩
    have hb : Applicable C a = Applicable D a := by simp [Applicable, h.2]
    exact hb ▸ ha.1

/-- A `p`-free schedule leaves the local state of `p` untouched. -/
theorem exec_st_of_pfree {p : Proc} (C : Config Proc Msg St) {σ : Schedule Proc Msg}
    (hσ : PFree p σ) : (exec P C σ).st p = C.st p := by
  induction σ generalizing C with
  | nil => rfl
  | cons a σ ih =>
    have hap : p ≠ a.1 := fun hq => hσ a (List.mem_cons_self ..) hq.symm
    rw [show exec P C (a :: σ) = exec P (apply P C a) σ from rfl,
      ih _ (fun x hx => hσ x (List.mem_cons_of_mem _ hx))]
    simp [apply, Function.update_of_ne hap]

end Async
end FLP
end Distributed
