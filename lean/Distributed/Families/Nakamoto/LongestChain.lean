import Mathlib.Data.List.Infix

set_option autoImplicit false

/-! # Distributed.Families.Nakamoto.LongestChain

A concrete, deterministic longest-chain model and its common-prefix theorem.

Model (one block per round, synchronous honest view, private-branch adversary):
- a production schedule `sched : Nat → Bool` says whether round `t`'s block is
  honest (`true`) or adversarial (`false`); `mint t` is that block,
- honest blocks always extend the public (adopted) chain `pub`,
- adversarial blocks extend one private branch `pub.take fork ++ priv`,
- after each round the adversary may wait, restart its branch at any fork
  point `≤ pub.length`, or release its branch, which honest parties adopt
  only if it is strictly longer (longest-chain rule).

Combinatorial condition (not a restatement of common prefix): in every
window of at least `k` consecutive rounds, adversarial blocks do not
outnumber honest blocks (`WindowHonestMajorityUpTo`).

Theorem `common_prefix`: under that condition every reorganisation removes
fewer than `k` blocks, so any prefix that is `k` blocks deep in the public
chain at round `i` stays a prefix at every later round `j ≤ T`.

Limitations, stated precisely: this is the deterministic core of the
Bitcoin-backbone common-prefix argument. It does not model network delay,
multiple simultaneous adversarial branches, or the probabilistic analysis
showing that random mining satisfies the window condition with high
probability.
-/

namespace Distributed
namespace Nakamoto
namespace LongestChain

universe v

/-! ## Production Counting -/

/-- Honest rounds among `s, s+1, …, s+n-1`. -/
def honestIn (sched : Nat → Bool) (s : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => honestIn sched s n + if sched (s + n) then 1 else 0

/-- Adversarial rounds among `s, s+1, …, s+n-1`. -/
def advIn (sched : Nat → Bool) (s : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => advIn sched s n + if sched (s + n) then 0 else 1

/-- Every round is honest or adversarial. -/
theorem honestIn_add_advIn (sched : Nat → Bool) (s n : Nat) :
    honestIn sched s n + advIn sched s n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [honestIn, advIn]; split <;> omega

/-- Honest majority (weak) in every window of `≥ k` rounds ending by `T`. -/
def WindowHonestMajorityUpTo (sched : Nat → Bool) (k T : Nat) : Prop :=
  ∀ s, s ≤ T → ∀ n, n ≤ T → s + n ≤ T → k ≤ n → advIn sched s n ≤ honestIn sched s n

instance (sched : Nat → Bool) (k T : Nat) :
    Decidable (WindowHonestMajorityUpTo sched k T) := by
  unfold WindowHonestMajorityUpTo; infer_instance

/-- Decidable check of the window condition over a concrete schedule prefix. -/
def checkWindowHonestMajority (sched : Nat → Bool) (k T : Nat) : Bool :=
  decide (WindowHonestMajorityUpTo sched k T)

/-- Soundness of `checkWindowHonestMajority`. -/
theorem checkWindowHonestMajority_sound (sched : Nat → Bool) (k T : Nat)
    (h : checkWindowHonestMajority sched k T = true) :
    WindowHonestMajorityUpTo sched k T :=
  of_decide_eq_true h

/-! ## Protocol State and Steps -/

/-- State: public chain, private branch, and ghost bookkeeping (`start`: round
of the last branch (re)start, `baseLen`: public length at that round). -/
structure LCState (Block : Type v) where
  pub : List Block
  priv : List Block
  fork : Nat
  start : Nat
  baseLen : Nat

variable {Block : Type v}

/-- Initial state: empty chains. -/
def init : LCState Block := ⟨[], [], 0, 0, 0⟩

/-- Block production in round `t`. -/
def produce (sched : Nat → Bool) (mint : Nat → Block) (t : Nat) (s : LCState Block) :
    LCState Block :=
  if sched t then { s with pub := s.pub ++ [mint t] }
  else { s with priv := s.priv ++ [mint t] }

/-- Adversary action at the end of a round, `t` being the next round index. -/
inductive AdvAct (t : Nat) : LCState Block → LCState Block → Prop
  | wait (s : LCState Block) : AdvAct t s s
  | restart (s : LCState Block) (f : Nat) :
      f ≤ s.pub.length → AdvAct t s ⟨s.pub, [], f, t, s.pub.length⟩
  | release (s : LCState Block) :
      s.pub.length < s.fork + s.priv.length →
      AdvAct t s ⟨s.pub.take s.fork ++ s.priv, [], (s.pub.take s.fork ++ s.priv).length,
        t, (s.pub.take s.fork ++ s.priv).length⟩

/-- A run of the protocol for a schedule and block minting function. -/
def IsRun (sched : Nat → Bool) (mint : Nat → Block) (run : Nat → LCState Block) : Prop :=
  run 0 = init ∧ ∀ t, AdvAct (t + 1) (produce sched mint t (run t)) (run (t + 1))

/-! ## Invariant -/

/-- Accounting invariant at round `t`. -/
def Inv (sched : Nat → Bool) (t : Nat) (s : LCState Block) : Prop :=
  s.start ≤ t ∧ s.fork ≤ s.baseLen ∧
    s.pub.length = s.baseLen + honestIn sched s.start (t - s.start) ∧
    s.priv.length = advIn sched s.start (t - s.start)

/-- Production preserves the invariant. -/
theorem inv_produce {sched : Nat → Bool} {mint : Nat → Block} {t : Nat}
    {s : LCState Block} (h : Inv sched t s) : Inv sched (t + 1) (produce sched mint t s) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : t + 1 - s.start = (t - s.start) + 1 := by omega
  have e2 : s.start + (t - s.start) = t := by omega
  unfold produce Inv
  cases hs : sched t <;>
    simp only [hs, e1, honestIn, advIn, e2, List.length_append, List.length_singleton,
      Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Adversary actions preserve the invariant. -/
theorem inv_act {sched : Nat → Bool} {t : Nat} {s s' : LCState Block}
    (h : Inv sched t s) (hA : AdvAct t s s') : Inv sched t s' := by
  obtain ⟨_, _, _, _⟩ := h
  cases hA with
  | wait => exact ⟨by assumption, by assumption, by assumption, by assumption⟩
  | restart f hf => simp only [Inv, Nat.sub_self, honestIn, advIn]; simp; omega
  | release _ => simp only [Inv, Nat.sub_self, honestIn, advIn]; simp

/-- Every state of a run satisfies the invariant. -/
theorem inv_run {sched : Nat → Bool} {mint : Nat → Block} {run : Nat → LCState Block}
    (hR : IsRun sched mint run) (t : Nat) : Inv sched t (run t) := by
  induction t with
  | zero => rw [hR.1]; simp [Inv, init, honestIn, advIn]
  | succ t ih => exact inv_act (inv_produce ih) (hR.2 t)

/-! ## Shallow Reorganisations -/

/-- A successful release removes fewer than `k` public blocks. -/
theorem release_shallow {sched : Nat → Bool} {k T t : Nat} {s : LCState Block}
    (hI : Inv sched t s) (ht : t ≤ T) (hW : WindowHonestMajorityUpTo sched k T)
    (hRel : s.pub.length < s.fork + s.priv.length) :
    s.pub.length < s.fork + k := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  have hHA := honestIn_add_advIn sched s.start (t - s.start)
  have hw := hW s.start (by omega) (t - s.start) (by omega) (by omega)
  by_contra hc
  have := hw (by omega)
  omega

/-- A deep prefix of the public chain: `pref` is a prefix with `k` blocks above it. -/
def DeepPrefix (k : Nat) (pref : List Block) (s : LCState Block) : Prop :=
  pref <+: s.pub ∧ pref.length + k ≤ s.pub.length

/-- Production preserves deep prefixes. -/
theorem deep_produce {sched : Nat → Bool} {mint : Nat → Block} {k t : Nat}
    {pref : List Block} {s : LCState Block} (h : DeepPrefix k pref s) :
    DeepPrefix k pref (produce sched mint t s) := by
  unfold produce
  split
  · exact ⟨h.1.trans (List.prefix_append _ _), by simp; have := h.2; omega⟩
  · exact h

/-- A prefix no longer than `m` survives truncation to length `m`. -/
theorem prefix_take {pref l : List Block} {m : Nat} (h : pref <+: l)
    (hm : pref.length ≤ m) : pref <+: l.take m := by
  obtain ⟨u, rfl⟩ := h
  rw [List.take_append, List.take_of_length_le hm]
  exact List.prefix_append _ _

/-- Adversary actions preserve deep prefixes under the window condition. -/
theorem deep_act {sched : Nat → Bool} {k T t : Nat} {pref : List Block}
    {s s' : LCState Block} (hI : Inv sched t s) (ht : t ≤ T)
    (hW : WindowHonestMajorityUpTo sched k T) (hA : AdvAct t s s')
    (h : DeepPrefix k pref s) : DeepPrefix k pref s' := by
  cases hA with
  | wait => exact h
  | restart _ _ => exact h
  | release hRel =>
    have hs := release_shallow hI ht hW hRel
    have hf : s.fork ≤ s.pub.length := by have := hI.2.1; have := hI.2.2.1; omega
    refine ⟨(prefix_take h.1 (by have := h.2; omega)).trans (List.prefix_append _ _), ?_⟩
    simp only [List.length_append, List.length_take]; have := h.2; omega

/-! ## Common Prefix -/

/-- Common prefix: a prefix `k` blocks deep at round `i` remains a prefix of the
public chain at every round `j` with `i ≤ j ≤ T`. -/
theorem common_prefix {sched : Nat → Bool} {mint : Nat → Block}
    {run : Nat → LCState Block} {k T : Nat}
    (hR : IsRun sched mint run) (hW : WindowHonestMajorityUpTo sched k T)
    {i j : Nat} (hij : i ≤ j) (hjT : j ≤ T) {pref : List Block}
    (hDeep : DeepPrefix k pref (run i)) : pref <+: (run j).pub := by
  suffices ∀ j, i ≤ j → j ≤ T → DeepPrefix k pref (run j) from (this j hij hjT).1
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact hDeep
  | succ j _ ih =>
    intro hjT
    exact deep_act (inv_produce (inv_run hR j)) hjT hW (hR.2 j)
      (deep_produce (ih (by omega)))

end LongestChain
end Nakamoto
end Distributed
