import Distributed.Families.FLP.Initial
import Distributed.Families.FLP.Bivalence

set_option autoImplicit false

/-! # Distributed.Families.FLP.Theorem

FLP Theorem 1 (Fischer–Lynch–Paterson 1985): no consensus protocol in the
asynchronous message-passing model with at least two processes is totally
correct in spite of one crash fault. Concretely, a protocol satisfying
agreement and validity has an admissible run from an initial configuration in
which no process ever decides.

The run is built in stages from a bivalent initial configuration (Lemma 2).
Targets `(p, m)` are enumerated so each occurs infinitely often; each stage
applies Lemma 3 to the target event (or to `p`'s null step when the target
message is not in the buffer) and so ends in a bivalent configuration. All
processes take infinitely many steps and every message is eventually received,
so the run is admissible, yet every configuration on it precedes a bivalent
one and therefore (by agreement) is undecided.
-/

namespace Distributed
namespace FLP
namespace Async

variable {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg]
variable {P : Protocol Proc Msg St}

/-- With agreement, an accessible bivalent configuration is undecided. -/
theorem bivalent_undecided (hA : Agreement P) {C : Config Proc Msg St}
    (hC : Accessible P C) (hB : Bivalent P C) (v : Bool) : ¬ Decided P C v := by
  intro hd
  cases v with
  | false =>
    obtain ⟨σ, hσ, hw⟩ := hB.1
    exact absurd (hA _ (accessible_exec P hC hσ) _ _ (decided_exec P σ hd) hw) (by decide)
  | true =>
    obtain ⟨σ, hσ, hw⟩ := hB.2
    exact absurd (hA _ (accessible_exec P hC hσ) _ _ (decided_exec P σ hd) hw) (by decide)

open Classical in
/-- The event served for target `t`: `t` itself if applicable, else a null step. -/
noncomputable def serveEvent (C : Config Proc Msg St) (t : Event Proc Msg) : Event Proc Msg :=
  if Applicable C t then t else (t.1, none)

/-- The served event is always applicable. -/
theorem serveEvent_applicable (C : Config Proc Msg St) (t : Event Proc Msg) :
    Applicable C (serveEvent C t) := by
  unfold serveEvent
  split_ifs with h
  · exact h
  · trivial

variable [Finite Proc] [Countable Msg]

open Classical in
/-- Stages preserving bivalence (FLP Lemma 3 applied to the served event). -/
noncomputable def bivStage (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q)
    (C : Config Proc Msg St) (t : Event Proc Msg) : Schedule Proc Msg :=
  if h : Accessible P C ∧ Bivalent P C then
    Classical.choose (bivalent_extension hT h2 h.1 h.2 (serveEvent_applicable C t)) ++
      [serveEvent C t]
  else [(t.1, none)]

/-- Specification of a bivalence-preserving stage. -/
theorem bivStage_spec (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q)
    {C : Config Proc Msg St} (t : Event Proc Msg) (h : Accessible P C ∧ Bivalent P C) :
    ∃ σ, bivStage hT h2 C t = σ ++ [serveEvent C t] ∧ Appl P C (σ ++ [serveEvent C t]) ∧
      Bivalent P (exec P C (σ ++ [serveEvent C t])) := by
  have hs := Classical.choose_spec (bivalent_extension hT h2 h.1 h.2 (serveEvent_applicable C t))
  exact ⟨_, by rw [bivStage, dif_pos h], hs.1, hs.2⟩

/-- The stage scheduler of FLP Theorem 1. -/
noncomputable def bivSched (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q)
    (tgt : ℕ → Event Proc Msg) (htgt : ∀ t N, ∃ i, N ≤ i ∧ tgt i = t) : Sched P where
  stage := bivStage hT h2
  tgt := tgt
  Inv C := Accessible P C ∧ Bivalent P C
  Alive _ := True
  nonempty C t h := by
    obtain ⟨σ, hσ, -⟩ := bivStage_spec hT h2 t h
    simp [hσ]
  appl C t h := by
    obtain ⟨σ, hσ, ha, -⟩ := bivStage_spec hT h2 t h
    rw [hσ]; exact ha
  inv C t h := by
    obtain ⟨σ, hσ, ha, hb⟩ := bivStage_spec hT h2 t h
    rw [hσ]; exact ⟨accessible_exec P h.1 ha, hb⟩
  serves C t h _ hap := by
    obtain ⟨σ, hσ, -⟩ := bivStage_spec hT h2 t h
    rw [hσ, serveEvent, if_pos hap]
    simp
  tgt_inf := htgt

/-- A configuration on the staged run lies before a bivalent boundary, hence
is undecided. -/
theorem staged_undecided (hA : Agreement P) (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q)
    (tgt : ℕ → Event Proc Msg) (htgt : ∀ t N, ∃ i, N ≤ i ∧ tgt i = t)
    (C₀ : Config Proc Msg St) (h0 : Appl P C₀ [] ∧ (Accessible P C₀ ∧ Bivalent P C₀))
    (d : Event Proc Msg) (k : ℕ) (v : Bool) :
    ¬ Decided P (((bivSched hT h2 tgt htgt).toRun [] C₀ h0 d).cfg k) v := by
  intro hd
  set S := bivSched hT h2 tgt htgt
  have hg := S.states_good [] C₀ h0 k
  obtain ⟨hb, hc, -⟩ := S.pend_run [] C₀ _ k rfl
  have hI := S.boundary_inv [] C₀ h0 hb
  rw [hc] at hI
  exact bivalent_undecided hA hI.1 hI.2 v (decided_exec P _ hd)

/-- FLP Theorem 1: a protocol with at least two processes satisfying agreement
and validity does not terminate on all admissible runs (one crash fault). -/
theorem flp_impossibility [Fintype Proc] (hA : Agreement P) (hV : Validity P)
    (h2 : ∃ p q : Proc, p ≠ q) : ¬ Termination P := by
  intro hT
  obtain ⟨a, b, hab⟩ := h2
  haveI : Nonempty (Event Proc Msg) := ⟨(a, none)⟩
  obtain ⟨tgt, htgt⟩ := exists_tgt (Event Proc Msg)
  obtain ⟨I, hI⟩ := exists_bivalent_init hV hT ⟨a, b, hab⟩
  set S := bivSched hT ⟨a, b, hab⟩ tgt htgt
  have h0 : Appl P (initCfg P I) [] ∧ (Accessible P (initCfg P I) ∧ Bivalent P (initCfg P I)) :=
    ⟨trivial, accessible_init P I, hI⟩
  set R := S.toRun [] (initCfg P I) h0 (a, none)
  have hadm : R.Admissible :=
    ⟨fun q _ _ => Or.inl (S.alive_nonFaulty [] _ h0 _ trivial),
     fun _ _ hx _ => S.msg_fair [] _ h0 _ hx trivial⟩
  obtain ⟨k, v, hk⟩ := hT R ⟨I, rfl⟩ hadm
  exact staged_undecided hA hT ⟨a, b, hab⟩ tgt htgt _ h0 (a, none) k v hk

/-- FLP lower-bound witness: an admissible run from an initial configuration in
which no process ever decides. -/
theorem flp_nondeciding_run [Fintype Proc] (hA : Agreement P) (hV : Validity P)
    (h2 : ∃ p q : Proc, p ≠ q) :
    ∃ r : Run P, (∃ I, r.cfg 0 = initCfg P I) ∧ r.Admissible ∧ ∀ k v, ¬ Decided P (r.cfg k) v := by
  have h := flp_impossibility hA hV h2
  simp only [Termination, not_forall, not_exists] at h
  obtain ⟨r, hI, hadm, hnd⟩ := h
  exact ⟨r, hI, hadm, hnd⟩

end Async
end FLP
end Distributed
