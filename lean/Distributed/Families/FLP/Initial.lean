import Distributed.Families.FLP.Valency

set_option autoImplicit false

/-! # Distributed.Families.FLP.Initial

FLP Lemma 2 (Fischer–Lynch–Paterson 1985): a protocol satisfying validity and
termination (with at most one crash) has a bivalent initial configuration.

Enumerate the processes as `0, …, n-1` and let `chain k` give input `true` to
exactly the first `k` processes. `chain 0` can only decide `false` and
`chain n` only `true` (validity), so some adjacent pair `chain k`,
`chain (k+1)` flips from "cannot decide `true`" to "can decide `true`". These
differ only at process `p = k`; running the `p`-free deciding schedule given by
termination (with `p` crashed) from `chain k` transfers its decision `false`
to `chain (k+1)`, which is therefore bivalent.
-/

namespace Distributed
namespace FLP
namespace Async

variable {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg] [Fintype Proc]
variable {P : Protocol Proc Msg St}

/-- Input chain: the first `k` processes of a fixed enumeration get `true`. -/
noncomputable def chain (k : ℕ) (p : Proc) : Bool :=
  decide (((Fintype.equivFin Proc) p : ℕ) < k)

/-- `chain 0` is unanimously `false`. -/
theorem chain_zero (p : Proc) : chain 0 p = false := by
  simp [chain]

/-- `chain n` is unanimously `true` for `n` the number of processes. -/
theorem chain_card (p : Proc) : chain (Fintype.card Proc) p = true := by
  simp [chain, ((Fintype.equivFin Proc) p).isLt]

/-- Adjacent chain configurations agree off the `k`-th process. -/
theorem chain_agree {k : ℕ} (hk : k < Fintype.card Proc) :
    AgreeOff ((Fintype.equivFin Proc).symm ⟨k, hk⟩)
      (initCfg P (chain k)) (initCfg P (chain (k + 1))) := by
  refine ⟨fun q hq => ?_, rfl⟩
  have hne : ((Fintype.equivFin Proc) q : ℕ) ≠ k := fun h =>
    hq (by rw [Equiv.eq_symm_apply]; exact Fin.ext h)
  show P.init q (chain k q) = P.init q (chain (k + 1) q)
  congr 1
  simp only [chain, decide_eq_decide]
  omega

variable [Countable Msg]

/-- The flip step: if `chain k` cannot decide `true`, then `chain (k+1)` can
decide `false` (decision transfer along the `p`-crashed schedule). -/
theorem chain_step (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q) {k : ℕ}
    (hk : k < Fintype.card Proc) (hnk : ¬ CanDecide P (initCfg P (chain k)) true) :
    CanDecide P (initCfg P (chain (k + 1))) false := by
  obtain ⟨r, hr⟩ := partner h2 ((Fintype.equivFin Proc).symm ⟨k, hk⟩)
  obtain ⟨σ, hσ, ha, v, hd⟩ := crash_decides hT (accessible_init P _) hr
  have hv : v = false := by
    cases v with
    | false => rfl
    | true => exact absurd ⟨σ, ha, hd⟩ hnk
  subst hv
  exact canDecide_transfer (chain_agree hk) hσ ha (P.init_undecided _ _) hd

/-- FLP Lemma 2: some initial configuration is bivalent. -/
theorem exists_bivalent_init (hV : Validity P) (hT : Termination P)
    (h2 : ∃ p q : Proc, p ≠ q) : ∃ I, Bivalent P (initCfg P I) := by
  by_contra hno
  have h0 : ¬ CanDecide P (initCfg P (chain 0)) true := fun h =>
    absurd (unanimous_canDecide hV chain_zero h) (by decide)
  obtain ⟨a, b, hab⟩ := h2
  obtain ⟨v, hv⟩ := init_canDecide hT hab (P := P) (chain (Fintype.card Proc))
  have hn : CanDecide P (initCfg P (chain (Fintype.card Proc))) true := by
    rwa [← unanimous_canDecide hV chain_card hv]
  obtain ⟨k, hk, hnk, hk1⟩ :=
    nat_flip (fun k => CanDecide P (initCfg P (chain k)) true) _ h0 hn
  exact hno ⟨_, hk1, chain_step hT ⟨a, b, hab⟩ hk hnk⟩

end Async
end FLP
end Distributed
