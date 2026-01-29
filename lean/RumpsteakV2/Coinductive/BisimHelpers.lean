import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
The Problem. EQ2C bisimulation proofs require constructing bisimulation relations
from head equality. When two coinductive types have matching heads, we need to
show they are EQ2C-equivalent by building appropriate witness relations.

The difficulty is that each head case (end, var, send, recv) requires a different
bisimulation construction, and we need to handle environment-aware EQ2CE as well.

Solution Structure.
1. Branch relation helpers for ofFn lists
2. Observable lemmas: head determines observability
3. EQ2C head lemmas: matching heads implies EQ2C
4. Mu eta: reconstruct mu nodes from dest
5. EQ2CE → EQ2C erasure lemmas
-/

namespace RumpsteakV2.Coinductive

open Classical
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## Branch relation helpers (ofFn) -/

lemma toCoindBranches_ofFn {n : Nat} (f : Fin n → (Label × LocalTypeR)) :
    toCoindBranches (List.ofFn f) =
      List.ofFn (fun i => ((f i).1, toCoind (f i).2)) := by
  induction n with
  | zero =>
      simp [List.ofFn_zero, toCoindBranches]
  | succ n ih =>
      simp [List.ofFn_succ, toCoindBranches, ih]

lemma BranchesRelCE_ofFn {R : Rel} {ρ : EnvPair} {n : Nat}
    {f g : Fin n → (Label × LocalTypeC)}
    (h : ∀ i, (f i).1 = (g i).1 ∧ R ρ (f i).2 (g i).2) :
    BranchesRelCE R ρ (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero =>
      simp [List.ofFn_zero, BranchesRelCE]
  | succ n ih =>
      have h0 := h ⟨0, Nat.succ_pos _⟩
      have h' : ∀ i : Fin n, (f i.succ).1 = (g i.succ).1 ∧ R ρ (f i.succ).2 (g i.succ).2 := by
        intro i
        simpa using h i.succ
      rcases h0 with ⟨hlabel, hrel⟩
      simp [List.ofFn_succ, BranchesRelCE]
      exact ⟨⟨hlabel, hrel⟩, ih h'⟩

lemma BranchesRelC_ofFn {n : Nat} {f g : Fin n → (Label × LocalTypeC)}
    (h : ∀ i, (f i).1 = (g i).1 ∧ EQ2C (f i).2 (g i).2) :
    BranchesRelC EQ2C (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero =>
      simp [List.ofFn_zero, BranchesRelC]
  | succ n ih =>
      have h0 := h ⟨0, Nat.succ_pos _⟩
      have h' :
          ∀ i : Fin n, (f i.succ).1 = (g i.succ).1 ∧ EQ2C (f i.succ).2 (g i.succ).2 := by
        intro i
        simpa using h i.succ
      rcases h0 with ⟨hlabel, hrel⟩
      simp [List.ofFn_succ, BranchesRelC]
      exact ⟨⟨hlabel, hrel⟩, ih h'⟩

/-! ## Observable lemmas -/

lemma observable_of_head_end {t : LocalTypeC} (h : head t = .end) : ObservableC t := by
  refine ObservableC.is_end ?_
  exact ⟨t, Relation.ReflTransGen.refl, h⟩

lemma observable_of_head_var {t : LocalTypeC} {v : String} (h : head t = .var v) :
    ObservableC t := by
  refine ObservableC.is_var v ?_
  exact ⟨t, Relation.ReflTransGen.refl, h⟩

lemma observable_of_head_send {t : LocalTypeC} {p : String} {labels : List Label}
    (h : head t = .send p labels) : ObservableC t := by
  refine ObservableC.is_send p (branchesOf t) ?_
  exact ⟨t, labels, Relation.ReflTransGen.refl, h, rfl⟩

lemma observable_of_head_recv {t : LocalTypeC} {p : String} {labels : List Label}
    (h : head t = .recv p labels) : ObservableC t := by
  refine ObservableC.is_recv p (branchesOf t) ?_
  exact ⟨t, labels, Relation.ReflTransGen.refl, h, rfl⟩

/-! ## EQ2C head lemmas -/

/-- Two types with end heads are EQ2C-equivalent. -/
lemma EQ2C_end_head {a b : LocalTypeC}
    (ha : head a = .end) (hb : head b = .end) : EQ2C a b := by
  let R : LocalTypeC → LocalTypeC → Prop := fun x y => head x = .end ∧ head y = .end
  have hR : IsBisimulationC R := by
    intro x y hxy
    have obs_x : ObservableC x := observable_of_head_end hxy.1
    have obs_y : ObservableC y := observable_of_head_end hxy.2
    have hx : UnfoldsToEndC x := ⟨x, Relation.ReflTransGen.refl, hxy.1⟩
    have hy : UnfoldsToEndC y := ⟨y, Relation.ReflTransGen.refl, hxy.2⟩
    exact ⟨obs_x, obs_y, ObservableRelC.is_end hx hy⟩
  exact ⟨R, hR, ⟨ha, hb⟩⟩

/-- Two types with matching var heads are EQ2C-equivalent. -/
lemma EQ2C_var_head {a b : LocalTypeC} {v : String}
    (ha : head a = .var v) (hb : head b = .var v) : EQ2C a b := by
  let R : LocalTypeC → LocalTypeC → Prop := fun x y => head x = .var v ∧ head y = .var v
  have hR : IsBisimulationC R := by
    intro x y hxy
    have obs_x : ObservableC x := observable_of_head_var hxy.1
    have obs_y : ObservableC y := observable_of_head_var hxy.2
    have hx : UnfoldsToVarC x v := ⟨x, Relation.ReflTransGen.refl, hxy.1⟩
    have hy : UnfoldsToVarC y v := ⟨y, Relation.ReflTransGen.refl, hxy.2⟩
    exact ⟨obs_x, obs_y, ObservableRelC.is_var v hx hy⟩
  exact ⟨R, hR, ⟨ha, hb⟩⟩

/-- Two types with matching send heads and related branches are EQ2C-equivalent. -/
lemma EQ2C_send_head {a b : LocalTypeC} {p : String} {labels labels' : List Label}
    (ha : head a = .send p labels) (hb : head b = .send p labels')
    (hbr : BranchesRelC EQ2C (branchesOf a) (branchesOf b)) : EQ2C a b := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun x y => (x = a ∧ y = b) ∨ EQ2C x y
  have hR' : IsBisimulationC R' := by
    intro x y hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_x, obs_y, hobs⟩ := hR x y hrel
        have hobs' : ObservableRelC R' x y :=
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_x, obs_y, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨hx, hy⟩
        have hx' : head x = .send p labels := by
          simpa [hx] using ha
        have hy' : head y = .send p labels' := by
          simpa [hy] using hb
        have obs_x : ObservableC x := observable_of_head_send hx'
        have obs_y : ObservableC y := observable_of_head_send hy'
        have hbr0 : BranchesRelC R' (branchesOf a) (branchesOf b) :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        have hbr' : BranchesRelC R' (branchesOf x) (branchesOf y) := by
          simpa [hx, hy] using hbr0
        have ha_send : CanSendC x p (branchesOf x) :=
          ⟨x, labels, Relation.ReflTransGen.refl, hx', rfl⟩
        have hb_send : CanSendC y p (branchesOf y) :=
          ⟨y, labels', Relation.ReflTransGen.refl, hy', rfl⟩
        exact ⟨obs_x, obs_y,
          ObservableRelC.is_send p (branchesOf x) (branchesOf y) ha_send hb_send hbr'⟩
  exact ⟨R', hR', Or.inl ⟨rfl, rfl⟩⟩

/-- Two types with matching recv heads and related branches are EQ2C-equivalent. -/
lemma EQ2C_recv_head {a b : LocalTypeC} {p : String} {labels labels' : List Label}
    (ha : head a = .recv p labels) (hb : head b = .recv p labels')
    (hbr : BranchesRelC EQ2C (branchesOf a) (branchesOf b)) : EQ2C a b := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun x y => (x = a ∧ y = b) ∨ EQ2C x y
  have hR' : IsBisimulationC R' := by
    intro x y hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_x, obs_y, hobs⟩ := hR x y hrel
        have hobs' : ObservableRelC R' x y :=
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_x, obs_y, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨hx, hy⟩
        have hx' : head x = .recv p labels := by
          simpa [hx] using ha
        have hy' : head y = .recv p labels' := by
          simpa [hy] using hb
        have obs_x : ObservableC x := observable_of_head_recv hx'
        have obs_y : ObservableC y := observable_of_head_recv hy'
        have hbr0 : BranchesRelC R' (branchesOf a) (branchesOf b) :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        have hbr' : BranchesRelC R' (branchesOf x) (branchesOf y) := by
          simpa [hx, hy] using hbr0
        have ha_recv : CanRecvC x p (branchesOf x) :=
          ⟨x, labels, Relation.ReflTransGen.refl, hx', rfl⟩
        have hb_recv : CanRecvC y p (branchesOf y) :=
          ⟨y, labels', Relation.ReflTransGen.refl, hy', rfl⟩
        exact ⟨obs_x, obs_y,
          ObservableRelC.is_recv p (branchesOf x) (branchesOf y) ha_recv hb_recv hbr'⟩
  exact ⟨R', hR', Or.inl ⟨rfl, rfl⟩⟩

/-! ## Mu eta and dest equality -/

lemma eq_of_dest_eq {a b : LocalTypeC} (h : PFunctor.M.dest a = PFunctor.M.dest b) : a = b := by
  refine PFunctor.M.bisim (R := fun x y => PFunctor.M.dest x = PFunctor.M.dest y) ?_ a b h
  intro x y hxy
  cases hx : x.dest with
  | mk a f =>
      have hy : y.dest = ⟨a, f⟩ := by
        simpa [hx] using hxy.symm
      refine ⟨a, f, f, rfl, hy, ?_⟩
      intro i
      rfl

lemma mu_eta {b : LocalTypeC} {x : String} {k : Unit → LocalTypeC}
    (hdest : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, k⟩) : b = mkMu x (k ()) := by
  have hk : k = fun _ => k () := by
    funext u
    cases u
    rfl
  have hdest' : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, fun _ => k ()⟩ := by
    have hdest' := hdest
    rw [hk] at hdest'
    exact hdest'
  exact eq_of_dest_eq hdest'

/-! ## EQ2CE → EQ2C erasure -/

/-- Convert an EQ2CE step to EQ2C given environment resolution. -/
lemma EQ2CE_step_to_EQ2C {R : Rel} {ρ : EnvPair} {a b : LocalTypeC}
    (hR : ∀ ρ a b, R ρ a b → EQ2C a b)
    (hEnv : EnvResolves ρ)
    (hstep : EQ2CE_step R ρ a b) : EQ2C a b := by
  cases hstep with
  | «end» ha hb =>
      exact EQ2C_end_head ha hb
  | var ha hb =>
      exact EQ2C_var_head ha hb
  | send ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_send_head ha hb hbr'
  | recv ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_recv_head ha hb hbr'
  | var_left ha hmem =>
      rename_i x
      have hvar : EQ2C a (mkVar x) := by
        have hb : head (mkVar x) = .var x := by simp
        exact EQ2C_var_head ha hb
      exact EQ2C_trans hvar (hEnv.1 _ _ hmem)
  | var_right hb hmem =>
      rename_i x
      have hvar : EQ2C (mkVar x) b := by
        have ha : head (mkVar x) = .var x := by simp
        exact EQ2C_var_head ha hb
      exact EQ2C_trans (hEnv.2 _ _ hmem) hvar
  | mu_left ha hmem hrel =>
      rename_i x f
      have hrec : EQ2C (f ()) b := hR _ _ _ hrel
      have hmu : EQ2C (mkMu x (f ())) b := EQ2C_unfold_left hrec x
      have ha' : a = mkMu x (f ()) := mu_eta (b := a) (x := x) (k := f) ha
      simpa [ha'] using hmu
  | mu_right hb hrel =>
      rename_i x f
      have hrec : EQ2C a (f ()) := hR _ _ _ hrel
      have hmu : EQ2C a (mkMu x (f ())) := EQ2C_unfold_right hrec x
      have hb' : b = mkMu x (f ()) := mu_eta (b := b) (x := x) (k := f) hb
      simpa [hb'] using hmu

/-- Variant using EnvResolvesL and EnvVarR. -/
lemma EQ2CE_step_to_EQ2C_varR {R : Rel} {ρ : EnvPair} {a b : LocalTypeC}
    (hR : ∀ ρ a b, R ρ a b → EQ2C a b)
    (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
    (hstep : EQ2CE_step R ρ a b) : EQ2C a b := by
  have hEnv : EnvResolves ρ := EnvResolves_of_left_varR hEnvL hVarR
  exact EQ2CE_step_to_EQ2C (hR := hR) hEnv hstep

/-- Variant with explicit no-right-var constraint. -/
lemma EQ2CE_step_to_EQ2C_left {R : Rel} {ρ : EnvPair} {a b : LocalTypeC}
    (hR : ∀ ρ a b, R ρ a b → EQ2C a b)
    (hEnv : EnvResolvesL ρ)
    (hNoRight : ∀ x, head b = .var x → a ∈ envR ρ x → False)
    (hstep : EQ2CE_step R ρ a b) : EQ2C a b := by
  cases hstep with
  | «end» ha hb =>
      exact EQ2C_end_head ha hb
  | var ha hb =>
      exact EQ2C_var_head ha hb
  | send ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_send_head ha hb hbr'
  | recv ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_recv_head ha hb hbr'
  | var_left ha hmem =>
      rename_i x
      have hvar : EQ2C a (mkVar x) := by
        have hb : head (mkVar x) = .var x := by simp
        exact EQ2C_var_head ha hb
      exact EQ2C_trans hvar (hEnv _ _ hmem)
  | var_right hb hmem =>
      rename_i x
      exact (hNoRight x hb hmem).elim
  | mu_left ha hmem hrel =>
      rename_i x f
      have hrec : EQ2C (f ()) b := hR _ _ _ hrel
      have hmu : EQ2C (mkMu x (f ())) b := EQ2C_unfold_left hrec x
      have ha' : a = mkMu x (f ()) := mu_eta (b := a) (x := x) (k := f) ha
      simpa [ha'] using hmu
  | mu_right hb hrel =>
      rename_i x f
      have hrec : EQ2C a (f ()) := hR _ _ _ hrel
      have hmu : EQ2C a (mkMu x (f ())) := EQ2C_unfold_right hrec x
      have hb' : b = mkMu x (f ()) := mu_eta (b := b) (x := x) (k := f) hb
      simpa [hb'] using hmu

end RumpsteakV2.Coinductive
