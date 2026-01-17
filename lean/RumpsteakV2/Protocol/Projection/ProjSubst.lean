import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.CoTypes.EQ2

set_option linter.unnecessarySimpa false

/-
The Problem. Prove that projection commutes with substitution in global types:
trans (g.substitute t G) role = (trans g role).substitute t (trans G role)

This property is essential for eliminating mu-unfold axioms. When a recursive type μt.body
is unfolded to body[t := μt.body], we must show that projecting the unfolded type is the
same as unfolding the projected type. The difficulty is that the mu case requires careful
guardedness analysis to ensure that the substitution preserves well-formedness.

Solution Structure. The Coq proof (indProj.v:173) proceeds by induction on g:
1. Base cases (.end, .var) are trivial equalities
2. Communication case (.comm) recurses on branch continuations
3. Mu case (.mu s body) is the complex case requiring guardedness preservation

This module axiomatizes the main theorem and provides specialized corollaries for
the mu-self substitution case needed by Harmony.lean.
-/

/-! # Projection-Substitution Commutation

This module provides the projection-substitution commutation axiom, following the Coq
proof in `indProj.v` (lemma `proj_subst`).

## Main Result

```
trans (g.substitute t G) role = (trans g role).substitute t (trans G role)
```

This is the key lemma needed to eliminate the mu-unfold axioms in Harmony.lean.

## Status

The main theorem is axiomatized. The Coq proof uses induction on g with:
- `.end`, `.var` cases: trivial
- `.mu s body` case: requires guardedness analysis (the complex case)
- `.comm` case: recursive on branch continuations

The axiom is semantically sound - proven in Coq's `indProj.v:173`.

## References

- Coq: `proj_subst` in `Projection/indProj.v` (line 173)
-/

namespace RumpsteakV2.Protocol.Projection.ProjSubst

open RumpsteakV2.Protocol.GlobalType (GlobalType Label)
open RumpsteakV2.Protocol.LocalTypeR (LocalTypeR)
open RumpsteakV2.Protocol.CoTypes.EQ2 (EQ2 EQ2_refl)

-- Aliases to avoid name collision with _root_.trans
abbrev projTrans := RumpsteakV2.Protocol.Projection.Trans.trans
abbrev projTransBranches := RumpsteakV2.Protocol.Projection.Trans.transBranches

/-! ## Size Lemmas (for termination) -/

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_head_snd_lt_cons (pair : Label × GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (pair :: rest) := by
  have h1 : sizeOf pair.2 < sizeOf pair := by
    simp only [sizeOf, Prod._sizeOf_1]
    omega
  have h2 : sizeOf pair < sizeOf (pair :: rest) := by
    simp only [sizeOf, List._sizeOf_1]
    omega
  exact Nat.lt_trans h1 h2

private theorem sizeOf_bs_lt_comm (sender receiver : String)
    (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  simp only [GlobalType.comm.sizeOf_spec]
  have h : 0 < 1 + sizeOf sender + sizeOf receiver := by omega
  omega

private theorem sizeOf_head_snd_lt_comm
    (sender receiver : String) (pair : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (GlobalType.comm sender receiver (pair :: rest)) := by
  have h1 : sizeOf pair.2 < sizeOf (pair :: rest) := sizeOf_head_snd_lt_cons pair rest
  have h2 : sizeOf (pair :: rest) < sizeOf (GlobalType.comm sender receiver (pair :: rest)) :=
    sizeOf_bs_lt_comm sender receiver (pair :: rest)
  exact Nat.lt_trans h1 h2

private theorem sizeOf_cont_lt_comm
    (sender receiver : String) (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf (GlobalType.comm sender receiver ((label, cont) :: rest)) := by
  exact sizeOf_head_snd_lt_comm sender receiver (label, cont) rest

private theorem sizeOf_cont_lt_cons (label : Label) (cont : GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf ((label, cont) :: rest) := by
  exact sizeOf_head_snd_lt_cons (label, cont) rest

private theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simp only [Nat.one_add]
    exact Nat.succ_pos (sizeOf t)
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simp only [sizeOf, GlobalType._sizeOf_1]
  omega

/-! ## Guardedness Preservation

These lemmas establish that guardedness is preserved through substitution,
which is needed for the mu case of proj_subst. -/

/-- If body is guarded for v, and repl is guarded for v, then substitution preserves guardedness.

    **PROVABLE**: By induction on body. -/
theorem isGuarded_substitute_preserved (body : LocalTypeR) (t v : String) (repl : LocalTypeR)
    (hbody : body.isGuarded v = true) (hrepl : repl.isGuarded v = true) :
    (body.substitute t repl).isGuarded v = true := by
  let P1 : LocalTypeR → Prop :=
    fun body =>
      ∀ t v repl, body.isGuarded v = true → repl.isGuarded v = true →
        (body.substitute t repl).isGuarded v = true
  let P2 : List (Label × LocalTypeR) → Prop := fun _ => True
  let P3 : Label × LocalTypeR → Prop := fun _ => True
  have hrec : P1 body := by
    refine (LocalTypeR.LocalTypeR.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ body)
    · intro t v repl hbody hrepl
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
    · intro p bs hbs t v repl hbody hrepl
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
    · intro p bs hbs t v repl hbody hrepl
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
    · intro s body ih t v repl hbody hrepl
      by_cases hvs : v = s
      · subst hvs
        by_cases hst : v = t
        · subst hst
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
        · simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hst]
      · have hbody' : body.isGuarded v = true := by
          simpa [LocalTypeR.isGuarded, hvs] using hbody
        by_cases hst : s = t
        · subst hst
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hvs, hbody']
        · have ih' := ih t v repl hbody' hrepl
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hvs, hst, ih']
    · intro w t v repl hbody hrepl
      have hbody' : (v != w) = true := by
        simpa [LocalTypeR.isGuarded] using hbody
      have hvw : v ≠ w := (bne_iff_ne).1 hbody'
      by_cases hwt : w = t
      · subst hwt
        simpa [LocalTypeR.substitute] using hrepl
      · have hvw' : (v != w) = true := (bne_iff_ne).2 hvw
        simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hwt, hvw']
    · exact True.intro
    · intro _ _ _ _
      exact True.intro
    · intro _ _ _
      exact True.intro
  exact hrec t v repl hbody hrepl

/-- If body is NOT guarded for v (v appears unguarded), and t ≠ v, then substitution
    for t doesn't change guardedness for v.

    **PROVABLE**: By induction on body. -/
theorem isGuarded_substitute_unguarded (body : LocalTypeR) (t v : String) (repl : LocalTypeR)
    (hbody : body.isGuarded v = false) (hneq : t ≠ v) :
    (body.substitute t repl).isGuarded v = false := by
  let P1 : LocalTypeR → Prop :=
    fun body =>
      ∀ t v repl, body.isGuarded v = false → t ≠ v →
        (body.substitute t repl).isGuarded v = false
  let P2 : List (Label × LocalTypeR) → Prop := fun _ => True
  let P3 : Label × LocalTypeR → Prop := fun _ => True
  have hrec : P1 body := by
    refine (LocalTypeR.LocalTypeR.rec (motive_1 := P1) (motive_2 := P2) (motive_3 := P3)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ body)
    · intro t v repl hbody hneq
      have : False := by
        simpa [LocalTypeR.isGuarded] using hbody
      exact this.elim
    · intro p bs hbs t v repl hbody hneq
      have : False := by
        simpa [LocalTypeR.isGuarded] using hbody
      exact this.elim
    · intro p bs hbs t v repl hbody hneq
      have : False := by
        simpa [LocalTypeR.isGuarded] using hbody
      exact this.elim
    · intro s body ih t v repl hbody hneq
      by_cases hvs : v = s
      · subst hvs
        have : False := by
          simpa [LocalTypeR.isGuarded] using hbody
        exact this.elim
      · have hbody' : body.isGuarded v = false := by
          simpa [LocalTypeR.isGuarded, hvs] using hbody
        by_cases hst : s = t
        · subst hst
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hvs, hbody']
        · have ih' := ih t v repl hbody' hneq
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hvs, hst, ih']
    · intro w t v repl hbody hneq
      have hvw : v = w := by
        by_cases hvw : v = w
        · exact hvw
        · have hne : (v != w) = true := (bne_iff_ne).2 hvw
          have : False := by
            simpa [LocalTypeR.isGuarded, hne] using hbody
          exact this.elim
      subst hvw
      have hvneq : v ≠ t := Ne.symm hneq
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hvneq]
    · exact True.intro
    · intro _ _ _ _
      exact True.intro
    · intro _ _ _
      exact True.intro
  exact hrec t v repl hbody hneq

/-! ## Main Axiom: Projection-Substitution Commutation -/

/- Projection commutes with global type substitution.

   Corresponds to Coq's `proj_subst`:
   ```
   trans p g[sigma] = (trans p g)[sigma >> trans p]
   ```

   Specialized to single-variable substitution:
   ```
   trans (g.substitute t G) role = (trans g role).substitute t (trans G role)
   ```

   In Coq, de Bruijn substitution is capture-avoiding, so the lemma holds
   unconditionally. In the named-variable setting, we require `G` to be closed
   so that substitution cannot introduce unguarded occurrences of a mu binder.

   **PROVABLE**: By induction on g, with guardedness preservation in the mu case. -/
mutual
  /-- Projection commutes with global type substitution (closed replacement). -/
  theorem proj_subst :
      ∀ (g : GlobalType) (t : String) (G : GlobalType) (role : String),
        G.isClosed = true →
        projTrans (g.substitute t G) role =
          (projTrans g role).substitute t (projTrans G role)
    | .end, t, G, role, hclosed => by
        simp [GlobalType.substitute, projTrans, Protocol.Projection.Trans.trans]
    | .var v, t, G, role, hclosed => by
        by_cases hvt : v = t
        · subst hvt
          simp [GlobalType.substitute, projTrans, Protocol.Projection.Trans.trans, LocalTypeR.substitute]
        · have hvt' : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
          simp [GlobalType.substitute, hvt', projTrans, Protocol.Projection.Trans.trans,
            LocalTypeR.substitute]
    | .comm sender receiver branches, t, G, role, hclosed => by
        by_cases hsender : role = sender
        · -- Sender case: projection is a send with projected branches.
          simp [GlobalType.substitute, projTrans, projTransBranches,
            Protocol.Projection.Trans.trans_comm_sender sender receiver role
              (GlobalType.substituteBranches branches t G) hsender,
            Protocol.Projection.Trans.trans_comm_sender sender receiver role branches hsender,
            proj_subst_branches branches t G role hclosed]
        · by_cases hreceiver : role = receiver
          · -- Receiver case: projection is a recv with projected branches.
            have hs : role ≠ sender := hsender
            simp [GlobalType.substitute, projTrans, projTransBranches,
              Protocol.Projection.Trans.trans_comm_receiver sender receiver role
                (GlobalType.substituteBranches branches t G) hreceiver hs,
              Protocol.Projection.Trans.trans_comm_receiver sender receiver role branches hreceiver hs,
              proj_subst_branches branches t G role hclosed]
          · -- Non-participant case: head projection on first branch.
            have hs : role ≠ sender := hsender
            have hr : role ≠ receiver := hreceiver
            cases branches with
            | nil =>
                simp [GlobalType.substitute, GlobalType.substituteBranches, projTrans,
                  Protocol.Projection.Trans.trans_comm_other sender receiver role [] hs hr]
            | cons head tail =>
                cases head with
                | mk label cont =>
                    have hrec := proj_subst cont t G role hclosed
                    simp [GlobalType.substitute, GlobalType.substituteBranches, projTrans,
                      Protocol.Projection.Trans.trans_comm_other sender receiver role
                        ((label, cont.substitute t G) :: GlobalType.substituteBranches tail t G) hs hr,
                      Protocol.Projection.Trans.trans_comm_other sender receiver role
                        ((label, cont) :: tail) hs hr,
                      hrec]
    | .mu s body, t, G, role, hclosed => by
        by_cases hst : s = t
        · subst hst
          cases hguard : (projTrans body role).isGuarded s <;>
            simp [GlobalType.substitute, projTrans, Protocol.Projection.Trans.trans,
              LocalTypeR.substitute, hguard]
        · have hrepl_closed : (projTrans G role).isClosed = true :=
            Protocol.Projection.Trans.trans_isClosed_of_isClosed G role hclosed
          have hrepl_guarded : (projTrans G role).isGuarded s = true :=
            LocalTypeR.isGuarded_of_closed (projTrans G role) s (by simpa using hrepl_closed)
          have hproj : projTrans (body.substitute t G) role =
              (projTrans body role).substitute t (projTrans G role) :=
            proj_subst body t G role hclosed
          set e := projTrans body role
          set repl := projTrans G role
          have hproj' : projTrans (body.substitute t G) role = e.substitute t repl := by
            simpa [e, repl] using hproj
          cases hguard : e.isGuarded s with
          | true =>
              have hguard' : (e.substitute t repl).isGuarded s = true :=
                isGuarded_substitute_preserved e t s repl hguard hrepl_guarded
              simp [GlobalType.substitute, hst, projTrans, Protocol.Projection.Trans.trans,
                LocalTypeR.substitute, hproj', e, repl, hguard, hguard']
          | false =>
              have hguard' : (e.substitute t repl).isGuarded s = false :=
                isGuarded_substitute_unguarded e t s repl hguard (Ne.symm hst)
              simp [GlobalType.substitute, hst, projTrans, Protocol.Projection.Trans.trans,
                hproj', e, repl, hguard, hguard']
  termination_by
    g => sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | exact sizeOf_cont_lt_comm _ _ _ _ _

  /-- Branch-wise version of proj_subst for transBranches/substituteBranches. -/
  theorem proj_subst_branches :
      ∀ (bs : List (Label × GlobalType)) (t : String) (G : GlobalType) (role : String),
        G.isClosed = true →
        projTransBranches (GlobalType.substituteBranches bs t G) role =
          LocalTypeR.substituteBranches (projTransBranches bs role) t (projTrans G role)
    | [], t, G, role, hclosed => by
        simp [GlobalType.substituteBranches, projTransBranches,
          Protocol.Projection.Trans.transBranches]
    | (label, cont) :: tail, t, G, role, hclosed => by
        simp [GlobalType.substituteBranches, projTransBranches,
          Protocol.Projection.Trans.transBranches,
          proj_subst cont t G role hclosed, proj_subst_branches tail t G role hclosed]
  termination_by
    bs => sizeOf bs
  decreasing_by
    all_goals
      first
      | exact sizeOf_tail_lt_cons _ _
      | exact sizeOf_cont_lt_cons _ _ _
end

/-! ## Corollaries -/

/-- proj_subst lifted to EQ2 (trivially, via equality). -/
theorem proj_subst_EQ2 (g : GlobalType) (t : String) (G : GlobalType) (role : String)
    (hclosed : G.isClosed = true) :
    EQ2 (projTrans (g.substitute t G) role)
        ((projTrans g role).substitute t (projTrans G role)) := by
  rw [proj_subst g t G role hclosed]
  exact EQ2_refl _

/-- Specialized version: substituting mu into its body commutes with projection.

    This is the key case for the Harmony axioms:
    ```
    trans (body.substitute t (mu t body)) role = (trans body role).substitute t (mu t (trans body role))
    ```
    when (trans body role).isGuarded t = true. -/
theorem proj_subst_mu_self (t : String) (body : GlobalType) (role : String)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    projTrans (body.substitute t (.mu t body)) role =
    (projTrans body role).substitute t (projTrans (.mu t body) role) :=
  proj_subst body t (.mu t body) role hclosed

/-- EQ2 version of mu-self substitution. -/
theorem proj_subst_mu_self_EQ2 (t : String) (body : GlobalType) (role : String)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    EQ2 (projTrans (body.substitute t (.mu t body)) role)
        ((projTrans body role).substitute t (projTrans (.mu t body) role)) := by
  rw [proj_subst_mu_self t body role hclosed]
  exact EQ2_refl _

/-! ## Guardedness Preservation

These lemmas establish that guardedness is preserved through substitution,
which is needed for the mu case of proj_subst. -/

end RumpsteakV2.Protocol.Projection.ProjSubst
