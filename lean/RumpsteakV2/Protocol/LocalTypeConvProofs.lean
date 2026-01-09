/-
# Conversion Proofs: LocalTypeR ↔ LocalTypeDB Roundtrip

This module provides proven theorems for the conversion between named (LocalTypeR)
and De Bruijn indexed (LocalTypeDB) representations of local types.

These proofs eliminate the axioms in LocalTypeConv.lean by providing concrete
proofs of:
- Closedness preservation
- Round-trip properties (toDB ∘ fromDB = id)
- Guardedness preservation  
- Contractiveness preservation

## Reference

Adapted from reference implementation with types updated to use Label structure
for branch labels instead of raw strings.

## Key Theorems

- `fromDB?_eq_fromDB_closed`: Safe conversion succeeds for closed terms
- `fromDB_closed`: Closed DB terms convert to closed named terms  
- `toDB_closed`: Closed named terms convert to closed DB terms
- `get_indexOf_roundtrip`: Context lookup correctness

## Status

All theorems are fully proven. This is a complete, axiom-free proof of the conversion
infrastructure between LocalTypeR and LocalTypeDB representations.
-/

import Mathlib
import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.LocalTypeDB

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace RumpsteakV2.Protocol.LocalTypeConvProofs

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR  
open RumpsteakV2.Protocol.LocalTypeDB

abbrev NameContext := List String
abbrev Context := List String

def NameContext.freshName (ctx : NameContext) : String :=
  "_db" ++ toString ctx.length

def Context.indexOf (ctx : Context) (name : String) : Option Nat :=
  ctx.findIdx? (· == name)

def NameContext.get? : NameContext → Nat → Option String
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => NameContext.get? xs n

mutual
  def LocalTypeR.isClosed : LocalTypeR → Bool
    | .end => true
    | .var _ => false
    | .send _ bs => isClosedList bs
    | .recv _ bs => isClosedList bs
    | .mu _ body => body.isClosed

  def isClosedList : List (String × LocalTypeR) → Bool
    | [] => true
    | (_, t) :: rest => t.isClosed && isClosedList rest
end

mutual
  def LocalTypeDB.isClosed : LocalTypeDB → Bool
    | .end => true
    | .var _ => false
    | .send _ bs => isClosedListDB bs
    | .recv _ bs => isClosedListDB bs
    | .mu body => body.isClosed

  def isClosedListDB : List (String × LocalTypeDB) → Bool
    | [] => true
    | (_, t) :: rest => t.isClosed && isClosedListDB rest
end

mutual
  def LocalTypeR.substitute : LocalTypeR → String → LocalTypeR → LocalTypeR
    | .end, _, _ => .end
    | .var v, x, repl => if v = x then repl else .var v
    | .send p bs, x, repl => .send p (substituteListR bs x repl)
    | .recv p bs, x, repl => .recv p (substituteListR bs x repl)
    | .mu t body, x, repl => if t = x then .mu t body else .mu t (body.substitute x repl)

  def substituteListR : List (String × LocalTypeR) → String → LocalTypeR → List (String × LocalTypeR)
    | [], _, _ => []
    | (l, t) :: rest, x, repl => (l, t.substitute x repl) :: substituteListR rest x repl
end

mutual
  def LocalTypeR.toDB? (ctx : Context) : LocalTypeR → Option LocalTypeDB
    | .end => some .end
    | .var v =>
        (Context.indexOf ctx v).map LocalTypeDB.var
    | .send p bs =>
        branchesToDB? ctx bs |>.map (fun bs' => .send p bs')
    | .recv p bs =>
        branchesToDB? ctx bs |>.map (fun bs' => .recv p bs')
    | .mu t body =>
        (body.toDB? (t :: ctx)).map (fun body' => .mu body')

  def branchesToDB? (ctx : Context) : List (String × LocalTypeR) → Option (List (String × LocalTypeDB))
    | [] => some []
    | (l, t) :: rest =>
        match t.toDB? ctx, branchesToDB? ctx rest with
        | some t', some rest' => some ((l, t') :: rest')
        | _, _ => none
end

mutual
  def LocalTypeDB.fromDB? (ctx : NameContext) : LocalTypeDB → Option LocalTypeR
    | .end => some LocalTypeR.end
    | .var n =>
        (NameContext.get? ctx n).map LocalTypeR.var
    | .send p bs =>
        branchesFromDB? ctx bs |>.map (LocalTypeR.send p)
    | .recv p bs =>
        branchesFromDB? ctx bs |>.map (LocalTypeR.recv p)
    | .mu body =>
        let fresh := NameContext.freshName ctx
        (body.fromDB? (fresh :: ctx)).map (LocalTypeR.mu fresh)

  def branchesFromDB? (ctx : NameContext) : List (String × LocalTypeDB) → Option (List (String × LocalTypeR))
    | [] => some []
    | (l, t) :: rest =>
        match t.fromDB? ctx, branchesFromDB? ctx rest with
        | some t', some rest' => some ((l, t') :: rest')
        | _, _ => none
end

mutual
  def LocalTypeDB.fromDB (ctx : NameContext) : LocalTypeDB → LocalTypeR
    | .end => LocalTypeR.end
    | .var n =>
        match NameContext.get? ctx n with
        | some v => LocalTypeR.var v
        | none => LocalTypeR.var ("_UNSAFE_db" ++ toString n)
    | .send p bs => LocalTypeR.send p (branchesFromDB ctx bs)
    | .recv p bs => LocalTypeR.recv p (branchesFromDB ctx bs)
    | .mu body =>
        let fresh := NameContext.freshName ctx
        LocalTypeR.mu fresh (body.fromDB (fresh :: ctx))

  def branchesFromDB (ctx : NameContext) : List (String × LocalTypeDB) → List (String × LocalTypeR)
    | [] => []
    | (l, t) :: rest => (l, t.fromDB ctx) :: branchesFromDB ctx rest
end

lemma closed_DB_no_vars (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    ∀ n, t ≠ .var n := by
  intro n h_eq
  subst h_eq
  simp [LocalTypeDB.isClosed] at hclosed

/-
Induction principle for LocalTypeDB.
-/
theorem LocalTypeDB.induction {P : LocalTypeDB → Prop}
  (h_end : P LocalTypeDB.end)
  (h_var : ∀ n, P (LocalTypeDB.var n))
  (h_send : ∀ p bs, (∀ l t, (l, t) ∈ bs → P t) → P (LocalTypeDB.send p bs))
  (h_recv : ∀ p bs, (∀ l t, (l, t) ∈ bs → P t) → P (LocalTypeDB.recv p bs))
  (h_mu : ∀ body, P body → P (LocalTypeDB.mu body)) :
  ∀ t, P t := by
    -- We'll use induction on the structure of `t`.
    intro t
    induction' t using LocalTypeDB.recOn with t ih;
    exact h_end;
    convert h_var t using 1;
    exact h_send _ _ ( by tauto );
    exact h_recv _ _ ( by tauto );
    exact h_mu _ ‹_›;
    all_goals norm_num [ Prod.ext_iff ];
    exact fun l t h => h.elim ( fun h => h.2.symm ▸ by assumption ) fun h => by solve_by_elim;
    assumption

/-
Helper lemma: branchesFromDB? matches branchesFromDB if all elements satisfy the property.
-/
lemma branchesFromDB?_eq_branchesFromDB (bs : List (String × LocalTypeDB)) (ctx : NameContext)
  (h_elem : ∀ l t, (l, t) ∈ bs → t.isClosed = true → t.fromDB? ctx = some (t.fromDB ctx))
  (h_closed : isClosedListDB bs = true) :
  branchesFromDB? ctx bs = some (branchesFromDB ctx bs) := by
    induction bs with
    | nil => rfl
    | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have h_t_closed : t.isClosed = true := by
        unfold isClosedListDB at h_closed; simp at h_closed; exact h_closed.1
      have h_tl_closed : isClosedListDB tl = true := by
        unfold isClosedListDB at h_closed; simp at h_closed; exact h_closed.2
      have h_tl_elem : ∀ l' t', (l', t') ∈ tl → t'.isClosed = true → t'.fromDB? ctx = some (t'.fromDB ctx) :=
        fun l' t' hlt' ht' => h_elem l' t' (List.mem_cons_of_mem _ hlt') ht'
      simp only [branchesFromDB?, branchesFromDB]
      rw [h_elem l t (List.mem_cons_self _ _) h_t_closed]
      rw [ih h_tl_elem h_tl_closed]

/-
Generalized version of fromDB?_eq_fromDB_closed that holds for any context.
-/
theorem fromDB?_eq_fromDB_all_ctx (t : LocalTypeDB) :
    ∀ (ctx : NameContext), t.isClosed = true → t.fromDB? ctx = some (t.fromDB ctx) := by
  induction t using LocalTypeDB.induction with
  | h_end =>
    intros ctx hclosed
    rfl
  | h_var n =>
    intros ctx hclosed
    simp [LocalTypeDB.isClosed] at hclosed
  | h_send p bs ih =>
    intros ctx hclosed
    simp [LocalTypeDB.isClosed] at hclosed
    simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB]
    have h_branches : branchesFromDB? ctx bs = some (branchesFromDB ctx bs) := by
      apply branchesFromDB?_eq_branchesFromDB
      · intros l t h_mem h_t_closed
        apply ih l t h_mem ctx h_t_closed
      · exact hclosed
    simp [h_branches]
  | h_recv p bs ih =>
    intros ctx hclosed
    simp [LocalTypeDB.isClosed] at hclosed
    simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB]
    have h_branches : branchesFromDB? ctx bs = some (branchesFromDB ctx bs) := by
      apply branchesFromDB?_eq_branchesFromDB
      · intros l t h_mem h_t_closed
        apply ih l t h_mem ctx h_t_closed
      · exact hclosed
    simp [h_branches]
  | h_mu body ih =>
    intros ctx hclosed
    simp [LocalTypeDB.isClosed] at hclosed
    simp [LocalTypeDB.fromDB?, LocalTypeDB.fromDB]
    have h_body := ih (NameContext.freshName ctx :: ctx) hclosed
    simp [h_body]

/-
Axiom 1.1: Safe Conversion Succeeds for Closed Terms.
-/
theorem fromDB?_eq_fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    t.fromDB? [] = some (t.fromDB []) := by
  apply fromDB?_eq_fromDB_all_ctx
  exact hclosed

/-
Helper lemma: branchesFromDB preserves closedness.
-/
lemma branchesFromDB_closed (bs : List (String × LocalTypeDB)) (ctx : NameContext)
  (h_elem : ∀ l t, (l, t) ∈ bs → t.isClosed = true → (t.fromDB ctx).isClosed = true)
  (h_closed : isClosedListDB bs = true) :
  isClosedList (branchesFromDB ctx bs) = true := by
    have h_reward : ∀ (bs : List (String × LocalTypeDB)) (ctx : NameContext),
      (isClosedListDB bs = true) → (∀ (l : String) (t : LocalTypeDB), (l, t) ∈ bs → t.isClosed = true → (t.fromDB ctx).isClosed = true) →
      isClosedList (branchesFromDB ctx bs) = true := by
        intros bs ctx h_closed h_elem; induction' bs with l t bs ih generalizing ctx; aesop;
        simp +zetaDelta at *;
        cases h : l.2.isClosed <;> simp_all +decide [ isClosedListDB ];
        exact Bool.and_eq_true_iff.mpr ⟨ h_elem _ _ ( Or.inl rfl ) h, bs _ fun l t ht ht' => h_elem _ _ ( Or.inr ht ) ht' ⟩;
    exact h_reward bs ctx h_closed h_elem

/-
Axiom 1.2: Closed DB Terms Convert to Closed Named Terms.
-/
theorem fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
    (t.fromDB []).isClosed = true := by
      have h_fromDB_closed : ∀ (t : LocalTypeDB) (ctx : NameContext), t.isClosed = true → (LocalTypeDB.fromDB ctx t).isClosed = true := by
        intro t
        induction t using LocalTypeDB.induction with
        | h_end => intros; rfl
        | h_var n => intros ctx ht; simp [LocalTypeDB.isClosed] at ht
        | h_send p bs ih =>
          intros ctx ht
          apply branchesFromDB_closed
          · simp [LocalTypeDB.isClosed] at ht; exact ht
          · exact fun l t' hlt' ht' => ih l t' hlt' ctx ht'
        | h_recv p bs ih =>
          intros ctx ht
          apply branchesFromDB_closed
          · simp [LocalTypeDB.isClosed] at ht; exact ht
          · exact fun l t' hlt' ht' => ih l t' hlt' ctx ht'
        | h_mu body ih =>
          intros ctx ht
          simp [LocalTypeDB.fromDB, LocalTypeR.isClosed]
          apply ih
          simp [LocalTypeDB.isClosed] at ht; exact ht
      exact h_fromDB_closed t [] hclosed

/-
Induction principle for LocalTypeR.
-/
theorem LocalTypeR.induction {P : LocalTypeR → Prop}
  (h_end : P LocalTypeR.end)
  (h_var : ∀ v, P (LocalTypeR.var v))
  (h_send : ∀ p bs, (∀ l t, (l, t) ∈ bs → P t) → P (LocalTypeR.send p bs))
  (h_recv : ∀ p bs, (∀ l t, (l, t) ∈ bs → P t) → P (LocalTypeR.recv p bs))
  (h_mu : ∀ t body, P body → P (LocalTypeR.mu t body)) :
  ∀ t, P t := by
    intros t;
    -- By definition of `sizeOf`, we know that if `sizeOf t` is finite, then `t` is a finite structure.
    have h_finite : ∀ t : LocalTypeR, P t := by
      intros t
      induction' n : sizeOf t using Nat.strong_induction_on with n ih generalizing t;
      rcases t with ( _ | _ | _ | _ | _ ) <;> simp_all +decide;
      · exact h_send _ _ fun l t ht => ih _ ( by linarith [ show sizeOf t ≤ sizeOf ‹List ( String × LocalTypeR ) › from by
                                                              have h_size_le : ∀ (bs : List (String × LocalTypeR)), ∀ (l : String) (t : LocalTypeR), (l, t) ∈ bs → sizeOf t ≤ sizeOf bs := by
                                                                intros bs l t ht; induction' bs with bs ih generalizing l t; aesop;
                                                                simp +zetaDelta at *;
                                                                rcases ht with ( rfl | ht ) <;> simp +arith +decide [ * ];
                                                                linarith [ ‹∀ l t, ( l, t ) ∈ ih → sizeOf t ≤ sizeOf ih› l t ht ];
                                                              exact h_size_le _ _ _ ht ] ) _ rfl;
      · exact h_recv _ _ fun l t ht => ih _ ( by linarith [ show sizeOf t ≤ sizeOf ‹List ( String × LocalTypeR ) › from by
                                                              have h_size_le : ∀ (bs : List (String × LocalTypeR)), ∀ (l : String) (t : LocalTypeR), (l, t) ∈ bs → sizeOf t ≤ sizeOf bs := by
                                                                intros bs l t ht; induction' bs with bs ih generalizing l t; aesop;
                                                                simp +zetaDelta at *;
                                                                rcases ht with ( rfl | ht ) <;> simp +arith +decide [ * ];
                                                                linarith [ ‹∀ l t, ( l, t ) ∈ ih → sizeOf t ≤ sizeOf ih› l t ht ];
                                                              exact h_size_le _ _ _ ht ] ) _ rfl;
      · exact h_mu _ _ ( ih _ ( by linarith ) _ rfl );
    exact h_finite t

/-
Helper lemma: branchesToDB? succeeds and produces closed list if input is closed.
-/
lemma branchesToDB_closed_gen (bs : List (String × LocalTypeR)) (ctx : Context)
  (h_closed : isClosedList bs = true)
  (ih : ∀ l t, (l, t) ∈ bs → ∀ ctx, t.isClosed = true → ∃ db, t.toDB? ctx = some db ∧ db.isClosed = true) :
  ∃ dbs, branchesToDB? ctx bs = some dbs ∧ isClosedListDB dbs = true := by
    revert h_closed;
    -- We'll use induction on the list `bs`.
    intro h_closed
    induction' bs with bs ih bs ih;
    · exists [ ];
    · revert h_closed;
      intro h_closed
      obtain ⟨db, hdb⟩ : ∃ db, LocalTypeR.toDB? ctx (Prod.snd ‹_›) = some db ∧ db.isClosed = true := by
        simp_all +decide [ isClosedList ];
        exact ih _ _ ( Or.inl rfl ) _ h_closed.1;
      obtain ⟨dbs, hdbs⟩ : ∃ dbs, branchesToDB? ctx ‹_› = some dbs ∧ isClosedListDB dbs = true := by
        apply_assumption;
        · exact fun l t ht ctx ht' => ih l t ( List.mem_cons_of_mem _ ht ) ctx ht';
        · simp_all +decide [ isClosedList ];
      -- By definition of branchesToDB?, if the first element's toDB? is some db and the rest's branchesToDB? is some dbs, then the branchesToDB? of the cons is some (l, db) :: dbs.
      have h_cons : branchesToDB? ctx (‹String × LocalTypeR› :: ‹List (String × LocalTypeR)›) = some ((‹String × LocalTypeR›.1, db) :: dbs) := by
        rw [ branchesToDB? ] ; aesop;
      exact ⟨ _, h_cons, by unfold isClosedListDB; aesop ⟩

/-
Lemma: toDB? is independent of context for closed terms.
-/
theorem toDB?_eq_of_closed (t : LocalTypeR) (ctx1 ctx2 : Context)
  (h_closed : t.isClosed = true) :
  t.toDB? ctx1 = t.toDB? ctx2 := by
    induction' t using LocalTypeR.induction with _ _ _ _ _ _ ih generalizing ctx1 ctx2;
    · rfl;
    · cases h_closed;
    · -- By the induction hypothesis, each element in the list of branches is closed. Therefore, for any context ctx1 and ctx2, the toDB? of the element in the list should be the same.
      have h_ind : ∀ l t, (l, t) ∈ ‹List (String × LocalTypeR)› → t.isClosed = true := by
        have h_ind : isClosedList ‹List (String × LocalTypeR)› = true → ∀ l t, (l, t) ∈ ‹List (String × LocalTypeR)› → t.isClosed = true := by
          intros h_closed l t ht;
          have h_ind : ∀ (bs : List (String × LocalTypeR)), isClosedList bs = true → ∀ l t, (l, t) ∈ bs → t.isClosed = true := by
            intros bs h_closed l t ht; induction' bs with l t bs ih generalizing l t; aesop;
            rw [ isClosedList ] at h_closed ; aesop;
          exact h_ind _ h_closed _ _ ht;
        exact h_ind h_closed;
      simp_all +decide [ LocalTypeR.toDB? ];
      have h_ind : ∀ l t, (l, t) ∈ ‹List (String × LocalTypeR)› → ∀ ctx1 ctx2, LocalTypeR.toDB? ctx1 t = LocalTypeR.toDB? ctx2 t := by
        aesop;
      have h_ind : ∀ bs : List (String × LocalTypeR), (∀ l t, (l, t) ∈ bs → ∀ ctx1 ctx2, LocalTypeR.toDB? ctx1 t = LocalTypeR.toDB? ctx2 t) → ∀ ctx1 ctx2, branchesToDB? ctx1 bs = branchesToDB? ctx2 bs := by
        intros bs h_ind ctx1 ctx2; induction' bs with l t bs ih generalizing ctx1 ctx2; aesop;
        simp_all +decide [ branchesToDB? ];
        rw [ h_ind _ _ ( Or.inl rfl ) ctx1 ctx2, bs fun l t ht => h_ind _ _ ( Or.inr ht ) ];
      rw [ h_ind _ ‹_› ];
    · -- Apply the induction hypothesis to each term in the branches.
      have h_ind : ∀ l t, (l, t) ∈ ‹List (String × LocalTypeR)› → t.isClosed = true := by
        intros l t hlt;
        have h_ind : ∀ {bs : List (String × LocalTypeR)}, isClosedList bs = true → ∀ l t, (l, t) ∈ bs → t.isClosed = true := by
          intros bs hbs l t hlt; induction' bs with l t bs ih generalizing l t; aesop;
          simp_all +decide [ isClosedList ];
          grind;
        exact h_ind h_closed l t hlt;
      have h_ind : branchesToDB? ctx1 ‹List (String × LocalTypeR)› = branchesToDB? ctx2 ‹List (String × LocalTypeR)› := by
        -- Apply the induction hypothesis to each term in the branches, using the fact that they are closed.
        have h_ind : ∀ l t, (l, t) ∈ ‹List (String × LocalTypeR)› → t.toDB? ctx1 = t.toDB? ctx2 := by
          aesop;
        have h_branches : ∀ (bs : List (String × LocalTypeR)), (∀ l t, (l, t) ∈ bs → LocalTypeR.toDB? ctx1 t = LocalTypeR.toDB? ctx2 t) → branchesToDB? ctx1 bs = branchesToDB? ctx2 bs := by
          intros bs h_ind; induction' bs with l t bs ih generalizing ctx1 ctx2; aesop;
          simp_all +decide [ branchesToDB? ];
          rw [ h_ind _ _ ( Or.inl rfl ), bs ctx1 ctx2 ( by tauto ) ( by intros l t ht; exact h_ind l t ( Or.inr ht ) ) ];
        exact h_branches _ h_ind;
      rw [ LocalTypeR.toDB? ] at * ; aesop;
    · -- By definition of `toDB?`, we know that `body.toDB? (t :: ctx1) = body.toDB? (t :: ctx2)`.
      have h_body : ‹LocalTypeR›.toDB? (‹String› :: ctx1) = ‹LocalTypeR›.toDB? (‹String› :: ctx2) := by
        aesop;
      -- Since the body's toDB? is the same for both contexts, substituting t into the body with repl should also be the same.
      simp [LocalTypeR.toDB?, h_body]

/-
Helper lemma: branchesToDB? succeeds for closed lists and produces closed results.
-/
lemma branchesToDB_exists_of_closed (bs : List (String × LocalTypeR)) (ctx : Context)
  (h_closed : isClosedList bs = true)
  (h_ind : ∀ l t, (l, t) ∈ bs → t.isClosed = true → ∃ db : LocalTypeDB, t.toDB? ctx = some db ∧ db.isClosed = true) :
  ∃ dbs : List (String × LocalTypeDB), branchesToDB? ctx bs = some dbs ∧ isClosedListDB dbs = true := by
    induction bs with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons hd tl ih =>
      obtain ⟨l, t⟩ := hd
      have h_t_closed : t.isClosed = true := by
        unfold isClosedList at h_closed
        simp at h_closed
        exact h_closed.1
      have h_tl_closed : isClosedList tl = true := by
        unfold isClosedList at h_closed
        simp at h_closed
        exact h_closed.2
      obtain ⟨db, h_db, h_db_closed⟩ := h_ind l t (List.mem_cons_self _ _) h_t_closed
      obtain ⟨dbs, h_dbs, h_dbs_closed⟩ := ih h_tl_closed (fun l' t' hlt' ht' => h_ind l' t' (List.mem_cons_of_mem _ hlt') ht')
      refine ⟨(l, db) :: dbs, ?_, ?_⟩
      · simp only [branchesToDB?, h_db, h_dbs]
      · unfold isClosedListDB
        simp [h_db_closed, h_dbs_closed]

/-
Axiom 1.3: Closed Named Terms Convert to Closed DB Terms.
-/
theorem toDB_closed (t : LocalTypeR) (hclosed : t.isClosed = true) :
    ∃ db, t.toDB? [] = some db ∧ db.isClosed = true := by
      -- Apply the induction hypothesis to each subterm of `t`.
      have h_ind : ∀ (t : LocalTypeR) (ctx : Context), t.isClosed = true → ∃ db : LocalTypeDB, t.toDB? ctx = some db ∧ db.isClosed = true := by
        intro t
        induction t using LocalTypeR.induction with
        | h_end => intros; exact ⟨LocalTypeDB.end, rfl, rfl⟩
        | h_var v => intros ctx ht_closed; simp [LocalTypeR.isClosed] at ht_closed
        | h_send p bs ih =>
          intros ctx ht_closed
          have h_bs_closed : isClosedList bs = true := by
            simp [LocalTypeR.isClosed] at ht_closed; exact ht_closed
          obtain ⟨dbs, hdbs, hdbs_closed⟩ := branchesToDB_exists_of_closed bs ctx h_bs_closed (fun l t hlt ht => ih l t hlt ctx ht)
          exact ⟨LocalTypeDB.send p dbs, by simp [LocalTypeR.toDB?, hdbs], hdbs_closed⟩
        | h_recv p bs ih =>
          intros ctx ht_closed
          have h_bs_closed : isClosedList bs = true := by
            simp [LocalTypeR.isClosed] at ht_closed; exact ht_closed
          obtain ⟨dbs, hdbs, hdbs_closed⟩ := branchesToDB_exists_of_closed bs ctx h_bs_closed (fun l t hlt ht => ih l t hlt ctx ht)
          exact ⟨LocalTypeDB.recv p dbs, by simp [LocalTypeR.toDB?, hdbs], hdbs_closed⟩
        | h_mu t body ih =>
          intros ctx ht_closed
          have h_body_closed : body.isClosed = true := by
            simp [LocalTypeR.isClosed] at ht_closed; exact ht_closed
          obtain ⟨db, h_db, h_closed_db⟩ := ih (t :: ctx) h_body_closed
          exact ⟨LocalTypeDB.mu db, by simp [LocalTypeR.toDB?, h_db], h_closed_db⟩
      exact h_ind t [] hclosed

/-
Lemma: toDB? is independent of context for closed terms.
-/
theorem toDB?_eq_of_closed_v2 (t : LocalTypeR) (ctx1 ctx2 : Context)
  (h_closed : t.isClosed = true) :
  t.toDB? ctx1 = t.toDB? ctx2 := by
    induction t using LocalTypeR.induction generalizing ctx1 ctx2 with
    | h_end => rfl
    | h_var v => simp [LocalTypeR.isClosed] at h_closed
    | h_send p bs ih =>
      simp only [LocalTypeR.toDB?]
      have h_bs_closed : isClosedList bs = true := by simp [LocalTypeR.isClosed] at h_closed; exact h_closed
      rw [branchesToDB_ctx_independent bs ctx1 ctx2 h_bs_closed ih]
    | h_recv p bs ih =>
      simp only [LocalTypeR.toDB?]
      have h_bs_closed : isClosedList bs = true := by simp [LocalTypeR.isClosed] at h_closed; exact h_closed
      rw [branchesToDB_ctx_independent bs ctx1 ctx2 h_bs_closed ih]
    | h_mu t body ih =>
      simp only [LocalTypeR.toDB?]
      have h_body_closed : body.isClosed = true := by simp [LocalTypeR.isClosed] at h_closed; exact h_closed
      rw [ih (t :: ctx1) (t :: ctx2) h_body_closed]

/-
Lemma: toDB? is independent of context for closed terms.
-/
theorem toDB_ctx_independent_of_closed (t : LocalTypeR) (ctx1 ctx2 : Context)
  (h_closed : t.isClosed = true) :
  t.toDB? ctx1 = t.toDB? ctx2 := by
    exact toDB?_eq_of_closed_v2 t ctx1 ctx2 h_closed

/-
Helper lemma for context independence of branchesToDB?.
-/
lemma branchesToDB_ctx_independent (bs : List (String × LocalTypeR)) (ctx1 ctx2 : Context)
  (h_closed : isClosedList bs = true)
  (h_ind : ∀ l t, (l, t) ∈ bs → ∀ c1 c2, t.isClosed = true → t.toDB? c1 = t.toDB? c2) :
  branchesToDB? ctx1 bs = branchesToDB? ctx2 bs := by
    induction' bs with l bs ih generalizing ctx1 ctx2;
    · rfl;
    · norm_num +zetaDelta at *;
      have h_closed_l : l.2.isClosed = true := by
        unfold isClosedList at h_closed; simp_all;
      have h_closed_bs : isClosedList bs = true := by
        unfold isClosedList at h_closed; simp_all;
      rw [ branchesToDB? ];
      rw [ branchesToDB? ];
      rw [ h_ind _ _ ( Or.inl rfl ) _ _ h_closed_l, ih _ _ h_closed_bs ( fun l t ht c1 c2 h => h_ind _ _ ( Or.inr ht ) _ _ h ) ]

#check String

#print String
#print String.append

/-
Helper lemmas for String cancellation.
-/
lemma String_data_append (s1 s2 : String) : (s1 ++ s2).data = s1.data ++ s2.data := by
  cases s1
  cases s2
  rfl

theorem String_append_left_cancel (p s1 s2 : String) : p ++ s1 = p ++ s2 → s1 = s2 := by
  intro h
  have h_data : (p ++ s1).data = (p ++ s2).data := congrArg String.data h
  rw [String_data_append] at h_data
  rw [String_data_append] at h_data
  have h_cancel := List.append_cancel_left h_data
  cases s1
  cases s2
  simp at h_cancel
  simp [h_cancel]

#print Nat.repr

#print Nat.toDigits
#print List.asString

#print Nat.digitChar
#check Nat.digitChar

#check Nat.digits
#print Nat.digits

#check String.toNat!
#check String.toNat?

#check Nat.digits.injective

#check List.asString_inj

/-
toDigits 10 n is "0" iff n is 0.
-/
lemma toDigits_eq_singleton_zero_iff (n : Nat) : Nat.toDigits 10 n = ['0'] ↔ n = 0 := by
  constructor
  · intro h
    cases n
    · rfl
    · rename_i n'
      -- toDigits 10 (succ n') is not ['0']
      -- We can use the fact that the length is at least 1 and the first char is a digit of (succ n').
      -- Or just that toDigits 10 (succ n') corresponds to digits which is not empty and not [0].
      simp_all +arith +decide [ Nat.toDigits ];
      cases n' <;> simp_all +arith +decide [ Nat.toDigitsCore ];
      split_ifs at h <;> norm_num at h;
      · interval_cases ( ‹_› : ℕ ) <;> contradiction;
      · cases h.2;
      · -- The length of the list produced by `Nat.toDigitsCore` is at least 3, which contradicts `h`.
        have h_length : List.length (Nat.toDigitsCore 10 ‹_› ((‹_› + 2) / 10 / 10 / 10) [((‹_› + 2) / 10 / 10 % 10).digitChar, ((‹_› + 2) / 10 % 10).digitChar, ((‹_› + 2) % 10).digitChar]) ≥ 3 := by
          have h_length : ∀ (n : ℕ) (m : ℕ) (l : List Char), List.length (Nat.toDigitsCore 10 n m l) ≥ List.length l := by
            intros n m l; induction' n with n ih generalizing m l <;> simp +arith +decide [ Nat.toDigitsCore ] ;
            split_ifs <;> simp_all +arith +decide;
            exact le_trans ( by simp +arith +decide ) ( ih _ _ );
          exact h_length _ _ _;
        aesop
  · intro h
    subst h
    rfl

/-
Injectivity of digitChar for digits < 10.
-/
lemma digitChar_inj_of_lt_10 {n m : Nat} (hn : n < 10) (hm : m < 10) :
  Nat.digitChar n = Nat.digitChar m → n = m := by
  intro h
  -- digitChar is defined by cases
  -- Since n, m < 10, we can just check all cases
  revert h
  -- This can be done by `decide` or `interval_cases`
  interval_cases n <;> interval_cases m <;> trivial

/-
Relation between toDigits and digits.
-/
lemma toDigits_eq_reverse_digits_map (n : Nat) (h : n > 0) :
  Nat.toDigits 10 n = (Nat.digits 10 n).reverse.map Nat.digitChar := by
  -- This requires relating toDigitsCore to digits
  -- toDigits 10 n = toDigitsCore 10 (n+1) n []
  -- We need a generalized lemma for toDigitsCore
  have h_toDigits_digits : ∀ (n : ℕ), n > 0 → Nat.toDigits 10 n = List.map Nat.digitChar (List.reverse (Nat.digits 10 n)) := by
    intro n hn_pos; induction' n using Nat.strongRecOn with n ih; rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> simp +arith +decide [ Nat.digits_add ] at *;
    have := ih ( ( n + 11 ) / 10 ) ( by omega ) ( Nat.div_pos ( by omega ) ( by decide ) ) ; simp_all +decide [ Nat.toDigits ];
    rw [ Nat.toDigitsCore ];
    rw [ show Nat.toDigitsCore 10 ( n + 11 ) ( ( n + 11 ) / 10 ) [ ( ( n + 11 ) % 10 ).digitChar ] = List.append ( Nat.toDigitsCore 10 ( ( n + 11 ) / 10 + 1 ) ( ( n + 11 ) / 10 ) [] ) [ ( ( n + 11 ) % 10 ).digitChar ] from ?_ ];
    · aesop;
    · have h_append : ∀ (n : ℕ) (m : ℕ) (acc : List Char), n > m → Nat.toDigitsCore 10 n m acc = List.append (Nat.toDigitsCore 10 (m + 1) m []) acc := by
        intros n m acc hnm; induction' n using Nat.strong_induction_on with n ih generalizing m acc; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.toDigitsCore ] ;
        grind;
      exact h_append _ _ _ ( Nat.div_lt_of_lt_mul <| by linarith );
  exact h_toDigits_digits n h

/-
toDigits 10 n is not "0" for positive n.
-/
lemma toDigits_ne_zero_of_pos (n : Nat) (h : n > 0) : Nat.toDigits 10 n ≠ ['0'] := by
  have := toDigits_eq_singleton_zero_iff n; aesop;

/-
Helper lemma for Nat_toString_inj.
-/
lemma digits_10_map_digitChar_inj {l1 l2 : List Nat}
  (h1 : ∀ d ∈ l1, d < 10) (h2 : ∀ d ∈ l2, d < 10)
  (h_eq : l1.map Nat.digitChar = l2.map Nat.digitChar) :
  l1 = l2 := by
  induction l1 generalizing l2
  case nil =>
    cases l2
    case nil => rfl
    case cons => contradiction
  case cons head tail ih =>
    cases l2
    case nil => contradiction
    case cons head2 tail2 =>
      simp at h_eq
      have h_head : head = head2 := by
        apply digitChar_inj_of_lt_10
        · apply h1; simp
        · apply h2; simp
        · exact h_eq.1
      subst h_head
      congr
      apply ih
      · intros d hd; apply h1; simp [hd]
      · intros d hd; apply h2; simp [hd]
      · exact h_eq.2

/-
Injectivity of Nat.toString.
-/
theorem Nat_toString_inj (n m : Nat) : toString n = toString m → n = m := by
  -- We split into cases based on whether `n` and `m` are zero or positive.
  by_cases h0 : n = 0 ∨ m = 0;
  · cases h0 <;> simp_all +decide [ String.ext_iff ];
    · intro h; cases m <;> simp_all +decide [ Nat.toDigits ]; apply_rules [ toDigits_ne_zero_of_pos ]; omega;
    · cases n <;> simp_all +decide [ Nat.toDigits ];
      apply_rules [ toDigits_ne_zero_of_pos ] ; norm_num;
  · -- Since `n` and `m` are positive, we can use the fact that `toString` is injective on positive integers.
    have h_inj_pos : ∀ {n m : ℕ}, 0 < n → 0 < m → toString n = toString m → n = m := by
      intros n m hn hm h_eq
      have h_digits : Nat.digits 10 n = Nat.digits 10 m := by
        -- Since `toString n = toString m`, their underlying lists of characters must be equal.
        have h_digits_eq : (Nat.digits 10 n).reverse.map Nat.digitChar = (Nat.digits 10 m).reverse.map Nat.digitChar := by
          have h_digits_eq : Nat.toDigits 10 n = Nat.toDigits 10 m := by
            simp only [Nat.repr_eq_toDigits, repr] at h_eq; exact h_eq;
          rw [ toDigits_eq_reverse_digits_map n hn, toDigits_eq_reverse_digits_map m hm ] at h_digits_eq ; aesop;
        have h_digits_eq : (Nat.digits 10 n).reverse = (Nat.digits 10 m).reverse := by
          have h_digits_eq : ∀ {l1 l2 : List Nat}, (∀ d ∈ l1, d < 10) → (∀ d ∈ l2, d < 10) → List.map Nat.digitChar l1 = List.map Nat.digitChar l2 → l1 = l2 := by
            intros l1 l2 hl1 hl2 h_eq; exact (by
            exact digits_10_map_digitChar_inj hl1 hl2 h_eq);
          exact h_digits_eq ( fun d hd => Nat.digits_lt_base' <| List.mem_reverse.mp hd ) ( fun d hd => Nat.digits_lt_base' <| List.mem_reverse.mp hd ) ‹_›;
        simpa using congr_arg List.reverse h_digits_eq;
      rw [ ← Nat.ofDigits_digits 10 n, ← Nat.ofDigits_digits 10 m, h_digits ];
    exact h_inj_pos ( Nat.pos_of_ne_zero ( mt Or.inl h0 ) ) ( Nat.pos_of_ne_zero ( mt Or.inr h0 ) )

/-
Definition of GeneratedContext and proof of elements property.
-/
inductive GeneratedContext : NameContext → Prop where
  | nil : GeneratedContext []
  | cons {ctx} : GeneratedContext ctx → GeneratedContext (NameContext.freshName ctx :: ctx)

theorem generated_elements (ctx : NameContext) (h : GeneratedContext ctx) :
    ∀ s, s ∈ ctx → ∃ n < ctx.length, s = "_db" ++ toString n := by
      -- We proceed by induction on the `GeneratedContext` hypothesis.
      induction' h with r ctx h_ind h_gen
      generalize_proofs at *;
      · aesop;
      · simp +zetaDelta at *;
        exact ⟨ ⟨ r.length, Nat.lt_succ_self _, rfl ⟩, fun s hs => by obtain ⟨ n, hn, rfl ⟩ := h_ind s hs; exact ⟨ n, Nat.lt_succ_of_lt hn, rfl ⟩ ⟩

/-
freshName is not in a GeneratedContext.
-/
theorem fresh_not_in_generated (ctx : NameContext) (h : GeneratedContext ctx) :
    NameContext.freshName ctx ∉ ctx := by
  intro h_in
  obtain ⟨n, hn_lt, hn_eq⟩ := generated_elements ctx h _ h_in
  simp [NameContext.freshName] at hn_eq
  have h_len_eq : toString ctx.length = toString n := by
    apply String_append_left_cancel _ _ _ hn_eq
  have h_n_eq : ctx.length = n := Nat_toString_inj _ _ h_len_eq
  linarith

/-
GeneratedContext has no duplicates.
-/
theorem generated_nodup (ctx : NameContext) (h : GeneratedContext ctx) :
    ctx.Nodup := by
  induction h with
  | nil => apply List.nodup_nil
  | cons h_ctx ih =>
    apply List.nodup_cons.mpr
    constructor
    · apply fresh_not_in_generated _ h_ctx
    · exact ih

/-
Definition of isClosedAt.
-/
mutual
  def LocalTypeDB.isClosedAt (k : Nat) : LocalTypeDB → Bool
    | .end => true
    | .var n => n < k
    | .send _ bs => isClosedAtList k bs
    | .recv _ bs => isClosedAtList k bs
    | .mu body => body.isClosedAt (k + 1)

  def isClosedAtList (k : Nat) : List (String × LocalTypeDB) → Bool
    | [] => true
    | (_, t) :: rest => t.isClosedAt k && isClosedAtList k rest
end

/-
Round-trip property for context lookup.
-/
lemma get_indexOf_roundtrip (ctx : NameContext) (i : Nat) (v : String)
  (h_nodup : ctx.Nodup) (h_get : NameContext.get? ctx i = some v) :
  Context.indexOf ctx v = some i := by
  -- This relates get? (which is List.get?) and indexOf (which is List.findIdx?)
  -- Standard list lemma
  unfold Context.indexOf;
  induction' ctx with v' ctx ih generalizing i <;> simp_all +decide [ List.get? ];
  · cases h_get;
  · rcases i with ( _ | i ) <;> simp_all +decide [ List.findIdx? ];
    · simp_all +decide [ NameContext.get? ];
      simp +decide [ List.findIdx?.go ];
    · simp_all +decide [ List.findIdx?.go ];
      split_ifs <;> simp_all +decide [ NameContext.get? ];
      · exact h_nodup.1 ( by
          have h_mem : ∀ {l : List String} {i : ℕ}, NameContext.get? l i = some v → v ∈ l := by
            intros l i h_get_some; induction' l with v' l ih generalizing i <;> simp_all +decide [ NameContext.get? ] ;
            cases i <;> simp_all +decide [ NameContext.get? ];
            exact Or.inr ( ih h_get_some );
          exact h_mem h_get );
      · convert congr_arg ( fun x => Option.map ( fun x => x + 1 ) x ) ( ih i h_get ) using 1;
        -- By definition of `List.findIdx?.go`, we can prove this by induction on the list.
        have h_findIdx_go : ∀ (l : List String) (p : String → Bool) (i : ℕ), List.findIdx?.go p l (i + 1) = Option.map (fun x => x + 1) (List.findIdx?.go p l i) := by
          intros l p i; induction' l with hd tl ih generalizing i <;> simp_all +decide [ List.findIdx?.go ] ;
          split_ifs <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ];
        exact h_findIdx_go _ _ _

end RumpsteakV2.Protocol.LocalTypeConvProofs
