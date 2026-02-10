import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import SessionTypes.GlobalType
import SessionTypes.TypeContext
import SessionTypes.ValType
-- Import after GlobalType to avoid circular dependencies
-- import SessionTypes.LocalTypeConv

set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

/-
The Problem. Session types need a readable representation with named variables for user-facing
code and debugging. The core type must support substitution, unfolding, duality, and well-formedness
predicates (closedness, guardedness, contractiveness) for protocol verification.

Solution Structure. Defines `LocalTypeR` with named string variables: end, var, send/recv with
labeled branches, and mu for recursion. Provides `substitute`, `unfold`, and `dual` operations.
Defines `isFreeIn`, `isGuarded`, `isContractive`, and `WellFormed` predicates. Size lemmas
enable structural termination proofs.
-/

/-! # SessionTypes.LocalTypeR

Recursive local types for the V2 development.

## Expose

The following definitions form the semantic interface for proofs:

- `LocalTypeR`
- `LocalTypeR.dual`
- `LocalTypeR.unfold`
- `LocalTypeR.freeVars`
- `LocalTypeR.substitute`
-/

namespace SessionTypes.LocalTypeR

open SessionTypes.GlobalType
open SessionTypes (ValType)

/-- Recursive local types with branching.

Each branch carries an optional `ValType` for payload type-checking:
- `send partner [(label, some T, cont)]` — single-branch value send with type T
- `send partner [(l₁, none, c₁), (l₂, none, c₂)]` — multi-branch label choice (select)
- `recv partner [(label, some T, cont)]` — single-branch value recv with type T
- `recv partner [(l₁, none, c₁), (l₂, none, c₂)]` — multi-branch label choice (branch)
-/
inductive LocalTypeR where
  | end : LocalTypeR
  | send : String → List (Label × Option ValType × LocalTypeR) → LocalTypeR
  | recv : String → List (Label × Option ValType × LocalTypeR) → LocalTypeR
  | mu : String → LocalTypeR → LocalTypeR
  | var : String → LocalTypeR
  deriving Repr, Inhabited

/-- A branch is a labeled continuation with an optional value type.
    The `Option ValType` is `some T` when the branch carries a typed payload,
    and `none` for pure label choices or when type info is unavailable. -/
abbrev BranchR := Label × Option ValType × LocalTypeR

/-- Extract the continuation from a branch triple. -/
def BranchR.cont : BranchR → LocalTypeR := fun (_, _, c) => c

/-! ## Payload Erasure -/

mutual
  /-- Erase all value types from a local type (set branch payloads to `none`). -/
  def LocalTypeR.eraseValTypes : LocalTypeR → LocalTypeR
    | .end => .end
    | .var t => .var t
    | .mu t body => .mu t (LocalTypeR.eraseValTypes body)
    | .send p bs => .send p (eraseBranchValTypes bs)
    | .recv p bs => .recv p (eraseBranchValTypes bs)

  /-- Erase all branch payload types. -/
  def eraseBranchValTypes : List BranchR → List BranchR
    | [] => []
    | (label, vt, cont) :: rest =>
        let vt' :=
          match vt with
          | some (.chan _ _) => vt
          | _ => none
        (label, vt', LocalTypeR.eraseValTypes cont) :: eraseBranchValTypes rest
end

mutual
  /-- Extract free type variables from a local type. -/
  def LocalTypeR.freeVars : LocalTypeR → List String
    | .end => []
    | .send _ branches => freeVarsOfBranches branches
    | .recv _ branches => freeVarsOfBranches branches
    | .mu t body => body.freeVars.filter (· != t)
    | .var t => [t]

  def freeVarsOfBranches : List BranchR → List String
    | [] => []
    | (_, _, t) :: rest => t.freeVars ++ freeVarsOfBranches rest
end

/-! ## freeVars / isFreeIn bridge (converse direction)

NOTE: These theorems are moved to after the isFreeIn definition below.
-/

theorem freeVarsOfBranches_eq_flatMap (branches : List BranchR) :
    freeVarsOfBranches branches = branches.flatMap (fun (_, _, t) => t.freeVars) := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk label rest =>
          cases rest with
          | mk vt t =>
              simp [freeVarsOfBranches, ih, List.flatMap]

/-! ## Size lemmas for termination proofs -/

@[simp]
lemma sizeOf_cont_lt_sizeOf_branches (label : Label) (vt : Option ValType) (cont : LocalTypeR)
    (tail : List BranchR) :
    sizeOf cont < sizeOf ((label, vt, cont) :: tail) := by
  simp +arith

@[simp]
lemma sizeOf_tail_lt_sizeOf_branches (head : BranchR)
    (tail : List BranchR) :
    sizeOf tail < sizeOf (head :: tail) := by
  simp +arith

@[simp]
lemma sizeOf_branches_lt_sizeOf_send (p : String) (bs : List BranchR) :
    sizeOf bs < sizeOf (LocalTypeR.send p bs) := by
  simp +arith

@[simp]
lemma sizeOf_branches_lt_sizeOf_recv (p : String) (bs : List BranchR) :
    sizeOf bs < sizeOf (LocalTypeR.recv p bs) := by
  simp +arith

@[simp]
lemma sizeOf_body_lt_sizeOf_mu (t : String) (body : LocalTypeR) :
    sizeOf body < sizeOf (LocalTypeR.mu t body) := by
  simp +arith

@[simp] lemma sizeOf_branches_lt_of_send_eq {lt : LocalTypeR} {p : String}
    {bs : List BranchR} (h : lt = LocalTypeR.send p bs) :
    sizeOf bs < sizeOf lt := by
  simpa [h] using sizeOf_branches_lt_sizeOf_send p bs

@[simp] lemma sizeOf_branches_lt_of_recv_eq {lt : LocalTypeR} {p : String}
    {bs : List BranchR} (h : lt = LocalTypeR.recv p bs) :
    sizeOf bs < sizeOf lt := by
  simpa [h] using sizeOf_branches_lt_sizeOf_recv p bs

@[simp] lemma sizeOf_body_lt_of_mu_eq {lt : LocalTypeR} {t : String} {body : LocalTypeR}
    (h : lt = LocalTypeR.mu t body) :
    sizeOf body < sizeOf lt := by
  simpa [h] using sizeOf_body_lt_sizeOf_mu t body

@[simp] lemma sizeOf_tail_lt_of_cons_eq {bs : List BranchR}
    {head : BranchR} {tail : List BranchR}
    (h : bs = head :: tail) :
    sizeOf tail < sizeOf bs := by
  simpa [h] using sizeOf_tail_lt_sizeOf_branches head tail

@[simp] lemma sizeOf_cont_lt_of_head_eq {bs : List BranchR}
    {head : BranchR} {tail : List BranchR}
    {label : Label} {vt : Option ValType} {cont : LocalTypeR}
    (hbs : bs = head :: tail) (hhead : head = (label, vt, cont)) :
    sizeOf cont < sizeOf bs := by
  simpa [hbs, hhead] using sizeOf_cont_lt_sizeOf_branches label vt cont tail

/-- Size of continuation is less than size of branch list when the continuation is in the list. -/
lemma sizeOf_cont_lt_sizeOf_branches_mem {cont : LocalTypeR}
    {bs : List BranchR} (hmem : cont ∈ bs.map BranchR.cont) :
    sizeOf cont < sizeOf bs := by
  induction bs with
  | nil => simp only [List.map_nil, List.not_mem_nil] at hmem
  | cons hd tl ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
          subst heq
          cases hd with
          | mk l rest =>
              cases rest with
              | mk vt c =>
                  exact sizeOf_cont_lt_sizeOf_branches l vt c tl
      | inr hmem' =>
          have h1 := ih hmem'
          exact Nat.lt_trans h1 (sizeOf_tail_lt_sizeOf_branches hd tl)

mutual
  /-- Substitute a local type for a variable: `t.substitute v repl` replaces free occurrences of `v` in `t` with `repl`. -/
  def LocalTypeR.substitute : LocalTypeR → String → LocalTypeR → LocalTypeR
    | .end, _, _ => .end
    | .send partner branches, varName, replacement =>
        .send partner (substituteBranches branches varName replacement)
    | .recv partner branches, varName, replacement =>
        .recv partner (substituteBranches branches varName replacement)
    | .mu t body, varName, replacement =>
        if t == varName then
          .mu t body
        else
          .mu t (body.substitute varName replacement)
    | .var t, varName, replacement =>
        if t == varName then replacement else .var t

  def substituteBranches : List BranchR → String → LocalTypeR → List BranchR
    | [], _, _ => []
    | (label, vt, cont) :: rest, varName, replacement =>
        (label, vt, cont.substitute varName replacement) ::
          substituteBranches rest varName replacement
end

/-- substituteBranches is equivalent to mapping substitute over the continuations. -/
@[simp]
theorem substituteBranches_eq_map (bs : List BranchR) (var : String) (repl : LocalTypeR) :
    substituteBranches bs var repl = bs.map (fun (l, vt, c) => (l, vt, c.substitute var repl)) := by
  induction bs with
  | nil => rfl
  | cons head tail ih =>
      simp only [substituteBranches, List.map_cons, ih]

/-! ## Basic Substitution Simplification Lemmas -/

/-- Substitution on end is always end. -/
@[simp]
theorem substitute_end (var : String) (repl : LocalTypeR) :
    LocalTypeR.end.substitute var repl = .end := rfl

/-- Substitution on send reduces to substituting on branches. -/
@[simp]
theorem substitute_send (partner : String) (branches : List BranchR)
    (var : String) (repl : LocalTypeR) :
    (LocalTypeR.send partner branches).substitute var repl
    = .send partner (substituteBranches branches var repl) := rfl

/-- Substitution on recv reduces to substituting on branches. -/
@[simp]
theorem substitute_recv (partner : String) (branches : List BranchR)
    (var : String) (repl : LocalTypeR) :
    (LocalTypeR.recv partner branches).substitute var repl
    = .recv partner (substituteBranches branches var repl) := rfl

/-- Unfold one level of recursion: μt.T ↦ T[μt.T/t]. -/
def LocalTypeR.unfold : LocalTypeR → LocalTypeR
  | lt@(.mu t body) => body.substitute t lt
  | lt => lt

mutual
  /-- Dualize a local type by swapping send/recv. -/
  def LocalTypeR.dual : LocalTypeR → LocalTypeR
    | .end => .end
    | .send partner branches => .recv partner (dualBranches branches)
    | .recv partner branches => .send partner (dualBranches branches)
    | .mu t body => .mu t (body.dual)
    | .var t => .var t

  def dualBranches : List BranchR → List BranchR
    | [] => []
    | (label, vt, cont) :: rest => (label, vt, cont.dual) :: dualBranches rest
end

mutual
  /-- Dual is an involution on local types. -/
  def LocalTypeR.dual_dual : (t : LocalTypeR) → t.dual.dual = t
    | .end => rfl
    | .var _ => rfl
    | .mu _ body => congrArg (LocalTypeR.mu _) body.dual_dual
    | .send _ bs => congrArg (LocalTypeR.send _) (dualBranches_dualBranches bs)
    | .recv _ bs => congrArg (LocalTypeR.recv _) (dualBranches_dualBranches bs)

  /-- Dual branches is an involution. -/
  def dualBranches_dualBranches : (bs : List BranchR) →
      dualBranches (dualBranches bs) = bs
    | [] => rfl
    | (_, _, cont) :: rest =>
        congrArg₂ List.cons
          (congrArg₂ Prod.mk rfl (congrArg₂ Prod.mk rfl cont.dual_dual))
          (dualBranches_dualBranches rest)
end

/-! ## Dual-Substitute Commutation

These lemmas show that dual and substitute commute, which is essential for
proving that EQ2 is a congruence for duality. -/

mutual
  /-- Dual commutes with substitute: (t.substitute v r).dual = t.dual.substitute v r.dual. -/
  theorem LocalTypeR.dual_substitute : (t : LocalTypeR) → (var : String) → (repl : LocalTypeR) →
      (t.substitute var repl).dual = t.dual.substitute var repl.dual
    | .end, _, _ => rfl
    | .var v, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        split <;> rfl
    | .mu v body, var, repl =>
        if hv : v == var then by
          -- Shadowed case: both sides reduce to mu v body.dual
          simp only [LocalTypeR.substitute, LocalTypeR.dual, hv, ↓reduceIte]
        else by
          -- Non-shadowed case
          simp only [LocalTypeR.substitute, LocalTypeR.dual, hv, ↓reduceIte, Bool.false_eq_true]
          exact congrArg (LocalTypeR.mu v) (LocalTypeR.dual_substitute body var repl)
    | .send p bs, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        exact congrArg (LocalTypeR.recv p) (dualBranches_substituteBranches bs var repl)
    | .recv p bs, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        exact congrArg (LocalTypeR.send p) (dualBranches_substituteBranches bs var repl)

  /-- Dual and substitute commute for branch lists. -/
  theorem dualBranches_substituteBranches : (bs : List BranchR) →
      (var : String) → (repl : LocalTypeR) →
      dualBranches (substituteBranches bs var repl) =
        substituteBranches (dualBranches bs) var repl.dual
    | [], _, _ => rfl
    | (label, vt, cont) :: rest, var, repl => by
        simp only [substituteBranches, dualBranches]
        exact congrArg₂ List.cons
          (congrArg₂ Prod.mk rfl (congrArg₂ Prod.mk rfl (LocalTypeR.dual_substitute cont var repl)))
          (dualBranches_substituteBranches rest var repl)
end

/-! ## Closedness Predicate (Coq-style `eclosed`)

A local type is closed if it has no free type variables.
This matches Coq's `eclosed e := forall n, n \notin lType_fv e`. -/

theorem List.isEmpty_eq_true {α : Type} (l : List α) : l.isEmpty = true ↔ l = [] := by
  cases l <;> simp

/-- A local type is closed if it has no free type variables. -/
def LocalTypeR.isClosed (lt : LocalTypeR) : Bool := lt.freeVars.isEmpty

/-! ## Guardedness Predicate (Coq-style `eguarded`)

A variable is guarded in a type if it only appears inside a communication (send/recv).
This is the key property for proving termination of mu-unfolding.

Follows Coq's `eguarded n e` which checks if variable n is guarded at depth n. -/

mutual
  /-- Check if a variable appears free in a local type. -/
  def LocalTypeR.isFreeIn (v : String) : LocalTypeR → Bool
    | .end => false
    | .var w => v == w
    | .send _ bs => isFreeInBranches' v bs
    | .recv _ bs => isFreeInBranches' v bs
    | .mu t body => if v == t then false else body.isFreeIn v

  /-- Helper: check if variable appears free in any branch. -/
  def isFreeInBranches' (v : String) : List BranchR → Bool
    | [] => false
    | (_, _, c) :: rest => c.isFreeIn v || isFreeInBranches' v rest
end

/-! ## freeVars / isFreeIn bridge lemmas -/

mutual
  theorem mem_freeVars_isFreeIn (lt : LocalTypeR) (v : String) :
      v ∈ lt.freeVars → lt.isFreeIn v = true := by
    intro hmem
    cases hlt : lt with
    | «end» =>
        simp [LocalTypeR.freeVars, hlt] at hmem
    | var w =>
        have hv : v = w := by
          simpa [LocalTypeR.freeVars, hlt] using hmem
        subst hv
        simp [LocalTypeR.isFreeIn, hlt]
    | send _ bs | recv _ bs =>
        -- Send and recv cases are identical (symmetric under duality)
        have h' : v ∈ freeVarsOfBranches bs := by
          simpa [LocalTypeR.freeVars, hlt] using hmem
        have hmem' := mem_freeVarsOfBranches_isFreeInBranches' bs v h'
        simpa [LocalTypeR.isFreeIn, hlt] using hmem'
    | mu t body =>
        have h' : v ∈ body.freeVars.filter (· != t) := by
          simpa [LocalTypeR.freeVars, hlt] using hmem
        have hpair : v ∈ body.freeVars ∧ (v != t) = true := by
          simpa [List.mem_filter] using h'
        have hvne : v ≠ t := (bne_iff_ne).1 hpair.2
        have hbody : body.isFreeIn v = true := mem_freeVars_isFreeIn body v hpair.1
        have hvne' : (v == t) = false := beq_eq_false_iff_ne.mpr hvne
        simpa [LocalTypeR.isFreeIn, hvne', hlt] using hbody
  termination_by sizeOf lt
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega

  theorem mem_freeVarsOfBranches_isFreeInBranches' (bs : List BranchR) (v : String) :
      v ∈ freeVarsOfBranches bs → isFreeInBranches' v bs = true := by
    intro hmem
    cases hbs : bs with
    | nil =>
        simp [freeVarsOfBranches, hbs] at hmem
    | cons head tail =>
        cases hhead : head with
        | mk label rest =>
            cases hrest : rest with
            | mk vt cont =>
                have hmem' : v ∈ cont.freeVars ∨ v ∈ freeVarsOfBranches tail := by
                  simpa [freeVarsOfBranches, hbs, hhead, hrest, List.mem_append] using hmem
                cases hmem' with
                | inl hcont =>
                    have hfree : cont.isFreeIn v = true := mem_freeVars_isFreeIn cont v hcont
                    simp [isFreeInBranches', hbs, hhead, hrest, hfree]
                | inr htail =>
                    have hfree := mem_freeVarsOfBranches_isFreeInBranches' tail v htail
                    simp [isFreeInBranches', hbs, hhead, hrest, hfree]
  termination_by sizeOf bs
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega
end

/-- Check if a variable is guarded (only appears inside send/recv) in a local type.
    A variable is guarded if it doesn't appear at the "head" position -
    i.e., only inside the continuations of communications, not at mu bodies before communications.

    This predicate checks if variable v is guarded at the current position:
    - In end: trivially true (no v)
    - In var w: must not be v (unguarded occurrence)
    - In send/recv: any occurrence in branches is guarded (inside comm)
    - In mu t body: if t = v, shadowed so ok; otherwise must check body -/
def LocalTypeR.isGuarded (v : String) : LocalTypeR → Bool
  | .end => true
  | .var w => v != w  -- v appears unguarded if this IS v
  | .send _ _ => true  -- Any occurrence of v in branches is guarded (inside comm)
  | .recv _ _ => true  -- Any occurrence of v in branches is guarded (inside comm)
  | .mu t body => if v == t then true else body.isGuarded v

@[simp] theorem isGuarded_eraseValTypes :
    ∀ (lt : LocalTypeR) (v : String),
      (LocalTypeR.eraseValTypes lt).isGuarded v = lt.isGuarded v
  | .end, _ => rfl
  | .var _, _ => rfl
  | .send _ _, _ => rfl
  | .recv _ _, _ => rfl
  | .mu t body, v => by
      simp only [LocalTypeR.eraseValTypes, LocalTypeR.isGuarded]
      split_ifs
      · rfl
      · exact isGuarded_eraseValTypes body v
  termination_by lt _ => sizeOf lt
  decreasing_by
    simp_wf
    simp only [sizeOf, LocalTypeR._sizeOf_1]
    omega

mutual
  /-- A local type is contractive if every mu-bound variable is guarded in its body.
      This ensures mu-unfolding eventually reaches a communication. -/
  def LocalTypeR.isContractive : LocalTypeR → Bool
    | .end => true
    | .var _ => true
    | .send _ bs => isContractiveBranches bs
    | .recv _ bs => isContractiveBranches bs
    | .mu t body => body.isGuarded t && body.isContractive

  /-- Helper: check if all branches are contractive. -/
  def isContractiveBranches : List BranchR → Bool
    | [] => true
    | (_, _, c) :: rest => c.isContractive && isContractiveBranches rest

end

/-- Well-formed local types are closed and contractive. -/
structure LocalTypeR.WellFormed (t : LocalTypeR) : Prop where
  closed : t.isClosed
  contractive : t.isContractive = true

/-- `.end` is well-formed. -/
theorem LocalTypeR.WellFormed_end : LocalTypeR.WellFormed .end :=
  ⟨by simp [LocalTypeR.isClosed, LocalTypeR.freeVars],
   by simp [LocalTypeR.isContractive]⟩

/-! ## Lightweight Contractiveness and Partner Occurrence -/

/-- Local contractiveness check for mu bodies (vars are non-contractive). -/
def LocalTypeR.lcontractive : LocalTypeR → Bool
  | .end => true
  | .var _ => false
  | .send _ _ => true
  | .recv _ _ => true
  | .mu _ body =>
      match body with
      | .var _ => false
      | .mu _ _ => false
      | .send _ _ => true
      | .recv _ _ => true
      | .end => true

/-- `hasSendTo e partner` holds when `e` can send to `partner` somewhere in its structure. -/
inductive LocalTypeR.hasSendTo : LocalTypeR → String → Prop where
  | send {partner : String} {branches : List BranchR} :
      hasSendTo (.send partner branches) partner
  | send_branch {receiver partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasSendTo lb.2.2 partner → hasSendTo (.send receiver branches) partner
  | recv_branch {sender partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasSendTo lb.2.2 partner → hasSendTo (.recv sender branches) partner
  | mu {t : String} {body : LocalTypeR} {partner : String} :
      hasSendTo body partner → hasSendTo (.mu t body) partner
  | noncontractive {t : String} {body : LocalTypeR} {partner : String} :
      LocalTypeR.lcontractive body = false → hasSendTo (.mu t body) partner

/-- `hasRecvFrom e partner` holds when `e` can receive from `partner` somewhere in its structure. -/
inductive LocalTypeR.hasRecvFrom : LocalTypeR → String → Prop where
  | recv {partner : String} {branches : List BranchR} :
      hasRecvFrom (.recv partner branches) partner
  | send_branch {receiver partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasRecvFrom lb.2.2 partner → hasRecvFrom (.send receiver branches) partner
  | recv_branch {sender partner : String} {branches : List BranchR}
      {lb : BranchR} :
      lb ∈ branches → hasRecvFrom lb.2.2 partner → hasRecvFrom (.recv sender branches) partner
  | mu {t : String} {body : LocalTypeR} {partner : String} :
      hasRecvFrom body partner → hasRecvFrom (.mu t body) partner
  | noncontractive {t : String} {body : LocalTypeR} {partner : String} :
      LocalTypeR.lcontractive body = false → hasRecvFrom (.mu t body) partner

/-- Lift send partner occurrence through mu. -/
theorem LocalTypeR.hasSendTo_mu {t : String} {body : LocalTypeR} {partner : String}
    (h : body.hasSendTo partner) : (LocalTypeR.mu t body).hasSendTo partner :=
  LocalTypeR.hasSendTo.mu h

/-- Lift recv partner occurrence through mu. -/
theorem LocalTypeR.hasRecvFrom_mu {t : String} {body : LocalTypeR} {partner : String}
    (h : body.hasRecvFrom partner) : (LocalTypeR.mu t body).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.mu h

/-- Direct send partner occurrence. -/
theorem LocalTypeR.hasSendTo_send {partner : String} {branches : List BranchR} :
    (LocalTypeR.send partner branches).hasSendTo partner :=
  LocalTypeR.hasSendTo.send

/-- Direct recv partner occurrence. -/
theorem LocalTypeR.hasRecvFrom_recv {partner : String} {branches : List BranchR} :
    (LocalTypeR.recv partner branches).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.recv

/-- Propagate send partner occurrence through send branches. -/
theorem LocalTypeR.hasSendTo_send_branch {receiver partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasSendTo partner) :
    (LocalTypeR.send receiver branches).hasSendTo partner :=
  LocalTypeR.hasSendTo.send_branch hmem h

/-- Propagate send partner occurrence through recv branches. -/
theorem LocalTypeR.hasSendTo_recv_branch {sender partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasSendTo partner) :
    (LocalTypeR.recv sender branches).hasSendTo partner :=
  LocalTypeR.hasSendTo.recv_branch hmem h

/-- Propagate recv partner occurrence through send branches. -/
theorem LocalTypeR.hasRecvFrom_send_branch {receiver partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasRecvFrom partner) :
    (LocalTypeR.send receiver branches).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.send_branch hmem h

/-- Propagate recv partner occurrence through recv branches. -/
theorem LocalTypeR.hasRecvFrom_recv_branch {sender partner : String} {branches : List BranchR}
    {lb : BranchR} (hmem : lb ∈ branches) (h : lb.2.2.hasRecvFrom partner) :
    (LocalTypeR.recv sender branches).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.recv_branch hmem h

/-- Any noncontractive mu counts as sending to every partner. -/
theorem LocalTypeR.hasSendTo_noncontractive {t : String} {body : LocalTypeR} {partner : String}
    (h : LocalTypeR.lcontractive body = false) : (LocalTypeR.mu t body).hasSendTo partner :=
  LocalTypeR.hasSendTo.noncontractive h

/-- Any noncontractive mu counts as receiving from every partner. -/
theorem LocalTypeR.hasRecvFrom_noncontractive {t : String} {body : LocalTypeR} {partner : String}
    (h : LocalTypeR.lcontractive body = false) : (LocalTypeR.mu t body).hasRecvFrom partner :=
  LocalTypeR.hasRecvFrom.noncontractive h



end SessionTypes.LocalTypeR
