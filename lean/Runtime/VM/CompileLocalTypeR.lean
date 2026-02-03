import Std
import Runtime.VM.Core
import Runtime.VM.TypeClasses
import SessionTypes.LocalTypeR
import Protocol.LocalType

/-!
# Compile LocalTypeR to VM Bytecode

Compiler from SessionTypes.LocalTypeR into Runtime VM instructions, plus a
LocalTypeR → LocalType conversion helper for building program images.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

/-- LocalType is inhabited for partial conversions. -/
instance : Inhabited LocalType := ⟨.end_⟩

/-- Convert SessionTypes.ValType to Protocol.ValType. -/
def valTypeRToValType : SessionTypes.ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod a b => .prod (valTypeRToValType a) (valTypeRToValType b)
  | .chan sid role => .chan sid role

/-- Find the de Bruijn index of a variable in a binder context. -/
def findVarIdx (ctx : List String) (name : String) : Nat :=
  match ctx.findIdx? (fun x => x == name) with
  | some idx => idx
  | none => 0

/-- Convert LocalTypeR (named recursion) to LocalType (de Bruijn). -/
partial def localTypeRToLocalTypeAux (ctx : List String) (lt : LocalTypeR) : LocalType :=
  match lt with
  | .end => .end_
  | .send partner branches =>
      match branches with
      | [] => .end_
      | (lbl, vt, cont) :: [] =>
          match vt with
          | some t => .send partner (valTypeRToValType t) (localTypeRToLocalTypeAux ctx cont)
          | none => .select partner [(lbl.name, localTypeRToLocalTypeAux ctx cont)]
      | _ =>
          let bs := branches.map (fun (lbl, _vt, cont) =>
            (lbl.name, localTypeRToLocalTypeAux ctx cont))
          .select partner bs
  | .recv partner branches =>
      match branches with
      | [] => .end_
      | (lbl, vt, cont) :: [] =>
          match vt with
          | some t => .recv partner (valTypeRToValType t) (localTypeRToLocalTypeAux ctx cont)
          | none => .branch partner [(lbl.name, localTypeRToLocalTypeAux ctx cont)]
      | _ =>
          let bs := branches.map (fun (lbl, _vt, cont) =>
            (lbl.name, localTypeRToLocalTypeAux ctx cont))
          .branch partner bs
  | .mu v body => .mu (localTypeRToLocalTypeAux (v :: ctx) body)
  | .var v => .var (findVarIdx ctx v)

/-- Public LocalTypeR → LocalType conversion. -/
def localTypeRToLocalType (lt : LocalTypeR) : LocalType :=
  localTypeRToLocalTypeAux [] lt

/-- Replace the element at index `n` in a list. -/
def listSet {α : Type u} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

mutual
  partial def compileInner {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
      [Inhabited (EffectModel.EffectAction ε)]
      (defaultAction : EffectModel.EffectAction ε)
      (t : LocalTypeR)
      (code : List (Instr γ ε))
      (loopTargets : List (String × PC))
      : List (Instr γ ε) × List (String × PC) :=
    match t with
    | .end => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
    | .send _ branches =>
        match branches with
        | [] => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
        | (_, _vt, cont) :: [] =>
            let code := code ++ [Instr.send (γ:=γ) (ε:=ε) 0 1, Instr.invoke (γ:=γ) (ε:=ε) defaultAction]
            compileInner defaultAction cont code loopTargets
        | (lbl, _vt, cont) :: _ =>
            -- Deterministic choice: select the first label (matches default handler behavior).
            let code := code ++ [Instr.offer (γ:=γ) (ε:=ε) 0 lbl.name]
            compileInner defaultAction cont code loopTargets
    | .recv _ branches =>
        match branches with
        | [] => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)
        | (_, _vt, cont) :: [] =>
            let code := code ++ [Instr.recv (γ:=γ) (ε:=ε) 0 1, Instr.invoke (γ:=γ) (ε:=ε) defaultAction]
            compileInner defaultAction cont code loopTargets
        | _ => compileRecvBranches defaultAction branches code loopTargets
    | .mu v body =>
        let target := code.length
        let loopTargets := (v, target) :: loopTargets
        compileInner defaultAction body code loopTargets
    | .var v =>
        match loopTargets.find? (fun p => p.fst == v) with
        | some (_, target) => (code ++ [Instr.jmp (γ:=γ) (ε:=ε) target], loopTargets)
        | none => (code ++ [Instr.halt (γ:=γ) (ε:=ε)], loopTargets)

  partial def compileRecvBranches {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
      [Inhabited (EffectModel.EffectAction ε)]
      (defaultAction : EffectModel.EffectAction ε)
      (branches : List BranchR)
      (code : List (Instr γ ε))
      (loopTargets : List (String × PC))
      : List (Instr γ ε) × List (String × PC) :=
    let placeholderPc := code.length
    let code := code ++ [Instr.choose (γ:=γ) (ε:=ε) 0 ([] : List (String × PC))]
    let step := fun (acc : List (Instr γ ε) × List (String × PC) × List (String × PC))
        (b : BranchR) =>
      let (accCode, table, accLoops) := acc
      let (lbl, _vt, cont) := b
      let startPc := accCode.length
      let (accCode', accLoops') := compileInner defaultAction cont accCode accLoops
      (accCode', table ++ [(lbl.name, startPc)], accLoops')
    let (code, table, loopTargets) := branches.foldl step (code, ([] : List (String × PC)), loopTargets)
    let code : List (Instr γ ε) :=
      listSet code placeholderPc (Instr.choose (γ:=γ) (ε:=ε) 0 table)
    (code, loopTargets)
end

/-- Compile LocalTypeR into bytecode instructions. -/
def ensureTerminal {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (code : List (Instr γ ε)) : List (Instr γ ε) :=
  match code.getLast? with
  | some .halt => code
  | some (.jmp _) => code
  | _ => code ++ [Instr.halt (γ:=γ) (ε:=ε)]

/- ensureTerminal does not change program behavior for well-formed compiles; it
   only guarantees a terminal instruction at the end. -/
def compileLocalTypeR {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    [Inhabited (EffectModel.EffectAction ε)]
    (lt : LocalTypeR) : List (Instr γ ε) :=
  let defaultAction : EffectModel.EffectAction ε := default
  let (code, _) := compileInner (γ:=γ) (ε:=ε) defaultAction lt [] []
  ensureTerminal (γ:=γ) (ε:=ε) code
