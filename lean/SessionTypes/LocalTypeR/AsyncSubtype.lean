import SessionTypes.LocalTypeR.Unfolding

set_option autoImplicit false

/-!
The Problem. Rust exposes a conservative executable asynchronous-subtyping checker
for local types (SISO phase decomposition + tree compatibility), but Lean lacked a
matching executable relation for parity checks.

Solution Structure. Define executable Lean mirrors of the Rust checker:
1. SISO input/output tree extraction with bounded fuel
2. Phase decomposition for local types
3. Conservative async-subtyping compatibility checks
-/

namespace SessionTypes.LocalTypeR

open SessionTypes.GlobalType

/-- Conservative async-subtyping errors aligned with Rust surfaces. -/
inductive AsyncSubtypeError where
  | notSisoDecomposable
  | inputTreeMismatch
  | outputTreeMismatch
  | phaseMismatch (subPhases supPhases : Nat)
  | unfoldLimitExceeded
  deriving Repr, DecidableEq

/-- Human-readable async-subtyping error message. -/
def AsyncSubtypeError.message : AsyncSubtypeError → String
  | .notSisoDecomposable => "type is not SISO decomposable"
  | .inputTreeMismatch => "input trees do not match"
  | .outputTreeMismatch => "output trees do not match"
  | .phaseMismatch subPhases supPhases =>
      s!"siso phase mismatch: subtype has {subPhases} segments, supertype has {supPhases}"
  | .unfoldLimitExceeded => "siso decomposition exceeded the unfold limit"

/-- Input-tree fragment for SISO decomposition. -/
inductive InputTree where
  | empty
  | recv (partner : String) (branches : List (Label × InputTree))
  deriving Repr

/-- Output-tree fragment for SISO decomposition. -/
inductive OutputTree where
  | empty
  | send (partner : String) (branches : List (Label × OutputTree))
  deriving Repr

/-- One SISO decomposition segment. -/
structure SisoSegment where
  input : InputTree
  output : OutputTree
  deriving Repr

/-- Default unfold/analysis budget for conservative SISO decomposition. -/
def defaultSisoFuel : Nat := 10000

/-! ## Tree Construction -/

mutual
  /-- Build an input tree (receives only) with fuel. -/
  def buildInputTreeWithFuel (fuel : Nat) (lt : LocalTypeR) : Except AsyncSubtypeError InputTree := do
    match fuel with
    | 0 => .error .unfoldLimitExceeded
    | fuel' + 1 =>
        match lt with
        | .end => .ok .empty
        | .var _ => .ok .empty
        | .recv partner branches =>
            let branches' ← buildInputBranchesWithFuel fuel' branches
            .ok (.recv partner branches')
        | _ => .error .notSisoDecomposable

  /-- Build input-tree branches with fuel. -/
  def buildInputBranchesWithFuel (fuel : Nat) (branches : List BranchR) :
      Except AsyncSubtypeError (List (Label × InputTree)) := do
    match branches with
    | [] => .ok []
    | (label, _vt, cont) :: rest =>
        let subtree ←
          match cont with
          | .recv _ _ => buildInputTreeWithFuel fuel cont
          | _ => .ok .empty
        let restTrees ← buildInputBranchesWithFuel fuel rest
        .ok ((label, subtree) :: restTrees)
end

mutual
  /-- Build an output tree (sends only) with fuel. -/
  def buildOutputTreeWithFuel (fuel : Nat) (lt : LocalTypeR) : Except AsyncSubtypeError OutputTree := do
    match fuel with
    | 0 => .error .unfoldLimitExceeded
    | fuel' + 1 =>
        match lt with
        | .end => .ok .empty
        | .var _ => .ok .empty
        | .send partner branches =>
            let branches' ← buildOutputBranchesWithFuel fuel' branches
            .ok (.send partner branches')
        | _ => .error .notSisoDecomposable

  /-- Build output-tree branches with fuel. -/
  def buildOutputBranchesWithFuel (fuel : Nat) (branches : List BranchR) :
      Except AsyncSubtypeError (List (Label × OutputTree)) := do
    match branches with
    | [] => .ok []
    | (label, _vt, cont) :: rest =>
        let subtree ←
          match cont with
          | .send _ _ => buildOutputTreeWithFuel fuel cont
          | _ => .ok .empty
        let restTrees ← buildOutputBranchesWithFuel fuel rest
        .ok ((label, subtree) :: restTrees)
end

/-! ## Continuation Discovery -/

mutual
  /-- Find the first continuation leaving an output phase. -/
  def findOutputContinuationWithFuel (fuel : Nat) (lt : LocalTypeR) :
      Except AsyncSubtypeError (Option LocalTypeR) := do
    match fuel with
    | 0 => .error .unfoldLimitExceeded
    | fuel' + 1 =>
        match lt with
        | .send _ branches => findOutputContinuationInBranchesWithFuel fuel' branches
        | _ => .ok none

  /-- Search output-phase continuation candidates in branch order. -/
  def findOutputContinuationInBranchesWithFuel (fuel : Nat) (branches : List BranchR) :
      Except AsyncSubtypeError (Option LocalTypeR) := do
    match fuel with
    | 0 => .error .unfoldLimitExceeded
    | fuel' + 1 =>
        match branches with
        | [] => .ok none
        | (_, _, cont) :: rest =>
            match cont with
            | .send _ _ =>
                match (← findOutputContinuationWithFuel fuel' cont) with
                | some inner => .ok (some inner)
                | none => findOutputContinuationInBranchesWithFuel fuel' rest
            | _ => .ok (some cont)
end

mutual
  /-- Find the first continuation leaving an input phase. -/
  def findInputContinuationWithFuel (fuel : Nat) (lt : LocalTypeR) :
      Except AsyncSubtypeError (Option LocalTypeR) := do
    match fuel with
    | 0 => .error .unfoldLimitExceeded
    | fuel' + 1 =>
        match lt with
        | .recv _ branches => findInputContinuationInBranchesWithFuel fuel' branches
        | _ => .ok none

  /-- Search input-phase continuation candidates in branch order. -/
  def findInputContinuationInBranchesWithFuel (fuel : Nat) (branches : List BranchR) :
      Except AsyncSubtypeError (Option LocalTypeR) := do
    match fuel with
    | 0 => .error .unfoldLimitExceeded
    | fuel' + 1 =>
        match branches with
        | [] => .ok none
        | (_, _, cont) :: rest =>
            match cont with
            | .recv _ _ =>
                match (← findInputContinuationWithFuel fuel' cont) with
                | some inner => .ok (some inner)
                | none => findInputContinuationInBranchesWithFuel fuel' rest
            | _ => .ok (some cont)
end

/-! ## SISO Decomposition -/

/-- Decompose a local type into conservative SISO segments with fuel. -/
def sisoDecomposeWithFuel (fuel : Nat) (lt : LocalTypeR) :
    Except AsyncSubtypeError (List SisoSegment) := do
  match fuel with
  | 0 => .error .unfoldLimitExceeded
  | fuel' + 1 =>
      match lt with
      | .end => .ok []
      | .var _ => .ok []
      | .mu var body =>
          let unfolded := body.substitute var lt
          sisoDecomposeWithFuel fuel' unfolded
      | .send _ _ =>
          let output ← buildOutputTreeWithFuel fuel' lt
          let continuation ← findOutputContinuationWithFuel fuel' lt
          let tail ←
            match continuation with
            | none => .ok []
            | some cont => sisoDecomposeWithFuel fuel' cont
          .ok ({ input := .empty, output := output } :: tail)
      | .recv _ _ =>
          let input ← buildInputTreeWithFuel fuel' lt
          let continuation ← findInputContinuationWithFuel fuel' lt
          let tail ←
            match continuation with
            | none => .ok []
            | some cont => sisoDecomposeWithFuel fuel' cont
          .ok ({ input := input, output := .empty } :: tail)

/-- Decompose a local type into conservative SISO segments. -/
def sisoDecompose (lt : LocalTypeR) : Except AsyncSubtypeError (List SisoSegment) :=
  sisoDecomposeWithFuel defaultSisoFuel lt

/-! ## Tree Compatibility -/

/-- Find a branch by label name. -/
def findInputBranchByName (branches : List (Label × InputTree)) (name : String) :
    Option (Label × InputTree) :=
  match branches with
  | [] => none
  | (label, tree) :: rest =>
      if label.name == name then
        some (label, tree)
      else
        findInputBranchByName rest name

/-- Find a branch by label name. -/
def findOutputBranchByName (branches : List (Label × OutputTree)) (name : String) :
    Option (Label × OutputTree) :=
  match branches with
  | [] => none
  | (label, tree) :: rest =>
      if label.name == name then
        some (label, tree)
      else
        findOutputBranchByName rest name

mutual
  /-- Conservative compatibility check for input trees. -/
  def inputTreeCompatible : InputTree → InputTree → Bool
    | .empty, .empty => true
    | .recv subPartner subBranches, .recv supPartner supBranches =>
        if subPartner != supPartner then
          false
        else if subBranches.length != supBranches.length then
          false
        else
          inputBranchesCompatible subBranches supBranches
    | _, _ => false

  /-- Branch-wise compatibility for input trees. -/
  def inputBranchesCompatible : List (Label × InputTree) → List (Label × InputTree) → Bool
    | [], _ => true
    | (subLabel, subTree) :: rest, supBranches =>
        match findInputBranchByName supBranches subLabel.name with
        | none => false
        | some (supLabel, supTree) =>
            decide (subLabel = supLabel) &&
            inputTreeCompatible subTree supTree &&
            inputBranchesCompatible rest supBranches
end

mutual
  /-- Conservative compatibility check for output trees. -/
  def outputTreeCompatible : OutputTree → OutputTree → Bool
    | .empty, .empty => true
    | .send subPartner subBranches, .send supPartner supBranches =>
        if subPartner != supPartner then
          false
        else if subBranches.length != supBranches.length then
          false
        else
          outputBranchesCompatible subBranches supBranches
    | _, _ => false

  /-- Branch-wise compatibility for output trees. -/
  def outputBranchesCompatible : List (Label × OutputTree) → List (Label × OutputTree) → Bool
    | [], _ => true
    | (subLabel, subTree) :: rest, supBranches =>
        match findOutputBranchByName supBranches subLabel.name with
        | none => false
        | some (supLabel, supTree) =>
            decide (subLabel = supLabel) &&
            outputTreeCompatible subTree supTree &&
            outputBranchesCompatible rest supBranches
end

/-! ## Conservative Async-Subtyping -/

/-- Check conservative async-subtyping with fuel. -/
def asyncSubtypeWithFuel (fuel : Nat) (sub sup : LocalTypeR) :
    Except AsyncSubtypeError Unit := do
  let subSegments ← sisoDecomposeWithFuel fuel sub
  let supSegments ← sisoDecomposeWithFuel fuel sup
  if subSegments.length != supSegments.length then
    .error (.phaseMismatch subSegments.length supSegments.length)
  else
    let rec go (subs sups : List SisoSegment) : Except AsyncSubtypeError Unit := do
      match subs, sups with
      | [], [] => .ok ()
      | subSeg :: subs', supSeg :: sups' =>
          if !inputTreeCompatible subSeg.input supSeg.input then
            .error .inputTreeMismatch
          else if !outputTreeCompatible subSeg.output supSeg.output then
            .error .outputTreeMismatch
          else
            go subs' sups'
      | _, _ => .error (.phaseMismatch subSegments.length supSegments.length)
    go subSegments supSegments

/-- Check conservative async-subtyping with default fuel. -/
def asyncSubtype (sub sup : LocalTypeR) : Except AsyncSubtypeError Unit :=
  asyncSubtypeWithFuel defaultSisoFuel sub sup

/-! ## Conservative Orphan-Freedom -/

private def branchHasLabelName (branches : List BranchR) (labelName : String) : Bool :=
  branches.any (fun (lbl, _vt, _cont) => lbl.name == labelName)

mutual
  /-- Conservative orphan-freedom check with bounded traversal fuel. -/
  def checkOrphanFreeWithFuel (fuel : Nat) (lt : LocalTypeR) (muStack : List String) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
        match lt with
        | .end => true
        | .var _ => true
        | .send partner branches =>
            branches.all (fun (label, _vt, cont) =>
              hasReachableRecvWithFuel fuel' cont partner label.name [] &&
              checkOrphanFreeWithFuel fuel' cont muStack)
        | .recv _ branches =>
            branches.all (fun (_label, _vt, cont) =>
              checkOrphanFreeWithFuel fuel' cont muStack)
        | .mu var body =>
            if var ∈ muStack then
              true
            else
              checkOrphanFreeWithFuel fuel' body (var :: muStack)

  /-- Reachability search for a matching receive along continuations. -/
  def hasReachableRecvWithFuel
      (fuel : Nat) (lt : LocalTypeR) (partner : String) (labelName : String) (muStack : List String) :
      Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
        match lt with
        | .end => false
        | .var _ => false
        | .send _ branches =>
            branches.any (fun (_label, _vt, cont) =>
              hasReachableRecvWithFuel fuel' cont partner labelName muStack)
        | .recv recvPartner branches =>
            if recvPartner == partner && branchHasLabelName branches labelName then
              true
            else
              branches.any (fun (_label, _vt, cont) =>
                hasReachableRecvWithFuel fuel' cont partner labelName muStack)
        | .mu var body =>
            if var ∈ muStack then
              false
            else
              hasReachableRecvWithFuel fuel' body partner labelName (var :: muStack)
end

/-- Conservative orphan-freedom predicate for local types. -/
def orphanFreeWithFuel (fuel : Nat) (lt : LocalTypeR) : Bool :=
  checkOrphanFreeWithFuel fuel lt []

/-- Conservative orphan-freedom predicate with default traversal fuel. -/
def orphanFree (lt : LocalTypeR) : Bool :=
  orphanFreeWithFuel defaultSisoFuel lt

end SessionTypes.LocalTypeR
