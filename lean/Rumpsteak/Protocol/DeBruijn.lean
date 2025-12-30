import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR

/-! # Rumpsteak.Protocol.DeBruijn

De Bruijn index representation for session types.

## Overview

This module provides de Bruijn index representations for session types,
enabling α-equivalence: types that differ only in variable names produce
identical serializations.

De Bruijn indices replace named variables with numeric indices representing
binding depth. For example:

```
Named:       μx. A → B : x        μy. A → B : y
De Bruijn:   μ. A → B : 0         μ. A → B : 0
                  ↑ same canonical form ↑
```

## Rust Correspondence

This module corresponds to `rust/types/src/de_bruijn.rs`.
-/

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.LocalTypeR

namespace Rumpsteak.Protocol.DeBruijn

/-- Global type with de Bruijn indices (for serialization only). -/
inductive GlobalTypeDB where
  | endDB : GlobalTypeDB
  | commDB : String → String → List (Label × GlobalTypeDB) → GlobalTypeDB
  | muDB : GlobalTypeDB → GlobalTypeDB
  | varDB : Nat → GlobalTypeDB
deriving Repr, BEq, Inhabited

/-- Local type with de Bruijn indices (for serialization only). -/
inductive LocalTypeRDB where
  | endDB : LocalTypeRDB
  | sendDB : String → List (Label × LocalTypeRDB) → LocalTypeRDB
  | recvDB : String → List (Label × LocalTypeRDB) → LocalTypeRDB
  | muDB : LocalTypeRDB → LocalTypeRDB
  | varDB : Nat → LocalTypeRDB
deriving Repr, BEq, Inhabited

/-- Find the index of an element in a list. -/
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  let rec go (i : Nat) : List α → Option Nat
    | [] => none
    | x :: xs => if p x then some i else go (i + 1) xs
  go 0 xs

/-- Convert a GlobalType to de Bruijn representation. -/
partial def globalToDeBruijn (g : GlobalType) (env : List String := []) : GlobalTypeDB :=
  match g with
  | .end => .endDB
  | .comm sender receiver branches =>
    .commDB sender receiver (branches.map fun (l, cont) => (l, globalToDeBruijn cont env))
  | .mu t body =>
    .muDB (globalToDeBruijn body (t :: env))
  | .var t =>
    match List.findIndex env (· == t) with
    | some idx => .varDB idx
    | none => .varDB env.length

/-- Convert a LocalTypeR to de Bruijn representation. -/
partial def localToDeBruijn (t : LocalTypeR) (env : List String := []) : LocalTypeRDB :=
  match t with
  | .end => .endDB
  | .send partner branches =>
    .sendDB partner (branches.map fun (l, cont) => (l, localToDeBruijn cont env))
  | .recv partner branches =>
    .recvDB partner (branches.map fun (l, cont) => (l, localToDeBruijn cont env))
  | .mu v body =>
    .muDB (localToDeBruijn body (v :: env))
  | .var v =>
    match List.findIndex env (· == v) with
    | some idx => .varDB idx
    | none => .varDB env.length

/-- Normalize branch ordering for deterministic serialization. -/
partial def GlobalTypeDB.normalize : GlobalTypeDB → GlobalTypeDB
  | .endDB => .endDB
  | .commDB sender receiver branches =>
    let sortedBranches := branches.map (fun (l, cont) => (l, cont.normalize))
      |>.mergeSort (fun a b => a.1.name < b.1.name)
    .commDB sender receiver sortedBranches
  | .muDB body => .muDB body.normalize
  | .varDB idx => .varDB idx

/-- Normalize branch ordering for local types. -/
partial def LocalTypeRDB.normalize : LocalTypeRDB → LocalTypeRDB
  | .endDB => .endDB
  | .sendDB partner branches =>
    let sortedBranches := branches.map (fun (l, cont) => (l, cont.normalize))
      |>.mergeSort (fun a b => a.1.name < b.1.name)
    .sendDB partner sortedBranches
  | .recvDB partner branches =>
    let sortedBranches := branches.map (fun (l, cont) => (l, cont.normalize))
      |>.mergeSort (fun a b => a.1.name < b.1.name)
    .recvDB partner sortedBranches
  | .muDB body => .muDB body.normalize
  | .varDB idx => .varDB idx

/-- Convert from de Bruijn back to named representation. -/
partial def GlobalTypeDB.toGlobalType (db : GlobalTypeDB) (names : List String := []) : GlobalType :=
  match db with
  | .endDB => .end
  | .commDB sender receiver branches =>
    .comm sender receiver (branches.map fun (l, cont) => (l, cont.toGlobalType names))
  | .muDB body =>
    let varName := s!"t{names.length}"
    .mu varName (body.toGlobalType (varName :: names))
  | .varDB idx =>
    match names[idx]? with
    | some name => .var name
    | none => .var s!"free{idx}"

/-- Convert from de Bruijn back to named representation. -/
partial def LocalTypeRDB.toLocalTypeR (db : LocalTypeRDB) (names : List String := []) : LocalTypeR :=
  match db with
  | .endDB => .end
  | .sendDB partner branches =>
    .send partner (branches.map fun (l, cont) => (l, cont.toLocalTypeR names))
  | .recvDB partner branches =>
    .recv partner (branches.map fun (l, cont) => (l, cont.toLocalTypeR names))
  | .muDB body =>
    let varName := s!"t{names.length}"
    .mu varName (body.toLocalTypeR (varName :: names))
  | .varDB idx =>
    match names[idx]? with
    | some name => .var name
    | none => .var s!"free{idx}"

/-- Two global types are α-equivalent iff their de Bruijn forms are equal. -/
def globalAlphaEquiv (g1 g2 : GlobalType) : Bool :=
  globalToDeBruijn g1 == globalToDeBruijn g2

/-- Two local types are α-equivalent iff their de Bruijn forms are equal. -/
def localAlphaEquiv (t1 t2 : LocalTypeR) : Bool :=
  localToDeBruijn t1 == localToDeBruijn t2

end Rumpsteak.Protocol.DeBruijn
