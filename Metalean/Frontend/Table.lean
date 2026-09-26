/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Export.Basic
public import Metalean.Frontend.Failure

@[expose] public section

namespace Metalean.Frontend

open Lean (Name)

inductive Binding where
  | const (pos : Nat)
  | ind (pos s : Nat)
  | ctor (pos s c : Nat) (metaOrder : List Nat)
  | recr (pos s : Nat) (orders : List (List (List Nat)))
  | quot (pos : Nat) (kind : Export.QuotKind)
deriving DecidableEq, Repr

abbrev Table := Std.HashMap Name Binding

def Table.const (t : Table) (name : Name) : Except Failure Nat :=
  match t.get? name with
  | some (.const pos) => pure pos
  | _ => throw (.reject (.unknownName name))

def Table.ind (t : Table) (name : Name) : Except Failure Nat :=
  match t.get? name with
  | some (.ind pos 0) => pure pos
  | _ => throw (.reject (.unknownName name))

end Metalean.Frontend
