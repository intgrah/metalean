/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Export.Basic

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

end Metalean.Frontend
