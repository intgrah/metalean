/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Operations
public import Metalean.Checker.Fast.Acceleration.Attr

@[expose] public section

namespace Metalean.Checker.Fast

namespace FExpr

/-- `Prop` -/
@[fexpr_unfold]
def prop : FExpr :=
  .sort .zero

scoped infixr:25 " ⟶ " => FExpr.forallE

end FExpr

syntax "fexpr_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| fexpr_simp $[[$ls,*]]? $[$loc]?) => do
    let ls := (ls.map (·.getElems)).getD #[]
    `(tactic| simp [fexpr_unfold, FExpr.instFVars, FExpr.instFVarsCore, FExpr.nat, FExpr.bool,
      FExpr.succ, FExpr.zero, FExpr.boolLit, FExpr.op₂, FExpr.natArrow, FExpr.natArrow₂,
      $ls,*] $[$loc]?)

end Metalean.Checker.Fast
