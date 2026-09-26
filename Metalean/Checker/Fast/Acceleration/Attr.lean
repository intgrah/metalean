/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public meta import Lean.Meta.Tactic.Simp
public import Lean.Meta.Tactic.Simp

public meta section

/-- FExpr builders unfolded by `fexpr_simp` -/
register_simp_attr fexpr_unfold
