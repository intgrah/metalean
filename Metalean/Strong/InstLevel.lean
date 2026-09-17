/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Defs
import Metalean.Strong.Substitution
import Metalean.Syntax.Substitution
import Metalean.Meta.InductionCases

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ ℓ' n : Nat} {Γ : Ctx ζ ℓ 0 n} {e e₁ e₂ t : Expr ζ ℓ n}

theorem DefeqStrong.instLevel (levelSubst : Param ℓ → Level ℓ') :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ.instL levelSubst] ⊢ₛ e₁.instL levelSubst ≡ e₂.instL levelSubst : t.instL levelSubst := by
  intro d
  induction_cases d with c =>
    simp -failIfUnchanged only [Ctx.get_instL, Expr.instL, Level.inst_succ, Expr.instL_wkClosed,
      Expr.instL_instL, Inductive.paramType_instL, Inductive.indexType_instL, Level.inst_inst,
      Expr.instL_subst, Subst.instL_append, RecField.instantiatedType_instL,
      Ctor.ordinaryFieldExpr_instL, Ctor.recursiveFieldExpr_instL, Ctor.targetIndex_instL,
      Inductive.motiveType_instL, Inductive.caseFnType_instL, Inductive.motiveResult_instL,
      Expr.instL_inst, Level.inst_imax, Expr.instL_wk, Expr.instL_wkFrom,
      Inductive.IsStructure.rebuildTerm_instL, Level.inst_zero, Inductive.iotaType_instL,
      Inductive.iotaLhs_instL, Inductive.iotaRhs_instL, Quot.relType_instL,
      Quot.compatType_instL, Quot.motiveType_instL, Quot.minorType_instL] at *
    apply c <;> solve_by_elim -constructor -symm -exfalso
      [-c, Inductive.RecAllowed.instL]

theorem CtxWFStrong.instLevel (levelSubst : Param ℓ → Level ℓ') :
    E[Γ] ⊢ₛ ok →
    E[Γ.instL levelSubst] ⊢ₛ ok := by
  intro hΓ
  induction hΓ with
  | nil => exact .nil
  | snoc _ ht ih =>
      have ⟨u, ht⟩ := ht
      exact .snoc ih ⟨u.inst levelSubst, ht.instLevel levelSubst⟩

end Metalean
