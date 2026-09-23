/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Defs
import Metalean.Typing.Substitution
import Metalean.Syntax.Substitution
import Metalean.Meta.InductionCases

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ ℓ' n : Nat} {Γ : Ctx ζ ℓ 0 n} {e e₁ e₂ t : Expr ζ ℓ n}

theorem Defeq.instLevel (ls : Param ℓ → Level ℓ') :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ{ls}] ⊢ e₁{ls} ≡ e₂{ls} : t{ls} := by
  intro d
  induction_cases d with c =>
    simp -failIfUnchanged [Ctx.get_instL] at *
    apply c <;> solve_by_elim [Inductive.RecAllowed.instL]

theorem CtxWF.instLevel (ls : Param ℓ → Level ℓ') :
    E[Γ] ⊢ ok →
    E[Γ{ls}] ⊢ ok := by
  intro hΓ
  induction hΓ with
  | nil => exact .nil
  | snoc _ ht ih =>
      have ⟨u, ht⟩ := ht
      exact .snoc ih ⟨u{ls}, ht.instLevel ls⟩

end Metalean
