/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
import Metalean.Meta.InductionCases

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ ℓ' n m : Nat} {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n m}
  {e₁ e₂ t : Expr ζ ℓ n}

theorem Defeq.instLevel (ls : Param ℓ → Level ℓ') :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ.instL ls] ⊢ e₁.instL ls ≡ e₂.instL ls : t.instL ls := by
  intro d
  induction_cases d with c =>
    simp -failIfUnchanged [Expr.instL, Ctx.get_instL] at *
    apply c <;> solve_by_elim [-c, Inductive.RecAllowed.instL]

theorem WFTele.instLevel {P : Level ℓ → Prop} {Q : Level ℓ' → Prop}
    (ls : Param ℓ → Level ℓ')
    (hPQ : ∀ {u}, P u → Q (u.inst ls)) (hΔ : WFTele E P Γ Δ) :
    WFTele E Q (Γ.instL ls) (Δ.instL ls) := by
  induction hΔ with
  | nil => exact .nil
  | @snoc b Δ t _ hA ih =>
    have ⟨l, hA, hu⟩ := hA
    refine .snoc ih ⟨_, ?_, hPQ hu⟩
    have hA := hA.instLevel ls
    rw [Ctx.instL_append] at hA
    change E[Ctx.instL ls Γ ++ Ctx.instL ls Δ] ⊢
      Expr.instL ls t : .sort (l.inst ls)
    simpa [Expr.instL] using hA

theorem Inductive.IdxWF.instLevel {ι : IndSig} {I : Inductive ζ ι} {s : Fin ι.nsorts}
    {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ n}
    {is : Fin (ι.nindices s) → Expr ζ ℓ n}
    (h : I.IdxWF E Γ s ls ps is) (ls' : Param ℓ → Level ℓ') :
    I.IdxWF E (Γ.instL ls') s (fun i => (ls i).inst ls')
      (fun i => (ps i).instL ls') fun i => (is i).instL ls' := by
  intro index
  simpa using (h index).instLevel ls'

end Metalean
