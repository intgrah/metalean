/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
public import Metalean.TypeTheory.NaturalModel.False

@[expose] public noncomputable section

namespace Metalean.TypeTheory

open CategoryTheory Opposite NaturalModel

local notation "y" => yoneda.obj

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  [HasSorts Ty Tm 0] [HasPi Ty Tm] {ζ : Sigs} {E : Env ζ} {Γ : C}

structure Realisation (E : Env ζ) (Ty : Cᵒᵖ ⥤ Type u) {Tm : Cᵒᵖ ⥤ Type u}
    [NaturalModel Ty Tm] [HasSorts Ty Tm 0] [HasPi Ty Tm] (Γ : C) where
  type {t : Expr ζ 0 0} (ht : E[.nil] ⊢ t typ) :
    y Γ ⟶ Ty
  term {e t : Expr ζ 0 0} (ht : E[.nil] ⊢ t typ)
    (he : E[.nil] ⊢ e : t) :
    Sect (type ht)
  type_falseTy :
    ∀ ht : E[.nil] ⊢ (.falseTy : Expr ζ 0 0) typ,
    type ht = falseType Ty 0 Γ

theorem Realisation.con (R : Realisation E Ty Γ) (h : IsEmpty (Sect (falseType Ty 0 Γ))) : E.Con := by
  intro hall
  have ⟨_, he⟩ := hall .falseTy (Expr.falseTy_isType E)
  exact h.elim (Sect.convert (R.type_falseTy (Expr.falseTy_isType E))
    (R.term (Expr.falseTy_isType E) he))

end Metalean.TypeTheory
