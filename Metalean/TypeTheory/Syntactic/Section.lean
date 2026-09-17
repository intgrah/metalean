/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Substitution
import Metalean.Strong

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Limits TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {t : Expr ζ ℓ Γ₂.as.len} {t₁ t₂ : Expr ζ ℓ Γ₁.as.len} {u u₁ u₂ : Level ℓ}

abbrev Raw.ContextSection {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ} (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂) :=
  Section (CtxCat.rawExtensionIsRepresented ht) σ label

namespace Raw.ContextSection

open CtxCat

def ofTyping {Γ₁ Γ₂ : CtxCat E ℓ} {t : Expr ζ ℓ Γ₂.as.len} {u : Level ℓ}
    (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ : Γ₁.as ⟶ Γ₂.as) {e : Expr ζ ℓ Γ₁.as.len}
    (he : E[Γ₁.as.ctx] ⊢ₛ e : t.subst σ.subst) :
    Raw.ContextSection ht (RawCtx.toCtx.map σ) (Tm.label Γ₁.as he) where
  hom := RawCtx.toCtx.map (σ.snoc ⟨u, ht⟩ he)
  over := snoc_projection Γ₂ ht σ he
  generic := by
    refine (Tm.map_varLabel (σ.snoc ⟨u, ht⟩ he) _).trans (Tm.label_eq ?_ ?_)
    · rw [Ctx.get_last, RawCtx.Hom.snoc_subst, Expr.wk_subst_extend]
      exact (IsTypeStrong.substitution ⟨u, ht⟩ σ.typed).isTypeEq
    · change E[Γ₁.as.ctx] ⊢ₛ (σ.subst.extend e) (Fin.last _) ≡ e :
        ((Γ₂.as.ctx.snoc t).get (Fin.last _)).subst (σ.subst.extend e)
      rw [Ctx.get_last, Expr.wk_subst_extend, Subst.extend_last]
      exact he

def ofTerm {Γ : CtxCat E ℓ} {t e : Expr ζ ℓ Γ.as.len} {u : Level ℓ}
    (ht : E[Γ.as.ctx] ⊢ₛ t : .sort u) (he : E[Γ.as.ctx] ⊢ₛ e : t) :
    Raw.ContextSection ht (𝟙 Γ) (Tm.label Γ.as he) where
  hom := RawCtx.toCtx.map (RawCtx.Hom.one ⟨u, ht⟩ he)
  over := (snoc_projection Γ ht (𝟙 Γ.as)
    (congr(E[Γ.as.ctx] ⊢ₛ e : $(RawCtx.expr.map_id_apply (Opposite.op Γ.as) t)).mpr he)).trans
      (RawCtx.toCtx.map_id Γ.as)
  generic := by
    refine (Tm.map_varLabel (RawCtx.Hom.one ⟨u, ht⟩ he) _).trans (Tm.label_eq ?_ ?_)
    · rw [Ctx.get_last, RawCtx.Hom.one_subst, Expr.wk_subst_extend, Expr.subst_id]
      exact IsTypeEq.ofDefEq ht
    · change E[Γ.as.ctx] ⊢ₛ (Subst.id.extend e) (Fin.last _) ≡ e :
        ((Γ.as.ctx.snoc t).get (Fin.last _)).subst (Subst.id.extend e)
      rw [Ctx.get_last, Expr.wk_subst_extend, Expr.subst_id, Subst.extend_last]
      exact he

end Raw.ContextSection

namespace Raw.ContextSection

open CtxCat

def mapExtension (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as)
    {σ₂ : Γ₃ ⟶ Γ₁} {label : Tm_ Γ₃}
    (s : Raw.ContextSection (ht.substitution σ₁.typed) σ₂ label) :
    Raw.ContextSection ht (σ₂ ≫ RawCtx.toCtx.map σ₁) label :=
  s.map (extensionMap ht σ₁) (by rw [extensionMap_projection, ← Category.assoc, s.over])
    (map_extensionMap_binderVar ht σ₁)

def cartesianLift (ht : E[Γ₂.as.ctx] ⊢ₛ t : .sort u) (σ₁ : Γ₁.as ⟶ Γ₂.as)
    {σ₂ : Γ₃ ⟶ Γ₁} {label : Tm_ Γ₃}
    (s : Raw.ContextSection ht (σ₂ ≫ RawCtx.toCtx.map σ₁) label) :
    Raw.ContextSection (ht.substitution σ₁.typed) σ₂ label :=
  s.lift (extensionIsPullback ht σ₁) (map_extensionMap_binderVar ht σ₁)

def convert (h : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ : .sort u) {σ : Γ₂ ⟶ Γ₁}
    {label : Tm_ Γ₂} (s : Raw.ContextSection h.right σ label) :
    Raw.ContextSection h.left σ label :=
  s.map (contextConversion (.ofDefEq h) h.left h.right)
    (by rw [contextConversion_projection, s.over]) (contextConversion_binderVar _ _ _)

end Raw.ContextSection

end Metalean
