module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Interpretation
import Metalean.Semantics.Interpretation.Binder.Pi
import Metalean.Semantics.Interpretation.Binder.Support
import Metalean.TypeTheory.Syntactic.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {t f e : Expr ζ ℓ Γ₁.as.len} {t' : Expr ζ ℓ (Γ₁.as.len + 1)} {u v : Level ℓ} {k : Nat}

theorem rawInterpret_app_subst (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v) (he : E[Γ₁.as.ctx] ⊢ₛ e : t)
    (σ₁ : Γ₂.as ⟶ Γ₁.as) (σ₂ : Γ₃ ⟶ Γ₂) (ρs ρt : RawValuation Γ₃)
    (hC : ((rawInterpret (piLimit E ℓ) Γ₁ t).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs).IsDirected)
    (hD : (RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) (rawInterpret (piLimit E ℓ) Γ₁ t)
      (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t')
      (σ₂ ≫ RawCtx.toCtx.map σ₁) ρs).IsIdealValued)
    (hFideal : ((rawInterpret (piLimit E ℓ) Γ₁ f).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs).IsDirected)
    (hXideal : ((rawInterpret (piLimit E ℓ) Γ₁ e).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs).IsDirected)
    (n : Tm_ Γ₃)
    (hFfixed : (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Γ₁ (.forallE t t')).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs) n
      ((rawInterpret (piLimit E ℓ) Γ₁ f).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs) =
      (rawInterpret (piLimit E ℓ) Γ₁ f).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs)
    (ihf : (rawInterpret (piLimit E ℓ) Γ₂ (f.subst σ₁.subst)).app _ σ₂.op ρt =
      (rawInterpret (piLimit E ℓ) Γ₁ f).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs)
    (iha : (rawInterpret (piLimit E ℓ) Γ₂ (e.subst σ₁.subst)).app _ σ₂.op ρt =
      (rawInterpret (piLimit E ℓ) Γ₁ e).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs) :
    (rawInterpret (piLimit E ℓ) Γ₂ ((Expr.app f e).subst σ₁.subst)).app _ σ₂.op ρt =
      (rawInterpret (piLimit E ℓ) Γ₁ (.app f e)).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs := by
  let F : Domain Γ₃ :=
    ((rawInterpret (piLimit E ℓ) Γ₁ f).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs).toIdeal hFideal
  let X : Domain Γ₃ :=
    ((rawInterpret (piLimit E ℓ) Γ₁ e).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs).toIdeal hXideal
  have hfixed : (piLimit E ℓ).rawExtend
      ((RawFamily.pi (piLimit E ℓ) (CtxCat.rawComprehension ht) (Ty.pairOfTyping Γ₁.as ht ht')
        (rawInterpret (piLimit E ℓ) Γ₁ t)
        (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t')).app _
          (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs) n F.val = F.val := by
    rwa [rawInterpret_forallE (piLimit E ℓ) ht ht'] at hFfixed
  have hsupport {Γ₄ : CtxCat E ℓ} (σ₃ : Γ₄ ⟶ Γ₃) (name : Tm_ Γ₄)
      {x y : CoherentShape Γ₄} (hy : OutputAtom (F.pullback σ₃).val name x y) :
      y ≤ ⊥ ∨ Nonempty (Raw.ContextSection ht (σ₃ ≫ σ₂ ≫ RawCtx.toCtx.map σ₁) name) :=
    RawFamily.outputAtom_rawPi_fixed_bot_or_section ht _ (rawInterpret (piLimit E ℓ) Γ₁ t)
      (rawInterpret_isFinitary (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t') _ ρs hC hD n hfixed σ₃ hy
  have htarget := RawFamily.rawApplication_eq_of_sections (ht.substitution σ₁.typed)
    (he.substitution σ₁.typed) σ₂ F X fun σ₃ name _ _ hy =>
      (hsupport σ₃ name hy).imp_right (Nonempty.map fun s =>
        Raw.ContextSection.cartesianLift ht σ₁ (by simpa using s))
  rw [← Tm.map_label he σ₁, ← Functor.map_comp_apply, ← op_comp] at htarget
  rw [Expr.subst_app, rawInterpret_app, rawInterpret_app, RawFamily.application_value,
    RawFamily.application_value, ihf, iha]
  exact htarget.trans (RawFamily.rawApplication_eq_of_sections ht he _ F X hsupport).symm

end Metalean.CoherentShape
