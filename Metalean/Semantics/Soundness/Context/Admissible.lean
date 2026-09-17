module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Interpretation
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {ctx : Ctx ζ ℓ 0 n} {hctx : E[ctx] ⊢ₛ ok}
  {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}

judgement SourceAdmissible : {n : Nat} → {ctx : Ctx ζ ℓ 0 n} → {hctx : E[ctx] ⊢ₛ ok} →
    {Γ₂ : CtxCat E ℓ} → (Γ₂ ⟶ (⟨ctx, hctx⟩ : CtxCat E ℓ)) → RawValuation Γ₂ → Prop where

  ──────────────────── nil {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ CtxCat.nil E ℓ) (ρ : RawValuation Γ₂)
  SourceAdmissible σ ρ

  SourceAdmissible (σ ≫ CtxCat.rawProjection ⟨ctx, hctx⟩ ht) ρ.tail
  ((rawInterpret (CodeAssignment.piLimit E ℓ) ⟨ctx, hctx⟩ t).app _
    (σ ≫ CtxCat.rawProjection ⟨ctx, hctx⟩ ht).op ρ.tail).IsDirected
  (ρ 0).IsDirected
  (CodeAssignment.piLimit E ℓ).rawExtend
    ((rawInterpret (CodeAssignment.piLimit E ℓ) ⟨ctx, hctx⟩ t).app _
      (σ ≫ CtxCat.rawProjection ⟨ctx, hctx⟩ ht).op ρ.tail)
    ((Tm E ℓ).map σ.op (CtxCat.rawComprehension ht).generic) (ρ 0) = ρ 0
  ──────────────────── cons {n : Nat} {ctx : Ctx ζ ℓ 0 n} {hctx : E[ctx] ⊢ₛ ok} {Γ₂ : CtxCat E ℓ}
    {t : Expr ζ ℓ n} {u : Level ℓ}
    (ht : E[ctx] ⊢ₛ t : .sort u) (σ : Γ₂ ⟶ CtxCat.extension ⟨ctx, hctx⟩ ht)
    (ρ : RawValuation Γ₂)
  SourceAdmissible σ ρ

namespace SourceAdmissible

theorem cons_iff (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (σ : Γ₂ ⟶ CtxCat.extension Γ₁ ht) (ρ : RawValuation Γ₂) :
    SourceAdmissible σ ρ ↔
      SourceAdmissible (σ ≫ CtxCat.rawProjection Γ₁ ht) ρ.tail ∧
      ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ t).app _
        (σ ≫ CtxCat.rawProjection Γ₁ ht).op ρ.tail).IsDirected ∧
      (ρ 0).IsDirected ∧
      (CodeAssignment.piLimit E ℓ).rawExtend
        ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ t).app _
          (σ ≫ CtxCat.rawProjection Γ₁ ht).op ρ.tail)
        ((Tm E ℓ).map σ.op (CtxCat.rawComprehension ht).generic) (ρ 0) = ρ 0 :=
  ⟨fun hρ => by cases hρ with | cons _ _ _ h₁ h₂ h₃ h₄ => exact ⟨h₁, h₂, h₃, h₄⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ => .cons ht σ ρ h₁ h₂ h₃ h₄⟩

theorem tail (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    {σ : Γ₂ ⟶ CtxCat.extension Γ₁ ht} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ ρ) :
    SourceAdmissible (σ ≫ CtxCat.rawProjection Γ₁ ht) ρ.tail :=
  ((cons_iff ht σ ρ).mp hρ).1

theorem pullback {σ₁ : Γ₂ ⟶ (⟨ctx, hctx⟩ : CtxCat E ℓ)} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ₁ ρ) (σ₂ : Γ₃ ⟶ Γ₂) :
    SourceAdmissible (σ₂ ≫ σ₁) (ρ.pullback σ₂) := by
  induction hρ with
  | nil σ₁ ρ => exact .nil _ _
  | @cons n ctx hctx Γ₂ t u ht σ₁ ρ htail htideal hhead hfixed ih =>
    refine cons ht (σ₂ ≫ σ₁) (ρ.pullback σ₂) ?_ ?_ ?_ ?_
    · simpa using ih σ₂
    · rw [Category.assoc, ← RawValuation.pullback_tail,
        op_comp, ← RawFamily.app_pullback]
      exact htideal.pullback σ₂
    · exact hhead.pullback σ₂
    · have h := congrArg (fun X : RawValue Γ₂ ↦ X.pullback σ₂) hfixed
      rw [CodeAssignment.pullback_rawExtend, RawFamily.app_pullback,
        ← Functor.map_comp_apply, ← op_comp] at h
      simpa [RawValuation.pullback] using h

theorem push {σ : Γ₂ ⟶ Γ₁} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ ρ) (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    {label : Tm_ Γ₂} (s : Raw.ContextSection ht σ label)
    {X : RawValue Γ₂}
    (htideal : ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ t).app _ σ.op ρ).IsDirected)
    (hX : X.IsDirected)
    (hfixed : (CodeAssignment.piLimit E ℓ).rawExtend
      ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ t).app _ σ.op ρ) label X = X) :
    SourceAdmissible s.hom (ρ.push X) := by
  have hlabel : (Tm E ℓ).map s.hom.op (CtxCat.rawComprehension ht).generic = label :=
    s.generic
  refine cons ht s.hom (ρ.push X) (s.over.symm ▸ hρ) (s.over.symm ▸ htideal) hX ?_
  rw [hlabel]
  exact s.over.symm ▸ hfixed

theorem variable_isDirected {σ : Γ₂ ⟶ (⟨ctx, hctx⟩ : CtxCat E ℓ)} {ρ : RawValuation Γ₂} (hρ : SourceAdmissible σ ρ)
    (v : Var n) : (ρ v.db).IsDirected := by
  induction hρ with
  | nil => exact v.elim0
  | @cons n ctx hctx Γ₂ t u ht σ ρ htail htI hhead hfixed ih =>
    cases v using Fin.lastCases with
    | last => rwa [Var.db_last]
    | cast v =>
      rw [Var.db_castSucc]
      exact ih v

end SourceAdmissible

def HasIdeality (Γ₁ : CtxCat E ℓ) (e : Expr ζ ℓ Γ₁.as.len) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂),
    SourceAdmissible σ ρ →
      ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ e).app _ σ.op ρ).IsDirected

noncomputable def SourceAdmissible.eval {σ : Γ₂ ⟶ Γ₁} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ ρ) {e : Expr ζ ℓ Γ₁.as.len} (he : HasIdeality Γ₁ e) : Domain Γ₂ :=
  ((rawInterpret (CodeAssignment.piLimit E ℓ) Γ₁ e).app _ σ.op ρ).toIdeal (he σ ρ hρ)

end Metalean.CoherentShape
