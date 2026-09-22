/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Telescope.Basic
public import Metalean.TypeTheory.Syntactic.Telescope

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Tgt Γ : CtxCat E ℓ}

theorem SemanticSubstitution.liftTele {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : TeleWF E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (σ₁ : Tgt.as ⟶ Src.as)
    (σ₂ : Γ ⟶ CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (hΔ.substitution σ₁.typed))
    (ρs ρt : RawValuation Γ) (args : Fin k → RawValue Γ)
    (hsub : SemanticSubstitution σ₁
      (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed))) ρs ρt)
    (htarget : SourceAdmissible
      (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed))) ρt)
    (hsource : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (σ₁.liftTele hΔ)) (ρs.pushFin args)) :
    SemanticSubstitution (σ₁.liftTele hΔ) σ₂ (ρs.pushFin args) (ρt.pushFin args) ∧
      SourceAdmissible σ₂ (ρt.pushFin args) := by
  induction Δ using Tele.addInduction with
  | nil =>
    change Γ ⟶ Tgt at σ₂
    change SemanticSubstitution σ₁ (σ₂ ≫ 𝟙 _) ρs ρt at hsub
    change SourceAdmissible (σ₂ ≫ 𝟙 _) ρt at htarget
    rw [Category.comp_id] at hsub htarget
    exact ⟨hsub, htarget⟩
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    let T := CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (TeleWF.substitution σ₁.typed hΔ.init)
    let g : T.as ⟶ S.as := σ₁.liftTele hΔ.init
    have ht : E[S.as.ctx] ⊢ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have htσ : E[T.as.ctx] ⊢ t.subst g.subst : .sort hΔ.last.choose := ht.substitution g.typed
    let σ₃ := σ₂ ≫ CtxCat.rawProjection T htσ
    let xs : Fin k → RawValue Γ := fun i => args i.castSucc
    let υs := ρs.pushFin xs
    let υt := ρt.pushFin xs
    have hbase : σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed)) =
        σ₃ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (TeleWF.substitution σ₁.typed hΔ.init)) := by
      erw [RawCtx.Hom.teleProjection_snoc (TeleWF.substitution σ₁.typed hΔ.init) hΔ.last.choose_spec.1 htσ]
      exact (Category.assoc _ _ _).symm
    rw [hbase] at hsub htarget
    change SourceAdmissible (σ₂ ≫ CtxCat.extensionMap ht g) (υs.push (args (Fin.last k))) at hsource
    have htail := hsource.tail ht
    erw [Category.assoc, CtxCat.extensionMap_projection, ← Category.assoc] at htail
    have ⟨hs, ha⟩ := ih hΔ.init pΔ.init σ₃ xs hsub htarget htail
    have heq := (pΔ.last S.as.wf).subst g σ₃ υs υt hs htail
    have .cons _ _ _ _ htI hx hfixed := hsource
    erw [Category.assoc, CtxCat.extensionMap_projection, ← Category.assoc] at htI hfixed
    have hname : (Tm E ℓ).map (σ₂ ≫ CtxCat.extensionMap ht g).op
        (CtxCat.rawComprehension ht).generic =
        (Tm E ℓ).map σ₂.op (CtxCat.rawComprehension htσ).generic := by
      erw [op_comp, Functor.map_comp_apply]
      exact congrArg ((Tm E ℓ).map σ₂.op) (CtxCat.map_extensionMap_binderVar ht g)
    erw [hname, ← heq] at hfixed
    exact ⟨.lift ht g σ₂ υs (ρt.pushFin args) hs,
      .cons htσ σ₂ _ ha (heq.symm ▸ htI) hx hfixed⟩

end Metalean.CoherentShape
