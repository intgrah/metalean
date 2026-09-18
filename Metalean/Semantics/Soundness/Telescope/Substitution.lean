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

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Tgt Γ : CtxCat E ℓ}

theorem SemanticSubstitution.liftTele {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (σ₁ : Tgt.as ⟶ Src.as)
    (σ₂ : Γ ⟶ CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (hΔ.substitution σ₁.typed))
    (ρs ρt : RawValuation Γ) (args : Fin k → RawValue Γ)
    (hsub : SemanticSubstitution σ₁
      (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed))) ρs ρt) :
    SemanticSubstitution (σ₁.liftTele hΔ) σ₂ (ρs.pushFin args) (ρt.pushFin args) := by
  induction Δ using Tele.addInduction with
  | nil =>
    change SemanticSubstitution σ₁ σ₂ ρs ρt
    change SemanticSubstitution σ₁ (σ₂ ≫ RawCtx.toCtx.map (𝟙 Tgt.as)) ρs ρt at hsub
    erw [RawCtx.toCtx.map_id, Category.comp_id] at hsub
    exact hsub
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    let T := CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (hΔ.init.substitution σ₁.typed)
    let g : T.as ⟶ S.as := σ₁.liftTele hΔ.init
    have ht : E[S.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have htσ : E[T.as.ctx] ⊢ₛ t.subst g.subst : .sort hΔ.last.choose := ht.substitution g.typed
    let σ₃ := σ₂ ≫ CtxCat.rawProjection T htσ
    have hbase : σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed)) =
        σ₃ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.init.substitution σ₁.typed)) := by
      erw [RawCtx.Hom.teleProjection_snoc (hΔ.init.substitution σ₁.typed) hΔ.last.choose_spec.1 htσ]
      exact (Category.assoc _ _ _).symm
    rw [hbase] at hsub
    exact SemanticSubstitution.lift ht g σ₂ (ρs.pushFin fun i => args i.castSucc)
      (ρt.pushFin args) (ih hΔ.init σ₃ (fun i => args i.castSucc) hsub)

theorem SemanticSubstitution.tele_admissible {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (σ₁ : Tgt.as ⟶ Src.as)
    (σ₂ : Γ ⟶ CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (hΔ.substitution σ₁.typed))
    (ρs ρt : RawValuation Γ) (args : Fin k → RawValue Γ)
    (hsub : SemanticSubstitution σ₁
      (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed))) ρs ρt)
    (htarget : SourceAdmissible
      (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed))) ρt)
    (hsource : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (σ₁.liftTele hΔ)) (ρs.pushFin args)) :
    SourceAdmissible σ₂ (ρt.pushFin args) := by
  induction Δ using Tele.addInduction with
  | nil => exact Category.comp_id σ₂ ▸ RawCtx.toCtx.map_id Tgt.as ▸ htarget
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    let T := CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (hΔ.init.substitution σ₁.typed)
    let g : T.as ⟶ S.as := σ₁.liftTele hΔ.init
    have ht : E[S.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have htσ : E[T.as.ctx] ⊢ₛ t.subst g.subst : .sort hΔ.last.choose := ht.substitution g.typed
    let σ₃ := σ₂ ≫ CtxCat.rawProjection T htσ
    let xs : Fin k → RawValue Γ := fun i => args i.castSucc
    let υs := ρs.pushFin xs
    let υt := ρt.pushFin xs
    have hbase : σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed)) =
        σ₃ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.init.substitution σ₁.typed)) := by
      erw [RawCtx.Hom.teleProjection_snoc (hΔ.init.substitution σ₁.typed) hΔ.last.choose_spec.1 htσ]
      exact (Category.assoc _ _ _).symm
    rw [hbase] at hsub htarget
    change SourceAdmissible (σ₂ ≫ CtxCat.extensionMap ht g) (υs.push (args (Fin.last k))) at hsource
    have htail := hsource.tail ht
    erw [Category.assoc, CtxCat.extensionMap_projection, ← Category.assoc] at htail
    have heq := (pΔ.last S.as.wf).subst g σ₃ υs υt
      (SemanticSubstitution.liftTele Δ hΔ.init σ₁ σ₃ ρs ρt xs hsub) htail
    have ⟨_, htI, hx, hfixed⟩ := (SourceAdmissible.cons_iff ht _ _).mp hsource
    erw [Category.assoc, CtxCat.extensionMap_projection, ← Category.assoc] at htI hfixed
    have hname : (Tm E ℓ).map (σ₂ ≫ CtxCat.extensionMap ht g).op
        (CtxCat.rawComprehension ht).generic =
        (Tm E ℓ).map σ₂.op (CtxCat.rawComprehension htσ).generic := by
      erw [op_comp, Functor.map_comp_apply]
      exact congrArg ((Tm E ℓ).map σ₂.op) (CtxCat.map_extensionMap_binderVar ht g)
    erw [hname, ← heq] at hfixed
    exact .cons htσ σ₂ _ (ih hΔ.init pΔ.init σ₃ xs hsub htarget htail)
      (heq.symm ▸ htI) hx hfixed

theorem SemanticSubstitution.sectionTele {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (σ₁ : Tgt.as ⟶ Src.as)
    (σ₂ : Γ ⟶ Tgt) (ρs ρt : RawValuation Γ) (args : Fin k → RawValue Γ)
    (hsub : SemanticSubstitution σ₁ σ₂ ρs ρt) (htarget : SourceAdmissible σ₂ ρt)
    (σ₃ : Γ ⟶ CtxCat.extendTele Src Δ hΔ)
    (hover : σ₃ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) = σ₂ ≫ RawCtx.toCtx.map σ₁)
    (hsource : SourceAdmissible σ₃ (ρs.pushFin args)) :
    ∃ σ₄ : Γ ⟶ CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (hΔ.substitution σ₁.typed),
      σ₄ ≫ RawCtx.toCtx.map (σ₁.liftTele hΔ) = σ₃ ∧
      σ₄ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed)) = σ₂ ∧
      (∀ f, (Tm E ℓ).map σ₄.op
        (Tm.varLabel (CtxCat.extendTele Tgt (Ctx.substN σ₁.subst k Δ) (hΔ.substitution σ₁.typed))
          (Fin.natAdd Tgt.as.len f)) =
        (Tm E ℓ).map σ₃.op
          (Tm.varLabel (CtxCat.extendTele Src Δ hΔ) (Fin.natAdd Src.as.len f))) ∧
      SourceAdmissible σ₄ (ρt.pushFin args) := by
  let square := σ₁.liftTele_isPullback hΔ
  let σ₄ := square.lift σ₃ σ₂ hover
  have hfst : σ₄ ≫ RawCtx.toCtx.map (σ₁.liftTele hΔ) = σ₃ := square.lift_fst σ₃ σ₂ hover
  have hsnd : σ₄ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (hΔ.substitution σ₁.typed)) = σ₂ :=
    square.lift_snd σ₃ σ₂ hover
  refine ⟨σ₄, hfst, hsnd, ?_, ?_⟩
  · intro f
    have hn := congrArg ((Tm E ℓ).map σ₄.op) (Tm.map_liftTele_varLabel σ₁ hΔ f)
    exact hn.symm.trans
      (((Tm E ℓ).map_comp_apply (RawCtx.toCtx.map (σ₁.liftTele hΔ)).op σ₄.op _).symm.trans
        (congrArg (fun ν : Γ ⟶ CtxCat.extendTele Src Δ hΔ =>
          (Tm E ℓ).map ν.op (Tm.varLabel (CtxCat.extendTele Src Δ hΔ)
            (Fin.natAdd Src.as.len f))) hfst))
  exact SemanticSubstitution.tele_admissible Δ hΔ pΔ σ₁ σ₄ ρs ρt args
    (by rwa [hsnd]) (by rwa [hsnd]) (by rwa [hfst])

end Metalean.CoherentShape
