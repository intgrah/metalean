/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Telescope.Substitution
import Metalean.Semantics.Soundness.Context.Transport
import Metalean.TypeTheory.Syntactic.Category

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Tgt Γ : CtxCat E ℓ}

theorem RawTeleProperties.extend_admissible {m k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len m) (hk : Src.as.len + k = m) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (σ₁ : Tgt.as ⟶ (CtxCat.extendTele Src Δ hΔ).as)
    (pσ₁ : ∀ i : Fin k, RawInterpretationProperties Tgt
      (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩))
    (hfixed : ∀ i : Fin k, HasFixedness Tgt
      (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩)
      ((Ctx.get ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩ (Src.as.ctx ++ Δ)).subst σ₁.subst))
    (σ₂ : Γ ⟶ Tgt) (ρs ρt : RawValuation Γ)
    (hsub : SemanticSubstitution (σ₁ ≫ RawCtx.Hom.teleProjection hΔ) σ₂ ρs ρt)
    (hsource : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (σ₁ ≫ RawCtx.Hom.teleProjection hΔ)) ρs)
    (htarget : SourceAdmissible σ₂ ρt) :
    SemanticSubstitution σ₁ σ₂
        (ρs.pushFin fun i : Fin k => (rawInterpret (piLimit E ℓ) Tgt
          (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩)).app _ σ₂.op ρt) ρt ∧
      SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁)
        (ρs.pushFin fun i : Fin k => (rawInterpret (piLimit E ℓ) Tgt
          (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩)).app _ σ₂.op ρt) := by
  subst hk
  induction Δ using Tele.addInduction with
  | nil =>
    erw [Category.comp_id] at hsub hsource
    exact ⟨hsub, hsource⟩
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    have ht : E[S.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    let σ₃ : Tgt.as ⟶ S.as := σ₁ ≫ S.projectionRaw ht
    have hbase : σ₁ ≫ RawCtx.Hom.teleProjection hΔ =
        σ₃ ≫ RawCtx.Hom.teleProjection hΔ.init := RawCtx.Hom.ext rfl
    rw [hbase] at hsub hsource
    have hf (i : Fin k) : HasFixedness Tgt (σ₃.subst (Fin.natAdd Src.as.len i))
        ((S.as.ctx.get (Fin.natAdd Src.as.len i)).subst σ₃.subst) := by
      have q := hfixed i.castSucc
      change HasFixedness Tgt (σ₁.subst (Fin.natAdd Src.as.len i).castSucc)
        ((Ctx.get (Fin.natAdd Src.as.len i).castSucc (S.as.ctx.snoc t)).subst σ₁.subst) at q
      erw [Ctx.get_snoc S.as.ctx t (Fin.natAdd Src.as.len i).castSucc
        (Nat.ne_of_lt (Fin.natAdd Src.as.len i).isLt),
        Expr.wk_subst] at q
      exact q
    have ⟨hsubInit, hadmInit⟩ := ih hΔ.init pΔ.init σ₃ (fun i => pσ₁ i.castSucc) hf hsub hsource
    have harg : E[Tgt.as.ctx] ⊢ₛ σ₁.subst (Fin.last S.as.len) : t.subst σ₃.subst := by
      have q := σ₁.typed (Fin.last S.as.len)
      change E[Tgt.as.ctx] ⊢ₛ σ₁.subst (Fin.last S.as.len) :
        (Ctx.get (Fin.last S.as.len) (S.as.ctx.snoc t)).subst σ₁.subst at q
      erw [Ctx.get_last, Expr.wk_subst] at q
      exact q
    have hargf : HasFixedness Tgt (σ₁.subst (Fin.last S.as.len)) (t.subst σ₃.subst) := by
      have q := hfixed (Fin.last k)
      change HasFixedness Tgt (σ₁.subst (Fin.last S.as.len))
        ((Ctx.get (Fin.last S.as.len) (S.as.ctx.snoc t)).subst σ₁.subst) at q
      erw [Ctx.get_last, Expr.wk_subst] at q
      exact q
    have hσ₁ : σ₃.snoc ⟨_, ht⟩ harg = σ₁ := RawCtx.Hom.ext (Fin.snoc_init_self σ₁.subst)
    have pt : RawInterpretationProperties S t := pΔ.last S.as.wf
    have he := pt.subst σ₃ σ₂ _ ρt hsubInit hadmInit
    have hfix := hargf harg σ₂ ρt htarget
    rw [he] at hfix
    have hadm := hadmInit.push ht ((Raw.ContextSection.ofTyping ht σ₃ harg).pullback σ₂)
      (pt.ideal _ _ hadmInit) ((pσ₁ (Fin.last k)).ideal σ₂ ρt htarget) hfix
    have hs := SemanticSubstitution.snoc ht σ₃ harg (pσ₁ (Fin.last k)).subst
      σ₂ _ ρt htarget hsubInit
    change SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (σ₃.snoc ⟨_, ht⟩ harg)) _ at hadm
    rw [hσ₁] at hs hadm
    exact ⟨hs, hadm⟩

theorem RawTeleProperties.extend_admissible_over {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ)
    (σ₁ : Src.as ⟶ (CtxCat.extendTele Src Δ hΔ).as)
    (hover : σ₁ ≫ RawCtx.Hom.teleProjection hΔ = 𝟙 Src.as)
    (pσ₁ : ∀ i : Fin k, RawInterpretationProperties Src (σ₁.subst (Fin.natAdd Src.as.len i)))
    (hfixed : ∀ i : Fin k, HasFixedness Src (σ₁.subst (Fin.natAdd Src.as.len i))
      ((Ctx.get (Fin.natAdd Src.as.len i) (Src.as.ctx ++ Δ)).subst σ₁.subst))
    (σ₂ : Γ ⟶ Src) (ρ : RawValuation Γ) (hsource : SourceAdmissible σ₂ ρ) :
    SemanticSubstitution σ₁ σ₂
        (ρ.pushFin fun i => (rawInterpret (piLimit E ℓ) Src
          (σ₁.subst (Fin.natAdd Src.as.len i))).app _ σ₂.op ρ) ρ ∧
      SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁)
        (ρ.pushFin fun i => (rawInterpret (piLimit E ℓ) Src
          (σ₁.subst (Fin.natAdd Src.as.len i))).app _ σ₂.op ρ) := by
  apply pΔ.extend_admissible Δ rfl hΔ σ₁ pσ₁ hfixed σ₂ ρ ρ
  · simpa [hover] using SemanticSubstitution.id σ₂ ρ
  · erw [hover, RawCtx.toCtx.map_id, Category.comp_id]
    exact hsource
  · exact hsource

end Metalean.CoherentShape
