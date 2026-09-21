/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Telescope.Application
public import Metalean.Semantics.Soundness.Telescope.Transport

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)}
  {e : Expr ζ ℓ Γ₁.as.len} {body : Expr ζ ℓ (Γ₁.as.len + k)} {v : Level ℓ}

theorem applyBound_ideal_fixed (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ)
    (hbody : E[Γ₁.as.ctx ++ Δ] ⊢ₛ body : .sort v)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Γ₁ Δ hΔ) body)
    (he : E[Γ₁.as.ctx] ⊢ₛ e : Ctx.pi body Δ)
    (pe : RawInterpretationProperties Γ₁ e) (fe : HasFixedness Γ₁ e (Ctx.pi body Δ)) :
    HasIdeality (CtxCat.extendTele Γ₁ Δ hΔ) (e.applyBound k) ∧
      HasFixedness (CtxCat.extendTele Γ₁ Δ hΔ) (e.applyBound k) body ∧
      ∀ {Γ₂ : CtxCat E ℓ} (σ₁ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ : RawValuation Γ₂),
        SourceAdmissible σ₁ ρ →
          (rawInterpret (piLimit E ℓ) (CtxCat.extendTele Γ₁ Δ hΔ) (e.applyBound k)).app _ σ₁.op ρ =
            rawApps ((rawInterpret (piLimit E ℓ) (CtxCat.extendTele Γ₁ Δ hΔ) (e.wkN k)).app _ σ₁.op ρ)
              (fun i : Fin k => (Tm E ℓ).map σ₁.op
                (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ) (Fin.natAdd Γ₁.as.len i)))
              (fun i : Fin k => ρ (Var.db i)) := by
  let T := CtxCat.extendTele Γ₁ Δ hΔ
  let σ₂ : T.as ⟶ Γ₁.as := RawCtx.Hom.teleProjection hΔ
  have hcode : (Ctx.pi body Δ).wkN k = (Ctx.pi body Δ).subst σ₂.subst :=
    Expr.wkN_eq_subst _ _
  have ptype := RawInterpretationProperties.pi Δ hΔ pΔ body hbody pbody
  have hw : E[T.as.ctx] ⊢ₛ e.wkN k : (Ctx.pi body Δ).wkN k := he.wkN
  have hw' : E[T.as.ctx] ⊢ₛ e.wkN k : (Ctx.pi body Δ).subst σ₂.subst := by
    rwa [← hcode]
  have hresult : E[T.as.ctx] ⊢ₛ e.applyBound k : body :=
    Ctx.pi_applyBoundStrong T.as.wf hbody he
  have happ : E[T.as.ctx] ⊢ₛ (e.wkN k).apps (fun i : Fin k => (Expr.var (Fin.natAdd Γ₁.as.len i))) :
      body.subst (RawCtx.Hom.subst (𝟙 T.as)) := by
    change E[T.as.ctx] ⊢ₛ (e.wkN k).apps (fun i : Fin k => Expr.var (Fin.natAdd Γ₁.as.len i)) :
      body.subst Subst.id
    simpa [Expr.applyBound_eq_apps] using hresult
  have hf : HasFixedness T (e.wkN k) ((Ctx.pi body Δ).wkN k) :=
    HasFixedness.wkN Δ hΔ he ptype pe fe
  have compute {Γ₂ : CtxCat E ℓ} (σ₁ : Γ₂ ⟶ T) (ρ : RawValuation Γ₂)
      (hρ : SourceAdmissible σ₁ ρ) :
      (rawInterpret (piLimit E ℓ) T (e.applyBound k)).app _ σ₁.op ρ =
        rawApps ((rawInterpret (piLimit E ℓ) T (e.wkN k)).app _ σ₁.op ρ)
          (fun i : Fin k => (Tm E ℓ).map σ₁.op (Tm.varLabel T (Fin.natAdd Γ₁.as.len i)))
          (fun i : Fin k => ρ (Var.db i)) ∧
      ((rawInterpret (piLimit E ℓ) T (e.applyBound k)).app _ σ₁.op ρ).IsDirected ∧
        (piLimit E ℓ).rawExtend
          ((rawInterpret (piLimit E ℓ) T body).app _ σ₁.op ρ)
          ((Tm E ℓ).map σ₁.op (Tm.label T.as hresult))
          ((rawInterpret (piLimit E ℓ) T (e.applyBound k)).app _ σ₁.op ρ) =
          (rawInterpret (piLimit E ℓ) T (e.applyBound k)).app _ σ₁.op ρ := by
    have hvars (i : Fin k) :
        (rawInterpret (piLimit E ℓ) T (.var (Fin.natAdd Γ₁.as.len i))).app _ σ₁.op ρ = ρ (Var.db i) := by
      rw [rawInterpret_var]
      change ρ (Var.db (Fin.natAdd Γ₁.as.len i)) = ρ (Var.db i)
      rw [Var.db_natAdd]
    have hvals : (ρ.tailN k).pushFin (fun i : Fin k =>
        (rawInterpret (piLimit E ℓ) T (.var (Fin.natAdd Γ₁.as.len i))).app _ σ₁.op ρ) = ρ := by
      simp only [hvars]
      simp
    have hfixed := hf hw σ₁ ρ hρ
    rw [ptype.wkN_value hΔ σ₁ ρ hρ, Tm.label_congr (he := hw) (hb := hw') hcode] at hfixed
    have hc := rawInterpret_applyTele_source Δ hΔ pΔ body hbody pbody.ideal σ₂ (e.wkN k) hw'
      (𝟙 T.as) (Category.id_comp σ₂) happ σ₁ (ρ.tailN k) ρ
      ((pe.wkN Δ hΔ).ideal σ₁ ρ hρ) hfixed (by
        erw [RawCtx.toCtx.map_id, Category.comp_id]
        change SourceAdmissible σ₁ ((ρ.tailN k).pushFin (fun i : Fin k =>
          (rawInterpret (piLimit E ℓ) T (.var (Fin.natAdd Γ₁.as.len i))).app _ σ₁.op ρ))
        rwa [hvals])
    erw [RawCtx.toCtx.map_id, Category.comp_id, hvals] at hc
    have hresultName : Tm.label T.as happ = Tm.label T.as hresult := by
      apply Tm.label_eq
      · rw [RawCtx.Hom.id_subst, Expr.subst_id]
        exact IsTypeStrong.isTypeEq ⟨v, hbody⟩
      · rw [RawCtx.Hom.id_subst]
        simpa [Expr.applyBound_eq_apps] using hresult
    erw [hresultName] at hc
    have hvarName (i : Fin k) :
        Tm.label T.as (RawCtx.Hom.typed (𝟙 T.as) (Fin.natAdd Γ₁.as.len i)) =
          Tm.varLabel T (Fin.natAdd Γ₁.as.len i) := by
      have hn := Tm.map_varLabel (𝟙 T.as) (Fin.natAdd Γ₁.as.len i)
      rw [RawCtx.toCtx.map_id, op_id, Functor.map_id_apply] at hn
      exact hn.symm
    simp only [hvarName] at hc
    have hvalues : (fun i : Fin k => (rawInterpret (piLimit E ℓ) T
        (RawCtx.Hom.subst (𝟙 T.as) (Fin.natAdd Γ₁.as.len i))).app _ σ₁.op ρ) =
          (fun i : Fin k => ρ (Var.db i)) := funext hvars
    rw [hvalues] at hc
    have happs : (e.wkN k).apps (fun i : Fin k =>
        RawCtx.Hom.subst (𝟙 T.as) (Fin.natAdd Γ₁.as.len i)) = e.applyBound k :=
      (Expr.applyBound_eq_apps e k).symm
    have hvalue := congrArg (fun a => (rawInterpret (piLimit E ℓ) T a).app _ σ₁.op ρ) happs
    exact congr(($(hvalue) = _) ∧ $(hvalue).IsDirected ∧
      (piLimit E ℓ).rawExtend _ _ $(hvalue) = $(hvalue)).mp hc
  exact ⟨fun _ σ₁ ρ hρ => (compute σ₁ ρ hρ).2.1, fun _ _ σ₁ ρ hρ => (compute σ₁ ρ hρ).2.2,
    fun σ₁ ρ hρ => (compute σ₁ ρ hρ).1⟩

theorem HasSubstitution.applyBound (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ)
    (hbody : E[Γ₁.as.ctx ++ Δ] ⊢ₛ body : .sort v)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Γ₁ Δ hΔ) body)
    (he : E[Γ₁.as.ctx] ⊢ₛ e : Ctx.pi body Δ)
    (pe : RawInterpretationProperties Γ₁ e) (fe : HasFixedness Γ₁ e (Ctx.pi body Δ)) :
    HasSubstitution (CtxCat.extendTele Γ₁ Δ hΔ) (e.applyBound k) := by
  let := Subst.category ζ ℓ
  intro Γ₂ Γ₃ σ₁ σ₂ ρs ρt hσ₁ hsource
  let T := CtxCat.extendTele Γ₁ Δ hΔ
  let σ₃ : T.as ⟶ Γ₁.as := RawCtx.Hom.teleProjection hΔ
  let σ₄ := σ₂ ≫ RawCtx.toCtx.map σ₁
  let σ₅ := σ₁ ≫ σ₃
  have hcode : (Ctx.pi body Δ).wkN k = (Ctx.pi body Δ).subst σ₃.subst :=
    Expr.wkN_eq_subst _ _
  have ptype := RawInterpretationProperties.pi Δ hΔ pΔ body hbody pbody
  have hw : E[T.as.ctx] ⊢ₛ e.wkN k : (Ctx.pi body Δ).wkN k := he.wkN
  have hw' : E[T.as.ctx] ⊢ₛ e.wkN k : (Ctx.pi body Δ).subst σ₃.subst := by
    rwa [← hcode]
  have hcomp := (Subst.functor _ _).map_comp_apply σ₃.subst σ₁.subst (Ctx.pi body Δ)
  have he' : E[Γ₂.as.ctx] ⊢ₛ (e.wkN k).subst σ₁.subst : (Ctx.pi body Δ).subst σ₅.subst :=
    congr(E[Γ₂.as.ctx] ⊢ₛ _ : $(hcomp.symm)).mp (hw'.substitution σ₁.typed)
  have hresult : E[T.as.ctx] ⊢ₛ e.applyBound k : body :=
    Ctx.pi_applyBoundStrong T.as.wf hbody he
  have happ : E[Γ₂.as.ctx] ⊢ₛ ((e.wkN k).subst σ₁.subst).apps
      (fun i : Fin k => σ₁.subst (Fin.natAdd Γ₁.as.len i)) : body.subst σ₁.subst :=
    congr(E[Γ₂.as.ctx] ⊢ₛ $((congrArg (Expr.subst σ₁.subst) (Expr.applyBound_eq_apps e k)).trans
        (((Expr.appSubstHom.finFold k).naturality_apply σ₁.subst
          ⟨e.wkN k, fun i => Expr.var (Fin.natAdd Γ₁.as.len i)⟩).symm)) : _).mp
      (hresult.substitution σ₁.typed)
  have heq := (pe.wkN Δ hΔ).subst σ₁ σ₂ ρs ρt hσ₁ hsource
  have ha (i : Fin k) : (rawInterpret (piLimit E ℓ) Γ₂
      (σ₁.subst (Fin.natAdd Γ₁.as.len i))).app _ σ₂.op ρt = ρs (Var.db i) := by
    simpa using hσ₁.variable_eq hsource (Fin.natAdd Γ₁.as.len i)
  have hf : HasFixedness T (e.wkN k) ((Ctx.pi body Δ).wkN k) :=
    HasFixedness.wkN Δ hΔ he ptype pe fe
  have hfixed := hf hw σ₄ ρs hsource
  rw [ptype.wkN_value hΔ σ₄ ρs hsource, Tm.label_congr hcode] at hfixed
  have hn : (Tm E ℓ).map σ₂.op (Tm.label Γ₂.as he') =
      (Tm E ℓ).map σ₄.op (Tm.label T.as hw') :=
    (congrArg ((Tm E ℓ).map σ₂.op)
      ((Tm.label_congr hcomp).trans (Tm.map_label hw' σ₁).symm)).trans
      ((Tm E ℓ).map_comp_apply (RawCtx.toCtx.map σ₁).op σ₂.op (Tm.label T.as hw')).symm
  have hei : ((rawInterpret (piLimit E ℓ) Γ₂ ((e.wkN k).subst σ₁.subst)).app _ σ₂.op ρt).IsDirected := by
    rw [heq]
    exact (pe.wkN Δ hΔ).ideal σ₄ ρs hsource
  have hff : (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi body Δ)).app _ (σ₂ ≫ RawCtx.toCtx.map σ₅).op (ρs.tailN k))
      ((Tm E ℓ).map σ₂.op (Tm.label Γ₂.as he'))
      ((rawInterpret (piLimit E ℓ) Γ₂ ((e.wkN k).subst σ₁.subst)).app _ σ₂.op ρt) =
      (rawInterpret (piLimit E ℓ) Γ₂ ((e.wkN k).subst σ₁.subst)).app _ σ₂.op ρt := by
    rwa [heq, hn, RawCtx.toCtx.map_comp, ← Category.assoc]
  have hadm : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁)
      ((ρs.tailN k).pushFin fun i : Fin k => (rawInterpret (piLimit E ℓ) Γ₂
        (σ₁.subst (Fin.natAdd Γ₁.as.len i))).app _ σ₂.op ρt) := by
    simp_rw [ha]
    rwa [RawValuation.pushFin_tailN]
  have htarget := rawInterpret_applyTele_source Δ hΔ pΔ body hbody pbody.ideal σ₅
    ((e.wkN k).subst σ₁.subst) he' σ₁ rfl happ σ₂ (ρs.tailN k) ρt hei hff hadm
  have hsrc := (applyBound_ideal_fixed hΔ pΔ hbody pbody he pe fe).2.2 σ₄ ρs hsource
  conv_lhs => rw [Expr.applyBound_eq_apps, Expr.subst_apps]
  erw [htarget.1, hsrc, heq]
  congr 1
  · funext i
    rw [← Tm.map_varLabel σ₁, op_comp, Functor.map_comp_apply]
  · funext i
    exact ha i

end Metalean.CoherentShape
