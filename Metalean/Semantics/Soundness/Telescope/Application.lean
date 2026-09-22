/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Pi.Term
public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Rules.Function
public import Metalean.Semantics.Soundness.Telescope.Transport
import Metalean.Semantics.Interpretation.Application
import Metalean.TypeTheory.Syntactic.Comprehension
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Tgt Γ : CtxCat E ℓ}
  {t : Expr ζ ℓ Src.as.len} {t' : Expr ζ ℓ (Src.as.len + 1)} {u v : Level ℓ}
  {f e : Expr ζ ℓ Tgt.as.len}

theorem RawTyped.apps {k m : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len m) (hk : Src.as.len + k = m)
    (hΔ : TeleWF E P Src.as.ctx Δ) (pΔ : RawTeleProperties E Src.as.ctx Δ)
    {body : Expr ζ ℓ m} (hbody : E[Src.as.ctx ++ Δ] ⊢ body : .sort v)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Src Δ hΔ) body)
    (σ : Tgt.as ⟶ (CtxCat.extendTele Src Δ hΔ).as)
    (hσ : SemanticHom (σ ≫ RawCtx.Hom.teleProjection hΔ))
    (pσ : ∀ i : Fin k, RawTyped Tgt (σ.subst ((Fin.natAdd Src.as.len i).cast hk))
      ((Ctx.get ((Fin.natAdd Src.as.len i).cast hk) (Src.as.ctx ++ Δ)).subst σ.subst))
    (pe : RawTyped Tgt e ((Ctx.pi body Δ).subst (σ ≫ RawCtx.Hom.teleProjection hΔ).subst)) :
    RawTyped Tgt (e.apps fun i : Fin k => σ.subst ((Fin.natAdd Src.as.len i).cast hk))
      (body.subst σ.subst) ∧
    ∀ {Γ : CtxCat E ℓ} (τ : Γ ⟶ Tgt) (ρ : RawValuation Γ), SourceAdmissible τ ρ →
      (rawInterpret (piLimit E ℓ) Tgt (e.apps fun i : Fin k => σ.subst ((Fin.natAdd Src.as.len i).cast hk))).app _ τ.op ρ =
        rawApps ((rawInterpret (piLimit E ℓ) Tgt e).app _ τ.op ρ)
          (fun i : Fin k => (Tm E ℓ).map τ.op (Tm.label Tgt.as (σ.typed ((Fin.natAdd Src.as.len i).cast hk))))
          (fun i : Fin k => (rawInterpret (piLimit E ℓ) Tgt (σ.subst ((Fin.natAdd Src.as.len i).cast hk))).app _ τ.op ρ) := by
  subst m
  simp only [Fin.cast_refl, id_eq] at *
  induction Δ using Tele.addInduction generalizing v with
  | nil =>
    have he : σ ≫ RawCtx.Hom.teleProjection hΔ = σ := Category.comp_id σ
    exact ⟨he ▸ pe, fun _ _ _ => rfl⟩
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    have ht : E[S.as.ctx] ⊢ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pt : RawInterpretationProperties S t := pΔ.last _
    obtain ⟨σ₁, arg, harg, rfl⟩ := RawCtx.Hom.exists_snoc (Γ₂ := S.as) ⟨_, ht⟩ σ
    have hbase : σ₁.snoc ⟨_, ht⟩ harg ≫ RawCtx.Hom.teleProjection hΔ =
        σ₁ ≫ RawCtx.Hom.teleProjection hΔ.init :=
      RawCtx.Hom.ext (funext fun v => Subst.extend_castSucc σ₁.subst arg (v.castLE Δ.le))
    have hσ := (congrArg SemanticHom hbase).mp hσ
    have pe := (congrArg (fun τ : Tgt.as ⟶ Src.as =>
      RawTyped Tgt e ((Ctx.pi body (Δ.snoc t)).subst τ.subst)) hbase).mp pe
    have pσ₁ (i : Fin k) := pσ i.castSucc
    simp only [Fin.natAdd_castSucc, RawCtx.Hom.snoc_subst, Subst.extend_castSucc,
      S, CtxCat.extendTele, Tele.append_snoc, Ctx.get_castSucc, Expr.wk_subst_extend] at pσ₁
    have ⟨pinit, hinit⟩ := ih hΔ.init pΔ.init (.forallEDF ht hbody hbody)
      (.forallE ht hbody pt pbody) σ₁ hσ pe pσ₁
    have hs := SemanticHom.extendTele rfl hΔ.init pΔ.init σ₁ hσ
      (fun i => (pσ₁ i).term) (fun i => (pσ₁ i).fixed)
    have parg := pσ (Fin.last k)
    simp only [Fin.natAdd_last, RawCtx.Hom.snoc_subst, Subst.extend_last,
      S, CtxCat.extendTele, Tele.append_snoc, Ctx.get_last, Expr.wk_subst_extend] at parg
    have hfull := SemanticHom.extendTele rfl hΔ pΔ (σ₁.snoc ⟨_, ht⟩ harg)
      ((congrArg SemanticHom hbase).mpr hσ) (fun i => (pσ i).term) (fun i => (pσ i).fixed)
    have pr := hfull.props pbody
    have pb := (hs.lift ht pt).props pbody
    have hb := hbody.substitution (σ₁.lift ⟨_, ht⟩).typed
    simp only [RawCtx.Hom.snoc_subst] at pr
    dsimp only [RawCtx.Hom.lift] at pb hb
    rw [Expr.subst_forallE] at pinit
    have pa := pinit.app (ht.substitution σ₁.typed) hb pb parg
      (by simpa [RawCtx.Hom.lift, Expr.inst_subst_lift] using pr)
    simp only [Expr.apps_last, Fin.natAdd_castSucc, Fin.natAdd_last, RawCtx.Hom.snoc_subst,
      Subst.extend_castSucc, Subst.extend_last, S, CtxCat.extendTele]
    refine ⟨?_, fun τ ρ hρ => ?_⟩
    · simpa [RawCtx.Hom.lift, Expr.inst_subst_lift] using pa.1
    · rw [pa.2 τ ρ hρ,
        ← rawApplication_singleton]
      dsimp only [SourceAdmissible.eval, ΩLower.toIdeal]
      rw [hinit τ ρ hρ, rawApps_last]
      simp [-Fin.castSucc_natAdd, Fin.natAdd_castSucc, Ctx.get_castSucc, Expr.wk_subst_extend]

theorem RawTyped.applyBound {Γ₁ : CtxCat E ℓ} {k : Nat} {P : Level ℓ → Prop}
    {Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)} {e : Expr ζ ℓ Γ₁.as.len}
    {body : Expr ζ ℓ (Γ₁.as.len + k)} (hΔ : TeleWF E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ)
    (hbody : E[Γ₁.as.ctx ++ Δ] ⊢ body : .sort v)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Γ₁ Δ hΔ) body)
    (pe : RawTyped Γ₁ e (Ctx.pi body Δ)) :
    RawTyped (CtxCat.extendTele Γ₁ Δ hΔ) (e.applyBound k) body := by
  let T := CtxCat.extendTele Γ₁ Δ hΔ
  have pw := (SemanticHom.teleProjection hΔ).typed pe
  have p := RawTyped.apps (Src := Γ₁) (Tgt := T) Δ rfl hΔ pΔ hbody pbody (𝟙 T.as)
    (by simpa using SemanticHom.teleProjection hΔ)
    (fun i => by
      simp only [Fin.cast_refl, id_eq, RawCtx.Hom.id_subst, Expr.subst_id]
      exact pΔ.var hΔ (Fin.natAdd Γ₁.as.len i) (Nat.le_add_right _ _))
    (by simpa using pw)
  simp only [RawCtx.Hom.id_subst, Expr.subst_id] at p
  simp only [Fin.cast_refl, id_eq, T, RawCtx.Hom.teleProjection, Expr.subst_vars] at p
  rw [Expr.applyBound_eq_apps, Expr.wkN_eq_rename]
  exact p.1

end Metalean.CoherentShape
