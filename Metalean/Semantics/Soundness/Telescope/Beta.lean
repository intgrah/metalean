/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Telescope
public import Metalean.Semantics.Soundness.Telescope.Basic
import Metalean.Semantics.Interpretation.Binder.Support
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Soundness.Rules.Function

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

theorem RawFamily.ctxLam_openBeta {P : Level ℓ → Prop} {b m k : Nat}
    (Δ : Ctx ζ ℓ Γ₁.as.len m) (hk : Γ₁.as.len + k = m) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ) (hb : Δ.headRank < b)
    (B : RawFamily (CtxCat.extendTele Γ₁ Δ hΔ)) (fB : B.IsFinitary)
    (iB : ∀ ⦃Γ₄ : CtxCat E ℓ⦄ (σ : Γ₄ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ₂ : RawValuation Γ₄),
      SourceAdmissible σ ρ₂ → (B.app _ σ.op ρ₂).IsDirected)
    (σ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ)
    (ρ₁ : RawValuation Γ₂) (args : Fin k → RawValue Γ₂) (hρ : SourceAdmissible σ (ρ₁.pushFin args)) :
    rawApps ((RawFamily.ctxLam (piLimit E ℓ) (fun Γ₂ e _ => rawInterpret (piLimit E ℓ) Γ₂ e) Γ₁ Δ hΔ hb B).app _
      (σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op ρ₁)
      (fun i => (Tm E ℓ).map σ.op (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ)
        ((Fin.natAdd Γ₁.as.len i).cast hk))) args =
      B.app _ σ.op (ρ₁.pushFin args) := by
  subst m
  simp only [Fin.cast_refl, id_eq]
  induction Δ using Tele.addInduction with
  | nil =>
    change B.app _ (σ ≫ 𝟙 _).op ρ₁ = B.app _ σ.op ρ₁
    rw [Category.comp_id]
  | snoc k Δ A ih =>
    let G := CtxCat.extendTele Γ₁ Δ hΔ.init
    have hA : E[G.as.ctx] ⊢ₛ A : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pA : RawInterpretationProperties G A := pΔ.last G.as.wf
    have .cons _ _ _ htail _ hdir hfixed := hρ
    rw [rawApps_last]
    have hnames :
        (fun i : Fin k => (Tm E ℓ).map σ.op
          (Tm.varLabel (CtxCat.extendTele Γ₁ (Δ.snoc A) hΔ) (Fin.natAdd Γ₁.as.len i.castSucc))) =
        fun i => (Tm E ℓ).map (σ ≫ CtxCat.rawProjection G hA).op
          (Tm.varLabel G (Fin.natAdd Γ₁.as.len i)) :=
      funext fun i => Tm.map_extension_varLabel hA σ (Fin.natAdd Γ₁.as.len i)
    have hbase : σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) =
        (σ ≫ CtxCat.rawProjection G hA) ≫
          RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init) :=
      (Category.assoc σ (CtxCat.rawProjection G hA)
        (RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init))).symm
    rw [hnames, hbase]
    refine (congrArg (fun F : RawValue Γ₂ => rawApplication F _ _)
      (ih (fun i => args i.castSucc) hΔ.init pΔ.init _ _
        (RawFamily.IsFinitary.abstraction _ _ (rawInterpret_isFinitary _ G A) fB)
        (fun _ _ _ hρ => RawAction.abstraction_isDirected _
          (RawFamily.bodyAction_isIdealValued hA pA.ideal iB _ _ hρ)) (σ ≫ CtxCat.rawProjection G hA) htail)).trans ?_
    have hb := RawFamily.rawApplication_singleton_abstraction_eq_body (piLimit E ℓ)
      (CtxCat.rawComprehension hA) (rawInterpret (piLimit E ℓ) G A) fB
      (σ ≫ CtxCat.rawProjection G hA) (ρ₁.pushFin fun i => args i.castSucc)
      (RawFamily.bodyAction_isIdealValued hA pA.ideal iB _ _ htail) ⟨args (Fin.last k), hdir⟩ ⟨σ, rfl, rfl⟩
    exact hb.trans (congrArg (fun X => B.app _ σ.op ((ρ₁.pushFin fun i => args i.castSucc).push X)) hfixed)

theorem RawInterpretationProperties.ctxLam {m : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Γ₁.as.len m) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ) (body : Expr ζ ℓ m)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Γ₁ Δ hΔ) body) :
    RawInterpretationProperties Γ₁ (Ctx.lam body Δ) := by
  induction Δ with
  | nil => exact pbody
  | snoc Δ t ih =>
    have ht : E[Γ₁.as.ctx ++ Δ] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    exact ih hΔ.init pΔ.init (.lam t body)
      (RawInterpretationProperties.lam ht (pΔ.last _) pbody)

theorem RawTyped.ctxLam {m : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Γ₁.as.len m) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ) {e t : Expr ζ ℓ m}
    (pb : RawTyped (CtxCat.extendTele Γ₁ Δ hΔ) e t) :
    RawTyped Γ₁ (Ctx.lam e Δ) (Ctx.pi t Δ) := by
  induction Δ with
  | nil => exact pb
  | snoc Δ A ih => exact ih hΔ.init pΔ.init (pb.lam hΔ.last.choose_spec.2 (pΔ.last _))

theorem rawInterpret_ctxLam_beta {ctx : Ctx ζ ℓ 0 n} (hctx : E[ctx] ⊢ₛ ok)
    (hprops : RawTeleProperties E .nil ctx) (body : Expr ζ ℓ n)
    (pbody : RawInterpretationProperties (⟨ctx, hctx⟩ : CtxCat E ℓ) body)
    (σ : Γ₁ ⟶ (⟨ctx, hctx⟩ : CtxCat E ℓ)) (ρ₁ ρ₂ : RawValuation Γ₁)
    (hρ : SourceAdmissible σ ρ₂) :
    rawApps ((rawInterpret (piLimit E ℓ) (CtxCat.nil E ℓ) (ctx.lam body)).app _
      (CtxCat.toNil Γ₁).op ρ₁)
      (fun v : Var n => (Tm E ℓ).map σ.op (Tm.varLabel ⟨ctx, hctx⟩ v))
      (fun v : Var n => ρ₂ v.db) =
      (rawInterpret (piLimit E ℓ) ⟨ctx, hctx⟩ body).app _ σ.op ρ₂ := by
  have hΔ := hctx.wfTeleStrong
  generalize hc : ctx = ctx' at hctx pbody σ hρ ⊢
  rw [← Tele.nil_append ctx] at hc
  subst ctx'
  simp only [Ctx.lam, Tele.foldr_append, Tele.foldr_nil]
  have plam := RawInterpretationProperties.ctxLam (Γ₁ := CtxCat.nil E ℓ) ctx hΔ hprops body pbody
  rw [plam.subst.closed_valuation (CtxCat.toNil Γ₁) ρ₁ (ρ₂.tailN n),
    rawInterpret_ctxLam (piLimit E ℓ) (Γ := CtxCat.nil E ℓ) ctx hΔ
      (Nat.lt_succ_self ctx.headRank) body]
  simpa [CtxCat.hom_nil_eq _ (CtxCat.toNil Γ₁)] using
    RawFamily.ctxLam_openBeta (Γ₁ := CtxCat.nil E ℓ) ctx (k := n) (by simp)
      hΔ hprops _ _ (rawInterpret_isFinitary _ _ _) pbody.ideal σ
      (ρ₂.tailN n) (fun v : Var n => ρ₂ v.db) (by simpa using hρ)

end Metalean.CoherentShape
