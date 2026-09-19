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

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

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
  induction hctx generalizing ρ₂ with
  | nil =>
    change (rawInterpret (piLimit E ℓ) (CtxCat.nil E ℓ) body).app _
      (CtxCat.toNil Γ₁).op ρ₁ = _
    rw [CtxCat.hom_nil_eq (CtxCat.toNil Γ₁) σ]
    exact HasSubstitution.closed_valuation pbody.subst σ ρ₁ ρ₂
  | @snoc n ctx A hctx ht ih =>
    have ⟨u, hA⟩ := ht
    have pA : RawInterpretationProperties (⟨ctx, hctx⟩ : CtxCat E ℓ) A :=
      hprops.entry (by simp) hctx
    have ⟨htail, hdirA, hdir, hfixed⟩ := (SourceAdmissible.cons_iff (Γ₁ := ⟨ctx, hctx⟩) hA σ ρ₂).mp hρ
    rw [rawApps_last]
    have hnames :
        (fun v : Var n => (Tm E ℓ).map σ.op
          (Tm.varLabel ⟨ctx.snoc A, hctx.snoc ⟨u, hA⟩⟩ v.castSucc)) =
        fun v : Var n => (Tm E ℓ).map
          (σ ≫ CtxCat.rawProjection ⟨ctx, hctx⟩ hA).op (Tm.varLabel ⟨ctx, hctx⟩ v) :=
      funext fun v => Tm.map_extension_varLabel (Γ₁ := ⟨ctx, hctx⟩) hA σ v
    simp only [hnames, Var.db_castSucc, Var.db_last]
    refine (congrArg (fun F : RawValue Γ₁ => rawApplication F _ _)
      (ih hprops.init (.lam A body) (RawInterpretationProperties.lam hA pA pbody)
        (σ ≫ CtxCat.rawProjection ⟨ctx, hctx⟩ hA) ρ₂.tail htail)).trans ?_
    rw [rawInterpret_lam (piLimit E ℓ) hA]
    have hb := RawFamily.rawApplication_singleton_abstraction_eq_body (piLimit E ℓ)
      (CtxCat.rawComprehension hA) (rawInterpret (piLimit E ℓ) ⟨ctx, hctx⟩ A)
      (rawInterpret_isFinitary (piLimit E ℓ) (CtxCat.extension ⟨ctx, hctx⟩ hA) body)
      (σ ≫ CtxCat.rawProjection ⟨ctx, hctx⟩ hA) ρ₂.tail
      (HasIdeality.bodyAction hA pA.ideal pbody.ideal _ _ htail)
      ⟨ρ₂ 0, hdir⟩ ⟨σ, rfl, rfl⟩
    exact hb.trans (congrArg
      ((rawInterpret (piLimit E ℓ) (CtxCat.extension ⟨ctx, hctx⟩ hA) body).app _ σ.op)
      ((congrArg ρ₂.tail.push hfixed).trans ρ₂.push_tail))

theorem RawFamily.ctxLam_beta {P : Level ℓ → Prop} {b : Nat} {ctx : Ctx ζ ℓ 0 n}
    (hctx : WFTeleStrong E P (CtxCat.nil E ℓ).as.ctx ctx) (pctx : RawTeleProperties E .nil ctx)
    (hb : ctx.headRank < b) (B : RawFamily (CtxCat.extendTele (CtxCat.nil E ℓ) ctx hctx))
    (fB : B.IsFinitary)
    (iB : ∀ ⦃Γ₃ : CtxCat E ℓ⦄ (σ : Γ₃ ⟶ CtxCat.extendTele (CtxCat.nil E ℓ) ctx hctx)
      (ρ : RawValuation Γ₃), SourceAdmissible σ ρ → (B.app _ σ.op ρ).IsDirected)
    (σ : Γ₁ ⟶ CtxCat.extendTele (CtxCat.nil E ℓ) ctx hctx) (ρ : RawValuation Γ₁)
    (hρ : SourceAdmissible σ ρ) :
    rawApps ((RawFamily.ctxLam (piLimit E ℓ) (fun Γ₁ e _ => rawInterpret (piLimit E ℓ) Γ₁ e)
      (CtxCat.nil E ℓ) ctx hctx hb B).app _ (CtxCat.toNil Γ₁).op (ρ.tailN n))
      (fun v : Var n => (Tm E ℓ).map σ.op
        (Tm.varLabel (CtxCat.extendTele (CtxCat.nil E ℓ) ctx hctx) v))
      (fun v : Var n => ρ v.db) =
      B.app _ σ.op ρ := by
  induction ctx generalizing ρ with
  | nil => exact congrArg (fun τ => B.app _ (Quiver.Hom.op τ) ρ) (CtxCat.hom_nil_eq _ _)
  | @snoc k ctx A ih =>
    let G := CtxCat.extendTele (CtxCat.nil E ℓ) ctx hctx.init
    have hA : E[G.as.ctx] ⊢ₛ A : .sort hctx.last.choose := hctx.last.choose_spec.2
    have pA : RawInterpretationProperties G A := pctx.last G.as.wf
    have ⟨htail, _, hdir, hfixed⟩ := (SourceAdmissible.cons_iff hA σ ρ).mp hρ
    have htailN : ρ.tail.tailN k = ρ.tailN (k + 1) :=
      (RawValuation.tailN_tailN ρ 1 k).trans (congrArg ρ.tailN (Nat.add_comm 1 k))
    rw [← htailN, rawApps_last]
    have hnames :
        (fun v : Var _ => (Tm E ℓ).map σ.op
          (Tm.varLabel (CtxCat.extendTele (CtxCat.nil E ℓ) (ctx.snoc A) hctx) v.castSucc)) =
        fun v => (Tm E ℓ).map (σ ≫ CtxCat.rawProjection G hA).op (Tm.varLabel G v) :=
      funext fun v => Tm.map_extension_varLabel hA σ v
    simp only [hnames, Var.db_castSucc, Var.db_last]
    refine (congrArg (fun F : RawValue Γ₁ => rawApplication F _ _)
      (ih hctx.init pctx.init _ _ (RawFamily.IsFinitary.abstraction _ _
        (rawInterpret_isFinitary _ G A) fB)
        (RawFamily.abstraction_isDirected_of hA pA.ideal iB)
        (σ ≫ CtxCat.rawProjection G hA) ρ.tail htail)).trans ?_
    have hb := RawFamily.rawApplication_singleton_abstraction_eq_body (piLimit E ℓ)
      (CtxCat.rawComprehension hA) (rawInterpret (piLimit E ℓ) G A) fB
      (σ ≫ CtxCat.rawProjection G hA) ρ.tail
      (RawFamily.bodyAction_isIdealValued hA pA.ideal iB _ _ htail) ⟨ρ 0, hdir⟩ ⟨σ, rfl, rfl⟩
    exact hb.trans (congrArg (B.app _ σ.op) ((congrArg ρ.tail.push hfixed).trans ρ.push_tail))

theorem RawFamily.ctxLam_openBeta {P : Level ℓ → Prop} {b m k : Nat}
    (Δ : Ctx ζ ℓ Γ₁.as.len m) (hk : Γ₁.as.len + k = m) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ) (hb : Δ.headRank < b)
    (B : RawFamily (CtxCat.extendTele Γ₁ Δ hΔ)) (fB : B.IsFinitary)
    (iB : ∀ ⦃Γ₄ : CtxCat E ℓ⦄ (σ : Γ₄ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ₂ : RawValuation Γ₄),
      SourceAdmissible σ ρ₂ → (B.app _ σ.op ρ₂).IsDirected)
    (σ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (τ : Γ₂ ⟶ Γ₁)
    (hτ : σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) = τ)
    (names : Fin k → Tm_ Γ₂)
    (hnames : ∀ i, (Tm E ℓ).map σ.op
      (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ) ⟨Γ₁.as.len + i.val, show Γ₁.as.len + i.val < m by omega⟩) =
        names i)
    (ρ₁ : RawValuation Γ₂) (args : Fin k → RawValue Γ₂) (hρ : SourceAdmissible σ (ρ₁.pushFin args)) :
    rawApps ((RawFamily.ctxLam (piLimit E ℓ) (fun Γ₂ e _ => rawInterpret (piLimit E ℓ) Γ₂ e) Γ₁ Δ hΔ hb B).app _
      τ.op ρ₁) names args = B.app _ σ.op (ρ₁.pushFin args) := by
  subst hτ hk
  obtain rfl := funext hnames
  clear hnames
  induction Δ using Tele.addInduction with
  | nil =>
    change B.app _ (σ ≫ 𝟙 _).op ρ₁ = B.app _ σ.op ρ₁
    rw [Category.comp_id]
  | snoc k Δ A ih =>
    let G := CtxCat.extendTele Γ₁ Δ hΔ.init
    have hA : E[G.as.ctx] ⊢ₛ A : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pA : RawInterpretationProperties G A := pΔ.last G.as.wf
    have ⟨htail, _, hdir, hfixed⟩ := (SourceAdmissible.cons_iff hA σ _).mp hρ
    rw [rawApps_last]
    have hnames :
        (fun i : Fin k => (Tm E ℓ).map σ.op
          (Tm.varLabel (CtxCat.extendTele Γ₁ (Δ.snoc A) hΔ) ⟨Γ₁.as.len + i.castSucc.val,
            show Γ₁.as.len + i.castSucc.val < Γ₁.as.len + (k + 1) by rw [Fin.val_castSucc]; omega⟩)) =
        fun i => (Tm E ℓ).map (σ ≫ CtxCat.rawProjection G hA).op
          (Tm.varLabel G ⟨Γ₁.as.len + i.val, show Γ₁.as.len + i.val < Γ₁.as.len + k by omega⟩) :=
      funext fun i => Tm.map_extension_varLabel hA σ
        ⟨Γ₁.as.len + i.val, show Γ₁.as.len + i.val < Γ₁.as.len + k by omega⟩
    have hbase : σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) =
        (σ ≫ CtxCat.rawProjection G hA) ≫
          RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init) :=
      (Category.assoc σ (CtxCat.rawProjection G hA)
        (RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init))).symm
    rw [hnames, hbase]
    refine (congrArg (fun F : RawValue Γ₂ => rawApplication F _ _)
      (ih (fun i => args i.castSucc) hΔ.init pΔ.init _ _
        (RawFamily.IsFinitary.abstraction _ _ (rawInterpret_isFinitary _ G A) fB)
        (RawFamily.abstraction_isDirected_of hA pA.ideal iB) (σ ≫ CtxCat.rawProjection G hA) htail)).trans ?_
    have hb := RawFamily.rawApplication_singleton_abstraction_eq_body (piLimit E ℓ)
      (CtxCat.rawComprehension hA) (rawInterpret (piLimit E ℓ) G A) fB
      (σ ≫ CtxCat.rawProjection G hA) (ρ₁.pushFin fun i => args i.castSucc)
      (RawFamily.bodyAction_isIdealValued hA pA.ideal iB _ _ htail) ⟨args (Fin.last k), hdir⟩ ⟨σ, rfl, rfl⟩
    exact hb.trans (congrArg (fun X => B.app _ σ.op ((ρ₁.pushFin fun i => args i.castSucc).push X)) hfixed)

theorem RawInterpretationProperties.ctxLam {m k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Γ₁.as.len m) (hk : Γ₁.as.len + k = m) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ) (body : Expr ζ ℓ m)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Γ₁ Δ hΔ) body) :
    RawInterpretationProperties Γ₁ (Ctx.lam body Δ) := by
  subst hk
  induction Δ using Tele.addInduction with
  | nil => exact pbody
  | snoc k Δ t ih =>
    have ht : E[Γ₁.as.ctx ++ Δ] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    exact ih hΔ.init pΔ.init (.lam t body)
      (RawInterpretationProperties.lam ht (pΔ.last _) pbody)

theorem HasFixedness.ctxLam {m k : Nat} {P : Level ℓ → Prop} {v : Level ℓ}
    (Δ : Ctx ζ ℓ Γ₁.as.len m) (hk : Γ₁.as.len + k = m) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ) (t' e' : Expr ζ ℓ m)
    (ht' : E[Γ₁.as.ctx ++ Δ] ⊢ₛ t' : .sort v) (he' : E[Γ₁.as.ctx ++ Δ] ⊢ₛ e' : t')
    (pt' : HasIdeality (CtxCat.extendTele Γ₁ Δ hΔ) t')
    (pe' : HasIdeality (CtxCat.extendTele Γ₁ Δ hΔ) e')
    (fb : HasFixedness (CtxCat.extendTele Γ₁ Δ hΔ) e' t') :
    HasFixedness Γ₁ (Ctx.lam e' Δ) (Ctx.pi t' Δ) := by
  subst hk
  induction Δ using Tele.addInduction generalizing v with
  | nil => exact fb
  | snoc k Δ t ih =>
    have ht : E[Γ₁.as.ctx ++ Δ] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pt : HasIdeality (CtxCat.extendTele Γ₁ Δ hΔ.init) t :=
      (pΔ.last (hΔ.init.appendCtxWFStrong Γ₁.as.wf)).ideal
    exact ih hΔ.init pΔ.init (.forallE t t') (.lam t e') (.forallEDF ht ht' ht')
      (.lamDF ht ht' ht' he' he') (HasIdeality.forallE ht ht' pt pt')
      (HasIdeality.lam ht pt pe') (HasFixedness.lam ht ht' he' pt pt' pe' fb)

theorem rawInterpret_openCtxLam_beta {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (hprops : RawTeleProperties E Γ₁.as.ctx Δ) (body : Expr ζ ℓ (Γ₁.as.len + k))
    (pbody : RawInterpretationProperties (CtxCat.extendTele Γ₁ Δ hΔ) body)
    (σ₁ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ₁ : RawValuation Γ₂) (args : Fin k → Domain Γ₂)
    (hρ : SourceAdmissible σ₁ (ρ₁.pushFin fun i => (args i).val)) :
    rawApps ((rawInterpret (piLimit E ℓ) Γ₁ (Ctx.lam body Δ)).app _
      (σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op ρ₁)
      (fun i => (Tm E ℓ).map σ₁.op
        (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ) (Fin.natAdd Γ₁.as.len i)))
      (fun i => (args i).val) =
      (rawInterpret (piLimit E ℓ) (CtxCat.extendTele Γ₁ Δ hΔ) body).app _
        σ₁.op (ρ₁.pushFin fun i => (args i).val) := by
  induction Δ using Tele.addInduction with
  | nil =>
    change (rawInterpret (piLimit E ℓ) Γ₁ body).app _ (σ₁ ≫ 𝟙 Γ₁).op ρ₁ =
      (rawInterpret (piLimit E ℓ) Γ₁ body).app _ σ₁.op ρ₁
    exact congrArg (fun σ₂ : Γ₂ ⟶ Γ₁ =>
      (rawInterpret (piLimit E ℓ) Γ₁ body).app _ σ₂.op ρ₁) (Category.comp_id σ₁)
  | snoc k Δ t ih =>
    let G := CtxCat.extendTele Γ₁ Δ hΔ.init
    have ht : E[G.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pt : RawInterpretationProperties G t := hprops.last G.as.wf
    let σ₂ := σ₁ ≫ CtxCat.rawProjection G ht
    let argsInit : Fin k → Domain Γ₂ := fun i => args i.castSucc
    let ρ₂ := ρ₁.pushFin fun i => (argsInit i).val
    have htail : SourceAdmissible σ₂ ρ₂ := SourceAdmissible.tail ht hρ
    have hprev := ih hΔ.init hprops.init (.lam t body) (RawInterpretationProperties.lam ht pt pbody)
      σ₂ argsInit htail
    have hnames := Tm.map_teleSnoc_varLabel hΔ ht σ₁
    have hbase : σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) =
        σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init) :=
      (Category.assoc σ₁ (CtxCat.rawProjection G ht)
        (RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init))).symm
    rw [rawApps_last, hnames, hbase]
    refine (congrArg (fun F : RawValue Γ₂ => rawApplication F _ _) hprev).trans ?_
    change rawApplication ((rawInterpret (piLimit E ℓ) G (.lam t body)).app _ σ₂.op ρ₂)
      {(Tm E ℓ).map σ₁.op (CtxCat.rawComprehension ht).generic} (args (Fin.last k)).val =
      (rawInterpret (piLimit E ℓ) (CtxCat.extension G ht) body).app _ σ₁.op
        (ρ₂.push (args (Fin.last k)).val)
    erw [rawInterpret_lam (piLimit E ℓ) ht, RawFamily.abstraction_value]
    have hb := RawFamily.rawApplication_singleton_abstraction_eq_body (piLimit E ℓ)
      (CtxCat.rawComprehension ht) (rawInterpret (piLimit E ℓ) G t)
      (rawInterpret_isFinitary (piLimit E ℓ) (CtxCat.extension G ht) body) σ₂ ρ₂
      (HasIdeality.bodyAction ht pt.ideal pbody.ideal σ₂ ρ₂ htail)
      (args (Fin.last k)) ⟨σ₁, rfl, rfl⟩
    have ⟨_, _, _, hfixed⟩ := (SourceAdmissible.cons_iff ht σ₁
      (ρ₂.push (args (Fin.last k)).val)).mp hρ
    exact hb.trans (congrArg (fun X =>
      (rawInterpret (piLimit E ℓ) (CtxCat.extension G ht) body).app _ σ₁.op (ρ₂.push X)) hfixed)

end Metalean.CoherentShape
