/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Telescope
public import Metalean.Semantics.Soundness.Telescope.Decoder
import Metalean.Semantics.Interpretation.Binder.Support
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Soundness.Rules.Function

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}

theorem rawInterpret_ctxPi_admissible {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (hprops : RawTeleProperties E Γ₁.as.ctx Δ) (body : Expr ζ ℓ (Γ₁.as.len + k))
    {v : Level ℓ} (hbody : E[(CtxCat.extendTele Γ₁ Δ hΔ).as.ctx] ⊢ₛ body : .sort v)
    (pbody : HasIdeality (CtxCat.extendTele Γ₁ Δ hΔ) body)
    (σ₁ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ₁ : RawValuation Γ₂) (args : Fin k → Domain Γ₂)
    (hρ : SourceAdmissible
      (σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)) ρ₁) (T : Domain Γ₂)
    (hT : T.val = (rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi body Δ)).app _
      (σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op ρ₁)
    (hfixed : ((piLimit E ℓ).telescope T
      (fun i => (Tm E ℓ).map σ₁.op
        (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ) (Fin.natAdd Γ₁.as.len i))) args).1 = args) :
    SourceAdmissible σ₁ (ρ₁.pushFin fun i => (args i).val) := by
  induction Δ using Tele.addInduction generalizing v with
  | nil =>
    exact Eq.mp (congrArg (fun σ₂ : Γ₂ ⟶ Γ₁ => SourceAdmissible σ₂ ρ₁)
      (Category.comp_id σ₁)) hρ
  | snoc k Δ t ih =>
    let G := CtxCat.extendTele Γ₁ Δ hΔ.init
    have ht : E[G.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pt : RawInterpretationProperties G t := hprops.last G.as.wf
    let σ₂ := σ₁ ≫ CtxCat.rawProjection G ht
    let argsInit : Fin k → Domain Γ₂ := fun i => args i.castSucc
    let ρ₂ := ρ₁.pushFin fun i => (argsInit i).val
    have hprojection :
        σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) =
          σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init) :=
      (Category.assoc σ₁ (CtxCat.rawProjection G ht)
        (RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init))).symm
    have hT' : T.val = (rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi (.forallE t body) Δ)).app _
        (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init)).op ρ₁ :=
      hT.trans (congrArg (fun σ₃ : Γ₂ ⟶ Γ₁ =>
        (rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi (.forallE t body) Δ)).app _ σ₃.op ρ₁) hprojection)
    have hnames := Tm.map_teleSnoc_varLabel hΔ ht σ₁
    have hbase : SourceAdmissible
        (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init)) ρ₁ :=
      hprojection ▸ hρ
    rw [telescope_snoc, hnames] at hfixed
    have hprefix : ((piLimit E ℓ).telescope T
        (fun i => (Tm E ℓ).map σ₂.op (Tm.varLabel G (Fin.natAdd Γ₁.as.len i))) argsInit).1 = argsInit := by
      simpa using congrArg (fun xs : Fin (k + 1) → Domain Γ₂ => fun i : Fin k => xs i.castSucc) hfixed
    have htail := ih hΔ.init hprops.init (.forallE t body) (.forallEDF ht hbody hbody)
      (HasIdeality.forallE ht hbody pt.ideal pbody) σ₂ argsInit hbase hT' hprefix
    have hdecoded := rawInterpret_ctxPi_decode Δ hΔ.init hprops.init (.forallE t body)
      (.forallEDF ht hbody hbody) (HasIdeality.forallE ht hbody pt.ideal pbody)
      σ₂ ρ₁ argsInit htail T hT'
    have hhead := congrArg (fun xs : Fin (k + 1) → Domain Γ₂ => xs (Fin.last k)) hfixed
    rw [hdecoded] at hhead
    simp only [Fin.snoc_last] at hhead
    have hdom : ctorTypeDomIdeal
        (((rawInterpret (piLimit E ℓ) G (.forallE t body)).app _ σ₂.op ρ₂).toIdeal
          (HasIdeality.forallE ht hbody pt.ideal pbody σ₂ ρ₂ htail)) =
        ((rawInterpret (piLimit E ℓ) G t).app _ σ₂.op ρ₂).toIdeal (pt.ideal σ₂ ρ₂ htail) := by
      apply Subtype.val_injective
      change RawValue.ctorTypeDom ((rawInterpret (piLimit E ℓ) G (.forallE t body)).app _ σ₂.op ρ₂) = _
      rw [rawInterpret_forallE (piLimit E ℓ) ht hbody]
      exact RawValue.ctorTypeDom_pi _ _ _
    have hhead' := (congrArg (fun U : Domain Γ₂ => (piLimit E ℓ).extend U
      ((Tm E ℓ).map σ₁.op (CtxCat.rawComprehension ht).generic) (args (Fin.last k)))
      hdom).symm.trans hhead
    exact (SourceAdmissible.cons_iff ht σ₁ (ρ₂.push (args (Fin.last k)).val)).mpr
      ⟨htail, pt.ideal σ₂ ρ₂ htail, (args (Fin.last k)).property, congrArg Subtype.val hhead'⟩

end Metalean.CoherentShape
