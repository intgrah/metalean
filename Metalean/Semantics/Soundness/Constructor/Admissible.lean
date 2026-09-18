/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Constructor.Types
public import Metalean.Semantics.Soundness.Telescope.Admissible
public import Metalean.Semantics.Soundness.Telescope.Substitution
import Metalean.Semantics.Soundness.Rules.Core

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}
  {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
  {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len}

theorem ctorFieldTypes_admissible
    (hctx : E[Ctx.instL ls (E.get η).block.params] ⊢ₛ ok)
    (hΔ : WFTeleStrong E (fun _ => True) (Ctx.instL ls (E.get η).block.params)
      (Ctx.instL ls ((E.get η).block.ctors s c).ordinaryTele))
    (pctx : RawTeleProperties E .nil (Ctx.instL ls (E.get η).block.params))
    (pfields : RawTeleProperties E (Ctx.instL ls (E.get η).block.params)
      (Ctx.instL ls ((E.get η).block.ctors s c).ordinaryTele))
    (pbody : RawInterpretationProperties (⟨Ctx.instL ls (E.get η).block.params, hctx⟩ : CtxCat E ℓ)
      (Expr.instL ls (((E.get η).block.ctors s c).ordinaryTele.pi (.sort (E.get η).block.level))))
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ₁ (ps p))
    (hpsfixed : ∀ p, HasFixedness Γ₁ (ps p) ((E.get η).block.paramType ls ps p))
    (hf : ∀ f, E[Γ₁.as.ctx] ⊢ₛ fds f :
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ)
    (args : Fin (ι.ctors s c).nfields → Domain Γ₂) (T : Domain Γ₂)
    (hT : T.val = (RawFamily.closedApps
      (rawInterpret (piLimit E ℓ) (CtxCat.nil E ℓ) (((E.get η).block.ctorTypeFn s c).instL fun p => ls p))
      (fun p => Tm.label Γ₁.as (hps p))
      fun p => rawInterpret (piLimit E ℓ) Γ₁ (ps p)).app _ σ₁.op ρ)
    (hfixed : ((piLimit E ℓ).telescope T
      (fun f => (Tm E ℓ).map σ₁.op (Tm.label Γ₁.as (hf f))) args).1 = args) :
    SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map
      (⟨Fin.append ps fds, Ctor.targetSubstWFStrong hps hf⟩ :
        Γ₁.as ⟶ (⟨Ctx.instL ls ((E.get η).block.params ++
          ((E.get η).block.ctors s c).ordinaryTele), by
            simpa using hΔ.appendCtxWFStrong hctx⟩ : CtxCat E ℓ).as))
      ((RawValuation.pushFin (fun _ => ⊥)
        fun p => (rawInterpret (piLimit E ℓ) Γ₁ (ps p)).app _ σ₁.op ρ).pushFin
          fun f => (args f).val) ∧
    ∃ σ₂ : Γ₂ ⟶ CtxCat.extendTele Γ₁
        (Ctx.substN ps (ι.ctors s c).nfields (Ctx.instL ls ((E.get η).block.ctors s c).ordinaryTele))
        (hΔ.substitution (Inductive.paramSubstEqStrong hps).left),
      σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection
        (hΔ.substitution (Inductive.paramSubstEqStrong hps).left)) = σ₁ ∧
      (∀ f, (Tm E ℓ).map σ₂.op (Tm.varLabel
          (CtxCat.extendTele Γ₁
            (Ctx.substN ps (ι.ctors s c).nfields (Ctx.instL ls ((E.get η).block.ctors s c).ordinaryTele))
            (hΔ.substitution (Inductive.paramSubstEqStrong hps).left))
          (Fin.natAdd Γ₁.as.len f)) =
        (Tm E ℓ).map σ₁.op (Tm.label Γ₁.as (hf f))) ∧
      SourceAdmissible σ₂ (ρ.pushFin fun f => (args f).val) := by
  have ⟨hproj, hT', hbase, hnames⟩ :=
    ctorFieldTypes_eq_pi hctx hΔ pctx pbody hps pps hpsfixed hf σ₁ ρ hρ
  rw [← hproj] at hT' hbase
  have hsource := rawInterpret_ctxPi_admissible _ hΔ pfields
    (.sort ((E.get η).block.level.inst ls)) .sortDF (HasIdeality.sort _ _)
    (σ₁ ≫ RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf)) _ args hbase T (hT.trans hT')
    ((congrArg (fun n => ((piLimit E ℓ).telescope T n args).1) hnames).trans hfixed)
  have ⟨σ₂, _, hover, hnames', hadm⟩ := SemanticSubstitution.sectionTele
    _ hΔ pfields (ctorParamHom hctx hps) σ₁ _ ρ (fun f => (args f).val)
    (SemanticSubstitution.ofHom hctx _ σ₁ ρ (fun p => (pps p).subst) hρ) hρ _ hproj hsource
  refine ⟨?_, σ₂, hover, fun f => (hnames' f).trans (congrFun hnames f), hadm⟩
  have q (C : Ctx ζ ℓ 0 (ι.nparams + (ι.ctors s c).nfields))
      (he : Ctx.instL ls (E.get η).block.params ++
        Ctx.instL ls ((E.get η).block.ctors s c).ordinaryTele = C)
      (wf : E[C] ⊢ₛ ok) (r : Γ₁.as ⟶ (⟨C, wf⟩ : RawCtx E ℓ))
      (hr : r.subst = Fin.append ps fds) :
      SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map r)
        ((RawValuation.pushFin (fun _ => ⊥) fun p =>
          (rawInterpret (piLimit E ℓ) Γ₁ (ps p)).app _ σ₁.op ρ).pushFin fun f => (args f).val) := by
    subst C
    obtain rfl : r = ctorTargetHom hctx hΔ hps hf := RawCtx.Hom.ext hr
    exact hsource
  exact q _ (Ctx.instL_append ls _ _).symm _ _ rfl

end Metalean.CoherentShape
