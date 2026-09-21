/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Telescope
public import Metalean.Semantics.Soundness.Rules.Function
public import Metalean.Semantics.Soundness.Telescope.Beta
import Metalean.Semantics.Interpretation.Binder.Support
import Metalean.Semantics.Interpretation

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}

theorem rawInterpret_forallE_decode {t : Expr ζ ℓ Γ₁.as.len} {t' : Expr ζ ℓ (Γ₁.as.len + 1)} {u v : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (pt : HasIdeality Γ₁ t) (pt' : HasIdeality (CtxCat.extension Γ₁ ht) t')
    (σ₁ : Γ₂ ⟶ CtxCat.extension Γ₁ ht) (ρ₂ : RawValuation Γ₂) (X : Domain Γ₂)
    (hρ : SourceAdmissible σ₁ (ρ₂.push X.val)) :
    let T := (hρ.tail ht).eval (HasIdeality.forallE ht ht' pt pt')
    let name := (Tm E ℓ).map σ₁.op (CtxCat.rawComprehension ht).generic
    let Y := (piLimit E ℓ).extend (ctorTypeDomIdeal T) name X
    (Y, ctorTypeFibreIdeal T name Y) =
      (X, hρ.eval pt') := by
  let T := (hρ.tail ht).eval (HasIdeality.forallE ht ht' pt pt')
  cases hρ with
  | cons _ _ _ htail hdirA _ hfixed =>
    let C := rawInterpret (piLimit E ℓ) Γ₁ t
    let body := rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t'
    let σ₂ := σ₁ ≫ CtxCat.rawProjection Γ₁ ht
    let name := (Tm E ℓ).map σ₁.op (CtxCat.rawComprehension ht).generic
    let M := RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C body σ₂ ρ₂
    let V := M.toIdealAction
      (RawFamily.normalizedBodyAction_isFinitary _ _ _ (rawInterpret_isFinitary _ _ _) _ _)
      (RawFamily.bodyAction_isIdealValued ht pt pt' σ₂ ρ₂ htail)
    let label := (Ty.pairPresheaf E ℓ).map σ₂.op (Ty.pairOfTyping Γ₁.as ht ht')
    have hpi : T = pi label ((C.app _ σ₂.op ρ₂).toIdeal hdirA) V :=
      Subtype.val_injective congr($(rawInterpret_forallE (piLimit E ℓ) ht ht').app _ σ₂.op ρ₂)
    have hdom : ctorTypeDomIdeal T = (C.app _ σ₂.op ρ₂).toIdeal hdirA := by
      rw [hpi]
      exact Subtype.val_injective (RawValue.ctorTypeDom_pi _ _ _)
    have hX : (piLimit E ℓ).extend (ctorTypeDomIdeal T) name X = X := by
      rw [hdom]
      exact Subtype.val_injective hfixed
    change ((piLimit E ℓ).extend (ctorTypeDomIdeal T) name X,
      ctorTypeFibreIdeal T name ((piLimit E ℓ).extend (ctorTypeDomIdeal T) name X)) = _
    rw [hX]
    apply congrArg (Prod.mk X)
    rw [hpi, ctorTypeFibreIdeal_pi]
    apply Subtype.val_injective
    change RawFamily.sectionValue (CtxCat.rawComprehension ht) body (𝟙 Γ₂ ≫ σ₂) (ρ₂.pullback (𝟙 Γ₂)) name
      ((piLimit E ℓ).rawExtend (C.app _ (𝟙 Γ₂ ≫ σ₂).op (ρ₂.pullback (𝟙 Γ₂))) name X.val) = _
    rw [Category.id_comp, RawValuation.pullback_id]
    have hbody := RawFamily.sectionValue_eq_value (CtxCat.rawComprehension ht) body σ₂ ρ₂ name
      ((piLimit E ℓ).rawExtend (C.app _ σ₂.op ρ₂) name X.val) ⟨σ₁, rfl, rfl⟩
    exact hbody.trans (congrArg (fun Y => body.app _ σ₁.op (ρ₂.push Y)) hfixed)

theorem rawInterpret_ctxPi_decode {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (hprops : RawTeleProperties E Γ₁.as.ctx Δ) (body : Expr ζ ℓ (Γ₁.as.len + k))
    {v : Level ℓ} (hbody : E[(CtxCat.extendTele Γ₁ Δ hΔ).as.ctx] ⊢ₛ body : .sort v)
    (pbody : HasIdeality (CtxCat.extendTele Γ₁ Δ hΔ) body)
    (σ₁ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ₁ : RawValuation Γ₂) (args : Fin k → Domain Γ₂)
    (hT : ((rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi body Δ)).app _
      (σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op ρ₁).IsDirected) :
    (∀ hρ : SourceAdmissible σ₁ (ρ₁.pushFin fun i => (args i).val),
      (piLimit E ℓ).telescope ⟨_, @hT⟩
        (fun i => (Tm E ℓ).map σ₁.op
          (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ) (Fin.natAdd Γ₁.as.len i))) args =
        (args, hρ.eval pbody)) ∧
    (SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)) ρ₁ →
    ((piLimit E ℓ).telescope ⟨_, @hT⟩
      (fun i => (Tm E ℓ).map σ₁.op
        (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ) (Fin.natAdd Γ₁.as.len i))) args).1 = args →
      SourceAdmissible σ₁ (ρ₁.pushFin fun i => (args i).val)) := by
  induction Δ using Tele.addInduction generalizing v with
  | nil =>
    refine ⟨fun _ => Prod.ext (funext fun i => i.elim0) ?_, fun hρ _ => ?_⟩
    · apply Subtype.val_injective
      exact congrArg (fun σ₃ : Γ₂ ⟶ Γ₁ =>
        (rawInterpret (piLimit E ℓ) Γ₁ body).app _ σ₃.op ρ₁) (Category.comp_id σ₁)
    · exact Eq.mp (congrArg (fun σ₂ : Γ₂ ⟶ Γ₁ => SourceAdmissible σ₂ ρ₁)
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
    have hnames : (fun i : Fin k => (Tm E ℓ).map σ₁.op
        (Tm.varLabel (CtxCat.extendTele Γ₁ (Δ.snoc t) hΔ) (i.castSucc.natAdd Γ₁.as.len))) =
        fun i => (Tm E ℓ).map σ₂.op (Tm.varLabel G (i.natAdd Γ₁.as.len)) :=
      funext fun i => Tm.map_extension_varLabel ht σ₁ (i.natAdd Γ₁.as.len)
    have hprev := ih hΔ.init hprops.init (.forallE t body) (.forallEDF ht hbody hbody)
      (HasIdeality.forallE ht hbody pt.ideal pbody) σ₂ argsInit
      (by rw [← hprojection]; exact hT)
    simp only [← hprojection] at hprev
    dsimp only [Ctx.pi, Tele.foldr] at hprev ⊢
    constructor
    · intro hadm
      rw [telescope_snoc, hnames, hprev.1 (hadm.tail ht)]
      have hstep := rawInterpret_forallE_decode ht hbody pt.ideal pbody σ₁ ρ₂
        (args (Fin.last k)) hadm
      exact (congrArg (fun result : Domain Γ₂ × Domain Γ₂ =>
        (Fin.snoc (α := fun _ : Fin (k + 1) => Domain Γ₂) argsInit result.1, result.2)) hstep).trans
          (Prod.ext (Fin.snoc_init_self args) rfl)
    · intro hρ hfixed
      rw [telescope_snoc, hnames] at hfixed
      have hprefix := congrArg (fun xs : Fin (k + 1) → Domain Γ₂ => fun i : Fin k => xs i.castSucc) hfixed
      simp only [Fin.snoc_castSucc] at hprefix
      have htail := hprev.2 hρ hprefix
      have hdecoded := hprev.1 htail
      have hhead := congrArg (fun xs : Fin (k + 1) → Domain Γ₂ => xs (Fin.last k)) hfixed
      dsimp only [Ctx.pi, Tele.foldr] at hdecoded hhead
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
      exact .cons ht σ₁ (ρ₂.push (args (Fin.last k)).val)
        htail (pt.ideal σ₂ ρ₂ htail) (args (Fin.last k)).property (congrArg Subtype.val hhead')

end Metalean.CoherentShape
