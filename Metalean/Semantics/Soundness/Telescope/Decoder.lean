/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Telescope
public import Metalean.Semantics.Soundness.Telescope.Beta
import Metalean.Semantics.Interpretation.Binder.Support
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Soundness.Rules.Function

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}

theorem rawInterpret_forallE_decode {t : Expr ζ ℓ Γ₁.as.len} {t' : Expr ζ ℓ (Γ₁.as.len + 1)} {u v : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (pt : HasIdeality Γ₁ t) (pt' : HasIdeality (CtxCat.extension Γ₁ ht) t')
    (σ₁ : Γ₂ ⟶ CtxCat.extension Γ₁ ht) (ρ₂ : RawValuation Γ₂) (X T : Domain Γ₂)
    (hρ : SourceAdmissible σ₁ (ρ₂.push X.val))
    (hT : T.val = (rawInterpret (piLimit E ℓ) Γ₁ (.forallE t t')).app _
      (σ₁ ≫ CtxCat.rawProjection Γ₁ ht).op ρ₂) :
    let name := (Tm E ℓ).map σ₁.op (CtxCat.rawComprehension ht).generic
    let Y := (piLimit E ℓ).extend (ctorTypeDomIdeal T) name X
    (Y, ctorTypeFibreIdeal T name Y) =
      (X, ((rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t').app _
        σ₁.op (ρ₂.push X.val)).toIdeal (pt' _ _ hρ)) := by
  have ⟨htail, hdirA, _, hfixed⟩ := (SourceAdmissible.cons_iff ht σ₁ (ρ₂.push X.val)).mp hρ
  let C := rawInterpret (piLimit E ℓ) Γ₁ t
  let body := rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t'
  let σ₂ := σ₁ ≫ CtxCat.rawProjection Γ₁ ht
  let name := (Tm E ℓ).map σ₁.op (CtxCat.rawComprehension ht).generic
  let M := RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C body σ₂ ρ₂
  have hbodyF : body.IsFinitary :=
    rawInterpret_isFinitary (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t'
  have hM : M.IsFinitary := RawFamily.normalizedBodyAction_isFinitary (piLimit E ℓ)
    (CtxCat.rawComprehension ht) C hbodyF σ₂ ρ₂
  have hMI : M.IsIdealValued := HasIdeality.bodyAction ht pt pt' σ₂ ρ₂ htail
  let V := M.toIdealAction hM hMI
  let label := (Ty.pairPresheaf E ℓ).map σ₂.op (Ty.pairOfTyping Γ₁.as ht ht')
  have hpi : T = pi label ((C.app _ σ₂.op ρ₂).toIdeal hdirA) V := by
    apply Subtype.val_injective
    rw [hT, rawInterpret_forallE (piLimit E ℓ) ht ht']
    rfl
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
    (hρ : SourceAdmissible σ₁ (ρ₁.pushFin fun i => (args i).val)) (T : Domain Γ₂)
    (hT : T.val = (rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi body Δ)).app _
      (σ₁ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op ρ₁) :
    (piLimit E ℓ).telescope T
      (fun i => (Tm E ℓ).map σ₁.op
        (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ) (Fin.natAdd Γ₁.as.len i))) args =
      (args, ((rawInterpret (piLimit E ℓ) (CtxCat.extendTele Γ₁ Δ hΔ) body).app _
        σ₁.op (ρ₁.pushFin fun i => (args i).val)).toIdeal (pbody _ _ hρ)) := by
  induction Δ using Tele.addInduction generalizing v with
  | nil =>
    apply Prod.ext
    · exact funext fun i => i.elim0
    · apply Subtype.val_injective
      exact hT.trans (congrArg (fun σ₃ : Γ₂ ⟶ Γ₁ =>
        (rawInterpret (piLimit E ℓ) Γ₁ body).app _ σ₃.op ρ₁) (Category.comp_id σ₁))
  | snoc k Δ t ih =>
    let G := CtxCat.extendTele Γ₁ Δ hΔ.init
    have ht : E[G.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pt : RawInterpretationProperties G t := hprops.last G.as.wf
    let σ₂ := σ₁ ≫ CtxCat.rawProjection G ht
    let argsInit : Fin k → Domain Γ₂ := fun i => args i.castSucc
    let ρ₂ := ρ₁.pushFin fun i => (argsInit i).val
    have htail : SourceAdmissible σ₂ ρ₂ := SourceAdmissible.tail ht hρ
    have hT' : T.val = (rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi (.forallE t body) Δ)).app _
        (σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init)).op ρ₁ :=
      hT.trans (congrArg (fun σ₃ : Γ₂ ⟶ Γ₁ =>
        (rawInterpret (piLimit E ℓ) Γ₁ (Ctx.pi (.forallE t body) Δ)).app _ σ₃.op ρ₁)
        (Category.assoc σ₁ (CtxCat.rawProjection G ht)
          (RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ.init))).symm)
    have hprev := ih hΔ.init hprops.init (.forallE t body) (.forallEDF ht hbody hbody)
      (HasIdeality.forallE ht hbody pt.ideal pbody) σ₂ argsInit htail hT'
    have hnames := Tm.map_teleSnoc_varLabel hΔ ht σ₁
    rw [telescope_snoc, hnames, hprev]
    let U := ((rawInterpret (piLimit E ℓ) G (.forallE t body)).app _ σ₂.op ρ₂).toIdeal
      (HasIdeality.forallE ht hbody pt.ideal pbody _ _ htail)
    have hstep := rawInterpret_forallE_decode ht hbody pt.ideal pbody σ₁ ρ₂
      (args (Fin.last k)) U hρ rfl
    have hresult := congrArg (fun result : Domain Γ₂ × Domain Γ₂ =>
      (Fin.snoc (α := fun _ : Fin (k + 1) => Domain Γ₂) argsInit result.1, result.2)) hstep
    exact hresult.trans (Prod.ext (Fin.snoc_init_self args) rfl)

end Metalean.CoherentShape
