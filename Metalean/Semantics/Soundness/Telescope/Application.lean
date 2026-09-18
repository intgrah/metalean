/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Pi.Term
public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Rules.Function
public import Metalean.Semantics.Soundness.Telescope.Section
import Metalean.Semantics.Interpretation.Application
import Metalean.TypeTheory.Syntactic.Comprehension
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Tgt Γ : CtxCat E ℓ}
  {t : Expr ζ ℓ Src.as.len} {t' : Expr ζ ℓ (Src.as.len + 1)} {u v : Level ℓ}
  {f e : Expr ζ ℓ Tgt.as.len}

theorem HasIdeality.application_value_fixed_subst
    (ht : E[Src.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Src.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (htI : HasIdeality Src t) (htI' : HasIdeality (Src.extension ht) t')
    (σ₁ : Tgt.as ⟶ Src.as)
    (hf : E[Tgt.as.ctx] ⊢ₛ f : (Expr.forallE t t').subst σ₁.subst)
    (he : E[Tgt.as.ctx] ⊢ₛ e : t.subst σ₁.subst)
    (happ : E[Tgt.as.ctx] ⊢ₛ .app f e : (t'.subst σ₁.subst.lift).inst e)
    (σ₂ : Γ ⟶ Tgt) (ρs ρt : RawValuation Γ)
    (hρ : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρs)
    (hfi : ((rawInterpret (piLimit E ℓ) Tgt f).app _ σ₂.op ρt).IsDirected)
    (hei : ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₂.op ρt).IsDirected)
    (hff : (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Src (.forallE t t')).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs)
      ((Tm E ℓ).map σ₂.op (Tm.label Tgt.as hf))
      ((rawInterpret (piLimit E ℓ) Tgt f).app _ σ₂.op ρt) =
      (rawInterpret (piLimit E ℓ) Tgt f).app _ σ₂.op ρt)
    (hef : (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Src t).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρs)
      ((Tm E ℓ).map σ₂.op (Tm.label Tgt.as he))
      ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₂.op ρt) =
      (rawInterpret (piLimit E ℓ) Tgt e).app _ σ₂.op ρt) :
    (rawInterpret (piLimit E ℓ) Tgt (.app f e)).app _ σ₂.op ρt =
      rawApplication ((rawInterpret (piLimit E ℓ) Tgt f).app _ σ₂.op ρt)
        {(Tm E ℓ).map σ₂.op (Tm.label Tgt.as he)}
        ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₂.op ρt) ∧
      (piLimit E ℓ).rawExtend
        ((rawInterpret (piLimit E ℓ) (Src.extension ht) t').app _
          (σ₂ ≫ RawCtx.toCtx.map (σ₁.snoc ⟨u, ht⟩ he)).op
          (ρs.push ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₂.op ρt)))
        ((Tm E ℓ).map σ₂.op (Tm.label Tgt.as happ))
        ((rawInterpret (piLimit E ℓ) Tgt (.app f e)).app _ σ₂.op ρt) =
        (rawInterpret (piLimit E ℓ) Tgt (.app f e)).app _ σ₂.op ρt := by
  have htσ := ht.substitution σ₁.typed
  have htσ' : E[Tgt.as.ctx.snoc (t.subst σ₁.subst)] ⊢ₛ t'.subst σ₁.subst.lift : .sort v :=
    ht'.substitution (SubstWFStrong.lift ⟨u, ht⟩ σ₁.typed)
  have hres := DefeqStrong.inst_congr htσ' he
  let F : Domain Γ := ⟨_, hfi⟩
  let X : Domain Γ := ⟨_, hei⟩
  let nf := (Tm E ℓ).map σ₂.op (Tm.label Tgt.as hf)
  let na := (Tm E ℓ).map σ₂.op (Tm.label Tgt.as he)
  have hp : (Ty.pairPresheaf E ℓ).map (σ₂ ≫ RawCtx.toCtx.map σ₁).op (Ty.pairOfTyping Src.as ht ht') =
      (Ty.pairPresheaf E ℓ).map σ₂.op (Ty.pairOfTyping Tgt.as htσ htσ') := by
    rw [op_comp, Functor.map_comp_apply, Ty.pairPresheaf_map_ofTyping]
  have hpiTgt : Tm.type (Tm.label Tgt.as hf) =
      Ty.piApp (Ty.pairOfTyping Tgt.as htσ htσ').1 (Ty.pairOfTyping Tgt.as htσ htσ').2 :=
    (Ty.piApp_eq_ofRepr _ _ ⟨_, u, htσ⟩ (CtxCat.rawComprehension_type htσ) ⟨_, v, htσ'⟩
      (Ty.eval_familyOfTyping Tgt.as htσ htσ').symm).symm
  have hdomTgt : Tm.type (Tm.label Tgt.as he) =
      yonedaEquiv (Ty.pairOfTyping Tgt.as htσ htσ').1 := (CtxCat.rawComprehension_type htσ).symm
  have hguard : Tm.type nf = Ty.piApp
      ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ RawCtx.toCtx.map σ₁).op
        (Ty.pairOfTyping Src.as ht ht')).1
      ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ RawCtx.toCtx.map σ₁).op
        (Ty.pairOfTyping Src.as ht ht')).2 := by
    rw [hp, Tm.type_map, hpiTgt, Ty.piApp_pairPresheaf_map]
  have harg : Tm.type na = yonedaEquiv
      ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ RawCtx.toCtx.map σ₁).op
        (Ty.pairOfTyping Src.as ht ht')).1 := by
    rw [hp, Tm.type_map, hdomTgt]
    change _ = yonedaEquiv (yoneda.map σ₂ ≫ (Ty.pairOfTyping Tgt.as htσ htσ').1)
    rw [← yonedaEquiv_naturality]
  have hlabel : Tm.apply
      ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ RawCtx.toCtx.map σ₁).op
        (Ty.pairOfTyping Src.as ht ht')).1
      ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ RawCtx.toCtx.map σ₁).op
        (Ty.pairOfTyping Src.as ht ht')).2
      nf na hguard harg = (Tm E ℓ).map σ₂.op (Tm.label Tgt.as happ) := by
    have hg' : Tm.type nf =
        Ty.piApp ((Ty.pairPresheaf E ℓ).map σ₂.op (Ty.pairOfTyping Tgt.as htσ htσ')).1
          ((Ty.pairPresheaf E ℓ).map σ₂.op (Ty.pairOfTyping Tgt.as htσ htσ')).2 := hp ▸ hguard
    have harg' : Tm.type na =
        yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ₂.op (Ty.pairOfTyping Tgt.as htσ htσ')).1 :=
      hp ▸ harg
    refine (Tm.apply_congr hp rfl rfl hguard harg hg' harg').trans ?_
    refine (Tm.map_apply (Ty.pairOfTyping Tgt.as htσ htσ').1 (Ty.pairOfTyping Tgt.as htσ htσ').2
      (Tm.label Tgt.as hf) (Tm.label Tgt.as he) hpiTgt hdomTgt σ₂ _ _).symm.trans ?_
    exact congrArg ((Tm E ℓ).map σ₂.op)
      ((Tm.apply_label Tgt.as htσ htσ' hf he hres hpiTgt hdomTgt).trans
        (Tm.label_eq (IsTypeStrong.isTypeEq ⟨_, hres⟩) happ))
  have hval : (rawInterpret (piLimit E ℓ) Tgt (.app f e)).app _ σ₂.op ρt =
      (application F na X).val := by
    rw [rawInterpret_app, RawFamily.application_value]
    exact HasIdeality.application_value_subst ht ht' htI htI' σ₁ he σ₂ ρs hρ _ (F := F) hff X
  have hfixed := HasIdeality.application_fixed ht ht' htI htI' (σ₂ ≫ RawCtx.toCtx.map σ₁) ρs hρ
    ((Raw.ContextSection.ofTyping ht σ₁ he).pullback σ₂) nf
    (F := F) (X := X) hff hef hguard harg
  constructor
  · rw [hval]
    exact (rawApplication_singleton F X na).symm
  · rw [hval, ← hlabel]
    exact hfixed

theorem rawInterpret_applyTele_source {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (body : Expr ζ ℓ (Src.as.len + k))
    (hbody : E[Src.as.ctx ++ Δ] ⊢ₛ body : .sort v)
    (pbody : HasIdeality (CtxCat.extendTele Src Δ hΔ) body)
    (σ₁ : Tgt.as ⟶ Src.as) (e : Expr ζ ℓ Tgt.as.len)
    (he : E[Tgt.as.ctx] ⊢ₛ e : (Ctx.pi body Δ).subst σ₁.subst)
    (σ₂ : Tgt.as ⟶ (CtxCat.extendTele Src Δ hΔ).as)
    (hover : σ₂ ≫ RawCtx.Hom.teleProjection hΔ = σ₁)
    (happ : E[Tgt.as.ctx] ⊢ₛ e.apps (fun i => σ₂.subst (Fin.natAdd Src.as.len i)) :
      body.subst σ₂.subst)
    (σ₃ : Γ ⟶ Tgt) (ρs ρ : RawValuation Γ)
    (hei : ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₃.op ρ).IsDirected)
    (hff : (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Src (Ctx.pi body Δ)).app _ (σ₃ ≫ RawCtx.toCtx.map σ₁).op ρs)
      ((Tm E ℓ).map σ₃.op (Tm.label Tgt.as he))
      ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₃.op ρ) =
      (rawInterpret (piLimit E ℓ) Tgt e).app _ σ₃.op ρ)
    (hadm : SourceAdmissible (σ₃ ≫ RawCtx.toCtx.map σ₂)
      (ρs.pushFin fun i => (rawInterpret (piLimit E ℓ) Tgt
        (σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ)) :
    (rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ =
      rawApps ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₃.op ρ)
        (fun i => (Tm E ℓ).map σ₃.op (Tm.label Tgt.as (σ₂.typed (Fin.natAdd Src.as.len i))))
        (fun i => (rawInterpret (piLimit E ℓ) Tgt (σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ) ∧
      ((rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ).IsDirected ∧
      (piLimit E ℓ).rawExtend
        ((rawInterpret (piLimit E ℓ) (CtxCat.extendTele Src Δ hΔ) body).app _
          (σ₃ ≫ RawCtx.toCtx.map σ₂).op
          (ρs.pushFin fun i => (rawInterpret (piLimit E ℓ) Tgt
            (σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ))
        ((Tm E ℓ).map σ₃.op (Tm.label Tgt.as happ))
        ((rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ) =
        (rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ := by
  induction Δ using Tele.addInduction generalizing v with
  | nil =>
    have hσ₂ : σ₂ = σ₁ := by
      change σ₂ ≫ 𝟙 Src.as = σ₁ at hover
      exact (Category.comp_id σ₂).symm.trans hover
    subst σ₂
    exact ⟨rfl, hei, hff⟩
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    have ht : E[S.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    let σ₄ : Tgt.as ⟶ S.as := σ₂ ≫ S.projectionRaw ht
    let arg := σ₂.subst (Fin.last S.as.len)
    let eInit := e.apps fun i : Fin k => σ₄.subst (Fin.natAdd Src.as.len i)
    have hoverInit : σ₄ ≫ RawCtx.Hom.teleProjection hΔ.init = σ₁ := by
      have hh : σ₄ ≫ RawCtx.Hom.teleProjection hΔ.init = σ₂ ≫ RawCtx.Hom.teleProjection hΔ :=
        RawCtx.Hom.ext rfl
      exact hh.trans hover
    have heInit : E[Tgt.as.ctx] ⊢ₛ eInit : (Expr.forallE t body).subst σ₄.subst :=
      RawCtx.Hom.applyTele_typed hΔ.init σ₄ hoverInit (.forallEDF ht hbody hbody) he
    have harg : E[Tgt.as.ctx] ⊢ₛ arg : t.subst σ₄.subst := by
      have h := σ₂.typed (Fin.last S.as.len)
      change E[Tgt.as.ctx] ⊢ₛ arg : (Ctx.get (Fin.last S.as.len) (S.as.ctx.snoc t)).subst σ₂.subst at h
      erw [Ctx.get_last, Expr.wk_subst] at h
      exact h
    have hsσ₂ : σ₄.snoc ⟨_, ht⟩ harg = σ₂ := RawCtx.Hom.ext (Fin.snoc_init_self σ₂.subst)
    let ρInit := ρs.pushFin fun i : Fin k =>
      (rawInterpret (piLimit E ℓ) Tgt (σ₄.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ
    have hadmInit : SourceAdmissible (σ₃ ≫ RawCtx.toCtx.map σ₄) ρInit := by
      have htail := hadm.tail ht
      change SourceAdmissible ((σ₃ ≫ RawCtx.toCtx.map σ₂) ≫ RawCtx.toCtx.map (S.projectionRaw ht)) ρInit at htail
      erw [Category.assoc, ← RawCtx.toCtx.map_comp] at htail
      exact htail
    have ⟨hevalInit, hidealInit, hfixedInit⟩ := ih hΔ.init pΔ.init (.forallE t body)
      (.forallEDF ht hbody hbody) (HasIdeality.forallE ht hbody (pΔ.last _).ideal pbody)
      he σ₄ hoverInit heInit hff hadmInit
    have hcons := ((SourceAdmissible.cons_iff ht _ _).mp hadm).2.2
    have hargi : ((rawInterpret (piLimit E ℓ) Tgt arg).app _ σ₃.op ρ).IsDirected := hcons.1
    have hhead := hcons.2
    have hname : (Tm E ℓ).map (σ₃ ≫ RawCtx.toCtx.map σ₂).op (CtxCat.rawComprehension ht).generic =
        (Tm E ℓ).map σ₃.op (Tm.label Tgt.as harg) := by
      erw [op_comp, Functor.map_comp_apply, CtxCat.rawComprehension_generic, Tm.map_varLabel]
      apply congrArg ((Tm E ℓ).map σ₃.op)
      apply Tm.label_congr
      change (Ctx.get (Fin.last S.as.len) (S.as.ctx.snoc t)).subst σ₂.subst = t.subst σ₄.subst
      erw [Ctx.get_last, Expr.wk_subst]
      rfl
    have hhead' : (piLimit E ℓ).rawExtend
        ((rawInterpret (piLimit E ℓ) S t).app _ (σ₃ ≫ RawCtx.toCtx.map σ₄).op ρInit)
        ((Tm E ℓ).map σ₃.op (Tm.label Tgt.as harg))
        ((rawInterpret (piLimit E ℓ) Tgt arg).app _ σ₃.op ρ) =
        (rawInterpret (piLimit E ℓ) Tgt arg).app _ σ₃.op ρ := by
      erw [hname] at hhead
      change (piLimit E ℓ).rawExtend
        ((rawInterpret (piLimit E ℓ) S t).app _
          ((σ₃ ≫ RawCtx.toCtx.map σ₂) ≫ RawCtx.toCtx.map (S.projectionRaw ht)).op ρInit)
        ((Tm E ℓ).map σ₃.op (Tm.label Tgt.as harg))
        ((rawInterpret (piLimit E ℓ) Tgt arg).app _ σ₃.op ρ) = _ at hhead
      erw [Category.assoc, ← RawCtx.toCtx.map_comp] at hhead
      exact hhead
    have htype : (body.subst σ₄.subst.lift).inst arg = body.subst σ₂.subst := by
      erw [Expr.inst_subst_lift]
      exact congrArg (fun σ₅ => body.subst σ₅) (congrArg RawCtx.Hom.subst hsσ₂)
    have heapp : e.apps (fun i => σ₂.subst (Fin.natAdd Src.as.len i)) = .app eInit arg := by
      rw [Expr.apps_last]
      rfl
    have happ' : E[Tgt.as.ctx] ⊢ₛ .app eInit arg : (body.subst σ₄.subst.lift).inst arg := by
      rwa [htype, ← heapp]
    have ⟨hstep, hstepfixed⟩ := HasIdeality.application_value_fixed_subst ht hbody
      (pΔ.last _).ideal pbody σ₄ heInit harg happ' σ₃ ρInit ρ hadmInit hidealInit hargi hfixedInit hhead'
    have hn (i : Fin k) : Tm.label Tgt.as (σ₂.typed (Fin.natAdd Src.as.len i.castSucc)) =
        Tm.label Tgt.as (σ₄.typed (Fin.natAdd Src.as.len i)) := by
      apply Tm.label_congr
      change (Ctx.get (Fin.natAdd Src.as.len i).castSucc (S.as.ctx.snoc t)).subst σ₂.subst =
        (Ctx.get (Fin.natAdd Src.as.len i) S.as.ctx).subst σ₄.subst
      erw [Ctx.get_snoc S.as.ctx t (Fin.natAdd Src.as.len i).castSucc
        (Nat.ne_of_lt (Fin.natAdd Src.as.len i).isLt), Fin.castLT_castSucc, Expr.wk_subst]
      rfl
    have hlast : Tm.label Tgt.as (σ₂.typed (Fin.natAdd Src.as.len (Fin.last k))) =
        Tm.label Tgt.as harg := by
      apply Tm.label_congr
      change (Ctx.get (Fin.last S.as.len) (S.as.ctx.snoc t)).subst σ₂.subst = t.subst σ₄.subst
      erw [Ctx.get_last, Expr.wk_subst]
      rfl
    have heval : (rawInterpret (piLimit E ℓ) Tgt
        (e.apps fun i => σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ =
        rawApps ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₃.op ρ)
          (fun i => (Tm E ℓ).map σ₃.op (Tm.label Tgt.as (σ₂.typed (Fin.natAdd Src.as.len i))))
          fun i => (rawInterpret (piLimit E ℓ) Tgt (σ₂.subst (Fin.natAdd Src.as.len i))).app _ σ₃.op ρ := by
      rw [Expr.apps_last, rawApps_last, hlast]
      simp_rw [hn]
      erw [← hevalInit]
      exact hstep
    refine ⟨heval, ?_, ?_⟩
    · rw [heapp, hstep, rawApplication_singleton ⟨_, hidealInit⟩ ⟨_, hargi⟩]
      exact (application ..).property
    · have hlabel : Tm.label Tgt.as happ' = Tm.label Tgt.as happ := by
        apply Tm.label_eq
        · rw [htype]
          exact IsTypeStrong.isTypeEq ⟨_, hbody.substitution σ₂.typed⟩
        · rwa [htype, ← heapp]
      rwa [hlabel, hsσ₂, ← heapp] at hstepfixed

theorem HasFixedness.id_rawExtend {T : Expr ζ ℓ Tgt.as.len}
    (hT : E[Tgt.as.ctx] ⊢ₛ T : .sort v) (he : E[Tgt.as.ctx] ⊢ₛ e : T)
    (he' : E[Tgt.as.ctx] ⊢ₛ e : T.subst (RawCtx.Hom.subst (𝟙 Tgt.as)))
    (pef : HasFixedness Tgt e T) (σ : Γ ⟶ Tgt) (ρ : RawValuation Γ) (hρ : SourceAdmissible σ ρ) :
    (piLimit E ℓ).rawExtend
        ((rawInterpret (piLimit E ℓ) Tgt T).app _ (σ ≫ RawCtx.toCtx.map (𝟙 Tgt.as)).op ρ)
        ((Tm E ℓ).map σ.op (Tm.label Tgt.as he'))
        ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ.op ρ) =
      (rawInterpret (piLimit E ℓ) Tgt e).app _ σ.op ρ := by
  have hl : Tm.label Tgt.as he' = Tm.label Tgt.as he :=
    Tm.label_eq (congr(E[Tgt.as.ctx] ⊢ₛ
      $(RawCtx.expr.map_id_apply (Opposite.op Tgt.as) T) ≡ T typ).mpr
      (IsTypeStrong.isTypeEq ⟨_, hT⟩)) he'
  erw [RawCtx.toCtx.map_id, Category.comp_id, hl]
  exact pef he σ ρ hρ

theorem rawInterpret_applyTele {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Tgt.as.len (Tgt.as.len + k)) (hΔ : WFTeleStrong E P Tgt.as.ctx Δ)
    (pΔ : RawTeleProperties E Tgt.as.ctx Δ) (body : Expr ζ ℓ (Tgt.as.len + k))
    (hbody : E[Tgt.as.ctx ++ Δ] ⊢ₛ body : .sort v)
    (pbody : HasIdeality (CtxCat.extendTele Tgt Δ hΔ) body)
    (e : Expr ζ ℓ Tgt.as.len) (he : E[Tgt.as.ctx] ⊢ₛ e : Ctx.pi body Δ)
    (pei : HasIdeality Tgt e) (pef : HasFixedness Tgt e (Ctx.pi body Δ))
    (σ₁ : Tgt.as ⟶ (CtxCat.extendTele Tgt Δ hΔ).as)
    (hover : σ₁ ≫ RawCtx.Hom.teleProjection hΔ = 𝟙 Tgt.as)
    (pσ₁ : ∀ i : Fin k, RawInterpretationProperties Tgt (σ₁.subst (Fin.natAdd Tgt.as.len i)))
    (hσ₁fixed : ∀ i : Fin k, HasFixedness Tgt (σ₁.subst (Fin.natAdd Tgt.as.len i))
      ((Ctx.get (Fin.natAdd Tgt.as.len i) (Tgt.as.ctx ++ Δ)).subst σ₁.subst))
    (happ : E[Tgt.as.ctx] ⊢ₛ e.apps (fun i => σ₁.subst (Fin.natAdd Tgt.as.len i)) :
      body.subst σ₁.subst)
    (σ₂ : Γ ⟶ Tgt) (ρ : RawValuation Γ) (hρ : SourceAdmissible σ₂ ρ) :
    (rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₁.subst (Fin.natAdd Tgt.as.len i))).app _ σ₂.op ρ =
      rawApps ((rawInterpret (piLimit E ℓ) Tgt e).app _ σ₂.op ρ)
        (fun i => (Tm E ℓ).map σ₂.op (Tm.label Tgt.as (σ₁.typed (Fin.natAdd Tgt.as.len i))))
        (fun i => (rawInterpret (piLimit E ℓ) Tgt (σ₁.subst (Fin.natAdd Tgt.as.len i))).app _ σ₂.op ρ) ∧
      ((rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₁.subst (Fin.natAdd Tgt.as.len i))).app _ σ₂.op ρ).IsDirected ∧
      (piLimit E ℓ).rawExtend
        ((rawInterpret (piLimit E ℓ) (CtxCat.extendTele Tgt Δ hΔ) body).app _
          (σ₂ ≫ RawCtx.toCtx.map σ₁).op
          (ρ.pushFin fun i => (rawInterpret (piLimit E ℓ) Tgt
            (σ₁.subst (Fin.natAdd Tgt.as.len i))).app _ σ₂.op ρ))
        ((Tm E ℓ).map σ₂.op (Tm.label Tgt.as happ))
        ((rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₁.subst (Fin.natAdd Tgt.as.len i))).app _ σ₂.op ρ) =
        (rawInterpret (piLimit E ℓ) Tgt (e.apps fun i => σ₁.subst (Fin.natAdd Tgt.as.len i))).app _ σ₂.op ρ := by
  have ⟨_, hadm⟩ := RawTeleProperties.extend_admissible_over Δ hΔ pΔ
    σ₁ hover pσ₁ hσ₁fixed σ₂ ρ hρ
  have he' : E[Tgt.as.ctx] ⊢ₛ e : (Ctx.pi body Δ).subst Subst.id := by
    rwa [Expr.subst_id]
  exact rawInterpret_applyTele_source Δ hΔ pΔ body hbody pbody (𝟙 Tgt.as) e he' σ₁
    hover happ σ₂ ρ ρ (pei σ₂ ρ hρ)
    (HasFixedness.id_rawExtend (Ctx.pi_isTypeStrong (CtxCat.extendTele Tgt Δ hΔ).as.wf hbody).choose_spec
      he he' pef σ₂ ρ hρ)
    hadm

end Metalean.CoherentShape
