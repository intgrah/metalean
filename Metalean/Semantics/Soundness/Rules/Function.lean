module

public import Metalean.TypeTheory.Syntactic.Pi.Term
public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Judgment
public import Metalean.TypeTheory.Syntactic.Substitution
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Interpretation.Application
import Metalean.Semantics.Interpretation.Binder.Pi
import Metalean.Semantics.Interpretation.Binder.Substitution
import Metalean.Semantics.Interpretation.Binder.Support
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Interpretation
public import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {t t₁ t₂ e e₁ e₂ f f' : Expr ζ ℓ Γ₁.as.len}
  {t' t₁' t₂' e' e₁' e₂' : Expr ζ ℓ (Γ₁.as.len + 1)} {u v : Level ℓ}

namespace HasSubstitution

theorem binder_body (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (htI : HasIdeality Γ₁ t)
    (he' : HasSubstitution (CtxCat.extension Γ₁ ht) e')
    (σ₁ : Γ₂.as ⟶ Γ₁.as) (σ₂ : Γ₃ ⟶ Γ₂) (ρs ρt : RawValuation Γ₃)
    (hσ₁ : SemanticSubstitution σ₁ σ₂ ρs ρt)
    (hρ : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρs)
    ⦃Γ₄ : CtxCat E ℓ⦄ (σ₃ : Γ₄ ⟶ Γ₃) (name : Tm_ Γ₄)
    (s : Raw.ContextSection (ht.substitution σ₁.typed) (σ₃ ≫ σ₂) name)
    (J : Domain Γ₄)
    (hJ : (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Γ₁ t).app _ ((σ₃ ≫ σ₂) ≫ RawCtx.toCtx.map σ₁).op
        (ρs.pullback σ₃)) name J.val = J.val) :
    (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) e').app _ (s.hom ≫ CtxCat.extensionMap ht σ₁).op
        ((ρs.pullback σ₃).push J.val) =
      (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₂ (ht.substitution σ₁.typed))
        (e'.subst σ₁.subst.lift)).app _ s.hom.op
        ((ρt.pullback σ₃).push J.val) := by
  have hbase : SourceAdmissible ((σ₃ ≫ σ₂) ≫ RawCtx.toCtx.map σ₁) (ρs.pullback σ₃) := by
    simpa using hρ.pullback σ₃
  have hhead := hbase.push ht (s.mapExtension ht σ₁)
    (htI _ _ hbase) J.property hJ
  have htail : SemanticSubstitution σ₁
      (s.hom ≫ CtxCat.rawProjection Γ₂ (ht.substitution σ₁.typed))
      (ρs.pullback σ₃) ((ρt.pullback σ₃).push J.val).tail := by
    rw [s.over, RawValuation.tail_push]
    exact hσ₁.pullback σ₃
  have htest := SemanticSubstitution.lift ht σ₁ s.hom (ρs.pullback σ₃)
    ((ρt.pullback σ₃).push J.val) htail
  exact (he'
    (σ₁.lift ⟨u, ht⟩) s.hom ((ρs.pullback σ₃).push J.val)
    ((ρt.pullback σ₃).push J.val) htest hhead).symm

theorem lam (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (htI : HasIdeality Γ₁ t)
    (hts : HasSubstitution Γ₁ t) (he' : HasSubstitution (CtxCat.extension Γ₁ ht) e') :
    HasSubstitution Γ₁ (.lam t e') := by
  intro Γ₂ Γ₃ σ₁ σ₂ ρs ρt hσ₁ hρ
  change (rawInterpret (piLimit E ℓ) Γ₂ (.lam (t.subst σ₁.subst) (e'.subst σ₁.subst.lift))).app _ σ₂.op ρt = _
  rw [rawInterpret_lam (piLimit E ℓ) ht,
    rawInterpret_lam (piLimit E ℓ) (ht.substitution σ₁.typed)]
  symm
  apply RawFamily.abstraction_substitution_eq (CtxCat.rawComprehension ht)
    (CtxCat.rawComprehension (ht.substitution σ₁.typed))
    (CtxCat.extensionIsPullback ht σ₁) (CtxCat.map_extensionMap_binderVar ht σ₁)
  · exact htI _ _ hρ
  · exact (hts σ₁ σ₂ ρs ρt hσ₁ hρ).symm
  · exact binder_body ht htI he' σ₁ σ₂ ρs ρt hσ₁ hρ

theorem forallE (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (hts : HasSubstitution Γ₁ t)
    (hts' : HasSubstitution (CtxCat.extension Γ₁ ht) t') :
    HasSubstitution Γ₁ (.forallE t t') := by
  intro Γ₂ Γ₃ σ₁ σ₂ ρs ρt hσ₁ hρ
  have htσ' : E[Γ₂.as.ctx.snoc (t.subst σ₁.subst)] ⊢ₛ t'.subst σ₁.subst.lift : .sort v :=
    ht'.substitution (σ₁.lift ⟨u, ht⟩).typed
  change (rawInterpret (piLimit E ℓ) Γ₂ (.forallE (t.subst σ₁.subst) (t'.subst σ₁.subst.lift))).app _
    σ₂.op ρt = _
  rw [rawInterpret_forallE (piLimit E ℓ) ht ht',
    rawInterpret_forallE (piLimit E ℓ) (ht.substitution σ₁.typed) htσ']
  symm
  rw [← Ty.pairPresheaf_map_ofTyping ht ht' σ₁]
  exact
    RawFamily.pi_substitution_eq (CtxCat.rawComprehension ht) (CtxCat.rawComprehension (ht.substitution σ₁.typed))
    (CtxCat.extensionIsPullback ht σ₁) (CtxCat.map_extensionMap_binderVar ht σ₁) (Ty.pairOfTyping Γ₁.as ht ht')
      _ _ _ _ σ₂ ρs ρt (htI _ _ hρ) (hts σ₁ σ₂ ρs ρt hσ₁ hρ).symm
      (binder_body ht htI hts' σ₁ σ₂ ρs ρt hσ₁ hρ)

end HasSubstitution

theorem HasSubstitution.app (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (he : E[Γ₁.as.ctx] ⊢ₛ e : t) (htI : HasIdeality Γ₁ t)
    (htI' : HasIdeality (Γ₁.extension ht) t')
    (hfI : HasIdeality Γ₁ f) (heI : HasIdeality Γ₁ e)
    (hf : E[Γ₁.as.ctx] ⊢ₛ f : .forallE t t')
    (hfF : HasFixedness Γ₁ f (.forallE t t'))
    (hfs : HasSubstitution Γ₁ f) (has : HasSubstitution Γ₁ e) :
    HasSubstitution Γ₁ (.app f e) :=
  fun _ _ σ₁ σ₂ ρs ρt hσ₁ hρ => rawInterpret_app_subst ht ht' he σ₁ σ₂ ρs ρt
    (htI _ _ hρ) (HasIdeality.bodyAction ht htI htI' _ _ hρ) (hfI _ _ hρ) (heI _ _ hρ) _
    (hfF hf _ _ hρ) (hfs σ₁ σ₂ ρs ρt hσ₁ hρ) (has σ₁ σ₂ ρs ρt hσ₁ hρ)

theorem piLimit_rawExtend_sort_le (r : Level ℓ) (n : Tm_ Γ₁)
    {I : RawValue Γ₁} :
    (piLimit E ℓ).rawExtend (ΩLower.principal (pointedOrder E ℓ) (sortAtom r)) n I ≤ I :=
  fun σ y hy => ((mem_piLimit_rawExtend_sort_iff r I n σ y).mp hy).1

theorem SourceAdmissible.push_fixed_pullback (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u) (htI : HasIdeality Γ₁ t₁)
    {σ₁ : Γ₂ ⟶ Γ₁} {ρ : RawValuation Γ₂} (hρ : SourceAdmissible σ₁ ρ)
    (J : Domain Γ₂) {label : Tm_ Γ₂}
    (hJ : (piLimit E ℓ).rawExtend ((rawInterpret (piLimit E ℓ) Γ₁ t₁).app _ σ₁.op ρ) label
      J.val = J.val)
    (σ₂ : Γ₃ ⟶ Γ₂)
    (s : Raw.ContextSection ht₁ (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op label)) :
    SourceAdmissible s.hom ((ρ.pullback σ₂).push (J.val.pullback σ₂)) := by
  have hJ' := congrArg (fun I : RawValue Γ₂ ↦ I.pullback σ₂) hJ
  rw [(piLimit E ℓ).pullback_rawExtend, RawFamily.app_pullback] at hJ'
  exact (hρ.pullback σ₂).push ht₁ s (htI _ _ (hρ.pullback σ₂))
    (J.pullback σ₂).property hJ'

theorem HasIdeality.forallE (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u) (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ t₁' : .sort v)
    (htI : HasIdeality Γ₁ t₁) (htI' : HasIdeality (CtxCat.extension Γ₁ ht₁) t₁') :
    HasIdeality Γ₁ (.forallE t₁ t₁') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht₁ ht₁', RawFamily.pi_value]
  exact rawPi_isDirected _ _ (htI σ ρ hρ) (bodyAction ht₁ htI htI' σ ρ hρ)

theorem HasIdeality.lam (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u) (htI : HasIdeality Γ₁ t₁)
    (heI' : HasIdeality (CtxCat.extension Γ₁ ht₁) e₁') : HasIdeality Γ₁ (.lam t₁ e₁') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_lam (piLimit E ℓ) ht₁, RawFamily.abstraction_value]
  exact RawAction.abstraction_isDirected _ (bodyAction ht₁ htI heI' σ ρ hρ)

theorem HasFixedness.forallE (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u)
    (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ t₁' : .sort v)
    (htI : HasIdeality Γ₁ t₁) (htsort' : HasFixedness (CtxCat.extension Γ₁ ht₁) t₁' (.sort v)) :
    HasFixedness Γ₁ (.forallE t₁ t₁') (.sort (.imax u v)) := by
  intro Γ₂ _ σ₁ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht₁ ht₁', RawFamily.pi_value, rawInterpret_sort,
    RawFamily.sort_value]
  refine le_antisymm (by exact piLimit_rawExtend_sort_le _ _) fun Γ₃ σ₂ y hy => ?_
  have ⟨a, ⟨f, hcoh⟩, _, hf, hy'⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hy
  refine (mem_piLimit_rawExtend_sort_iff _ _ _ _ _).mpr ⟨hy, ?_⟩
  rw [Level.rel_imax]
  cases hv : Level.rel v with
  | true => exact Shape.IsCode.of_le hy' .forallE
  | false =>
    refine Shape.IsCode.of_le hy' (.forallE_prop fun i => ?_)
    let T := rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht₁) t₁'
    have hT : ((rawInterpret (piLimit E ℓ) Γ₁ t₁).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).IsDirected :=
      htI _ _ (hρ.pullback σ₂)
    let J : Domain Γ₃ := ⟨_, (piLimit E ℓ).rawExtend_isDirected (f.names i) hT
      (principalIdeal (CoherentGraph.input ⟨f, hcoh⟩ i)).property⟩
    have hJ := (piLimit E ℓ).rawExtend_idempotent piLimit_isIdempotent (f.names i) hT
      (principalIdeal (CoherentGraph.input ⟨f, hcoh⟩ i)).property
    let S := RawFamily.bodySection (CtxCat.rawComprehension ht₁) T (σ₂ ≫ σ₁) (ρ.pullback σ₂) (f.names i)
      J.val
    have hsort : (piLimit E ℓ).rawExtend (ΩLower.principal (pointedOrder E ℓ) (sortAtom v))
        (f.names i) S.extend = S.extend := by
      apply S.eq_extend
      · intro Γ₄ σ₃ z hz
        exact S.support (piLimit_rawExtend_sort_le v _ σ₃ z hz)
      · intro Γ₄ σ₃ s
        rw [(piLimit E ℓ).pullback_rawExtend, ΩLower.presheaf_map_principal, S.pullback_extend σ₃ s]
        have h := htsort' ht₁' s.hom _
          ((hρ.pullback σ₂).push_fixed_pullback ht₁ htI J hJ σ₃ s)
        rw [rawInterpret_sort, RawFamily.sort_value] at h
        exact Eq.trans (ΩLower.ext fun σ z => (mem_piLimit_rawExtend_sort_iff v _ _ σ z).trans
          (mem_piLimit_rawExtend_sort_iff v _ _ σ z).symm) h
    have hmem := hf i
    change (RawFamily.sectionValue (CtxCat.rawComprehension ht₁) T (σ₂ ≫ σ₁) (ρ.pullback σ₂) (f.names i)
      J.val).mem (𝟙 Γ₃) _ at hmem
    rw [RawFamily.sectionValue, ← hsort] at hmem
    have ⟨_, hcode⟩ := (mem_piLimit_rawExtend_sort_iff _ _ _ _ _).mp hmem
    rwa [hv] at hcode

theorem Tm.section_label (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u)
    (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ t₁' : .sort v) (he₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ e₁' : t₁')
    {σ : Γ₂ ⟶ Γ₁} {m : Tm_ Γ₂} (s : Raw.ContextSection ht₁ σ m)
    (h : Tm.type ((Tm E ℓ).map σ.op (Tm.label Γ₁.as (.lamDF ht₁ ht₁' ht₁' he₁' he₁'))) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).1
        ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).2)
    (hm : Tm.type m =
      yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).1) :
    (Tm E ℓ).map s.hom.op (Tm.label (CtxCat.extension Γ₁ ht₁).as he₁') =
      Tm.apply ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).1
        ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).2
        ((Tm E ℓ).map σ.op (Tm.label Γ₁.as (.lamDF ht₁ ht₁' ht₁' he₁' he₁'))) m h hm := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  have hlift := SubstWFStrong.lift ⟨u, ht₁⟩ σ.typed
  have htσ : E[Γ₂.as.ctx] ⊢ₛ t₁.subst σ.subst : .sort u := ht₁.substitution σ.typed
  have htσ' : E[Γ₂.as.ctx.snoc (t₁.subst σ.subst)] ⊢ₛ t₁'.subst σ.subst.lift : .sort v :=
    ht₁'.substitution hlift
  have heσ' : E[Γ₂.as.ctx.snoc (t₁.subst σ.subst)] ⊢ₛ e₁'.subst σ.subst.lift : t₁'.subst σ.subst.lift :=
    he₁'.substitution hlift
  have hlabel := Ty.pairPresheaf_map_ofTyping ht₁ ht₁' σ
  have hmty : Tm.type m = Ty.ofRepr ⟨t₁.subst σ.subst, u, htσ⟩ := by
    rw [hm, hlabel]
    exact yonedaEquiv.apply_symm_apply _
  have ⟨a, harg, hmeq⟩ := Tm.exists_label m ⟨t₁.subst σ.subst, u, htσ⟩ hmty
  have hres : E[Γ₂.as.ctx] ⊢ₛ (t₁'.subst σ.subst.lift).inst a : .sort v :=
    DefeqStrong.inst_congr htσ' harg
  have hinst : E[Γ₂.as.ctx] ⊢ₛ (e₁'.subst σ.subst.lift).inst a :
      (t₁'.subst σ.subst.lift).inst a := DefeqStrong.inst_congr heσ' harg
  have h' : Tm.type (Tm.label Γ₂.as (.lamDF htσ htσ' htσ' heσ' heσ')) =
      Ty.piApp (Ty.pairOfTyping Γ₂.as htσ htσ').1 (Ty.pairOfTyping Γ₂.as htσ htσ').2 :=
    ((Ty.piApp_eq_ofRepr _ _ ⟨_, u, htσ⟩ (yonedaEquiv.apply_symm_apply _) ⟨_, v, htσ'⟩
      (Ty.eval_familyOfTyping Γ₂.as htσ htσ').symm)).symm
  have hm' : Tm.type (Tm.label Γ₂.as harg) =
      yonedaEquiv (Ty.pairOfTyping Γ₂.as htσ htσ').1 :=
    (CtxCat.rawComprehension_type htσ).symm
  have hsnoc : s.hom = (Raw.ContextSection.ofTyping ht₁ σ harg).hom :=
    Section.hom_eq s
      { hom := (Raw.ContextSection.ofTyping ht₁ σ harg).hom
        over := (Raw.ContextSection.ofTyping ht₁ σ harg).over
        generic := ((Raw.ContextSection.ofTyping ht₁ σ harg).generic).trans hmeq.symm }
  rw [hsnoc]
  change (Tm E ℓ).map (RawCtx.toCtx.map (σ.snoc ⟨u, ht₁⟩ harg)).op _ = _
  rw [Tm.map_label he₁' (σ.snoc ⟨u, ht₁⟩ harg)]
  refine Eq.trans ?_
    (Tm.apply_congr hlabel (Tm.map_label (.lamDF ht₁ ht₁' ht₁' he₁' he₁') σ) hmeq h hm h' hm').symm
  refine Eq.trans ?_
    (Tm.apply_label Γ₂.as htσ htσ' (.lamDF htσ htσ' htσ' heσ' heσ') harg hres h' hm').symm
  refine Tm.label_eq ?_ ?_
  · change E[Γ₂.as.ctx] ⊢ₛ t₁'.subst (σ.subst.extend a) ≡ _ typ
    rw [← Expr.inst_subst_lift]
    exact IsTypeEq.ofDefEq hres
  · change E[Γ₂.as.ctx] ⊢ₛ e₁'.subst (σ.subst.extend a) ≡ _ :
      t₁'.subst (σ.subst.extend a)
    rw [← Expr.inst_subst_lift, ← Expr.inst_subst_lift]
    exact (DefeqStrong.beta htσ htσ' heσ' harg hres hinst).symm

theorem HasFixedness.lam (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u) (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ t₁' : .sort v)
    (he₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ e₁' : t₁')
    (htI : HasIdeality Γ₁ t₁) (htI' : HasIdeality (CtxCat.extension Γ₁ ht₁) t₁')
    (heI' : HasIdeality (CtxCat.extension Γ₁ ht₁) e₁')
    (heF' : HasFixedness (CtxCat.extension Γ₁ ht₁) e₁' t₁') :
    HasFixedness Γ₁ (.lam t₁ e₁') (.forallE t₁ t₁') := by
  intro Γ₂ _ σ₁ ρ hρ
  rw [rawInterpret_lam (piLimit E ℓ) ht₁, rawInterpret_forallE (piLimit E ℓ) ht₁ ht₁',
    RawFamily.abstraction_value, RawFamily.pi_value]
  refine RawFamily.normalizedAbstraction_fixed ht₁ _ _ _
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht₁) t₁')
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht₁) e₁') σ₁ ρ _
    (by
      change yonedaEquiv (yoneda.map σ₁ ≫ (CtxCat.rawComprehension ht₁).type) = _
      rw [← yonedaEquiv_naturality, CtxCat.rawComprehension_type]) _ ?_ (htI σ₁ ρ hρ)
    (HasIdeality.bodyAction ht₁ htI htI' σ₁ ρ hρ) (HasIdeality.bodyAction ht₁ htI heI' σ₁ ρ hρ) ?_
  · rw [Tm.type_map, Ty.piApp_pairPresheaf_map]
    exact congrArg ((Ty E ℓ).map σ₁.op)
      (Ty.piApp_eq_ofRepr _ _ ⟨_, u, ht₁⟩ (CtxCat.rawComprehension_type ht₁) ⟨_, v, ht₁'⟩
        (Ty.eval_familyOfTyping Γ₁.as ht₁ ht₁').symm).symm
  · intro Γ₃ σ₂ name J hguard hmguard hJ
    let S₁ := RawFamily.bodySection (CtxCat.rawComprehension ht₁)
      (rawInterpret (piLimit E ℓ) (Γ₁.extension ht₁) t₁') (σ₂ ≫ σ₁) (ρ.pullback σ₂) name J.val
    let S₂ := RawFamily.bodySection (CtxCat.rawComprehension ht₁)
      (rawInterpret (piLimit E ℓ) (Γ₁.extension ht₁) e₁') (σ₂ ≫ σ₁) (ρ.pullback σ₂) name J.val
    apply S₂.eq_extend
    · intro Γ₄ σ₃ y hy hne
      have ⟨c, hc, hcne⟩ := (piLimit E ℓ).rawExtend_nonbottom_code piLimit_value_bottom hy hne
      exact S₁.support hc hcne
    intro Γ₄ σ₃ t
    rw [(piLimit E ℓ).pullback_rawExtend, RawFamily.sectionValue, RawFamily.sectionValue,
      S₁.pullback_extend σ₃ t, S₂.pullback_extend σ₃ t]
    refine (congrArg (fun m => (piLimit E ℓ).rawExtend _ m _) ?_).trans
      (heF' he₁' t.hom _ ((hρ.pullback σ₂).push_fixed_pullback ht₁ htI J hJ σ₃ t))
    symm
    have hguard' : Tm.type ((Tm E ℓ).map σ₃.op ((Tm E ℓ).map σ₂.op ((Tm E ℓ).map σ₁.op
          (Tm.label Γ₁.as (.lamDF ht₁ ht₁' ht₁' he₁' he₁'))))) =
        Ty.piApp (yoneda.map σ₃ ≫ ((Ty.pairPresheaf E ℓ).map σ₂.op
            ((Ty.pairPresheaf E ℓ).map σ₁.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁'))).1)
          (fibreMap ((Ty.pairPresheaf E ℓ).map σ₂.op
            ((Ty.pairPresheaf E ℓ).map σ₁.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁'))).1
              (yoneda.map σ₃) ≫ ((Ty.pairPresheaf E ℓ).map σ₂.op
                ((Ty.pairPresheaf E ℓ).map σ₁.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁'))).2) := by
      rw [Tm.type_map, hguard, Ty.map_piApp]
    have hmguard' : Tm.type ((Tm E ℓ).map σ₃.op name) =
        yonedaEquiv (yoneda.map σ₃ ≫ ((Ty.pairPresheaf E ℓ).map σ₂.op
          ((Ty.pairPresheaf E ℓ).map σ₁.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁'))).1) := by
      rw [Tm.type_map, hmguard, ← yonedaEquiv_naturality]
    have triple (F : (CtxCat E ℓ)ᵒᵖ ⥤ Type) (x : F.obj (.op Γ₁)) :
        F.map σ₃.op (F.map σ₂.op (F.map σ₁.op x)) = F.map (σ₃ ≫ σ₂ ≫ σ₁).op x := by
      rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
      rfl
    have eL := triple (Ty.pairPresheaf E ℓ) (Ty.pairOfTyping Γ₁.as ht₁ ht₁')
    have eN := triple (Tm E ℓ) (Tm.label Γ₁.as (.lamDF ht₁ ht₁' ht₁' he₁' he₁'))
    have h : Tm.type ((Tm E ℓ).map (σ₃ ≫ σ₂ ≫ σ₁).op
          (Tm.label Γ₁.as (.lamDF ht₁ ht₁' ht₁' he₁' he₁'))) =
        Ty.piApp ((Ty.pairPresheaf E ℓ).map (σ₃ ≫ σ₂ ≫ σ₁).op
            (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).1
          ((Ty.pairPresheaf E ℓ).map (σ₃ ≫ σ₂ ≫ σ₁).op
            (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).2 := by
      rw [Tm.type_map, Ty.piApp_pairPresheaf_map]
      exact congrArg ((Ty E ℓ).map (σ₃ ≫ σ₂ ≫ σ₁).op)
        (Ty.piApp_eq_ofRepr _ _ ⟨_, u, ht₁⟩ (CtxCat.rawComprehension_type ht₁) ⟨_, v, ht₁'⟩
          (Ty.eval_familyOfTyping Γ₁.as ht₁ ht₁').symm).symm
    have hm : Tm.type ((Tm E ℓ).map σ₃.op name) =
        yonedaEquiv ((Ty.pairPresheaf E ℓ).map (σ₃ ≫ σ₂ ≫ σ₁).op
          (Ty.pairOfTyping Γ₁.as ht₁ ht₁')).1 := by
      rw [← eL]
      exact hmguard'
    rw [Tm.map_apply _ _ _ _ hguard hmguard σ₃ hguard' hmguard']
    exact (Tm.section_label ht₁ ht₁' he₁' t h hm).trans
      (Tm.apply_congr eL.symm eN.symm rfl h hm hguard' hmguard')

namespace HasEquality

theorem normalizedBodyAction_contextConversion
    (ht : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ : .sort u) (htI : HasIdeality Γ₁ t₁)
    (hteq : HasEquality Γ₁ t₁ t₂)
    (he' : HasEquality (CtxCat.extension Γ₁ ht.left) e₁' e₂')
    (he₂' : HasSubstitution (CtxCat.extension Γ₁ ht.left) e₂')
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ)
    (σ₂ : Γ₃ ⟶ Γ₂) (label : Tm_ Γ₃) (I : Domain Γ₃) :
    (RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht.left) (rawInterpret (piLimit E ℓ) Γ₁ t₁)
      (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht.left) e₁') σ₁ ρ).app _ (σ₂.op, label) I.val =
      (RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht.right) (rawInterpret (piLimit E ℓ) Γ₁ t₂)
        (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht.right) e₂') σ₁ ρ).app _ (σ₂.op, label) I.val := by
  have hT : ((rawInterpret (piLimit E ℓ) Γ₁ t₁).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)).IsDirected :=
    htI _ _ (hρ.pullback σ₂)
  let J : Domain Γ₃ := ⟨_, (piLimit E ℓ).rawExtend_isDirected label hT I.property⟩
  have hJ := (piLimit E ℓ).rawExtend_idempotent piLimit_isIdempotent label hT I.property
  change RawFamily.sectionValue (CtxCat.rawComprehension _) _ _ _ _ J.val =
    RawFamily.sectionValue (CtxCat.rawComprehension _) _ _ _ _
      ((piLimit E ℓ).rawExtend
        ((rawInterpret (piLimit E ℓ) Γ₁ t₂).app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) label I.val)
  rw [← hteq _ _ (hρ.pullback σ₂)]
  change RawFamily.sectionValue (CtxCat.rawComprehension ht.left) _ (σ₂ ≫ σ₁) (ρ.pullback σ₂) label
      J.val =
    RawFamily.sectionValue (CtxCat.rawComprehension ht.right) _ (σ₂ ≫ σ₁) (ρ.pullback σ₂) label J.val
  have hbody {Γ₄ : CtxCat E ℓ} (σ₃ : Γ₄ ⟶ Γ₃)
      (s : Raw.ContextSection ht.right (σ₃ ≫ σ₂ ≫ σ₁) ((Tm E ℓ).map σ₃.op label)) :
      (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht.left) e₁').app _ (s.convert ht).hom.op
          (((ρ.pullback σ₂).pullback σ₃).push (J.val.pullback σ₃)) =
        (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht.right) e₂').app _ s.hom.op
          (((ρ.pullback σ₂).pullback σ₃).push (J.val.pullback σ₃)) := by
    have hadm := (hρ.pullback σ₂).push_fixed_pullback ht.left htI J hJ σ₃ (s.convert ht)
    have h := he₂'.rename (r := CtxCat.contextConversionRaw (.ofDefEq ht) ht.left ht.right) (fun v => ⟨v, rfl⟩) s.hom
      (.of_var id (fun _ => rfl) fun _ => rfl) hadm
    rw [show (CtxCat.contextConversionRaw (.ofDefEq ht) ht.left ht.right).subst = Subst.id from rfl, Expr.subst_id] at h
    exact (he' _ _ hadm).trans h.symm
  ext Γ₄ σ₃ y
  simp_rw [RawFamily.mem_sectionValue]
  constructor
  · intro
    | .inl hy => exact Or.inl hy
    | .inr ⟨s, hy⟩ =>
      let s' := Raw.ContextSection.convert ht.symm s
      have hs : (s'.convert ht).hom = s.hom := Section.hom_eq _ _
      exact Or.inr ⟨s', by rwa [← hbody σ₃ s', hs]⟩
  · intro
    | .inl hy => exact Or.inl hy
    | .inr ⟨s, hy⟩ => exact Or.inr ⟨Raw.ContextSection.convert ht s, by rwa [hbody σ₃ s]⟩

theorem lam (ht : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ : .sort u) (htI : HasIdeality Γ₁ t₁)
    (hteq : HasEquality Γ₁ t₁ t₂)
    (he' : HasEquality (CtxCat.extension Γ₁ ht.left) e₁' e₂')
    (he₂' : HasSubstitution (CtxCat.extension Γ₁ ht.left) e₂') :
    HasEquality Γ₁ (.lam t₁ e₁') (.lam t₂ e₂') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_lam (piLimit E ℓ) ht.left,
    rawInterpret_lam (piLimit E ℓ) ht.right, RawFamily.abstraction_value,
    RawFamily.abstraction_value]
  exact RawAction.abstraction_eq_of_eq_on_ideals (normalizedBodyAction_contextConversion ht htI hteq he' he₂' σ ρ hρ)

theorem forallE (ht : E[Γ₁.as.ctx] ⊢ₛ t₁ ≡ t₂ : .sort u)
    (ht' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ t₁' ≡ t₂' : .sort v)
    (ht₂' : E[Γ₁.as.ctx.snoc t₂] ⊢ₛ t₁' ≡ t₂' : .sort v)
    (htI : HasIdeality Γ₁ t₁) (hteq : HasEquality Γ₁ t₁ t₂)
    (hteq' : HasEquality (CtxCat.extension Γ₁ ht.left) t₁' t₂')
    (htR' : HasSubstitution (CtxCat.extension Γ₁ ht.left) t₂') :
    HasEquality Γ₁ (.forallE t₁ t₁') (.forallE t₂ t₂') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht.left ht'.left,
    rawInterpret_forallE (piLimit E ℓ) ht.right ht₂'.right,
    RawFamily.pi_value, RawFamily.pi_value, Ty.pairOfTyping_congr Γ₁.as ht ht', hteq σ ρ hρ]
  exact rawPi_eq_of_eq_on_ideals _ _
    (normalizedBodyAction_contextConversion ht htI hteq hteq' htR' σ ρ hρ)

end HasEquality

theorem RawInterpretationProperties.forallE (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u)
    (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ₛ t₁' : .sort v)
    (pt : RawInterpretationProperties Γ₁ t₁) (pt' : RawInterpretationProperties (CtxCat.extension Γ₁ ht₁) t₁') :
    RawInterpretationProperties Γ₁ (.forallE t₁ t₁') where
  ideal := HasIdeality.forallE ht₁ ht₁' pt.ideal pt'.ideal
  subst := HasSubstitution.forallE ht₁ ht₁' pt.ideal pt.subst pt'.subst

theorem RawInterpretationProperties.lam (ht₁ : E[Γ₁.as.ctx] ⊢ₛ t₁ : .sort u)
    (pt : RawInterpretationProperties Γ₁ t₁) (pe₁' : RawInterpretationProperties (CtxCat.extension Γ₁ ht₁) e₁') :
    RawInterpretationProperties Γ₁ (.lam t₁ e₁') where
  ideal := HasIdeality.lam ht₁ pt.ideal pe₁'.ideal
  subst := HasSubstitution.lam ht₁ pt.ideal pt.subst pe₁'.subst

theorem RawJudgment.forallEDF (pt : RawJudgment Γ₁ t₁ t₂ (.sort u))
    (pt' : RawJudgment (CtxCat.extension Γ₁ pt.syntactic.left) t₁' t₂' (.sort v))
    (pt₂' : RawJudgment (CtxCat.extension Γ₁ pt.syntactic.right) t₁' t₂' (.sort v)) :
    RawJudgment Γ₁ (.forallE t₁ t₁') (.forallE t₂ t₂') (.sort (.imax u v)) where
  syntactic := .forallEDF pt.syntactic pt'.syntactic pt₂'.syntactic
  type := RawInterpretationProperties.sort Γ₁ (.imax u v)
  left := RawInterpretationProperties.forallE pt.syntactic.left pt'.syntactic.left pt.left pt'.left
  right := RawInterpretationProperties.forallE pt.syntactic.right pt₂'.syntactic.right pt.right
    pt₂'.right
  equal := HasEquality.forallE pt.syntactic pt'.syntactic pt₂'.syntactic pt.left.ideal pt.equal
    pt'.equal pt'.right.subst
  fixed := HasFixedness.forallE pt.syntactic.left pt'.syntactic.left pt.left.ideal pt'.fixed

theorem RawJudgment.lamDF (pt : RawJudgment Γ₁ t₁ t₂ (.sort u))
    (pt' : RawJudgment (CtxCat.extension Γ₁ pt.syntactic.left) t₁' t₁' (.sort v))
    (pe' : RawJudgment (CtxCat.extension Γ₁ pt.syntactic.left) e₁' e₂' t₁')
    (pe₂' : RawJudgment (CtxCat.extension Γ₁ pt.syntactic.right) e₁' e₂' t₁') :
    RawJudgment Γ₁ (.lam t₁ e₁') (.lam t₂ e₂') (.forallE t₁ t₁') where
  syntactic := .lamDF pt.syntactic pt'.syntactic (pt.syntactic.snocConv pt'.syntactic)
    pe'.syntactic pe₂'.syntactic
  type := RawInterpretationProperties.forallE pt.syntactic.left pt'.syntactic pt.left pt'.left
  left := RawInterpretationProperties.lam pt.syntactic.left pt.left pe'.left
  right := RawInterpretationProperties.lam pt.syntactic.right pt.right pe₂'.right
  equal := HasEquality.lam pt.syntactic pt.left.ideal pt.equal pe'.equal pe'.right.subst
  fixed := HasFixedness.lam pt.syntactic.left pt'.syntactic pe'.syntactic.left pt.left.ideal
    pt'.left.ideal pe'.left.ideal pe'.fixed

theorem HasIdeality.application_value_subst
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (htI' : HasIdeality (Γ₁.extension ht) t')
    (σ₁ : Γ₂.as ⟶ Γ₁.as) {e : Expr ζ ℓ Γ₂.as.len}
    (he : E[Γ₂.as.ctx] ⊢ₛ e : t.subst σ₁.subst)
    (σ₂ : Γ₃ ⟶ Γ₂) (ρ : RawValuation Γ₃)
    (hρ : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρ) {F : Domain Γ₃}
    (n : Tm_ Γ₃)
    (hF : (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) Γ₁ (.forallE t t')).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρ) n
      F.val = F.val) (X : Domain Γ₃) :
    rawApplication F.val ((Tm E ℓ).map σ₂.op '' RawFamily.sourceQuery Γ₂ e) X.val =
      (application F ((Tm E ℓ).map σ₂.op (Tm.label Γ₂.as he)) X).val := by
  rw [rawInterpret_forallE (piLimit E ℓ) ht ht'] at hF
  apply RawFamily.rawApplication_eq_of_sections (ht.substitution σ₁.typed) he σ₂ F X
  intro Γ₄ σ₃ name x y hy
  refine (RawFamily.outputAtom_rawPi_fixed_bot_or_section ht _ (rawInterpret (piLimit E ℓ) Γ₁ t)
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') _ ρ (htI _ ρ hρ)
    (bodyAction ht htI htI' _ ρ hρ) n hF σ₃ hy).imp_right ?_
  rintro ⟨s⟩
  exact ⟨Raw.ContextSection.cartesianLift ht σ₁ (by simpa using s)⟩

theorem HasIdeality.application_fixed
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (htI' : HasIdeality (Γ₁.extension ht) t')
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ)
    {F X : Domain Γ₂} {name : Tm_ Γ₂}
    (s : Raw.ContextSection ht σ name) (n : Tm_ Γ₂)
    (hF : (piLimit E ℓ).rawExtend ((rawInterpret (piLimit E ℓ) Γ₁ (.forallE t t')).app _ σ.op ρ) n
      F.val = F.val)
    (hX : (piLimit E ℓ).rawExtend ((rawInterpret (piLimit E ℓ) Γ₁ t).app _ σ.op ρ) name
      X.val = X.val)
    (h : Tm.type n =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).1
        ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).2)
    (hm : Tm.type name =
      yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).1) :
    (piLimit E ℓ).rawExtend
      ((rawInterpret (piLimit E ℓ) (Γ₁.extension ht) t').app _ s.hom.op (ρ.push X.val))
      (Tm.apply ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).1
        ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).2 n name h hm)
      (application F name X).val = (application F name X).val := by
  rw [rawInterpret_forallE (piLimit E ℓ) ht ht'] at hF
  have elabel : (Ty.pairPresheaf E ℓ).map (𝟙 Γ₂).op
      ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')) =
      (Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht') := by
    simp only [op_id, Functor.map_id_apply]
  have en : (Tm E ℓ).map (𝟙 Γ₂).op n = n := by simp only [op_id, Functor.map_id_apply]
  have h' : Tm.type ((Tm E ℓ).map (𝟙 Γ₂).op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map (𝟙 Γ₂).op
          ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht'))).1
        ((Ty.pairPresheaf E ℓ).map (𝟙 Γ₂).op
          ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht'))).2 := by
    rwa [elabel, en]
  have hm' : Tm.type name = yonedaEquiv ((Ty.pairPresheaf E ℓ).map (𝟙 Γ₂).op
      ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht'))).1 := by
    rwa [elabel]
  refine Eq.trans (congrArg (fun m => (piLimit E ℓ).rawExtend _ m _)
    (Tm.apply_congr elabel en rfl h' hm' h hm).symm) ?_
  have hfix := RawFamily.application_rawPi_fixed ht _ (rawInterpret (piLimit E ℓ) Γ₁ t)
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') σ ρ (htI σ ρ hρ)
    (bodyAction ht htI htI' σ ρ hρ) n hF (𝟙 Γ₂) name X (by simpa using hX) h' hm'
  simp only [Category.id_comp, RawValuation.pullback_id, ΩIdeal.pullback_id] at hfix
  rw [RawFamily.sectionValue_eq_value (CtxCat.rawComprehension ht) _ σ ρ name X.val s] at hfix
  exact hfix

theorem HasIdeality.application_value
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (htI' : HasIdeality (Γ₁.extension ht) t')
    (he₁ : E[Γ₁.as.ctx] ⊢ₛ e₁ : t) (hf : E[Γ₁.as.ctx] ⊢ₛ f : .forallE t t')
    (hFI : HasIdeality Γ₁ f) (hXI : HasIdeality Γ₁ e₁)
    (hFF : HasFixedness Γ₁ f (.forallE t t'))
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :
    (rawInterpret (piLimit E ℓ) Γ₁ (.app f e₁)).app _ σ₁.op ρ =
      (application (hρ.eval hFI)
        ((Tm E ℓ).map σ₁.op (Tm.label Γ₁.as he₁)) (hρ.eval hXI)).val := by
  let F := hρ.eval hFI
  let X := hρ.eval hXI
  have hF := hFF hf σ₁ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht ht'] at hF
  rw [rawInterpret_app, RawFamily.application_value]
  exact RawFamily.rawApplication_eq_of_sections ht he₁ σ₁ F X fun σ₂ _ _ _ hy =>
    RawFamily.outputAtom_rawPi_fixed_bot_or_section ht _ (rawInterpret (piLimit E ℓ) Γ₁ t)
      (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') σ₁ ρ (htI σ₁ ρ hρ)
      (bodyAction ht htI htI' σ₁ ρ hρ) _ hF σ₂ hy

theorem eta_body_value (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (hren : HasSubstitution Γ₁ e)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ)
    (F : Domain Γ₂)
    (hF : F.val = (rawInterpret (piLimit E ℓ) Γ₁ e).app _ σ₁.op ρ)
    (hsupport : ∀ {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
      (X : Domain Γ₃) {y : CoherentShape Γ₃},
      (application (F.pullback σ₂) name X).mem (𝟙 Γ₃) y →
      ¬ y ≤ ⊥ →
      Nonempty (Raw.ContextSection ht (σ₂ ≫ σ₁) name))
    {label : Tm_ Γ₂} (s : Raw.ContextSection ht σ₁ label)
    (X : Domain Γ₂) :
    (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) (.app e.wk (.var (Fin.last Γ₁.as.len)))).app _ s.hom.op (ρ.push X.val) = (application F label X).val := by
  have hvar : E[(CtxCat.extension Γ₁ ht).as.ctx] ⊢ₛ .var (Fin.last Γ₁.as.len) :
      t.subst (CtxCat.projectionRaw Γ₁ ht).subst := by
    rw [show t.subst (CtxCat.projectionRaw Γ₁ ht).subst = t.wk from Expr.subst_wk t]
    exact CtxWFStrong.varLast (Γ₁.as.wf.snoc ⟨u, ht⟩)
  rw [rawInterpret_app, RawFamily.application_value, rawInterpret_var, Var.db_last,
    HasSubstitution.wk_value ht hren s.hom (ρ.push X.val) (by rwa [s.over]), s.over,
    RawValuation.tail_push, ← hF]
  refine (RawFamily.rawApplication_eq_of_sections
    (ht.substitution (CtxCat.projectionRaw Γ₁ ht).typed) hvar s.hom F X
      fun {_} σ₂ name {x y} hy => ?_).trans ?_
  · by_cases hbottom : y ≤ ⊥
    · exact Or.inl hbottom
    have ⟨r⟩ := hsupport σ₂ name (principalIdeal x)
      (hy.mem_application ((principalIdeal_mem x (𝟙 _) x).mpr (by simp))) hbottom
    exact Or.inr ⟨Raw.ContextSection.cartesianLift ht (CtxCat.projectionRaw Γ₁ ht)
      ⟨r.hom, r.over.trans ((congrArg (σ₂ ≫ ·) s.over).symm.trans (Category.assoc _ _ _).symm),
        r.generic⟩⟩
  · rw [Tm.label_eq_var hvar rfl, ← CtxCat.rawComprehension_generic]
    exact congrArg (fun n => (application F n X).val) s.generic

theorem eta_sectionValue (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (hren : HasSubstitution Γ₁ e)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ)
    (F : Domain Γ₂)
    (hF : F.val = (rawInterpret (piLimit E ℓ) Γ₁ e).app _ σ₁.op ρ)
    (hsupport : ∀ {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
      (X : Domain Γ₃) {y : CoherentShape Γ₃},
      (application (F.pullback σ₂) name X).mem (𝟙 Γ₃) y →
      ¬ y ≤ ⊥ →
      Nonempty (Raw.ContextSection ht (σ₂ ≫ σ₁) name))
    (label : Tm_ Γ₂) (X : Domain Γ₂) :
    RawFamily.sectionValue (CtxCat.rawComprehension ht)
      (rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) (.app e.wk (.var (Fin.last Γ₁.as.len))))
      σ₁ ρ label X.val = (application F label X).val := by
  refine (PartialSection.eq_extend _ _ (fun σ₂ y hy hne => hsupport σ₂ _ (X.pullback σ₂) ?_ hne)
    fun σ₂ s => ?_).symm
  · rw [← pullback_application]
    exact (ΩIdeal.presheaf_map_mem_id (application F label X) σ₂ y).mpr hy
  change ((application F label X).pullback σ₂).val = _
  rw [pullback_application]
  refine (eta_body_value ht hren (σ₂ ≫ σ₁) (ρ.pullback σ₂) (hρ.pullback σ₂) (F.pullback σ₂)
    ((congrArg (fun I : RawValue Γ₂ ↦ I.pullback σ₂) hF).trans
      ((rawInterpret (piLimit E ℓ) Γ₁ e).app_pullback σ₁.op σ₂ ρ))
    (fun σ₃ name Y y hy hne => ?_) s (X.pullback σ₂)).symm
  simpa using hsupport (σ₃ ≫ σ₂) name Y (by simpa using hy) hne

theorem HasEquality.eta
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (htI' : HasIdeality (Γ₁.extension ht) t')
    (he : E[Γ₁.as.ctx] ⊢ₛ e : .forallE t t')
    (hEI : HasIdeality Γ₁ e) (hEF : HasFixedness Γ₁ e (.forallE t t'))
    (hER : HasSubstitution Γ₁ e) :
    HasEquality Γ₁ (.lam t (.app e.wk (.var (Fin.last Γ₁.as.len)))) e := by
  intro Γ₂ σ₁ ρ hρ
  let C := rawInterpret (piLimit E ℓ) Γ₁ t
  let N := rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) t'
  let Eb := rawInterpret (piLimit E ℓ) (CtxCat.extension Γ₁ ht) (.app e.wk (.var (Fin.last Γ₁.as.len)))
  let T := hρ.eval htI
  let Vraw := RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C N σ₁ ρ
  have hV : Vraw.IsFinitary := RawFamily.normalizedBodyAction_isFinitary (piLimit E ℓ) (CtxCat.rawComprehension ht) C
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') σ₁ ρ
  let V := Vraw.toIdealAction hV (HasIdeality.bodyAction ht htI htI' σ₁ ρ hρ)
  let F := hρ.eval hEI
  let label := Ty.pairOfTyping Γ₁.as ht ht'
  let n := (Tm E ℓ).map σ₁.op (Tm.label Γ₁.as he)
  have hfixed : (piLimit E ℓ).rawExtend ((RawFamily.pi (piLimit E ℓ) (CtxCat.rawComprehension ht) label C N).app _ σ₁.op ρ)
      n F.val = F.val := by
    have h := hEF he σ₁ ρ hρ
    rwa [rawInterpret_forallE (piLimit E ℓ) ht ht'] at h
  have hF : IdealAction.abstraction
      ((piLimit E ℓ).piBody ((Ty.pairPresheaf E ℓ).map σ₁.op label) n T V F) = F := by
    have h := CodeAssignment.piAction_fixed_of_rawExtend_rawPi
      ((Ty.pairPresheaf E ℓ).map σ₁.op label) T Vraw hV (HasIdeality.bodyAction ht htI htI' σ₁ ρ hρ) n hfixed
    rwa [piAction_app_id] at h
  let K := (piLimit E ℓ).piBody ((Ty.pairPresheaf E ℓ).map σ₁.op label) n T V F
  let U := RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C Eb σ₁ ρ
  have hsupport {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
      (X : Domain Γ₃) {y : CoherentShape Γ₃}
      (hy : (application (F.pullback σ₂) name X).mem (𝟙 Γ₃) y)
      (hne : ¬ y ≤ ⊥) :
      Nonempty (Raw.ContextSection ht (σ₂ ≫ σ₁) name) :=
    RawFamily.application_rawPi_fixed_support ht label C
      (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') σ₁ ρ (htI σ₁ ρ hρ)
      (HasIdeality.bodyAction ht htI htI' σ₁ ρ hρ) n hfixed σ₂ name X hy hne
  have hvalues {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
      (X : Domain Γ₃) :
      U.app _ (σ₂.op, name) X.val = (K.val.app _ (σ₂.op, name) X).val := by
    let Y := (piLimit E ℓ).extend (T.pullback σ₂) name X
    have hY : (piLimit E ℓ).extend (T.pullback σ₂) name Y = Y :=
      (piLimit E ℓ).extend_idempotent piLimit_isIdempotent _ _ _
    have hK : K.val.app _ (σ₂.op, name) X = application (F.pullback σ₂) name Y := by
      have h := (piLimit E ℓ).application_eq_of_piBody_fixed _ n T V hF σ₂ name Y
      rw [hY] at h
      exact h.symm
    have hhead : (piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name X.val =
        Y.val := by
      change (piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name X.val =
        ((piLimit E ℓ).extend (T.pullback σ₂) name X).val
      rw [← (piLimit E ℓ).rawExtend_toLower]
      exact congrArg (fun I : RawValue Γ₃ ↦ (piLimit E ℓ).rawExtend I name X.val)
        (C.app_pullback σ₁.op σ₂ ρ).symm
    change RawFamily.sectionValue (CtxCat.rawComprehension ht) Eb (σ₂ ≫ σ₁) (ρ.pullback σ₂) name
      ((piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name X.val) = _
    rw [hhead, hK]
    exact eta_sectionValue ht hER (σ₂ ≫ σ₁) (ρ.pullback σ₂) (hρ.pullback σ₂) (F.pullback σ₂)
      ((rawInterpret (piLimit E ℓ) Γ₁ e).app_pullback σ₁.op σ₂ ρ)
      (fun σ₃ name' Z y hy hne => by simpa using hsupport (σ₃ ≫ σ₂) name' Z (by simpa using hy) hne)
      _ _
  rw [rawInterpret_lam (piLimit E ℓ) ht]
  exact (U.abstraction_eq_of_ideal_values K hvalues).trans (congrArg Subtype.val hF)

theorem RawInterpretationProperties.app (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (ht' : E[Γ₁.as.ctx.snoc t] ⊢ₛ t' : .sort v) (htI : HasIdeality Γ₁ t)
    (htI' : HasIdeality (Γ₁.extension ht) t')
    (he₁ : E[Γ₁.as.ctx] ⊢ₛ e₁ : t) (hf : E[Γ₁.as.ctx] ⊢ₛ f : .forallE t t')
    (pf : RawInterpretationProperties Γ₁ f) (pe : RawInterpretationProperties Γ₁ e₁)
    (hfF : HasFixedness Γ₁ f (.forallE t t')) : RawInterpretationProperties Γ₁ (.app f e₁) where
  ideal _ σ ρ hρ := by
    rw [HasIdeality.application_value ht ht' htI htI' he₁ hf pf.ideal pe.ideal hfF σ ρ hρ]
    exact (application ..).property
  subst := HasSubstitution.app ht ht' he₁ htI htI' pf.ideal pe.ideal hf hfF pf.subst pe.subst

theorem RawJudgment.appDF (pt : RawJudgment Γ₁ t t (.sort u)) :
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) t' t' (.sort v) →
    RawJudgment Γ₁ f f' (.forallE t t') →
    RawJudgment Γ₁ e₁ e₂ t →
    RawJudgment Γ₁ (t'.inst e₁) (t'.inst e₂) (.sort v) →
    RawJudgment Γ₁ (.app f e₁) (.app f' e₂) (t'.inst e₁) := by
  intro pt' pf pe pResult
  have ht := pt.syntactic
  have ht' := pt'.syntactic
  have he₁ := pe.syntactic.left
  have hf := pf.syntactic.left
  refine ⟨.appDF ht ht' pf.syntactic pe.syntactic pResult.syntactic, pResult.left,
    .app ht ht' pt.left.ideal pt'.left.ideal he₁ hf pf.left pe.left pf.fixed,
    .app ht ht' pt.left.ideal pt'.left.ideal pe.syntactic.right pf.syntactic.right pf.right pe.right
      pf.fixed_right, fun _ σ ρ hρ => ?_, fun _ happ σ ρ hρ => ?_⟩
  · rw [HasIdeality.application_value ht ht' pt.left.ideal pt'.left.ideal he₁ hf pf.left.ideal
        pe.left.ideal pf.fixed σ ρ hρ,
      HasIdeality.application_value ht ht' pt.left.ideal pt'.left.ideal pe.syntactic.right
        pf.syntactic.right pf.right.ideal pe.right.ideal pf.fixed_right σ ρ hρ,
      Tm.label_eq (IsTypeEq.ofDefEq ht) pe.syntactic, HasEquality.eval pf.equal hρ pf.left.ideal pf.right.ideal,
      HasEquality.eval pe.equal hρ pe.left.ideal pe.right.ideal]
  have hpi : Tm.type (Tm.label Γ₁.as hf) =
      Ty.piApp (Ty.pairOfTyping Γ₁.as ht ht').1 (Ty.pairOfTyping Γ₁.as ht ht').2 :=
    (Ty.piApp_eq_ofRepr _ _ ⟨_, u, ht⟩ (CtxCat.rawComprehension_type ht) ⟨_, v, ht'⟩
      (Ty.eval_familyOfTyping Γ₁.as ht ht').symm).symm
  have hdom : Tm.type (Tm.label Γ₁.as he₁) =
      yonedaEquiv (Ty.pairOfTyping Γ₁.as ht ht').1 := (CtxCat.rawComprehension_type ht).symm
  have hguard : Tm.type ((Tm E ℓ).map σ.op (Tm.label Γ₁.as hf)) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).1
        ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).2 := by
    rw [Tm.type_map, hpi, Ty.piApp_pairPresheaf_map]
  have hguardDom : Tm.type ((Tm E ℓ).map σ.op (Tm.label Γ₁.as he₁)) =
      yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).1 := by
    rw [Tm.type_map, hdom]
    change _ = yonedaEquiv (yoneda.map σ ≫ (Ty.pairOfTyping Γ₁.as ht ht').1)
    rw [← yonedaEquiv_naturality]
  have hclass : Tm.apply ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).1
        ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')).2
        ((Tm E ℓ).map σ.op (Tm.label Γ₁.as hf))
        ((Tm E ℓ).map σ.op (Tm.label Γ₁.as he₁)) hguard hguardDom =
      (Tm E ℓ).map σ.op (Tm.label Γ₁.as happ) :=
    (Tm.map_apply (Ty.pairOfTyping Γ₁.as ht ht').1 (Ty.pairOfTyping Γ₁.as ht ht').2 _ _ hpi hdom σ
      hguard hguardDom).symm.trans (congrArg ((Tm E ℓ).map σ.op)
        (Tm.apply_label Γ₁.as ht ht' hf he₁ (DefeqStrong.inst_congr ht' he₁) hpi hdom))
  have hresult := HasIdeality.application_fixed ht ht' pt.left.ideal pt'.left.ideal σ ρ hρ
    ((Raw.ContextSection.ofTerm ht he₁).pullbackId σ)
    ((Tm E ℓ).map σ.op (Tm.label Γ₁.as hf))
    (F := hρ.eval pf.left.ideal) (X := hρ.eval pe.left.ideal) (pf.fixed hf σ ρ hρ)
    (pe.fixed he₁ σ ρ hρ) hguard hguardDom
  rwa [← HasSubstitution.instantiate ht he₁ pt.left.ideal pe.left.ideal pe.fixed pe.left.subst
    pt'.left.subst σ ρ hρ, HasIdeality.application_value ht ht' pt.left.ideal pt'.left.ideal he₁ hf
      pf.left.ideal pe.left.ideal pf.fixed σ ρ hρ, ← hclass]

theorem RawJudgment.beta {e : Expr ζ ℓ Γ₁.as.len} {e' : Expr ζ ℓ (Γ₁.as.len + 1)}
    (pt : RawJudgment Γ₁ t t (.sort u)) :
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) t' t' (.sort v) →
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) e' e' t' →
    RawJudgment Γ₁ e e t →
    RawJudgment Γ₁ (t'.inst e) (t'.inst e) (.sort v) →
    RawJudgment Γ₁ (e'.inst e) (e'.inst e) (t'.inst e) →
    RawJudgment Γ₁ (.app (.lam t e') e) (e'.inst e) (t'.inst e) := by
  intro pt' pe' pe pResult pInst
  exact of_typings (.beta pt.syntactic pt'.syntactic pe'.syntactic pe.syntactic pResult.syntactic
      pInst.syntactic)
    (appDF pt pt' (lamDF pt pt' pe' pe') pe pResult) pInst
    (HasEquality.beta pt.syntactic pe.syntactic pt.left.ideal pe'.left.ideal pe.left.ideal pe.fixed
      pe.left.subst pe'.left.subst)

def CtxCat.wkFromRaw (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (htw : E[Γ₁.as.ctx.snoc t] ⊢ₛ t.wk : .sort v) :
    (CtxCat.extension (CtxCat.extension Γ₁ ht) htw).as ⟶ (CtxCat.extension Γ₁ ht).as where
  subst := Subst.wkFrom Γ₁.as.len
  typed := by
    rw [Subst.wkFrom_eq_lift_wk]
    simpa [Expr.subst_wk] using SubstWFStrong.lift ⟨u, ht⟩ (SubstWFStrong.wk t Γ₁.as.wf)

theorem RawJudgment.eta (pt : RawJudgment Γ₁ t t (.sort u))
    (hR : RawTeleProperties E .nil (CtxCat.extension Γ₁ pt.syntactic).as.ctx) :
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) t' t' (.sort v) →
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) t.wk t.wk (.sort u) →
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) e.wk e.wk
      (.forallE t.wk (t'.wkFrom Γ₁.as.len)) →
    RawJudgment Γ₁ e e (.forallE t t') →
    RawJudgment Γ₁ (.lam t (.app e.wk (.var (Fin.last Γ₁.as.len)))) e (.forallE t t') := by
  intro pt' ptw pew pe
  have hσ := SemanticHom.ofImages (CtxCat.extension Γ₁ pt.syntactic).as.wf hR
    (CtxCat.wkFromRaw pt.syntactic ptw.syntactic)
    (fun w => .var (CtxCat.extension (CtxCat.extension Γ₁ pt.syntactic) ptw.syntactic)
      (Ren.wkFrom Γ₁.as.len w)) fun w => by
      have h : HasFixedness (CtxCat.extension (CtxCat.extension Γ₁ pt.syntactic) ptw.syntactic)
          (.var (Ren.wkFrom Γ₁.as.len w))
          ((Γ₁.as.ctx.insert t (#t[].snoc t)).get (Ren.wkFrom Γ₁.as.len w)) :=
        HasFixedness.var _ (hR.extension _ ptw.left) _
      rwa [Ctx.get_insert, Expr.wkFrom_eq_subst] at h
  have pw := hσ.props pt'.left
  have fw : HasFixedness _ _ _ :=
    hσ.fixed pt'.syntactic.left (HasSubstitution.sort _ v) pt'.left.subst pt'.fixed
  have hw := pt'.syntactic.left.substitution (CtxCat.wkFromRaw pt.syntactic ptw.syntactic).typed
  rw [show t'.subst (CtxCat.wkFromRaw pt.syntactic ptw.syntactic).subst = t'.wkFrom Γ₁.as.len from
    Expr.subst_vars _ _] at pw fw hw
  have pvar : RawJudgment (CtxCat.extension Γ₁ pt.syntactic) (.var (Fin.last Γ₁.as.len))
      (.var (Fin.last Γ₁.as.len))
      ((CtxCat.extension Γ₁ pt.syntactic).as.ctx.get (Fin.last Γ₁.as.len)) :=
    RawJudgment.var hR (by rwa [Ctx.get_last])
  rw [Ctx.get_last] at pvar
  have pbody := appDF ptw ⟨hw, .sort _ v, pw, pw, HasEquality.refl _ _, fw⟩ pew pvar
    (by rwa [Expr.inst_wkFrom_last])
  rw [Expr.inst_wkFrom_last] at pbody
  exact of_typings (.eta pt.syntactic pt'.syntactic ptw.syntactic pew.syntactic pe.syntactic)
    (lamDF pt pt' pbody pbody) pe
    (HasEquality.eta pt.syntactic pt'.syntactic pt.left.ideal pt'.left.ideal pe.syntactic.left
      pe.left.ideal pe.fixed pe.left.subst)

end Metalean.CoherentShape
