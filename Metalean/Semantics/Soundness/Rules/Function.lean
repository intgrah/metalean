/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
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

open CategoryTheory CodeAssignment Presheaf TypeTheory NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {t t₁ t₂ e e₁ e₂ f f' : Expr ζ ℓ Γ₁.as.len}
  {t' t₁' t₂' e' e₁' e₂' : Expr ζ ℓ (Γ₁.as.len + 1)} {u v : Level ℓ}

namespace HasSubstitution

theorem binder_body (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (htI : HasIdeality Γ₁ t)
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
    rw [s.over]
    exact hσ₁.pullback σ₃
  have htest := SemanticSubstitution.lift ht σ₁ s.hom (ρs.pullback σ₃)
    ((ρt.pullback σ₃).push J.val) htail
  exact (he'
    (σ₁.lift ⟨u, ht⟩) s.hom ((ρs.pullback σ₃).push J.val)
    ((ρt.pullback σ₃).push J.val) htest hhead).symm

theorem lam (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (htI : HasIdeality Γ₁ t)
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

theorem forallE (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (hts : HasSubstitution Γ₁ t)
    (hts' : HasSubstitution (CtxCat.extension Γ₁ ht) t') :
    HasSubstitution Γ₁ (.forallE t t') := by
  intro Γ₂ Γ₃ σ₁ σ₂ ρs ρt hσ₁ hρ
  have htσ' : E[Γ₂.as.ctx.snoc (t.subst σ₁.subst)] ⊢ t'.subst σ₁.subst.lift : .sort v :=
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

theorem piLimit_rawExtend_sort_le (r : Level ℓ) (n : Tm_ Γ₁)
    {I : RawValue Γ₁} :
    (piLimit E ℓ).rawExtend (ΩLower.principal (pointedOrder E ℓ) (sortAtom r)) n I ≤ I :=
  fun σ y hy => ((mem_piLimit_rawExtend_sort_iff r I n σ y).mp hy).1

theorem SourceAdmissible.push_fixed_pullback (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u) (htI : HasIdeality Γ₁ t₁)
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

theorem HasIdeality.forallE (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u) (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ t₁' : .sort v)
    (htI : HasIdeality Γ₁ t₁) (htI' : HasIdeality (CtxCat.extension Γ₁ ht₁) t₁') :
    HasIdeality Γ₁ (.forallE t₁ t₁') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht₁ ht₁']
  exact rawPi_isDirected _ _ (htI σ ρ hρ) (RawFamily.bodyAction_isIdealValued ht₁ htI htI' σ ρ hρ)

theorem HasIdeality.lam (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u) (htI : HasIdeality Γ₁ t₁)
    (heI' : HasIdeality (CtxCat.extension Γ₁ ht₁) e₁') : HasIdeality Γ₁ (.lam t₁ e₁') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_lam (piLimit E ℓ) ht₁]
  exact RawAction.abstraction_isDirected _ (RawFamily.bodyAction_isIdealValued ht₁ htI heI' σ ρ hρ)

theorem HasFixedness.forallE (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u)
    (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ t₁' : .sort v)
    (htI : HasIdeality Γ₁ t₁) (htsort' : HasFixedness (CtxCat.extension Γ₁ ht₁) t₁' (.sort v)) :
    HasFixedness Γ₁ (.forallE t₁ t₁') (.sort (.imax u v)) := by
  intro Γ₂ _ σ₁ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht₁ ht₁', rawInterpret_sort]
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
        rw [(piLimit E ℓ).pullback_rawExtend, S.pullback_extend σ₃ s]
        have h := htsort' ht₁' s.hom _
          ((hρ.pullback σ₂).push_fixed_pullback ht₁ htI J hJ σ₃ s)
        rw [rawInterpret_sort] at h
        exact Eq.trans (ΩLower.ext fun σ z => (mem_piLimit_rawExtend_sort_iff v _ _ σ z).trans
          (mem_piLimit_rawExtend_sort_iff v _ _ σ z).symm) h
    have hmem := hf i
    change (RawFamily.sectionValue (CtxCat.rawComprehension ht₁) T (σ₂ ≫ σ₁) (ρ.pullback σ₂) (f.names i)
      J.val).mem (𝟙 Γ₃) _ at hmem
    rw [RawFamily.sectionValue, ← hsort] at hmem
    have ⟨_, hcode⟩ := (mem_piLimit_rawExtend_sort_iff _ _ _ _ _).mp hmem
    rwa [hv] at hcode

theorem Tm.section_label (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u)
    (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ t₁' : .sort v) (he₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ e₁' : t₁')
    {σ : Γ₂ ⟶ Γ₁} {m : Tm_ Γ₂} (s : Raw.ContextSection ht₁ σ m) :
    (Tm E ℓ).map s.hom.op (Tm.label (CtxCat.extension Γ₁ ht₁).as he₁') =
      Tm.apply ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht₁ ht₁'))
        ((Tm E ℓ).map σ.op (Tm.label Γ₁.as (.lamDF ht₁ ht₁' ht₁' he₁' he₁'))) m
        (by rw [Tm.type_map, Ty.piApp_pairPresheaf_map]
            exact congrArg ((Ty E ℓ).map σ.op) (Ty.piApp_ofTyping Γ₁.as ht₁ ht₁').symm)
        (s.type_eq.trans (yonedaEquiv_naturality _ σ)) := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  have hlift := SubstWF.lift ⟨u, ht₁⟩ σ.typed
  have htσ := ht₁.substitution σ.typed
  have htσ' := ht₁'.substitution hlift
  have heσ' := he₁'.substitution hlift
  obtain ⟨a, harg, rfl⟩ := Tm.exists_label m ⟨_, _, htσ⟩ (by
    have hm := s.type_eq
    simp only [Equiv.apply_symm_apply] at hm
    exact hm)
  rw [Section.hom_eq s (Raw.ContextSection.ofTyping ht₁ σ harg)]
  refine (Tm.map_label he₁' (σ.snoc ⟨u, ht₁⟩ harg)).trans ?_
  simp only [Ty.pairPresheaf_map_ofTyping ht₁ ht₁' σ,
    Tm.map_label (.lamDF ht₁ ht₁' ht₁' he₁' he₁') σ]
  refine Eq.trans (Tm.label_eq ?_ ?_)
    (Tm.apply_label Γ₂.as htσ htσ' (.lamDF htσ htσ' htσ' heσ' heσ') harg).symm
  · simpa [RawCtx.Hom.snoc_subst, Expr.inst_subst_lift] using
      TypeEq.ofDefEq (Defeq.inst_congr htσ' harg)
  · simpa [RawCtx.Hom.snoc_subst, Expr.inst_subst_lift] using
      (Defeq.beta htσ htσ' heσ' harg (Defeq.inst_congr htσ' harg) (Defeq.inst_congr heσ' harg)).symm

theorem HasFixedness.lam (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u) (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ t₁' : .sort v)
    (he₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ e₁' : t₁')
    (htI : HasIdeality Γ₁ t₁) (htI' : HasIdeality (CtxCat.extension Γ₁ ht₁) t₁')
    (heI' : HasIdeality (CtxCat.extension Γ₁ ht₁) e₁')
    (heF' : HasFixedness (CtxCat.extension Γ₁ ht₁) e₁' t₁') :
    HasFixedness Γ₁ (.lam t₁ e₁') (.forallE t₁ t₁') := by
  intro Γ₂ _ σ₁ ρ hρ
  rw [rawInterpret_lam (piLimit E ℓ) ht₁, rawInterpret_forallE (piLimit E ℓ) ht₁ ht₁',
    RawFamily.pi_value]
  refine RawFamily.normalizedAbstraction_fixed ht₁ _ _ _
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht₁) t₁')
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht₁) e₁') σ₁ ρ _
    (by
      change yonedaEquiv (yoneda.map σ₁ ≫ (CtxCat.rawComprehension ht₁).type) = _
      rw [← yonedaEquiv_naturality, CtxCat.rawComprehension_type]) _ ?_ (htI σ₁ ρ hρ)
    (RawFamily.bodyAction_isIdealValued ht₁ htI htI' σ₁ ρ hρ) (RawFamily.bodyAction_isIdealValued ht₁ htI heI' σ₁ ρ hρ) ?_
  · rw [Tm.type_map, Ty.piApp_pairPresheaf_map]
    exact congrArg ((Ty E ℓ).map σ₁.op)
      (Ty.piApp_ofTyping Γ₁.as ht₁ ht₁').symm
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
    rw [Tm.map_apply _ _ _ hguard hmguard σ₃]
    simpa [op_comp, Functor.map_comp_apply] using Tm.section_label ht₁ ht₁' he₁' t

namespace HasEquality

theorem normalizedBodyAction_contextConversion
    (ht : E[Γ₁.as.ctx] ⊢ t₁ ≡ t₂ : .sort u) (htI : HasIdeality Γ₁ t₁)
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
  let S := RawFamily.bodySection (CtxCat.rawComprehension ht.left)
    (rawInterpret (piLimit E ℓ) (Γ₁.extension ht.left) e₁') (σ₂ ≫ σ₁) (ρ.pullback σ₂) label J.val
  refine PartialSection.eq_extend _ S.extend (fun σ₃ y hy hne => ?_) fun σ₃ s => ?_
  · have ⟨s⟩ := S.support hy hne
    exact ⟨Raw.ContextSection.convert ht.symm s⟩
  · rw [S.pullback_extend σ₃ (Raw.ContextSection.convert ht s)]
    have hadm := (hρ.pullback σ₂).push_fixed_pullback ht.left htI J hJ σ₃
      (Raw.ContextSection.convert ht s)
    have h := he₂' (CtxCat.contextConversionRaw (.ofDefEq ht) ht.left ht.right) s.hom _ _
      (.ren (fun v => ⟨v, rfl⟩) (.of_var id (fun _ => rfl) fun _ => rfl)) hadm
    rw [show (CtxCat.contextConversionRaw (.ofDefEq ht) ht.left ht.right).subst = Subst.id from rfl,
      Expr.subst_id] at h
    exact (he' _ _ hadm).trans h.symm

theorem lam (ht : E[Γ₁.as.ctx] ⊢ t₁ ≡ t₂ : .sort u) (htI : HasIdeality Γ₁ t₁)
    (hteq : HasEquality Γ₁ t₁ t₂)
    (he' : HasEquality (CtxCat.extension Γ₁ ht.left) e₁' e₂')
    (he₂' : HasSubstitution (CtxCat.extension Γ₁ ht.left) e₂') :
    HasEquality Γ₁ (.lam t₁ e₁') (.lam t₂ e₂') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_lam (piLimit E ℓ) ht.left, rawInterpret_lam (piLimit E ℓ) ht.right]
  exact RawAction.abstraction_eq_of_eq_on_ideals (normalizedBodyAction_contextConversion ht htI hteq he' he₂' σ ρ hρ)

theorem forallE (ht : E[Γ₁.as.ctx] ⊢ t₁ ≡ t₂ : .sort u)
    (ht' : E[Γ₁.as.ctx.snoc t₁] ⊢ t₁' ≡ t₂' : .sort v)
    (ht₂' : E[Γ₁.as.ctx.snoc t₂] ⊢ t₁' ≡ t₂' : .sort v)
    (htI : HasIdeality Γ₁ t₁) (hteq : HasEquality Γ₁ t₁ t₂)
    (hteq' : HasEquality (CtxCat.extension Γ₁ ht.left) t₁' t₂')
    (htR' : HasSubstitution (CtxCat.extension Γ₁ ht.left) t₂') :
    HasEquality Γ₁ (.forallE t₁ t₁') (.forallE t₂ t₂') := by
  intro Γ₂ σ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht.left ht'.left,
    rawInterpret_forallE (piLimit E ℓ) ht.right ht₂'.right, RawFamily.pi_value,
    Ty.pairOfTyping_congr Γ₁.as ht ht', hteq σ ρ hρ]
  exact rawPi_eq_of_eq_on_ideals _ _
    (normalizedBodyAction_contextConversion ht htI hteq hteq' htR' σ ρ hρ)

end HasEquality

theorem RawInterpretationProperties.forallE (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u)
    (ht₁' : E[Γ₁.as.ctx.snoc t₁] ⊢ t₁' : .sort v)
    (pt : RawInterpretationProperties Γ₁ t₁) (pt' : RawInterpretationProperties (CtxCat.extension Γ₁ ht₁) t₁') :
    RawInterpretationProperties Γ₁ (.forallE t₁ t₁') where
  ideal := HasIdeality.forallE ht₁ ht₁' pt.ideal pt'.ideal
  subst := HasSubstitution.forallE ht₁ ht₁' pt.ideal pt.subst pt'.subst

theorem RawInterpretationProperties.lam (ht₁ : E[Γ₁.as.ctx] ⊢ t₁ : .sort u)
    (pt : RawInterpretationProperties Γ₁ t₁) (pe₁' : RawInterpretationProperties (CtxCat.extension Γ₁ ht₁) e₁') :
    RawInterpretationProperties Γ₁ (.lam t₁ e₁') where
  ideal := HasIdeality.lam ht₁ pt.ideal pe₁'.ideal
  subst := HasSubstitution.lam ht₁ pt.ideal pt.subst pe₁'.subst

theorem RawTyped.lam (ht : E[Γ₁.as.ctx] ⊢ t : .sort u)
    (pt : RawInterpretationProperties Γ₁ t)
    (pb : RawTyped (Γ₁.extension ht) e₁' t₁') :
    RawTyped Γ₁ (.lam t e₁') (.forallE t t₁') := by
  obtain ⟨v, ht'⟩ := pb.typed.regular
  exact ⟨.lamDF ht ht' ht' pb.typed pb.typed, .forallE ht ht' pt pb.type,
    .lam ht pt pb.term, .lam ht ht' pb.typed pt.ideal pb.type.ideal pb.term.ideal pb.fixed⟩

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

theorem HasEquality.eta
    (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (ht' : E[Γ₁.as.ctx.snoc t] ⊢ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (htI' : HasIdeality (Γ₁.extension ht) t')
    (he : E[Γ₁.as.ctx] ⊢ e : .forallE t t')
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
  let V := Vraw.toIdealAction hV (RawFamily.bodyAction_isIdealValued ht htI htI' σ₁ ρ hρ)
  let F := hρ.eval hEI
  let label := Ty.pairOfTyping Γ₁.as ht ht'
  let n := (Tm E ℓ).map σ₁.op (Tm.label Γ₁.as he)
  have hfixed := hEF he σ₁ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht ht'] at hfixed
  have hF := CodeAssignment.piAction_fixed_of_rawExtend_rawPi (F := F)
    ((Ty.pairPresheaf E ℓ).map σ₁.op label) T Vraw hV
    (RawFamily.bodyAction_isIdealValued ht htI htI' σ₁ ρ hρ) n hfixed
  rw [piAction_app_id] at hF
  let K := (piLimit E ℓ).piBody ((Ty.pairPresheaf E ℓ).map σ₁.op label) n T V F
  let U := RawFamily.normalizedBodyAction (piLimit E ℓ) (CtxCat.rawComprehension ht) C Eb σ₁ ρ
  have hsupport {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
      (X : Domain Γ₃) {y : CoherentShape Γ₃}
      (hy : (application (F.pullback σ₂) name X).mem (𝟙 Γ₃) y)
      (hne : ¬ y ≤ ⊥) :
      Nonempty (Raw.ContextSection ht (σ₂ ≫ σ₁) name) :=
    RawFamily.application_rawPi_fixed_support ht label C
      (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') σ₁ ρ (htI σ₁ ρ hρ)
      (RawFamily.bodyAction_isIdealValued ht htI htI' σ₁ ρ hρ) n hfixed σ₂ name X hy hne
  have hsection {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (label : Tm_ Γ₃) (X : Domain Γ₃) :
      RawFamily.sectionValue (CtxCat.rawComprehension ht) Eb (σ₂ ≫ σ₁) (ρ.pullback σ₂)
        label X.val = (application (F.pullback σ₂) label X).val := by
    refine (PartialSection.eq_extend _ _ (fun σ₃ y hy hne => ?_)
      fun σ₃ (s : Raw.ContextSection ht (σ₃ ≫ (σ₂ ≫ σ₁)) ((Tm E ℓ).map σ₃.op label)) => ?_).symm
    · have h := hsupport (σ₃ ≫ σ₂) _ (X.pullback σ₃)
        (by simpa using (ΩIdeal.presheaf_map_mem_id (application (F.pullback σ₂) label X) σ₃ y).mpr hy) hne
      rw [Category.assoc] at h
      exact h
    change ((application (F.pullback σ₂) label X).pullback σ₃).val = _
    rw [pullback_application]
    symm
    dsimp only [RawFamily.bodySection, Eb]
    have hvar := CtxWF.varLast (Γ₁.as.wf.snoc ⟨u, ht⟩)
    rw [← Expr.subst_wk] at hvar
    rw [rawInterpret_app, RawFamily.application_value, rawInterpret_var, Var.db_last,
      HasSubstitution.wk_value ht hER s.hom _ (by rw [s.over]; exact (hρ.pullback σ₂).pullback σ₃),
      s.over, RawValuation.tail_push]
    rw [op_comp, ← RawFamily.app_pullback, op_comp, ← RawFamily.app_pullback]
    refine (RawFamily.rawApplication_eq_of_sections
      (ht.substitution (CtxCat.projectionRaw Γ₁ ht).typed) hvar s.hom
      ((F.pullback σ₂).pullback σ₃) (X.pullback σ₃) fun {_} σ₄ name {x y} hy => ?_).trans ?_
    · by_cases hbottom : y ≤ ⊥
      · exact Or.inl hbottom
      have ⟨r⟩ := hsupport (σ₄ ≫ σ₃ ≫ σ₂) name (principalIdeal x)
        (by simpa using hy.mem_application ((principalIdeal_mem x (𝟙 _) x).mpr (by simp))) hbottom
      exact Or.inr ⟨Raw.ContextSection.cartesianLift ht (CtxCat.projectionRaw Γ₁ ht)
        ⟨r.hom, by
          have ho := r.over
          simp only [Category.assoc] at ho
          exact ho.trans ((congr(σ₄ ≫ $(s.over))).symm.trans (Category.assoc ..).symm), r.generic⟩⟩
    · rw [Tm.label_eq_var hvar rfl]
      exact congrArg (fun n => (application ((F.pullback σ₂).pullback σ₃) n (X.pullback σ₃)).val) s.generic
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
      exact congrArg (fun I : RawValue Γ₃ ↦ (piLimit E ℓ).rawExtend I name X.val)
        (C.app_pullback σ₁.op σ₂ ρ).symm
    change RawFamily.sectionValue (CtxCat.rawComprehension ht) Eb (σ₂ ≫ σ₁) (ρ.pullback σ₂) name
      ((piLimit E ℓ).rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) name X.val) = _
    rw [hhead, hK]
    exact hsection σ₂ name Y
  rw [rawInterpret_lam (piLimit E ℓ) ht]
  exact (U.abstraction_eq_of_ideal_values K hvalues).trans (congrArg Subtype.val hF)

theorem RawInterpretationProperties.app (ht : E[Γ₁.as.ctx] ⊢ t : .sort u)
    (ht' : E[Γ₁.as.ctx.snoc t] ⊢ t' : .sort v)
    (htI : HasIdeality Γ₁ t) (htI' : HasIdeality (Γ₁.extension ht) t')
    (pf : RawTyped Γ₁ f (.forallE t t')) (pe : RawInterpretationProperties Γ₁ e₁)
    (he : E[Γ₁.as.ctx] ⊢ e₁ : t) :
    RawInterpretationProperties Γ₁ (.app f e₁) ∧
    ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ),
      (rawInterpret (piLimit E ℓ) Γ₁ (.app f e₁)).app _ σ.op ρ =
        (application (hρ.eval pf.term.ideal) ((Tm E ℓ).map σ.op (Tm.label Γ₁.as he))
          (hρ.eval pe.ideal)).val := by
  have hvalue {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
      (hρ : SourceAdmissible σ ρ) :
      (rawInterpret (piLimit E ℓ) Γ₁ (.app f e₁)).app _ σ.op ρ =
        (application (hρ.eval pf.term.ideal) ((Tm E ℓ).map σ.op (Tm.label Γ₁.as he))
          (hρ.eval pe.ideal)).val := by
    have hF := pf.fixed pf.typed σ ρ hρ
    rw [rawInterpret_forallE (piLimit E ℓ) ht ht'] at hF
    rw [rawInterpret_app]
    exact RawFamily.rawApplication_eq_of_sections ht he σ
      (hρ.eval pf.term.ideal) (hρ.eval pe.ideal) fun σ₂ _ _ _ hy =>
      RawFamily.outputAtom_rawPi_fixed_bot_or_section ht _ (rawInterpret (piLimit E ℓ) Γ₁ t)
        (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') σ ρ (htI σ ρ hρ)
        (RawFamily.bodyAction_isIdealValued ht htI htI' σ ρ hρ) _ hF σ₂ hy
  refine ⟨⟨?_, ?_⟩, hvalue⟩
  · intro Γ₂ σ ρ hρ
    rw [hvalue σ ρ hρ]
    exact (application ..).property
  · exact fun _ _ σ₁ σ₂ ρs ρt hσ₁ hρ => rawInterpret_app_subst ht ht' he σ₁ σ₂ ρs ρt
      (htI _ _ hρ) (RawFamily.bodyAction_isIdealValued ht htI htI' _ _ hρ)
      (pf.term.ideal _ _ hρ) (pe.ideal _ _ hρ) _ (pf.fixed pf.typed _ _ hρ)
      (pf.term.subst σ₁ σ₂ ρs ρt hσ₁ hρ) (pe.subst σ₁ σ₂ ρs ρt hσ₁ hρ)

theorem RawTyped.app (ht : E[Γ₁.as.ctx] ⊢ t : .sort u)
    (ht' : E[Γ₁.as.ctx.snoc t] ⊢ t' : .sort v)
    (pt' : RawInterpretationProperties (Γ₁.extension ht) t')
    (pf : RawTyped Γ₁ f (.forallE t t')) (pe : RawTyped Γ₁ e₁ t)
    (pr : RawInterpretationProperties Γ₁ (t'.inst e₁)) :
    RawTyped Γ₁ (.app f e₁) (t'.inst e₁) ∧
    ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ),
      (rawInterpret (piLimit E ℓ) Γ₁ (.app f e₁)).app _ σ.op ρ =
        (application (hρ.eval pf.term.ideal) ((Tm E ℓ).map σ.op (Tm.label Γ₁.as pe.typed))
          (hρ.eval pe.term.ideal)).val := by
  have ⟨papp, hvalue⟩ := RawInterpretationProperties.app ht ht' pe.type.ideal pt'.ideal pf pe.term pe.typed
  refine ⟨⟨.appDF ht ht' pf.typed pe.typed (ht'.inst_congr pe.typed), pr, papp,
    fun Γ₂ happ σ ρ hρ => ?_⟩, hvalue⟩
  have hf := pf.typed
  have he₁ := pe.typed
  have hpi : Tm.type (Tm.label Γ₁.as hf) =
      Ty.piApp (Ty.pairOfTyping Γ₁.as ht ht').1 (Ty.pairOfTyping Γ₁.as ht ht').2 :=
    (Ty.piApp_ofTyping Γ₁.as ht ht').symm
  have hdom : Tm.type (Tm.label Γ₁.as he₁) =
      yonedaEquiv (Ty.pairOfTyping Γ₁.as ht ht').1 := (CtxCat.rawComprehension_type ht).symm
  have hF := pf.fixed hf σ ρ hρ
  rw [rawInterpret_forallE (piLimit E ℓ) ht ht'] at hF
  have elabel : (Ty.pairPresheaf E ℓ).map (𝟙 Γ₂).op
      ((Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht')) =
      (Ty.pairPresheaf E ℓ).map σ.op (Ty.pairOfTyping Γ₁.as ht ht') := by simp
  have hresult := RawFamily.application_rawPi_fixed (F := hρ.eval pf.term.ideal)
    ht (Ty.pairOfTyping Γ₁.as ht ht') (rawInterpret (piLimit E ℓ) Γ₁ t)
    (rawInterpret_isFinitary (piLimit E ℓ) (Γ₁.extension ht) t') σ ρ (pe.type.ideal σ ρ hρ)
    (RawFamily.bodyAction_isIdealValued ht pe.type.ideal pt'.ideal σ ρ hρ)
    ((Tm E ℓ).map σ.op (Tm.label Γ₁.as hf)) hF (𝟙 _) ((Tm E ℓ).map σ.op (Tm.label Γ₁.as he₁)) (hρ.eval pe.term.ideal)
    (by simpa [SourceAdmissible.eval, ΩLower.toIdeal] using pe.fixed he₁ σ ρ hρ)
    (by
      rw [elabel]
      simp only [op_id, (Tm E ℓ).map_id_apply]
      rw [Tm.type_map, hpi, Ty.piApp_pairPresheaf_map])
    (by
      rw [elabel, Tm.type_map, hdom]
      exact yonedaEquiv_naturality _ σ)
  simp only [elabel] at hresult
  simp only [Category.id_comp, RawValuation.pullback_id, ΩIdeal.pullback_id,
    op_id, (Tm E ℓ).map_id_apply] at hresult
  rw [RawFamily.sectionValue_eq_value (CtxCat.rawComprehension ht) _ σ ρ _ _
    ((Raw.ContextSection.ofTerm ht he₁).pullbackId σ)] at hresult
  rw [← Tm.map_apply _ _ _ hpi hdom σ,
    Tm.apply_label Γ₁.as ht ht' hf he₁] at hresult
  rwa [← HasSubstitution.instantiate ht he₁ pe.type.ideal pe.term.ideal pe.fixed pe.term.subst
    pt'.subst σ ρ hρ, hvalue σ ρ hρ]

theorem RawJudgment.appDF (pt : RawJudgment Γ₁ t t (.sort u)) :
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) t' t' (.sort v) →
    RawJudgment Γ₁ f f' (.forallE t t') →
    RawJudgment Γ₁ e₁ e₂ t →
    RawJudgment Γ₁ (t'.inst e₁) (t'.inst e₂) (.sort v) →
    RawJudgment Γ₁ (.app f e₁) (.app f' e₂) (t'.inst e₁) := by
  intro pt' pf pe pResult
  have p₁ := pf.toRawTyped.app pt.syntactic pt'.syntactic pt'.left pe.toRawTyped pResult.left
  have p₂ := pf.symm.toRawTyped.app pt.syntactic pt'.syntactic pt'.left pe.symm.toRawTyped pResult.right
  refine ⟨.appDF pt.syntactic pt'.syntactic pf.syntactic pe.syntactic pResult.syntactic,
    pResult.left, p₁.1.term, p₂.1.term, fun _ σ ρ hρ => ?_, p₁.1.fixed⟩
  rw [p₁.2 σ ρ hρ, p₂.2 σ ρ hρ, Tm.label_eq (TypeEq.ofDefEq pt.syntactic) pe.syntactic,
    HasEquality.eval pf.equal hρ pf.left.ideal pf.right.ideal,
    HasEquality.eval pe.equal hρ pe.left.ideal pe.right.ideal]

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

theorem RawJudgment.eta (pt : RawJudgment Γ₁ t t (.sort u)) :
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) t' t' (.sort v) →
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) t.wk t.wk (.sort u) →
    RawJudgment (CtxCat.extension Γ₁ pt.syntactic) e.wk e.wk
      (.forallE t.wk (t'.wkFrom Γ₁.as.len)) →
    RawJudgment Γ₁ e e (.forallE t t') →
    RawJudgment Γ₁ (.lam t (.app e.wk (.var (Fin.last Γ₁.as.len)))) e (.forallE t t') := by
  intro pt' ptw pew pe
  have pw : RawJudgment ((Γ₁.extension pt.syntactic).extension ptw.syntactic)
      (t'.wkFrom Γ₁.as.len) (t'.wkFrom Γ₁.as.len) (.sort v) := by
    convert ((SemanticHom.projection pt.syntactic).lift pt.syntactic pt.left).judgment pt' using 1 <;>
      simp [RawCtx.Hom.lift, RawCtx.snoc, CtxCat.extension, CtxCat.projectionRaw,
        ← Subst.wkFrom_eq_lift_wk, ← Expr.wkFrom_eq_subst]
    congr 2
    exact (Expr.subst_wk _).symm
  have pvar : RawJudgment (Γ₁.extension pt.syntactic) (.var (Fin.last Γ₁.as.len))
      (.var (Fin.last Γ₁.as.len)) t.wk :=
    ⟨CtxWF.varLast (Γ₁.as.wf.snoc ⟨_, pt.syntactic⟩), ptw.left,
      .var _ _, .var _ _, .refl _ _, .varLast pt.syntactic pt.left.subst⟩
  have pbody := appDF ptw pw pew pvar (by rwa [Expr.inst_wkFrom_last])
  rw [Expr.inst_wkFrom_last] at pbody
  exact of_typings (.eta pt.syntactic pt'.syntactic ptw.syntactic pew.syntactic pe.syntactic)
    (lamDF pt pt' pbody pbody) pe
    (HasEquality.eta pt.syntactic pt'.syntactic pt.left.ideal pt'.left.ideal pe.syntactic.left
      pe.left.ideal pe.fixed pe.left.subst)

end Metalean.CoherentShape
