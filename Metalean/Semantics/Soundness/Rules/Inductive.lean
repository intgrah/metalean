/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Constructor.Types
public import Metalean.Semantics.Soundness.Judgment
public import Metalean.Semantics.Soundness.Telescope.Decoder
import Metalean.Strong.InstLevel
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Domain.Inductive.Decoder
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Soundness.Rules.Core

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
  {Γ₁ : CtxCat E₂ ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
  {is₁ is₂ : Fin (ι.nindices s) → Expr ζ₂ ℓ Γ₁.as.len}
  {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len}
  {recFds₁ recFds₂ : Fin (ι.ctors s c).nrecFields → Expr ζ₂ ℓ Γ₁.as.len}
  {fieldLevels : Fin (ι.ctors s c).nfields → Level ℓ}
  {recFieldLevels : Fin (ι.ctors s c).nrecFields → Level ℓ}

noncomputable def ctorFieldTypes {Γ₂ : CtxCat E₂ ℓ}
    (pfn : ∀ d : Fin (ι.nctors s), HasIdeality (CtxCat.nil E₂ ℓ)
      (((E₂.get η).block.ctorTypeFn s d).instL fun p => ls p))
    (names : Fin ι.nparams → Tm_ Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hps : ∀ p, ((rawInterpret (piLimit E₂ ℓ) Γ₁ (ps₁ p)).app _ σ.op ρ).IsDirected)
    (d : Fin (ι.nctors s)) : Domain Γ₂ :=
  ((RawFamily.closedApps
    (rawInterpret (piLimit E₂ ℓ) (CtxCat.nil E₂ ℓ) (((E₂.get η).block.ctorTypeFn s d).instL fun p => ls p))
    names fun p => rawInterpret (piLimit E₂ ℓ) Γ₁ (ps₁ p)).app _ σ.op ρ).toIdeal
    (ctorFieldTypes_value_isDirected d (pfn d) _ _ σ ρ hps)

theorem HasIdeality.ind (h : IndTyping Γ₁ η s ls ps₁ is₁) (hB : (E₂.get η).block.WFStrong E₂)
    (hfn : ∀ c : Fin (ι.nctors s), HasIdeality (CtxCat.nil E₂ ℓ)
      (((E₂.get η).block.ctorTypeFn s c).instL fun p => ls p))
    (hp : ∀ p, HasIdeality Γ₁ (ps₁ p)) :
    HasIdeality Γ₁ (.ind η s ls ps₁ is₁) :=
  fun _ σ ρ hρ => by
    rw [rawInterpret_ind_typed _ h hB]
    exact RawValue.ind_isDirected _ fun c =>
      ctorFieldTypes_value_isDirected c (hfn c) _ _ σ ρ fun p => hp p σ ρ hρ

theorem HasSubstitution.ind (h : IndTyping Γ₁ η s ls ps₁ is₁) (hB : (E₂.get η).block.WFStrong E₂)
    (hp : ∀ p, HasSubstitution Γ₁ (ps₁ p)) :
    HasSubstitution Γ₁ (.ind η s ls ps₁ is₁) := by
  intro Γ₂ Γ₃ σ₁ σ₂ ρs ρt hsub hρ
  change (rawInterpret (piLimit E₂ ℓ) Γ₂
    (.ind η s ls (fun p => (ps₁ p).subst σ₁.subst) fun i => (is₁ i).subst σ₁.subst)).app _ σ₂.op ρt = _
  rw [rawInterpret_ind_typed _ (h.subst σ₁) hB, rawInterpret_ind_typed _ h hB,
    RawFamily.ind_value, RawFamily.ind_value]
  refine RawValue.ind_congr ?_ fun (c c' : Fin (ι.nctors s)) hcc => ?_
  · rw [← h.code_map, ← IndCode.map_comp_hom]
  · rw [Fin.ext hcc, RawFamily.closedApps_value, RawFamily.closedApps_value,
      CtxCat.hom_nil_eq (σ₂ ≫ CtxCat.toNil Γ₂)
        ((σ₂ ≫ RawCtx.toCtx.map σ₁) ≫ CtxCat.toNil Γ₁)]
    congr 1
    · funext p
      rw [op_comp, Functor.map_comp_apply, Tm.map_label]
      exact congrArg ((Tm E₂ ℓ).map σ₂.op) (Tm.label_congr (by simp))
    · funext p
      exact hp p σ₁ σ₂ ρs ρt hsub hρ

theorem HasFixedness.ind (h : IndTyping Γ₁ η s ls ps₁ is₁) (hB : (E₂.get η).block.WFStrong E₂) :
    HasFixedness Γ₁ (.ind η s ls ps₁ is₁) (.sort ((E₂.get η).block.level.inst ls)) := by
  intro _ _ σ₁ ρ _
  rw [rawInterpret_sort, RawFamily.sort_value, rawInterpret_ind_typed _ h hB,
    RawFamily.ind_value]
  apply le_antisymm
  · intro Γ₃ σ₂ y hy
    exact ((mem_piLimit_rawExtend_sort_iff _ _ _ _ _).mp hy).1
  · intro Γ₃ σ₂ y hy
    refine (mem_piLimit_rawExtend_sort_iff _ _ _ _ _).mpr ⟨hy, ?_⟩
    have ⟨ts, _, hle⟩ := hy
    refine Shape.IsCode.of_le hle (.ind _ ?_)
    rw [IndCode.rel_map, IndCode.rel_map, h.code_rel]

theorem RawJudgment.indDF (hB : (E₂.get η).block.WFStrong E₂)
    (pfn : ∀ c : Fin (ι.nctors s), RawInterpretationProperties (CtxCat.nil E₂ ℓ)
      (((E₂.get η).block.ctorTypeFn s c).instL fun p => ls p)) :
    (∀ p, RawJudgment Γ₁ (ps₁ p) (ps₂ p) ((E₂.get η).block.paramType ls ps₁ p)) →
    (∀ i, RawJudgment Γ₁ (is₁ i) (is₂ i) ((E₂.get η).block.indexType ls s ps₁ is₁ i)) →
    RawJudgment Γ₁ (.ind η s ls ps₁ is₁) (.ind η s ls ps₂ is₂)
      (.sort ((E₂.get η).block.level.inst ls)) := by
  intro pps pis
  have hps := fun p => (pps p).syntactic
  have his := fun i => (pis i).syntactic
  have h₁ := IndTyping.left hps his
  have h₂ := IndTyping.right hB hps his
  exact {
    syntactic := .indDF hps his
    type := RawInterpretationProperties.sort Γ₁ _
    left := ⟨HasIdeality.ind h₁ hB (fun c => (pfn c).ideal) fun p => (pps p).left.ideal,
      HasSubstitution.ind h₁ hB fun p => (pps p).left.subst⟩
    right := ⟨HasIdeality.ind h₂ hB (fun c => (pfn c).ideal) fun p => (pps p).right.ideal,
      HasSubstitution.ind h₂ hB fun p => (pps p).right.subst⟩
    equal := fun _ σ ρ hρ => by
      rw [rawInterpret_ind_typed _ h₁ hB, rawInterpret_ind_typed _ h₂ hB,
        RawFamily.ind_value, RawFamily.ind_value]
      refine RawValue.ind_congr (congrArg (IndCode.map _) (h₁.code_congr hB hps his h₂))
        fun (c c' : Fin (ι.nctors s)) hcc => ?_
      rw [Fin.ext hcc, RawFamily.closedApps_value, RawFamily.closedApps_value]
      congr 1
      · funext p
        exact congrArg ((Tm E₂ ℓ).map σ.op)
          (Tm.label_eq (Inductive.paramType_congr hB p hps) (hps p))
      · funext p
        exact (pps p).equal σ ρ hρ
    fixed := HasFixedness.ind h₁ hB }

theorem RawInterpretationProperties.ctor (h : CtorTyping Γ₁ η s c ls ps₁ fds₁ recFds₁)
    (pf : ∀ f, RawInterpretationProperties Γ₁ (fds₁ f)) (pr : ∀ f, RawInterpretationProperties Γ₁ (recFds₁ f)) :
    RawInterpretationProperties Γ₁ (.ctor η s c ls ps₁ fds₁ recFds₁) where
  ideal := fun _ σ ρ hρ => by
    cases hrel : Level.rel ((E₂.get η).block.level.inst ls)
    · rw [rawInterpret_ctor_prop _ hrel]
      exact ΩLower.isDirected_bot
    · rw [rawInterpret_ctor_typed _ h hrel]
      refine RawValue.ctor_isDirected _ _ fun i => ?_
      beta_reduce
      cases i using Fin.addCases with
      | left f => rw [Fin.append_left]; exact (pf f).ideal σ ρ hρ
      | right f => rw [Fin.append_right]; exact (pr f).ideal σ ρ hρ
  subst := by
    intro Γ₂ Γ₃ σ₁ σ₂ ρs ρt hσ₁ hρ
    change (rawInterpret (piLimit E₂ ℓ) Γ₂ (.ctor η s c ls (fun p => (ps₁ p).subst σ₁.subst)
      (fun f => (fds₁ f).subst σ₁.subst) fun f => (recFds₁ f).subst σ₁.subst)).app _ σ₂.op ρt = _
    cases hrel : Level.rel ((E₂.get η).block.level.inst ls)
    · rw [rawInterpret_ctor_prop _ hrel, rawInterpret_ctor_prop _ hrel]
      rfl
    · rw [rawInterpret_ctor_typed _ (h.subst σ₁) hrel, rawInterpret_ctor_typed _ h hrel,
        RawFamily.ctor_value, RawFamily.ctor_value, ← h.names_map σ₁]
      congr 1
      · funext i
        exact ((Tm E₂ ℓ).map_comp_apply _ _ _).symm
      · funext i
        cases i using Fin.addCases with
        | left f => simpa only [Fin.append_left] using (pf f).subst σ₁ σ₂ ρs ρt hσ₁ hρ
        | right f => simpa only [Fin.append_right] using (pr f).subst σ₁ σ₂ ρs ρt hσ₁ hρ

theorem RawJudgment.ctorDF (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hB : (E₂.get η).block.WFStrong E₂) :
    (∀ p, RawJudgment Γ₁ (ps₁ p) (ps₂ p) ((E₂.get η).block.paramType ls ps₁ p)) →
    (∀ f, RawJudgment Γ₁ (fds₁ f) (fds₂ f)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f)) →
    (∀ f, RawJudgment Γ₁ (recFds₁ f) (recFds₂ f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f)) →
    (∀ f, E₂[Γ₁.as.ctx] ⊢ₛ
      ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f ≡
      ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₂ fds₂ f : .sort (fieldLevels f)) →
    (∀ f, E₂[Γ₁.as.ctx] ⊢ₛ
      ((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f ≡
      ((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₂ fds₂ f : .sort (recFieldLevels f)) →
    RawJudgment Γ₁
      (.ind η s ls ps₁ fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps₁ fds₁ i)
      (.ind η s ls ps₂ fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps₂ fds₂ i)
      (.sort ((E₂.get η).block.level.inst ls)) →
    RawJudgment Γ₁ (.ctor η s c ls ps₁ fds₁ recFds₁) (.ctor η s c ls ps₂ fds₂ recFds₂)
      (.ind η s ls ps₁ fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps₁ fds₁ i) := by
  intro pps pf pr hfieldTypes hrecFieldTypes pT
  have h₁ := CtorTyping.left (fun f => (pf f).syntactic) fun f => (pr f).syntactic
  have h₂ := CtorTyping.right (fun f => (pf f).syntactic) (fun f => (pr f).syntactic) hfieldTypes
    hrecFieldTypes
  refine ⟨.ctorDF (fun p => (pps p).syntactic) (fun f => (pf f).syntactic)
      (fun f => (pr f).syntactic) hfieldTypes hrecFieldTypes pT.syntactic, pT.left,
    .ctor h₁ (fun f => (pf f).left) fun f => (pr f).left,
    .ctor h₂ (fun f => (pf f).right) fun f => (pr f).right, fun _ σ ρ hρ => ?_,
    fun Γ₂ ht σ ρ hρ => ?_⟩
  · cases hrel : Level.rel ((E₂.get η).block.level.inst ls)
    · rw [rawInterpret_ctor_prop _ hrel, rawInterpret_ctor_prop _ hrel]
    rw [rawInterpret_ctor_typed _ h₁ hrel, rawInterpret_ctor_typed _ h₂ hrel,
      RawFamily.ctor_value, RawFamily.ctor_value, CtorTyping.names_congr
        (fun f => (pf f).syntactic) (fun f => (pr f).syntactic) hfieldTypes hrecFieldTypes h₁ h₂]
    congr 1
    funext i
    cases i using Fin.addCases with
    | left f => simpa only [Fin.append_left] using (pf f).equal σ ρ hρ
    | right f => simpa only [Fin.append_right] using (pr f).equal σ ρ hρ
  have hT := IndTyping.ofTyping hB pT.syntactic.left
  cases hrel : Level.rel ((E₂.get η).block.level.inst ls)
  · rw [rawInterpret_ctor_prop _ hrel]
    exact rawExtend_bottom_payload piLimit_isPayloadStrict _ _
  by_cases hs : (E₂.get η).block.IsStructure s c
  · have ppsLeft := fun p => (pps p).leftRefl
    have pfLeft := fun f => (pf f).leftRefl
    have hctx := hB.paramClosedWF ls
    have hΔ := hB.ordinaryTeleInstL s c ls
    have pctx := hsound.paramTeleProperties hI hblock ls
    have pfields := hsound.blockOrdinaryTeleProperties η hI hblock s c ls
    have pbody := hsound.blockCtorFieldProperties η hI hblock s c ls hctx
    have pfn (d : Fin (ι.nctors s)) := hsound.blockCtorTypeFnProperties η hI hblock s d ls
    have hindices : (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps₁ fds₁ i) =
        hs.indices := funext hs.no_indices.elim
    have hrecursive : recFds₁ = hs.recursive := funext hs.no_recursive.elim
    have hctor : E₂[Γ₁.as.ctx] ⊢ₛ .ctor η s c ls ps₁ fds₁ hs.recursive :
        .ind η s ls ps₁ hs.indices := by
      simpa only [hindices, hrecursive] using ht
    have hlabel : Tm.label Γ₁.as ht = Tm.label Γ₁.as hctor := by
      apply Tm.label_eq
      · simpa only [hindices] using IsTypeStrong.isTypeEq ht.regular
      · simpa only [hrecursive] using ht
    let w : hT.code.StructWitness c (Tm.label Γ₁.as ht) := {
      params := ps₁
      struct := hs
      block := hB
      typed := hT.param
      params_eq := fun _ => rfl
      guard := by
        change Ty.ofTyping Γ₁.as ht.regular.choose_spec = Ty.ofTyping Γ₁.as _
        exact Ty.ofTyping_congr (congrArg (Expr.ind η s ls ps₁) hindices) }
    let hg : hT.code.StructGuard c (Tm.label Γ₁.as ht) := ⟨w⟩
    have hnames : indNames (hg.pullback σ) = fun i => (Tm E₂ ℓ).map σ.op (h₁.names i) := by
      funext i
      rw [← map_indNames hg σ (hg.pullback σ) i]
      apply congrArg ((Tm E₂ ℓ).map σ.op)
      cases i using Fin.addCases with
      | left f =>
        change Fin (ι.ctors s c).nfields at f
        simp only [indNames, CtorTyping.names, CtorHead.sig, IndCode.ctorHead,
          IndTyping.code, IndCode.map]
        rw [Fin.append_left, Fin.append_left]
        exact Tm.projOfCode_ctor_label hg w fds₁ hctor hlabel (fun f => h₁.ordinary f) f
      | right f => exact hs.no_recursive.elim f
    let vals : Fin (ι.ctors s c).nfields → Domain Γ₂ := fun f => hρ.eval (pfLeft f).left.ideal
    let fields : Fin (CtorHead.mk η s c).arity → Domain Γ₂ :=
      Fin.append vals hs.no_recursive.elim
    let names : Fin (CtorHead.mk η s c).arity → Tm_ Γ₂ :=
      fun i => (Tm E₂ ℓ).map σ.op (h₁.names i)
    let X : Domain Γ₂ := ctorIdeal ⟨η, s, c⟩ names fields
    have hX : (rawInterpret (piLimit E₂ ℓ) Γ₁ (.ctor η s c ls ps₁ fds₁ recFds₁)).app _ σ.op ρ = X.val := by
      rw [rawInterpret_ctor_typed _ h₁ hrel, RawFamily.ctor_value]
      apply congrArg (RawValue.ctor ⟨η, s, c⟩ names)
      funext i
      cases i using Fin.addCases with
      | left f => simp only [fields, CtorHead.sig, Fin.append_left]; rfl
      | right f => exact hs.no_recursive.elim f
    let types := ctorFieldTypes (fun d => (pfn d).ideal) (fun p => Tm.label Γ₁.as (hT.param p))
      σ ρ fun p => (ppsLeft p).left.ideal σ ρ hρ
    rw [rawInterpret_ind_typed _ hT hB, RawFamily.ind_value, hX]
    change (piLimit E₂ ℓ).rawExtend
      (RawValue.ind (hT.code.map ((Tm E₂ ℓ).map σ.op)) fun d => (types d).val)
      ((Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as ht)) X.val = X.val
    rw [piLimit_rawExtend_indValue_of_structural _
      ((IndCode.rel_map _ _).trans (hT.code_rel.trans hrel)) (hg.pullback σ) types X]
    apply congrArg Subtype.val
    change (piLimit E₂ ℓ).indBody (types c) X (hg.pullback σ) = X
    unfold indBody
    rw [hnames]
    change ctorIdeal ⟨η, s, c⟩ names
      ((piLimit E₂ ℓ).telescope (types c) names fun i => projIdeal ⟨η, s, c⟩ i X).1 = X
    have hproj : (fun i => projIdeal (CtorHead.mk η s c) i X) = fields := by
      funext i
      exact Subtype.val_injective (RawValue.proj_ctor _ _ _ i)
    rw [hproj]
    have hps := fun p => (ppsLeft p).syntactic.left
    have hf := fun f => (pfLeft f).syntactic.left
    have ⟨hprojPi, hT', _, hlabels⟩ := ctorFieldTypes_eq_pi hctx hΔ pctx pbody hps
      (fun p => (ppsLeft p).left) (fun p => (ppsLeft p).fixed) hf σ ρ hρ
    have pσ (v : Var (ι.nparams + (ι.ctors s c).nfields)) : RawJudgment Γ₁
        ((ctorTargetHom hctx hΔ hps hf).subst v) ((ctorTargetHom hctx hΔ hps hf).subst v)
        (((CtxCat.extendTele ⟨_, hctx⟩ _ hΔ).as.ctx.get v).subst
          (ctorTargetHom hctx hΔ hps hf).subst) := by
      simpa [CtxCat.extendTele, ctorTargetHom] using ctorSourceJudgment ppsLeft pfLeft v
    have hsource := (pctx.append (by simpa using pfields)).admissible_of_images
      (CtxCat.extendTele ⟨_, hctx⟩ _ hΔ).as.wf (ctorTargetHom hctx hΔ hps hf) σ ρ hρ
      (fun v => (pσ v).left.ideal) (fun v => (pσ v).left.subst) fun v => (pσ v).fixed
    have hvals : (fun v => (rawInterpret (piLimit E₂ ℓ) Γ₁
        ((ctorTargetHom hctx hΔ hps hf).subst v)).app _ σ.op ρ) =
        Fin.append (fun p => (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps₁ p)).app _ σ.op ρ)
          fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (fds₁ f)).app _ σ.op ρ := by
      funext v
      cases v using Fin.addCases <;> simp [ctorTargetHom]
    rw [hvals, RawValuation.pushFin_append] at hsource
    have hd' := rawInterpret_ctxPi_decode _ hΔ pfields
      (.sort ((E₂.get η).block.level.inst ls)) .sortDF (HasIdeality.sort _ _)
      (σ ≫ RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf)) _
      (fun f => ((rawInterpret (piLimit E₂ ℓ) Γ₁ (fds₁ f)).app _ σ.op ρ).toIdeal
        ((pfLeft f).left.ideal σ ρ hρ)) hsource (types c)
      (by rw [hprojPi]; exact hT')
    have hd : ((piLimit E₂ ℓ).telescope (types c)
        (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as (pfLeft f).syntactic.left)) vals).1 = vals :=
      (congrArg (fun n => ((piLimit E₂ ℓ).telescope (types c) n _).1) hlabels).symm.trans
        (congrArg Prod.fst hd')
    have hnr := Fin.eq_zero_of_isEmpty hs.no_recursive
    have hdecode : ∀ (ns : Fin (ι.ctors s c).nrecFields → Tm_ Γ₂)
        (xs : Fin (ι.ctors s c).nrecFields → Domain Γ₂),
        ((piLimit E₂ ℓ).telescope (types c)
          (Fin.append (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as (pfLeft f).syntactic.left)) ns)
          (Fin.append vals xs)).1 = Fin.append vals xs := by
      rw [hnr]
      intro ns xs
      simp only [Fin.append_zero_right]
      exact hd
    have hnames' : names = Fin.append
        (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as (pfLeft f).syntactic.left))
        hs.no_recursive.elim := by
      funext i
      cases i using Fin.addCases with
      | left f => simp [names, CtorTyping.names, CtorHead.sig]
      | right f => exact hs.no_recursive.elim f
    change ctorIdeal ⟨η, s, c⟩ names ((piLimit E₂ ℓ).telescope (types c) names fields).1 =
      ctorIdeal ⟨η, s, c⟩ names fields
    rw [hnames', hdecode]
  · have hns' (s' : Fin ι.nsorts) (c' : Fin (ι.nctors s')) :
        ¬ (E₂.get η).block.IsStructure s' c' := by
      intro hs'
      obtain rfl := hs'.sort_unique s
      obtain rfl := hs'.ctor_unique c
      exact hs hs'
    have hrel' : ∀ {s' : Fin ι.nsorts} {ps' : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
        {is' : Fin (ι.nindices s') → Expr ζ₂ ℓ Γ₁.as.len} (h' : IndTyping Γ₁ η s' ls ps' is'),
        (h'.code.map ((Tm E₂ ℓ).map σ.op)).rel = true :=
      fun h' => (IndCode.rel_map _ _).trans (h'.code_rel.trans hrel)
    rw [rawInterpret_ind_typed _ hT hB, RawFamily.ind_value, rawInterpret_ctor_typed _ h₁ hrel,
      RawFamily.ctor_value, piLimit_rawExtend_indValue_of_nonstructural _ (hrel' hT) (hns' s)]
    refine (RawValue.indProjection_ctor ⟨η, s, c⟩ _ _).trans ?_
    congr 1
    funext i
    cases i using Fin.addCases with
    | left f => simp [CtorHead.sig, CtorHead.projectFields]
    | right f =>
      simp only [CtorHead.sig, CtorHead.projectFields, Fin.append_right]
      cases harity : (ι.ctors s c).recursiveArity f with
      | succ => exact ite_eq_right (Nat.succ_ne_zero _)
      | zero =>
        rw [ite_eq_left rfl]
        have ⟨is, hrec⟩ :=
          ((E₂.get η).block.ctors s c).recursiveFieldExpr_eq_ind η ls ps₁ fds₁ f harity
        have hfix := (pr f).fixed (pr f).syntactic.left σ ρ hρ
        have hty := (hrecFieldTypes f).left
        rw [hrec] at hty
        have hTeq : rawInterpret (piLimit E₂ ℓ) Γ₁
            (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f) =
            rawInterpret (piLimit E₂ ℓ) Γ₁
              (.ind η ((ι.ctors s c).recursiveTarget f) ls ps₁ is) := by rw [hrec]
        rwa [hTeq, rawInterpret_ind_typed _ (IndTyping.ofTyping hB hty) hB, RawFamily.ind_value,
          piLimit_rawExtend_indValue_of_nonstructural _ (hrel' _) (hns' _)] at hfix

end Metalean.CoherentShape
