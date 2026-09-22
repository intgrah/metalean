/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Constructor.Types
public import Metalean.Semantics.Soundness.Judgment
public import Metalean.Semantics.Soundness.Telescope.Decoder
import Metalean.Typing.InstLevel
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Domain.Inductive.Decoder
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Soundness.Rules.Core

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment Presheaf

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
    (by
      rw [RawFamily.closedApps_value]
      exact rawApps_isDirected ⟨_, pfn d _ _ (.nil _ _)⟩ _ fun p => ⟨_, hps p⟩)

theorem HasIdeality.ind (h : IndTyping Γ₁ η s ls ps₁ is₁) (hB : InductiveWF E₂ (E₂.get η).block)
    (hfn : ∀ c : Fin (ι.nctors s), HasIdeality (CtxCat.nil E₂ ℓ)
      (((E₂.get η).block.ctorTypeFn s c).instL fun p => ls p))
    (hp : ∀ p, HasIdeality Γ₁ (ps₁ p)) :
    HasIdeality Γ₁ (.ind η s ls ps₁ is₁) :=
  fun _ σ ρ hρ => by
    rw [rawInterpret_ind_typed _ h hB]
    exact RawValue.ind_isDirected _ fun c =>
      (ctorFieldTypes hfn (fun p => Tm.label Γ₁.as (h.param p)) σ ρ (fun p => hp p σ ρ hρ) c).property

theorem HasSubstitution.ind (h : IndTyping Γ₁ η s ls ps₁ is₁) (hB : InductiveWF E₂ (E₂.get η).block)
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
      rw [op_comp, Functor.map_comp_apply]
      exact congr((Tm E₂ ℓ).map σ₂.op (Tm.label _ (t := $(by simp)) _))
    · funext p
      exact hp p σ₁ σ₂ ρs ρt hsub hρ

theorem HasFixedness.ind (h : IndTyping Γ₁ η s ls ps₁ is₁) (hB : InductiveWF E₂ (E₂.get η).block) :
    HasFixedness Γ₁ (.ind η s ls ps₁ is₁) (.sort ((E₂.get η).block.level.inst ls)) := by
  intro _ _ σ₁ ρ _
  rw [rawInterpret_sort, rawInterpret_ind_typed _ h hB]
  apply le_antisymm
  · intro Γ₃ σ₂ y hy
    exact ((mem_piLimit_rawExtend_sort_iff _ _ _ _ _).mp hy).1
  · intro Γ₃ σ₂ y hy
    refine (mem_piLimit_rawExtend_sort_iff _ _ _ _ _).mpr ⟨hy, ?_⟩
    have ⟨ts, _, hle⟩ := hy
    refine Shape.IsCode.of_le hle (.ind _ ?_)
    rw [IndCode.rel_map, IndCode.rel_map, h.code_rel]

theorem RawJudgment.indDF (hB : InductiveWF E₂ (E₂.get η).block)
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
      rw [rawInterpret_ind_typed _ h₁ hB, rawInterpret_ind_typed _ h₂ hB]
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
      RawFamily.ctor_value, ← h.names_map σ₁]
      congr 1
      · funext i
        exact ((Tm E₂ ℓ).map_comp_apply _ _ _).symm
      · funext i
        cases i using Fin.addCases with
        | left f => simpa using (pf f).subst σ₁ σ₂ ρs ρt hσ₁ hρ
        | right f => simpa using (pr f).subst σ₁ σ₂ ρs ρt hσ₁ hρ

theorem RawTyped.ctor (hsound : RawSound E₂ ℓ pre) (hI : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hB : InductiveWF E₂ (E₂.get η).block)
    (pps : ∀ p, RawTyped Γ₁ (ps₁ p) ((E₂.get η).block.paramType ls ps₁ p))
    (pf : ∀ f, RawTyped Γ₁ (fds₁ f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f))
    (pr : ∀ f, RawTyped Γ₁ (recFds₁ f) (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f)) :
    RawTyped Γ₁ (.ctor η s c ls ps₁ fds₁ recFds₁)
      (.ind η s ls ps₁ fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps₁ fds₁ i) := by
  have hps := fun p => (pps p).typed
  have h₁ : CtorTyping Γ₁ η s c ls ps₁ fds₁ recFds₁ := ⟨fun f => (pf f).typed, fun f => (pr f).typed⟩
  have hT : IndTyping Γ₁ η s ls ps₁ (((E₂.get η).block.ctors s c).targetIndex ls ps₁ fds₁) :=
    ⟨hps, fun i => (hB.ctors s c).targetIndex i (Ctor.forall_ordinarySubst le_rfl hps h₁.ordinary)⟩
  refine ⟨.ctorDF hps h₁.ordinary h₁.recursive
      (fun f => (hB.ctors s c).ordinaryFieldExpr f hps h₁.ordinary)
      (fun f => ((hB.ctors s c).recursiveFieldExpr rfl f Γ₁.as.wf hps h₁.ordinary).choose_spec)
      (.indDF hT.param hT.index),
    ⟨HasIdeality.ind hT hB (fun d => (hsound.ctorTypeFnProperties η hI hblock s d ls).ideal)
      (fun p => (pps p).term.ideal), HasSubstitution.ind hT hB fun p => (pps p).term.subst⟩,
    .ctor h₁ (fun f => (pf f).term) (fun f => (pr f).term), fun Γ₂ ht σ ρ hρ => ?_⟩
  cases hrel : Level.rel ((E₂.get η).block.level.inst ls)
  · rw [rawInterpret_ctor_prop _ hrel]
    exact rawExtend_bottom_payload piLimit_isPayloadStrict _ _
  by_cases hs : (E₂.get η).block.IsStructure s c
  · have hctx := hB.paramClosedWF ls
    have hΔ := ((hB.ctors s c).ordinaryTeleAux _ le_rfl).instLevel (Q := fun _ => True) ls fun _ => trivial
    have pctx := hsound.paramTeleProperties hI hblock ls
    have pfields := hsound.ordinaryTeleProperties η hI hblock s c ls
    have pbody := hsound.ctorFieldProperties η hI hblock s c ls hctx
    have pfn (d : Fin (ι.nctors s)) := hsound.ctorTypeFnProperties η hI hblock s d ls
    have hindices : (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps₁ fds₁ i) =
        hs.indices := funext hs.no_indices.elim
    have hrecursive : recFds₁ = hs.recursive := funext hs.no_recursive.elim
    have hctor : E₂[Γ₁.as.ctx] ⊢ .ctor η s c ls ps₁ fds₁ hs.recursive :
        .ind η s ls ps₁ hs.indices := by
      simpa [hindices, hrecursive] using ht
    let w : hT.code.StructWitness c (Tm.label Γ₁.as ht) := {
      params := ps₁
      struct := hs
      block := hB
      typed := hT.param
      params_eq := fun _ => rfl
      guard := by
        change Ty.ofTyping Γ₁.as ht.regular.choose_spec = Ty.ofTyping Γ₁.as _
        exact congr(Quotient.mk _ (⟨Expr.ind η s ls ps₁ $hindices, _⟩ : Ty.Repr Γ₁)) }
    let hg : hT.code.StructGuard c (Tm.label Γ₁.as ht) := ⟨w⟩
    have hnames : indNames (hg.pullback σ) = fun i => (Tm E₂ ℓ).map σ.op (h₁.names i) := by
      funext i
      rw [← map_indNames hg σ (hg.pullback σ) i]
      apply congrArg ((Tm E₂ ℓ).map σ.op)
      cases i using Fin.addCases with
      | left f =>
        change Fin (ι.ctors s c).nfields at f
        simp only [indNames, CtorTyping.names, IndTyping.code]
        rw [Fin.append_left, Fin.append_left]
        refine (Tm.projOfCode_eq_proj hg w f).trans ?_
        trans Tm.proj hs hB ls ps₁ hT.param f (Tm.label Γ₁.as hctor) rfl
        · congr 1
          simp [hindices, hrecursive]
        · exact Tm.proj_ctor_label hs hB ls ps₁ hT.param fds₁ hctor h₁.ordinary f
      | right f => exact hs.no_recursive.elim f
    let vals : Fin (ι.ctors s c).nfields → Domain Γ₂ := fun f => hρ.eval (pf f).term.ideal
    let fields : Fin (CtorHead.mk η s c).arity → Domain Γ₂ :=
      Fin.append vals hs.no_recursive.elim
    let names : Fin (CtorHead.mk η s c).arity → Tm_ Γ₂ :=
      fun i => (Tm E₂ ℓ).map σ.op (h₁.names i)
    let X : Domain Γ₂ := ctorIdeal ⟨η, s, c⟩ names fields
    have hX : (rawInterpret (piLimit E₂ ℓ) Γ₁ (.ctor η s c ls ps₁ fds₁ recFds₁)).app _ σ.op ρ = X.val := by
      rw [rawInterpret_ctor_typed _ h₁ hrel]
      apply congrArg (RawValue.ctor ⟨η, s, c⟩ names)
      funext i
      cases i using Fin.addCases with
      | left f => simp only [fields, Fin.append_left]; rfl
      | right f => exact hs.no_recursive.elim f
    let types := ctorFieldTypes (fun d => (pfn d).ideal) (fun p => Tm.label Γ₁.as (hT.param p))
      σ ρ fun p => (pps p).term.ideal σ ρ hρ
    rw [rawInterpret_ind_typed _ hT hB, hX]
    change (piLimit E₂ ℓ).rawExtend
      (RawValue.ind (hT.code.map ((Tm E₂ ℓ).map σ.op)) fun d => (types d).val)
      ((Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as ht)) X.val = X.val
    rw [piLimit_rawExtend_indValue_of_structural _
      ((IndCode.rel_map _ _).trans (hT.code_rel.trans hrel)) (hg.pullback σ) types X]
    apply congrArg Subtype.val
    unfold indBody
    rw [hnames]
    change ctorIdeal ⟨η, s, c⟩ names
      ((piLimit E₂ ℓ).telescope (types c) names fun i => projIdeal ⟨η, s, c⟩ i X).1 = X
    have hproj : (fun i => projIdeal (CtorHead.mk η s c) i X) = fields := by
      funext i
      exact Subtype.val_injective (RawValue.proj_ctor _ _ _ i)
    rw [hproj]
    have hps := fun p => (pps p).typed
    have hf := fun f => (pf f).typed
    have ⟨hprojPi, hT', _, hlabels⟩ := ctorFieldTypes_eq_pi hctx hΔ pctx pbody hps
      (fun p => (pps p).term) (fun p => (pps p).fixed) hf σ ρ hρ
    have pσ := Ctor.forall_ordinarySubst
      (motive := fun e _ t => RawTyped Γ₁ e t) (ps₂ := ps₁) (fds₂ := fds₁) le_rfl pps pf
    simp only [Ctx.instL_append] at pσ
    have hsource := (pctx.append (by simpa using pfields)).admissible_of_images
      (CtxCat.extendTele ⟨_, hctx⟩ _ hΔ).as.wf (ctorTargetHom hctx hΔ hps hf) σ ρ hρ
      (fun v => (pσ v).term) fun v => (pσ v).fixed
    dsimp only [ctorTargetHom] at hsource
    rw [Fin.append_comp ps₁ fds₁ (fun e => (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ.op ρ),
      RawValuation.pushFin_append] at hsource
    have hd' := (rawInterpret_ctxPi_decode _ hΔ pfields
      (.sort ((E₂.get η).block.level.inst ls)) .sortDF (HasIdeality.sort _ _)
      (σ ≫ RawCtx.toCtx.map (ctorTargetHom hctx hΔ hps hf)) _
      (fun f => ((rawInterpret (piLimit E₂ ℓ) Γ₁ (fds₁ f)).app _ σ.op ρ).toIdeal
        ((pf f).term.ideal σ ρ hρ))
      (by rw [hprojPi, ← hT']; exact (types c).property)).1 hsource
    simp only [hprojPi, ← hT'] at hd'
    have hd : ((piLimit E₂ ℓ).telescope (types c)
        (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as (pf f).typed)) vals).1 = vals :=
      (congrArg (fun n => ((piLimit E₂ ℓ).telescope (types c) n _).1) hlabels).symm.trans
        (congrArg Prod.fst hd')
    have hnr := Fin.eq_zero_of_isEmpty hs.no_recursive
    have hdecode : ∀ (ns : Fin (ι.ctors s c).nrecFields → Tm_ Γ₂)
        (xs : Fin (ι.ctors s c).nrecFields → Domain Γ₂),
        ((piLimit E₂ ℓ).telescope (types c)
          (Fin.append (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as (pf f).typed)) ns)
          (Fin.append vals xs)).1 = Fin.append vals xs := by
      rw [hnr]
      intro ns xs
      simpa using hd
    change ctorIdeal ⟨η, s, c⟩ names ((piLimit E₂ ℓ).telescope (types c) names fields).1 =
      ctorIdeal ⟨η, s, c⟩ names fields
    simp [names, CtorTyping.names, Fin.append_comp, fields, hdecode]
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
      piLimit_rawExtend_indValue_of_nonstructural _ (hrel' hT) (hns' s)]
    refine (RawValue.indProjection_ctor ⟨η, s, c⟩ _ _).trans ?_
    congr 1
    funext i
    cases i using Fin.addCases with
    | left f => simp
    | right f =>
      simp only [CtorHead.projectFields, Fin.append_right]
      cases harity : (ι.ctors s c).recursiveArity f with
      | succ => exact ite_eq_right (Nat.succ_ne_zero _)
      | zero =>
        have ⟨is, hrec⟩ :=
          ((E₂.get η).block.ctors s c).recursiveFieldExpr_eq_ind η ls ps₁ fds₁ f harity
        have hfix := (pr f).fixed (pr f).typed σ ρ hρ
        have ⟨v, hty⟩ := (hB.ctors s c).recursiveFieldExpr rfl f Γ₁.as.wf hps h₁.ordinary
        rw [hrec] at hty
        conv_lhs at hfix =>
          arg 2
          rw [hrec, rawInterpret_ind_typed _ (IndTyping.ofTyping hB hty) hB, RawFamily.ind_value]
        rwa [piLimit_rawExtend_indValue_of_nonstructural _ (hrel' _) (hns' _)] at hfix

theorem RawJudgment.ctorDF (hsound : RawSound E₂ ℓ pre) (hI : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hB : InductiveWF E₂ (E₂.get η).block) :
    (∀ p, RawJudgment Γ₁ (ps₁ p) (ps₂ p) ((E₂.get η).block.paramType ls ps₁ p)) →
    (∀ f, RawJudgment Γ₁ (fds₁ f) (fds₂ f)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f)) →
    (∀ f, RawJudgment Γ₁ (recFds₁ f) (recFds₂ f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f)) →
    (∀ f, E₂[Γ₁.as.ctx] ⊢ ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f ≡
      ((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₂ fds₂ f : .sort (fieldLevels f)) →
    (∀ f, E₂[Γ₁.as.ctx] ⊢ ((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f ≡
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
    (RawTyped.ctor hsound hI hblock hB (fun p => (pps p).toRawTyped)
      (fun f => (pf f).toRawTyped) (fun f => (pr f).toRawTyped)).fixed⟩
  · cases hrel : Level.rel ((E₂.get η).block.level.inst ls)
    · rw [rawInterpret_ctor_prop _ hrel, rawInterpret_ctor_prop _ hrel]
    rw [rawInterpret_ctor_typed _ h₁ hrel, rawInterpret_ctor_typed _ h₂ hrel, RawFamily.ctor_value,
      CtorTyping.names_congr (fun f => (pf f).syntactic) (fun f => (pr f).syntactic) hfieldTypes hrecFieldTypes h₁ h₂]
    congr 1
    funext i
    cases i using Fin.addCases with
    | left f => simpa using (pf f).equal σ ρ hρ
    | right f => simpa using (pr f).equal σ ρ hρ

end Metalean.CoherentShape
