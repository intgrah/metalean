/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Recursor.Access
public import Metalean.SetSemantics.Environment.Inductive.Recursor.Telescope
import Metalean.SetSemantics.InductiveComputation
import Metalean.Syntax.Inductive.LargeElimination

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}

namespace CtorCode

private theorem applyFields_zero_congr {n : Nat}
    {code : CtorCode n} {block : ZFSet}
    {γ : Slots n} (minor : ZFSet) {left right : ZFSet}
    (hleft : left ∈ code.argSet block γ)
    (hright : right ∈ code.argSet block γ)
    (h : code.ArgAgree left right) :
    code.applyFields 0 γ minor left =
      code.applyFields 0 γ minor right := by
  induction h generalizing minor with
  | target => rfl
  | arg hfst _ ih =>
    obtain ⟨leftValue, leftTail, _, hleftTail, rfl⟩ := argSet_arg_inv hleft
    obtain ⟨rightValue, rightTail, _, hrightTail, rfl⟩ := argSet_arg_inv hright
    simp at hfst ih
    subst hfst
    simpa [applyFields] using ih _ hleftTail hrightTail
  | @recArg _ _ tele index _ _ _ _ ih =>
    obtain ⟨leftField, leftTail, hleftField, hleftTail, rfl⟩ := argSet_recArg_inv hleft
    obtain ⟨rightField, rightTail, hrightField, hrightTail, rfl⟩ := argSet_recArg_inv hright
    simp only [snd_pair] at ih
    simp only [applyFields, fst_pair, snd_pair]
    rw [eraseRecField_zero_eq tele index index block block γ hleftField hrightField]
    exact ih _ hleftTail hrightTail

private theorem applyIhs_argMap_congr {n : Nat}
    {code : CtorCode n} {block graph : ZFSet}
    (hgraph : ∀ key leftValue rightValue,
      pair key leftValue ∈ block → pair key rightValue ∈ block →
      app graph (pair key leftValue) = app graph (pair key rightValue))
    {γ : Slots n} (minor : ZFSet) {left right : ZFSet}
    (hleft : left ∈ code.argSet block γ)
    (hright : right ∈ code.argSet block γ)
    (h : code.ArgAgree left right) :
    code.applyIhs minor (code.argMap graph γ left) =
      code.applyIhs minor (code.argMap graph γ right) := by
  induction h generalizing minor with
  | target => rfl
  | arg hfst _ ih =>
    obtain ⟨leftValue, leftTail, _, hleftTail, rfl⟩ := argSet_arg_inv hleft
    obtain ⟨rightValue, rightTail, _, hrightTail, rfl⟩ := argSet_arg_inv hright
    simp only [fst_pair, snd_pair] at hfst ih
    subst hfst
    simpa [argMap, applyIhs, fst_pair, snd_pair] using ih _ hleftTail hrightTail
  | @recArg _ _ tele index _ _ _ _ ih =>
    obtain ⟨leftField, leftTail, hleftField, hleftTail, rfl⟩ := argSet_recArg_inv hleft
    obtain ⟨rightField, rightTail, hrightField, hrightTail, rfl⟩ := argSet_recArg_inv hright
    simp only [snd_pair] at ih
    simp only [argMap, applyIhs, fst_pair, snd_pair]
    have hmap : recMap tele index graph γ leftField = recMap tele index graph γ rightField := by
      rw [recFieldSet] at hleftField hrightField
      apply tele.lamAt_eq_of_mem
        (leftDomain := fun final => fibreOp block (index final))
        (rightDomain := fun final => fibreOp block (index final))
        (hleft := hleftField) (hright := hrightField)
      intro final leftValue rightValue hleftValue hrightValue
      exact hgraph _ _ _ (mem_fibre.mp hleftValue) (mem_fibre.mp hrightValue)
    rw [hmap]
    exact ih _ hleftTail hrightTail

theorem applyMinor_zero_argMap_congr_of_argAgree
    {n : Nat} (code : CtorCode n)
    (block graph : ZFSet)
    (hgraph : ∀ key leftValue rightValue,
      pair key leftValue ∈ block → pair key rightValue ∈ block →
      app graph (pair key leftValue) = app graph (pair key rightValue))
    (γ : Slots n) (minor : ZFSet) {left right : ZFSet}
    (hleft : left ∈ code.argSet block γ)
    (hright : right ∈ code.argSet block γ)
    (h : code.ArgAgree left right) :
    code.applyMinor 0 γ minor (code.argMap graph γ left) =
      code.applyMinor 0 γ minor (code.argMap graph γ right) := by
  unfold applyMinor
  rw [forgetIhs_argMap code γ left hleft, forgetIhs_argMap code γ right hright,
    applyFields_zero_congr minor hleft hright h]
  exact applyIhs_argMap_congr hgraph _ hleft hright h

end CtorCode

namespace StrongInductiveModel

variable (model : StrongInductiveModel E₁ ε₁ I ls)

theorem mem_largeAccessRel_of_predecessor
    (vps : Slots ι.nparams) {key : ZFSet}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {vargs : ZFSet}
    (hargs : vargs ∈ (model.codeOf s c).argSet (model.toModel.block vps) vps)
    (htarget : (model.codeOf s c).targetIndex vps vargs = key)
    (predecessor : ZFSet) (hpredecessor : predecessor ∈ (model.codeOf s c).predecessors vps vargs) :
    pair (fst predecessor) key ∈ model.largeAccessRel vps := by
  have hprojected : pair (fst predecessor)
      (fst (entry ((model.codeOf s c).targetIndex vps vargs) (tagOf s c) vargs)) ∈
        model.largeAccessRel vps :=
    mem_image.mpr
      ⟨_, mem_blockPredecessorRel.mpr ⟨s, c, vargs, hargs, hpredecessor, rfl⟩, by simp⟩
  rwa [entry_eq, fst_pair, htarget] at hprojected

theorem recGraph_congr_key
    (hdecl : SemDecls E₁ ε₁ zeroNs) (hrule : SemDeclRules E₁ ε₁ zeroNs)
    (ho : E₁.Ordered) (hB : I.WFStrong E₁)
    (hlarge : I.LargeElim) (hlevel : model.toModel.level = 0)
    (s : Fin ι.nsorts) (l : Level 0) (γ : RecSlots ι s)
    (hγ : γ ∈ Reachable Set.univ (model.recrTeleSem s l))
    {left right : ZFSet}
    (hleft : left ∈ model.toModel.block (RecSlots.paramsOf γ))
    (hright : right ∈ model.toModel.block (RecSlots.paramsOf γ))
    (hkeys : fst left = fst right) :
    app (model.recrGraph s γ) left = app (model.recrGraph s γ) right := by
  let vps := RecSlots.paramsOf γ
  let block := model.toModel.block vps
  let graph := model.recrGraph s γ
  let lift := model.liftLargeAccessGraph vps graph
  have hmaps := model.mapsTo vps
  have hps := model.recrParamsReachable s l γ hγ
  have hstep := model.recrStepSound s l γ hγ
  have hzero : (I.level.inst ls).eval zeroNs = 0 := hlevel
  have hdecompose {entry : ZFSet} (hentry : entry ∈ block) :
      ∃ s₁, ∃ c₁, ∃ args ∈ (model.codeOf s₁ c₁).argSet block vps,
        entry =
          ZFSet.entry ((model.codeOf s₁ c₁).targetIndex vps args) (tagOf s₁ c₁) args := by
    change entry ∈ indSet model.toModel.codes model.toModel.bound vps at hentry
    rw [← indSet_unfold hmaps] at hentry
    have ⟨s₁, c₁, args, hargs, heq⟩ := mem_indOp.mp hentry
    exact ⟨s₁, c₁, args, hargs, heq.symm⟩
  refine accSet_induction (p := fun key => ∀ left ∈ block, fst left = key →
      ∀ right ∈ block, fst right = key → app graph left = app graph right)
    (fun key hkey ih left hleft hleftKey right hright hrightKey => ?_)
    (fst left) (model.large_key_accessible hdecl hrule ho hB hlarge hlevel vps hps left hleft)
    left hleft rfl right hright hkeys.symm
  have ⟨s₁, c₁, leftArgs, hleftArgs, hleftEntry⟩ := hdecompose hleft
  have ⟨s₂, c₂, rightArgs, hrightArgs, hrightEntry⟩ := hdecompose hright
  have hleftTarget : (model.codeOf s₁ c₁).targetIndex vps leftArgs = key := by
    rwa [hleftEntry, entry_eq, fst_pair] at hleftKey
  have hrightTarget : (model.codeOf s₂ c₂).targetIndex vps rightArgs = key := by
    rwa [hrightEntry, entry_eq, fst_pair] at hrightKey
  have hleftIota : app graph left = (model.codeOf s₁ c₁).applyMinor model.toModel.level vps
      [zf|$(minorFamily (RecSlots.casesOf γ)) $(encode (tagOf s₁ c₁))]
      ((model.codeOf s₁ c₁).argMap graph vps leftArgs) :=
    hleftEntry ▸ recGraph_iota hmaps hstep hleftArgs
  have hrightIota : app graph right = (model.codeOf s₂ c₂).applyMinor model.toModel.level vps
      [zf|$(minorFamily (RecSlots.casesOf γ)) $(encode (tagOf s₂ c₂))]
      ((model.codeOf s₂ c₂).argMap graph vps rightArgs) :=
    hrightEntry ▸ recGraph_iota hmaps hstep hrightArgs
  cases model.large_target_separates hlarge hlevel vps (hleftTarget.trans hrightTarget.symm)
  have hagree := model.large_argAgree hdecl hrule ho hB
    (Inductive.SortLargeElim.singleton_of_eval_zero (hlarge s₁) ls hzero c₁).2
    vps hps block (fun _ h => h) hleftArgs hrightArgs
    (hleftTarget.trans hrightTarget.symm)
  have hmap {vargs : ZFSet}
      (hargs : vargs ∈ (model.codeOf s₁ c₁).argSet block vps)
      (htarget : (model.codeOf s₁ c₁).targetIndex vps vargs = key) :
      (model.codeOf s₁ c₁).argMap lift vps vargs =
        (model.codeOf s₁ c₁).argMap graph vps vargs :=
    (model.codeOf s₁ c₁).argMap_congr_of_predecessors vps vargs hargs
      fun predecessor hpredecessor => by
        have hblock := (model.codeOf s₁ c₁).predecessors_mem_block vps vargs hargs
          predecessor hpredecessor
        have hrelation := model.mem_largeAccessRel_of_predecessor vps hargs htarget
          predecessor hpredecessor
        rw [model.app_liftLargeAccessGraph vps hblock]
        exact ih (fst predecessor) (accSet_inv hkey _ (mem_image.mpr ⟨predecessor, hblock, rfl⟩)
          hrelation) hrelation _ (model.largeAccessEntry_mem vps hblock)
          (model.fst_largeAccessEntry vps _) predecessor hblock rfl
  rw [hleftIota, hrightIota, ← hmap hleftArgs hleftTarget, ← hmap hrightArgs hrightTarget,
    hlevel]
  exact CtorCode.applyMinor_zero_argMap_congr_of_argAgree _ block lift
    (fun key leftValue rightValue hleftValue hrightValue => by
      rw [model.app_liftLargeAccessGraph vps hleftValue,
        model.app_liftLargeAccessGraph vps hrightValue, fst_pair, fst_pair])
    vps _ hleftArgs hrightArgs hagree

noncomputable def recLeaf (s : Fin ι.nsorts) (l : Level 0) :
    Dom (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) :=
  fun γ => propVal (l.eval zeroNs) (app (model.recrGraph s γ) (model.recrState s γ))

theorem recLeaf_eq_proof (s : Fin ι.nsorts) (l : Level 0) (hl : l.eval zeroNs = 0)
    (γ : RecSlots ι s) :
    model.recLeaf s l γ = proof := by
  rw [recLeaf, hl, propVal_zero]

theorem recLeaf_mem (s : Fin ι.nsorts) (l : Level 0) (γ : RecSlots ι s)
    (hγ : γ ∈ Reachable Set.univ (model.recrTeleSem s l)) :
    model.recLeaf s l γ ∈ ε₂[γ]⟦ι.recrBody s⟧ := by
  rw [model.recrBody_denotes s l γ hγ]
  have hmaps := model.mapsTo (RecSlots.paramsOf γ)
  refine propVal_mem_propSet (recGraph_app_mem hmaps ?_)
  rw [dom_recGraph hmaps (model.recrStepSound s l γ hγ)]
  exact model.recrState_mem s l γ hγ

theorem recLeaf_iota
    (hdecl : SemDecls E₁ ε₁ zeroNs) (hrule : SemDeclRules E₁ ε₁ zeroNs)
    (ho : E₁.Ordered) (hB : I.WFStrong E₁)
    (s : Fin ι.nsorts) (l : Level 0)
    (hallowed : I.RecAllowed l) (γ : RecSlots ι s)
    (hγ : γ ∈ Reachable Set.univ (model.recrTeleSem s l))
    (c : Fin (ι.nctors s)) {vargs : ZFSet}
    (hargs : vargs ∈ (model.codeOf s c).argSet
      (model.toModel.block (RecSlots.paramsOf γ)) (RecSlots.paramsOf γ))
    (htarget : (model.codeOf s c).targetIndex (RecSlots.paramsOf γ) vargs =
      sortKey s.val (RecSlots.indicesOfSlots γ))
    (hmaj : RecSlots.majorOfSlots γ =
      propVal model.toModel.level (entryValue (tagOf s c) vargs)) :
    model.recLeaf s l γ =
      (model.codeOf s c).applyMinor model.toModel.level (RecSlots.paramsOf γ)
        (RecSlots.casesOf γ (Fin.encodeSigma ι.nctors ⟨s, c⟩))
        ((model.codeOf s c).argMap (model.recrGraph s γ) (RecSlots.paramsOf γ) vargs) := by
  have hmaps := model.mapsTo (RecSlots.paramsOf γ)
  have hstep := model.recrStepSound s l γ hγ
  have hstateMem := model.recrState_mem s l γ hγ
  have hentry :
      pair (sortKey s.val (RecSlots.indicesOfSlots γ)) (entryValue (tagOf s c) vargs) ∈
        model.toModel.block (RecSlots.paramsOf γ) := by
    have h := entry_mem_indSet hmaps hargs
    rwa [htarget] at h
  have hiota : app (model.recrGraph s γ)
      (pair (sortKey s.val (RecSlots.indicesOfSlots γ)) (entryValue (tagOf s c) vargs)) =
      (model.codeOf s c).applyMinor model.toModel.level (RecSlots.paramsOf γ)
        (RecSlots.casesOf γ (Fin.encodeSigma ι.nctors ⟨s, c⟩))
        ((model.codeOf s c).argMap (model.recrGraph s γ) (RecSlots.paramsOf γ) vargs) := by
    rw [
      show RecSlots.casesOf γ (Fin.encodeSigma ι.nctors ⟨s, c⟩) = [zf|$(minorFamily (RecSlots.casesOf γ)) $(encode (tagOf s c))] from by exact (app_minorFamily (RecSlots.casesOf γ) (Fin.encodeSigma ι.nctors ⟨s, c⟩)).symm,
      ← htarget]
    exact recGraph_iota hmaps hstep hargs
  by_cases hresult : l.eval zeroNs = 0
  · have hmem : app (model.recrGraph s γ)
        (pair (sortKey s.val (RecSlots.indicesOfSlots γ)) (entryValue (tagOf s c) vargs)) ∈
        fibreOp (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
          (pair (sortKey s.val (RecSlots.indicesOfSlots γ)) (entryValue (tagOf s c) vargs)) :=
      recGraph_app_mem hmaps (by rwa [dom_recGraph hmaps hstep])
    have hcoherent :
        fibreOp (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
          (pair (sortKey s.val (RecSlots.indicesOfSlots γ)) (entryValue (tagOf s c) vargs)) =
        fibreOp (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
          (model.recrState s γ) := by
      rw [recrCaseMotive, fibre_bundleMotive_propVal hentry,
        fibre_bundleMotive_propVal hstateMem]
      simp only [recrState, fst_pair, snd_pair]
      rw [← hmaj, model.propVal_recrMajorOf s l γ hγ]
    rw [hiota, hcoherent] at hmem
    rw [model.recLeaf_eq_proof s l hresult]
    exact (model.eq_proof_of_mem_fibre_motive s l γ hγ hresult hmem).symm
  rw [recLeaf, propVal_of_ne_zero hresult]
  by_cases hlevel : model.toModel.level = 0
  · rw [model.recGraph_congr_key hdecl hrule ho hB (hallowed.largeElim hresult) hlevel s l γ hγ
      hstateMem hentry (by rw [recrState, fst_pair, fst_pair])]
    exact hiota
  rw [recrState, show model.recrMajorOf s γ = entryValue (tagOf s c) vargs from by
    have h := model.propVal_recrMajorOf s l γ hγ
    rw [hmaj] at h
    simpa only [propVal_of_ne_zero hlevel] using h]
  exact hiota

theorem recLeaf_eq_recGraph_app
    {l : Level 0} {s s₁ : Fin ι.nsorts} (outer : RecSlots ι s)
    (houter : outer ∈ Reachable Set.univ (model.recrTeleSem s l))
    (child : RecSlots ι s₁)
    (hchild : child ∈ Reachable Set.univ (model.recrTeleSem s₁ l))
    (hparams : RecSlots.paramsOf child = RecSlots.paramsOf outer)
    (hmotives : RecSlots.motivesOf child = RecSlots.motivesOf outer)
    (hcases : RecSlots.casesOf child = RecSlots.casesOf outer)
    (predecessor : ZFSet)
    (hpredecessor : predecessor ∈ model.toModel.block (RecSlots.paramsOf outer))
    (hstate : model.recrState s₁ child = predecessor) :
    model.recLeaf s₁ l child = app (model.recrGraph s outer) predecessor := by
  by_cases hresult : l.eval zeroNs = 0
  · have hmaps := model.mapsTo (RecSlots.paramsOf outer)
    have hmem : app (model.recrGraph s outer) predecessor ∈
        fibreOp (model.recrCaseMotive (RecSlots.paramsOf child) (RecSlots.motivesOf child))
          (model.recrState s₁ child) := by
      rw [hparams, hmotives, hstate]
      exact recGraph_app_mem hmaps
        (by rwa [dom_recGraph hmaps (model.recrStepSound s l outer houter)])
    rw [model.recLeaf_eq_proof s₁ l hresult]
    exact (model.eq_proof_of_mem_fibre_motive s₁ l child hchild hresult hmem).symm
  rw [recLeaf, propVal_of_ne_zero hresult,
    show model.recrGraph s₁ child = model.recrGraph s outer from by
      rw [recrGraph, recrGraph, hparams, hmotives, hcases], hstate]

end StrongInductiveModel

end Metalean
