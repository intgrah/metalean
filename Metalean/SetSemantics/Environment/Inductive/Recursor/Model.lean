/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

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

namespace StrongInductiveModel

variable (model : StrongInductiveModel E₁ ε₁ I ls)

theorem recGraph_congr_key
    (hdecl : SemDecls E₁ ε₁ ![]) (hrule : SemDeclRules E₁ ε₁ ![])
    (hE : EnvWF E₁) (hB : InductiveWF E₁ I)
    (hsubsingleton : I.Subsingleton) (hlevel : model.toModel.level = 0)
    (s : Fin ι.nsorts) (l : Level 0) (γ : RecSlots ι s)
    (hγ : γ.valuation ∈ Reachable Set.univ (model.recrTeleSem s l))
    {left right : ZFSet}
    (hleft : left ∈ model.toModel.block (RecSlots.params γ))
    (hright : right ∈ model.toModel.block (RecSlots.params γ))
    (hkeys : fst left = fst right) :
    app (model.recrGraph s γ) left = app (model.recrGraph s γ) right := by
  let vps := γ.params
  let block := model.toModel.block vps
  let graph := model.recrGraph s γ
  let good := block.sep fun x => ∀ y ∈ block, fst x = fst y → app graph x = app graph y
  have hgood : good ⊆ block := fun _ h => (mem_sep.mp h).1
  have hmaps := model.mapsTo vps
  have hstep := model.recrStepSound s l γ hγ
  have hiota {s₁ : Fin ι.nsorts} {c : Fin (ι.nctors s₁)} {args : ZFSet}
      (hargs : args ∈ (model.codeOf s₁ c).argSet block vps) :
      app graph (entry ((model.codeOf s₁ c).targetIndex vps args) (tagOf s₁ c) args) =
        (model.codeOf s₁ c).applyMinor model.toModel.level graph vps
          [zf|$(minorFamily γ.cases) $(encode (tagOf s₁ c))]
          args :=
    recGraph_iota hmaps hstep hargs
  have hclosed : indOp model.toModel.codes vps good ⊆ good := by
    rintro current hcurrent
    obtain ⟨s₁, c₁, args₁, hargs₁, rfl⟩ := mem_indOp.mp hcurrent
    have hargs₁' := CtorCode.argSet_mono hgood _ vps hargs₁
    refine mem_sep.mpr ⟨entry_mem_indSet hmaps hargs₁', ?_⟩
    intro other hother hkeys
    change other ∈ indSet model.toModel.codes model.toModel.bound vps at hother
    rw [← indSet_unfold hmaps] at hother
    obtain ⟨s₂, c₂, args₂, hargs₂, rfl⟩ := mem_indOp.mp hother
    simp only [entry_eq, fst_pair] at hkeys
    change (model.codeOf s₁ c₁).targetIndex vps args₁ =
      (model.codeOf s₂ c₂).targetIndex vps args₂ at hkeys
    cases model.large_target_separates hsubsingleton vps hkeys
    have hagree := model.large_argAgree hdecl hrule hE hB
      (hsubsingleton.eligible s₁ c₁) vps (model.recrParamsReachable s l γ hγ)
      good hgood hargs₁ hargs₂ hkeys
    rw [hiota hargs₁', hiota hargs₂, hlevel]
    exact CtorCode.applyMinor_zero_congr_of_argAgree _ good block graph
      (fun key value₁ value₂ h₁ h₂ => (mem_sep.mp h₁).2 _ h₂ (by simp))
      vps _ hargs₁ hargs₂ hagree
  have hblock : block ⊆ good := lfp_least (fun _ h => lfp_subset (hgood h)) hclosed
  exact (mem_sep.mp (hblock hleft)).2 right hright hkeys

noncomputable def recLeaf (s : Fin ι.nsorts) (l : Level 0) :
    RecSlots ι s → ZFSet :=
  fun γ => propVal (l.eval ![]) (app (model.recrGraph s γ) (model.recrState s γ))

theorem recLeaf_eq_proof (s : Fin ι.nsorts) (l : Level 0) (hl : l.eval ![] = 0)
    (γ : RecSlots ι s) :
    model.recLeaf s l γ = proof := by
  rw [recLeaf, hl, propVal_zero]

theorem recLeaf_mem (s : Fin ι.nsorts) (l : Level 0) (γ : RecSlots ι s)
    (hγ : γ.valuation ∈ Reachable Set.univ (model.recrTeleSem s l)) :
    model.recLeaf s l γ ∈ ε₂[γ]⟦ι.recrBody s⟧ := by
  rw [model.recrBody_denotes s l γ hγ]
  have hmaps := model.mapsTo (RecSlots.params γ)
  refine propVal_mem_propSet ((recGraph_isApprox hmaps).app_mem ?_)
  rw [dom_recGraph hmaps (model.recrStepSound s l γ hγ)]
  exact model.recrState_mem s l γ hγ

theorem recLeaf_iota
    (hdecl : SemDecls E₁ ε₁ ![]) (hrule : SemDeclRules E₁ ε₁ ![])
    (hE : EnvWF E₁) (hB : InductiveWF E₁ I)
    (s : Fin ι.nsorts) (l : Level 0)
    (hallowed : I.RecAllowed ls l) (γ : RecSlots ι s)
    (hγ : γ.valuation ∈ Reachable Set.univ (model.recrTeleSem s l))
    (c : Fin (ι.nctors s)) {vargs : ZFSet}
    (hargs : vargs ∈ (model.codeOf s c).argSet
      (model.toModel.block (RecSlots.params γ)) (RecSlots.params γ))
    (htarget : (model.codeOf s c).targetIndex (RecSlots.params γ) vargs =
      sortKey s.val (encode (RecSlots.indices γ)))
    (hmaj : RecSlots.major γ =
      propVal model.toModel.level (entryValue (tagOf s c) vargs)) :
    model.recLeaf s l γ =
      (model.codeOf s c).applyMinor model.toModel.level (model.recrGraph s γ) (RecSlots.params γ)
        (RecSlots.cases γ (Fin.encodeSigma ι.nctors ⟨s, c⟩))
        vargs := by
  have hmaps := model.mapsTo (RecSlots.params γ)
  have hstep := model.recrStepSound s l γ hγ
  have hstateMem := model.recrState_mem s l γ hγ
  have hentry :
      pair (sortKey s.val (encode (RecSlots.indices γ))) (entryValue (tagOf s c) vargs) ∈
        model.toModel.block (RecSlots.params γ) := by
    have h := entry_mem_indSet hmaps hargs
    rwa [htarget] at h
  have hiota : app (model.recrGraph s γ)
      (pair (sortKey s.val (encode (RecSlots.indices γ))) (entryValue (tagOf s c) vargs)) =
      (model.codeOf s c).applyMinor model.toModel.level (model.recrGraph s γ) (RecSlots.params γ)
        (RecSlots.cases γ (Fin.encodeSigma ι.nctors ⟨s, c⟩))
        vargs := by
    rw [
      show RecSlots.cases γ (Fin.encodeSigma ι.nctors ⟨s, c⟩) = [zf|$(minorFamily (RecSlots.cases γ)) $(encode (tagOf s c))] from by exact (app_minorFamily (RecSlots.cases γ) (Fin.encodeSigma ι.nctors ⟨s, c⟩)).symm,
      ← htarget]
    exact recGraph_iota hmaps hstep hargs
  by_cases hresult : l.eval ![] = 0
  · have hmem : app (model.recrGraph s γ)
        (pair (sortKey s.val (encode (RecSlots.indices γ))) (entryValue (tagOf s c) vargs)) ∈
        fibreOp (model.recrCaseMotive (RecSlots.params γ) (RecSlots.motives γ))
          (pair (sortKey s.val (encode (RecSlots.indices γ))) (entryValue (tagOf s c) vargs)) :=
      (recGraph_isApprox hmaps).app_mem (by rwa [dom_recGraph hmaps hstep])
    have hcoherent :
        fibreOp (model.recrCaseMotive (RecSlots.params γ) (RecSlots.motives γ))
          (pair (sortKey s.val (encode (RecSlots.indices γ))) (entryValue (tagOf s c) vargs)) =
        fibreOp (model.recrCaseMotive (RecSlots.params γ) (RecSlots.motives γ))
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
  · rw [model.recGraph_congr_key hdecl hrule hE hB (hallowed.subsingleton hresult hlevel) hlevel s l γ hγ
      hstateMem hentry (by rw [recrState, fst_pair, fst_pair])]
    exact hiota
  rw [recrState, show model.recrMajorOf s γ = entryValue (tagOf s c) vargs from by
    have h := model.propVal_recrMajorOf s l γ hγ
    rw [hmaj] at h
    simpa [propVal_of_ne_zero hlevel] using h]
  exact hiota

theorem recLeaf_eq_recGraph_app
    {l : Level 0} {s s₁ : Fin ι.nsorts} (outer : RecSlots ι s)
    (houter : outer.valuation ∈ Reachable Set.univ (model.recrTeleSem s l))
    (indices : Slots (ι.nindices s₁)) (major : ZFSet)
    (hchild : (RecSlots.mk outer.params outer.motives outer.cases indices major).valuation ∈
      Reachable Set.univ (model.recrTeleSem s₁ l))
    (predecessor : ZFSet)
    (hpredecessor : predecessor ∈ model.toModel.block outer.params)
    (hstate : model.recrState s₁
      (RecSlots.mk outer.params outer.motives outer.cases indices major) = predecessor) :
    model.recLeaf s₁ l (RecSlots.mk outer.params outer.motives outer.cases indices major) =
      app (model.recrGraph s outer) predecessor := by
  by_cases hresult : l.eval ![] = 0
  · have hmem : app (model.recrGraph s outer) predecessor ∈
        fibreOp (model.recrCaseMotive outer.params outer.motives) predecessor :=
      (recGraph_isApprox (model.mapsTo outer.params)).app_mem
        (by rwa [dom_recGraph (model.mapsTo outer.params) (model.recrStepSound s l outer houter)])
    rw [model.recLeaf_eq_proof s₁ l hresult]
    rw [← hstate] at hmem
    simpa [hstate] using
      (model.eq_proof_of_mem_fibre_motive s₁ l _ hchild hresult hmem).symm
  rw [recLeaf, propVal_of_ne_zero hresult, hstate]
  rfl

end StrongInductiveModel

end Metalean
