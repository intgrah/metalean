/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Recursor.Telescope
import Metalean.SetSemantics.InductiveComputation
import Metalean.Syntax.Inductive.LargeElimination
import Metalean.Strong.Inductive
import Metalean.Strong.InstLevel

@[expose] public section

universe u

namespace Metalean.StrongInductiveModel

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  (model : StrongInductiveModel E₁ ε₁ I ls)

noncomputable def largeAccessDom (vps : Slots ι.nparams) : ZFSet :=
  image fst (model.toModel.block vps)

noncomputable def largeAccessRel (vps : Slots ι.nparams) : ZFSet :=
  image (fun edge => pair (fst (fst edge)) (fst (snd edge)))
    (blockPredecessorRel (model.toModel.block vps) vps model.toModel.codes)

theorem large_target_separates
    (hlarge : I.LargeElim) (hlevel : model.toModel.level = 0)
    (vps : Slots ι.nparams)
    {s₁ s₂ : Fin ι.nsorts} {c₁ : Fin (ι.nctors s₁)} {c₂ : Fin (ι.nctors s₂)}
    {leftArgs rightArgs : ZFSet}
    (htarget : (model.codeOf s₁ c₁).targetIndex vps leftArgs =
      (model.codeOf s₂ c₂).targetIndex vps rightArgs) :
    (⟨s₁, c₁⟩ : (s : Fin ι.nsorts) × Fin (ι.nctors s)) = ⟨s₂, c₂⟩ := by
  have hsortKey : sortKey s₁.val
      (encode (model.targetValues s₁ c₁ (model.ordinaryOf s₁ c₁ vps leftArgs))) =
      sortKey s₂.val
        (encode (model.targetValues s₂ c₂ (model.ordinaryOf s₂ c₂ vps rightArgs))) := by
    rwa [← model.codeOf_targetIndex s₁ c₁ vps leftArgs,
      ← model.codeOf_targetIndex s₂ c₂ vps rightArgs]
  obtain rfl : s₁ = s₂ := Fin.ext (congrArg Prod.fst (sortKey_injective hsortKey))
  have hone := (Inductive.SortLargeElim.singleton_of_eval_zero (hlarge s₁) ls hlevel c₁).1
  obtain rfl : c₁ = c₂ := Fin.ext (by omega)
  rfl

theorem eq_pair_fst_snd_of_mem_blockPredecessorRel {n m : Nat} {nctors : Fin m → Nat}
    {block : ZFSet} {γ : Slots n} (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    {edge : ZFSet} (hedge : edge ∈ blockPredecessorRel block γ codes) :
    edge = [zf|(edge.1, edge.2)] := by
  have ⟨edges, hedges, hedge⟩ := mem_sUnion.mp hedge
  obtain ⟨_, _, _, _, rfl⟩ := mem_tagGraph.mp hedges
  obtain ⟨_, _, rfl⟩ := mem_image.mp hedge
  simp

noncomputable def largeAccessEntry (vps : Slots ι.nparams) (key : ZFSet) : ZFSet :=
  [zf|(key, $(Classical.epsilon (· ∈ fibreOp (model.toModel.block vps) key)))]

theorem largeAccessEntry_mem (vps : Slots ι.nparams) {current : ZFSet}
    (hcurrent : current ∈ model.toModel.block vps) :
    model.largeAccessEntry vps (fst current) ∈ model.toModel.block vps := by
  refine mem_fibre.mp (Classical.epsilon_spec ?_)
  have hcurrentOp := hcurrent
  change current ∈ indSet model.toModel.codes model.toModel.bound vps at hcurrentOp
  rw [← indSet_unfold (model.mapsTo vps)] at hcurrentOp
  have ⟨s, c, vargs, _, heq⟩ := mem_indOp.mp hcurrentOp
  rw [← heq] at hcurrent ⊢
  rw [entry_eq, fst_pair]
  exact ⟨entryValue (tagOf s c) vargs, entryValue_mem_fibre hcurrent⟩

@[simp] theorem fst_largeAccessEntry (vps : Slots ι.nparams) (key : ZFSet) :
    fst (model.largeAccessEntry vps key) = key := by
  simp [largeAccessEntry]

noncomputable def liftLargeAccessGraph (vps : Slots ι.nparams) (graph : ZFSet) : ZFSet :=
  map (fun entry => app graph (model.largeAccessEntry vps (fst entry))) (model.toModel.block vps)

theorem app_liftLargeAccessGraph (vps : Slots ι.nparams) {graph entry : ZFSet}
    (hentry : entry ∈ model.toModel.block vps) :
    app (model.liftLargeAccessGraph vps graph) entry =
      app graph (model.largeAccessEntry vps (fst entry)) := by
  rw [liftLargeAccessGraph, app_map hentry]

theorem ordinarySemCtx
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (slots : Slots (ι.nparams + (ι.ctors s c).nfields))
    (hslots : slots ∈ Reachable {vps} (model.ctors s c).source.ordinary.sem) :
    ε₁[zeroNs] ⊨ slots : Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele) :=
  Ctx.instL_append .. ▸ (model.ctors s c).source.ordinary.semCtx slots
    (Reachable.mono hslots (Set.singleton_subset_iff.mpr hps))

theorem ordinary_eq_proof
    (hdecl : SemDecls E₁ ε₁ zeroNs) (hrule : SemDeclRules E₁ ε₁ zeroNs)
    (ho : E₁.Ordered) (hB : I.WFStrong E₁)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (slots : Slots (ι.nparams + (ι.ctors s c).nfields))
    (hslots : slots ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem)
    (f : Fin (ι.ctors s c).nfields)
    (hzero : (((I.ctors s c).ordinary f).level.inst ls).eval zeroNs = 0) :
    slots (Fin.natAdd ι.nparams f) = proof := by
  have hrealises := model.ordinarySemCtx s c vps hps slots hslots
  have hsorted := (soundness hdecl hrule ho
    (((hB.ctors s c).ordinaryTele_get f).instLevel ls) slots hrealises).mem
  have hslot := hrealises (Fin.natAdd ι.nparams f)
  simp only [Ctx.get_instL, Expr.instL, Expr.denote] at hsorted hslot
  rw [hzero] at hsorted
  exact mem_verum.mp (eq_verum_of_mem hsorted hslot ▸ hslot)

theorem large_argAgree
    (hdecl : SemDecls E₁ ε₁ zeroNs) (hrule : SemDeclRules E₁ ε₁ zeroNs)
    (ho : E₁.Ordered) (hB : I.WFStrong E₁)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (heligible : (I.ctors s c).Eligible I.level)
    (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (approximation : ZFSet)
    (happroximation : approximation ⊆ model.toModel.block vps)
    {leftArgs rightArgs : ZFSet}
    (hleftArgs : leftArgs ∈ (model.codeOf s c).argSet
      approximation vps)
    (hrightArgs : rightArgs ∈ (model.codeOf s c).argSet
      (model.toModel.block vps) vps)
    (htarget : (model.codeOf s c).targetIndex vps leftArgs =
      (model.codeOf s c).targetIndex vps rightArgs) :
    (model.codeOf s c).ArgAgree leftArgs rightArgs := by
  let ordinary := (model.ctors s c).source.ordinary.sem
  let rest := model.recursiveRest s c
  have hleftReach := SemTele.reachable_values hleftArgs (Set.mem_singleton vps)
  have hrightReach := SemTele.reachable_values hrightArgs (Set.mem_singleton vps)
  have hleftTail := CtorCode.tail_mem_argSet hleftArgs
  have hrightTail := CtorCode.tail_mem_argSet hrightArgs
  have hleftDenotes := model.targetRealizes s c vps hps leftArgs
    (CtorCode.argSet_mono happroximation (model.codeOf s c) vps hleftArgs)
  have hrightDenotes := model.targetRealizes s c vps hps rightArgs hrightArgs
  have htargetValues : model.targetValues s c (model.ordinaryOf s c vps leftArgs) =
      model.targetValues s c (model.ordinaryOf s c vps rightArgs) :=
    Encode.injective (congrArg Prod.snd (sortKey_injective (by
      rwa [← model.codeOf_targetIndex s c vps leftArgs,
        ← model.codeOf_targetIndex s c vps rightArgs])))
  have hfields : model.ordinaryOf s c vps leftArgs =
      model.ordinaryOf s c vps rightArgs := by
    funext slot
    cases slot using Fin.addCases with
    | left param =>
      exact (model.ordinaryOf_castLE s c vps leftArgs param).trans
        (model.ordinaryOf_castLE s c vps rightArgs param).symm
    | right f =>
      cases heligible.ordinary f with
      | inl hzero =>
        have hzero : (((I.ctors s c).ordinary f).level.inst ls).eval zeroNs = 0 := by
          simp [hzero]
        have heq (vargs : ZFSet) (hreach : ordinary.values vps vargs ∈
            Reachable {vps} (model.ctors s c).source.ordinary.sem) :=
          model.ordinary_eq_proof hdecl hrule ho hB s c vps hps _ hreach f hzero
        exact (heq leftArgs hleftReach).trans (heq rightArgs hrightReach).symm
      | inr hindex =>
        have ⟨index, hindex⟩ := hindex
        have hvar : (I.ctors s c).targetIndices index =
            .var (Fin.natAdd ι.nparams f) := by
          apply Expr.eq_var_of_isVar
          simpa using hindex
        have hleftValue := hleftDenotes index
        have hrightValue := hrightDenotes index
        rw [hvar] at hleftValue hrightValue
        exact hleftValue.trans ((congrFun htargetValues index).trans hrightValue.symm)
  rw [← show ordinary.values vps leftArgs = ordinary.values vps rightArgs from hfields]
    at hrightTail
  exact CtorCode.argAgree_prependOrdinary ordinary rest vps
    (CtorCode.argAgree_prependRecursive (model.ctors s c).source.recursiveCodes
      (StrongCtorSource.targetIndex (model.ctors s c).target)
      (model.toModel.block vps) (model.ordinaryOf s c vps leftArgs)
      (CtorCode.argSet_mono happroximation rest (model.ordinaryOf s c vps leftArgs) hleftTail)
      hrightTail)
    hfields

theorem large_key_accessible
    (hdecl : SemDecls E₁ ε₁ zeroNs) (hrule : SemDeclRules E₁ ε₁ zeroNs)
    (ho : E₁.Ordered) (hB : I.WFStrong E₁)
    (hlarge : I.LargeElim) (hlevel : model.toModel.level = 0)
    (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (entry : ZFSet) (hentry : entry ∈ model.toModel.block vps) :
    fst entry ∈ accSet (model.largeAccessDom vps) (model.largeAccessRel vps) := by
  let block := model.toModel.block vps
  let accessible := accSet (model.largeAccessDom vps) (model.largeAccessRel vps)
  let approximation := block.sep fun entry => fst entry ∈ accessible
  have happroximation : approximation ⊆ block := fun _ hentry =>
    (mem_sep.mp hentry).1
  have hblock : block ⊆ approximation := by
    refine lfp_least (fun _ hentry => lfp_subset (happroximation hentry))
      fun current hcurrent => ?_
    have ⟨s₁, c₁, vargs, hargs, hcurrentEq⟩ := mem_indOp.mp hcurrent
    have hcurrentBlock : current ∈ block := by
      change current ∈ indSet model.toModel.codes model.toModel.bound vps
      rw [← indSet_unfold (model.mapsTo vps)]
      exact mem_indOp.mpr ⟨s₁, c₁, vargs,
        CtorCode.argSet_mono happroximation _ vps hargs, hcurrentEq⟩
    refine mem_sep.mpr ⟨hcurrentBlock, accSet_intro
      (mem_image.mpr ⟨current, hcurrentBlock, rfl⟩) fun predecessor _ hedge => ?_⟩
    have ⟨rawEdge, hrawEdge, hedgeEq⟩ := mem_image.mp hedge
    have hrawPair := eq_pair_fst_snd_of_mem_blockPredecessorRel
      model.toModel.codes hrawEdge
    rw [hrawPair] at hrawEdge hedgeEq
    have ⟨s₂, c₂, edgeArgs, hedgeArgs, hrawPredecessor, hrawCurrent⟩ :=
      mem_blockPredecessorRel.mp hrawEdge
    have ⟨hkeyLeft, hkeyRight⟩ : fst (fst rawEdge) = predecessor ∧
        fst (snd rawEdge) = fst current := by
      simpa using pair_inj.mp hedgeEq
    have htarget : (model.codeOf s₁ c₁).targetIndex vps vargs =
        (model.codeOf s₂ c₂).targetIndex vps edgeArgs := by
      rw [hrawCurrent, ← hcurrentEq, entry_eq, entry_eq, fst_pair, fst_pair] at hkeyRight
      exact hkeyRight.symm
    cases model.large_target_separates hlarge hlevel vps htarget
    have hagree := model.large_argAgree hdecl hrule ho hB
      (Inductive.SortLargeElim.singleton_of_eval_zero (hlarge s₁) ls hlevel c₁).2
      vps hps approximation happroximation hargs (by simpa using hedgeArgs) htarget
    have ⟨recovered, hrecovered, hrecoveredKey⟩ :=
      (model.codeOf s₁ c₁).predecessor_key_recover
        approximation block vps hargs (by simpa using hedgeArgs)
        hagree hrawPredecessor
    rw [← hkeyLeft, ← hrecoveredKey]
    exact (mem_sep.mp ((model.codeOf s₁ c₁).predecessors_mem_block vps vargs hargs
      recovered hrecovered)).2
  exact (mem_sep.mp (hblock hentry)).2

end Metalean.StrongInductiveModel
