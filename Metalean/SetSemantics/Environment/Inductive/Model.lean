/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Constructor
import Metalean.SetSemantics.InductiveComputation
import Metalean.Typing.Inductive
import Metalean.Typing.InstLevel

/-! # Semantic models for inductive blocks -/

@[expose] public section

universe u

namespace Metalean

open ZFSet

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}

structure StrongInductiveModel
    (E₁ : Env ζ₁) (ε₁ : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (ls : Fin ι.nlevels → Level 0) :
    Type (u + 1) where
  params : StrongTeleModel E₁ ε₁ ![] I.params{ls}
  indicesBound (s : Fin ι.nsorts) : Nat
  indices (s : Fin ι.nsorts) :
    StrongTeleExtension E₁ ε₁ ![] params (I.indices s){ls} (indicesBound s)
  ctors (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    StrongCtorModel E₁ ε₁ I ls (I.ctors s c) params

theorem InductiveWF.model (hdecl : SemDecls E₁ ε₁ ![])
    (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁) (hB : InductiveWF E₁ I) :
    Nonempty (StrongInductiveModel E₁ ε₁ I ls) := by
  have ⟨params⟩ := (hB.params.instLevel ls fun _ => trivial).model hdecl hrule hE
  let indices (s) := Classical.choice
    ((hB.indices s).instLevel ls (fun _ => trivial) |>.modelExtension hdecl hrule hE params)
  exact ⟨params, fun s => (indices s).1, fun s => (indices s).2,
    fun s c => Classical.choice ((hB.ctors s c).model hdecl hrule hE params (indices s).2)⟩

namespace StrongInductiveModel

variable (model : StrongInductiveModel E₁ ε₁ I ls)

noncomputable abbrev codeOf (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) :
    CtorCode ι.nparams :=
  (model.ctors s c).source.code

noncomputable def ordinaryOf (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vargs : ZFSet) :
    Slots (ι.nparams + (ι.ctors s c).nfields) :=
  (model.ctors s c).source.ordinary.sem.values vps vargs

def ctorBound : (s : Fin ι.nsorts) × Fin (ι.nctors s) → Nat
  | ⟨s, c⟩ => (model.ctors s c).bound

noncomputable def targetBound : (s : Fin ι.nsorts) × Fin (ι.nctors s) → Nat
  | ⟨s, c⟩ => Classical.choose (model.ctors s c).targetBounded

noncomputable def bound : Nat :=
  max (Finset.univ.sup (ctorBound model)) (Finset.univ.sup (targetBound model))

theorem codeOf_domsIn (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (codeOf model s c).DomsIn (bound model) := by
  have hle : (model.ctors s c).bound ≤ bound model :=
    (Finset.le_sup (f := ctorBound model) (Finset.mem_univ ⟨s, c⟩)).trans (Nat.le_max_left _ _)
  exact (model.ctors s c).source.codeDomsIn.mono hle

theorem codeOf_localDoms {level : Nat} (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (hlevel : I.level{ls}.eval ![] = level + 1) :
    (codeOf model s c).DomsIn level :=
  (model.ctors s c).localDoms level hlevel

theorem codeOf_targetIndex_mem_type (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots ι.nparams) (vargs : ZFSet) :
    (codeOf model s c).targetIndex γ vargs ∈ U_ (bound model) := by
  have hle : Classical.choose (model.ctors s c).targetBounded ≤ bound model :=
    (Finset.le_sup (f := targetBound model) (Finset.mem_univ ⟨s, c⟩)).trans
      (Nat.le_max_right _ _)
  exact (model.ctors s c).source.code_targetIndex_mem_type
    (fun γ i => type_mono hle (Classical.choose_spec (model.ctors s c).targetBounded γ i)) γ vargs

def paramsSem : SemTele 0 ι.nparams := model.params.sem

def indicesSem (s : Fin ι.nsorts) :
    SemTele ι.nparams (ι.nparams + ι.nindices s) :=
  (model.indices s).sem

def sortSem (s : Fin ι.nsorts) :
    SemTele 0 (ι.nparams + ι.nindices s) :=
  paramsSem model ++ indicesSem model s

noncomputable def targetValues (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Slots (ι.nparams + (ι.ctors s c).nfields) →
      Fin (ι.nindices s) → ZFSet :=
  (model.ctors s c).source.targetValues

noncomputable abbrev toModel : InductiveModel ι where
  paramsSem := model.paramsSem
  codes := model.codeOf
  bound := U_ model.bound
  level := I.level{ls}.eval ![]
  ordinaryOf := model.ordinaryOf
  indicesSem := model.indicesSem
  targetValues := model.targetValues

theorem mapsTo (vps : Slots ι.nparams) :
    Set.MapsTo (indOp model.toModel.codes vps) (Set.Iic model.toModel.bound)
      (Set.Iic model.toModel.bound) :=
  indOp_mapsTo (codeOf_domsIn model) (codeOf_targetIndex_mem_type model) vps

noncomputable def ctorArgs
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vfds : Slots (ι.ctors s c).nfields)
    (vrecFds : Slots (ι.ctors s c).nrecFields) : ZFSet :=
  (model.codeOf s c).pack (model.toModel.block vps) model.toModel.level
    vps vfds vrecFds

noncomputable def ctorResult
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vfds : Slots (ι.ctors s c).nfields)
    (vrecFds : Slots (ι.ctors s c).nrecFields) : ZFSet :=
  propVal model.toModel.level
    (entryValue (tagOf s c) (model.ctorArgs s c vps vfds vrecFds))

theorem ordinaryOf_castLE (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vargs : ZFSet) (param : Fin ι.nparams) :
    ordinaryOf model s c vps vargs (param.castLE (Nat.le_add_right _ _)) = vps param :=
  (model.ctors s c).source.ordinary.sem.values_base vps vargs param

theorem codeOf_targetIndex (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vargs : ZFSet) :
    (codeOf model s c).targetIndex vps vargs =
      sortKey s.val (encode (targetValues model s c (ordinaryOf model s c vps vargs))) := rfl

theorem ordinaryOf_reachable (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.params.sem)
    (vargs : ZFSet)
    (hargs : vargs ∈ (codeOf model s c).argSet
      (model.toModel.block vps) vps) :
    ordinaryOf model s c vps vargs ∈
      Reachable (Reachable Set.univ model.params.sem)
        (model.ctors s c).source.ordinary.sem := by
  exact Reachable.mono (SemTele.mem_sigma.mp hargs).1
    (Set.singleton_subset_iff.mpr hps)

theorem targetRealizes (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.params.sem)
    (vargs : ZFSet)
    (hargs : vargs ∈ (codeOf model s c).argSet
      (model.toModel.block vps) vps)
    (index : Fin (ι.nindices s)) :
    ε₁[ordinaryOf model s c vps vargs]⟦((I.ctors s c).targetIndices index){ls}⟧ =
      targetValues model s c (ordinaryOf model s c vps vargs) index :=
  (model.ctors s c).source.targetValues_denotes _
    (Reachable.append (model.ordinaryOf_reachable s c vps hps vargs hargs)) index

theorem fieldsRealize (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.params.sem)
    (vargs : ZFSet)
    (hargs : vargs ∈ (codeOf model s c).argSet
      (model.toModel.block vps) vps) :
    ε₁[![]] ⊨ ordinaryOf model s c vps vargs :
      (I.params ++ (I.ctors s c).ordinaryTele){ls} := by
  rw [Ctx.instL_append]
  exact (model.ctors s c).source.ordinary.semCtx _
    (model.ordinaryOf_reachable s c vps hps vargs hargs)

theorem recursiveField_apply
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields)
    (γ : Slots (ι.nparams + (ι.ctors s c).nfields +
      (ι.ctors s c).recursiveArity f)) :
    model.toModel.sortValue ((ι.ctors s c).recursiveTarget f)
      (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
      (ε₁[γ]⟦((I.ctors s c).recursive f).indices{ls} ·⟧) =
      propSet model.toModel.level (fibreOp (model.toModel.block
        fun param => γ (param.castLE (by omega)))
        ((StrongRecursiveFieldSource.code ((I.ctors s c).recursive f)
          ((model.ctors s c).source.recursive f)).index γ)) := by
  simp [InductiveModel.sortValue]

theorem realizes
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    model.toModel.Interprets ε₂ ![] (I.map pre.sigs) ls where
  level_eq := rfl
  params := by
    simpa [paramsSem, Inductive.map] using model.params.realizes.mapInst pre hatoms
  indicesRealizes s := by
    simpa [paramsSem, indicesSem, Inductive.map] using
      (model.indices s).realizes.mapInst pre hatoms
  ordinaryOf_castLE := model.ordinaryOf_castLE
  targetIndex_eq := model.codeOf_targetIndex
  targetRealizes s c vps hps vargs hargs index := by
    simpa [Inductive.map, Ctor.map] using (Expr.denote_map pre.sigs hatoms _ _).trans
      (targetRealizes model s c vps hps vargs hargs index)
  fieldsRealize s c vps hps vargs hargs v := by
    have hv := fieldsRealize model s c vps hps vargs hargs v
    rw [← Expr.denote_map pre.sigs hatoms, ← Ctx.get_map] at hv
    simpa [Inductive.map] using hv
  bounded := model.mapsTo

theorem ctorArgs_mem
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams)
    (vfds : Slots (ι.ctors s c).nfields)
    (hfields : Fin.append vps vfds ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem)
    (vrecFds : Fin (ι.ctors s c).nrecFields → ZFSet)
    (hrecFields : ∀ f, vrecFds f ∈ typedRecFieldSet
      (StrongRecursiveFieldSource.code
        ((I.ctors s c).recursive f)
        ((model.ctors s c).source.recursive f)).tele
      (StrongRecursiveFieldSource.code
        ((I.ctors s c).recursive f)
        ((model.ctors s c).source.recursive f)).index
      (model.toModel.block vps) model.toModel.level (Fin.append vps vfds)) :
    model.ctorArgs s c vps vfds vrecFds ∈
        (model.codeOf s c).argSet (model.toModel.block vps) vps ∧
      model.ordinaryOf s c vps (model.ctorArgs s c vps vfds vrecFds) =
        Fin.append vps vfds := by
  constructor
  · exact (model.codeOf s c).pack_mem hfields hrecFields
  · exact (model.codeOf s c).values_pack _ _ _ _ _

theorem ctorResult_mem_sortValue
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vfds : Slots (ι.ctors s c).nfields)
    (hfields : Fin.append vps vfds ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem)
    (vrecFds : Slots (ι.ctors s c).nrecFields)
    (hrecFields : ∀ f, vrecFds f ∈ typedRecFieldSet
      ((model.ctors s c).source.code.recursive f).tele
      ((model.ctors s c).source.code.recursive f).index
      (model.toModel.block vps) model.toModel.level (Fin.append vps vfds)) :
    model.ctorResult s c vps vfds vrecFds ∈ model.toModel.sortValue s vps
      (model.targetValues s c (Fin.append vps vfds)) := by
  have ⟨hargs, hvalues⟩ := model.ctorArgs_mem s c vps vfds hfields vrecFds hrecFields
  have hentry := entry_mem_indSet (model.mapsTo vps) hargs
  rw [model.codeOf_targetIndex, hvalues] at hentry
  exact propVal_mem_propSet (entryValue_mem_fibre hentry)

theorem large_target_separates
    (hsubsingleton : I.Subsingleton)
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
  obtain rfl : c₁ = c₂ := hsubsingleton.unique s₁ c₁ c₂
  rfl

theorem ordinarySemCtx
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (slots : Slots (ι.nparams + (ι.ctors s c).nfields))
    (hslots : slots ∈ Reachable {vps} (model.ctors s c).source.ordinary.sem) :
    ε₁[![]] ⊨ slots : (I.params ++ (I.ctors s c).ordinaryTele){ls} :=
  Ctx.instL_append .. ▸ (model.ctors s c).source.ordinary.semCtx slots
    (Reachable.mono hslots (Set.singleton_subset_iff.mpr hps))

theorem ordinary_eq_proof
    (hdecl : SemDecls E₁ ε₁ ![]) (hrule : SemDeclRules E₁ ε₁ ![])
    (hE : EnvWF E₁) (hB : InductiveWF E₁ I)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (slots : Slots (ι.nparams + (ι.ctors s c).nfields))
    (hslots : slots ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem)
    (f : Fin (ι.ctors s c).nfields)
    (hzero : ((I.ctors s c).ordinary f).level{ls}.eval ![] = 0) :
    slots (Fin.natAdd ι.nparams f) = proof := by
  have hrealises := model.ordinarySemCtx s c vps hps slots hslots
  have hsorted := (soundness hdecl hrule hE
    (((hB.ctors s c).ordinaryTele_get f).instLevel ls) slots hrealises).mem
  have hslot := hrealises (Fin.natAdd ι.nparams f)
  simp only [Ctx.get_instL, Expr.inst_sort, Expr.denote] at hsorted hslot
  rw [hzero] at hsorted
  exact mem_verum.mp (eq_verum_of_mem hsorted hslot ▸ hslot)

theorem large_ordinary_eq
    (hdecl : SemDecls E₁ ε₁ ![]) (hrule : SemDeclRules E₁ ε₁ ![])
    (hE : EnvWF E₁) (hB : InductiveWF E₁ I)
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
    model.ordinaryOf s c vps leftArgs = model.ordinaryOf s c vps rightArgs := by
  let ordinary := (model.ctors s c).source.ordinary.sem
  have hleftReach := (SemTele.mem_sigma.mp hleftArgs).1
  have hrightReach := (SemTele.mem_sigma.mp hrightArgs).1
  have hleftDenotes := model.targetRealizes s c vps hps leftArgs
    (CtorCode.argSet_mono happroximation (model.codeOf s c) vps hleftArgs)
  have hrightDenotes := model.targetRealizes s c vps hps rightArgs hrightArgs
  have htargetValues : model.targetValues s c (model.ordinaryOf s c vps leftArgs) =
      model.targetValues s c (model.ordinaryOf s c vps rightArgs) :=
    Encode.injective (congrArg Prod.snd (sortKey_injective (by
      rwa [← model.codeOf_targetIndex s c vps leftArgs,
        ← model.codeOf_targetIndex s c vps rightArgs])))
  funext slot
  cases slot using Fin.addCases with
  | left param =>
    exact (model.ordinaryOf_castLE s c vps leftArgs param).trans
      (model.ordinaryOf_castLE s c vps rightArgs param).symm
  | right f =>
    cases heligible.ordinary f with
    | inl hzero =>
      have hzero : ((I.ctors s c).ordinary f).level{ls}.eval ![] = 0 := by
        simp [hzero]
      have heq (vargs : ZFSet) (hreach : ordinary.values vps vargs ∈
          Reachable {vps} (model.ctors s c).source.ordinary.sem) :=
        model.ordinary_eq_proof hdecl hrule hE hB s c vps hps _ hreach f hzero
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

end StrongInductiveModel

end Metalean
