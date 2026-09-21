/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Constructor

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
  tele : BlockTeleModels E₁ ls ε₁ I
  ctors (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    StrongCtorModel E₁ ε₁ I ls (I.ctors s c) tele.params

theorem Inductive.WF.model
    (hdecl : SemDecls E₁ ε₁ zeroNs)
    (hrule : SemDeclRules E₁ ε₁ zeroNs) (ho : E₁.Ordered)
    (hB : I.WF E₁) :
    Nonempty (StrongInductiveModel E₁ ε₁ I ls) :=
  have ⟨tele⟩ := hB.teleModels hdecl hrule ho
  ⟨⟨tele, fun s c => Classical.choice
    ((hB.ctors s c).model hdecl hrule ho tele.params (tele.indices s))⟩⟩

namespace StrongInductiveModel

variable (model : StrongInductiveModel E₁ ε₁ I ls)

noncomputable def codeOf (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) :
    CtorCode ι.nparams :=
  (model.ctors s c).source.code
    (StrongCtorSource.targetIndex (model.ctors s c).target)

noncomputable def recursiveRest (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    CtorCode (ι.nparams + (ι.ctors s c).nfields) :=
  CtorCode.prependRecursive (ι.ctors s c).nrecFields (model.ctors s c).source.recursiveCodes
    (.target (StrongCtorSource.targetIndex (model.ctors s c).target))

theorem codeOf_eq (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    model.codeOf s c =
      CtorCode.prependOrdinary (model.ctors s c).source.ordinary.sem (model.recursiveRest s c) :=
  rfl

noncomputable def ordinaryOf (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vargs : ZFSet) :
    Slots (ι.nparams + (ι.ctors s c).nfields) :=
  (model.ctors s c).source.ordinary.sem.values vps vargs

def ctorBound : (s : Fin ι.nsorts) × Fin (ι.nctors s) → Nat
  | ⟨s, c⟩ => (model.ctors s c).bound

noncomputable def targetBound : (s : Fin ι.nsorts) × Fin (ι.nctors s) → Nat
  | ⟨s, c⟩ => Classical.choose (model.ctors s c).target.bounded

noncomputable def bound : Nat :=
  max (Finset.univ.sup (ctorBound model)) (Finset.univ.sup (targetBound model))

theorem codeOf_domsIn (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (codeOf model s c).DomsIn (bound model) := by
  have hle : (model.ctors s c).bound ≤ bound model :=
    (Finset.le_sup (f := ctorBound model) (Finset.mem_univ ⟨s, c⟩)).trans (Nat.le_max_left _ _)
  exact (model.ctors s c).source.codeDomsIn
    (StrongCtorSource.targetIndex (model.ctors s c).target) |>.mono hle

theorem codeOf_localDoms {level : Nat} (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (hlevel : (I.level.inst ls).eval zeroNs = level + 1) :
    (codeOf model s c).DomsIn level :=
  (model.ctors s c).localDoms level hlevel

theorem codeOf_targetIndex_mem_type (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots ι.nparams) (vargs : ZFSet) :
    (codeOf model s c).targetIndex γ vargs ∈ U_ (bound model) :=
  (model.ctors s c).source.code_targetIndex_mem_type (model.ctors s c).target
    ((Finset.le_sup (f := targetBound model) (Finset.mem_univ (Sigma.mk s c))).trans
      (Nat.le_max_right _ _)) γ vargs

def paramsSem : SemTele 0 ι.nparams := model.tele.params.sem

def indicesSem (s : Fin ι.nsorts) :
    SemTele ι.nparams (ι.nparams + ι.nindices s) :=
  (model.tele.indices s).sem

def sortSem (s : Fin ι.nsorts) :
    SemTele 0 (ι.nparams + ι.nindices s) :=
  paramsSem model ++ indicesSem model s

def targetValues (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Slots (ι.nparams + (ι.ctors s c).nfields) →
      Fin (ι.nindices s) → ZFSet :=
  (model.ctors s c).target.values

noncomputable abbrev toModel : InductiveModel ι where
  paramsSem := model.paramsSem
  codes := model.codeOf
  bound := U_ model.bound
  level := (I.level.inst ls).eval zeroNs
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
  let fieldSlots := Fin.append vps vfds
  (model.ctors s c).source.ordinary.sem.pack fieldSlots
    (CtorCode.packRecursive (model.toModel.block vps)
      (model.ctors s c).source.recursiveCodes
      model.toModel.level fieldSlots vrecFds proof)

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
      sortKey s.val (encode (targetValues model s c (ordinaryOf model s c vps vargs))) := by
  rw [codeOf, StrongCtorSource.code, SemTele.targetIndex_prependOrdinary,
    CtorCode.targetIndex_prependRecursive]
  rfl

theorem ordinaryOf_reachable (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.tele.params.sem)
    (vargs : ZFSet)
    (hargs : vargs ∈ (codeOf model s c).argSet
      (model.toModel.block vps) vps) :
    ordinaryOf model s c vps vargs ∈
      Reachable (Reachable Set.univ model.tele.params.sem)
        (model.ctors s c).source.ordinary.sem := by
  have hargs₁ : vargs ∈
      (CtorCode.prependOrdinary (model.ctors s c).source.ordinary.sem
        (model.recursiveRest s c)).argSet (model.toModel.block vps) vps := hargs
  exact Reachable.mono (SemTele.reachable_values hargs₁ (Set.mem_singleton vps))
    (Set.singleton_subset_iff.mpr hps)

theorem targetRealizes (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.tele.params.sem)
    (vargs : ZFSet)
    (hargs : vargs ∈ (codeOf model s c).argSet
      (model.toModel.block vps) vps)
    (index : Fin (ι.nindices s)) :
    ε₁[ordinaryOf model s c vps vargs]⟦Expr.instL ls ((I.ctors s c).targetIndices index)⟧ =
      targetValues model s c (ordinaryOf model s c vps vargs) index :=
  (model.ctors s c).target.denotes _
    (Reachable.append (model.ordinaryOf_reachable s c vps hps vargs hargs)) index

theorem fieldsRealize (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.tele.params.sem)
    (vargs : ZFSet)
    (hargs : vargs ∈ (codeOf model s c).argSet
      (model.toModel.block vps) vps) :
    ε₁[zeroNs] ⊨ ordinaryOf model s c vps vargs :
      Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele) := by
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
      (ε₁[γ]⟦((I.ctors s c).recursive f).indices · |>.instL ls⟧) =
      propSet model.toModel.level (fibreOp (model.toModel.block
        fun param => γ (param.castLE (by omega)))
        ((StrongRecursiveFieldSource.code ((I.ctors s c).recursive f)
          ((model.ctors s c).source.recursive f)).index γ)) := by
  simp [InductiveModel.sortValue]

theorem realizes
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (hsorts : ∀ s vps vis,
      ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis) :
    model.toModel.Interprets ε₂ zeroNs (I.map pre.sigs) η ls where
  level_eq := rfl
  params := by
    simpa [paramsSem, Inductive.map] using model.tele.params.realizes_mapInst pre hatoms
  indicesRealizes s := by
    simpa [paramsSem, indicesSem, Inductive.map] using
      (model.tele.indices s).realizes_mapInst pre hatoms
  ctorRealizes s c vps hps := by
    let ctorModel := model.ctors s c
    let source := ctorModel.source
    let target := ctorModel.target
    have hctor := source.realizes pre hatoms target vps hps
      model.toModel.sortValue hsorts (happlyTarget := by
      intro fieldSlots hfields
      have hbase := Reachable.base hfields
      have hpsEq : (fun param : Fin ι.nparams =>
        fieldSlots (param.castLE (Nat.le_add_right _ _))) = vps := hbase
      rw [hpsEq]
      rfl) (happlyRecursive := by
      intro f γ hγ
      have hpsEq :
          (fun param : Fin ι.nparams => γ (param.castLE (by omega))) =
            vps := by
        funext param
        simpa using
          congrFun (Set.eq_of_mem_singleton (Reachable.base (Reachable.base hγ))) param
      simpa [hpsEq] using recursiveField_apply model s c f γ)
    simpa [codeOf, Inductive.map] using hctor
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
  let fieldSlots := Fin.append vps vfds
  let source := (model.ctors s c).source
  let fields := source.recursiveCodes
  let tail := CtorCode.packRecursive (model.toModel.block vps) fields
    model.toModel.level fieldSlots vrecFds proof
  change source.ordinary.sem.pack fieldSlots tail ∈
      (model.codeOf s c).argSet (model.toModel.block vps) vps ∧
    model.ordinaryOf s c vps
      (source.ordinary.sem.pack fieldSlots tail) = fieldSlots
  have hbase := Set.eq_of_mem_singleton (Reachable.base hfields)
  constructor
  · have htail : tail ∈ (model.recursiveRest s c).argSet
        (model.toModel.block vps) fieldSlots :=
      CtorCode.packRecursive_mem hrecFields (CtorCode.proof_mem_argSet_target fieldSlots)
    simpa [codeOf_eq] using SemTele.pack_mem hfields htail
  · unfold ordinaryOf
    rw [← hbase]
    exact source.ordinary.sem.values_pack fieldSlots tail

end StrongInductiveModel

end Metalean
