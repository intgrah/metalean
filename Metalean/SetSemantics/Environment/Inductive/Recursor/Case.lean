/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
import Metalean.Syntax.Substitution
import Metalean.Typing.Weakening

@[expose] public section

universe u

namespace Metalean

open ZFSet StrongInductiveModel

variable {bound : Nat}
  {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {ctor : Ctor ζ₁ ι s csig}
  {params : StrongTeleModel E₁ ε₁ zeroNs (Ctx.instL ls I.params)}
  (model : StrongInductiveModel E₁ ε₁ I ls)
  (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
  (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)

namespace StrongInductiveModel

noncomputable def recrMotiveTele (s : Fin ι.nsorts) :
    SemTele ι.nparams (ι.nparams + ι.nindices s + 1) :=
  (model.indicesSem s).snoc fun γ => model.toModel.sortValue s
    (fun param : Fin ι.nparams => γ (param.castLE (Nat.le_add_right _ _))) fun index =>
      γ (Fin.natAdd ι.nparams index)

noncomputable def recrMotiveValue (s : Fin ι.nsorts) (l : Level 0) : Dom ι.nparams :=
  (model.recrMotiveTele s).pi fun _ => S_ (l.eval zeroNs)

include hatoms hsorts in
theorem recrMotiveValue_denotes (s : Fin ι.nsorts) (l : Level 0) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem) :
    ε₂[vps]⟦(I.map pre.sigs).motiveType η ls (fun param => Expr.var param) l s⟧ =
      model.recrMotiveValue s l vps := by
  let := Subst.category ζ₂ 0
  have htele : Realizes ε₂ zeroNs (Reachable Set.univ model.paramsSem)
      ((I.map pre.sigs).motiveTele η ls (fun param => Expr.var param) s)
      (model.recrMotiveTele s) := by
    have hlast (γ : Slots (ι.nparams + ι.nindices s))
        (_ : γ ∈ Reachable (Reachable Set.univ model.paramsSem) (model.indicesSem s)) :
        ε₂[γ]⟦.ind η s ls (fun param => (Expr.var param).wkN (ι.nindices s))
            (fun index => Expr.var ⟨ι.nparams + index.val, by omega⟩)⟧ = model.toModel.sortValue s
            (fun param : Fin ι.nparams => γ (param.castLE (Nat.le_add_right _ _)))
            fun index : Fin (ι.nindices s) => γ (Fin.natAdd ι.nparams index) := by
      simpa [Expr.denote, Fin.natAdd, Fin.castLE, Fin.castAdd] using hsorts s
        (fun param => γ (param.castLE (Nat.le_add_right _ _))) fun index =>
          γ (Fin.natAdd ι.nparams index)
    have hsnoc := Tele.Forall₂.snoc ((model.tele.indices s).realizes_mapInst pre hatoms) hlast
    have hindexTele : Ctx.instL ls ((I.map pre.sigs).indices s) =
        (I.map pre.sigs).indexTele ls s fun param => Expr.var param :=
      ((Ctx.substFunctor _).map_id_apply _ _).symm
    rw [Inductive.motiveTele, ← hindexTele]
    simpa [Inductive.map, paramsSem, indicesSem, recrMotiveTele] using hsnoc
  apply Realizes.denotes_pi hps (fun _ _ => rfl)
  simpa [Inductive.motiveType, recrMotiveValue] using htele

noncomputable def recrMotivesSem (l : Level 0) :
    SemTele ι.nparams (ι.nparams + ι.nsorts) :=
  SemTele.ofDoms fun s => model.recrMotiveValue s l

include hatoms hsorts in
theorem recrMotivesRealizes (l : Level 0) :
    Realizes ε₂ zeroNs (Reachable Set.univ model.paramsSem)
      ((I.map pre.sigs).motiveBinders η ls l) (model.recrMotivesSem l) :=
  Realizes.ofTypes fun s => model.recrMotiveValue_denotes pre hatoms hsorts s l

noncomputable def recrCaseMotive (vps : Slots ι.nparams) (vms : Fin ι.nsorts → ZFSet) : ZFSet :=
  bundleMotive model.toModel.level ι.nindices vms (model.toModel.block vps)

noncomputable def _root_.Metalean.StrongCtorSource.recursiveSem
    (block : Dom (ι.nparams + csig.nfields)) (level : Nat) :
    SemTele (ι.nparams + csig.nfields) (ι.nparams + csig.nfields + csig.nrecFields) :=
  SemTele.ofDoms fun f =>
    typedRecFieldSetDep (source.recursiveCodes f).2.tele (source.recursiveCodes f).2.index block
      level

include hatoms in
theorem _root_.Metalean.StrongCtorSource.recursiveSem_realizes
    {block : Dom (ι.nparams + csig.nfields)} {level : Nat}
    {reach : Set (Slots (ι.nparams + csig.nfields))}
    (hreaches : reach ⊆ Reachable Set.univ (params.append source.ordinary).sem)
    (sortValues : (s : Fin ι.nsorts) → Slots ι.nparams → Slots (ι.nindices s) → ZFSet)
    (hsortValues : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = sortValues s vps vis)
    (happlyRecursive : ∀ f : Fin csig.nrecFields,
      ∀ γ ∈ Reachable reach
        (StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)).tele,
      sortValues (csig.recursiveTarget f)
          (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
          (ε₁[γ]⟦(ctor.recursive f).indices · |>.instL ls⟧) =
        propSet level (fibreOp
          (block fun current : Fin (ι.nparams + csig.nfields) =>
            γ (current.castLE (StrongRecursiveFieldSource.code (ctor.recursive f)
              (source.recursive f)).tele.le))
          ((StrongRecursiveFieldSource.code (ctor.recursive f) (source.recursive f)).index γ))) :
    Realizes ε₂ zeroNs reach
      ((ctor.map pre.sigs).recursiveFieldTele η ls
        (fun param => (.var (param.castLE (Nat.le_add_right _ _)) :
          Expr ζ₂ 0 (ι.nparams + csig.nfields)))
        (Expr.boundVars ι.nparams csig.nfields 0))
      (source.recursiveSem block level) :=
  Realizes.ofTypes fun f γ hγ => by
    have hden := StrongRecursiveFieldSource.denotesDepMapEnv pre hatoms (ctor.recursive f)
      (source.recursive f) hreaches (hsortValues (csig.recursiveTarget f)) (happlyRecursive f) γ hγ
    simp [StrongCtorSource.recursiveCodes] at hden ⊢
    exact hden

section
variable (s : Fin ι.nsorts) (c : Fin (ι.nctors s))

noncomputable def recrCaseOrdinarySem :
    SemTele (ι.nparams + ι.nsorts) (ι.nparams + ι.nsorts + (ι.ctors s c).nfields) :=
  (model.ctors s c).source.ordinary.sem.pull (fun γ param => γ (param.castAdd ι.nsorts))
    (ι.ctors s c).nfields

noncomputable def recrCaseRecursiveSem :
    SemTele (ι.nparams + ι.nsorts + (ι.ctors s c).nfields)
      (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) :=
  ((model.ctors s c).source.recursiveSem
    (fun γ => model.toModel.block fun param => γ (param.castLE (Nat.le_add_right _ _)))
    model.toModel.level).pull (Slots.pull fun γ param => γ (param.castAdd ι.nsorts))
    (ι.ctors s c).nrecFields

noncomputable def recrCaseFieldsSem :
    SemTele (ι.nparams + ι.nsorts)
      (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) :=
  model.recrCaseOrdinarySem s c ++ model.recrCaseRecursiveSem s c

def recrCaseFieldBase (_model : StrongInductiveModel E₁ ε₁ I ls)
    (γ : Slots (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)) :
    Slots (ι.nparams + (ι.ctors s c).nfields) :=
  Slots.pull (fun γ param => γ (param.castAdd ι.nsorts)) fun v =>
    γ (v.castAdd (ι.ctors s c).nrecFields)

end

theorem recrCaseFieldsSem_reachable (l : Level 0) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vms : Fin ι.nsorts → ZFSet)
    (vfds : Fin (ι.ctors s c).nfields → ZFSet) (vrecFds : Fin (ι.ctors s c).nrecFields → ZFSet)
    (hms : Fin.append vps vms ∈
      Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
    (hrecFields : Fin.append (Fin.append vps vfds) vrecFds ∈ Reachable
      (Reachable (Reachable Set.univ model.paramsSem) (model.ctors s c).source.ordinary.sem)
      ((model.ctors s c).source.recursiveSem
        (fun γ => model.toModel.block fun param => γ (param.castLE (Nat.le_add_right _ _)))
        model.toModel.level)) :
    Fin.append (Fin.append (Fin.append vps vms) vfds) vrecFds ∈ Reachable
      (Reachable (Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
        (model.recrCaseOrdinarySem s c))
      (model.recrCaseRecursiveSem s c) :=
  Reachable.of_pull (reach := Reachable (Reachable Set.univ model.paramsSem)
      (model.ctors s c).source.ordinary.sem) (by simpa using hrecFields)
    (Reachable.of_pull
      (by simpa using Reachable.base hrecFields) (by simpa using hms))

section
variable (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (l : Level 0)
  (γ : Slots (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields))
  (hγ : γ ∈ Reachable (Reachable (Reachable Set.univ model.paramsSem)
    (model.recrMotivesSem l)) (model.recrCaseFieldsSem s c))

include hγ

theorem recrCaseFieldsSem_base :
    model.recrCaseFieldBase s c γ ∈
      Reachable Set.univ (model.tele.params.append (model.ctors s c).source.ordinary).sem :=
  Reachable.append (Reachable.pull (Reachable.base (Reachable.of_append hγ))
    fun _ hbase => Reachable.base hbase)

theorem recrCaseFieldsSem_recursive_mem (f : Fin (ι.ctors s c).nrecFields) :
    γ (Fin.natAdd (ι.nparams + ι.nsorts + (ι.ctors s c).nfields) f) ∈ typedRecFieldSetDep
      (StrongRecursiveFieldSource.code ((I.ctors s c).recursive f)
        ((model.ctors s c).source.recursive f)).tele
      (StrongRecursiveFieldSource.code ((I.ctors s c).recursive f)
        ((model.ctors s c).source.recursive f)).index
      (fun current => model.toModel.block fun param => current (param.castLE (by omega)))
      model.toModel.level (model.recrCaseFieldBase s c γ) := by
  simpa [recrCaseFieldBase, StrongCtorSource.recursiveCodes] using
    Reachable.ofDoms_mem (Reachable.pull (Reachable.of_append hγ) fun _ hbase =>
      Reachable.pull hbase fun _ hbase => Reachable.base hbase) f

end

include hatoms hsorts in
theorem recrCaseFieldsSem_realizes (l : Level 0) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Realizes ε₂ zeroNs (Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
      (((I.ctors s c).map pre.sigs).fieldTele η ls fun param => Expr.var (param.castLE (by omega)))
      (model.recrCaseFieldsSem s c) := by
  let := Subst.category ζ₂ 0
  let source := (model.ctors s c).source
  let C := I.ctors s c
  let σ : Subst ζ₂ 0 ι.nparams (ι.nparams + ι.nsorts) := fun param => .var (param.castAdd ι.nsorts)
  have hbase : Set.MapsTo (fun γ param => γ (param.castAdd ι.nsorts))
      (Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
      (Reachable Set.univ model.paramsSem) := fun _ hγ => Reachable.base hγ
  have hrecFields := source.recursiveSem_realizes pre hatoms
    (block := fun γ => model.toModel.block fun param => γ (param.castLE (Nat.le_add_right _ _)))
    (level := model.toModel.level)
    (reach := Reachable (Reachable Set.univ model.paramsSem) source.ordinary.sem)
    (fun _ => Reachable.append) model.toModel.sortValue hsorts
    (fun f γ _ => by simpa [C] using model.recursiveField_apply s c f γ)
  have hfields := source.ordinary.realizes_mapInst pre hatoms
  simp at hfields
  have hordTele : Ctx.instL ls ((I.ctors s c).map pre.sigs).ordinaryTele =
      ((I.ctors s c).map pre.sigs).ordinaryFieldTele η ls fun param => Expr.var param :=
    ((Ctx.substFunctor _).map_id_apply _ _).symm
  rw [hordTele] at hfields
  have h := (hfields.pull σ _ hbase fun _ _ _ => rfl).append
    (hrecFields.pull (σ.liftN (ι.ctors s c).nfields) _ (fun _ hγ => Reachable.pull hγ hbase)
      fun γ _ v => congrFun (Expr.denote_substLiftN γ σ) v)
  have hfieldTele : ((I.ctors s c).map pre.sigs).fieldTele η ls (fun param => Expr.var param) =
      ((I.ctors s c).map pre.sigs).ordinaryFieldTele η ls (fun param => Expr.var param) ++
        ((I.ctors s c).map pre.sigs).recursiveFieldTeleAux η ls
          (fun param => Expr.var (param.castLE (Nat.le_add_right _ _)))
          (Expr.boundVars ι.nparams (ι.ctors s c).nfields 0) (ι.ctors s c).nrecFields le_rfl := by
    simp [Ctor.fieldTele, Fin.castAdd]
  rwa [← Ctx.substN₂_append, ← hfieldTele, Ctor.fieldTele_subst] at h

section
variable (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
  (γ : Slots (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields))

def recrCaseParams (_model : StrongInductiveModel E₁ ε₁ I ls) : Slots ι.nparams :=
  fun param => γ (((param.castAdd ι.nsorts).castAdd
    (ι.ctors s c).nfields).castAdd (ι.ctors s c).nrecFields)

def recrCaseMotives (_model : StrongInductiveModel E₁ ε₁ I ls) : Fin ι.nsorts → ZFSet :=
  fun s₁ => γ (((Fin.natAdd ι.nparams s₁).castAdd
    (ι.ctors s c).nfields).castAdd (ι.ctors s c).nrecFields)

def recrCaseOrdinary (_model : StrongInductiveModel E₁ ε₁ I ls) :
    Fin (ι.ctors s c).nfields → ZFSet :=
  fun f => γ ((Fin.natAdd (ι.nparams + ι.nsorts) f).castAdd (ι.ctors s c).nrecFields)

def recrCaseRecursive (_model : StrongInductiveModel E₁ ε₁ I ls) :
    Fin (ι.ctors s c).nrecFields → ZFSet :=
  fun f => γ (Fin.natAdd (ι.nparams + ι.nsorts + (ι.ctors s c).nfields) f)

end

section
variable (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (vps : Slots ι.nparams)
  (vms : Fin ι.nsorts → ZFSet)
  (vfds : Fin (ι.ctors s c).nfields → ZFSet) (vrecFds : Fin (ι.ctors s c).nrecFields → ZFSet)

@[simp] theorem recrCaseParams_append :
    model.recrCaseParams s c (Fin.append (Fin.append (Fin.append vps vms) vfds) vrecFds) = vps :=
  funext fun _ => by simp [recrCaseParams]

@[simp] theorem recrCaseMotives_append :
    model.recrCaseMotives s c (Fin.append (Fin.append (Fin.append vps vms) vfds) vrecFds) = vms :=
  funext fun _ => by simp [recrCaseMotives]

@[simp] theorem recrCaseOrdinary_append :
    model.recrCaseOrdinary s c (Fin.append (Fin.append (Fin.append vps vms) vfds) vrecFds) = vfds :=
  funext fun _ => by simp [recrCaseOrdinary]

@[simp] theorem recrCaseRecursive_append :
    model.recrCaseRecursive s c (Fin.append (Fin.append (Fin.append vps vms) vfds) vrecFds) =
      vrecFds :=
  funext fun _ => by simp [recrCaseRecursive]

end

section
variable (s : Fin ι.nsorts) (c : Fin (ι.nctors s))

noncomputable def recrCaseLeaf :
    Dom (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
      (ι.ctors s c).nrecFields) :=
  fun γ =>
    let fields := fun v => γ (v.castAdd (ι.ctors s c).nrecFields)
    let vps := model.recrCaseParams s c fields
    let vfds := model.recrCaseOrdinary s c fields
    [zf|$(model.recrCaseMotives s c fields s) $(model.targetValues s c (Fin.append vps vfds))...
      $(model.ctorResult s c vps vfds (model.recrCaseRecursive s c fields))]

theorem recrCaseFieldBase_eq_append
    (γ : Slots (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)) :
    model.recrCaseFieldBase s c γ =
      Fin.append (model.recrCaseParams s c γ) (model.recrCaseOrdinary s c γ) := by
  funext current
  cases current using Fin.addCases <;>
    simp [recrCaseFieldBase, recrCaseParams, recrCaseOrdinary]

noncomputable def recrCaseIhSem :
    SemTele (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
      (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
        (ι.ctors s c).nrecFields) :=
  SemTele.ofDoms fun f γ =>
    ihType ((model.ctors s c).source.recursiveCodes f).2.tele
      ((model.ctors s c).source.recursiveCodes f).2.index
      (model.recrCaseMotive (model.recrCaseParams s c γ) (model.recrCaseMotives s c γ))
      (Fin.append (model.recrCaseParams s c γ) (model.recrCaseOrdinary s c γ))
      (model.recrCaseRecursive s c γ f)

noncomputable def recrCaseTele :
    SemTele (ι.nparams + ι.nsorts)
      (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
        (ι.ctors s c).nrecFields) :=
  model.recrCaseFieldsSem s c ++ model.recrCaseIhSem s c

end

include hatoms in
theorem recrCaseIhSem_realizes (l : Level 0) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Realizes ε₂ zeroNs
      (Reachable (Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
        (model.recrCaseFieldsSem s c))
      (((I.ctors s c).map pre.sigs).ihTele ls (fun param => Expr.var (param.castLE (by omega)))
        fun s => Expr.var ⟨ι.nparams + s.val, by omega⟩)
      (model.recrCaseIhSem s c) := by
  refine Realizes.ofTypes fun f γ hγ => ?_
  let sig := ι.ctors s c
  let C := I.ctors s c
  let source := (model.ctors s c).source.recursive f
  let code := StrongRecursiveFieldSource.code (C.recursive f) source
  let vps := model.recrCaseParams s c γ
  let vms := model.recrCaseMotives s c γ
  let δ := model.recrCaseFieldBase s c γ
  let ms : Fin ι.nsorts → Expr ζ₂ 0 (ι.nparams + ι.nsorts + sig.nfields + sig.nrecFields) :=
    fun s => .var ⟨ι.nparams + s.val, by omega⟩
  let ps : Fin ι.nparams → Expr ζ₂ 0 (ι.nparams + ι.nsorts) := fun p => .var (p.castAdd ι.nsorts)
  let σ := Fin.append (sig.fieldParams ps) (sig.fieldOrdinary (n := ι.nparams + ι.nsorts))
  have hproject : δ = Fin.append vps (model.recrCaseOrdinary s c γ) :=
    model.recrCaseFieldBase_eq_append s c γ
  have hden := StrongRecursiveFieldSource.ihType_denotes (C.recursive f) source pre hatoms γ δ
    (model.recrCaseFieldsSem_base s c l γ hγ)
    (σ := σ) (ms := ms) (e := sig.fieldRecursive f) (motive := model.recrCaseMotive vps vms)
    (by
      funext v
      cases v using Fin.addCases <;>
        simp! [σ, ps, δ, sig, CtorSig.fieldParams, CtorSig.fieldOrdinary, recrCaseFieldBase,
          Slots.pull])
    (hleaf := fun final hfinal value hvalue => by
      have hps : (fun param : Fin ι.nparams =>
          final ((param.castAdd sig.nfields).castLE code.tele.le)) = vps :=
        funext fun param => (hfinal (param.castAdd sig.nfields)).trans
          ((congrFun hproject (param.castAdd sig.nfields)).trans (Fin.append_left ..))
      change value ∈ propSet model.toModel.level
        (fibreOp (model.toModel.block fun p => final ((p.castAdd sig.nfields).castLE code.tele.le))
          (code.index final)) at hvalue
      rw [hps] at hvalue
      change [zf|$(vms (sig.recursiveTarget f))
        $((ε₁[final]⟦(C.recursive f).indices · |>.instL ls⟧))... value] = _
      exact (fibre_bundleMotive_typed (vms := vms) (sig.recursiveTarget f)
        (ε₁[final]⟦(C.recursive f).indices · |>.instL ls⟧) hvalue).symm)
    (model.recrCaseFieldsSem_recursive_mem s c l γ hγ f)
  rw [hproject] at hden
  simp [Ctor.ihType, StrongCtorSource.recursiveCodes] at hden ⊢
  exact hden

end StrongInductiveModel

end Metalean
