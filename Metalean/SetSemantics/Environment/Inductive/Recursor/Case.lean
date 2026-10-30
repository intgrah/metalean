/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
import Metalean.Syntax.Substitution

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
  {params : StrongTeleModel E₁ ε₁ ![] I.params{ls}}
  (model : StrongInductiveModel E₁ ε₁ I ls)
  (source : StrongCtorSource E₁ ε₁ I ls ctor params bound)
  (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)

structure CaseSlots (ι : IndSig) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) where
  params : Slots.{u} ι.nparams
  motives : Slots.{u} ι.nsorts
  ordinary : Slots.{u} (ι.ctors s c).nfields
  recursive : Slots.{u} (ι.ctors s c).nrecFields

namespace CaseSlots

variable {ι : IndSig} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}

def valuation (γ : CaseSlots.{u} ι s c) :
    Slots (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) :=
  Fin.append (Fin.append (Fin.append γ.params γ.motives) γ.ordinary) γ.recursive

def ofValuation
    (γ : Slots (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)) :
    CaseSlots.{u} ι s c where
  params p := γ (((p.castAdd ι.nsorts).castAdd (ι.ctors s c).nfields).castAdd
    (ι.ctors s c).nrecFields)
  motives s₁ := γ (((s₁.natAdd ι.nparams).castAdd (ι.ctors s c).nfields).castAdd
    (ι.ctors s c).nrecFields)
  ordinary f := γ ((f.natAdd (ι.nparams + ι.nsorts)).castAdd (ι.ctors s c).nrecFields)
  recursive f := γ (f.natAdd (ι.nparams + ι.nsorts + (ι.ctors s c).nfields))

def fieldValues (γ : CaseSlots.{u} ι s c) : Slots (ι.nparams + (ι.ctors s c).nfields) :=
  Fin.append γ.params γ.ordinary

theorem fieldValues_ofValuation
    (γ : Slots (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)) :
    (ofValuation (ι := ι) (s := s) (c := c) γ).fieldValues =
      Slots.pull (fun base param => base (param.castAdd ι.nsorts))
        (fun v => γ (v.castAdd (ι.ctors s c).nrecFields)) := by
  funext v
  cases v using Fin.addCases <;> simp [ofValuation, fieldValues, Slots.pull]

@[simp] theorem ofValuation_valuation (γ : CaseSlots.{u} ι s c) :
    ofValuation γ.valuation = γ := by
  cases γ
  simp [ofValuation, valuation]

end CaseSlots

namespace StrongInductiveModel

noncomputable def recrMotiveTele (s : Fin ι.nsorts) :
    SemTele ι.nparams (ι.nparams + ι.nindices s + 1) :=
  (model.indicesSem s).snoc fun γ => model.toModel.sortValue s
    (fun param : Fin ι.nparams => γ (param.castLE (Nat.le_add_right _ _))) fun index =>
      γ (Fin.natAdd ι.nparams index)

noncomputable def recrMotiveValue (s : Fin ι.nsorts) (l : Level 0) : Dom ι.nparams :=
  (model.recrMotiveTele s).pi fun _ => S_ (l.eval ![])

include hatoms hsorts in
theorem recrMotiveValue_denotes (s : Fin ι.nsorts) (l : Level 0) (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem) :
    ε₂[vps]⟦(I.map pre.sigs).motiveType η ls (fun param => Expr.var param) l s⟧ =
      model.recrMotiveValue s l vps := by
  let := Subst.category ζ₂ 0
  have htele : Realizes ε₂ ![] (Reachable Set.univ model.paramsSem)
      ((I.map pre.sigs).motiveTele η ls (fun param => Expr.var param) s)
      (model.recrMotiveTele s) := by
    have hlast (γ : Slots (ι.nparams + ι.nindices s))
        (_ : γ ∈ Reachable (Reachable Set.univ model.paramsSem) (model.indicesSem s)) :
        ε₂[γ]⟦.ind η s ls (fun param => (Expr.var param).wkN (ι.nindices s))
            (fun index => Expr.var ⟨ι.nparams + index.val, by omega⟩)⟧ = model.toModel.sortValue s
            (fun param : Fin ι.nparams => γ (param.castLE (Nat.le_add_right _ _)))
            fun index : Fin (ι.nindices s) => γ (Fin.natAdd ι.nparams index) := by
      simpa! [Fin.natAdd, Fin.castAdd] using hsorts s
        (fun param => γ (param.castLE (Nat.le_add_right _ _))) fun index =>
          γ (Fin.natAdd ι.nparams index)
    have hsnoc := Tele.Forall₂.snoc ((model.indices s).realizes.mapInst pre hatoms) hlast
    have hindexTele : ((I.map pre.sigs).indices s){ls} =
        (I.map pre.sigs).indexTele ls s fun param => Expr.var param :=
      ((Ctx.substFunctor _).map_id_apply _ _).symm
    rw [Inductive.motiveTele, ← hindexTele]
    simpa [Inductive.map, paramsSem, indicesSem, recrMotiveTele] using hsnoc
  apply Realizes.denotes_pi hps (fun _ _ => rfl)
  simpa using htele

noncomputable def recrMotivesSem (l : Level 0) :
    SemTele ι.nparams (ι.nparams + ι.nsorts) :=
  SemTele.ofDoms fun s => model.recrMotiveValue s l

include hatoms hsorts in
theorem recrMotivesRealizes (l : Level 0) :
    Realizes ε₂ ![] (Reachable Set.univ model.paramsSem)
      ((I.map pre.sigs).motiveBinders η ls l) (model.recrMotivesSem l) :=
  Realizes.ofTypes fun s => model.recrMotiveValue_denotes pre hatoms hsorts s l

noncomputable def recrCaseMotive (vps : Slots ι.nparams) (vms : Fin ι.nsorts → ZFSet) : ZFSet :=
  bundleMotive model.toModel.level ι.nindices vms (model.toModel.block vps)


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
    (CaseSlots.ofValuation (ι := ι) (s := s) (c := c) γ).fieldValues ∈
      Reachable Set.univ (model.params.append (model.ctors s c).source.ordinary).sem :=
  by
    rw [CaseSlots.fieldValues_ofValuation]
    exact Reachable.append (Reachable.pull (Reachable.base (Reachable.of_append hγ))
      fun _ hbase => Reachable.base hbase)

theorem recrCaseFieldsSem_recursive_mem (f : Fin (ι.ctors s c).nrecFields) :
    γ (Fin.natAdd (ι.nparams + ι.nsorts + (ι.ctors s c).nfields) f) ∈ typedRecFieldSetDep
      (StrongRecursiveFieldSource.code ((I.ctors s c).recursive f)
        ((model.ctors s c).source.recursive f)).tele
      (StrongRecursiveFieldSource.code ((I.ctors s c).recursive f)
        ((model.ctors s c).source.recursive f)).index
      (fun current => model.toModel.block fun param => current (param.castLE (by omega)))
      model.toModel.level ((CaseSlots.ofValuation (ι := ι) (s := s) (c := c) γ).fieldValues) := by
  rw [CaseSlots.fieldValues_ofValuation, typedRecFieldSetDep_apply]
  simpa [StrongCtorSource.code] using
    Reachable.ofDoms_mem (Reachable.pull (Reachable.of_append hγ) fun _ hbase =>
      Reachable.pull hbase fun _ hbase => Reachable.base hbase) f

end

include hatoms hsorts in
theorem recrCaseFieldsSem_realizes (l : Level 0) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Realizes ε₂ ![] (Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
      (((I.ctors s c).map pre.sigs).fieldTele η ls fun param => Expr.var (param.castLE (by omega)))
      (model.recrCaseFieldsSem s c) := by
  let := Subst.category ζ₂ 0
  let source := (model.ctors s c).source
  let σ : Subst ζ₂ 0 ι.nparams (ι.nparams + ι.nsorts) := fun param => .var (param.castAdd ι.nsorts)
  have hbase : Set.MapsTo (fun γ param => γ (param.castAdd ι.nsorts))
      (Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
      (Reachable Set.univ model.paramsSem) := fun _ hγ => Reachable.base hγ
  have hrecFields := source.recursiveSem_realizes pre hatoms
    (block := fun γ => model.toModel.block fun param => γ (param.castLE (Nat.le_add_right _ _)))
    (level := model.toModel.level)
    (reach := Reachable (Reachable Set.univ model.paramsSem) source.ordinary.sem)
    (fun _ => Reachable.append) model.toModel.sortValue hsorts
    (fun f γ _ => model.recursiveField_apply s c f γ)
  have hfields := source.ordinary.realizes.mapInst pre hatoms
  simp at hfields
  have hordTele : ((I.ctors s c).map pre.sigs).ordinaryTele{ls} =
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

noncomputable def recrCaseLeaf :
    Dom (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
      (ι.ctors s c).nrecFields) :=
  fun γ =>
    let fields := CaseSlots.ofValuation (ι := ι) (s := s) (c := c)
      (fun v => γ (v.castAdd (ι.ctors s c).nrecFields))
    [zf|$(fields.motives s) $(model.targetValues s c fields.fieldValues)...
      $(model.ctorResult s c fields.params fields.ordinary fields.recursive)]

noncomputable def recrCaseIhSem :
    SemTele (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
      (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
        (ι.ctors s c).nrecFields) :=
  SemTele.ofDoms fun f γ =>
    let fields := CaseSlots.ofValuation (ι := ι) (s := s) (c := c) γ
    ihType ((model.ctors s c).source.code.recursive f).tele
      ((model.ctors s c).source.code.recursive f).index
      (model.recrCaseMotive fields.params fields.motives) fields.fieldValues (fields.recursive f)

noncomputable def recrCaseTele :
    SemTele (ι.nparams + ι.nsorts)
      (ι.nparams + ι.nsorts + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
        (ι.ctors s c).nrecFields) :=
  model.recrCaseFieldsSem s c ++ model.recrCaseIhSem s c

end

include hatoms in
theorem recrCaseIhSem_realizes (l : Level 0) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Realizes ε₂ ![]
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
  let fields := CaseSlots.ofValuation (ι := ι) (s := s) (c := c) γ
  let vps := fields.params
  let vms := fields.motives
  let δ := fields.fieldValues
  let ms : Fin ι.nsorts → Expr ζ₂ 0 (ι.nparams + ι.nsorts + sig.nfields + sig.nrecFields) :=
    fun s => .var ⟨ι.nparams + s.val, by omega⟩
  let ps : Fin ι.nparams → Expr ζ₂ 0 (ι.nparams + ι.nsorts) := fun p => .var (p.castAdd ι.nsorts)
  let σ := Fin.append (sig.fieldParams ps) (sig.fieldOrdinary (n := ι.nparams + ι.nsorts))
  have hden := StrongRecursiveFieldSource.ihType_denotes (C.recursive f) source pre hatoms γ δ
    (model.recrCaseFieldsSem_base s c l γ hγ)
    (σ := σ) (ms := ms) (e := sig.fieldRecursive f) (motive := model.recrCaseMotive vps vms)
    (by
      funext v
      cases v using Fin.addCases <;>
        simp! [σ, ps, δ, sig, CtorSig.fieldParams, CtorSig.fieldOrdinary, CaseSlots.ofValuation, CaseSlots.fieldValues, fields, Slots.pull])
    (hleaf := fun final hfinal value hvalue => by
      have hps : (fun param : Fin ι.nparams =>
          final ((param.castAdd sig.nfields).castLE code.tele.le)) = vps :=
        funext fun param => (hfinal (param.castAdd sig.nfields)).trans
          (Fin.append_left ..)
      change value ∈ propSet model.toModel.level
        (fibreOp (model.toModel.block fun p => final ((p.castAdd sig.nfields).castLE code.tele.le))
          (code.index final)) at hvalue
      rw [hps] at hvalue
      change [zf|$(vms (sig.recursiveTarget f))
        $((ε₁[final]⟦(C.recursive f).indices{ls} ·⟧))... value] = _
      exact (fibre_bundleMotive_typed (vms := vms) (sig.recursiveTarget f)
        (ε₁[final]⟦(C.recursive f).indices{ls} ·⟧) hvalue).symm)
    (model.recrCaseFieldsSem_recursive_mem s c l γ hγ f)
  simp [Ctor.ihType] at hden ⊢
  exact hden

end StrongInductiveModel

end Metalean
