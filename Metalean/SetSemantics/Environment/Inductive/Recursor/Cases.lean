/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
public import Metalean.SetSemantics.Environment.Inductive.Recursor.Case
import Metalean.SetSemantics.InductiveComputation
import Metalean.Syntax.Substitution

public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {bound : Nat}
  {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {ctor : Ctor ζ₁ ι s csig}
  {params : StrongTeleModel E₁ ε₁ ![] I.params{ls}}
  (model : StrongInductiveModel E₁ ε₁ I ls)
  (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
  (hctors : ∀ s c vps vfds vrecFds,
    ε₂ (.ctor η s c ls vps vfds vrecFds) = model.ctorResult s c vps vfds vrecFds)
  (l : Level 0)

noncomputable def StrongInductiveModel.recrCaseDomain
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots (ι.nparams + ι.nsorts)) : ZFSet :=
  (model.recrCaseTele s c).pi (model.recrCaseLeaf s c) γ

theorem StrongInductiveModel.recrCase_applyMinor_mem
    (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vms : Fin ι.nsorts → ZFSet)
    (hms : Fin.append vps vms ∈
      Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
    (minor : ZFSet)
    (hminor : minor ∈ model.recrCaseDomain s c (Fin.append vps vms))
    (approximation : ZFSet) (happroximation : approximation ⊆ model.toModel.block vps)
    (graph : ZFSet)
    (hgraph : ∀ value ∈ approximation, app graph value ∈ fibreOp (model.recrCaseMotive vps vms) value)
    (vargs : ZFSet) (hargs : vargs ∈ (model.codeOf s c).argSet approximation vps) :
    (model.codeOf s c).applyMinor model.toModel.level graph vps minor vargs ∈
      fibreOp (model.recrCaseMotive vps vms)
        (entry ((model.codeOf s c).targetIndex vps vargs) (tagOf s c) vargs) := by
  let source := (model.ctors s c).source
  let fieldTele := source.ordinary.sem
  let fields := source.recursiveCodes
  let rest := CtorCode.prependRecursive (ι.ctors s c).nrecFields fields
    (.target (StrongCtorSource.targetIndex (model.ctors s c).target))
  have hps : vps ∈ Reachable Set.univ model.paramsSem := by
    simpa using Reachable.base hms
  have hfields := SemTele.reachable_values (Δ := fieldTele)
    (reach := Reachable Set.univ model.paramsSem)
    hargs hps
  let γ₁ := fieldTele.values vps vargs
  let vfds := fun f => γ₁ (Fin.natAdd ι.nparams f)
  have hfieldsBase : (fun param : Fin ι.nparams =>
      γ₁ (param.castLE fieldTele.le)) = vps :=
    funext <| fieldTele.values_base vps vargs
  let raw := tupleValues (ι.ctors s c).nrecFields (fieldTele.tail vargs)
  have hvargs := CtorCode.tail_mem_argSet (Δ := fieldTele) (rest := rest) hargs
  have hvargs' := CtorCode.argSet_mono happroximation rest γ₁ hvargs
  have hraw := CtorCode.recursiveValues_mem hvargs'
  let ihs := fun f => recMap (fields f).2.tele (fields f).2.index graph γ₁ (raw f)
  have hihs (f) : ihs f ∈ ihType (fields f).2.tele (fields f).2.index
      (model.recrCaseMotive vps vms) γ₁ (raw f) :=
    recMap_mem (fields f).2.tele (fields f).2.index hgraph γ₁ (raw f)
      (CtorCode.recursiveValues_mem hvargs f)
  let typed := fun f => eraseRecField (fields f).2.tele model.toModel.level γ₁ (raw f)
  have hfieldsSlotsEq : γ₁ = Fin.append vps vfds := fieldTele.values_eq_append vps vargs
  have hrecFields : Fin.append γ₁ typed ∈ Reachable
      (Reachable (Reachable Set.univ model.paramsSem) fieldTele)
      (source.recursiveSem (fun current => model.toModel.block fun param =>
        current (param.castLE (Nat.le_add_right _ _))) model.toModel.level) :=
    Reachable.ofDoms_append hfields fun f => by
      simpa only [hfieldsBase] using eraseRecField_mem _ _ (hraw f)
  rw [hfieldsSlotsEq] at hrecFields
  have hrec := model.recrCaseFieldsSem_reachable l s c vps vms vfds typed hms hrecFields
  have hihSlots : Fin.append (Fin.append (Fin.append (Fin.append vps vms) vfds) typed) ihs ∈
      Reachable
        (Reachable (Reachable (Reachable Set.univ model.paramsSem)
          (model.recrMotivesSem l)) (model.recrCaseFieldsSem s c))
        (model.recrCaseIhSem s c) :=
    Reachable.ofDoms_append (Reachable.append hrec) fun f => by
      have hi := hihs f
      change ihs f ∈ ihType (fields f).2.tele (fields f).2.index
        (bundleMotive model.toModel.level ι.nindices vms (model.toModel.block vps)) γ₁ (raw f) at hi
      rw [ihType_eraseRecField _ _ γ₁ (raw f) (hraw f)] at hi
      simpa [CaseSlots.ofValuation, CaseSlots.fieldValues, ← hfieldsSlotsEq,
        typed, fields, source, StrongCtorSource.recursiveCodes, recrCaseMotive] using hi

  have hleaf := Reachable.app_mem_of_base
    (Δ := model.recrCaseTele s c) (Reachable.append hihSlots)
    (γ := Fin.append vps vms) (fun v => by
      change Fin.append (Fin.append (Fin.append (Fin.append vps vms) vfds) typed) ihs
        (((v.castAdd _).castAdd _).castAdd _) = _
      simp) hminor
  simp [recrCaseTele, recrCaseFieldsSem, SemTele.app_append, SemTele.app_eq_apps] at hleaf
  have happlyMinor : (model.codeOf s c).applyMinor model.toModel.level
        graph vps minor vargs = [zf|minor vfds... typed... ihs...] := by
    rw [show model.codeOf s c = CtorCode.prependOrdinary fieldTele rest from rfl]
    unfold CtorCode.applyMinor
    rw [SemTele.applyFields_prependOrdinary, SemTele.applyIhs_prependOrdinary,
      CtorCode.applyFields_prependRecursive, CtorCode.applyIhs_prependRecursive, SemTele.app_eq_apps]
  simp [recrCaseLeaf, CaseSlots.ofValuation, CaseSlots.fieldValues] at hleaf
  have hfieldsRaw : model.ordinaryOf s c vps vargs = γ₁ := rfl
  have hmaj : model.ctorResult s c vps vfds typed =
      propVal model.toModel.level (entryValue (tagOf s c) vargs) := by
    rw [show vargs = fieldTele.pack γ₁ (fieldTele.tail vargs) from
      (SemTele.pack_values hargs).symm]
    dsimp only [StrongInductiveModel.ctorResult, StrongInductiveModel.ctorArgs]
    rw [← hfieldsSlotsEq]
    exact CtorCode.packRecursive_erase hvargs' model.toModel.level (tagOf s c)
      (fieldTele.pack γ₁)
  have htarget := model.codeOf_targetIndex s c vps vargs
  rw [hfieldsRaw, hfieldsSlotsEq] at htarget
  have hentry : _ ∈ model.toModel.block vps := entry_mem_indSet (model.mapsTo vps)
    (CtorCode.argSet_mono happroximation _ vps hargs)
  rw [htarget] at hentry
  have hvalue := hmaj ▸ propVal_mem_propSet (level := model.toModel.level)
    (entryValue_mem_fibre hentry)
  rwa [happlyMinor, htarget, recrCaseMotive, fibre_bundleMotive_propVal hentry, entry_eq, fst_pair,
    snd_pair, ← hmaj, fibre_bundleMotive_typed s _ hvalue]

include hatoms hsorts hctors in
theorem StrongInductiveModel.recrCaseDomain_denotes
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots (ι.nparams + ι.nsorts))
    (hγ : γ ∈ Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l)) :
    ε₂[γ]⟦(I.map pre.sigs).caseFnType η ls
      (fun param => Expr.var (param.castLE (by omega)))
      (fun s => Expr.var ⟨ι.nparams + s.val, by omega⟩)
      s c⟧ = model.recrCaseDomain s c γ := by
  let ctorModel := model.ctors s c
  have hresult : DenotesOver ε₂ ![]
      (Reachable (Reachable Set.univ model.paramsSem)
        (model.recrMotivesSem l)) (model.recrCaseTele s c)
      ((I.map pre.sigs).caseType η ls
        (fun param => Expr.var (param.castLE (by omega)))
        (fun s => Expr.var ⟨ι.nparams + s.val, by omega⟩)
        s c) (model.recrCaseLeaf s c) := by
    intro δ hδ
    let sig := ι.ctors s c
    let fieldSlots : Slots (ι.nparams + ι.nsorts + sig.nfields + sig.nrecFields) :=
      fun v => δ (v.castAdd sig.nrecFields)
    have hsource := model.recrCaseFieldsSem_base s c l fieldSlots
      (Reachable.base (Reachable.of_append hδ))
    let ps : Fin ι.nparams → Expr ζ₂ 0 (ι.nparams + ι.nsorts) :=
      fun p => .var (p.castAdd ι.nsorts)
    have htarget (i : Fin (ι.nindices s)) :
        ε₂[δ]⟦((I.map pre.sigs).ctors s c).targetIndex ls
          (sig.caseParams ps) sig.caseOrdinary i⟧ =
        model.targetValues s c
          (Fin.append ((CaseSlots.ofValuation (ι := ι) (s := s) (c := c) fieldSlots).params)
            ((CaseSlots.ofValuation (ι := ι) (s := s) (c := c) fieldSlots).ordinary)) i := by
      have h := (Expr.denote_map pre.sigs hatoms _ _).trans
        (ctorModel.target.denotes _ hsource i)
      rw [Expr.map_instL] at h
      simp only [Ctor.targetIndex, Expr.denote_subst, Fin.append_comp, ps, CtorSig.caseParams,
        CtorSig.fieldParams, CtorSig.caseOrdinary, CtorSig.fieldOrdinary, Expr.var_wkN]
      exact h
    simp only [Inductive.caseType, Inductive.motiveResult, Expr.denote, Expr.denote_apps,
      CtorSig.caseParams, CtorSig.caseOrdinary, CtorSig.caseRecursive,
      CtorSig.fieldParams, CtorSig.fieldOrdinary, CtorSig.fieldRecursive, Expr.var_wkN]
    change [zf|$((CaseSlots.ofValuation (ι := ι) (s := s) (c := c) fieldSlots).motives s)
      $((ε₂[δ]⟦((I.map pre.sigs).ctors s c).targetIndex ls
        (sig.caseParams ps) sig.caseOrdinary ·⟧))...
      $(ε₂ (.ctor η s c ls ((CaseSlots.ofValuation (ι := ι) (s := s) (c := c) fieldSlots).params)
        ((CaseSlots.ofValuation (ι := ι) (s := s) (c := c) fieldSlots).ordinary)
        ((CaseSlots.ofValuation (ι := ι) (s := s) (c := c) fieldSlots).recursive)))] = _
    rw [funext htarget, hctors]
    rfl
  exact ((model.recrCaseFieldsSem_realizes pre hatoms hsorts l s c).append
    (model.recrCaseIhSem_realizes pre hatoms l s c)).denotes_pi hγ hresult

namespace StrongInductiveModel

noncomputable def recrCasesSem :
    SemTele (ι.nparams + ι.nsorts) (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
  SemTele.ofDoms fun tag =>
    let ⟨s, c⟩ := Fin.decodeSigma ι.nctors tag
    model.recrCaseDomain s c

theorem recrCasesSem_mem
    (γ : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors))
    (hγ : γ ∈ Reachable (Reachable (Reachable Set.univ model.paramsSem)
        (model.recrMotivesSem l))
      model.recrCasesSem)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    γ (Fin.natAdd (ι.nparams + ι.nsorts) (Fin.encodeSigma ι.nctors ⟨s, c⟩)) ∈
      model.recrCaseDomain s c fun base => γ (base.castAdd (Fin.sum ι.nctors)) := by
  have h := Reachable.ofDoms_mem hγ (Fin.encodeSigma ι.nctors ⟨s, c⟩)
  rwa [Fin.decodeSigma_encodeSigma] at h

include hatoms hsorts hctors in
theorem recrCasesRealizes :
    Realizes ε₂ ![]
      (Reachable (Reachable Set.univ model.paramsSem)
        (model.recrMotivesSem l))
      ((I.map pre.sigs).caseBinders η ls)
      model.recrCasesSem :=
  Realizes.ofTypes fun tag =>
    let ⟨s, c⟩ := Fin.decodeSigma ι.nctors tag
    model.recrCaseDomain_denotes pre hatoms hsorts hctors l s c

end StrongInductiveModel

end Metalean
