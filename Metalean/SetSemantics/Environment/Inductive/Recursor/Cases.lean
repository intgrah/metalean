/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
public import Metalean.SetSemantics.Inductive.Motive
import Metalean.SetSemantics.Inductive.Recursion
import Metalean.Syntax.Substitution

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  (model : StrongInductiveModel E₁ ε₁ I ls)
  (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
  (hctors : ∀ s c vps vfds vrecFds,
    ε₂ (.ctor η s c ls vps vfds vrecFds) = model.ctorResult s c vps vfds vrecFds)
  (l : Level 0)

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

end StrongInductiveModel

noncomputable def StrongInductiveModel.recrCaseDomain
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots (ι.nparams + ι.nsorts)) : ZFSet :=
  let vps : Slots ι.nparams := fun p => γ (p.castAdd ι.nsorts)
  let vms : Slots ι.nsorts := fun s => γ (s.natAdd ι.nparams)
  (model.codeOf s c).minorType model.toModel.level (model.toModel.block vps)
    (model.recrCaseMotive vps vms) (fun final fields =>
      [zf|$(vms s) $(model.targetValues s c final)...
        $(model.ctorResult s c vps (fun f => final (f.natAdd ι.nparams)) fields)]) vps

theorem StrongInductiveModel.recrCase_applyMinor_mem
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vms : Fin ι.nsorts → ZFSet)
    (minor : ZFSet)
    (hminor : minor ∈ model.recrCaseDomain s c (Fin.append vps vms))
    (approximation : ZFSet) (happroximation : approximation ⊆ model.toModel.block vps)
    (graph : ZFSet)
    (hgraph : ∀ value ∈ approximation, app graph value ∈ fibreOp (model.recrCaseMotive vps vms) value)
    (vargs : ZFSet) (hargs : vargs ∈ (model.codeOf s c).argSet approximation vps) :
    (model.codeOf s c).applyMinor model.toModel.level graph vps minor vargs ∈
      fibreOp (model.recrCaseMotive vps vms)
        (entry ((model.codeOf s c).targetIndex vps vargs) (tagOf s c) vargs) := by
  let code := model.codeOf s c
  let final := code.ordinary.values vps vargs
  let fields := fun f => eraseRecField (code.recursive f).tele model.toModel.level final
    (tupleValues code.nrecFields (code.ordinary.tail vargs) f)
  have hminor : minor ∈ code.minorType model.toModel.level (model.toModel.block vps)
      (model.recrCaseMotive vps vms) (fun current recursive =>
        [zf|$(vms s) $(model.targetValues s c current)...
          $(model.ctorResult s c vps (fun f => current (f.natAdd ι.nparams)) recursive)]) vps := by
    simpa [recrCaseDomain] using hminor
  have hleaf := CtorCode.applyMinor_mem hminor happroximation hgraph
    (fun _ _ h => by simpa [recrCaseMotive] using fibre_bundleMotive_propVal h) hargs
  have hmaj : model.ctorResult s c vps (fun f => final (f.natAdd ι.nparams)) fields =
      propVal model.toModel.level (entryValue (tagOf s c) vargs) :=
    code.pack_erase (CtorCode.argSet_mono happroximation _ _ hargs) _ _
  have htarget := model.codeOf_targetIndex s c vps vargs
  have hentry : _ ∈ model.toModel.block vps := entry_mem_indSet (model.mapsTo vps)
    (CtorCode.argSet_mono happroximation _ vps hargs)
  rw [htarget] at hentry
  have hvalue := hmaj ▸ propVal_mem_propSet (level := model.toModel.level)
    (entryValue_mem_fibre hentry)
  rwa [htarget, recrCaseMotive, fibre_bundleMotive_propVal hentry, entry_eq, fst_pair,
    snd_pair, ← hmaj, fibre_bundleMotive_typed s _ hvalue]

include hatoms hsorts hctors in
theorem StrongInductiveModel.recrCaseDomain_denotes
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots (ι.nparams + ι.nsorts))
    (hps : (fun p => γ (p.castAdd ι.nsorts)) ∈ Reachable Set.univ model.paramsSem) :
    ε₂[γ]⟦(I.map pre.sigs).caseFnType η ls
      (fun param => Expr.var (param.castLE (by omega)))
      (fun s => Expr.var ⟨ι.nparams + s.val, by omega⟩)
      s c⟧ = model.recrCaseDomain s c γ := by
  let sig := ι.ctors s c
  let C := I.ctors s c
  let source := (model.ctors s c).source
  let ps : Subst ζ₂ 0 ι.nparams (ι.nparams + ι.nsorts) := fun p => .var (p.castAdd ι.nsorts)
  let vps : Slots ι.nparams := fun p => γ (p.castAdd ι.nsorts)
  let vms : Slots ι.nsorts := fun s => γ (s.natAdd ι.nparams)
  change ε₂[γ]⟦(I.map pre.sigs).caseFnType η ls ps
    (fun s => .var (s.natAdd ι.nparams)) s c⟧ = _
  have hord := source.ordinary.realizes.mapInst pre hatoms
  simp at hord
  simp only [Inductive.caseFnType, Inductive.caseTele, Ctor.fieldTele,
    Ctx.pi, Tele.foldr_append]
  apply hord.denotes_fold_subst Expr.forallE Aczel.pi (fun _ _ _ => rfl)
    (fun _ _ _ h => Aczel.pi_congr h) ps γ vps hps rfl
  intro values hvalues
  let δ := Fin.append vps values
  let ξ := Fin.append γ values
  have hδ : δ ∈ Reachable Set.univ (model.params.append source.ordinary).sem :=
    Reachable.append (Reachable.mono hvalues (Set.singleton_subset_iff.mpr hps))
  have hrec (f : Fin sig.nrecFields) :
      ε₂[ξ]⟦((C.map pre.sigs).recursive f).instantiatedType η ls
        (fun p => (ps p).wkN sig.nfields) (Fin.append (fun p => (ps p).wkN sig.nfields)
          (Expr.boundVars (ι.nparams + ι.nsorts) sig.nfields 0))⟧ =
      typedRecFieldSet (source.code.recursive f).tele (source.code.recursive f).index
        (model.toModel.block vps) model.toModel.level δ := by
    have h := StrongRecursiveFieldSource.type_denotes (C.recursive f) (source.recursive f)
      pre hatoms (σ := ps.liftN sig.nfields)
      (block := fun current => model.toModel.block fun p => current (p.castAdd sig.nfields))
      ξ δ hδ (by
        rw [Expr.denote_substLiftN]
        simp [Expr.denote, ξ, δ, ps, vps])
      (hsorts _) (fun final _ => model.recursiveField_apply s c f final)
    simpa [Subst.liftN_eq_append, δ, sig, C, Ctor.map] using h
  change ε₂[ξ]⟦(Ctx.ofTypes _).pi ((Ctx.ofTypes _).pi _)⟧ = _
  rw [Expr.denote_pi_ofTypes]
  simp only [Fin.castLE_refl]
  change Aczel.pis (fun f => ε₂[ξ]⟦((C.map pre.sigs).recursive f).instantiatedType η ls
    (fun p => (ps p).wkN sig.nfields) (Fin.append (fun p => (ps p).wkN sig.nfields)
      (Expr.boundVars (ι.nparams + ι.nsorts) sig.nfields 0))⟧) _ = _
  rw [funext hrec]
  apply Aczel.pis_congr
  intro fields hfields
  rw [Expr.denote_pi_ofTypes]
  have hih (f : Fin sig.nrecFields) :
      ε₂[Fin.append ξ fields]⟦(C.map pre.sigs).ihType ls ps
        (fun s => .var (s.natAdd ι.nparams)) f⟧ =
      ihType (source.code.recursive f).tele (source.code.recursive f).index
        (model.recrCaseMotive vps vms) δ (fields f) := by
    let σ := Fin.append (sig.fieldParams ps)
      (sig.fieldOrdinary (n := ι.nparams + ι.nsorts))
    have h := StrongRecursiveFieldSource.ihType_denotes (C.recursive f) (source.recursive f)
      pre hatoms (Fin.append ξ fields) δ hδ (σ := σ)
      (ms := fun s => ((Expr.var (s.natAdd ι.nparams)).wkN sig.nfields).wkN sig.nrecFields)
      (e := sig.fieldRecursive f) (motive := model.recrCaseMotive vps vms)
      (domain := fun final => propSet model.toModel.level
        (fibreOp (model.toModel.block vps) ((source.code.recursive f).index final)))
      (by
        funext v
        cases v using Fin.addCases <;>
          simp [Expr.denote, σ, ps, δ, ξ, vps, sig, CtorSig.fieldParams, CtorSig.fieldOrdinary])
      (by
        simp only [CtorSig.fieldRecursive, Expr.denote, sig, Fin.append_right]
        exact hfields f)
      (fun final hfinal value hvalue => by
        change value ∈ propSet model.toModel.level
          (fibreOp (model.toModel.block vps) ((source.code.recursive f).index final)) at hvalue
        simpa [Expr.denote, recrCaseMotive, vms, ξ, sig] using
          (fibre_bundleMotive_typed (vms := vms) (sig.recursiveTarget f)
            (ε₁[final]⟦(C.recursive f).indices{ls} ·⟧) hvalue).symm)
    simpa only [Ctor.ihType, Ctor.ihTypeWith, Ctor.map, CtorSig.fieldRecursive,
      Expr.denote, Fin.append_right] using h
  change Aczel.pis (fun f => ε₂[Fin.append ξ fields]⟦(C.map pre.sigs).ihType ls ps
    (fun s => .var (s.natAdd ι.nparams)) f⟧) _ = _
  rw [funext hih]
  apply Aczel.pis_congr
  intro ihs _
  have htarget (i : Fin (ι.nindices s)) :
      ε₂[Fin.append (Fin.append ξ fields) ihs]⟦(C.map pre.sigs).targetIndex ls
        (sig.caseParams ps) sig.caseOrdinary i⟧ = model.targetValues s c δ i := by
    have h := (Expr.denote_map pre.sigs hatoms _ _).trans (source.targetValues_denotes δ hδ i)
    rw [Expr.map_instL] at h
    simp only [Ctor.targetIndex, Expr.denote_subst, Fin.append_comp, CtorSig.caseParams,
      CtorSig.fieldParams, CtorSig.caseOrdinary, CtorSig.fieldOrdinary, Expr.var_wkN]
    simp only [Expr.denote, δ, ξ, ps, vps, sig, Expr.var_wkN,
      Fin.append_left, Fin.append_right]
    exact h
  simp only [Inductive.caseType, Inductive.motiveResult, Expr.denote, Expr.denote_apps,
    CtorSig.caseParams, CtorSig.caseOrdinary, CtorSig.caseRecursive,
    CtorSig.fieldParams, CtorSig.fieldOrdinary, CtorSig.fieldRecursive, Expr.var_wkN]
  simp only [ξ, ps, Expr.var_wkN, Expr.denote, Fin.append_left, Fin.append_right]
  change [zf|$(vms s) $((ε₂[Fin.append (Fin.append ξ fields) ihs]⟦
    (C.map pre.sigs).targetIndex ls (sig.caseParams ps) sig.caseOrdinary ·⟧))...
    $(ε₂ (.ctor η s c ls vps values fields))] = _
  rw [funext htarget, hctors]

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
  Realizes.ofTypes fun tag γ hγ =>
    let ⟨s, c⟩ := Fin.decodeSigma ι.nctors tag
    model.recrCaseDomain_denotes pre hatoms hsorts hctors s c γ (Reachable.base hγ)

end StrongInductiveModel

end Metalean
