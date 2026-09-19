/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Recursor.Cases
public import Metalean.SetSemantics.Environment.Inductive.Recursor.Witness
public import Metalean.Syntax.Inductive.Recursor.Substitution
import Metalean.Grind
import Metalean.SetSemantics.InductiveComputation
import Metalean.Syntax.Inductive.Recursor
import Metalean.Syntax.Substitution

@[expose] public section

universe u

namespace Metalean

open ZFSet

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  (model : StrongInductiveModel E₁ ε₁ I ls)
  (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
  (hctors : ∀ s c vps vfds vrecFds,
    ε₂ (.ctor η s c ls vps vfds vrecFds) = model.ctorResult s c vps vfds vrecFds)
  (s : Fin ι.nsorts) (l : Level 0) (γ : RecSlots.{u} ι s)

namespace StrongInductiveModel

noncomputable def recrPrefixSem :
    SemTele 0 (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
  model.paramsSem ++ model.recrMotivesSem l ++ model.recrCasesSem

noncomputable def recrIndicesSem :
    SemTele (ι.nparams + ι.nsorts + Fin.sum ι.nctors)
      (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s) :=
  (model.indicesSem s).pull (RecSlots.recrParams) (ι.nindices s)

noncomputable def recrMajorDomain :
    Dom (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s) :=
  fun γ => model.toModel.sortValue s
    (fun param : Fin ι.nparams => γ (param.castLE (by omega)))
    (RecSlots.recrIndices s γ)

noncomputable def recrTeleSem :
    SemTele 0 (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) :=
  (model.recrPrefixSem l ++ model.recrIndicesSem s).snoc (model.recrMajorDomain s)

include hatoms hsorts hctors in
theorem recrPrefixRealizes :
    Realizes ε₂ zeroNs Set.univ
      (Ctx.instL ls (I.map pre.sigs).params ++ (I.map pre.sigs).motiveBinders η ls l ++
        (I.map pre.sigs).caseBinders η ls)
      (model.recrPrefixSem l) :=
  ((model.tele.params.realizes_mapInst pre hatoms).append
    (model.recrMotivesRealizes pre hatoms hsorts l)).append
    ((model.recrCasesRealizes pre hatoms hsorts hctors l).monoReach
      fun _ => Reachable.of_append)

include hatoms in
theorem recrIndicesRealizes :
    Realizes ε₂ zeroNs (Reachable Set.univ (model.recrPrefixSem l))
      ((I.map pre.sigs).indexTele ls s fun param => .var (param.castLE (by omega)))
      (model.recrIndicesSem s) := by
  have his := ((model.tele.indices s).realizes_mapInst pre hatoms).pull
    (reach₁ := Reachable Set.univ (model.recrPrefixSem l))
    (fun param => .var (param.castLE (by omega))) (RecSlots.recrParams (ι := ι))
    (fun _ hγ =>
      (Reachable.base (Reachable.of_append (Reachable.base (Reachable.of_append hγ))) :))
    fun γ _ param => rfl
  simpa [Inductive.map, recrIndicesSem, indicesSem, Inductive.indexTele] using his

include hatoms hsorts hctors in
theorem recrTeleRealizes :
    Realizes ε₂ zeroNs Set.univ ((I.map pre.sigs).recrTele η s ls l)
      (model.recrTeleSem s l) := by
  refine .snoc ((model.recrPrefixRealizes pre hatoms hsorts hctors l).append
    (model.recrIndicesRealizes pre hatoms s l)) fun γ _ => ?_
  simp only [Expr.var_wkN]
  exact hsorts s (fun p => γ (p.castLE (by omega))) (RecSlots.recrIndices s γ)

include hatoms hsorts hctors in
theorem recrArgs_reachable {n : Nat} {γ : Slots n} {s : Fin ι.nsorts}
    {ps : Fin ι.nparams → Expr ζ₂ 0 n} {ms : Fin ι.nsorts → Expr ζ₂ 0 n}
    {mins : (target : Fin ι.nsorts) → Fin (ι.nctors target) → Expr ζ₂ 0 n}
    {is : Fin (ι.nindices s) → Expr ζ₂ 0 n} {maj : Expr ζ₂ 0 n}
    (hps : ∀ param, ε₂[γ]⟦ps param⟧ ∈ ε₂[γ]⟦(I.map pre.sigs).paramType ls ps param⟧)
    (hms : ∀ target, ε₂[γ]⟦ms target⟧ ∈ ε₂[γ]⟦(I.map pre.sigs).motiveType η ls ps l target⟧)
    (hmins : ∀ target ctor, ε₂[γ]⟦mins target ctor⟧ ∈
      ε₂[γ]⟦(I.map pre.sigs).caseFnType η ls ps ms target ctor⟧)
    (his : ∀ index, ε₂[γ]⟦is index⟧ ∈ ε₂[γ]⟦(I.map pre.sigs).indexType ls s ps is index⟧)
    (hmaj : ε₂[γ]⟦maj⟧ ∈ ε₂[γ]⟦.ind η s ls ps is⟧) :
    RecSlots.args (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦ms ·⟧) (ε₂[γ]⟦mins · ·⟧) (ε₂[γ]⟦is ·⟧) ε₂[γ]⟦maj⟧ ∈
      Reachable Set.univ (model.recrTeleSem s l) :=
  RecSlots.denote_recrSubst ε₂ zeroNs γ ps ms mins is maj ▸
    SemDefeq.reachable (model.recrTeleRealizes pre hatoms hsorts hctors s l)
      (SemDefeq.recrSubst · (fun param => ⟨rfl, hps param⟩) (fun target => ⟨rfl, hms target⟩)
        (fun target ctor => ⟨rfl, hmins target ctor⟩) (fun index => ⟨rfl, his index⟩)
        ⟨rfl, hmaj⟩)

noncomputable def recrMajorOf : ZFSet :=
  propGet model.toModel.level (fibreOp (model.toModel.block (RecSlots.paramsOf γ))
    (sortKey s.val (RecSlots.indicesOfSlots γ))) (RecSlots.majorOfSlots γ)

noncomputable def recrState : ZFSet :=
  [zf|($(sortKey s.val (RecSlots.indicesOfSlots γ)), $(model.recrMajorOf s γ))]

noncomputable def recrGraph : ZFSet :=
  recGraph model.toModel.codes model.toModel.bound
    (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
    (stepGraph model.toModel.level (model.toModel.block (RecSlots.paramsOf γ))
      (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
      (RecSlots.paramsOf γ) (minorFamily (RecSlots.casesOf γ)) model.toModel.codes)
    (RecSlots.paramsOf γ)

variable (hγ : γ ∈ Reachable Set.univ (model.recrTeleSem s l))

include hγ

theorem recrSortReachable : Fin.append (RecSlots.paramsOf γ) (RecSlots.indexValuesOf γ) ∈
    Reachable Set.univ (model.sortSem s) :=
  Reachable.append <|
    Reachable.pull (Reachable.of_append (Reachable.init hγ)) fun _ hbase =>
      (Reachable.base (Reachable.of_append (Reachable.base (Reachable.of_append hbase))) :)

@[reachability →] theorem recrParamsReachable :
    RecSlots.paramsOf γ ∈ Reachable Set.univ model.paramsSem := by
  simpa using
    Reachable.base (Reachable.of_append (model.recrSortReachable s l γ hγ))

theorem recrMajorOf_erased : RecSlots.majorOfSlots γ ∈ propSet model.toModel.level
    (fibreOp (model.toModel.block (RecSlots.paramsOf γ))
      (sortKey s.val (RecSlots.indicesOfSlots γ))) :=
  Reachable.last hγ

theorem recrState_mem : model.recrState s γ ∈ model.toModel.block (RecSlots.paramsOf γ) :=
  mem_fibre.mp (propGet_mem (model.recrMajorOf_erased s l γ hγ))

theorem propVal_recrMajorOf :
    propVal model.toModel.level (model.recrMajorOf s γ) = RecSlots.majorOfSlots γ :=
  propVal_propGet (model.recrMajorOf_erased s l γ hγ)

theorem fibre_motive_recrState :
    fibreOp (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
      (model.recrState s γ) =
        [zf|$(RecSlots.motivesOf γ s) $(RecSlots.indexValuesOf γ)...
          $(RecSlots.majorOfSlots γ)] := by
  rw [recrCaseMotive, fibre_bundleMotive_propVal (model.recrState_mem s l γ hγ), recrState,
    snd_pair, model.propVal_recrMajorOf s l γ hγ]
  simpa [RecSlots.indicesOfSlots] using
    fibre_bundleMotive_typed s (RecSlots.indexValuesOf γ) (model.recrMajorOf_erased s l γ hγ)

theorem recrMotiveResult_mem_sort :
    [zf|$(RecSlots.motivesOf γ s) $(RecSlots.indexValuesOf γ)... $(RecSlots.majorOfSlots γ)] ∈
      S_ (l.eval zeroNs) := by
  have hprefix := Reachable.base (Reachable.of_append (Reachable.init hγ))
  rw [recrPrefixSem] at hprefix
  let final : Slots (ι.nparams + ι.nindices s + 1) :=
    Fin.snoc (Fin.append (RecSlots.paramsOf γ) (RecSlots.indexValuesOf γ))
      (RecSlots.majorOfSlots γ)
  have hmaj : RecSlots.majorOfSlots γ ∈
      model.toModel.sortValue s (RecSlots.paramsOf γ) (RecSlots.indexValuesOf γ) := by
    simpa [InductiveModel.sortValue, RecSlots.indicesOfSlots] using
      model.recrMajorOf_erased s l γ hγ
  have hfinal :
      final ∈ Reachable (Reachable Set.univ model.paramsSem) (model.recrMotiveTele s) :=
    .snoc (by simpa [final] using Reachable.of_append (model.recrSortReachable s l γ hγ))
      (by simpa [final] using hmaj)
  have hsuffix : (fun f : Fin (ι.nindices s + 1) => final (Fin.natAdd ι.nparams f)) =
      Fin.snoc (RecSlots.indexValuesOf γ) (RecSlots.majorOfSlots γ) := by
    simpa using Slots.natAdd_snoc (Fin.append (RecSlots.paramsOf γ) (RecSlots.indexValuesOf γ))
      (RecSlots.majorOfSlots γ)
  have hmotive : RecSlots.motivesOf γ s ∈ model.recrMotiveValue s l (RecSlots.paramsOf γ) :=
    Reachable.ofDoms_mem (Reachable.of_append (Reachable.base (Reachable.of_append hprefix))) s
  simpa [hsuffix] using
    Reachable.apps_mem_of_base (k := ι.nindices s + 1) hfinal (by simp [final]) hmotive

theorem eq_proof_of_mem_fibre_motive (hl : l.eval zeroNs = 0) {value : ZFSet}
    (hvalue : value ∈ fibreOp
      (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ)) (model.recrState s γ)) :
    value = proof := by
  have hsorted := model.recrMotiveResult_mem_sort s l γ hγ
  rw [← model.fibre_motive_recrState s l γ hγ, hl] at hsorted
  exact mem_verum.mp (eq_verum_of_mem hsorted hvalue ▸ hvalue)

theorem recrBody_denotes :
    ε₂[γ]⟦ι.recrBody s⟧ = propSet (l.eval zeroNs)
      (fibreOp (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
        (model.recrState s γ)) := by
  rw [model.fibre_motive_recrState s l γ hγ,
    propSet_eq_self_of_mem_sort (model.recrMotiveResult_mem_sort s l γ hγ)]
  simp! [IndSig.recrBody, Inductive.motiveResult]
  rfl

theorem recrStepSound :
    StepSound model.toModel.codes (model.toModel.block (RecSlots.paramsOf γ))
      (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
      (stepGraph model.toModel.level (model.toModel.block (RecSlots.paramsOf γ))
        (model.recrCaseMotive (RecSlots.paramsOf γ) (RecSlots.motivesOf γ))
        (RecSlots.paramsOf γ) (minorFamily (RecSlots.casesOf γ)) model.toModel.codes)
      (RecSlots.paramsOf γ) := by
  let caseSlots : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
    fun current => γ (current.castLE (by omega))
  let motiveSlots : Slots (ι.nparams + ι.nsorts) := fun current => γ (current.castLE (by omega))
  have hprefix := Reachable.base (Reachable.of_append (Reachable.init hγ))
  rw [recrPrefixSem] at hprefix
  have hcaseReach : caseSlots ∈ Reachable (Reachable (Reachable Set.univ model.paramsSem)
      (model.recrMotivesSem l)) model.recrCasesSem :=
    Reachable.mono (Reachable.of_append hprefix) fun _ hbase => Reachable.of_append hbase
  have hmsReach : motiveSlots ∈
      Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l) :=
    (Reachable.base hcaseReach :)
  intro s₁ c vargs hargs
  have hminor : RecSlots.casesOf γ (Fin.encodeSigma ι.nctors ⟨s₁, c⟩) ∈
      model.recrCaseDomain s₁ c motiveSlots :=
    model.recrCasesSem_mem l caseSlots hcaseReach s₁ c
  have hminorEq : [zf|$(minorFamily (RecSlots.casesOf γ)) $(encode (tagOf s₁ c))] =
      RecSlots.casesOf γ (Fin.encodeSigma ι.nctors ⟨s₁, c⟩) :=
    app_minorFamily (vmins := RecSlots.casesOf γ) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩)
  rw [app_stepGraph hargs, hminorEq]
  rw [← Fin.append_castAdd_natAdd (f := motiveSlots)] at hmsReach hminor
  exact model.recrCase_applyMinor_mem l s₁ c _ _ hmsReach _ hminor vargs hargs

end StrongInductiveModel

end Metalean
