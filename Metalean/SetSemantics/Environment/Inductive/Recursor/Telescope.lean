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
  (model.indicesSem s).pull (fun γ p => γ (p.castLE (by omega))) (ι.nindices s)

noncomputable def recrMajorDomain :
    Dom (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s) :=
  fun γ => model.toModel.sortValue s
    (fun param : Fin ι.nparams =>
      γ (((param.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors)).castAdd (ι.nindices s)))
    (fun i => γ (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) i))

noncomputable def recrTeleSem :
    SemTele 0 (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) :=
  (model.recrPrefixSem l ++ model.recrIndicesSem s).snoc (model.recrMajorDomain s)

include hatoms hsorts hctors in
theorem recrPrefixRealizes :
    Realizes ε₂ ![] Set.univ
      ((I.map pre.sigs).params{ls} ++ (I.map pre.sigs).motiveBinders η ls l ++
        (I.map pre.sigs).caseBinders η ls)
      (model.recrPrefixSem l) :=
  ((model.tele.params.realizes.mapInst pre hatoms).append
    (model.recrMotivesRealizes pre hatoms hsorts l)).append
    ((model.recrCasesRealizes pre hatoms hsorts hctors l).monoReach
      fun _ => Reachable.of_append)

include hatoms in
theorem recrIndicesRealizes :
    Realizes ε₂ ![] (Reachable Set.univ (model.recrPrefixSem l))
      ((I.map pre.sigs).indexTele ls s fun param => .var (param.castLE (by omega)))
      (model.recrIndicesSem s) := by
  have his := ((model.tele.indices s).realizes.mapInst pre hatoms).pull
    (reach₁ := Reachable Set.univ (model.recrPrefixSem l))
    (fun param => .var (param.castLE (by omega))) (fun γ p => γ (p.castLE (by omega)))
    (fun _ hγ =>
      (Reachable.base (Reachable.of_append (Reachable.base (Reachable.of_append hγ))) :))
    fun γ _ param => rfl
  simpa [Inductive.map, recrIndicesSem, indicesSem, Inductive.indexTele] using his

include hatoms hsorts hctors in
theorem recrTeleRealizes :
    Realizes ε₂ ![] Set.univ ((I.map pre.sigs).recrTele η s ls l)
      (model.recrTeleSem s l) := by
  refine .snoc ((model.recrPrefixRealizes pre hatoms hsorts hctors l).append
    (model.recrIndicesRealizes pre hatoms s l)) fun γ _ => ?_
  simp only [Expr.var_wkN]
  exact hsorts s (fun p => γ (p.castLE (by omega))) (fun i => γ (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) i))

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
    (RecSlots.args (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦ms ·⟧) (ε₂[γ]⟦mins · ·⟧) (ε₂[γ]⟦is ·⟧) ε₂[γ]⟦maj⟧).valuation ∈
      Reachable Set.univ (model.recrTeleSem s l) :=
  RecSlots.denote_recrSubst ε₂ ![] γ ps ms mins is maj ▸
    SemDefeq.reachable (model.recrTeleRealizes pre hatoms hsorts hctors s l)
      (Inductive.forall_recrSubst (motive := fun _ e₁ e₂ t => ε₂[γ] ⊨ e₁ ≡ e₂ : t)
        (fun param => ⟨rfl, hps param⟩) (fun target => ⟨rfl, hms target⟩)
        (fun target ctor => ⟨rfl, hmins target ctor⟩) (fun index => ⟨rfl, his index⟩)
        ⟨rfl, hmaj⟩)

noncomputable def recrMajorOf : ZFSet :=
  propGet model.toModel.level (fibreOp (model.toModel.block (RecSlots.params γ))
    (sortKey s.val (encode (RecSlots.indices γ)))) (RecSlots.major γ)

noncomputable def recrState : ZFSet :=
  [zf|($(sortKey s.val (encode (RecSlots.indices γ))), $(model.recrMajorOf s γ))]

noncomputable def recrGraph : ZFSet :=
  recGraph model.toModel.codes model.toModel.bound
    (model.recrCaseMotive γ.params γ.motives) model.toModel.level
    (minorFamily γ.cases) γ.params

variable (hγ : γ.valuation ∈ Reachable Set.univ (model.recrTeleSem s l))

include hγ

theorem recrSortReachable : Fin.append (RecSlots.params γ) (RecSlots.indices γ) ∈
    Reachable Set.univ (model.sortSem s) :=
  by
    apply Reachable.append
    have h := Reachable.pull (Reachable.of_append (Reachable.init hγ))
      (fun _ hbase =>
        (Reachable.base (Reachable.of_append (Reachable.base (Reachable.of_append hbase))) :))
    simpa [RecSlots.valuation, RecSlots.prefixValues, Slots.pull] using h

@[reachability →] theorem recrParamsReachable :
    RecSlots.params γ ∈ Reachable Set.univ model.paramsSem := by
  simpa using
    Reachable.base (Reachable.of_append (model.recrSortReachable s l γ hγ))

theorem recrChildReachable {s₁ : Fin ι.nsorts} (indices : Slots (ι.nindices s₁))
    (his : Fin.append γ.params indices ∈
      Reachable (Reachable Set.univ model.paramsSem) (model.indicesSem s₁))
    (major : ZFSet) (hmaj : major ∈ model.toModel.sortValue s₁ γ.params indices) :
    (RecSlots.mk γ.params γ.motives γ.cases indices major).valuation ∈
      Reachable Set.univ (model.recrTeleSem s₁ l) := by
  have hprefix : γ.prefixValues ∈ Reachable Set.univ (model.recrPrefixSem l) := by
    simpa [RecSlots.valuation] using Reachable.base (Reachable.of_append (Reachable.init hγ))
  have hindices : Fin.append γ.prefixValues indices ∈
      Reachable (Reachable Set.univ (model.recrPrefixSem l)) (model.recrIndicesSem s₁) :=
    Reachable.of_pull (by simpa [Slots.pull_append, RecSlots.prefixValues] using his) (by simpa using hprefix)
  change (Fin.snoc (Fin.append γ.prefixValues indices) major :
      Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s₁ + 1)) ∈
    Reachable Set.univ (model.recrTeleSem s₁ l)
  refine Reachable.snoc (by simpa using Reachable.append hindices) ?_
  simpa [recrMajorDomain, RecSlots.prefixValues] using hmaj

theorem recrMajorOf_erased : RecSlots.major γ ∈ propSet model.toModel.level
    (fibreOp (model.toModel.block (RecSlots.params γ))
      (sortKey s.val (encode (RecSlots.indices γ)))) :=
  by simpa [RecSlots.valuation, RecSlots.prefixValues, recrMajorDomain, InductiveModel.sortValue] using Reachable.last hγ

theorem recrState_mem : model.recrState s γ ∈ model.toModel.block (RecSlots.params γ) :=
  mem_fibre.mp (propGet_mem (model.recrMajorOf_erased s l γ hγ))

theorem propVal_recrMajorOf :
    propVal model.toModel.level (model.recrMajorOf s γ) = RecSlots.major γ :=
  propVal_propGet (model.recrMajorOf_erased s l γ hγ)

theorem fibre_motive_recrState :
    fibreOp (model.recrCaseMotive (RecSlots.params γ) (RecSlots.motives γ))
      (model.recrState s γ) =
        [zf|$(RecSlots.motives γ s) $(RecSlots.indices γ)...
          $(RecSlots.major γ)] := by
  rw [recrCaseMotive, fibre_bundleMotive_propVal (model.recrState_mem s l γ hγ), recrState,
    snd_pair, model.propVal_recrMajorOf s l γ hγ]
  simpa [RecSlots.args] using
    fibre_bundleMotive_typed s (RecSlots.indices γ) (model.recrMajorOf_erased s l γ hγ)

theorem recrMotiveResult_mem_sort :
    [zf|$(RecSlots.motives γ s) $(RecSlots.indices γ)... $(RecSlots.major γ)] ∈
      S_ (l.eval ![]) := by
  have hprefix := Reachable.base (Reachable.of_append (Reachable.init hγ))
  rw [recrPrefixSem] at hprefix
  let final : Slots (ι.nparams + ι.nindices s + 1) :=
    Fin.snoc (Fin.append (RecSlots.params γ) (RecSlots.indices γ))
      (RecSlots.major γ)
  have hmaj : RecSlots.major γ ∈
      model.toModel.sortValue s (RecSlots.params γ) (RecSlots.indices γ) := by
    simpa [InductiveModel.sortValue] using
      model.recrMajorOf_erased s l γ hγ
  have hfinal :
      final ∈ Reachable (Reachable Set.univ model.paramsSem) (model.recrMotiveTele s) :=
    .snoc (by simpa [final] using Reachable.of_append (model.recrSortReachable s l γ hγ))
      (by simpa [final] using hmaj)
  have hsuffix : (fun f : Fin (ι.nindices s + 1) => final (Fin.natAdd ι.nparams f)) =
      Fin.snoc (RecSlots.indices γ) (RecSlots.major γ) := by
    simpa [Function.comp_def] using Fin.snoc_comp_natAdd (Fin.append (RecSlots.params γ) (RecSlots.indices γ))
      (RecSlots.major γ)
  have hmotive : RecSlots.motives γ s ∈ model.recrMotiveValue s l (RecSlots.params γ) :=
    by simpa [RecSlots.valuation, RecSlots.prefixValues] using
      Reachable.ofDoms_mem (Reachable.of_append (Reachable.base (Reachable.of_append hprefix))) s
  simpa [hsuffix] using
    Reachable.apps_mem_of_base (k := ι.nindices s + 1) hfinal (by simp [final]) hmotive

theorem eq_proof_of_mem_fibre_motive (hl : l.eval ![] = 0) {value : ZFSet}
    (hvalue : value ∈ fibreOp
      (model.recrCaseMotive (RecSlots.params γ) (RecSlots.motives γ)) (model.recrState s γ)) :
    value = proof := by
  have hsorted := model.recrMotiveResult_mem_sort s l γ hγ
  rw [← model.fibre_motive_recrState s l γ hγ, hl] at hsorted
  exact mem_verum.mp (eq_verum_of_mem hsorted hvalue ▸ hvalue)

theorem recrBody_denotes :
    ε₂[γ]⟦ι.recrBody s⟧ = propSet (l.eval ![])
      (fibreOp (model.recrCaseMotive (RecSlots.params γ) (RecSlots.motives γ))
        (model.recrState s γ)) := by
  rw [model.fibre_motive_recrState s l γ hγ,
    propSet_eq_self_of_mem_sort (model.recrMotiveResult_mem_sort s l γ hγ)]
  simp! [IndSig.recrBody, Inductive.motiveResult, RecSlots.valuation, RecSlots.prefixValues,
    IndSig.casesEnd, IndSig.motivesEnd, Fin.natAdd_castSucc, -Fin.castSucc_natAdd]

theorem recrStepSound :
    StepSound model.toModel.codes (model.toModel.block (RecSlots.params γ))
      (model.recrCaseMotive γ.params γ.motives) model.toModel.level
      (minorFamily γ.cases) γ.params := by
  have hprefix : γ.prefixValues ∈ Reachable Set.univ (model.recrPrefixSem l) := by
    simpa [RecSlots.valuation] using Reachable.base (Reachable.of_append (Reachable.init hγ))
  rw [recrPrefixSem] at hprefix
  have hcaseReach := Reachable.mono (Reachable.of_append hprefix)
    (fun _ hbase => Reachable.of_append hbase)
  have hmsReach : Fin.append γ.params γ.motives ∈
      Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l) := by
    simpa [RecSlots.prefixValues] using Reachable.base hcaseReach
  intro approximation happroximation graph hgraph s₁ c vargs hargs
  have hminor : RecSlots.cases γ (Fin.encodeSigma ι.nctors ⟨s₁, c⟩) ∈
      model.recrCaseDomain s₁ c (Fin.append γ.params γ.motives) :=
    by simpa [RecSlots.prefixValues] using
      model.recrCasesSem_mem l γ.prefixValues hcaseReach s₁ c
  have hminorEq : [zf|$(minorFamily (RecSlots.cases γ)) $(encode (tagOf s₁ c))] =
      RecSlots.cases γ (Fin.encodeSigma ι.nctors ⟨s₁, c⟩) :=
    app_minorFamily (vmins := RecSlots.cases γ) (Fin.encodeSigma ι.nctors ⟨s₁, c⟩)
  rw [hminorEq]
  exact model.recrCase_applyMinor_mem l s₁ c _ _ hmsReach _ hminor approximation happroximation graph hgraph vargs hargs

end StrongInductiveModel

end Metalean
