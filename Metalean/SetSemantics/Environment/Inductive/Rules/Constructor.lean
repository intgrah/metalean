/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
import Metalean.SetSemantics.InductiveComputation
import Metalean.Syntax.Substitution

@[expose] public section

universe u

namespace Metalean

open ZFSet

variable {n : Nat}
  {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {γ : Slots n}
  {ps : Fin ι.nparams → Expr ζ₂ 0 n}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ 0 n}

namespace StrongInductiveModel

variable (model : StrongInductiveModel E₁ ε₁ I ls)

noncomputable def recCode
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields) :=
  StrongRecursiveFieldSource.code ((I.ctors s c).recursive f)
    ((model.ctors s c).source.recursive f)

noncomputable def recFieldSet
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields) (vps : Slots ι.nparams)
    (fieldSlots : Slots (ι.nparams + (ι.ctors s c).nfields)) :=
  typedRecFieldSet (model.recCode s c f).tele (model.recCode s c f).index
    (model.toModel.block vps) model.toModel.level fieldSlots

section

variable (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
  (hparamReach : (ε₂[γ]⟦ps ·⟧) ∈ Reachable Set.univ model.paramsSem)
  (hfieldsReach : Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧) ∈
    Reachable {(ε₂[γ]⟦ps ·⟧)} (model.ctors s c).source.ordinary.sem)

include hatoms hsorts in
theorem paramsReachable {ps₂ : Fin ι.nparams → Expr ζ₂ 0 n}
    (hps : ∀ param, ε₂[γ] ⊨ ps param ≡ ps₂ param :
      (I.map pre.sigs).paramType ls ps param) :
    (ε₂[γ]⟦ps ·⟧) ∈ Reachable Set.univ model.paramsSem :=
  SemDefeq.reachable (model.realizes pre hatoms hsorts).params fun param => by
    rw [Ctx.get_subst _ _ param param.val param.isLt rfl]
    simpa [Inductive.paramType] using hps param

include hatoms hparamReach in
theorem fieldSlotsReachable
    {fds₁ : Fin (ι.ctors s c).nfields → Expr ζ₂ 0 n}
    (hfields : ∀ f, ε₂[γ] ⊨ fds f ≡ fds₁ f :
      ((((I.map pre.sigs).ctors s c).ordinaryType f).instL ls).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) :
    Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧) ∈
      Reachable {(ε₂[γ]⟦ps ·⟧)} (model.ctors s c).source.ordinary.sem := by
  have hsourceMap : Realizes ε₂ zeroNs
      {(ε₂[γ]⟦ps ·⟧)}
      (Ctx.instL ls ((I.ctors s c).map pre.sigs).ordinaryTele)
      (model.ctors s c).source.ordinary.sem :=
    (congrArg (fun Δ => Realizes ε₂ zeroNs _ Δ _)
      ((Ctx.map_instL pre.sigs ls (I.ctors s c).ordinaryTele).trans
        (congrArg (Ctx.instL ls) (Ctor.ordinaryTele_map pre.sigs (I.ctors s c))))).mp
          (((model.ctors s c).source.ordinary.realizes.monoReach
            (reach₂ := {(ε₂[γ]⟦ps ·⟧)})
            (Set.singleton_subset_iff.mpr hparamReach)).map pre hatoms)
  apply hsourceMap.reachable_subst (γ := γ) (Γ := (I.map pre.sigs).params.instL ls)
    (Fin.append ps fds) (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧))
  · simp
  · intro v
    cases v using Fin.addCases <;> simp
  · intro f hfield
    cases f using Fin.addCases with
    | left param => exact ((Nat.not_le_of_gt param.isLt) hfield).elim
    | right current =>
      rw [Ctx.get_subst _ _ (Fin.natAdd ι.nparams current)
        (ι.nparams + current.val) (by omega) (by simp),
        Ctx.entry_append_right
          (Ctx.instL ls (I.map pre.sigs).params)
          (Ctx.instL ls
            ((I.ctors s c).map pre.sigs).ordinaryTele)
          (by omega) (by omega) (by omega),
        ← Ctx.entry_instL]
      simpa [Inductive.map] using (hfields current).mem

include hatoms hsorts hparamReach hfieldsReach in
theorem recFieldsMem
    {recFds₁ recFds₂ : Fin (ι.ctors s c).nrecFields → Expr ζ₂ 0 n}
    (hrecFields : ∀ f, ε₂[γ] ⊨ recFds₁ f ≡ recFds₂ f :
      (((I.map pre.sigs).ctors s c).recursive f).instantiatedType η
        ls ps (Fin.append ps fds)) :
    ∀ f, ε₂[γ]⟦recFds₁ f⟧ ∈ model.recFieldSet s c f (ε₂[γ]⟦ps ·⟧)
      (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧)) := by
  intro f
  have hdomain := StrongRecursiveFieldSource.denotesDepMapEnv
    (I := I) (block := fun _ => model.toModel.block (ε₂[γ]⟦ps ·⟧))
    (level := model.toModel.level) pre hatoms ((I.ctors s c).recursive f)
    ((model.ctors s c).source.recursive f)
    (fun _ hcurrent =>
      Reachable.append (Reachable.mono hcurrent (Set.singleton_subset_iff.mpr hparamReach)))
    (hsorts _)
    (fun δ hδ => by
      have hpsEq :
          (fun param : Fin ι.nparams =>
            δ (param.castLE (by omega))) = (ε₂[γ]⟦ps ·⟧) := by
        funext param
        simpa using
          congrFun (Set.eq_of_mem_singleton (Reachable.base (Reachable.base hδ))) param
      simpa [hpsEq] using model.recursiveField_apply s c f δ)
    (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧)) hfieldsReach
  suffices heq : _ = model.recFieldSet s c f (ε₂[γ]⟦ps ·⟧)
      (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧)) from heq ▸ (hrecFields f).mem
  simpa [recFieldSet, recCode, Inductive.map, Ctor.map, Expr.subst] using
    (Expr.denote_subst γ (Fin.append ps fds) _).trans
      ((congrArg (fun δ => ε₂[δ]⟦_⟧)
        (Fin.append_comp ps fds fun e => ε₂[γ]⟦e⟧)).trans hdomain)

include hatoms hparamReach hfieldsReach in
theorem targetIndexDenotes (index : Fin (ι.nindices s)) :
    ε₂[γ]⟦((I.map pre.sigs).ctors s c).targetIndex ls ps fds index⟧ =
      model.targetValues s c (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧)) index := by
  simpa [Inductive.map, Ctor.map, Ctor.targetIndex, StrongInductiveModel.targetValues] using
    (Expr.denote_subst γ (Fin.append ps fds) _).trans
      ((congrArg (fun δ => ε₂[δ]⟦_⟧) (Fin.append_comp ps fds fun e => ε₂[γ]⟦e⟧)).trans
        ((Expr.denote_map pre.sigs hatoms _ _).trans ((model.ctors s c).target.denotes
          (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧))
          (Reachable.append
            (Reachable.mono hfieldsReach (Set.singleton_subset_iff.mpr hparamReach))) index)))

include hatoms hsorts hparamReach hfieldsReach in
theorem targetIndexInterp (index : Fin (ι.nindices s)) :
    ε₂[γ] ⊨ ((I.map pre.sigs).ctors s c).targetIndex ls ps fds index ≡
      ((I.map pre.sigs).ctors s c).targetIndex ls ps fds index :
      (I.map pre.sigs).indexType ls s ps
        (fun i => ((I.map pre.sigs).ctors s c).targetIndex ls ps fds i) index := by
  have hrealizes := model.realizes pre hatoms hsorts
  let expressions : Fin (ι.nindices s) → Expr ζ₂ 0 n :=
    fun i => ((I.map pre.sigs).ctors s c).targetIndex ls ps fds i
  let σ : Subst ζ₂ 0 (ι.nparams + ι.nindices s) n :=
    Fin.append ps expressions
  let γ₁ : Slots (ι.nparams + ι.nindices s) :=
    Fin.append (ε₂[γ]⟦ps ·⟧) (model.targetValues s c (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧)))
  have hvalues := (model.ctors s c).target.valuesReachable
    (model.indicesSem s) (model.tele.indices s).realizes
    (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧))
    (Reachable.append (Reachable.mono hfieldsReach (Set.singleton_subset_iff.mpr hparamReach)))
  rw [show (fun param : Fin ι.nparams =>
      Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧) (param.castLE (Nat.le_add_right _ _))) =
      (ε₂[γ]⟦ps ·⟧) from funext (Fin.append_left (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧))] at hvalues
  have hσ : ∀ v, ε₂[γ]⟦σ v⟧ = γ₁ v := by
    intro v
    cases v using Fin.addCases with
    | left param => simp [σ, γ₁]
    | right i =>
      simpa [σ, γ₁] using
        model.targetIndexDenotes pre hatoms hparamReach hfieldsReach i
  have h := (hrealizes.params.append (by simpa using hrealizes.indicesRealizes s)).slot_interp
    (Γ := .nil) σ γ₁ (Reachable.append hvalues) hσ (Fin.natAdd ι.nparams index) (by simp)
  rwa [show σ (Fin.natAdd ι.nparams index) = expressions index by simp [σ],
    show (Ctx.get (Fin.natAdd ι.nparams index)
      ((#t[] : Ctx ζ₂ 0 0 0) ++ (Ctx.instL ls (I.map pre.sigs).params ++
        Ctx.instL ls ((I.map pre.sigs).indices s)))).subst σ =
      (I.map pre.sigs).indexType ls s ps expressions index by
      rw [← Inductive.indexType_eq_get_subst, Tele.nil_append, ← Ctx.instL_append,
        ← Ctx.get_instL]] at h

end

theorem indRuleSound
    (pre : E₁.as ⟶ E₂.as)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ 0 n}
    {is₁ is₂ : Fin (ι.nindices s) → Expr ζ₂ 0 n} :
    (∀ param, ε₂[γ] ⊨ ps₁ param ≡ ps₂ param : (E₂.get η).block.paramType ls ps₁ param) →
    (∀ index, ε₂[γ] ⊨ is₁ index ≡ is₂ index : (E₂.get η).block.indexType ls s ps₁ is₁ index) →
    ε₂[γ] ⊨ .ind η s ls ps₁ is₁ ≡
      .ind η s ls ps₂ is₂ :
      .sort ((E₂.get η).block.level.inst ls) := by
  intro hps his
  refine ⟨?_, ?_⟩
  · simp only [Expr.denote]
    rw [funext fun p => (hps p).eq, funext fun i => (his i).eq]
  · change ε₂ (.ind η s ls _ _) ∈ S_ (((E₂.get η).block.level.inst ls).eval zeroNs)
    rw [hsorts, hblock]
    exact propSet_mem_sort fun k hk =>
      fibreOp_indSet_mem_type (fun s c => model.codeOf_localDoms s c hk) (model.mapsTo _) _

theorem ctorRuleSound
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
    (hctors : ∀ s c vps vfds vrecFds,
      ε₂ (.ctor η s c ls vps vfds vrecFds) = model.ctorResult s c vps vfds vrecFds)
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ 0 n}
    {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ₂ 0 n}
    {recFds₁ recFds₂ : Fin (ι.ctors s c).nrecFields → Expr ζ₂ 0 n} :
    (∀ param, ε₂[γ] ⊨ ps₁ param ≡ ps₂ param : (E₂.get η).block.paramType ls ps₁ param) →
    (∀ f, ε₂[γ] ⊨ fds₁ f ≡ fds₂ f :
      ((((E₂.get η).block.ctors s c).ordinaryType f).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le))) →
    (∀ f, ε₂[γ] ⊨ recFds₁ f ≡ recFds₂ f :
      (((E₂.get η).block.ctors s c).recursive f).instantiatedType η ls ps₁
        (Fin.append ps₁ fds₁)) →
    ε₂[γ] ⊨ .ctor η s c ls ps₁ fds₁ recFds₁ ≡
      .ctor η s c ls ps₂ fds₂ recFds₂ :
      .ind η s ls ps₁ fun index =>
        ((E₂.get η).block.ctors s c).targetIndex ls ps₁ fds₁ index := by
  intro hps hfields hrecFields
  rw [hblock] at hps hfields hrecFields
  let vps : Slots ι.nparams := (ε₂[γ]⟦ps₁ ·⟧)
  let vfds : Fin (ι.ctors s c).nfields → ZFSet := (ε₂[γ]⟦fds₁ ·⟧)
  let vrecFds : Fin (ι.ctors s c).nrecFields → ZFSet := (ε₂[γ]⟦recFds₁ ·⟧)
  have hparamReach := model.paramsReachable pre hatoms hsorts hps
  have hfieldsReach := model.fieldSlotsReachable pre hatoms hparamReach hfields
  have ⟨hargs, hfieldsOf⟩ :=
    model.ctorArgs_mem s c vps vfds hfieldsReach vrecFds
      (model.recFieldsMem pre hatoms hsorts hparamReach hfieldsReach hrecFields)
  refine ⟨?_, ?_⟩
  · simp only [Expr.denote]
    rw [funext fun p => (hps p).eq, funext fun f => (hfields f).eq,
      funext fun f => (hrecFields f).eq]
  · rw [hblock]
    change ε₂ (.ctor η s c ls vps vfds vrecFds) ∈ ε₂ (.ind η s ls vps _)
    rw [hctors, funext fun index =>
      model.targetIndexDenotes pre hatoms hparamReach hfieldsReach index, hsorts]
    have hentry := entry_mem_indSet (model.mapsTo vps) hargs
    have hkey := model.codeOf_targetIndex s c vps (model.ctorArgs s c vps vfds vrecFds)
    rw [hfieldsOf] at hkey
    rw [hkey] at hentry
    exact propVal_mem_propSet (entryValue_mem_fibre
      (by simpa [InductiveModel.block] using hentry))

theorem applyMinor_ctorApplication
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vfds : Slots (ι.ctors s c).nfields)
    (hfields : Fin.append vps vfds ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem)
    (vrecFds : Fin (ι.ctors s c).nrecFields → ZFSet)
    (hrecFields : ∀ f, vrecFds f ∈ model.recFieldSet s c f vps (Fin.append vps vfds))
    (graph minor : ZFSet) :
    (model.codeOf s c).applyMinor model.toModel.level vps minor
        ((model.codeOf s c).argMap graph vps (model.ctorArgs s c vps vfds vrecFds)) =
      [zf|minor vfds... vrecFds... $(fun f =>
          recMap (model.recCode s c f).tele (model.recCode s c f).index graph
            (Fin.append vps vfds)
            (recoverRecField (model.recCode s c f).tele (model.recCode s c f).index
              (model.toModel.block vps) model.toModel.level (Fin.append vps vfds)
              (vrecFds f)))...] := by
  let source := (model.ctors s c).source
  let tele := source.ordinary.sem
  let fields := source.recursiveCodes
  let index := StrongCtorSource.targetIndex (model.ctors s c).target
  let rest := CtorCode.prependRecursive (ι.ctors s c).nrecFields fields (.target index)
  let tail := CtorCode.packRecursive (model.toModel.block vps) fields model.toModel.level
    (Fin.append vps vfds) vrecFds proof
  have htail : tail ∈ rest.argSet (model.toModel.block vps) (Fin.append vps vfds) :=
    CtorCode.packRecursive_mem hrecFields (CtorCode.proof_mem_argSet_target _)
  have hpack := SemTele.pack_mem hfields htail
  have hvalues := tele.values_pack (Fin.append vps vfds) tail
  rw [Set.eq_of_mem_singleton (Reachable.base hfields)] at hpack hvalues
  change (CtorCode.prependOrdinary tele rest).applyMinor model.toModel.level vps minor
    ((CtorCode.prependOrdinary tele rest).argMap graph vps
      (tele.pack (Fin.append vps vfds) tail)) = _
  rw [CtorCode.applyMinor, CtorCode.forgetIhs_argMap _ vps _ hpack,
    SemTele.applyFields_prependOrdinary, SemTele.applyIhs_prependOrdinary, SemTele.tail_argMap,
    hvalues, tele.tail_pack]
  simp only [Fin.append_right]
  rw [CtorCode.applyFields_packRecursive fields index _ (Fin.append vps vfds) vrecFds hrecFields]
  exact CtorCode.applyIhs_argMap_packRecursive fields index _ graph (Fin.append vps vfds) vrecFds _

end StrongInductiveModel

end Metalean
