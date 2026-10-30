/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
import Metalean.SetSemantics.Inductive.Recursion
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

noncomputable def recFieldSet
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields) (vps : Slots ι.nparams)
    (fieldSlots : Slots (ι.nparams + (ι.ctors s c).nfields)) :=
  typedRecFieldSet ((model.codeOf s c).recursive f).tele ((model.codeOf s c).recursive f).index
    (model.toModel.block vps) model.toModel.level fieldSlots

section

variable (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
  (hparamReach : (ε₂[γ]⟦ps ·⟧) ∈ Reachable Set.univ model.paramsSem)
  (hfieldsReach : Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧) ∈
    Reachable {(ε₂[γ]⟦ps ·⟧)} (model.ctors s c).source.ordinary.sem)

include hatoms in
theorem paramsReachable {ps₂ : Fin ι.nparams → Expr ζ₂ 0 n}
    (hps : ∀ param, ε₂[γ] ⊨ ps param ≡ ps₂ param :
      (I.map pre.sigs).paramType ls ps param) :
    (ε₂[γ]⟦ps ·⟧) ∈ Reachable Set.univ model.paramsSem :=
  SemDefeq.reachable (model.realizes pre hatoms).params fun param => by
    rw [Ctx.get_subst _ _ param param.val param.isLt rfl]
    simpa [Inductive.paramType] using hps param

include hatoms hparamReach in
theorem fieldSlotsReachable
    {fds₁ : Fin (ι.ctors s c).nfields → Expr ζ₂ 0 n}
    (hfields : ∀ f, ε₂[γ] ⊨ fds f ≡ fds₁ f :
      ((((I.map pre.sigs).ctors s c).ordinary f).type{ls}).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) :
    Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧) ∈
      Reachable {(ε₂[γ]⟦ps ·⟧)} (model.ctors s c).source.ordinary.sem := by
  have hsourceMap : Realizes ε₂ ![]
      {(ε₂[γ]⟦ps ·⟧)}
      ((I.ctors s c).map pre.sigs).ordinaryTele{ls}
      (model.ctors s c).source.ordinary.sem :=
    (congrArg (fun Δ => Realizes ε₂ ![] _ Δ _)
      ((Ctx.map_instL pre.sigs ls (I.ctors s c).ordinaryTele).trans
        (congrArg (·{ls}) (Ctor.ordinaryTeleAux_map pre.sigs (I.ctors s c) _ _)))).mp
          (((model.ctors s c).source.ordinary.realizes.monoReach
            (reach₂ := {(ε₂[γ]⟦ps ·⟧)})
            (Set.singleton_subset_iff.mpr hparamReach)).map pre hatoms)
  apply hsourceMap.reachable_subst (γ := γ) (Γ := (I.map pre.sigs).params{ls})
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
          (I.map pre.sigs).params{ls}
          ((I.ctors s c).map pre.sigs).ordinaryTele{ls}
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
  have hdomain := StrongRecursiveFieldSource.type_denotes ((I.ctors s c).recursive f)
    ((model.ctors s c).source.recursive f) pre hatoms
    (block := fun _ => model.toModel.block (ε₂[γ]⟦ps ·⟧)) (level := model.toModel.level)
    (σ := Fin.append ps fds) γ (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧))
    (Reachable.append (Reachable.mono hfieldsReach (Set.singleton_subset_iff.mpr hparamReach)))
    (Fin.append_comp ps fds fun e => ε₂[γ]⟦e⟧) (hsorts _)
    (fun δ hδ => by
      have hpsEq : (fun param : Fin ι.nparams => δ (param.castLE (by omega))) =
          (ε₂[γ]⟦ps ·⟧) := by
        funext param
        have h := congrFun (Set.eq_of_mem_singleton (Reachable.base hδ))
          (param.castAdd (ι.ctors s c).nfields)
        rw [Fin.append_left] at h
        exact h
      rw [← hpsEq]
      exact model.recursiveField_apply s c f δ)
  simp only [Fin.append_left] at hdomain
  have hmem := (hrecFields f).mem
  simp only [Inductive.map, Ctor.map] at hmem
  rw [hdomain] at hmem
  exact hmem

include hatoms hparamReach hfieldsReach in
theorem targetIndexDenotes (index : Fin (ι.nindices s)) :
    ε₂[γ]⟦((I.map pre.sigs).ctors s c).targetIndex ls ps fds index⟧ =
      model.targetValues s c (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧)) index := by
  simpa [Inductive.map, Ctor.map, Ctor.targetIndex, StrongInductiveModel.targetValues] using
    (Expr.denote_subst γ (Fin.append ps fds) _).trans
      ((congrArg (fun δ => ε₂[δ]⟦_⟧) (Fin.append_comp ps fds fun e => ε₂[γ]⟦e⟧)).trans
        ((Expr.denote_map pre.sigs hatoms _ _).trans ((model.ctors s c).source.targetValues_denotes
          (Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧))
          (Reachable.append
            (Reachable.mono hfieldsReach (Set.singleton_subset_iff.mpr hparamReach))) index)))

include hatoms hparamReach hfieldsReach in
theorem targetIndexInterp (index : Fin (ι.nindices s)) :
    ε₂[γ] ⊨ ((I.map pre.sigs).ctors s c).targetIndex ls ps fds index ≡
      ((I.map pre.sigs).ctors s c).targetIndex ls ps fds index :
      (I.map pre.sigs).indexType ls s ps
        (fun i => ((I.map pre.sigs).ctors s c).targetIndex ls ps fds i) index := by
  let fields := Fin.append (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦fds ·⟧)
  have hmem := ((model.ctors s c).targetInterp fields
    (Reachable.append (Reachable.mono hfieldsReach
      (Set.singleton_subset_iff.mpr hparamReach))) index).mem
  rw [← Expr.denote_map pre.sigs hatoms] at hmem
  refine ⟨rfl, ?_⟩
  have hsubst := Expr.denote_subst (ε := ε₂) (ν := ![]) γ (Fin.append ps fds)
    ((I.indexType ls s (fun param => .var (param.castAdd (ι.ctors s c).nfields))
      (I.ctors s c).targetIndices{ls} index).map pre.sigs)
  simp [Expr.map_instL, Fin.append_comp] at hsubst
  have hvalue := (model.targetIndexDenotes pre hatoms hparamReach hfieldsReach index).trans
    ((model.ctors s c).source.targetValues_denotes fields
      (Reachable.append (Reachable.mono hfieldsReach
        (Set.singleton_subset_iff.mpr hparamReach))) index).symm
  rw [← hvalue] at hmem
  simp only [Inductive.indexType_map, InstLevel.inst_apply, Expr.map_instL, Expr.map] at hmem
  dsimp only [fields] at hmem
  simp only [Fin.castAdd, Fin.castLE] at hsubst
  rw [← hsubst] at hmem
  simpa [Ctor.targetIndex, Inductive.map, Ctor.map] using hmem

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
      .sort (E₂.get η).block.level{ls} := by
  intro hps his
  refine ⟨?_, ?_⟩
  · simp only [Expr.denote]
    rw [funext fun p => (hps p).eq, funext fun i => (his i).eq]
  · change ε₂ (.ind η s ls _ _) ∈ S_ ((E₂.get η).block.level{ls}.eval ![])
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
      ((((E₂.get η).block.ctors s c).ordinary f).type{ls}).subst
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
  have hparamReach := model.paramsReachable pre hatoms hps
  have hfieldsReach := model.fieldSlotsReachable pre hatoms hparamReach hfields
  refine ⟨?_, ?_⟩
  · simp only [Expr.denote]
    rw [funext fun p => (hps p).eq, funext fun f => (hfields f).eq,
      funext fun f => (hrecFields f).eq]
  · rw [hblock]
    change ε₂ (.ctor η s c ls vps vfds vrecFds) ∈ ε₂ (.ind η s ls vps _)
    rw [hctors, funext fun index =>
      model.targetIndexDenotes pre hatoms hparamReach hfieldsReach index, hsorts]
    exact model.ctorResult_mem_sortValue s c vps vfds hfieldsReach vrecFds
      (model.recFieldsMem pre hatoms hsorts hparamReach hfieldsReach hrecFields)

end StrongInductiveModel

end Metalean
