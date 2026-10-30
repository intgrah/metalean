/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
public import Metalean.SetSemantics.Environment.Inductive.Recursor.Evaluation
public import Metalean.SetSemantics.Environment.Inductive.Rules.Constructor
import Metalean.Grind
import Metalean.SetSemantics.Inductive.Constructor
import Metalean.SetSemantics.Environment.Inductive.Recursor.Telescope
import Metalean.SetSemantics.Inductive.Recursion
import Metalean.Syntax.Substitution

public section

universe u

namespace Metalean

open ZFSet

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  (model : StrongInductiveModel E₁ ε₁ I ls)

namespace StrongInductiveModel

theorem iotaRuleSound
    (hdecl : SemDecls E₁ ε₁ ![]) (hsourceRule : SemDeclRules E₁ ε₁ ![])
    (hB : InductiveWF E₁ I)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hsorts : ∀ s vps vis,
      ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
    (hctors : ∀ s c vps vfds vrecFds,
      ε₂ (.ctor η s c ls vps vfds vrecFds) = model.ctorResult s c vps vfds vrecFds)
    (hrecr : ∀ s l vps vms vmins vis vmaj,
      ε₂ (.recr η s ls l vps vms vmins vis vmaj) = model.recLeaf s l
          (RecSlots.mk vps vms vmins vis vmaj))
    {n : Nat} {γ : Slots n}
    {l : Level 0}
    {ps : Fin ι.nparams → Expr ζ₂ 0 n}
    {ms : Fin ι.nsorts → Expr ζ₂ 0 n}
    {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ 0 n}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ 0 n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₂ 0 n}
    (hallowed : (E₂.get η).block.RecAllowed ls l) :
    EnvWF E₁ →
    (∀ param, ε₂[γ] ⊨ ps param ≡ ps param :
      (E₂.get η).block.paramType ls ps param) →
    (∀ s, ε₂[γ] ⊨ ms s ≡ ms s :
      (E₂.get η).block.motiveType η ls ps l s) →
    (∀ s c, ε₂[γ] ⊨ mins s c ≡ mins s c :
      (E₂.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, ε₂[γ] ⊨ fds f ≡ fds f :
      ((((E₂.get η).block.ctors s c).ordinary f).type{ls}).subst
        (Fin.append ps fun previous : Fin f.val =>
          fds (previous.castLE f.isLt.le))) →
    (∀ f, ε₂[γ] ⊨ recFds f ≡ recFds f :
      (((E₂.get η).block.ctors s c).recursive f).instantiatedType
        η ls ps (Fin.append ps fds)) →
    ε₂[γ] ⊨ (E₂.get η).block.iotaLhs η ls l ps ms mins s c fds recFds ≡
      (E₂.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
      (E₂.get η).block.iotaType η ls ps ms s c fds recFds := by
  intro hE hps hms hmins hfields hrecFields
  have hmajInterp := model.ctorRuleSound pre hatoms hblock hsorts hctors hps hfields hrecFields
  rw [hblock] at hallowed hps hms hmins hfields hrecFields hmajInterp ⊢
  have hparamReach := model.paramsReachable pre hatoms hps
  let vfds : Fin (ι.ctors s c).nfields → ZFSet := (ε₂[γ]⟦fds ·⟧)
  let vrecFds := (ε₂[γ]⟦recFds ·⟧)
  have hfieldsReach := model.fieldSlotsReachable pre hatoms hparamReach hfields
  let outer := RecSlots.mk (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦ms ·⟧) (ε₂[γ]⟦mins · ·⟧)
    (ε₂[γ]⟦((I.map pre.sigs).ctors s c).targetIndex ls ps fds ·⟧)
    ε₂[γ]⟦.ctor η s c ls ps fds recFds⟧
  have houter : outer.valuation ∈ Reachable Set.univ (model.recrTeleSem s l) :=
    model.recrArgs_reachable pre hatoms hsorts hctors l
      (fun p => (hps p).mem) (fun s => (hms s).mem) (fun s c => (hmins s c).mem)
      (fun i => (model.targetIndexInterp pre hatoms
        hparamReach hfieldsReach i).mem) hmajInterp.mem
  have hrecFieldsMem := model.recFieldsMem pre hatoms hsorts
    hparamReach hfieldsReach hrecFields
  have ⟨hargs, hordinary⟩ := model.ctorArgs_mem s c _ vfds hfieldsReach vrecFds hrecFieldsMem
  have htarget : (model.codeOf s c).targetIndex (ε₂[γ]⟦ps ·⟧)
      (model.ctorArgs s c (ε₂[γ]⟦ps ·⟧) vfds vrecFds) =
      sortKey s.val (encode (RecSlots.indices outer)) := by
    rw [model.codeOf_targetIndex, hordinary]
    congr 2
    funext index
    exact model.targetIndexDenotes pre hatoms hparamReach hfieldsReach index |>.symm
  have hmajEntry : RecSlots.major outer =
      propVal model.toModel.level (entryValue (tagOf s c)
        (model.ctorArgs s c (ε₂[γ]⟦ps ·⟧) vfds vrecFds)) :=
    hctors s c _ vfds vrecFds
  have hleaf := model.recLeaf_iota hdecl hsourceRule hE hB s l
    ((I.recAllowed_map pre.sigs ls l).mp hallowed) outer houter c hargs htarget hmajEntry
  have hlhsDen : ε₂[γ]⟦(I.map pre.sigs).iotaLhs η ls l ps ms mins s c fds recFds⟧ = _ :=
    (show ε₂[γ]⟦(I.map pre.sigs).iotaLhs η ls l ps ms mins s c fds recFds⟧ =
      model.recLeaf s l outer by rw [Inductive.iotaLhs, Expr.denote, hrecr]).trans hleaf
  have hrhsDen : ε₂[γ]⟦(I.map pre.sigs).iotaRhs η ls l ps ms mins s c fds recFds⟧ =
      (model.codeOf s c).applyMinor model.toModel.level (model.recrGraph s outer) (RecSlots.params outer)
        (RecSlots.cases outer s c)
        (model.ctorArgs s c (RecSlots.params outer) vfds vrecFds) := by
    let fieldSlots := Fin.append (RecSlots.params outer) vfds
    have hih (f) : ε₂[γ]⟦(I.map pre.sigs).iotaIHs η ls l ps ms mins
          s c fds recFds f⟧ =
        recMap ((model.codeOf s c).recursive f).tele ((model.codeOf s c).recursive f).index
          (model.recrGraph s outer) fieldSlots
          (recoverRecField ((model.codeOf s c).recursive f).tele ((model.codeOf s c).recursive f).index
            (model.toModel.block (RecSlots.params outer)) model.toModel.level
            fieldSlots (vrecFds f)) := by
      let recFd := (I.ctors s c).recursive f
      let source := (model.ctors s c).source.recursive f
      let code := (model.codeOf s c).recursive f
      let recovered := recoverRecField code.tele code.index (model.toModel.block outer.params)
        model.toModel.level fieldSlots (vrecFds f)
      have hfields : fieldSlots ∈ Reachable Set.univ
          (model.params.append (model.ctors s c).source.ordinary).sem :=
        Reachable.append (Reachable.mono hfieldsReach (Set.singleton_subset_iff.mpr hparamReach))
      have hσ : (ε₂[γ]⟦Fin.append ps fds ·⟧) = fieldSlots :=
        Fin.append_comp ps fds fun e => ε₂[γ]⟦e⟧
      have hden := (source.extension.realizes.mapInst pre hatoms).denotes_fold_subst
        Expr.lam Aczel.lam (fun _ _ _ => rfl) (fun _ _ _ h => Aczel.lam_congr h)
        (Fin.append ps fds) γ fieldSlots hfields hσ
        (e := .recr η ((ι.ctors s c).recursiveTarget f) ls l
          (fun p => (ps p).wkN code.arity) (fun s => (ms s).wkN code.arity)
          (fun s c => (mins s c).wkN code.arity)
          ((recFd.map pre.sigs).instantiatedIndices ls (Fin.append ps fds))
          ((recFds f).applyBound code.arity))
        (leaf := fun final => app (model.recrGraph s outer) (pair (code.index final)
          [zf|recovered $(fun i => final (Fin.natAdd (ι.nparams + (ι.ctors s c).nfields) i))...]))
        (fun values hvalues => by
          let final := Fin.append fieldSlots values
          let indices := (ε₁[final]⟦recFd.indices{ls} ·⟧)
          have hparams : (fun p : Fin ι.nparams => final (p.castLE (by omega))) = outer.params := by
            funext param
            exact (congrFun (Set.eq_of_mem_singleton (Reachable.base hvalues))
              (param.castAdd (ι.ctors s c).nfields)).trans
              (congrFun (Set.eq_of_mem_singleton (Reachable.base hfieldsReach)) param)
          have his := Inductive.indexValuesReachable (by omega)
            (model.indices ((ι.ctors s c).recursiveTarget f)).realizes recFd.indices{ls} final
            (by rw [hparams]; exact hparamReach)
            (fun i => ⟨rfl, source.mem final
              (Reachable.mono hvalues (Set.singleton_subset_iff.mpr hfields)) i⟩)
          rw [hparams] at his
          have hmajor := Reachable.apps_mem_of_base hvalues
            (congrFun (Set.eq_of_mem_singleton (Reachable.base hvalues))) (hrecFieldsMem f)
          simp only [Fin.append_right] at hmajor
          have hchild := model.recrChildReachable s l outer houter indices his
            (Aczel.apps (vrecFds f) values) hmajor
          have heq : model.recLeaf _ l (RecSlots.mk outer.params outer.motives outer.cases
              indices (Aczel.apps (vrecFds f) values)) =
              app (model.recrGraph s outer) (pair (code.index final) (Aczel.apps recovered values)) := by
            rw [model.recLeaf_eq_recGraph_app _ _ _ hchild]
            apply congrArg (app (model.recrGraph s outer))
            change pair (code.index final)
              (propGet model.toModel.level (fibreOp (model.toModel.block outer.params) (code.index final))
                (Aczel.apps (vrecFds f) values)) = _
            simpa only [Fin.append_right] using congrArg (pair (code.index final))
              (recoverRecField_apps (index := code.index) (block := model.toModel.block outer.params)
                (level := model.toModel.level) (value := vrecFds f) hvalues).symm
          have hindices (i) : ε₂[Fin.append γ values]⟦(recFd.map pre.sigs).instantiatedIndices
              ls (Fin.append ps fds) i⟧ = ε₁[final]⟦(recFd.indices i){ls}⟧ := by
            rw [RecField.instantiatedIndices, Expr.denote_substLiftN_append, hσ]
            simp only [RecField.map]
            rw [← Expr.map_instL]
            exact Expr.denote_map pre.sigs hatoms _ _
          simp only [Expr.denote, hindices, hrecr, code, Expr.denote_wkN,
            Expr.denote_applyBound, Fin.append_left, Fin.append_right]
          exact heq)
      simp only [recMap, SemTele.lamAt, SemTele.foldAt, SemTele.app_eq_apps]
      exact hden
    simp only [ctorArgs]
    rw [(model.codeOf s c).applyMinor_pack (model.toModel.block outer.params)
      (model.recrGraph s outer) model.toModel.level outer.params vfds vrecFds
      hrecFieldsMem (outer.cases s c)]
    simp [Inductive.iotaRhs, hih]
    rfl
  refine ⟨hlhsDen.trans hrhsDen.symm, ?_⟩
  have htype := Expr.denote_subst (ε := ε₂) (ν := ![]) γ (Inductive.recrSubst ps ms mins
    (fun i => ((I.map pre.sigs).ctors s c).targetIndex ls ps fds i) (.ctor
      η s c ls ps fds recFds)) (ι.recrBody s)
  rw [RecSlots.denote_recrSubst] at htype
  change _ ∈ ε₂[γ]⟦Inductive.motiveResult (ms s)
    (fun i => ((I.map pre.sigs).ctors s c).targetIndex ls ps fds i)
    (.ctor η s c ls ps fds recFds)⟧
  rw [← IndSig.recrBody_subst, htype, hlhsDen, ← hleaf]
  exact model.recLeaf_mem s l outer houter

end StrongInductiveModel

end Metalean
