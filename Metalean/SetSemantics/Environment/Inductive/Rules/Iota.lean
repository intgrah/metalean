/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
public import Metalean.SetSemantics.Environment.Inductive.Recursor.Model
public import Metalean.SetSemantics.Environment.Inductive.Rules.Constructor
import Metalean.Grind
import Metalean.SetSemantics.ConstructorValue
import Metalean.SetSemantics.Environment.Inductive.Recursor.Telescope
import Metalean.SetSemantics.InductiveComputation
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

private theorem StrongRecursiveFieldSource.iotaIH_denotes_of_leaf
    {nfields arity n : Nat}
    {Γ : Ctx ζ₁ 0 0 (ι.nparams + nfields)}
    {base : StrongTeleModel E₁ ε₁ ![] Γ}
    {bound : Nat} {s : Fin ι.nsorts}
    (recFd : RecField ζ₁ ι nfields arity s)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    {l : Level 0}
    {σ : Subst ζ₂ 0 (ι.nparams + nfields) n}
    {ps : Fin ι.nparams → Expr ζ₂ 0 n}
    {ms : Fin ι.nsorts → Expr ζ₂ 0 n}
    {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ 0 n}
    {r : Expr ζ₂ 0 n} {graph block : ZFSet} {level : Nat}
    (γ : Slots n) (δ : Slots (ι.nparams + nfields))
    (hδ : δ ∈ Reachable Set.univ base.sem)
    (hσ : (ε₂[γ]⟦σ ·⟧) = δ)
    (hatom : ∀ final ∈ Reachable {δ} (code recFd source).tele,
      ε₂ (.recr η s ls l (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦ms ·⟧)
        (ε₂[γ]⟦mins · ·⟧)
        (ε₁[final]⟦recFd.indices{ls} ·⟧)
        [zf|$(ε₂[γ]⟦r⟧) $(fun argument => final (Fin.natAdd (ι.nparams + nfields) argument))...]) =
        app graph (pair
            ((code recFd source).index final)
            [zf|$(recoverRecField
                (code recFd source).tele (code recFd source).index block level
                δ ε₂[γ]⟦r⟧)
              $(fun argument => final (Fin.natAdd (ι.nparams + nfields) argument))...])) :
    ε₂[γ]⟦(recFd.map pre.sigs).iotaIH
        η ls l ps ms mins σ r⟧ = recMap (code recFd source).tele
        (code recFd source).index graph δ
        (recoverRecField (code recFd source).tele (code recFd source).index block level
          δ ε₂[γ]⟦r⟧) := by
  let recovered := recoverRecField (code recFd source).tele (code recFd source).index block level
    δ ε₂[γ]⟦r⟧
  have hden := (Realizes.mapInst source.extension.realizes pre hatoms).denotes_fold_subst
    Expr.lam Aczel.lam (fun _ _ _ => rfl) (fun _ _ _ h => Aczel.lam_congr h)
    σ γ δ hδ hσ
    (e := .recr η s ls l (fun p => (ps p).wkN arity)
      (fun s => (ms s).wkN arity) (fun s c => (mins s c).wkN arity)
      ((recFd.map pre.sigs).instantiatedIndices ls σ) (r.applyBound arity))
    (leaf := fun final => app graph (pair ((code recFd source).index final)
      [zf|recovered $(fun f => final (Fin.natAdd (ι.nparams + nfields) f))...]))
    (fun values hvalues => by
      have his (index : Fin (ι.nindices s)) :
          ε₂[Fin.append γ values]⟦(recFd.map pre.sigs).instantiatedIndices ls σ index⟧ =
            ε₁[Fin.append δ values]⟦(recFd.indices index){ls}⟧ := by
        rw [RecField.instantiatedIndices, Expr.denote_substLiftN_append, hσ]
        simp only [RecField.map]
        rw [← Expr.map_instL]
        exact Expr.denote_map pre.sigs hatoms _ _
      simpa [Expr.denote, his, recovered, -Expr.denote_instL] using hatom (Fin.append δ values) hvalues)
  have hfold := SemTele.fold_applyAt source.extension.sem Aczel.lam
    (fun final value => app graph (pair ((code recFd source).index final) value)) δ recovered
  simp only [SemTele.app_eq_apps] at hfold
  exact hden.trans hfold

namespace StrongInductiveModel

theorem recursiveIotaLeaf
    {l : Level 0} (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields) (outer : RecSlots ι s)
    (houter : outer.valuation ∈ Reachable Set.univ (model.recrTeleSem s l))
    (fieldSlots : Slots (ι.nparams + (ι.ctors s c).nfields))
    (hfields : fieldSlots ∈ Reachable {outer.params} (model.ctors s c).source.ordinary.sem)
    (value : ZFSet)
    (hvalue : value ∈ typedRecFieldSet (model.recCode s c f).tele
      (model.recCode s c f).index (model.toModel.block outer.params)
      model.toModel.level fieldSlots)
    (final : Slots (ι.nparams + (ι.ctors s c).nfields + (ι.ctors s c).recursiveArity f))
    (hfinal : final ∈ Reachable {fieldSlots} (model.recCode s c f).tele) :
    let code := model.recCode s c f
    let arguments := fun argument => final (Fin.natAdd (ι.nparams + (ι.ctors s c).nfields) argument)
    model.recLeaf ((ι.ctors s c).recursiveTarget f) l
      (RecSlots.mk outer.params outer.motives outer.cases
        (ε₁[final]⟦((I.ctors s c).recursive f).indices{ls} ·⟧) (Aczel.apps value arguments)) =
      app (model.recrGraph s outer)
        (pair (code.index final)
          (Aczel.apps (recoverRecField code.tele code.index (model.toModel.block outer.params)
            model.toModel.level fieldSlots value) arguments)) := by
  dsimp only
  let recFd := (I.ctors s c).recursive f
  let source := (model.ctors s c).source.recursive f
  let code := model.recCode s c f
  let indices := (ε₁[final]⟦recFd.indices{ls} ·⟧)
  let arguments := fun argument => final (Fin.natAdd (ι.nparams + (ι.ctors s c).nfields) argument)
  have hparams : (fun param : Fin ι.nparams => final (param.castLE (by omega))) = outer.params := by
    funext param
    exact (congrFun (Set.eq_of_mem_singleton (Reachable.base hfinal))
      (param.castLE (Nat.le_add_right _ _))).trans
      (congrFun (Set.eq_of_mem_singleton (Reachable.base hfields)) param)
  have hps := model.recrParamsReachable s l outer houter
  have his := StrongRecursiveFieldSource.valuesReachable recFd source model.paramsSem
    (model.indicesSem ((ι.ctors s c).recursiveTarget f))
    (model.tele.indices ((ι.ctors s c).recursiveTarget f)).realizes
    (Set.singleton_subset_iff.mpr
      (Reachable.append (Reachable.mono hfields (Set.singleton_subset_iff.mpr hps))))
    (Set.mapsTo_singleton.mpr ((Set.eq_of_mem_singleton (Reachable.base hfields)) ▸ hps))
    final hfinal
  rw [hparams] at his
  have hmajor := Reachable.apps_mem_of_base hfinal
    (congrFun (Set.eq_of_mem_singleton (Reachable.base hfinal))) hvalue
  have hraw := Reachable.apps_mem_of_base hfinal
    (congrFun (Set.eq_of_mem_singleton (Reachable.base hfinal)))
    (recoverRecField_mem code.tele code.index hvalue)
  have hchild := model.recrChildReachable s l outer houter indices his
    (Aczel.apps value arguments) hmajor
  apply model.recLeaf_eq_recGraph_app outer houter indices (Aczel.apps value arguments)
    hchild _ (mem_fibre.mp hraw)
  change pair (code.index final)
    (propGet model.toModel.level (fibreOp (model.toModel.block outer.params) (code.index final))
      (Aczel.apps value arguments)) = _
  exact congrArg (pair (code.index final)) (recoverRecField_apps hfinal).symm

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
          (RecSlots.args vps vms vmins vis vmaj))
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
  have hparamReach := model.paramsReachable pre hatoms hsorts hps
  let vfds : Fin (ι.ctors s c).nfields → ZFSet := (ε₂[γ]⟦fds ·⟧)
  let vrecFds := (ε₂[γ]⟦recFds ·⟧)
  have hfieldsReach := model.fieldSlotsReachable pre hatoms hparamReach hfields
  let outer := RecSlots.args (ε₂[γ]⟦ps ·⟧) (ε₂[γ]⟦ms ·⟧) (ε₂[γ]⟦mins · ·⟧)
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
  have hvps : (ε₂[γ]⟦ps ·⟧) = RecSlots.params outer := rfl
  rw [hvps] at hfieldsReach hrecFieldsMem hargs htarget hmajEntry
  have hleaf := model.recLeaf_iota hdecl hsourceRule hE hB s l
    ((I.recAllowed_map pre.sigs ls l).mp hallowed) outer houter c hargs htarget hmajEntry
  have hlhsDen : ε₂[γ]⟦(I.map pre.sigs).iotaLhs η ls l ps ms mins s c fds recFds⟧ = _ :=
    (show ε₂[γ]⟦(I.map pre.sigs).iotaLhs η ls l ps ms mins s c fds recFds⟧ =
      model.recLeaf s l outer by rw [Inductive.iotaLhs, Expr.denote, hrecr]).trans hleaf
  have hps' (param) : ε₂[γ]⟦ps param⟧ = RecSlots.params outer param := by simp [outer, RecSlots.args]
  have hms' (s) : ε₂[γ]⟦ms s⟧ = RecSlots.motives outer s := by simp [outer, RecSlots.args]
  have hmins' (s) (c) :
      ε₂[γ]⟦mins s c⟧ = RecSlots.cases outer (Fin.encodeSigma ι.nctors ⟨s, c⟩) := by
    change ε₂[γ]⟦mins s c⟧ =
      (let ⟨s₁, c₁⟩ := Fin.decodeSigma ι.nctors (Fin.encodeSigma ι.nctors ⟨s, c⟩)
       ε₂[γ]⟦mins s₁ c₁⟧)
    rw [Fin.decodeSigma_encodeSigma]
  have hrhsDen : ε₂[γ]⟦(I.map pre.sigs).iotaRhs η ls l ps ms mins s c fds recFds⟧ =
      (model.codeOf s c).applyMinor model.toModel.level (model.recrGraph s outer) (RecSlots.params outer)
        (RecSlots.cases outer (Fin.encodeSigma ι.nctors ⟨s, c⟩))
        (model.ctorArgs s c (RecSlots.params outer) vfds vrecFds) := by
    let fieldSlots := Fin.append (RecSlots.params outer) vfds
    have hparamReach' : RecSlots.params outer ∈ Reachable Set.univ model.paramsSem := by
      grind only [reachability]
    have hih (f) : ε₂[γ]⟦(I.map pre.sigs).iotaIHs η ls l ps ms mins
          s c fds recFds f⟧ =
        recMap (model.recCode s c f).tele (model.recCode s c f).index
          (model.recrGraph s outer) fieldSlots
          (recoverRecField (model.recCode s c f).tele (model.recCode s c f).index
            (model.toModel.block (RecSlots.params outer)) model.toModel.level
            fieldSlots (vrecFds f)) := by
      refine StrongRecursiveFieldSource.iotaIH_denotes_of_leaf
        ((I.ctors s c).recursive f) ((model.ctors s c).source.recursive f)
        pre hatoms (σ := Fin.append ps fds) γ fieldSlots
        (Reachable.append
          (Reachable.mono hfieldsReach (Set.singleton_subset_iff.mpr hparamReach')))
        ((Fin.append_comp ps fds fun e => ε₂[γ]⟦e⟧).trans
          (congrArg (Fin.append · _) (funext hps')))
        fun final hfinal => ?_
      have hcases : (fun tag =>
          let ⟨target, c₁⟩ := Fin.decodeSigma ι.nctors tag
          outer.cases (Fin.encodeSigma ι.nctors ⟨target, c₁⟩)) = outer.cases := by
        funext tag
        change outer.cases (Fin.encodeSigma ι.nctors (Fin.decodeSigma ι.nctors tag)) = _
        rw [Fin.encodeSigma_decodeSigma]
      simp only [hps', hms', hmins', hrecr]
      change model.recLeaf _ l (RecSlots.mk _ _ _ _ _) = _
      rw [hcases]
      exact model.recursiveIotaLeaf s c f outer houter fieldSlots
        hfieldsReach (vrecFds f) (hrecFieldsMem f) final hfinal
    rw [model.applyMinor_ctorApplication s c
      (RecSlots.params outer) vfds vrecFds
      hrecFieldsMem (model.recrGraph s outer)
      (RecSlots.cases outer (Fin.encodeSigma ι.nctors ⟨s, c⟩))]
    simp [Inductive.iotaRhs, hmins', hih]
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
