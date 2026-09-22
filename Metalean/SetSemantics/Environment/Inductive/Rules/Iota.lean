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
import Metalean.SetSemantics.ConstructorPredecessors
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
    {base : StrongTeleModel E₁ ε₁ zeroNs Γ}
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
        (ε₁[final]⟦recFd.indices · |>.instL ls⟧)
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
  let project : Slots n → Slots (ι.nparams + nfields) := fun _ => δ
  have hrealizes := ((congrArg (fun Δ => Realizes ε₂ zeroNs _ Δ _)
    (Ctx.map_instL pre.sigs ls recFd.tele)).mp
      (source.extension.realizes.map pre hatoms)).pull σ project (reach₁ := {γ})
    (fun _ _ => hδ) fun current hcurrent v => by subst current; exact congrFun hσ v
  have hbase (final : Slots (n + arity))
      (hfinal : final ∈ Reachable {γ} (source.extension.sem.pull project arity)) :
      (fun v => final (v.castAdd arity)) = γ := Set.eq_of_mem_singleton (Reachable.base hfinal)
  let recovered := recoverRecField (code recFd source).tele (code recFd source).index block level
    δ ε₂[γ]⟦r⟧
  let leaf : DomAt (ι.nparams + nfields + arity) :=
    fun final value => app graph (pair ((code recFd source).index final) value)
  have hden := hrealizes.denotes_lam
    (leaf := fun final => leaf (Slots.pull project final)
      (Aczel.apps recovered fun v => final (Fin.natAdd n v)))
    (e := .recr η s ls l (fun p => (ps p).wkN arity)
      (fun s => (ms s).wkN arity) (fun s c => (mins s c).wkN arity)
      (fun i => (((recFd.indices i).map pre.sigs).instL ls).subst (σ.liftN arity))
      (r.applyBound arity))
    (Set.mem_singleton γ) fun final hfinal => by
      simp only [Expr.denote, Expr.denote_wkN, Expr.denote_applyBound]
      rw [hbase final hfinal, funext fun index => show
          ε₂[final]⟦(((recFd.indices index).map pre.sigs).instL ls).subst
            (σ.liftN arity)⟧ = ε₁[Slots.pull project final]⟦(recFd.indices index).instL ls⟧ by
        rw [Expr.denote_subst, Expr.denote_substLiftN, hbase final hfinal, hσ, ← Expr.map_instL]
        exact Expr.denote_map pre.sigs hatoms _ _]
      have h := hatom (Slots.pull project final) (Reachable.pull hfinal fun _ _ => rfl)
      simpa only [Slots.pull, Fin.addCases_right] using h
  rwa [SemTele.lam_applyAt (source.extension.sem.pull project arity)
    (fun final value => leaf (Slots.pull project final) value) γ recovered,
    SemTele.lamAt_pull] at hden

namespace StrongInductiveModel

theorem recursiveIotaLeaf
    {l : Level 0}
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields)
    (outer : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors +
      ι.nindices s + 1))
    (houter : outer ∈ Reachable Set.univ (model.recrTeleSem s l))
    (fieldSlots : Slots
      (ι.nparams + (ι.ctors s c).nfields))
    (hfields : fieldSlots ∈ Reachable {RecSlots.paramsOf outer}
      (model.ctors s c).source.ordinary.sem)
    (vrecFds : Fin (ι.ctors s c).nrecFields → ZFSet)
    (hrecFields : ∀ current, vrecFds current ∈ typedRecFieldSet
      (StrongRecursiveFieldSource.code
        ((I.ctors s c).recursive current)
        ((model.ctors s c).source.recursive current)).tele
      (StrongRecursiveFieldSource.code
        ((I.ctors s c).recursive current)
        ((model.ctors s c).source.recursive current)).index
      (model.toModel.block (RecSlots.paramsOf outer)) model.toModel.level fieldSlots)
    (final : Slots (ι.nparams + (ι.ctors s c).nfields +
      (ι.ctors s c).recursiveArity f))
    (hfinal : final ∈ Reachable {fieldSlots}
      (StrongRecursiveFieldSource.code
        ((I.ctors s c).recursive f)
        ((model.ctors s c).source.recursive f)).tele) :
    let recFd := (I.ctors s c).recursive f
    let code := StrongRecursiveFieldSource.code recFd ((model.ctors s c).source.recursive f)
    let vmaj := [zf|$(vrecFds f) $(fun argument => final (Fin.natAdd
      (ι.nparams + (ι.ctors s c).nfields) argument))...]
    let raw := [zf|$(recoverRecField code.tele code.index
        (model.toModel.block (RecSlots.paramsOf outer)) model.toModel.level fieldSlots
        (vrecFds f)) $(fun argument => final (Fin.natAdd
        (ι.nparams + (ι.ctors s c).nfields) argument))...]
    model.recLeaf ((ι.ctors s c).recursiveTarget f) l
      (RecSlots.args (RecSlots.paramsOf outer)
        (RecSlots.motivesOf outer)
        (fun target c => RecSlots.casesOf outer
          (Fin.encodeSigma ι.nctors ⟨target, c⟩))
        (ε₁[final]⟦recFd.indices · |>.instL ls⟧) vmaj) =
      app (model.recrGraph s outer) (pair (code.index final) raw) := by
  dsimp only
  let source := (model.ctors s c).source
  let recFd := (I.ctors s c).recursive f
  let recSource := source.recursive f
  let code := StrongRecursiveFieldSource.code recFd recSource
  let vmaj := [zf|$(vrecFds f) $(fun argument => final (Fin.natAdd
    (ι.nparams + (ι.ctors s c).nfields) argument))...]
  let vis := (ε₁[final]⟦recFd.indices · |>.instL ls⟧)
  let child : Slots (ι.nparams + ι.nsorts + Fin.sum ι.nctors +
      ι.nindices ((ι.ctors s c).recursiveTarget f) + 1) :=
    RecSlots.childOf outer vis vmaj
  let raw := [zf|$(recoverRecField code.tele code.index
      (model.toModel.block (RecSlots.paramsOf outer)) model.toModel.level fieldSlots
      (vrecFds f)) $(fun argument => final (Fin.natAdd
      (ι.nparams + (ι.ctors s c).nfields) argument))...]
  have hchild : child ∈ Reachable Set.univ
      (model.recrTeleSem ((ι.ctors s c).recursiveTarget f) l) := by
    have hprefix : RecSlots.prefixOf outer ∈ Reachable Set.univ (model.recrPrefixSem l) := by
      change (fun current => Fin.init outer (current.castLE (by omega))) ∈
        Reachable Set.univ (model.recrPrefixSem l)
      simpa using Reachable.base (Reachable.of_append (Reachable.init houter))
    have hpsOuter : RecSlots.paramsOf outer ∈ Reachable Set.univ model.paramsSem :=
      model.recrParamsReachable s l outer houter
    have hvalues := StrongRecursiveFieldSource.valuesReachable
      recFd recSource model.paramsSem
      (model.indicesSem ((ι.ctors s c).recursiveTarget f))
      (model.tele.indices ((ι.ctors s c).recursiveTarget f)).realizes
      (Set.singleton_subset_iff.mpr
        (Reachable.append (Reachable.mono hfields (Set.singleton_subset_iff.mpr hpsOuter))))
      (Set.mapsTo_singleton.mpr
        ((Set.eq_of_mem_singleton (Reachable.base hfields)) ▸ hpsOuter))
      final hfinal
    rw [show (fun param : Fin ι.nparams => final (param.castLE (by omega))) =
        RecSlots.paramsOf outer by
      funext param
      rw [show param.castLE (by omega) =
          (param.castLE (Nat.le_add_right _ _)).castLE code.tele.le from rfl,
        congrFun (Set.eq_of_mem_singleton (Reachable.base hfinal))
          (param.castLE (Nat.le_add_right _ _))]
      exact congrFun (Set.eq_of_mem_singleton (Reachable.base hfields)) param] at hvalues
    have his : RecSlots.withIndices outer vis ∈ Reachable (Reachable Set.univ
        (model.recrPrefixSem l))
        (model.recrIndicesSem ((ι.ctors s c).recursiveTarget f)) := by
      apply Reachable.of_pull
      · rw [RecSlots.pull_recrParams_withIndices]
        simpa [vis] using hvalues
      · simpa using hprefix
    refine Reachable.snoc (by simpa [child] using Reachable.append his) ?_
    simp only [child, Fin.init_snoc]
    have hmaj : vmaj ∈ propSet model.toModel.level
        (fibreOp (model.toModel.block (RecSlots.paramsOf outer))
          (code.index final)) := by
      apply Reachable.apps_mem_of_base hfinal
        (congrFun (Set.eq_of_mem_singleton (Reachable.base hfinal)))
      simpa [typedRecFieldSet, code] using hrecFields f
    unfold recrMajorDomain InductiveModel.sortValue
    rw [RecSlots.withIndices_params]
    simpa [code, vis] using hmaj
  rw [show RecSlots.args (RecSlots.paramsOf outer)
      (RecSlots.motivesOf outer)
      (fun target c => RecSlots.casesOf outer
        (Fin.encodeSigma ι.nctors ⟨target, c⟩))
      (ε₁[final]⟦recFd.indices · |>.instL ls⟧) vmaj = child by
    simp [RecSlots.args, child, vis, RecSlots.append_params_motives_cases]]
  let fields := source.recursiveCodes
  let vargs := source.ordinary.sem.pack fieldSlots
    (CtorCode.packRecursive (model.toModel.block (RecSlots.paramsOf outer)) fields
      model.toModel.level fieldSlots vrecFds proof)
  have htail : CtorCode.packRecursive (model.toModel.block (RecSlots.paramsOf outer)) fields
      model.toModel.level fieldSlots vrecFds proof ∈ (model.recursiveRest s c).argSet
        (model.toModel.block (RecSlots.paramsOf outer)) fieldSlots :=
    CtorCode.packRecursive_mem hrecFields (CtorCode.proof_mem_argSet_target fieldSlots)
  have hargs := SemTele.pack_mem hfields htail
  rw [Set.eq_of_mem_singleton (Reachable.base hfields)] at hargs
  apply model.recLeaf_eq_recGraph_app outer houter child hchild
    (RecSlots.paramsOf_childOf ..) (RecSlots.motivesOf_childOf ..) (RecSlots.casesOf_childOf ..)
  · refine (model.codeOf s c).predecessors_mem_block
      (RecSlots.paramsOf outer) vargs hargs (pair (code.index final) raw) ?_
    rw [model.codeOf_eq s c, StrongInductiveModel.recursiveRest,
      ← Set.eq_of_mem_singleton (Reachable.base hfields), SemTele.predecessors_prependOrdinary,
      SemTele.tail_pack, SemTele.values_pack]
    simpa [fields, code, StrongCtorSource.recursiveCodes] using
      CtorCode.mem_predecessors_packRecursive
        (model.toModel.block (RecSlots.paramsOf outer)) fields
        (StrongCtorSource.targetIndex (model.ctors s c).target)
        fieldSlots vrecFds f final hfinal
  · let leaf : DomAt
        (ι.nparams + (ι.ctors s c).nfields +
          (ι.ctors s c).recursiveArity f) :=
      fun current value => propGet model.toModel.level
        (fibreOp (model.toModel.block (RecSlots.paramsOf outer))
          (code.index current)) value
    have happ := congrArg (fun function => [zf|function $(fun argument =>
      final (Fin.natAdd (ι.nparams + (ι.ctors s c).nfields) argument))...])
      (SemTele.lam_applyAt code.tele leaf fieldSlots (vrecFds f))
    rw [Reachable.apps_lam_of_base hfinal
      (leaf := fun current => leaf current [zf|$(vrecFds f) $(fun argument =>
        current (Fin.natAdd (ι.nparams + (ι.ctors s c).nfields) argument))...])] at happ
    unfold recrState recrMajorOf
    rw [RecSlots.paramsOf_childOf, RecSlots.indicesOfSlots_childOf, RecSlots.majorOfSlots_childOf]
    exact congrArg (pair (code.index final))
      (show leaf final vmaj = raw by simpa [recoverRecField, raw] using happ)

theorem iotaRuleSound
    (hdecl : SemDecls E₁ ε₁ zeroNs) (hsourceRule : SemDeclRules E₁ ε₁ zeroNs)
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
    (hallowed : (E₂.get η).block.RecAllowed l) :
    EnvWF E₁ →
    (∀ param, ε₂[γ] ⊨ ps param ≡ ps param :
      (E₂.get η).block.paramType ls ps param) →
    (∀ s, ε₂[γ] ⊨ ms s ≡ ms s :
      (E₂.get η).block.motiveType η ls ps l s) →
    (∀ s c, ε₂[γ] ⊨ mins s c ≡ mins s c :
      (E₂.get η).block.caseFnType η ls ps ms s c) →
    (∀ f, ε₂[γ] ⊨ fds f ≡ fds f :
      (((((E₂.get η).block.ctors s c).ordinary f).type).instL ls).subst
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
  have houter : outer ∈ Reachable Set.univ (model.recrTeleSem s l) :=
    model.recrArgs_reachable pre hatoms hsorts hctors l
      (fun p => (hps p).mem) (fun s => (hms s).mem) (fun s c => (hmins s c).mem)
      (fun i => (model.targetIndexInterp pre hatoms hsorts
        hparamReach hfieldsReach i).mem) hmajInterp.mem
  have hrecFieldsMem := model.recFieldsMem pre hatoms hsorts
    hparamReach hfieldsReach hrecFields
  have ⟨hargs, hordinary⟩ := model.ctorArgs_mem s c _ vfds hfieldsReach vrecFds hrecFieldsMem
  have htarget : (model.codeOf s c).targetIndex (ε₂[γ]⟦ps ·⟧)
      (model.ctorArgs s c (ε₂[γ]⟦ps ·⟧) vfds vrecFds) =
      sortKey s.val (RecSlots.indicesOfSlots outer) := by
    rw [model.codeOf_targetIndex, hordinary,
      RecSlots.indicesOfSlots, RecSlots.indexValuesOf_args]
    congr 2
    funext index
    exact model.targetIndexDenotes pre hatoms hparamReach hfieldsReach index |>.symm
  have hmajEntry : RecSlots.majorOfSlots outer =
      propVal model.toModel.level (entryValue (tagOf s c)
        (model.ctorArgs s c (ε₂[γ]⟦ps ·⟧) vfds vrecFds)) :=
    (RecSlots.majorOfSlots_args ..).trans (hctors s c _ vfds vrecFds)
  have hvps : (ε₂[γ]⟦ps ·⟧) = RecSlots.paramsOf outer := (RecSlots.paramsOf_args ..).symm
  rw [hvps] at hfieldsReach hrecFieldsMem hargs htarget hmajEntry
  have hleaf := model.recLeaf_iota hdecl hsourceRule hE hB s l
    ((I.recAllowed_map pre.sigs l).mp hallowed) outer houter c hargs htarget hmajEntry
  have hlhsDen : ε₂[γ]⟦(I.map pre.sigs).iotaLhs η ls l ps ms mins s c fds recFds⟧ = _ :=
    (show ε₂[γ]⟦(I.map pre.sigs).iotaLhs η ls l ps ms mins s c fds recFds⟧ =
      model.recLeaf s l outer by rw [Inductive.iotaLhs, Expr.denote, hrecr]).trans hleaf
  have hps' : ∀ param, ε₂[γ]⟦ps param⟧ = RecSlots.paramsOf outer param := by simp [outer]
  have hms' : ∀ s, ε₂[γ]⟦ms s⟧ = RecSlots.motivesOf outer s := by simp [outer]
  have hmins' : ∀ s c,
      ε₂[γ]⟦mins s c⟧ = RecSlots.casesOf outer (Fin.encodeSigma ι.nctors ⟨s, c⟩) := by
    simp [outer]
  have hrhsDen : ε₂[γ]⟦(I.map pre.sigs).iotaRhs η ls l ps ms mins s c fds recFds⟧ =
      (model.codeOf s c).applyMinor model.toModel.level (RecSlots.paramsOf outer)
        (RecSlots.casesOf outer (Fin.encodeSigma ι.nctors ⟨s, c⟩))
        ((model.codeOf s c).argMap (model.recrGraph s outer) (RecSlots.paramsOf outer)
          (model.ctorArgs s c (RecSlots.paramsOf outer) vfds vrecFds)) := by
    let fieldSlots := Fin.append (RecSlots.paramsOf outer) vfds
    have hparamReach' : RecSlots.paramsOf outer ∈ Reachable Set.univ model.paramsSem := by
      grind only [reachability]
    have hih (f) : ε₂[γ]⟦(I.map pre.sigs).iotaIHs η ls l ps ms mins
          s c fds recFds f⟧ =
        recMap (model.recCode s c f).tele (model.recCode s c f).index
          (model.recrGraph s outer) fieldSlots
          (recoverRecField (model.recCode s c f).tele (model.recCode s c f).index
            (model.toModel.block (RecSlots.paramsOf outer)) model.toModel.level
            fieldSlots (vrecFds f)) := by
      refine StrongRecursiveFieldSource.iotaIH_denotes_of_leaf
        ((I.ctors s c).recursive f) ((model.ctors s c).source.recursive f)
        pre hatoms (σ := Fin.append ps fds) γ fieldSlots
        (Reachable.append
          (Reachable.mono hfieldsReach (Set.singleton_subset_iff.mpr hparamReach')))
        ((Fin.append_comp ps fds fun e => ε₂[γ]⟦e⟧).trans
          (congrArg (Fin.append · _) (funext hps')))
        fun final hfinal => ?_
      simpa [hps', hms', hmins'] using (hrecr ((ι.ctors s c).recursiveTarget f) l
        (RecSlots.paramsOf outer) (RecSlots.motivesOf outer)
        (fun target c => RecSlots.casesOf outer
          (Fin.encodeSigma ι.nctors ⟨target, c⟩))
        (ε₁[final]⟦((I.ctors s c).recursive f).indices · |>.instL ls⟧)
        [zf|$(vrecFds f) $(fun argument =>
          final (Fin.natAdd (ι.nparams + (ι.ctors s c).nfields) argument))...]).trans
        (model.recursiveIotaLeaf s c f outer houter fieldSlots
          hfieldsReach vrecFds hrecFieldsMem final hfinal)
    rw [model.applyMinor_ctorApplication s c
      (RecSlots.paramsOf outer) vfds hfieldsReach vrecFds
      hrecFieldsMem (model.recrGraph s outer)
      (RecSlots.casesOf outer (Fin.encodeSigma ι.nctors ⟨s, c⟩))]
    simp [Inductive.iotaRhs, hmins', hih]
    rfl
  refine ⟨hlhsDen.trans hrhsDen.symm, ?_⟩
  have htype := Expr.denote_subst (ε := ε₂) (ν := zeroNs) γ (Inductive.recrSubst ps ms mins
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
