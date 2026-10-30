/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Recursor.Model
import Metalean.SetSemantics.Environment.Inductive.Recursor.Telescope
import Metalean.SetSemantics.Environment.Inductive.Rules.Constructor
import Metalean.SetSemantics.InductiveComputation
import Metalean.Typing.Inductive
import Metalean.Typing.InstLevel
import Metalean.Syntax.Structure.Projection
import Metalean.Syntax.Substitution

public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  (model : StrongInductiveModel E₁ ε₁ I ls)

namespace StrongInductiveModel

noncomputable def fieldsOf (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vis : Slots (ι.nindices s)) (vmaj : ZFSet) :
    Slots (ι.ctors s c).nfields :=
  fun f => (model.ctors s c).source.ordinary.sem.values vps
    (snd (propGet model.toModel.level
      (fibreOp (model.toModel.block vps) (sortKey s.val (encode vis))) vmaj))
    (Fin.natAdd ι.nparams f)

theorem fieldsOf_ctorResult (hlevel : model.toModel.level ≠ 0) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams) (vis : Slots (ι.nindices s))
    (vfds : Slots (ι.ctors s c).nfields) (vrecFds : Slots (ι.ctors s c).nrecFields) :
    model.fieldsOf s c vps vis (model.ctorResult s c vps vfds vrecFds) = vfds := by
  have hvalues := SemTele.values_pack
    (model.ctors s c).source.ordinary.sem (Fin.append vps vfds)
    (CtorCode.packRecursive (model.toModel.block vps)
      (model.ctors s c).source.recursiveCodes
      model.toModel.level (Fin.append vps vfds) vrecFds proof)
  simp at hvalues
  unfold fieldsOf ctorResult
  rw [propGet_of_ne_zero hlevel, propVal_of_ne_zero hlevel]
  change (fun f => (model.ctors s c).source.ordinary.sem.values vps
    (snd (pair (numeral (tagOf s c))
      (model.ctorArgs s c vps vfds vrecFds))) (Fin.natAdd ι.nparams f)) = vfds
  rw [snd_pair, show model.ctorArgs s c vps vfds vrecFds =
    (model.ctors s c).source.ordinary.sem.pack (Fin.append vps vfds) _ from rfl, hvalues]
  exact funext (Fin.append_right vps vfds)

theorem ctorResult_of_mem_sortValue {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (hsort : ∀ other : Fin ι.nsorts, other = s) (hctor : ∀ other : Fin (ι.nctors s), other = c)
    (hrec : IsEmpty (Fin (ι.ctors s c).nrecFields)) (vps : Slots ι.nparams)
    (vis : Slots (ι.nindices s)) (vrecFds : Slots (ι.ctors s c).nrecFields) {vmaj : ZFSet}
    (hmem : vmaj ∈ model.toModel.sortValue s vps vis) :
    Fin.append vps (model.fieldsOf s c vps vis vmaj) ∈
        Reachable {vps} (model.ctors s c).source.ordinary.sem ∧
      model.ctorResult s c vps (model.fieldsOf s c vps vis vmaj) vrecFds = vmaj := by
  let fieldTele := (model.ctors s c).source.ordinary.sem
  let carrier := fibreOp (model.toModel.block vps) (sortKey s.val (encode vis))
  have hcarrier : vmaj ∈ propSet model.toModel.level carrier := hmem
  let raw := propGet model.toModel.level carrier vmaj
  have hvalue : propVal model.toModel.level raw = vmaj := propVal_propGet hcarrier
  have hentry := mem_fibre.mp (propGet_mem hcarrier : raw ∈ carrier)
  rw [InductiveModel.block, ← indSet_unfold (model.mapsTo vps)] at hentry
  have ⟨s₁, c₁, vargs, hargs, hentryEq⟩ := mem_indOp.mp hentry
  obtain rfl := (hsort s₁).symm
  obtain rfl := (hctor c₁).symm
  have hrawEq : raw = entryValue (tagOf s c) vargs := by
    have h := congrArg snd hentryEq
    simp [entry_eq] at h
    exact h.symm
  have htailProof : fieldTele.tail vargs = proof :=
    CtorCode.eq_proof_of_mem_argSet_prependRecursive hrec
      (CtorCode.tail_mem_argSet hargs)
  let vfds : Slots (ι.ctors s c).nfields :=
    fun f => fieldTele.values vps vargs (Fin.natAdd ι.nparams f)
  have hslotsEq : fieldTele.values vps vargs = Fin.append vps vfds :=
    fieldTele.values_eq_append vps vargs
  rw [show model.fieldsOf s c vps vis vmaj = vfds from by
    change (fun f => fieldTele.values vps (snd raw) (Fin.natAdd ι.nparams f)) = vfds
    rw [hrawEq, entryValue, snd_pair]]
  refine ⟨hslotsEq ▸ SemTele.reachable_values hargs rfl, ?_⟩
  rw [ctorResult, show model.ctorArgs s c vps vfds vrecFds = vargs from by
    change fieldTele.pack (Fin.append vps vfds)
      (CtorCode.packRecursive (model.toModel.block vps) (model.ctors s c).source.recursiveCodes
        model.toModel.level (Fin.append vps vfds) vrecFds proof) = vargs
    rw [CtorCode.packRecursive_of_isEmpty _ _ _ _ _ _ hrec, ← hslotsEq, ← htailProof]
    exact SemTele.pack_values hargs, ← hrawEq, hvalue]

section

variable (hdecl : SemDecls E₁ ε₁ ![])
  (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁) (hB : InductiveWF E₁ I)
include hdecl hrule hB

section

variable (total : E₁.as ⟶ E₂.as) (hatoms : AtomsMap total.sigs ε₁ ε₂)
include hE hatoms

theorem projTypeWith_denotes {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (w : Slots (ι.nparams + (ι.ctors s c).nfields)) (hw : w ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem)
    (f : Fin (ι.ctors s c).nfields) {m : Nat} {γ : Slots m}
    (ps₁ : Fin ι.nparams → Expr ζ₂ 0 m) (previous : Fin f.val → Expr ζ₂ 0 m)
    (hps₁ : ∀ param, ε₂[γ]⟦ps₁ param⟧ = w (param.castLE (by omega)))
    (hprevious : ∀ prior : Fin f.val, ε₂[γ]⟦previous prior⟧ =
      w (Fin.natAdd ι.nparams (prior.castLE f.isLt.le))) :
    w (Fin.natAdd ι.nparams f) ∈
        ε₂[γ]⟦Inductive.IsStructure.projTypeWith (I.map total.sigs) ls ps₁ f previous⟧ ∧
      ε₂[γ]⟦Inductive.IsStructure.projTypeWith (I.map total.sigs) ls ps₁ f previous⟧ ∈
        S_ (((I.ctors s c).ordinary f).level{ls}.eval ![]) := by
  have hentry : Ctx.get (Fin.natAdd ι.nparams f)
      (I.params ++ (I.ctors s c).ordinaryTele){ls} =
      (Ctx.entry (I.ctors s c).ordinaryTele{ls}
          (Nat.le_add_right ι.nparams f.val) (by omega)).rename
        fun slot : Var (ι.nparams + f.val) => slot.castLE (by omega) := by
    rw [Ctx.get_eq_entry_rename _ _ (ι.nparams + f.val) (by omega) rfl, Ctx.instL_append,
      Ctx.entry_append_right I.params{ls}
        (I.ctors s c).ordinaryTele{ls} (by omega)
        (Nat.le_add_right ι.nparams f.val) (by omega)]
  let domain := ε₁[w]⟦Ctx.get (Fin.natAdd ι.nparams f)
    (I.params ++ (I.ctors s c).ordinaryTele){ls}⟧
  have hden : ε₁[fun v => w (v.castLE (by omega))]⟦Ctx.entry
      (I.ctors s c).ordinaryTele{ls} (Nat.le_add_right ι.nparams f.val) (by omega)⟧ =
      domain := by
    dsimp only [domain]
    rw [hentry, Expr.denote_rename]
    rfl
  have hsorted : domain ∈ S_ (((I.ctors s c).ordinary f).level{ls}.eval ![]) := by
    simpa! [domain, Ctx.get_instL, Level.eval_inst] using
      (soundness hdecl hrule hE (((hB.ctors s c).ordinaryTele_get f).instLevel ls) w
        (model.ordinarySemCtx s c vps hps w hw)).mem
  suffices htype : ε₂[γ]⟦Inductive.IsStructure.projTypeWith
      (I.map total.sigs) ls ps₁ f previous⟧ = domain by
    rw [htype]
    exact ⟨model.ordinarySemCtx s c vps hps w hw (Fin.natAdd ι.nparams f), hsorted⟩
  rw [← Ctx.entry_instL, Ctor.ordinaryTeleAux_entry] at hden
  change ε₂[γ]⟦(((I.ctors s c).ordinary f).type.map total.sigs){ls}.subst
    (Fin.append ps₁ previous)⟧ = domain
  rw [Expr.denote_subst]
  have hσ : (ε₂[γ]⟦Fin.append ps₁ previous ·⟧) =
      fun v : Fin (ι.nparams + f.val) => w (v.castLE (by omega)) := by
    funext v
    cases v using Fin.addCases with
    | left v =>
      rw [Fin.append_left, hps₁]
      exact congrArg w (Fin.ext rfl)
    | right v =>
      rw [Fin.append_right, hprevious]
      exact congrArg w (Fin.ext rfl)
  rwa [hσ, ← Expr.map_instL, Expr.denote_map total.sigs hatoms]

theorem projTerm_denotes_field
    (hsorts₂ : ∀ target vps vis,
      ε₂ (.ind η target ls vps vis) = model.toModel.sortValue target vps vis)
    (hrecr₂ : ∀ target l vps vms vmins vis vmaj,
      ε₂ (.recr η target ls l vps vms vmins vis vmaj) =
        model.recLeaf target l (RecSlots.args vps vms vmins vis vmaj))
    (hlevel : model.toModel.level ≠ 0)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (hstruct : (I.map total.sigs).IsStructure s c)
    (vis : Slots (ι.nindices s)) (f : Fin (ι.ctors s c).nfields)
    {m₁ : Nat} {γ₁ : Slots m₁}
    {ps₁ : Fin ι.nparams → Expr ζ₂ 0 m₁} {maj₁ : Expr ζ₂ 0 m₁}
    (hvps : (ε₂[γ₁]⟦ps₁ ·⟧) ∈ Reachable Set.univ model.paramsSem)
    (hmajMem₁ : ε₂[γ₁]⟦maj₁⟧ ∈ model.toModel.sortValue s (ε₂[γ₁]⟦ps₁ ·⟧) vis) :
    ε₂[γ₁]⟦hstruct.projTerm η ls ps₁ f maj₁⟧ =
      model.fieldsOf s c (ε₂[γ₁]⟦ps₁ ·⟧) vis ε₂[γ₁]⟦maj₁⟧ f := by
  induction f using Fin.strong_induction_on with
  | h f ih =>
    let vps := (ε₂[γ₁]⟦ps₁ ·⟧)
    let major := ε₂[γ₁]⟦maj₁⟧
    let vfds := model.fieldsOf s c vps vis major
    have ⟨hfields, hrebuild⟩ := model.ctorResult_of_mem_sortValue hstruct.sort_unique
      hstruct.ctor_unique hstruct.no_recursive vps vis hstruct.recursive hmajMem₁
    have htyped : vfds f ∈ ε₂[γ₁]⟦hstruct.projType η ls ps₁ f maj₁⟧ ∧
        ε₂[γ₁]⟦hstruct.projType η ls ps₁ f maj₁⟧ ∈
          S_ (((I.ctors s c).ordinary f).level{ls}.eval ![]) := by
      rw [hstruct.projType_eq_projTypeWith]
      have h := model.projTypeWith_denotes hdecl hrule hE hB total hatoms vps hvps
        (Fin.append vps vfds) hfields f ps₁
        (fun prior => hstruct.projTerm η ls ps₁ (prior.castLE f.isLt.le) maj₁)
        (γ := γ₁) (by simp [vps]) (fun prior => by
          simpa [vfds, vps, major] using ih (prior.castLE f.isLt.le) prior.isLt)
      simpa using h
    let u := (((I.map total.sigs).ctors s c).ordinary f).level{ls}
    let mot := hstruct.projectionMotives η ls ps₁ f
    let vms := (ε₂[γ₁]⟦mot ·⟧)
    let vmins := (ε₂[γ₁]⟦hstruct.projectionCases η ls ps₁ f mot · ·⟧)
    have hmotive : [zf|$(vms s) vis... major] = ε₂[γ₁]⟦hstruct.projType η ls ps₁ f maj₁⟧ := by
      rw [Aczel.apps_of_zero (Fin.eq_zero_of_isEmpty hstruct.no_indices)]
      change Aczel.app ε₂[γ₁]⟦hstruct.projectionMotives η ls ps₁ f s⟧ major = _
      rw [hstruct.projectionMotives_self, Expr.denote,
        show ε₂[γ₁]⟦.ind η s ls ps₁ hstruct.indices⟧ = model.toModel.sortValue s vps vis from by
          rw [Expr.denote, hsorts₂]
          exact congrArg _ (funext hstruct.no_indices.elim), Aczel.app_lam hmajMem₁]
      rw [← Expr.denote_inst γ₁ maj₁]
      simp [Expr.inst, Expr.wk_subst_extend]
    have hord := ((congrArg (Realizes ε₂ ![] _ · _)
      (congrArg (·{ls}) (Ctor.ordinaryTeleAux_map total.sigs (I.ctors s c) _ _))).mp
      ((model.ctors s c).source.ordinary.realizes.mapInst total hatoms)).pull
      (reach₁ := {γ₁}) ps₁ (fun _ => vps)
      (fun _ _ => hvps) (fun _ hγ _ => by subst hγ; rfl)
    have hcase : [zf|$(vmins s c) vfds...] = vfds f := by
      change Aczel.apps ε₂[γ₁]⟦hstruct.projectionCases η ls ps₁ f mot s c⟧ vfds = _
      rw [hstruct.projectionCases_self]
      have hden := hord.denotes_lam (e := Expr.boundVars m₁ (ι.ctors s c).nfields 0 f)
        (leaf := fun slots => slots (Fin.natAdd m₁ f))
        (Set.mem_singleton γ₁)
        (fun _ _ => rfl)
      have hfinal : Fin.append γ₁ vfds ∈ Reachable {γ₁}
          ((model.ctors s c).source.ordinary.sem.pull (fun _ : Slots m₁ => vps)
            (ι.ctors s c).nfields) :=
        Reachable.of_pull (by simpa using hfields) (by simp)
      have hbeta := Reachable.apps_lam_of_base
        (leaf := fun slots => slots (Fin.natAdd m₁ f)) hfinal
      exact (congrArg (fun fn => Aczel.apps fn vfds) hden).trans (by simpa using hbeta)
    let args := model.ctorArgs s c vps vfds hstruct.recursive
    have hargs : args ∈ (model.codeOf s c).argSet ∅ vps := by
      have htail := CtorCode.packRecursive_mem (block := (∅ : ZFSet))
        (fields := (model.ctors s c).source.recursiveCodes)
        (rest := CtorCode.target (StrongCtorSource.targetIndex (model.ctors s c).source))
        (level := model.toModel.level) (γ := Fin.append vps vfds)
        (block₁ := model.toModel.block vps) (values := hstruct.recursive)
        hstruct.no_recursive.elim proof_mem_verum
      simpa [args, ctorArgs, codeOf, StrongCtorSource.code, recursiveRest, vfds, major] using
        SemTele.pack_mem hfields htail
    have htarget : (model.codeOf s c).targetIndex vps args = sortKey s.val (encode vis) := by
      rw [model.codeOf_targetIndex]
      exact congrArg (sortKey s.val) (congrArg encode (funext hstruct.no_indices.elim))
    have hmajor : major = entryValue (tagOf s c) args := by
      change ε₂[γ₁]⟦maj₁⟧ = _
      rw [← hrebuild, ctorResult, propVal_of_ne_zero hlevel]
    have happly : (model.codeOf s c).applyMinor model.toModel.level ∅ vps
        [zf|$(minorFamily (RecSlots.args vps vms vmins vis major).cases) $(encode (tagOf s c))]
        args = vfds f := by
      have hminor : [zf|$(minorFamily (RecSlots.args vps vms vmins vis major).cases)
          $(encode (tagOf s c))] =
          (RecSlots.args vps vms vmins vis major).cases (Fin.encodeSigma ι.nctors ⟨s, c⟩) :=
        app_minorFamily _ (Fin.encodeSigma ι.nctors ⟨s, c⟩)
      rw [hminor]
      dsimp only [RecSlots.args]
      rw [Fin.decodeSigma_encodeSigma]
      rw [model.applyMinor_ctorApplication s c vps vfds hstruct.recursive hstruct.no_recursive.elim,
        Aczel.apps_of_zero (Fin.eq_zero_of_isEmpty hstruct.no_recursive),
        Aczel.apps_of_zero (Fin.eq_zero_of_isEmpty hstruct.no_recursive), hcase]
    have hiota := recGraph_iota_of_empty (model.mapsTo vps)
      (motive := model.recrCaseMotive vps vms) (minors := minorFamily
        (RecSlots.args vps vms vmins vis major).cases) hargs
      (by
        rw [happly, htarget, entry_eq, ← hmajor, recrCaseMotive,
          fibre_bundleMotive_typed s vis hmajMem₁, hmotive]
        exact htyped.1)
    rw [happly, htarget, entry_eq, ← hmajor] at hiota
    rw [hstruct.projTerm_eq_recr, Expr.denote, hrecr₂,
      show (ε₂[γ₁]⟦hstruct.indices ·⟧) = vis from funext hstruct.no_indices.elim, recLeaf]
    change propVal (u.eval ![]) (app (model.recrGraph s (RecSlots.args vps vms vmins vis major))
      (model.recrState s (RecSlots.args vps vms vmins vis major))) = _
    rw [recrState, recrMajorOf, propGet_of_ne_zero hlevel]
    change propVal (u.eval ![]) (app (model.recrGraph s (RecSlots.args vps vms vmins vis major))
      (pair (sortKey s.val (encode vis)) major)) = _
    rw [show app (model.recrGraph s (RecSlots.args vps vms vmins vis major))
        (pair (sortKey s.val (encode vis)) major) = vfds f from hiota]
    exact propVal_eq_self_of_mem htyped.2 htyped.1

end

theorem etaStructRuleSound
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    (hblock : (E₂.get η).block = I.map pre.sigs)
    (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
    (hctors : ∀ s c vps vfds vrecFds,
      ε₂ (.ctor η s c ls vps vfds vrecFds) = model.ctorResult s c vps vfds vrecFds)
    (hrecr : ∀ s l vps vms vmins vis vmaj,
      ε₂ (.recr η s ls l vps vms vmins vis vmaj) =
        model.recLeaf s l (RecSlots.args vps vms vmins vis vmaj))
    {n : Nat}
    {γ : Slots n} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {ps : Fin ι.nparams → Expr ζ₂ 0 n}
    {is : Fin (ι.nindices s) → Expr ζ₂ 0 n} {maj : Expr ζ₂ 0 n}
    (hstruct : (E₂.get η).block.IsStructure s c) :
    EnvWF E₁ →
    (∀ param, ε₂[γ] ⊨ ps param ≡ ps param : (E₂.get η).block.paramType ls ps param) →
    ε₂[γ] ⊨ maj ≡ maj : .ind η s ls ps is →
    ε₂[γ] ⊨ hstruct.rebuildTerm η ls ps maj ≡ maj :
      .ind η s ls ps is := by
  intro hE hps hmaj
  revert hstruct hps
  rw [hblock]
  intro hstruct hps
  let vps : Slots ι.nparams := (ε₂[γ]⟦ps ·⟧)
  let vis : Slots (ι.nindices s) := hstruct.no_indices.elim
  have htype : ε₂[γ]⟦.ind η s ls ps is⟧ = model.toModel.sortValue s vps vis := by
    simp only [Expr.denote]
    rw [hsorts]
    exact congrArg _ (funext hstruct.no_indices.elim)
  have hmajMem : ε₂[γ]⟦maj⟧ ∈ model.toModel.sortValue s vps vis := htype ▸ hmaj.mem
  have hrebuild : ε₂[γ]⟦hstruct.rebuildTerm η ls ps maj⟧ = ε₂[γ]⟦maj⟧ := by
    simp only [Inductive.IsStructure.rebuildTerm, Expr.denote]
    rw [hctors]
    by_cases hlevel : model.toModel.level = 0
    · rw [InductiveModel.sortValue, hlevel] at hmajMem
      have ⟨_, _, hproof⟩ := mem_squash.mp hmajMem
      rw [ctorResult, hlevel, propVal_zero, hproof]
    have hfields (f) : ε₂[γ]⟦hstruct.projTerm η ls ps f maj⟧ =
        model.fieldsOf s c vps vis ε₂[γ]⟦maj⟧ f :=
      model.projTerm_denotes_field hdecl hrule hE hB pre hatoms hsorts hrecr hlevel
        hstruct vis f (model.paramsReachable pre hatoms hps)
        hmajMem
    simpa [hfields] using (model.ctorResult_of_mem_sortValue hstruct.sort_unique hstruct.ctor_unique
      hstruct.no_recursive vps vis _ hmajMem).2
  exact ⟨hrebuild, hrebuild.symm ▸ hmaj.mem⟩

end

end StrongInductiveModel

end Metalean
