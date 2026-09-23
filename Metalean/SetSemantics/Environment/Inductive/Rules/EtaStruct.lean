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

theorem append_castLE_base (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vfds : Slots (ι.ctors s c).nfields) :
    (fun base : Fin ι.nparams => Fin.append vps vfds
      (base.castLE (model.ctors s c).source.ordinary.sem.le)) =
      vps := by
  funext base
  rw [show base.castLE (model.ctors s c).source.ordinary.sem.le =
    base.castAdd (ι.ctors s c).nfields from Fin.ext rfl, Fin.append_left]

theorem fieldsOf_ctorResult (hlevel : model.toModel.level ≠ 0) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (vps : Slots ι.nparams) (vis : Slots (ι.nindices s))
    (vfds : Slots (ι.ctors s c).nfields) (vrecFds : Slots (ι.ctors s c).nrecFields) :
    model.fieldsOf s c vps vis (model.ctorResult s c vps vfds vrecFds) = vfds := by
  have hvalues := SemTele.values_pack
    (model.ctors s c).source.ordinary.sem (Fin.append vps vfds)
    (CtorCode.packRecursive (model.toModel.block vps)
      (model.ctors s c).source.recursiveCodes
      model.toModel.level (Fin.append vps vfds) vrecFds proof)
  rw [model.append_castLE_base s c vps vfds] at hvalues
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

theorem ctorArgs_mem_argSet {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (hrec : IsEmpty (Fin (ι.ctors s c).nrecFields)) (vps : Slots ι.nparams)
    (vfds : Slots (ι.ctors s c).nfields) (vrecFds : Slots (ι.ctors s c).nrecFields)
    (hfieldsReach : Fin.append vps vfds ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem) :
    model.ctorArgs s c vps vfds vrecFds ∈
      (model.codeOf s c).argSet (model.toModel.block vps) vps := by
  have hargs := SemTele.pack_mem (Δ := (model.ctors s c).source.ordinary.sem) (reach := {vps})
    hfieldsReach (CtorCode.packRecursive_mem
      (fields := (model.ctors s c).source.recursiveCodes)
      (rest := .target (StrongCtorSource.targetIndex (model.ctors s c).target))
      (level := model.toModel.level) (γ := Fin.append vps vfds)
      (block := model.toModel.block vps) (values := vrecFds) (tail := proof)
      hrec.elim (CtorCode.proof_mem_argSet_target _))
  rwa [model.append_castLE_base s c vps vfds] at hargs

theorem ctorResult_mem_sortValue {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (hrec : IsEmpty (Fin (ι.ctors s c).nrecFields)) (hind : IsEmpty (Fin (ι.nindices s)))
    (vps : Slots ι.nparams)
    (vfds : Slots (ι.ctors s c).nfields) (vrecFds : Slots (ι.ctors s c).nrecFields)
    (vis : Slots (ι.nindices s)) (hfieldsReach : Fin.append vps vfds ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem) :
    model.ctorResult s c vps vfds vrecFds ∈ model.toModel.sortValue s vps vis := by
  have hentry := entry_mem_indSet (model.mapsTo vps)
    (model.ctorArgs_mem_argSet hrec vps vfds vrecFds hfieldsReach)
  rw [model.codeOf_targetIndex s c vps (model.ctorArgs s c vps vfds vrecFds),
    show model.targetValues s c (model.ordinaryOf s c vps (model.ctorArgs s c vps vfds vrecFds)) = vis from funext hind.elim] at hentry
  exact propVal_mem_propSet (entryValue_mem_fibre (by simpa [InductiveModel.block] using hentry))

section

variable (hdecl : SemDecls E₁ ε₁ ![])
  (hrule : SemDeclRules E₁ ε₁ ![]) (hE : EnvWF E₁) (hB : InductiveWF E₁ I)
include hdecl hrule hE hB

section

variable (total : E₁.as ⟶ E₂.as) (hatoms : AtomsMap total.sigs ε₁ ε₂)
include hatoms

theorem projTypeWith_denotes {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (vps : Slots ι.nparams)
    (hps : vps ∈ Reachable Set.univ model.paramsSem)
    (w : Slots (ι.nparams + (ι.ctors s c).nfields)) (hw : w ∈ Reachable {vps}
      (model.ctors s c).source.ordinary.sem)
    (f : Fin (ι.ctors s c).nfields) {m : Nat} {γ : Slots m}
    (ps₁ : Fin ι.nparams → Expr ζ₂ 0 m) (previous : Fin f.val → Expr ζ₂ 0 m)
    (hps₁ : ∀ param, ε₂[γ]⟦ps₁ param⟧ = w (param.castLE (by omega)))
    (hprevious : ∀ prior : Fin f.val, ε₂[γ]⟦previous prior⟧ =
      w (Fin.natAdd ι.nparams (prior.castLT (prior.isLt.trans f.isLt)))) :
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
    simpa [domain, Ctx.get_instL, Expr.denote, Level.eval_inst] using
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
    (hctors₂ : ∀ target ctor vps vfds vrecFds,
      ε₂ (.ctor η target ctor ls vps vfds vrecFds) =
        model.ctorResult target ctor vps vfds vrecFds)
    (hrecr₂ : ∀ target l vps vms vmins vis vmaj,
      ε₂ (.recr η target ls l vps vms vmins vis vmaj) =
        model.recLeaf target l (RecSlots.args vps vms vmins vis vmaj))
    (hlevel : model.toModel.level ≠ 0)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (hstruct : (I.map total.sigs).IsStructure s c)
    (vis : Slots (ι.nindices s)) (f : Fin (ι.ctors s c).nfields)
    {m₁ : Nat} {γ₁ : Slots m₁}
    {ps₁ : Fin ι.nparams → Expr ζ₂ 0 m₁} {maj₁ : Expr ζ₂ 0 m₁}
    (hvps : (ε₂[γ₁]⟦ps₁ ·⟧) ∈ Reachable Set.univ model.paramsSem)
    (hpsTy₁ : ∀ param, ε₂[γ₁]⟦ps₁ param⟧ ∈
      ε₂[γ₁]⟦(I.map total.sigs).paramType ls ps₁ param⟧)
    (hmajMem₁ : ε₂[γ₁]⟦maj₁⟧ ∈ model.toModel.sortValue s (ε₂[γ₁]⟦ps₁ ·⟧) vis) :
    ε₂[γ₁]⟦hstruct.projTerm η ls ps₁ f maj₁⟧ =
      model.fieldsOf s c (ε₂[γ₁]⟦ps₁ ·⟧) vis ε₂[γ₁]⟦maj₁⟧ f := by
  have ⟨bound, hbound⟩ : ∃ bound, f.val = bound := ⟨f.val, rfl⟩
  induction bound using Nat.strongRecOn generalizing f m₁ γ₁ ps₁ maj₁ with
  | _ bound ih =>
    subst hbound
    let vps := (ε₂[γ₁]⟦ps₁ ·⟧)
    have hdecomp {z : ZFSet} (hz : z ∈ model.toModel.sortValue s vps vis) :=
      model.ctorResult_of_mem_sortValue hstruct.sort_unique hstruct.ctor_unique
        hstruct.no_recursive vps vis hstruct.recursive hz
    have hsortAt {m : Nat} (δ : Slots m) (ps : Fin ι.nparams → Expr ζ₂ 0 m)
        (is : Fin (ι.nindices s) → Expr ζ₂ 0 m) (hps : (ε₂[δ]⟦ps ·⟧) = vps) :
        ε₂[δ]⟦.ind η s ls ps is⟧ = model.toModel.sortValue s vps vis := by
      simp only [Expr.denote]
      rw [hps, hsorts₂]
      exact congrArg _ (funext hstruct.no_indices.elim)
    let u : Level 0 := (((I.map total.sigs).ctors s c).ordinary f).level{ls}
    let mot := hstruct.projectionMotives η ls ps₁ f
    let Δcase := (I.map total.sigs).caseTele η ls ps₁ mot s c
    let projTy {m₂ : Nat} (ps₂ : Fin ι.nparams → Expr ζ₂ 0 m₂) (maj₂ : Expr ζ₂ 0 m₂) :=
      Inductive.IsStructure.projTypeWith (I.map total.sigs) ls ps₂ f fun prior =>
        hstruct.projTerm η ls ps₂ (prior.castLT (prior.isLt.trans f.isLt)) maj₂
    have hbody {m₂ : Nat} {γ₂ : Slots m₂}
        {ps₂ : Fin ι.nparams → Expr ζ₂ 0 m₂} {maj₂ : Expr ζ₂ 0 m₂}
        (hpsDen₂ : (ε₂[γ₂]⟦ps₂ ·⟧) = vps)
        (hpsTy₂ : ∀ param,
          ε₂[γ₂]⟦ps₂ param⟧ ∈ ε₂[γ₂]⟦(I.map total.sigs).paramType ls ps₂ param⟧)
        (hmajMem₂ : ε₂[γ₂]⟦maj₂⟧ ∈ model.toModel.sortValue s vps vis) :
        model.fieldsOf s c vps vis ε₂[γ₂]⟦maj₂⟧ f ∈ ε₂[γ₂]⟦projTy ps₂ maj₂⟧ ∧
          ε₂[γ₂]⟦projTy ps₂ maj₂⟧ ∈
            S_ (((I.ctors s c).ordinary f).level{ls}.eval ![]) := by
      have ⟨hmem, hsorted⟩ := model.projTypeWith_denotes hdecl hrule hE hB total hatoms vps hvps
        (Fin.append vps (model.fieldsOf s c vps vis ε₂[γ₂]⟦maj₂⟧)) (hdecomp hmajMem₂).1 f ps₂
        (fun prior => hstruct.projTerm η ls ps₂ (prior.castLT (prior.isLt.trans f.isLt)) maj₂)
        (γ := γ₂) fun param => by simpa using congrFun hpsDen₂ param
        fun prior => by
          rw [Fin.append_right]
          simpa [hpsDen₂] using ih prior.val prior.isLt _ (hpsDen₂ ▸ hvps) hpsTy₂
            (hpsDen₂ ▸ hmajMem₂) rfl
      rw [Fin.append_right] at hmem
      exact ⟨hmem, hsorted⟩
    have hindices : (ε₂[γ₁]⟦hstruct.indices ·⟧) = vis :=
      funext hstruct.no_indices.elim
    have hsortDen := hsortAt γ₁ ps₁ hstruct.indices rfl
    have hpsWk {k : Nat} (δ : Slots (m₁ + k))
        (hδ : (fun v : Fin m₁ => δ (v.castAdd k)) = γ₁) :
        (ε₂[δ]⟦ps₁ · |>.wkN k⟧) = vps ∧
          ∀ param, ε₂[δ]⟦(ps₁ param).wkN k⟧ ∈
            ε₂[δ]⟦(I.map total.sigs).paramType ls (fun p => (ps₁ p).wkN k) param⟧ :=
      ⟨funext fun param => by rw [Expr.denote_wkN, hδ],
        fun param => by
          rw [← Inductive.paramType_wkN]
          simpa only [Expr.denote_wkN, hδ] using hpsTy₁ param⟩
    let op (z : ZFSet) :=
      ε₂[Fin.snoc γ₁ z]⟦projTy (fun param => (ps₁ param).wkN 1) (.var (Fin.last m₁))⟧
    have hop (z : ZFSet) (hz : z ∈ model.toModel.sortValue s vps vis) :
        model.fieldsOf s c vps vis z f ∈ op z := by
      have ⟨hden, hty⟩ := hpsWk (k := 1) (Fin.snoc γ₁ z)
        (funext fun v => Fin.snoc_castSucc (α := fun _ => ZFSet) ..)
      have ⟨hmem, _⟩ := hbody (γ₂ := Fin.snoc γ₁ z) (ps₂ := fun param => (ps₁ param).wkN 1)
        (maj₂ := .var (Fin.last m₁)) hden hty (by simpa [Expr.denote] using hz)
      simpa [Expr.denote] using hmem
    let vms : Fin ι.nsorts → ZFSet :=
      fun _ => [zf|fun value : $(model.toModel.sortValue s vps vis) => $(op value)]
    have hmsDen (target : Fin ι.nsorts) : ε₂[γ₁]⟦mot target⟧ = vms target := by
      obtain rfl := (hstruct.sort_unique target).symm
      unfold mot
      rw [Inductive.IsStructure.projectionMotives_self, hstruct.projType_eq, Expr.denote,
        hsortDen]
      rfl
    have hmsMem (target : Fin ι.nsorts) : ε₂[γ₁]⟦mot target⟧ ∈
        ε₂[γ₁]⟦(I.map total.sigs).motiveType η ls ps₁ u target⟧ := by
      obtain rfl := (hstruct.sort_unique target).symm
      refine Expr.denote_lam_mem_pi fun slots hslots => ?_
      have hprefix : (fun v : Fin m₁ => slots (v.castAdd (ι.nindices s + 1))) = γ₁ :=
        Set.eq_of_mem_singleton (Reachable.base hslots)
      have ⟨hpsSlots, hpsTySlots⟩ := hpsWk (k := ι.nindices s + 1) slots hprefix
      have hlastMem : slots (Fin.last (m₁ + ι.nindices s)) ∈ model.toModel.sortValue s vps vis :=
        hsortAt (Fin.init slots) (fun param => (ps₁ param).wkN (ι.nindices s)) _
          (funext fun param => by
            rw [Expr.denote_wkN]
            exact congrArg (ε₂[·]⟦ps₁ param⟧) hprefix) ▸ Reachable.last hslots
      exact (hbody (maj₂ := .var (Fin.last (m₁ + ι.nindices s))) hpsSlots hpsTySlots
        hlastMem).2
    have hord₂ := ((congrArg (Realizes ε₂ ![] _ · _)
      (congrArg (·{ls}) (Ctor.ordinaryTeleAux_map total.sigs (I.ctors s c) _ _))).mp
      ((model.ctors s c).source.ordinary.realizes_mapInst total hatoms)).pull
      (reach₁ := {γ₁}) ps₁ (fun _ => vps)
      (fun δ hδ => by subst hδ; exact hvps) fun δ hδ v => by subst hδ; rfl
    have hnr : (ι.ctors s c).nrecFields = 0 := Fin.eq_zero_of_isEmpty hstruct.no_recursive
    have ⟨Δrec, hrecRealizes⟩ := Realizes.of_le (ε := ε₂) (ν := ![])
      (reach := Reachable {γ₁} ((model.ctors s c).source.ordinary.sem.pull
        (fun _ : Slots m₁ => vps) (ι.ctors s c).nfields)) (by omega)
      (((I.ctors s c).map total.sigs).recursiveFieldTele η ls
        (fun param => (ps₁ param).wkN (ι.ctors s c).nfields)
        (Expr.boundVars m₁ (ι.ctors s c).nfields 0))
    have hcaseRealizes := (hord₂.append hrecRealizes).append
      (Realizes.of_le (ε := ε₂) (ν := ![]) (by omega)
        (((I.ctors s c).map total.sigs).ihTele ls ps₁ mot)).choose_spec
    have hcaseValue : ε₂[γ₁]⟦hstruct.projectionCases η ls ps₁ f mot s c⟧ =
        ((model.ctors s c).source.ordinary.sem.pull
          (fun _ : Slots m₁ => vps) (ι.ctors s c).nfields).lam
          (fun slots => slots (Fin.natAdd m₁ f)) γ₁ := by
      rw [hstruct.projectionCases_self]
      exact Realizes.denotes_lam (reach := {γ₁}) rfl (fun slots _ => rfl) hord₂
    have hmins (target : Fin ι.nsorts) (ctor : Fin (ι.nctors target)) :
        ε₂[γ₁]⟦hstruct.projectionCases η ls ps₁ f mot target ctor⟧ ∈
        ε₂[γ₁]⟦(I.map total.sigs).caseFnType η ls ps₁ mot target ctor⟧ := by
      obtain rfl := (hstruct.sort_unique target).symm
      obtain rfl := (hstruct.ctor_unique ctor).symm
      refine Expr.denote_lam_mem_pi (Δ := Δcase) (body := (ι.ctors s c).caseOrdinary f)
        (leaf := (I.map total.sigs).caseType η ls ps₁ mot s c) fun slots hslots => ?_
      let vfds₁ : Slots (ι.ctors s c).nfields := fun i => slots ⟨m₁ + i.val, by omega⟩
      have hwk3 (e : Expr ζ₂ 0 m₁) :
          ε₂[slots]⟦((e.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields).wkN
            (ι.ctors s c).nrecFields⟧ = ε₂[γ₁]⟦e⟧ := by
        simp only [Expr.denote_wkN]
        change ε₂[fun v => slots (v.castLE Δcase.le)]⟦e⟧ = ε₂[γ₁]⟦e⟧
        rw [Set.eq_of_mem_singleton (Reachable.base hslots)]
      have hfieldVar (i : Fin (ι.ctors s c).nfields) :
          ε₂[slots]⟦(ι.ctors s c).caseOrdinary i⟧ = vfds₁ i := by
        unfold CtorSig.caseOrdinary CtorSig.fieldOrdinary
        rw [Expr.var_wkN, Expr.var_wkN]
        rfl
      have hreachArgs := Reachable.pull (reach := {vps})
        (Reachable.base (Reachable.of_append (Reachable.base (Reachable.of_append
          (Reachable.of_denote hcaseRealizes rfl hslots)))))
        fun base _ => rfl
      rw [show Slots.pull (fun _ : Slots m₁ => vps)
          (fun w : Fin (m₁ + (ι.ctors s c).nfields) =>
            (fun w₁ : Fin (m₁ + (ι.ctors s c).nfields +
              (ι.ctors s c).nrecFields) => slots (w₁.castLE (by omega)))
              (w.castLE (by omega))) = Fin.append vps vfds₁ from by
        funext w
        cases w using Fin.addCases with
        | left param => simp
        | right field =>
          simp only [Slots.pull_natAdd, Fin.append_right]
          exact congrArg slots (Fin.ext rfl)] at hreachArgs
      have hctorMem := model.ctorResult_mem_sortValue hstruct.no_recursive
        hstruct.no_indices vps vfds₁ hstruct.recursive vis hreachArgs
      rw [show ε₂[slots]⟦(I.map total.sigs).caseType η ls ps₁ mot s c⟧ =
          [zf|$(vms s) $(model.ctorResult s c vps vfds₁ hstruct.recursive)] from by
        simp only [Inductive.caseType, Inductive.motiveResult,
          Expr.apps_eq_self_of_zero (Fin.eq_zero_of_isEmpty hstruct.no_indices), Expr.denote,
          CtorSig.caseParams, CtorSig.fieldParams, hwk3, hmsDen, hfieldVar, hctors₂]
        congr 2
        exact funext hstruct.no_recursive.elim, Aczel.app_lam hctorMem, hfieldVar f]
      simpa [model.fieldsOf_ctorResult hlevel] using hop _ hctorMem
    let vminsVal := (ε₂[γ₁]⟦hstruct.projectionCases η ls ps₁ f mot · ·⟧)
    let vfds := model.fieldsOf s c vps vis ε₂[γ₁]⟦maj₁⟧
    have ⟨hreachFds, hrebuild⟩ := hdecomp hmajMem₁
    have hreach := model.recrArgs_reachable total hatoms hsorts₂
      hctors₂ u (maj := maj₁) hpsTy₁ hmsMem hmins
      hstruct.no_indices.elim
      (by rwa [hsortDen])
    rw [funext hmsDen, hindices] at hreach
    have hargs := model.ctorArgs_mem_argSet hstruct.no_recursive vps vfds hstruct.recursive
      hreachFds
    have hkey : (model.codeOf s c).targetIndex vps
        (model.ctorArgs s c vps vfds hstruct.recursive) = sortKey s.val (encode vis) := by
      rw [model.codeOf_targetIndex]
      exact congrArg (sortKey s.val)
        (congrArg encode (funext hstruct.no_indices.elim))
    have hiota := model.recLeaf_iota hdecl hrule hE hB s u
      ((I.recAllowed_map total.sigs u).mp (hstruct.recAllowed u))
      (RecSlots.args vps vms vminsVal vis ε₂[γ₁]⟦maj₁⟧) hreach c
      (by simpa using hargs)
      (by simpa [RecSlots.indicesOfSlots] using hkey)
      ((RecSlots.majorOfSlots_args ..).trans hrebuild.symm)
    rw [RecSlots.casesOf_args, RecSlots.paramsOf_args,
      model.applyMinor_ctorApplication s c vps vfds hreachFds hstruct.recursive hstruct.no_recursive.elim,
      Aczel.apps_of_zero hnr, Aczel.apps_of_zero hnr, show vminsVal s c = _ from hcaseValue] at hiota
    have hlamApp := Reachable.apps_lam_of_base
      (leaf := fun slots => slots (Fin.natAdd m₁ f))
      (Reachable.of_pull (by rwa [Slots.pull_append])
        (funext fun base => Fin.append_left γ₁ vfds base) :
        Fin.append γ₁ vfds ∈ Reachable {γ₁}
          ((model.ctors s c).source.ordinary.sem.pull
            (fun _ : Slots m₁ => vps) (ι.ctors s c).nfields))
    simp only [Fin.append_right] at hlamApp
    rw [hlamApp] at hiota
    rw [hstruct.projTerm_eq_recr]
    change ε₂[γ₁]⟦Expr.recr η s ls u ps₁ mot
      (hstruct.projectionCases η ls ps₁ f mot) hstruct.indices maj₁⟧ = _
    rw [Expr.denote, funext hmsDen, hindices]
    exact (hrecr₂ s _ vps _ _ vis ε₂[γ₁]⟦maj₁⟧).trans hiota

end

omit hE in
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
      model.projTerm_denotes_field hdecl hrule hE hB pre hatoms hsorts hctors hrecr hlevel
        hstruct vis f (model.paramsReachable pre hatoms hsorts hps)
        (fun param => (hps param).mem) hmajMem
    simpa [hfields] using (model.ctorResult_of_mem_sortValue hstruct.sort_unique hstruct.ctor_unique
      hstruct.no_recursive vps vis _ hmajMem).2
  exact ⟨hrebuild, hrebuild.symm ▸ hmaj.mem⟩

end

end StrongInductiveModel

end Metalean
