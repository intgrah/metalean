/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model
public import Metalean.SetSemantics.Environment.Inductive.Recursor.Case
import Metalean.SetSemantics.InductiveComputation
import Metalean.Syntax.Substitution

public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {bound : Nat}
  {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0}
  {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {ctor : Ctor ζ₁ ι s csig}
  {params : StrongTeleModel E₁ ε₁ ![] (Ctx.instL ls I.params)}
  (model : StrongInductiveModel E₁ ε₁ I ls)
  (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
  (hsorts : ∀ s vps vis, ε₂ (.ind η s ls vps vis) = model.toModel.sortValue s vps vis)
  (hctors : ∀ s c vps vfds vrecFds,
    ε₂ (.ctor η s c ls vps vfds vrecFds) = model.ctorResult s c vps vfds vrecFds)
  (l : Level 0)

private theorem SemTele.piAt_lamAt
    {a b : Nat} (tele : SemTele a b)
    {domain : Dom b} (map leaf leaf' : DomAt b)
    (h : ∀ final value, value ∈ domain final →
      leaf final value = leaf' final (map final value))
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ tele.pi domain γ) :
    tele.piAt leaf γ fn =
      tele.piAt leaf' γ (tele.lamAt map γ fn) := by
  induction tele generalizing fn with
  | nil => exact h γ fn hf
  | snoc tele binder ih =>
    apply ih
    · intro current value hvalue
      apply congrArg (Aczel.piMap (binder current))
      apply ZFSet.map_congr
      intro argument hargument
      rw [Aczel.app_lam hargument]
      have happ := Aczel.app_mem
        (b := ZFSet.map (fun argument => domain (current.snoc argument))
          (binder current)) hvalue hargument
      rw [app_map hargument] at happ
      exact h (current.snoc argument) [zf|value argument] happ
    · exact hf

private theorem StrongRecursiveFieldSource.ihType_eraseRecField
    {nfields arity : Nat} {s : Fin ι.nsorts}
    {Γ : Ctx ζ₁ 0 0 (ι.nparams + nfields)}
    {base : StrongTeleModel E₁ ε₁ ![] Γ}
    (recFd : RecField ζ₁ ι nfields arity s)
    (source : StrongRecursiveFieldSource E₁ ε₁ I ls base bound recFd)
    (level : Nat) (vms : Fin ι.nsorts → ZFSet) (block : ZFSet)
    (γ : Slots (ι.nparams + nfields)) (raw : ZFSet)
    (hraw : raw ∈ recFieldSet
      (StrongRecursiveFieldSource.code recFd source).tele
      (StrongRecursiveFieldSource.code recFd source).index block γ) :
    ihType (StrongRecursiveFieldSource.code recFd source).tele
        (StrongRecursiveFieldSource.code recFd source).index
        (bundleMotive level ι.nindices vms block) γ raw =
      ihType (StrongRecursiveFieldSource.code recFd source).tele
        (StrongRecursiveFieldSource.code recFd source).index
        (bundleMotive level ι.nindices vms block) γ
        (eraseRecField (StrongRecursiveFieldSource.code recFd source).tele
          level γ raw) := by
  let code := StrongRecursiveFieldSource.code recFd source
  refine code.tele.piAt_lamAt
    (domain := fun final => fibreOp block (code.index final))
    (map := fun _ value => propVal level value)
    (leaf := fun final value => fibreOp
      (bundleMotive level ι.nindices vms block)
      (pair (code.index final) value))
    (leaf' := fun final value => fibreOp
      (bundleMotive level ι.nindices vms block)
      (pair (code.index final) value)) ?_ γ raw ?_
  · intro final value hvalue
    have hentry : pair (code.index final) value ∈ block := mem_fibre.mp hvalue
    have htag : fst (fst (pair (code.index final) value)) =
        numeral s.val := by
      change fst (fst (pair
        (pair (numeral s.val)
          (encode (ε₁[final]⟦recFd.indices · |>.instL ls⟧)))
        value)) = _
      simp
    have hright := fibre_bundleMotive_value (level := level)
      (arities := ι.nindices) (vms := vms) s hentry htag
    simp only [fst_pair, snd_pair] at hright
    rw [fibre_bundleMotive (level := level) (arities := ι.nindices) (vms := vms) s hentry htag,
      hright]
    cases level <;> simp [motiveAt]
  · exact hraw

noncomputable def StrongInductiveModel.recrCaseDomain
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots (ι.nparams + ι.nsorts)) : ZFSet :=
  (model.recrCaseTele s c).pi (model.recrCaseLeaf s c) γ

theorem StrongInductiveModel.recrCase_applyMinor_mem
    (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s))
    (vps : Slots ι.nparams) (vms : Fin ι.nsorts → ZFSet)
    (hms : Fin.append vps vms ∈
      Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l))
    (minor : ZFSet)
    (hminor : minor ∈ model.recrCaseDomain s c (Fin.append vps vms))
    (vargs : ZFSet)
    (hargs : vargs ∈ (model.codeOf s c).ihArgSet
      (model.toModel.block vps) (model.recrCaseMotive vps vms) vps) :
    (model.codeOf s c).applyMinor model.toModel.level vps minor vargs ∈
      fibreOp (model.recrCaseMotive vps vms)
        (entry
          ((model.codeOf s c).targetIndex vps
            ((model.codeOf s c).forgetIhs vargs))
          (tagOf s c)
          ((model.codeOf s c).forgetIhs vargs)) := by
  let source := (model.ctors s c).source
  let fieldTele := source.ordinary.sem
  let fields := source.recursiveCodes
  let rest := CtorCode.prependRecursive (ι.ctors s c).nrecFields fields
    (.target (StrongCtorSource.targetIndex (model.ctors s c).target))
  have hps : vps ∈ Reachable Set.univ model.paramsSem := by
    simpa using Reachable.base hms
  have hfields := SemTele.reachable_values (Δ := fieldTele)
    (reach := Reachable Set.univ model.paramsSem)
    (CtorCode.forgetIhs_mem_argSet _ _ _ hargs) hps
  rw [SemTele.values_forgetIhs] at hfields
  let γ₁ := fieldTele.values vps vargs
  let vfds := fun f => γ₁ (Fin.natAdd ι.nparams f)
  have hfieldsBase : (fun param : Fin ι.nparams =>
      γ₁ (param.castLE fieldTele.le)) = vps :=
    funext <| fieldTele.values_base vps vargs
  have ⟨raw, ihs, hraw, hihs, happlyFields, happlyIhs, hpacked⟩ :=
    CtorCode.splitIhArgSet_prependRecursive
      (level := model.toModel.level) (fields := fields)
      (CtorCode.tail_mem_ihArgSet (Δ := fieldTele) (rest := rest) hargs)
  let typed := fun f => eraseRecField (fields f).2.tele model.toModel.level γ₁ (raw f)
  have hfieldsSlotsEq : γ₁ = Fin.append vps vfds := fieldTele.values_eq_append vps vargs
  have hrecFields : Fin.append γ₁ typed ∈ Reachable
      (Reachable (Reachable Set.univ model.paramsSem) fieldTele)
      (source.recursiveSem (fun current => model.toModel.block fun param =>
        current (param.castLE (Nat.le_add_right _ _))) model.toModel.level) :=
    Reachable.ofDoms_append hfields fun f => by
      simp only [typedRecFieldSetDep_apply]
      rw [hfieldsBase]
      exact eraseRecField_mem _ _ (hraw f)
  rw [hfieldsSlotsEq] at hrecFields
  let fieldSlots := Fin.append (Fin.append (Fin.append vps vms) vfds) typed
  have hrec := model.recrCaseFieldsSem_reachable l s c vps vms vfds typed hms hrecFields
  have hord := Reachable.base hrec
  have hihSlots : Fin.append (Fin.append (Fin.append (Fin.append vps vms) vfds) typed) ihs ∈
      Reachable
        (Reachable (Reachable (Reachable Set.univ model.paramsSem)
          (model.recrMotivesSem l)) (model.recrCaseFieldsSem s c))
        (model.recrCaseIhSem s c) :=
    Reachable.ofDoms_append (Reachable.append hrec) fun f => by
      simpa [← hfieldsSlotsEq] using
        StrongRecursiveFieldSource.ihType_eraseRecField ((I.ctors s c).recursive f)
          (source.recursive f) model.toModel.level vms (model.toModel.block vps) γ₁ (raw f) (hraw f) ▸
          hihs f
  have hminor₁ : minor ∈ SemTele.pi
      (SemTele.pi ((model.recrCaseIhSem s c).pi (model.recrCaseLeaf s c))
        (model.recrCaseRecursiveSem s c)) (model.recrCaseOrdinarySem s c)
      (Fin.append vps vms) := by
    rw [StrongInductiveModel.recrCaseDomain, StrongInductiveModel.recrCaseTele,
      StrongInductiveModel.recrCaseFieldsSem] at hminor
    simpa [SemTele.pi, SemTele.fold, Tele.foldr_append] using hminor
  have hordApp := Reachable.apps_mem_of_base hord (γ := Fin.append vps vms)
    (by simp) hminor₁
  have hrecApp := Reachable.apps_mem_of_base hrec (γ := Fin.append (Fin.append vps vms) vfds)
    (by simp) (by simpa using hordApp)
  have hleaf := Reachable.apps_mem_of_base hihSlots (γ := fieldSlots) (by simp [fieldSlots])
    (by simpa using hrecApp)
  simp only [Fin.append_right] at hleaf
  have happlyMinor : (model.codeOf s c).applyMinor model.toModel.level
        vps minor vargs = [zf|minor vfds... typed... ihs...] := by
    rw [show model.codeOf s c = CtorCode.prependOrdinary fieldTele rest from rfl]
    unfold CtorCode.applyMinor
    rw [SemTele.applyFields_prependOrdinary, SemTele.values_forgetIhs, SemTele.tail_forgetIhs,
      happlyFields, SemTele.applyIhs_prependOrdinary, happlyIhs]
  simp only [recrCaseLeaf, Fin.append_left, recrCaseParams_append, recrCaseMotives_append,
    recrCaseOrdinary_append, recrCaseRecursive_append] at hleaf
  let rawArgs := (model.codeOf s c).forgetIhs vargs
  have hfieldsRaw : model.ordinaryOf s c vps rawArgs = γ₁ :=
    fieldTele.values_forgetIhs rest vps vargs
  have hmaj : model.ctorResult s c vps vfds typed =
      propVal model.toModel.level (entryValue (tagOf s c) rawArgs) := by
    rw [show rawArgs = fieldTele.pack γ₁ (rest.forgetIhs (fieldTele.tail vargs)) from
      fieldTele.forgetIhs_prependOrdinary rest vps vargs]
    dsimp only [StrongInductiveModel.ctorResult, StrongInductiveModel.ctorArgs]
    rw [← hfieldsSlotsEq]
    exact hpacked _ (fieldTele.pack γ₁)
  have htarget := model.codeOf_targetIndex s c vps rawArgs
  rw [hfieldsRaw, hfieldsSlotsEq] at htarget
  have hentry : _ ∈ model.toModel.block vps := entry_mem_indSet (model.mapsTo vps)
    (CtorCode.forgetIhs_mem_argSet _ _ _ hargs)
  rw [htarget] at hentry
  have hvalue := hmaj ▸ propVal_mem_propSet (level := model.toModel.level)
    (entryValue_mem_fibre hentry)
  rwa [happlyMinor, htarget, recrCaseMotive, fibre_bundleMotive_propVal hentry, entry_eq, fst_pair,
    snd_pair, ← hmaj, fibre_bundleMotive_typed s _ hvalue]

include hatoms hsorts hctors in
theorem StrongInductiveModel.recrCaseDomain_denotes
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (γ : Slots (ι.nparams + ι.nsorts))
    (hγ : γ ∈ Reachable (Reachable Set.univ model.paramsSem) (model.recrMotivesSem l)) :
    ε₂[γ]⟦(I.map pre.sigs).caseFnType η ls
      (fun param => Expr.var (param.castLE (by omega)))
      (fun s => Expr.var ⟨ι.nparams + s.val, by omega⟩)
      s c⟧ = model.recrCaseDomain s c γ := by
  let ctorModel := model.ctors s c
  have hresult : DenotesOver ε₂ ![]
      (Reachable (Reachable Set.univ model.paramsSem)
        (model.recrMotivesSem l)) (model.recrCaseTele s c)
      ((I.map pre.sigs).caseType η ls
        (fun param => Expr.var (param.castLE (by omega)))
        (fun s => Expr.var ⟨ι.nparams + s.val, by omega⟩)
        s c) (model.recrCaseLeaf s c) := by
    intro δ hδ
    let sig := ι.ctors s c
    let fieldSlots : Slots (ι.nparams + ι.nsorts + sig.nfields + sig.nrecFields) :=
      fun v => δ (v.castAdd sig.nrecFields)
    have hsource := model.recrCaseFieldsSem_base s c l fieldSlots
      (Reachable.base (Reachable.of_append hδ))
    let ps : Fin ι.nparams → Expr ζ₂ 0 (ι.nparams + ι.nsorts) :=
      fun p => .var (p.castAdd ι.nsorts)
    have htarget (i : Fin (ι.nindices s)) :
        ε₂[δ]⟦((I.map pre.sigs).ctors s c).targetIndex ls
          (sig.caseParams ps) sig.caseOrdinary i⟧ =
        model.targetValues s c
          (Fin.append (model.recrCaseParams s c fieldSlots)
            (model.recrCaseOrdinary s c fieldSlots)) i := by
      have h := (Expr.denote_map pre.sigs hatoms _ _).trans
        (ctorModel.target.denotes _ hsource i)
      rw [Expr.map_instL] at h
      simp only [Ctor.targetIndex, Expr.denote_subst, Fin.append_comp, ps, CtorSig.caseParams,
        CtorSig.fieldParams, CtorSig.caseOrdinary, CtorSig.fieldOrdinary, Expr.var_wkN]
      exact h
    simp only [Inductive.caseType, Inductive.motiveResult, Expr.denote, Expr.denote_apps,
      CtorSig.caseParams, CtorSig.caseOrdinary, CtorSig.caseRecursive,
      CtorSig.fieldParams, CtorSig.fieldOrdinary, CtorSig.fieldRecursive, Expr.var_wkN]
    change [zf|$(model.recrCaseMotives s c fieldSlots s)
      $((ε₂[δ]⟦((I.map pre.sigs).ctors s c).targetIndex ls
        (sig.caseParams ps) sig.caseOrdinary ·⟧))...
      $(ε₂ (.ctor η s c ls (model.recrCaseParams s c fieldSlots)
        (model.recrCaseOrdinary s c fieldSlots)
        (model.recrCaseRecursive s c fieldSlots)))] = _
    rw [funext htarget, hctors]
    rfl
  exact ((model.recrCaseFieldsSem_realizes pre hatoms hsorts l s c).append
    (model.recrCaseIhSem_realizes pre hatoms l s c)).denotes_pi hγ hresult

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
  Realizes.ofTypes fun tag =>
    let ⟨s, c⟩ := Fin.decodeSigma ι.nctors tag
    model.recrCaseDomain_denotes pre hatoms hsorts hctors l s c

end StrongInductiveModel

end Metalean
