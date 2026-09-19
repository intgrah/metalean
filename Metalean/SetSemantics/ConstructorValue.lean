/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.ConstructorCode
public import Metalean.SetTheory.ZFC.Coding
import Metalean.Fin

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

namespace SemTele

variable {n b : Nat}

noncomputable def pack {b : Nat} : SemTele n b → Slots b → ZFSet → ZFSet
  | .nil => fun _ tail => tail
  | .snoc Δ _ => fun γ tail => pack Δ (Fin.init γ) (pair (γ (Fin.last _)) tail)

theorem tail_pack (Δ : SemTele n b) (γ : Slots b) (tail : ZFSet) :
    Δ.tail (Δ.pack γ tail) = tail := by
  induction Δ generalizing tail with
  | nil => rfl
  | snoc Δ domain ih => exact (congrArg snd (ih (Fin.init γ) _)).trans (snd_pair ..)

theorem values_pack (Δ : SemTele n b) (γ : Slots b) (tail : ZFSet) :
    Δ.values (fun base => γ (base.castLE Δ.le)) (Δ.pack γ tail) = γ := by
  induction Δ generalizing tail with
  | nil => rfl
  | snoc Δ domain ih =>
    change Slots.snoc
      (values (fun base => Fin.init γ (base.castLE Δ.le))
        (pack Δ (Fin.init γ) (pair (γ (Fin.last _)) tail)) Δ)
      (fst (SemTele.tail (pack Δ (Fin.init γ) (pair (γ (Fin.last _)) tail)) Δ)) = γ
    rw [ih, tail_pack, fst_pair]
    exact Fin.snoc_init_self γ

theorem pack_values {Δ : SemTele n b} {rest : CtorCode b}
    {block : ZFSet} {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ (CtorCode.prependOrdinary Δ rest).argSet block γ) :
    Δ.pack (Δ.values γ vargs) (Δ.tail vargs) = vargs := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    have ⟨_, _, _, _, heq⟩ :=
      CtorCode.argSet_arg_inv (CtorCode.tail_mem_argSet hargs)
    simp only [pack, values, SemTele.tail, Fin.init_snoc, Fin.snoc_last]
    rw [heq, fst_pair, snd_pair, ← heq]
    exact ih hargs

theorem tail_forgetIhs (Δ : SemTele n b) (rest : CtorCode b) (vargs : ZFSet) :
    Δ.tail ((CtorCode.prependOrdinary Δ rest).forgetIhs vargs) =
      rest.forgetIhs (Δ.tail vargs) := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih => exact (congrArg snd (ih (.arg domain rest))).trans (snd_pair ..)

theorem values_forgetIhs (Δ : SemTele n b) (rest : CtorCode b)
    (γ : Slots n) (vargs : ZFSet) :
    Δ.values γ ((CtorCode.prependOrdinary Δ rest).forgetIhs vargs) = Δ.values γ vargs := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    change Slots.snoc
      (values γ ((CtorCode.prependOrdinary Δ (.arg domain rest)).forgetIhs vargs) Δ)
      (fst (SemTele.tail ((CtorCode.prependOrdinary Δ (.arg domain rest)).forgetIhs vargs) Δ)) = _
    rw [ih, tail_forgetIhs]
    exact congrArg (Fin.snoc _) (fst_pair ..)

theorem forgetIhs_prependOrdinary (Δ : SemTele n b) (rest : CtorCode b)
    (γ : Slots n) (vargs : ZFSet) :
    (CtorCode.prependOrdinary Δ rest).forgetIhs vargs =
      Δ.pack (Δ.values γ vargs) (rest.forgetIhs (Δ.tail vargs)) := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    exact (ih (.arg domain rest)).trans (by simp [pack, values, SemTele.tail, CtorCode.forgetIhs])

theorem tail_argMap (Δ : SemTele n b) (rest : CtorCode b) (graph : ZFSet)
    (γ : Slots n) (vargs : ZFSet) :
    Δ.tail ((CtorCode.prependOrdinary Δ rest).argMap graph γ vargs) =
      rest.argMap graph (Δ.values γ vargs) (Δ.tail vargs) := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih => exact (congrArg snd (ih (.arg domain rest))).trans (snd_pair ..)

theorem applyFields_prependOrdinary {level count : Nat}
    (Δ : SemTele n (n + count)) (rest : CtorCode (n + count))
    (γ : Slots n) (fn vargs : ZFSet) :
    (CtorCode.prependOrdinary Δ rest).applyFields level γ fn vargs =
      rest.applyFields level (Δ.values γ vargs)
        [zf|fn $(fun f : Fin count => Δ.values γ vargs (Fin.natAdd n f))...]
        (Δ.tail vargs) := by
  induction Δ using Tele.addInduction generalizing fn with
  | nil => rfl
  | snoc count Δ domain ih =>
    refine (ih (.arg domain rest) fn).trans ?_
    change _ = rest.applyFields level (Slots.snoc (values γ vargs Δ) (fst (SemTele.tail vargs Δ)))
      [zf|fn $(fun f : Fin (count + 1) =>
        Slots.snoc (values γ vargs Δ) (fst (SemTele.tail vargs Δ)) (Fin.natAdd n f))...]
      (snd (SemTele.tail vargs Δ))
    rw [Slots.natAdd_snoc, Aczel.apps_snoc]
    rfl

theorem applyIhs_prependOrdinary (Δ : SemTele n b) (rest : CtorCode b)
    (fn vargs : ZFSet) :
    (CtorCode.prependOrdinary Δ rest).applyIhs fn vargs =
      rest.applyIhs fn (Δ.tail vargs) := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih => exact ih (.arg domain rest)

theorem predecessors_prependOrdinary (Δ : SemTele n b) (rest : CtorCode b)
    (γ : Slots n) (vargs : ZFSet) :
    (CtorCode.prependOrdinary Δ rest).predecessors γ vargs =
      rest.predecessors (Δ.values γ vargs) (Δ.tail vargs) := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih => exact ih (.arg domain rest)

theorem targetIndex_prependOrdinary (Δ : SemTele n b) (rest : CtorCode b)
    (γ : Slots n) (vargs : ZFSet) :
    (CtorCode.prependOrdinary Δ rest).targetIndex γ vargs =
      rest.targetIndex (Δ.values γ vargs) (Δ.tail vargs) := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih => exact ih (.arg domain rest)

end SemTele

namespace CtorCode

variable {n count : Nat} {block graph : ZFSet}

theorem targetIndex_prependRecursive
    {fields : Fin count → CtorRecCode.Packed n} {index : Dom n}
    (γ : Slots n) (vargs : ZFSet) :
    (prependRecursive count fields (.target index)).targetIndex γ vargs =
      index γ := by
  induction count generalizing vargs with
  | zero => rfl
  | succ count ih => exact ih (snd vargs)

theorem predecessors_mem_block (code : CtorCode n) (γ : Slots n)
    (vargs : ZFSet) (hargs : vargs ∈ code.argSet block γ) :
    ∀ predecessor ∈ code.predecessors γ vargs, predecessor ∈ block := by
  induction code generalizing vargs with
  | target => simp [predecessors]
  | arg domain rest ih =>
    obtain ⟨value, tail, _, htail, rfl⟩ := argSet_arg_inv hargs
    simpa! using ih (γ.snoc value) tail htail
  | recArg tele index rest ih =>
    obtain ⟨value, tail, hvalue, htail, rfl⟩ := argSet_recArg_inv hargs
    intro predecessor hpredecessor
    simp! at hpredecessor
    cases hpredecessor with
    | inl hentry =>
      exact mem_recEntries_of_mem tele index γ value hvalue predecessor hentry
    | inr hrest => exact ih γ tail htail predecessor hrest

noncomputable def packRecursive {n count : Nat} (block : ZFSet)
    (fields : Fin count → CtorRecCode.Packed n) (level : Nat)
    (γ : Slots n) (values : Fin count → ZFSet) (tail : ZFSet) : ZFSet :=
  match count with
  | 0 => tail
  | _ + 1 =>
    let f := fields 0
    pair (recoverRecField f.2.tele f.2.index block level γ (values 0))
      (packRecursive block (Fin.tail fields) level γ (Fin.tail values) tail)

theorem packRecursive_of_isEmpty {n count : Nat} (block : ZFSet)
    (fields : Fin count → CtorRecCode.Packed n) (level : Nat)
    (γ : Slots n) (values : Fin count → ZFSet) (tail : ZFSet)
    (hcount : IsEmpty (Fin count)) :
    packRecursive block fields level γ values tail = tail := by
  obtain rfl : count = 0 := Fin.eq_zero_of_isEmpty hcount
  rfl

theorem packRecursive_mem {fields : Fin count → CtorRecCode.Packed n}
    {rest : CtorCode n} {level : Nat} {γ : Slots n}
    {values : Fin count → ZFSet} {tail : ZFSet}
    (hvalues : ∀ f, values f ∈ typedRecFieldSet
      (fields f).2.tele (fields f).2.index block level γ)
    (htail : tail ∈ rest.argSet block γ) :
    packRecursive block fields level γ values tail ∈
      (prependRecursive count fields rest).argSet block γ := by
  induction count generalizing tail with
  | zero => exact htail
  | succ count ih =>
    let f := fields 0
    let restFields : Fin count → CtorRecCode.Packed n :=
      fun current => fields current.succ
    exact mem_argSet_recArg
      (recoverRecField_mem f.2.tele f.2.index (hvalues 0))
      (by simpa [Fin.tail_def] using ih (Fin.tail hvalues) htail)

theorem eraseRecField_recoverRecField {b level : Nat}
    (tele : SemTele n b) (index : Dom b) (block : ZFSet)
    (γ : Slots n) (value : ZFSet)
    (hfield : value ∈ typedRecFieldSet tele index block level γ) :
    eraseRecField tele level γ
        (recoverRecField tele index block level γ value) = value := by
  calc
    _ = _ := tele.lamAt_comp _ _ (fun _ _ => propGet_mem) γ value hfield
    _ = _ := tele.lamAt_congr (fun _ _ => propVal_propGet) γ value hfield
    _ = value := tele.lamAt_id
      (fun final => propSet level (fibreOp block (index final)))
      γ value hfield

theorem applyFields_packRecursive {level : Nat}
    (fields : Fin count → CtorRecCode.Packed n) (index : Dom n)
    (block : ZFSet) (γ : Slots n) (values : Fin count → ZFSet)
    (hvalues : ∀ f, values f ∈ typedRecFieldSet
      (fields f).2.tele (fields f).2.index block level γ)
    (minor : ZFSet) :
    (prependRecursive count fields (.target index)).applyFields level γ minor
        (packRecursive block fields level γ values proof) =
      [zf|minor values...] := by
  induction count generalizing minor with
  | zero => rfl
  | succ count ih =>
    let f := fields 0
    simp [Aczel.apps_succ, prependRecursive, packRecursive, applyFields]
    rw [eraseRecField_recoverRecField f.2.tele f.2.index block γ
      (values 0) (hvalues 0)]
    exact ih (Fin.tail fields) (Fin.tail values) (Fin.tail hvalues) [zf|minor $(values 0)]

theorem applyIhs_argMap_packRecursive {level : Nat}
    (fields : Fin count → CtorRecCode.Packed n) (index : Dom n)
    (block graph : ZFSet) (γ : Slots n) (values : Fin count → ZFSet)
    (minor : ZFSet) :
    (prependRecursive count fields (.target index)).applyIhs minor
        ((prependRecursive count fields (.target index)).argMap graph γ
          (packRecursive block fields level γ values proof)) =
      [zf|minor $(fun f =>
        recMap (fields f).2.tele (fields f).2.index graph γ
          (recoverRecField (fields f).2.tele (fields f).2.index block
            level γ (values f)))...] := by
  induction count generalizing minor with
  | zero => rfl
  | succ count ih =>
    let f := fields 0
    simp [Aczel.apps_succ, prependRecursive, packRecursive, argMap, applyIhs]
    exact ih (Fin.tail fields) (Fin.tail values)
      [zf|minor $(recMap f.2.tele f.2.index graph γ
        (recoverRecField f.2.tele f.2.index block level γ (values 0)))]

theorem splitIhArgSet_prependRecursive
    {motive : ZFSet} {level : Nat}
    {fields : Fin count → CtorRecCode.Packed n} {index : Dom n}
    {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ (prependRecursive count fields
      (.target index)).ihArgSet block motive γ) :
    ∃ raw ihs : Fin count → ZFSet,
      let typed := fun f => eraseRecField (fields f).2.tele level γ (raw f)
      (∀ f, raw f ∈ recFieldSet (fields f).2.tele
        (fields f).2.index block γ) ∧
      (∀ f, ihs f ∈ ihType (fields f).2.tele
        (fields f).2.index motive γ (raw f)) ∧
      (∀ fn, (prependRecursive count fields
        (.target index)).applyFields level γ fn
          ((prependRecursive count fields
            (.target index)).forgetIhs vargs) = [zf|fn typed...]) ∧
      (∀ fn, (prependRecursive count fields
        (.target index)).applyIhs fn vargs = [zf|fn ihs...]) ∧
      ∀ (tag : Nat) (build : ZFSet → ZFSet), propVal level (entryValue tag
          (build (packRecursive block fields level γ typed proof))) =
        propVal level (entryValue tag
          (build ((prependRecursive count fields
            (.target index)).forgetIhs vargs))) := by
  induction count generalizing vargs with
  | zero =>
    obtain rfl : vargs = proof := mem_verum.mp hargs
    exact ⟨![], ![], fun f => Fin.elim0 f, fun f => Fin.elim0 f,
      fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  | succ count ih =>
    let recCode := fields 0
    let rest : Fin count → CtorRecCode.Packed n := Fin.tail fields
    obtain ⟨fieldAndIh, hfieldAndIh, tail, htail, rfl⟩ := mem_sigma.mp hargs
    rw [app_map hfieldAndIh] at htail
    obtain ⟨rawHead, hrawHead, ihHead, hihHead, rfl⟩ := mem_sigma.mp hfieldAndIh
    rw [app_map hrawHead] at hihHead
    have ⟨rawTail, ihTail, hrawTail, hihTail, happlyFields, happlyIhs, hpacked⟩ :=
      ih htail
    let raw : Fin (count + 1) → ZFSet := Fin.cons rawHead rawTail
    let ihs : Fin (count + 1) → ZFSet := Fin.cons ihHead ihTail
    refine ⟨raw, ihs, Fin.cases hrawHead hrawTail, Fin.cases hihHead hihTail, ?_, ?_, ?_⟩
    · intro fn
      simp [prependRecursive, applyFields, forgetIhs, Aczel.apps_succ]
      exact happlyFields _
    · intro fn
      simp [prependRecursive, applyIhs, Aczel.apps_succ]
      exact happlyIhs _
    · intro tag build
      cases level with
      | zero => simp
      | succ level =>
        have herase := eraseRecField_of_ne_zero (Nat.succ_ne_zero level)
          recCode.2.tele recCode.2.index block γ rawHead hrawHead
        have hrecover := recoverRecField_of_ne_zero (Nat.succ_ne_zero level)
          recCode.2.tele recCode.2.index block γ rawHead hrawHead
        simp [packRecursive, raw]
        rw [herase, hrecover]
        simpa [prependRecursive, forgetIhs, Fin.tail_def] using
          hpacked tag fun tail => build (pair rawHead tail)

end CtorCode

end Metalean
