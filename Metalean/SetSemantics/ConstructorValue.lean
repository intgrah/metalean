/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.ConstructorCode
public import Metalean.SetTheory.ZFC.Coding
import Metalean.Data.Fin

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

namespace SemTele

variable {n b : Nat} {block : ZFSet}

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
      mem_sigma_map.mp (CtorCode.tail_mem_argSet (Δ := Δ) hargs)
    simp only [pack, values, SemTele.tail, Fin.init_snoc, Fin.snoc_last]
    rw [heq, fst_pair, snd_pair, ← heq]
    exact ih hargs

theorem applyFields_prependOrdinary {level : Nat}
    (Δ : SemTele n b) (rest : CtorCode b) (γ : Slots n) (fn vargs : ZFSet) :
    (CtorCode.prependOrdinary Δ rest).applyFields level γ fn vargs =
      rest.applyFields level (Δ.values γ vargs) (Δ.app (Δ.values γ vargs) fn) (Δ.tail vargs) := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    change (CtorCode.prependOrdinary Δ (.arg domain rest)).applyFields level γ fn vargs = _
    rw [ih]
    simp [CtorCode.applyFields, app, values, SemTele.tail]

theorem applyIhs_prependOrdinary (Δ : SemTele n b) (rest : CtorCode b)
    (graph : ZFSet) (γ : Slots n) (fn vargs : ZFSet) :
    (CtorCode.prependOrdinary Δ rest).applyIhs graph γ fn vargs =
      rest.applyIhs graph (Δ.values γ vargs) fn (Δ.tail vargs) := by
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

theorem reachable_values {Δ : SemTele n b} {rest : CtorCode b}
    {reach : Set (Slots n)} {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ (CtorCode.prependOrdinary Δ rest).argSet block γ)
    (hγ : γ ∈ reach) :
    Δ.values γ vargs ∈ Reachable reach Δ := by
  induction Δ with
  | nil => exact .nil hγ
  | snoc Δ domain ih =>
    have ⟨_, _, hvalue, _, heq⟩ :=
      mem_sigma_map.mp (CtorCode.tail_mem_argSet (Δ := Δ) hargs)
    change Fin.snoc (values γ vargs Δ) (fst (SemTele.tail vargs Δ)) ∈
      Reachable reach (Δ.snoc domain)
    refine .snoc ?_ ?_
    · rw [Fin.init_snoc]
      exact ih hargs
    · rwa [Fin.init_snoc, Fin.snoc_last, heq, fst_pair]

theorem pack_mem {Δ : SemTele n b} {rest : CtorCode b}
    {reach : Set (Slots n)} {γ : Slots b} {tail : ZFSet}
    (hγ : γ ∈ Reachable reach Δ)
    (htail : tail ∈ rest.argSet block γ) :
    Δ.pack γ tail ∈ (CtorCode.prependOrdinary Δ rest).argSet block
      fun base => γ (base.castLE Δ.le) := by
  induction Δ generalizing tail with
  | nil => exact htail
  | snoc Δ domain ih =>
    have .snoc hprefix hlast := hγ
    refine ih hprefix (pair_mem_sigma_map.mpr ⟨hlast, ?_⟩)
    simpa [Slots.snoc] using htail

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
    {rest : CtorCode n} {block₁ : ZFSet} {level : Nat} {γ : Slots n}
    {values : Fin count → ZFSet} {tail : ZFSet}
    (hvalues : ∀ f, recoverRecField (fields f).2.tele (fields f).2.index block₁ level γ (values f) ∈
      recFieldSet (fields f).2.tele (fields f).2.index block γ)
    (htail : tail ∈ rest.argSet block γ) :
    packRecursive block₁ fields level γ values tail ∈
      (prependRecursive count fields rest).argSet block γ := by
  induction count generalizing tail with
  | zero => exact htail
  | succ count ih =>
    let f := fields 0
    exact pair_mem_sigma_map.mpr ⟨hvalues 0,
      by simpa [Fin.tail_def] using ih (Fin.tail hvalues) htail⟩

theorem eraseRecField_recoverRecField {b level : Nat}
    (tele : SemTele n b) (index : Dom b) (block : ZFSet)
    (γ : Slots n) (value : ZFSet)
    (hfield : value ∈ typedRecFieldSet tele index block level γ) :
    eraseRecField tele level γ
        (recoverRecField tele index block level γ value) = value := by
  calc
    _ = _ := tele.lamAt_comp _ _ γ value
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
    simp! [Aczel.apps_succ]
    rw [eraseRecField_recoverRecField f.2.tele f.2.index block γ
      (values 0) (hvalues 0)]
    exact ih (Fin.tail fields) (Fin.tail values) (Fin.tail hvalues) [zf|minor $(values 0)]

theorem applyIhs_packRecursive {level : Nat}
    (fields : Fin count → CtorRecCode.Packed n) (index : Dom n)
    (block graph : ZFSet) (γ : Slots n) (values : Fin count → ZFSet)
    (minor : ZFSet) :
    (prependRecursive count fields (.target index)).applyIhs graph γ minor
        (packRecursive block fields level γ values proof) =
      [zf|minor $(fun f =>
        recMap (fields f).2.tele (fields f).2.index graph γ
          (recoverRecField (fields f).2.tele (fields f).2.index block
            level γ (values f)))...] := by
  induction count generalizing minor with
  | zero => rfl
  | succ count ih =>
    let f := fields 0
    simp! [Aczel.apps_succ]
    exact ih (Fin.tail fields) (Fin.tail values)
      [zf|minor $(recMap f.2.tele f.2.index graph γ
        (recoverRecField f.2.tele f.2.index block level γ (values 0)))]

theorem recursiveValues_mem {fields : Fin count → CtorRecCode.Packed n} {index : Dom n}
    {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ (prependRecursive count fields (.target index)).argSet block γ) :
    ∀ f, tupleValues count vargs f ∈ recFieldSet (fields f).2.tele (fields f).2.index block γ := by
  induction count generalizing vargs with
  | zero => exact fun f => Fin.elim0 f
  | succ count ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma_map.mp hargs
    simpa using Fin.cases hvalue (ih (fields := Fin.tail fields) htail)

theorem applyFields_prependRecursive (fields : Fin count → CtorRecCode.Packed n)
    (index : Dom n) (level : Nat) (γ : Slots n) (fn vargs : ZFSet) :
    (prependRecursive count fields (.target index)).applyFields level γ fn vargs =
      [zf|fn $(fun f => eraseRecField (fields f).2.tele level γ (tupleValues count vargs f))...] := by
  induction count generalizing fn vargs with
  | zero => rfl
  | succ count ih =>
    simpa [prependRecursive, applyFields, applyIhs, Aczel.apps_succ, Fin.tail_def] using ih (Fin.tail fields)
      [zf|fn $(eraseRecField (fields 0).2.tele level γ (fst vargs))] (snd vargs)

theorem applyIhs_prependRecursive (fields : Fin count → CtorRecCode.Packed n)
    (index : Dom n) (graph : ZFSet) (γ : Slots n) (fn vargs : ZFSet) :
    (prependRecursive count fields (.target index)).applyIhs graph γ fn vargs =
      [zf|fn $(fun f => recMap (fields f).2.tele (fields f).2.index graph γ
        (tupleValues count vargs f))...] := by
  induction count generalizing fn vargs with
  | zero => rfl
  | succ count ih =>
    simpa [prependRecursive, applyFields, applyIhs, Aczel.apps_succ, Fin.tail_def] using ih (Fin.tail fields)
      [zf|fn $(recMap (fields 0).2.tele (fields 0).2.index graph γ (fst vargs))] (snd vargs)

theorem packRecursive_erase {fields : Fin count → CtorRecCode.Packed n} {index : Dom n}
    {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ (prependRecursive count fields (.target index)).argSet block γ)
    (level tag : Nat) (build : ZFSet → ZFSet) :
    propVal level (entryValue tag (build (packRecursive block fields level γ
      (fun f => eraseRecField (fields f).2.tele level γ (tupleValues count vargs f)) proof))) =
      propVal level (entryValue tag (build vargs)) := by
  induction count generalizing vargs build with
  | zero => rw [mem_verum.mp hargs]; rfl
  | succ count ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma_map.mp hargs
    cases level with
    | zero => simp
    | succ level =>
      have herase := eraseRecField_of_ne_zero (Nat.succ_ne_zero level)
        (fields 0).2.tele (fields 0).2.index block γ value hvalue
      have hrecover := recoverRecField_of_ne_zero (Nat.succ_ne_zero level)
        (fields 0).2.tele (fields 0).2.index block γ value hvalue
      simp only [packRecursive, tupleValues_succ, fst_pair, snd_pair, Fin.cons_zero]
      rw [herase, hrecover]
      exact ih (fields := Fin.tail fields) (build := fun tail => build (pair value tail)) htail

theorem applyMinor_zero_congr
    (fields : Fin count → CtorRecCode.Packed n) (index : Dom n)
    {block₁ block₂ graph : ZFSet}
    (hgraph : ∀ key value₁ value₂,
      pair key value₁ ∈ block₁ → pair key value₂ ∈ block₂ →
      app graph (pair key value₁) = app graph (pair key value₂))
    (γ : Slots n) (minor : ZFSet) {left right : ZFSet}
    (hleft : left ∈ (prependRecursive count fields (.target index)).argSet block₁ γ)
    (hright : right ∈ (prependRecursive count fields (.target index)).argSet block₂ γ) :
    (prependRecursive count fields (.target index)).applyMinor 0 graph γ minor left =
      (prependRecursive count fields (.target index)).applyMinor 0 graph γ minor right := by
  have hl := recursiveValues_mem hleft
  have hr := recursiveValues_mem hright
  have hfields : (fun f => eraseRecField (fields f).2.tele 0 γ (tupleValues count left f)) =
      fun f => eraseRecField (fields f).2.tele 0 γ (tupleValues count right f) :=
    funext fun f => eraseRecField_zero_eq _ _ _ _ _ _ (hl f) (hr f)
  have hihs : (fun f => recMap (fields f).2.tele (fields f).2.index graph γ
        (tupleValues count left f)) =
      fun f => recMap (fields f).2.tele (fields f).2.index graph γ
        (tupleValues count right f) := by
    funext f
    apply (fields f).2.tele.lamAt_eq_of_mem
      (leftDomain := fun final => fibreOp block₁ ((fields f).2.index final))
      (rightDomain := fun final => fibreOp block₂ ((fields f).2.index final))
      (hleft := hl f) (hright := hr f)
    exact fun _ _ _ h₁ h₂ => hgraph _ _ _ (mem_fibre.mp h₁) (mem_fibre.mp h₂)
  simp only [applyMinor, applyFields_prependRecursive, applyIhs_prependRecursive]
  rw [hfields, hihs]

end CtorCode

end Metalean
