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

namespace CtorCode

variable {n : Nat} {code : CtorCode n} {block block₁ block₂ : ZFSet}

noncomputable def pack (block : ZFSet) (level : Nat) (code : CtorCode n)
    (γ : Slots n) (values : Slots code.nfields) (fields : Slots code.nrecFields) : ZFSet :=
  code.ordinary.pack (Fin.append γ values) (tuple fun f => recoverRecField (code.recursive f).tele
    (code.recursive f).index block level (Fin.append γ values) (fields f))

@[simp] theorem values_pack (code : CtorCode n) (block : ZFSet) (level : Nat)
    (γ : Slots n) (values : Slots code.nfields) (fields : Slots code.nrecFields) :
    code.ordinary.values γ (code.pack block level γ values fields) = Fin.append γ values := by
  have h := code.ordinary.values_pack (Fin.append γ values)
    (tuple fun f => recoverRecField (code.recursive f).tele (code.recursive f).index block level
      (Fin.append γ values) (fields f))
  have hbase : (fun base : Fin n => Fin.append γ values (base.castLE code.ordinary.le)) = γ :=
    funext fun base => Fin.append_left γ values base
  rwa [hbase] at h

theorem pack_mem {reach : Set (Slots n)} {γ : Slots n} {values : Slots code.nfields}
    {fields : Slots code.nrecFields} {level : Nat}
    (hfinal : Fin.append γ values ∈ Reachable reach code.ordinary)
    (hfields : ∀ f, fields f ∈ typedRecFieldSet
      (code.recursive f).tele (code.recursive f).index block level (Fin.append γ values)) :
    code.pack block level γ values fields ∈ code.argSet block γ := by
  have h := SemTele.pack_mem
    (leaf := fun final => tupleSet fun f =>
      recFieldSet (code.recursive f).tele (code.recursive f).index block final)
    hfinal (tuple_mem_tupleSet fun f => recoverRecField_mem _ _ (hfields f))
  have hbase : (fun base : Fin n => Fin.append γ values (base.castLE code.ordinary.le)) = γ :=
    funext fun base => Fin.append_left γ values base
  rw [hbase] at h
  exact h

theorem applyMinor_pack (code : CtorCode n) (block graph : ZFSet) (level : Nat)
    (γ : Slots n) (values : Slots code.nfields) (fields : Slots code.nrecFields)
    (hfields : ∀ f, fields f ∈ typedRecFieldSet
      (code.recursive f).tele (code.recursive f).index block level (Fin.append γ values))
    (minor : ZFSet) :
    code.applyMinor level graph γ minor (code.pack block level γ values fields) =
      [zf|minor values... fields...
        $(fun f => recMap (code.recursive f).tele (code.recursive f).index graph (Fin.append γ values)
          (recoverRecField (code.recursive f).tele (code.recursive f).index block level
            (Fin.append γ values) (fields f)))...] := by
  simp only [applyMinor, values_pack]
  simp only [pack, SemTele.tail_pack, tupleValues_tuple, SemTele.app_eq_apps, Fin.append_right]
  congr 2
  funext f
  exact eraseRecField_recoverRecField _ _ _ _ _ (hfields f)

theorem pack_erase (code : CtorCode n) {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ code.argSet block γ) (level tag : Nat) :
    propVal level (entryValue tag (code.pack block level γ
      (fun f => code.ordinary.values γ vargs (Fin.natAdd n f))
      (fun f => eraseRecField (code.recursive f).tele level (code.ordinary.values γ vargs)
        (tupleValues code.nrecFields (code.ordinary.tail vargs) f)))) =
      propVal level (entryValue tag vargs) := by
  obtain ⟨_, htail, hpack⟩ := SemTele.mem_sigma.mp hargs
  obtain ⟨hfields, htuple⟩ := mem_tupleSet.mp htail
  cases level with
  | zero => simp
  | succ level =>
    have hvalues : (fun f => recoverRecField (code.recursive f).tele (code.recursive f).index
        block (level + 1) (code.ordinary.values γ vargs)
        (eraseRecField (code.recursive f).tele (level + 1) (code.ordinary.values γ vargs)
          (tupleValues code.nrecFields (code.ordinary.tail vargs) f))) =
        tupleValues code.nrecFields (code.ordinary.tail vargs) := by
      funext f
      rw [eraseRecField_of_ne_zero (Nat.succ_ne_zero level) _ _ _ _ _ (hfields f),
        recoverRecField_of_ne_zero (Nat.succ_ne_zero level) _ _ _ _ _ (hfields f)]
    simp [pack, ← code.ordinary.values_eq_append γ vargs, hvalues, htuple, hpack]

theorem applyMinor_zero_congr (code : CtorCode n)
    {γ : Slots n} {left right graph : ZFSet}
    (hgraph : ∀ key value₁ value₂,
      pair key value₁ ∈ block₁ → pair key value₂ ∈ block₂ →
      app graph (pair key value₁) = app graph (pair key value₂))
    (hleft : left ∈ code.argSet block₁ γ) (hright : right ∈ code.argSet block₂ γ)
    (hordinary : code.ordinary.values γ left = code.ordinary.values γ right)
    (minor : ZFSet) :
    code.applyMinor 0 graph γ minor left = code.applyMinor 0 graph γ minor right := by
  have hl := (mem_tupleSet.mp (SemTele.mem_sigma.mp hleft).2.1).1
  have hr := (mem_tupleSet.mp (SemTele.mem_sigma.mp hright).2.1).1
  rw [hordinary] at hl
  dsimp only [applyMinor]
  rw [hordinary]
  have hfields : (fun f => eraseRecField (code.recursive f).tele 0 (code.ordinary.values γ right)
      (tupleValues code.nrecFields (code.ordinary.tail left) f)) =
      fun f => eraseRecField (code.recursive f).tele 0 (code.ordinary.values γ right)
        (tupleValues code.nrecFields (code.ordinary.tail right) f) :=
    funext fun f => eraseRecField_zero_eq _ _ _ _ _ _ (hl f) (hr f)
  rw [hfields]
  congr 1
  funext f
  apply (code.recursive f).tele.lamAt_ext
  exact fun final hfinal => hgraph _ _ _
    (mem_fibre.mp (Reachable.app_mem hfinal (hl f)))
    (mem_fibre.mp (Reachable.app_mem hfinal (hr f)))

end CtorCode

end Metalean
