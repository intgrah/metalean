/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Realization

public section

universe u

namespace Metalean

open ZFSet

namespace SemTele

variable {n b : Nat} {block : ZFSet}

theorem reachable_values {Δ : SemTele n b} {rest : CtorCode b}
    {reach : Set (Slots n)} {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ (CtorCode.prependOrdinary Δ rest).argSet block γ)
    (hγ : γ ∈ reach) :
    Δ.values γ vargs ∈ Reachable reach Δ := by
  induction Δ with
  | nil => exact .nil hγ
  | snoc Δ domain ih =>
    have ⟨_, _, hvalue, _, heq⟩ :=
      CtorCode.argSet_arg_inv (CtorCode.tail_mem_argSet hargs)
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
    refine ih hprefix (CtorCode.mem_argSet_arg hlast ?_)
    rwa [Fin.snoc_init_self]

end SemTele

namespace CtorCode

theorem mem_predecessors_packRecursive
    {n count level : Nat} (block : ZFSet)
    (fields : Fin count → CtorRecCode.Packed n) (index : Dom n)
    (γ : Slots n)
    (values : Fin count → ZFSet)
    (f : Fin count)
    (final : Slots (n + (fields f).1))
    (hfinal : final ∈ Reachable {γ} (fields f).2.tele) :
    pair ((fields f).2.index final)
        [zf|$(recoverRecField (fields f).2.tele (fields f).2.index block
            level γ (values f))
          $(fun argument => final (Fin.natAdd n argument))...] ∈
      (prependRecursive count fields (.target index)).predecessors γ
        (packRecursive block fields level γ values proof) := by
  induction f using Fin.succRecOn with
  | zero count =>
    simp [prependRecursive, packRecursive, predecessors]
    left
    apply Reachable.mem_collect hfinal
      (fun current value => {pair ((fields 0).2.index current) value})
      (recoverRecField (fields 0).2.tele (fields 0).2.index block level γ (values 0))
    simp
  | succ count f ih =>
    simp [prependRecursive, packRecursive, predecessors]
    right
    exact ih
      (fun current => fields current.succ)
      (fun current => values current.succ) final hfinal

end CtorCode

end Metalean
