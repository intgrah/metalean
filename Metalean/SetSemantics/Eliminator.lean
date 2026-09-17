/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.InductiveBlock
public import Metalean.SetTheory.ZFC.Accessibility
import Metalean.Fin

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {n : Nat}

section

variable {count level sortCode arity : Nat} {arities : Fin count → Nat}
  {vms : Fin count → ZFSet} {motive block entry value : ZFSet}

noncomputable def appTuple : Nat → ZFSet → ZFSet → ZFSet
  | 0, f, _ => f
  | k + 1, f, values => [zf|$(appTuple k f [zf|values.1]) values.2]

def sortPart (sortCode : Nat) (block : ZFSet) : ZFSet :=
  block.sep fun entry => [zf|(entry.1).1] = numeral sortCode

noncomputable def motiveAt (level arity : Nat) (motive entry : ZFSet) : ZFSet :=
  [zf|$(appTuple arity motive [zf|(entry.1).2]) $(propVal level [zf|entry.2])]

noncomputable def motivePart (level sortCode arity : Nat)
    (motive block : ZFSet) : ZFSet :=
  σ (sortPart sortCode block)
    (map (motiveAt level arity motive) (sortPart sortCode block))

theorem mem_fibre_motivePart :
    value ∈ fibreOp (motivePart level sortCode arity motive block) entry ↔
      entry ∈ sortPart sortCode block ∧ value ∈ motiveAt level arity motive entry := by
  rw [mem_fibre, motivePart]
  constructor
  · intro h
    have ⟨entry', hentry, value', hvalue, heq⟩ := mem_sigma.mp h
    have ⟨rfl, hvalueEq⟩ := pair_inj.mp heq
    rw [app_map hentry] at hvalue
    exact ⟨hentry, hvalueEq ▸ hvalue⟩
  · intro ⟨hentry, hvalue⟩
    refine mem_sigma.mpr ⟨entry, hentry, value, ?_, rfl⟩
    rwa [app_map hentry]

theorem fibre_motivePart (hentry : entry ∈ sortPart sortCode block) :
    fibreOp (motivePart level sortCode arity motive block) entry =
      motiveAt level arity motive entry :=
  ZFSet.ext fun _ => mem_fibre_motivePart.trans (and_iff_right hentry)

theorem fibre_motivePart_empty (hentry : entry ∉ sortPart sortCode block) :
    fibreOp (motivePart level sortCode arity motive block) entry = ∅ :=
  (eq_empty _).2 fun _ hvalue => hentry
    (mem_fibre_motivePart (level := level) (arity := arity)
      (motive := motive).mp hvalue).1

noncomputable def motiveDomain (level : Nat) (block : ZFSet) : ZFSet :=
  block ∪ image (fun entry => [zf|(entry.1, $(propVal level [zf|entry.2]))]) block

theorem mem_motiveDomain_entry (hentry : entry ∈ block) :
    entry ∈ motiveDomain level block :=
  mem_union.mpr (.inl hentry)

theorem mem_motiveDomain_value (hentry : entry ∈ block) :
    [zf|(entry.1, $(propVal level [zf|entry.2]))] ∈ motiveDomain level block :=
  mem_union.mpr (.inr (mem_image.mpr ⟨entry, hentry, rfl⟩))

noncomputable def bundleMotive : {count : Nat} → Nat →
    ((s : Fin count) → Nat) → (Fin count → ZFSet) → ZFSet → ZFSet
  | 0, _, _, _, _ => ∅
  | count + 1, level, arities, vms, block =>
    bundleMotive level (fun s => arities s.castSucc)
        (fun s => vms s.castSucc) block ∪
      motivePart level count (arities (Fin.last count))
        (vms (Fin.last count)) (motiveDomain level block)

theorem fibre_bundleMotive_empty (htags : ∀ s : Fin count, [zf|(entry.1).1] ≠ numeral s.val) :
    fibreOp (bundleMotive level arities vms block) entry = ∅ := by
  induction count with
  | zero => exact fibre_empty entry
  | succ count ih =>
    rw [bundleMotive, fibre_union,
      ih (arities := fun s => arities s.castSucc) (vms := fun s => vms s.castSucc)
        fun s => htags s.castSucc,
      fibre_motivePart_empty (sortCode := count)
        (arity := arities (Fin.last count))
        fun hentry => htags (Fin.last count) (mem_sep.mp hentry).2, union_empty]

theorem fibre_bundleMotive_of_mem (s : Fin count)
    (hentry : entry ∈ motiveDomain level block)
    (htag : [zf|(entry.1).1] = numeral s.val) :
    fibreOp (bundleMotive level arities vms block) entry =
      motiveAt level (arities s) (vms s) entry := by
  induction s using Fin.lastInduction with
  | last count =>
    rw [bundleMotive, fibre_union,
      fibre_bundleMotive_empty fun t heq =>
        Fin.castSucc_ne_last t (Fin.ext (numeral_injective (heq.symm.trans htag))),
      fibre_motivePart (sortCode := count) (mem_sep.mpr ⟨hentry, htag⟩), empty_union]
  | @cast count current ih =>
    rw [bundleMotive, fibre_union,
      ih htag,
      fibre_motivePart_empty fun hmem => current.isLt.ne
        (numeral_injective (htag.symm.trans (mem_sep.mp hmem).2)), union_empty]

theorem fibre_bundleMotive (s : Fin count) (hentry : entry ∈ block)
    (htag : [zf|(entry.1).1] = numeral s.val) :
    fibreOp (bundleMotive level arities vms block) entry =
      motiveAt level (arities s) (vms s) entry :=
  fibre_bundleMotive_of_mem s (mem_motiveDomain_entry hentry) htag

theorem fibre_bundleMotive_value (s : Fin count) (hentry : entry ∈ block)
    (htag : [zf|(entry.1).1] = numeral s.val) :
    fibreOp (bundleMotive level arities vms block)
        [zf|(entry.1, $(propVal level [zf|entry.2]))] =
      motiveAt level (arities s) (vms s)
        [zf|(entry.1, $(propVal level [zf|entry.2]))] := by
  apply fibre_bundleMotive_of_mem s (mem_motiveDomain_value hentry)
  simpa using htag

theorem fibre_bundleMotive_propVal (hentry : entry ∈ block) :
    fibreOp (bundleMotive level arities vms block) entry =
      fibreOp (bundleMotive level arities vms block) [zf|(entry.1, $(propVal level [zf|entry.2]))] := by
  induction count with
  | zero => rw [bundleMotive, fibre_empty, fibre_empty]
  | succ count ih =>
    rw [bundleMotive, fibre_union, fibre_union, ih]
    by_cases htag : [zf|(entry.1).1] = numeral count
    · have hvalue : [zf|(entry.1, $(propVal level [zf|entry.2]))] ∈ motiveDomain level block := by
        simpa using mem_motiveDomain_value hentry
      rw [fibre_motivePart
          (mem_sep.mpr ⟨mem_motiveDomain_entry hentry, htag⟩),
        fibre_motivePart
          (mem_sep.mpr ⟨hvalue, by simpa using htag⟩)]
      cases level <;> simp [motiveAt]
    · rw [fibre_motivePart_empty fun h => htag (mem_sep.mp h).2,
        fibre_motivePart_empty fun h => htag (by
          simpa using (mem_sep.mp h).2)]

noncomputable def minorFamily : {count : Nat} → Slots count → ZFSet
  | 0, _ => ∅
  | count + 1, vmins =>
    minorFamily (Fin.init vmins) ∪
      [zf|fun _ : $({numeral count}) => $(vmins (Fin.last count))]

theorem app_minorFamily_outside {count : Nat} (vmins : Slots count)
    (tag : Nat) (htag : count ≤ tag) :
    [zf|$(minorFamily vmins) $(numeral tag)] = ∅ := by
  induction vmins using Fin.snocInduction with
  | elim0 => simp [minorFamily, Aczel.app_empty]
  | snoc vmins vmin ih =>
    rw [minorFamily, Fin.init_snoc, Fin.snoc_last, app_union,
      ih (Nat.le_trans (Nat.le_succ _) htag),
      app_lam_singleton_ne (by
        intro heq
        have := numeral_injective heq
        omega), empty_union]

@[simp] theorem app_minorFamily {count : Nat} (vmins : Slots count)
    (tag : Fin count) :
    [zf|$(minorFamily vmins) $(numeral tag.val)] = vmins tag := by
  induction tag using Fin.lastInduction with
  | last count =>
    rw [minorFamily, Fin.val_last, app_union,
      app_minorFamily_outside (Fin.init vmins) count le_rfl,
      Aczel.app_lam (mem_singleton.mpr rfl), empty_union]
  | @cast count current ih =>
    rw [minorFamily, Fin.val_castSucc, app_union, ih,
      app_lam_singleton_ne (by
        intro heq
        have := numeral_injective heq
        omega), union_empty]
    rfl

end

end Metalean
