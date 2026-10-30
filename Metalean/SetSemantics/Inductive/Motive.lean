/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Meta.ZF
public import Metalean.SetTheory.ZFC.Aczel.Spine
public import Metalean.SetTheory.ZFC.Erasure

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {count level sortCode arity : Nat} {arities : Fin count → Nat}
  {vms : Fin count → ZFSet} {motive block entry value : ZFSet}

def sortPart (sortCode : Nat) (block : ZFSet) : ZFSet :=
  block.sep fun entry => [zf|(entry.1).1] = numeral sortCode

noncomputable def motiveAt (level arity : Nat) (motive entry : ZFSet) : ZFSet :=
  [zf|$(Aczel.appTuple motive [zf|(entry.1).2] arity) $(propVal level [zf|entry.2])]

noncomputable def motivePart (level sortCode arity : Nat)
    (motive block : ZFSet) : ZFSet :=
  σ (sortPart sortCode block)
    (map (motiveAt level arity motive) (sortPart sortCode block))

noncomputable def motiveDomain (level : Nat) (block : ZFSet) : ZFSet :=
  block ∪ image (fun entry => [zf|(entry.1, $(propVal level [zf|entry.2]))]) block

theorem mem_motiveDomain_entry (hentry : entry ∈ block) :
    entry ∈ motiveDomain level block :=
  mem_union.mpr (.inl hentry)

theorem mem_motiveDomain_value (hentry : entry ∈ block) :
    [zf|(entry.1, $(propVal level [zf|entry.2]))] ∈ motiveDomain level block :=
  mem_union.mpr (.inr (mem_image.mpr ⟨entry, hentry, rfl⟩))

noncomputable def bundleMotive {count : Nat} (level : Nat)
    (arities : Fin count → Nat) (vms : Fin count → ZFSet.{u}) (block : ZFSet.{u}) : ZFSet.{u} :=
  ⋃ s, motivePart level s.val (arities s) (vms s) (motiveDomain level block)

theorem fibre_bundleMotive_of_mem (s : Fin count)
    (hentry : entry ∈ motiveDomain level block)
    (htag : [zf|(entry.1).1] = numeral s.val) :
    fibreOp (bundleMotive level arities vms block) entry =
      motiveAt level (arities s) (vms s) entry := by
  ext value
  rw [bundleMotive, fibre_iUnion]
  simp only [mem_iUnion, motivePart, mem_fibre_sigma_map, sortPart, mem_sep]
  constructor
  · rintro ⟨t, ⟨_, ht⟩, hv⟩
    have : t = s := Fin.ext (numeral_injective (ht.symm.trans htag))
    simpa [this] using hv
  · exact fun hv => ⟨s, ⟨hentry, htag⟩, hv⟩

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
  ext value
  rw [bundleMotive, fibre_iUnion, fibre_iUnion]
  simp only [mem_iUnion, motivePart, mem_fibre_sigma_map, sortPart, mem_sep]
  apply exists_congr
  intro s
  have h₁ := mem_motiveDomain_entry (level := level) hentry
  have h₂ := mem_motiveDomain_value (level := level) hentry
  cases level <;> simp_all [motiveAt]

theorem fibre_bundleMotive_typed {count level : Nat}
    {arities : Fin count → Nat} {vms : Fin count → ZFSet}
    {block value : ZFSet} (s : Fin count)
    (vis : Fin (arities s) → ZFSet)
    (hvalue : value ∈ propSet level
      (fibreOp block (sortKey s.val (encode vis)))) :
    fibreOp (bundleMotive level arities vms block)
        (pair (sortKey s.val (encode vis)) value) =
      [zf|$(vms s) vis... value] := by
  let carrier := fibreOp block (sortKey s.val (encode vis))
  let raw := propGet level carrier value
  have hraw : raw ∈ carrier := propGet_mem hvalue
  have hval : propVal level raw = value := propVal_propGet hvalue
  have hvalueEq : propVal level value = value := by
    cases level with
    | zero =>
      rw [propSet_zero, mem_squash] at hvalue
      have ⟨_, _, heq⟩ := hvalue
      simpa using heq.symm
    | succ level => simp
  have hentry : pair (sortKey s.val (encode vis)) raw ∈ block :=
    mem_fibre.mp hraw
  have htag : fst (fst (pair (sortKey s.val (encode vis)) raw)) =
      numeral s.val := by
    simp [sortKey, encode]
  have his : snd (sortKey s.val (encode vis)) = encode vis := by
    simp [sortKey, encode]
  simpa [motiveAt, his, Aczel.appTuple_encode, hval, hvalueEq] using
    fibre_bundleMotive_value (level := level) (arities := arities) s hentry htag

end Metalean
