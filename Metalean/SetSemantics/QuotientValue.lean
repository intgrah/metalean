/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Quotient
public import Metalean.SetTheory.ZFC.Universe.Sort
import Metalean.SetTheory.ZFC.Erasure

public section

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

@[expose] noncomputable def quotientArrow (α β : ZFSet) : ZFSet := [zf|α → β]

@[expose] noncomputable def quotientProp : ZFSet := S_ 0

@[expose] noncomputable def quotientRel (α : ZFSet) : ZFSet := [zf|α → α → quotientProp]

@[expose] noncomputable def quotientCompat (equality : ZFSet → ZFSet → ZFSet → ZFSet)
    (α r β fn : ZFSet) : ZFSet :=
  [zf|(a₁ a₂ : α) → r a₁ a₂ → $(equality β [zf|fn a₁] [zf|fn a₂])]

@[expose] def EqualitySeparates (n : Nat) (equality : ZFSet → ZFSet → ZFSet → ZFSet) : Prop :=
  ∀ β ∈ S_ n, ∀ b₁ ∈ β, ∀ b₂ ∈ β, ∀ w, w ∈ equality β b₁ b₂ → b₁ = b₂

theorem quotientCompat_respects {n : Nat} {equality : ZFSet → ZFSet → ZFSet → ZFSet}
    {α r β fn h : ZFSet}
    (hseparates : EqualitySeparates n equality) (hb : β ∈ S_ n)
    (hf : fn ∈ quotientArrow α β)
    (hh : h ∈ quotientCompat equality α r β fn) :
    ∀ a₁ ∈ α, ∀ a₂ ∈ α, [zf|r a₁ a₂] = verum → [zf|fn a₁] = [zf|fn a₂] := by
  intro a₁ hx a₂ hy hr
  have hfx := Aczel.app_mem hf hx
  have hfy := Aczel.app_mem hf hy
  rw [app_map hx] at hfx
  rw [app_map hy] at hfy
  have hhx := Aczel.app_mem hh hx
  rw [app_map hx] at hhx
  have hhxy := Aczel.app_mem hhx hy
  rw [app_map hy] at hhxy
  have hhrel := Aczel.app_mem hhxy (hr ▸ proof_mem_verum)
  rw [app_map (hr ▸ proof_mem_verum)] at hhrel
  exact hseparates β hb _ hfx _ hfy _ hhrel

noncomputable abbrev quotientClass (n : Nat) (α r a : ZFSet) : ZFSet :=
  equivClosure α (U_ (n - 1)) r a

noncomputable abbrev quotientClasses (n : Nat) (α r : ZFSet) : ZFSet := quotient α (U_ (n - 1)) r

noncomputable def quotientCarrier (n : Nat) (α r : ZFSet) : ZFSet :=
  propSet n (quotientClasses n α r)

noncomputable def quotientMk (n : Nat) (α r a : ZFSet) : ZFSet :=
  propVal n (quotientClass n α r a)

private theorem mem_type_pred {n : Nat} {α : ZFSet} (ha : α ∈ S_ n) : α ∈ U_ (n - 1) := by
  match n with
  | 0 => exact mem_type_of_mem_sort (by decide) ha
  | _ + 1 => exact ha

private theorem subset_type_pred {n : Nat} {α : ZFSet} (ha : α ∈ S_ n) : α ⊆ U_ (n - 1) :=
  fun _ hx => mem_type_of_mem (mem_type_pred ha) hx

theorem quotientClass_eq_of_rel {n : Nat} {α r a₁ a₂ : ZFSet}
    (ha : α ∈ S_ n) (hx : a₁ ∈ α) (hy : a₂ ∈ α)
    (hr : [zf|r a₁ a₂] = verum) :
    quotientClass n α r a₁ = quotientClass n α r a₂ :=
  equivClosure_eq_of_rel (subset_type_pred ha) hx hy hr

theorem quotientMk_eq_of_rel {n : Nat} {α r a₁ a₂ : ZFSet}
    (ha : α ∈ S_ n) (hx : a₁ ∈ α) (hy : a₂ ∈ α)
    (hr : [zf|r a₁ a₂] = verum) :
    quotientMk n α r a₁ = quotientMk n α r a₂ := by
  simp [quotientMk, quotientClass_eq_of_rel ha hx hy hr]

theorem quotientMk_mem {n : Nat} {α r a : ZFSet} (hx : a ∈ α) :
    quotientMk n α r a ∈ quotientCarrier n α r :=
  propVal_mem_propSet (mem_quotient.mpr ⟨a, hx, rfl⟩)

theorem quotientCarrier_mem_sort {n : Nat} {α r : ZFSet} (ha : α ∈ S_ n) :
    quotientCarrier n α r ∈ S_ n := by
  match n with
  | 0 => exact squash_mem_truth _
  | k + 1 =>
    change propSet (k + 1) _ ∈ _
    rw [propSet_succ]
    exact image_mem_type (mem_type_pred ha) fun _ hx =>
      mem_type_of_mem (powerset_mem_type (mem_type_pred ha))
        (ZFSet.mem_powerset.mpr (equivClosure_subset (subset_type_pred ha) hx))

theorem quotientCarrier_zero {α r : ZFSet} (ha : α ∈ S_ 0) : quotientCarrier 0 α r = α := by
  rw [quotientCarrier, propSet_zero]
  rcases mem_truth.mp ha with rfl | rfl
  · rw [show quotientClasses 0 falsum r = falsum from
      (ZFSet.eq_empty _).mpr fun _ h => by
        simpa [falsum] using (mem_quotient.mp h).choose_spec.1,
      squash_falsum]
  · exact squash_eq_verum
      (mem_quotient.mpr ⟨proof, proof_mem_verum, rfl⟩)

theorem quotientMk_zero {α r a : ZFSet} (ha : α ∈ S_ 0) (hx : a ∈ α) :
    quotientMk 0 α r a = a := by
  simp [quotientMk, ← mem_verum.mp (eq_verum_of_mem ha hx ▸ hx)]

theorem quotientCarrier_representation {n : Nat} {α r c : ZFSet}
    (ha : α ∈ S_ n) (hc : c ∈ quotientCarrier n α r) :
    ∃ a ∈ α, c = quotientMk n α r a := by
  match n with
  | 0 =>
    rw [quotientCarrier_zero ha] at hc
    exact ⟨c, hc, (quotientMk_zero ha hc).symm⟩
  | k + 1 =>
    rw [quotientCarrier, propSet_succ] at hc
    have ⟨a, hx, hc⟩ := mem_quotient.mp hc
    exact ⟨a, hx, by simpa [quotientMk, quotientClass] using hc⟩

noncomputable def quotientLift (n : Nat) (fn c : ZFSet) : ZFSet :=
  if n = 0 then [zf|fn c] else ZFSet.quotientLift fn c

theorem quotientLift_mk {n : Nat} {α r fn a : ZFSet} (ha : α ∈ S_ n)
    (hcompat : ∀ a₁ ∈ α, ∀ a₂ ∈ α, [zf|r a₁ a₂] = verum → [zf|fn a₁] = [zf|fn a₂])
    (hx : a ∈ α) :
    quotientLift n fn (quotientMk n α r a) = [zf|fn a] := by
  match n with
  | 0 => simp [quotientLift, quotientMk_zero ha hx]
  | k + 1 =>
    simp [quotientLift, quotientMk]
    exact quotientLift_equivClosure (subset_type_pred ha) hx hcompat

theorem quotientLift_mem {n : Nat} {α r β fn c : ZFSet}
    (ha : α ∈ S_ n) (hf : fn ∈ quotientArrow α β)
    (hcompat : ∀ a₁ ∈ α, ∀ a₂ ∈ α, [zf|r a₁ a₂] = verum → [zf|fn a₁] = [zf|fn a₂])
    (hc : c ∈ quotientCarrier n α r) :
    quotientLift n fn c ∈ β := by
  match n with
  | 0 =>
    rw [quotientCarrier_zero ha] at hc
    rw [quotientLift, ite_eq_left rfl]
    have h := Aczel.app_mem hf hc
    rwa [app_map hc] at h
  | k + 1 =>
    rw [quotientCarrier, propSet_succ] at hc
    rw [quotientLift, ite_eq_right (Nat.succ_ne_zero k)]
    have ⟨a, hx, hc⟩ := mem_quotient.mp hc
    rw [hc, quotientLift_equivClosure (subset_type_pred ha) hx hcompat]
    have h := Aczel.app_mem hf hx
    rwa [app_map hx] at h

noncomputable def quotientLiftResult (n m : Nat) (fn c : ZFSet) : ZFSet :=
  propVal m (quotientLift n fn c)

theorem quotientIndResult_mem {n : Nat} {α r motive minor c : ZFSet} (ha : α ∈ S_ n)
    (hmotive : motive ∈ quotientArrow (quotientCarrier n α r) quotientProp)
    (hminor : minor ∈ [zf|(a : α) → motive $(quotientMk n α r a)])
    (hc : c ∈ quotientCarrier n α r) :
    proof ∈ [zf|motive c] := by
  have ⟨a, hx, hc⟩ := quotientCarrier_representation ha hc
  have hminorApp := Aczel.app_mem hminor hx
  rw [app_map hx] at hminorApp
  have hmotiveApp := Aczel.app_mem hmotive (quotientMk_mem hx)
  rw [app_map (quotientMk_mem hx)] at hmotiveApp
  rw [hc, eq_verum_of_mem hmotiveApp hminorApp]
  exact proof_mem_verum

theorem quotientLiftResult_mem {n m : Nat} {equality : ZFSet → ZFSet → ZFSet → ZFSet}
    {α r β fn h c : ZFSet}
    (hseparates : EqualitySeparates m equality)
    (ha : α ∈ S_ n) (hb : β ∈ S_ m)
    (hf : fn ∈ quotientArrow α β) (hh : h ∈ quotientCompat equality α r β fn)
    (hc : c ∈ quotientCarrier n α r) :
    quotientLiftResult n m fn c ∈ β := by
  match m with
  | 0 =>
    have ⟨a, hx, _⟩ := quotientCarrier_representation ha hc
    have hfx := Aczel.app_mem hf hx
    rw [app_map hx] at hfx
    rw [quotientLiftResult, propVal_zero, eq_verum_of_mem hb hfx]
    exact proof_mem_verum
  | k + 1 =>
    rw [quotientLiftResult, propVal_succ]
    exact quotientLift_mem ha hf (quotientCompat_respects hseparates hb hf hh) hc

theorem quotientLiftResult_mk {n m : Nat} {equality : ZFSet → ZFSet → ZFSet → ZFSet}
    {α r β fn h a : ZFSet}
    (hseparates : EqualitySeparates m equality)
    (ha : α ∈ S_ n) (hb : β ∈ S_ m)
    (hf : fn ∈ quotientArrow α β) (hh : h ∈ quotientCompat equality α r β fn)
    (hx : a ∈ α) :
    quotientLiftResult n m fn (quotientMk n α r a) = [zf|fn a] := by
  match m with
  | 0 =>
    have hleft := quotientLiftResult_mem hseparates ha hb hf hh (quotientMk_mem hx)
    have hright := Aczel.app_mem hf hx
    rw [app_map hx] at hright
    exact (mem_verum.mp (eq_verum_of_mem hb hleft ▸ hleft)).trans
      (mem_verum.mp (eq_verum_of_mem hb hright ▸ hright)).symm
  | k + 1 =>
    rw [quotientLiftResult, propVal_succ]
    exact quotientLift_mk ha (quotientCompat_respects hseparates hb hf hh) hx

end Metalean
