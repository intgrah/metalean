/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.VonNeumann
public import Metalean.SetTheory.Cardinal.Inaccessible

public section

universe u

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

@[expose] def SmallOver (Λ X : ZFSet) : Prop :=
  ∃ i ∈ Λ, ∃ g : ZFSet → ZFSet, X ⊆ image g i

theorem exists_closed_of_indexed_support {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {Φ : ZFSet.{u} → ZFSet.{u}} (hmono : Monotone Φ)
    (hΦ : ∀ X, X ∈ V_ κ.ord → Φ X ∈ V_ κ.ord)
    {ι : Type*} [Small.{u} ι] (hι : Cardinal.mk (Shrink.{u} ι) < κ)
    (hsupp : ∀ X z, z ∈ Φ X →
      ∃ X₀, X₀ ⊆ X ∧ (∃ g : ι → ZFSet, X₀ ⊆ range g) ∧ z ∈ Φ X₀) :
    ∃ W, W ∈ V_ κ.ord ∧ Φ W ⊆ W := by
  classical
  let β : ULift.{u} Bool → Type u := fun b => if b.down then Shrink.{u} ι else PEmpty
  have hβ (b : ULift.{u} Bool) : Cardinal.mk (β b) < κ := by
    cases b with
    | up b =>
      cases b with
      | false => simpa [β] using hκ.pos
      | true => exact hι
  have htrees : Cardinal.mk (WType β) < κ :=
    hκ.wType_lt (α := ULift.{u} Bool) (β := β)
      (by simpa [Cardinal.mk_fintype] using hκ.nat_lt 2) hβ
  have hrange {ι : Type u} (f : ι → ZFSet.{u}) (hι : Cardinal.mk ι < κ)
      (hf : ∀ i, f i ∈ V_ κ.ord) : range f ∈ V_ κ.ord :=
    range_mem_vonNeumann (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le)
      (by simpa [hκ.isRegular.cof_ord] using hι) hf
  let stage : WType β → ZFSet.{u} := WType.elim _ fun p =>
    let X := ⋃₀ range p.2
    X ∪ Φ X
  have hstage (t : WType β) : stage t ∈ V_ κ.ord := by
    induction t with
    | mk b children ih =>
      have hX := sUnion_mem_vonNeumann (hrange _ (hβ b) ih)
      exact union_mem_vonNeumann hX (hΦ _ hX)
  refine ⟨⋃₀ range stage, sUnion_mem_vonNeumann (hrange stage htrees hstage), ?_⟩
  intro z hz
  obtain ⟨X₀, hX₀W, ⟨g, hX₀g⟩, hz⟩ := hsupp _ z hz
  have hnext (j : ι) : ∃ t : WType β, g j ∈ X₀ → g j ∈ stage t := by
    by_cases hj : g j ∈ X₀
    · obtain ⟨Y, hY, hgj⟩ := mem_sUnion.mp (hX₀W hj)
      obtain ⟨t, rfl⟩ := mem_range.mp hY
      exact ⟨t, fun _ => hgj⟩
    · exact ⟨.mk ⟨false⟩ PEmpty.elim, fun h => (hj h).elim⟩
  let children : Shrink.{u} ι → WType β := fun j =>
    Classical.choose (hnext ((equivShrink ι).symm j))
  have hX₀ : X₀ ⊆ ⋃₀ range (fun j => stage (children j)) := by
    intro x hx
    obtain ⟨j, rfl⟩ := mem_range.mp (hX₀g hx)
    refine mem_sUnion.mpr ⟨_, mem_range_self (f := fun j => stage (children j))
      (equivShrink ι j), ?_⟩
    simpa [children] using Classical.choose_spec (hnext j) hx
  have hzstage : z ∈ stage (.mk ⟨true⟩ children) :=
    mem_union.mpr (.inr (hmono hX₀ hz))
  exact mem_sUnion.mpr ⟨_, mem_range_self (f := stage) (.mk ⟨true⟩ children), hzstage⟩

theorem exists_closed_of_smallSupport {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {Φ : ZFSet.{u} → ZFSet.{u}} (hmono : Monotone Φ)
    (hΦ : ∀ X, X ∈ V_ κ.ord → Φ X ∈ V_ κ.ord)
    {Λ : ZFSet.{u}} (hΛ : Λ ∈ V_ κ.ord)
    (hsupp : ∀ X z, z ∈ Φ X → ∃ X₀, X₀ ⊆ X ∧ SmallOver Λ X₀ ∧ z ∈ Φ X₀) :
    ∃ W, W ∈ V_ κ.ord ∧ Φ W ⊆ W := by
  refine exists_closed_of_indexed_support hκ hmono hΦ
    (ι := ⋃₀ Λ) (card_lt_of_mem_vonNeumann hκ (sUnion_mem_vonNeumann hΛ)) ?_
  intro X z hz
  obtain ⟨X₀, hX₀, ⟨i, hi, g, hg⟩, hz⟩ := hsupp X z hz
  refine ⟨X₀, hX₀, ⟨fun j => g j.1, ?_⟩, hz⟩
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_image.mp (hg hx)
  exact mem_range.mpr ⟨⟨j, mem_sUnion.mpr ⟨i, hi, hj⟩⟩, rfl⟩

end ZFSet
