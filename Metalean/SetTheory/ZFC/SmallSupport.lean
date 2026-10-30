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

theorem exists_closed_of_smallSupport {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {Φ : ZFSet.{u} → ZFSet.{u}} (hmono : Monotone Φ)
    (hΦ : ∀ X, X ∈ V_ κ.ord → Φ X ∈ V_ κ.ord)
    {Λ : ZFSet.{u}} (hΛ : Λ ∈ V_ κ.ord)
    (hsupp : ∀ X z, z ∈ Φ X → ∃ X₀, X₀ ⊆ X ∧ SmallOver Λ X₀ ∧ z ∈ Φ X₀) :
    ∃ W, W ∈ V_ κ.ord ∧ Φ W ⊆ W := by
  classical
  let T := ⋃₀ Λ
  let β : ULift.{u} Bool → Type u := fun b => if b.down then Shrink.{u} T else PEmpty
  have hT : T ∈ V_ κ.ord := sUnion_mem_vonNeumann hΛ
  have hβ (b : ULift.{u} Bool) : Cardinal.mk (β b) < κ := by
    cases b with
    | up b =>
      cases b with
      | false => simpa [β] using hκ.pos
      | true => exact card_lt_of_mem_vonNeumann hκ hT
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
  obtain ⟨X₀, hX₀W, ⟨i, hi, g, hX₀g⟩, hz⟩ := hsupp _ z hz
  have hnext (j : T) : ∃ t : WType β, g j.1 ∈ X₀ → g j.1 ∈ stage t := by
    by_cases hj : g j.1 ∈ X₀
    · obtain ⟨Y, hY, hgj⟩ := mem_sUnion.mp (hX₀W hj)
      obtain ⟨t, rfl⟩ := mem_range.mp hY
      exact ⟨t, fun _ => hgj⟩
    · exact ⟨.mk ⟨false⟩ PEmpty.elim, fun h => (hj h).elim⟩
  let children : Shrink.{u} T → WType β := fun j =>
    Classical.choose (hnext ((equivShrink T).symm j))
  have hX₀ : X₀ ⊆ ⋃₀ range (fun j => stage (children j)) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp (hX₀g hx)
    let jT : T := ⟨j, mem_sUnion.mpr ⟨i, hi, hj⟩⟩
    refine mem_sUnion.mpr ⟨_, mem_range_self (f := fun j => stage (children j))
      (equivShrink T jT), ?_⟩
    simpa [children] using Classical.choose_spec (hnext jT) hx
  have hzstage : z ∈ stage (.mk ⟨true⟩ children) :=
    mem_union.mpr (.inr (hmono hX₀ hz))
  exact mem_sUnion.mpr ⟨_, mem_range_self (f := stage) (.mk ⟨true⟩ children), hzstage⟩

end ZFSet
