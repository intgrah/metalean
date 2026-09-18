/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Order.Presheaf.Lower

@[expose] public section

universe u v w

namespace Metalean.Presheaf

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C]

structure PartialDomain (X : C) where
  Witness {Y : C} : (Y ⟶ X) → Type w
  pullback {Y Z : C} {f : Y ⟶ X} : Witness f → (g : Z ⟶ Y) → Witness (g ≫ f)

structure PartialSection (R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}) {X : C}
    (D : PartialDomain.{u, v, w} X) where
  value {Y : C} (f : Y ⟶ X) : D.Witness f → ΩLower R Y
  natural {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (s : D.Witness f)
    (t : D.Witness (g ≫ f)) : (value f s).pullback g = value (g ≫ f) t

namespace PartialSection

variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X Y : C} {D : PartialDomain.{u, v, w} X}

def extend (F : PartialSection R D) : ΩLower R X where
  mem f a := a ≤ ⊥ ∨ ∃ s, (F.value f s).mem (𝟙 _) a
  natural f g a
    | .inl ha => .inl ((R.map g.op).map_le_bot ha)
    | .inr ⟨s, ha⟩ => .inr ⟨D.pullback s g, by
        rw [← F.natural f g s]
        exact (ΩLower.presheaf_map_mem_id _ _ _).mpr
          (by simpa using (F.value f s).natural (𝟙 _) g a ha)⟩
  bottom _ := .inl le_rfl
  lower f hab
    | .inl hb => .inl (hab.trans hb)
    | .inr ⟨s, hb⟩ => .inr ⟨s, (F.value f s).lower (𝟙 _) hab hb⟩

@[simp] theorem mem_extend (F : PartialSection R D) (f : Y ⟶ X) (a : R.obj (op Y)) :
    F.extend.mem f a ↔ a ≤ ⊥ ∨ ∃ s, (F.value f s).mem (𝟙 _) a := Iff.rfl

theorem pullback_extend (F : PartialSection R D) (f : Y ⟶ X) (s : D.Witness f) :
    F.extend.pullback f = F.value f s := by
  ext Z g a
  rw [ΩLower.presheaf_map_mem, mem_extend]
  constructor
  · intro
    | .inl ha => exact (F.value f s).lower g ha ((F.value f s).bottom g)
    | .inr ⟨t, ha⟩ =>
      rw [← F.natural f g s t] at ha
      exact (ΩLower.presheaf_map_mem_id _ _ _).mp ha
  · intro ha
    refine .inr ⟨D.pullback s g, ?_⟩
    rw [← F.natural f g s]
    exact (ΩLower.presheaf_map_mem_id _ _ _).mpr ha

theorem extend_le_iff (F : PartialSection R D) (L : ΩLower R X) :
    F.extend ≤ L ↔ ∀ {Y} (f : Y ⟶ X) (s : D.Witness f), F.value f s ≤ L.pullback f := by
  constructor
  · intro h Y f s
    rw [← F.pullback_extend f s]
    exact ΩLower.pullback_mono h f
  · intro h Y f a ha
    rcases ha with ha | ⟨s, ha⟩
    · exact L.lower f ha (L.bottom f)
    · exact (ΩLower.presheaf_map_mem_id _ _ _).mp (h f s (𝟙 _) a ha)

theorem extend_mono {F G : PartialSection R D}
    (h : ∀ {Y} (f : Y ⟶ X) (s : D.Witness f), F.value f s ≤ G.value f s) :
    F.extend ≤ G.extend :=
  (F.extend_le_iff G.extend).mpr fun f s => by rw [G.pullback_extend f s]; exact h f s

theorem support (F : PartialSection R D) {f : Y ⟶ X} {a : R.obj (op Y)}
    (ha : F.extend.mem f a) (hne : ¬ a ≤ ⊥) : Nonempty (D.Witness f) := by
  rcases ha with ha | ⟨s, _⟩
  · exact (hne ha).elim
  · exact ⟨s⟩

theorem eq_extend (F : PartialSection R D) (L : ΩLower R X)
    (hs : ∀ {Y} (f : Y ⟶ X) (a : R.obj (op Y)),
      L.mem f a → ¬ a ≤ ⊥ → Nonempty (D.Witness f))
    (hv : ∀ {Y} (f : Y ⟶ X) (s : D.Witness f), L.pullback f = F.value f s) :
    L = F.extend := by
  apply le_antisymm
  · intro Y f a ha
    by_cases hbot : a ≤ ⊥
    · exact .inl hbot
    · have ⟨s⟩ := hs f a ha hbot
      refine .inr ⟨s, ?_⟩
      rw [← hv f s]
      exact (ΩLower.presheaf_map_mem_id _ _ _).mpr ha
  · apply (F.extend_le_iff L).mpr
    intro Y f s
    rw [hv f s]

theorem isDirected (F : PartialSection R D)
    (h : ∀ {Y} (f : Y ⟶ X) (s : D.Witness f), (F.value f s).IsDirected) :
    F.extend.IsDirected := by
  intro Y f a b ha hb
  rcases ha with ha | ⟨s, ha⟩
  · exact ⟨b, hb, ha.trans bot_le, le_rfl⟩
  · have hb' := (ΩLower.presheaf_map_mem_id F.extend f b).mpr hb
    rw [F.pullback_extend f s] at hb'
    have ⟨c, hc, hac, hbc⟩ := h f s (𝟙 _) ha hb'
    exact ⟨c, .inr ⟨s, hc⟩, hac, hbc⟩

end PartialSection

end Metalean.Presheaf
