/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Meta.ZF
public import Metalean.SetTheory.ZFC.Aczel
public import Metalean.SetTheory.ZFC.FixedPoint

@[expose] public noncomputable section

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {α r a c t : ZFSet}

def accOp (α r s : ZFSet) : ZFSet :=
  α.sep fun a => ∀ b ∈ α, pair b a ∈ r → b ∈ s

def accSet (α r : ZFSet) : ZFSet := lfp α (accOp α r)

theorem accOp_mapsTo (α r : ZFSet) :
    Set.MapsTo (accOp α r) (Set.Iic α) (Set.Iic α) :=
  fun _ _ _ hz => (mem_sep.mp hz).1

theorem monotoneOn_accOp (α r : ZFSet) : MonotoneOn (accOp α r) (Set.Iic α) :=
  fun _ _ _ _ hXY _ hz =>
    have ⟨h₁, h₂⟩ := mem_sep.mp hz
    mem_sep.mpr ⟨h₁, fun b hy hr => hXY (h₂ b hy hr)⟩

theorem accSet_subset : accSet α r ⊆ α := lfp_subset

theorem accSet_intro (hx : a ∈ α)
    (h : ∀ b ∈ α, pair b a ∈ r → b ∈ accSet α r) : a ∈ accSet α r :=
  lfp_closed (accOp_mapsTo α r) (monotoneOn_accOp α r) (mem_sep.mpr ⟨hx, h⟩)

theorem accSet_inv (hx : a ∈ accSet α r) : ∀ b ∈ α, pair b a ∈ r → b ∈ accSet α r :=
  (mem_sep.mp (lfp_unfold (accOp_mapsTo α r) (monotoneOn_accOp α r) hx)).2

theorem accSet_induction {p : ZFSet → Prop}
    (step : ∀ a ∈ accSet α r, (∀ b ∈ accSet α r, pair b a ∈ r → p b) → p a) :
    ∀ a ∈ accSet α r, p a := by
  have key : accSet α r ⊆ (accSet α r).sep p := by
    refine lfp_least (fun _ hz => accSet_subset (mem_sep.mp hz).1) fun c hz => ?_
    have ⟨hzA, hzy⟩ := mem_sep.mp hz
    have hacc : c ∈ accSet α r :=
      accSet_intro hzA fun b hy hr => (mem_sep.mp (hzy b hy hr)).1
    exact mem_sep.mpr ⟨hacc, step c hacc fun b hy hr =>
      (mem_sep.mp (hzy b (accSet_subset hy) hr)).2⟩
  exact fun _ hx => (mem_sep.mp (key hx)).2

theorem app_union (f g a : ZFSet) : [zf|$(f ∪ g) a] = [zf|f a] ∪ [zf|g a] := by
  ext c
  rw [Aczel.mem_app, mem_union, Aczel.mem_app, Aczel.mem_app]
  constructor
  · intro ⟨p, hp, h₁, h₂⟩
    rcases mem_union.mp hp with h | h
    · exact .inl ⟨p, h, h₁, h₂⟩
    · exact .inr ⟨p, h, h₁, h₂⟩
  · rintro (⟨p, hp, h₁, h₂⟩ | ⟨p, hp, h₁, h₂⟩)
    · exact ⟨p, mem_union.mpr (.inl hp), h₁, h₂⟩
    · exact ⟨p, mem_union.mpr (.inr hp), h₁, h₂⟩

theorem app_lam_singleton_ne (h : c ≠ a) :
    [zf|$([zf|fun _ : $({a}) => t]) c] = ∅ :=
  (eq_empty _).2 fun _ hw => by
    have ⟨p, hp, hfp, _⟩ := Aczel.mem_app.mp hw
    have ⟨input, hinput, b, _, hpk⟩ := Aczel.mem_lam.mp hp
    rw [hpk, fst_pair] at hfp
    exact h (by rw [← hfp]; exact mem_singleton.mp hinput)

end ZFSet
