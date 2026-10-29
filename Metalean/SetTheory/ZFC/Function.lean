/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.ZFC.Basic
import Metalean.Grind

@[expose] public section

universe u

namespace ZFSet

variable {a b c f α β : ZFSet.{u}}

attribute [local instance 2000] Classical.allZFSetDefinable

theorem mem_image' {op : ZFSet → ZFSet} {c α : ZFSet} :
    c ∈ image op α ↔ ∃ a ∈ α, c = op a :=
  mem_image.trans (exists_congr fun _ => and_congr_right fun _ => eq_comm)

theorem mem_sUnion_image {op : ZFSet → ZFSet} {c α : ZFSet} :
    c ∈ ⋃₀ image op α ↔ ∃ a ∈ α, c ∈ op a := by
  simp

open scoped Classical in
noncomputable def fst (p : ZFSet) : ZFSet :=
  if h : ∃ a b, p = pair a b then h.choose else ∅

open scoped Classical in
noncomputable def snd (p : ZFSet) : ZFSet :=
  if h : ∃ a b, p = pair a b then h.choose_spec.choose else ∅

@[simp] theorem fst_pair (a b : ZFSet) : fst (pair a b) = a := by
  let h : ∃ a₁ b₁, pair a b = pair a₁ b₁ := ⟨a, b, rfl⟩
  rw [fst, dite_eq_left h]
  have ⟨b, hb⟩ := h.choose_spec
  exact (pair_inj.mp hb).1.symm

@[simp] theorem snd_pair (a b : ZFSet) : snd (pair a b) = b := by
  let h : ∃ a₁ b₁, pair a b = pair a₁ b₁ := ⟨a, b, rfl⟩
  rw [snd, dite_eq_left h]
  exact (pair_inj.mp h.choose_spec.choose_spec).2.symm

noncomputable def dom (f : ZFSet) : ZFSet := image fst f

@[simp] theorem mem_dom : a ∈ dom f ↔ ∃ c ∈ f, a = fst c := mem_image'

theorem pair_mem_dom (h : pair a b ∈ f) : a ∈ dom f :=
  mem_dom.mpr ⟨pair a b, h, (fst_pair a b).symm⟩

theorem isFunc_dom_image_snd
    (hpair : ∀ c ∈ f, ∃ a b, c = pair a b)
    (huniq : ∀ a b₁ b₂, pair a b₁ ∈ f → pair a b₂ ∈ f → b₁ = b₂) :
    IsFunc (dom f) (image snd f) f := by
  constructor
  · intro c hc
    obtain ⟨a, b, rfl⟩ := hpair c hc
    exact pair_mem_prod.mpr ⟨pair_mem_dom hc,
      mem_image.mpr ⟨pair a b, hc, by simp⟩⟩
  · intro a₁ ha₁
    have ⟨c, hc, ha⟩ := mem_dom.mp ha₁
    obtain ⟨a₂, b₁, rfl⟩ := hpair c hc
    rw [fst_pair] at ha
    subst a₂
    exact ⟨b₁, hc, fun b₂ hb₂ => huniq a₁ b₂ b₁ hb₂ hc⟩

theorem isFunc_range_pair {ι : Type*} [Small.{u} ι] (key value : ι → ZFSet.{u})
    (hkey : Function.Injective key) :
    IsFunc (dom (range fun i => pair (key i) (value i)))
      (image snd (range fun i => pair (key i) (value i)))
      (range fun i => pair (key i) (value i)) := by
  refine isFunc_dom_image_snd ?_ ?_
  · intro p hp
    obtain ⟨i, rfl⟩ := mem_range.mp hp
    exact ⟨key i, value i, rfl⟩
  · intro x y₁ y₂ h₁ h₂
    have ⟨i, hi⟩ := mem_range.mp h₁
    have ⟨j, hj⟩ := mem_range.mp h₂
    have hi := pair_inj.mp hi
    have hj := pair_inj.mp hj
    cases hkey (hi.1.trans hj.1.symm)
    exact hi.2.symm.trans hj.2

def fibreOp (α a : ZFSet) : ZFSet :=
  (⋃₀ ⋃₀ α).sep fun b => pair a b ∈ α

@[simp] theorem mem_fibre : b ∈ fibreOp α a ↔ pair a b ∈ α := by
  rw [fibreOp, mem_sep]
  exact ⟨And.right, fun h => ⟨mem_sUnion.2 ⟨{a, b},
    mem_sUnion.2 ⟨pair a b, h, by simp [pair]⟩, by simp⟩, h⟩⟩

theorem fibre_mono {α β : ZFSet} (h : α ⊆ β) (a : ZFSet) :
    fibreOp α a ⊆ fibreOp β a :=
  fun _ hb => mem_fibre.mpr (h (mem_fibre.mp hb))

def app (f a : ZFSet) : ZFSet :=
  (⋃₀ ⋃₀ ⋃₀ f).sep fun c => ∃ b, pair a b ∈ f ∧ c ∈ b

@[simp] theorem mem_app : c ∈ app f a ↔ ∃ b, pair a b ∈ f ∧ c ∈ b := by
  rw [app, mem_sep]
  exact ⟨And.right, fun ⟨b, hab, hc⟩ => ⟨mem_sUnion.2 ⟨b, mem_sUnion.2 ⟨{a, b},
    mem_sUnion.2 ⟨pair a b, hab, by simp [pair]⟩, by simp⟩, hc⟩, b, hab, hc⟩⟩

noncomputable def σ (α β : ZFSet) : ZFSet :=
  (prod α (⋃₀ image (app β) α)).sep fun c =>
    ∃ a ∈ α, ∃ b ∈ app β a, c = pair a b

@[simp] theorem mem_sigma : c ∈ σ α β ↔ ∃ a ∈ α, ∃ b ∈ app β a, c = pair a b := by
  rw [σ, mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact mem_prod.2 ⟨a, ha, b, mem_sUnion.2 ⟨app β a, mem_image.2 ⟨a, ha, rfl⟩, hb⟩, rfl⟩

theorem IsFunc.app_eq (hf : IsFunc α β f) (hab : pair a b ∈ f) : app f a = b := by
  have ha := (pair_mem_prod.mp (hf.1 hab)).1
  have ⟨b₁, hb₁, huniq⟩ := hf.2 a ha
  ext c
  rw [mem_app]
  constructor
  · intro ⟨b₂, hb₂, hc⟩
    exact (huniq b₂ hb₂).trans (huniq b hab).symm ▸ hc
  · exact fun hc => ⟨b, hab, hc⟩

def IsPi (α β f : ZFSet) : Prop :=
  IsFunc α (⋃₀ image (app β) α) f ∧ f ⊆ σ α β

theorem IsPi.app_mem (hf : IsPi α β f) (ha : a ∈ α) : app f a ∈ app β a := by
  have ⟨b, hb, _⟩ := hf.1.2 a ha
  rw [hf.1.app_eq hb]
  have ⟨a₁, _, b₁, hb₁, hab⟩ := mem_sigma.mp (hf.2 hb)
  have h := pair_inj.mp hab
  simpa [h.1, h.2] using hb₁

noncomputable def pi (α β : ZFSet) : ZFSet :=
  (powerset (prod α (⋃₀ image (app β) α))).sep (IsPi α β)

@[simp] theorem mem_pi : f ∈ pi α β ↔ IsPi α β f := by
  rw [pi, mem_sep]
  exact ⟨And.right, fun h => ⟨mem_powerset.mpr h.1.1, h⟩⟩

@[zfBounds =] theorem app_map {op : ZFSet → ZFSet} (ha : a ∈ α) :
    app (map op α) a = op a := by
  ext c
  rw [mem_app]
  constructor
  · intro ⟨b, hp, hc⟩
    have ⟨a₁, _, heq⟩ := mem_map.mp hp
    have hpair := pair_inj.mp heq
    exact hpair.2.symm.trans (congrArg op hpair.1) ▸ hc
  · intro hc
    exact ⟨op a, mem_map.mpr ⟨a, ha, rfl⟩, hc⟩

theorem map_congr {op₁ op₂ : ZFSet → ZFSet}
    (h : ∀ a ∈ α, op₁ a = op₂ a) : map op₁ α = map op₂ α := by
  ext c
  rw [mem_map, mem_map]
  constructor
  · intro ⟨a, ha, hc⟩
    exact ⟨a, ha, (congrArg (pair a) (h a ha)).symm.trans hc⟩
  · intro ⟨a, ha, hc⟩
    exact ⟨a, ha, (congrArg (pair a) (h a ha)).trans hc⟩

theorem map_mem_pi {op : ZFSet → ZFSet}
    (h : ∀ a ∈ α, op a ∈ app β a) : map op α ∈ pi α β := by
  refine mem_pi.mpr ⟨map_isFunc.mpr fun a ha => ?_, ?_⟩
  · exact mem_sUnion.mpr ⟨app β a, mem_image.mpr ⟨a, ha, rfl⟩, h a ha⟩
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hc
    exact mem_sigma.mpr ⟨a, ha, op a, h a ha, rfl⟩

theorem app_mem_of_mem_pi (hf : f ∈ pi α β) (ha : a ∈ α) :
    app f a ∈ app β a := (mem_pi.mp hf).app_mem ha

open scoped Classical in
theorem pi_nonempty (h : ∀ a ∈ α, ∃ b, b ∈ app β a) :
    ∃ f, f ∈ pi α β := by
  let choose a := if ha : a ∈ α then Classical.choose (h a ha) else ∅
  have choose_mem (a) (ha : a ∈ α) : choose a ∈ app β a := by
    simpa [choose, ha] using Classical.choose_spec (h a ha)
  exact ⟨map choose α, map_mem_pi choose_mem⟩

theorem sigma_mono {α₁ α₂ β₁ β₂ : ZFSet} (hα : α₁ ⊆ α₂)
    (hβ : ∀ a ∈ α₁, app β₁ a ⊆ app β₂ a) : σ α₁ β₁ ⊆ σ α₂ β₂ := by
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sigma.mp hc
  exact mem_sigma.mpr ⟨a, hα ha, b, hβ a ha hb, rfl⟩

@[simp] theorem dom_empty : dom ∅ = ∅ := by
  ext x
  simp

@[simp] theorem dom_sUnion (s : ZFSet) : dom (⋃₀ s) = ⋃₀ image dom s := by
  ext x
  rw [mem_dom, mem_sUnion_image]
  simp only [mem_sUnion, mem_dom]
  constructor
  · rintro ⟨p, ⟨f, hf, hp⟩, rfl⟩
    exact ⟨f, hf, p, hp, rfl⟩
  · rintro ⟨f, hf, p, hp, rfl⟩
    exact ⟨p, ⟨f, hf, hp⟩, rfl⟩

@[simp] theorem dom_union (f g : ZFSet) : dom (f ∪ g) = dom f ∪ dom g := by
  ext x
  simp only [mem_dom, mem_union]
  constructor
  · rintro ⟨p, hp | hp, rfl⟩
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr ⟨p, hp, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, .inl hp, rfl⟩
    · exact ⟨p, .inr hp, rfl⟩

@[simp] theorem dom_singleton_pair (a b : ZFSet) : dom {pair a b} = {a} := by
  ext x
  simp

theorem dom_mono {f g : ZFSet} (h : f ⊆ g) : dom f ⊆ dom g := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_dom.mp hx
  exact mem_dom.mpr ⟨p, h hp, rfl⟩

theorem IsFunc.pair_mem (hf : IsFunc α β f) (ha : a ∈ dom f) : pair a (app f a) ∈ f := by
  obtain ⟨p, hp, rfl⟩ := mem_dom.mp ha
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod.mp (hf.1 hp)
  simpa [hf.app_eq hp] using hp

theorem IsFunc.app_eq_of_subset {g α₁ β₁ : ZFSet} (hf : IsFunc α β f)
    (hg : IsFunc α₁ β₁ g) (hfg : f ⊆ g) (ha : a ∈ dom f) : app g a = app f a :=
  hg.app_eq (hfg (hf.pair_mem ha))

theorem isFunc_sUnion {s : ZFSet}
    (hf : ∀ f ∈ s, IsFunc (dom f) (image snd f) f)
    (hcompat : ∀ f ∈ s, ∀ g ∈ s, ∀ x ∈ dom f, x ∈ dom g → app f x = app g x) :
    IsFunc (dom (⋃₀ s)) (image snd (⋃₀ s)) (⋃₀ s) := by
  refine isFunc_dom_image_snd ?_ ?_
  · intro p hp
    have ⟨f, hf', hp⟩ := mem_sUnion.mp hp
    obtain ⟨a, _, b, _, heq⟩ := mem_prod.mp ((hf f hf').1 hp)
    exact ⟨a, b, heq⟩
  · intro x y₁ y₂ h₁ h₂
    have ⟨f, hf', h₁⟩ := mem_sUnion.mp h₁
    have ⟨g, hg, h₂⟩ := mem_sUnion.mp h₂
    simpa [(hf f hf').app_eq h₁, (hf g hg).app_eq h₂] using
      hcompat f hf' g hg x (pair_mem_dom h₁) (pair_mem_dom h₂)

theorem IsFunc.union_singleton (hf : IsFunc α β f) (ha : a ∉ dom f) (b : ZFSet) :
    IsFunc (dom (f ∪ {pair a b})) (image snd (f ∪ {pair a b})) (f ∪ {pair a b}) := by
  refine isFunc_dom_image_snd ?_ ?_
  · intro p hp
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨x, _, y, _, heq⟩ := mem_prod.mp (hf.1 hp)
      exact ⟨x, y, heq⟩
    · exact ⟨a, b, mem_singleton.mp hp⟩
  · intro x y₁ y₂ h₁ h₂
    rcases mem_union.mp h₁ with h₁ | h₁
    · rcases mem_union.mp h₂ with h₂ | h₂
      · exact (hf.app_eq h₁).symm.trans (hf.app_eq h₂)
      · exact (ha ((pair_inj.mp (mem_singleton.mp h₂)).1 ▸ pair_mem_dom h₁)).elim
    · obtain ⟨rfl, rfl⟩ := pair_inj.mp (mem_singleton.mp h₁)
      rcases mem_union.mp h₂ with h₂ | h₂
      · exact (ha (pair_mem_dom h₂)).elim
      · exact (pair_inj.mp (mem_singleton.mp h₂)).2.symm

theorem mem_pi_of_isFunc {B : ZFSet} (hf : IsFunc α β f)
    (hval : ∀ x y, pair x y ∈ f → y ∈ app B x) : f ∈ pi α B := by
  have hsigma : f ⊆ σ α B := by
    intro p hp
    obtain ⟨x, hx, y, _, rfl⟩ := mem_prod.mp (hf.1 hp)
    exact mem_sigma.mpr ⟨x, hx, y, hval x y hp, rfl⟩
  refine mem_pi.mpr ⟨⟨?_, hf.2⟩, hsigma⟩
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sigma.mp (hsigma hp)
  exact pair_mem_prod.mpr ⟨hx, mem_sUnion_image.mpr ⟨x, hx, hy⟩⟩

@[simp] theorem mem_fibre_sigma : b ∈ fibreOp (σ α β) a ↔ a ∈ α ∧ b ∈ app β a := by
  simp

@[simp] theorem mem_fibre_sigma_map {V : ZFSet → ZFSet} :
    b ∈ fibreOp (σ α (map V α)) a ↔ a ∈ α ∧ b ∈ V a := by
  rw [mem_fibre_sigma]
  exact and_congr_right fun ha => by rw [app_map ha]

@[simp] theorem fibre_iUnion {ι : Type*} [Small.{u} ι] (f : ι → ZFSet.{u}) (a : ZFSet.{u}) :
    fibreOp (⋃ i, f i) a = ⋃ i, fibreOp (f i) a := by
  ext b
  simp



theorem fibre_empty (a : ZFSet) : fibreOp ∅ a = ∅ :=
  (eq_empty _).2 fun _ he => notMem_empty _ (mem_fibre.mp he)

theorem fibre_union {f g a : ZFSet} :
    fibreOp (f ∪ g) a = fibreOp f a ∪ fibreOp g a := by
  ext b
  simp

theorem union_empty (set : ZFSet) : set ∪ ∅ = set := by
  ext
  simp

theorem empty_union (set : ZFSet) : ∅ ∪ set = set := by
  ext
  simp

end ZFSet
