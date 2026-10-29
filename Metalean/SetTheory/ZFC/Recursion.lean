/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.FixedPoint
public import Metalean.SetTheory.ZFC.Function

@[expose] public noncomputable section

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {Φ V : ZFSet → ZFSet} {F : ZFSet → ZFSet → ZFSet} {bound graph : ZFSet}

structure IsApprox (Φ : ZFSet → ZFSet) (bound : ZFSet) (V : ZFSet → ZFSet)
    (F : ZFSet → ZFSet → ZFSet) (graph : ZFSet) : Prop where
  isFunction : graph ∈ pi (dom graph) (map V (dom graph))
  memBlock : dom graph ⊆ lfp bound Φ
  closed : dom graph ⊆ Φ (dom graph)
  appEq : ∀ x ∈ dom graph, app graph x = F graph x

def approxSet (Φ : ZFSet → ZFSet) (bound : ZFSet) (V : ZFSet → ZFSet)
    (F : ZFSet → ZFSet → ZFSet) : ZFSet :=
  (powerset (σ (lfp bound Φ) (map V (lfp bound Φ)))).sep (IsApprox Φ bound V F)

def recGraph (Φ : ZFSet → ZFSet) (bound : ZFSet) (V : ZFSet → ZFSet)
    (F : ZFSet → ZFSet → ZFSet) : ZFSet :=
  ⋃₀ approxSet Φ bound V F

theorem IsApprox.app_mem (hg : IsApprox Φ bound V F graph) {x : ZFSet}
    (hx : x ∈ dom graph) : app graph x ∈ V x := by
  simpa [app_map hx] using app_mem_of_mem_pi hg.isFunction hx

theorem IsApprox.mem_approxSet (hg : IsApprox Φ bound V F graph) :
    graph ∈ approxSet Φ bound V F := by
  refine mem_sep.mpr ⟨mem_powerset.mpr ?_, hg⟩
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sigma.mp ((mem_pi.mp hg.isFunction).2 hp)
  exact mem_sigma.mpr ⟨x, hg.memBlock hx, y, by
    simpa [app_map hx, app_map (hg.memBlock hx)] using hy, rfl⟩

variable (hmaps : Set.MapsTo Φ (Set.Iic bound) (Set.Iic bound))
  (hmono : MonotoneOn Φ (Set.Iic bound))
  (hinter : ∀ x y, Φ x ∩ Φ y ⊆ Φ (x ∩ y))
  (hcongr : ∀ x graph₁ graph₂ z, (∀ w ∈ x, app graph₁ w = app graph₂ w) →
    z ∈ Φ x → z ∈ lfp bound Φ → F graph₁ z = F graph₂ z)

include hmaps hinter hcongr in
theorem IsApprox.agree {graph₁ graph₂ : ZFSet}
    (hg₁ : IsApprox Φ bound V F graph₁) (hg₂ : IsApprox Φ bound V F graph₂)
    {z : ZFSet} (hz₁ : z ∈ dom graph₁) (hz₂ : z ∈ dom graph₂) :
    app graph₁ z = app graph₂ z := by
  have key : lfp bound Φ ⊆ bound.sep fun z =>
      z ∈ dom graph₁ → z ∈ dom graph₂ → app graph₁ z = app graph₂ z := by
    refine lfp_least sep_subset fun z hz => ?_
    refine mem_sep.mpr ⟨hmaps sep_subset hz, fun hz₁ hz₂ => ?_⟩
    have h₁ := hinter _ _ (mem_inter.mpr ⟨hz, hg₁.closed hz₁⟩)
    have h₂ := hinter _ _ (mem_inter.mpr ⟨h₁, hg₂.closed hz₂⟩)
    rw [hg₁.appEq z hz₁, hg₂.appEq z hz₂]
    exact hcongr (((bound.sep fun z => z ∈ dom graph₁ → z ∈ dom graph₂ →
      app graph₁ z = app graph₂ z) ∩ dom graph₁) ∩ dom graph₂) _ _ z (fun w hw =>
      (mem_sep.mp (mem_inter.mp (mem_inter.mp hw).1).1).2
        (mem_inter.mp (mem_inter.mp hw).1).2 (mem_inter.mp hw).2) h₂ (hg₁.memBlock hz₁)
  exact (mem_sep.mp (key (hg₁.memBlock hz₁))).2 hz₁ hz₂

include hmaps hinter hcongr in
theorem recGraph_isFunc :
    IsFunc (dom (recGraph Φ bound V F)) (image snd (recGraph Φ bound V F))
      (recGraph Φ bound V F) := by
  refine isFunc_sUnion (fun graph hg => ?_) (fun graph₁ hg₁ graph₂ hg₂ x hx₁ hx₂ => ?_)
  · have hf := (mem_pi.mp (mem_sep.mp hg).2.isFunction).1
    refine isFunc_dom_image_snd (fun p hp => ?_) (fun x y₁ y₂ h₁ h₂ => ?_)
    · obtain ⟨a, _, b, _, heq⟩ := mem_prod.mp (hf.1 hp)
      exact ⟨a, b, heq⟩
    · exact (hf.app_eq h₁).symm.trans (hf.app_eq h₂)
  · exact IsApprox.agree hmaps hinter hcongr (mem_sep.mp hg₁).2 (mem_sep.mp hg₂).2 hx₁ hx₂

include hmaps hinter hcongr in
theorem recGraph_app_eq (hg : graph ∈ approxSet Φ bound V F) {x : ZFSet}
    (hx : x ∈ dom graph) : app (recGraph Φ bound V F) x = app graph x :=
  (mem_pi.mp (mem_sep.mp hg).2.isFunction).1.app_eq_of_subset
    (recGraph_isFunc hmaps hinter hcongr) (fun _ hp => mem_sUnion.mpr ⟨graph, hg, hp⟩) hx

include hmaps hmono hinter hcongr in
theorem recGraph_isApprox : IsApprox Φ bound V F (recGraph Φ bound V F) := by
  have hfunc := recGraph_isFunc hmaps hinter hcongr (V := V)
  have hdom {x : ZFSet} : x ∈ dom (recGraph Φ bound V F) ↔
      ∃ graph ∈ approxSet Φ bound V F, x ∈ dom graph := by
    rw [recGraph, dom_sUnion, mem_sUnion_image]
  have hblock : dom (recGraph Φ bound V F) ⊆ lfp bound Φ := by
    intro x hx
    have ⟨graph, hg, hx⟩ := hdom.mp hx
    exact (mem_sep.mp hg).2.memBlock hx
  refine ⟨mem_pi_of_isFunc hfunc ?_, hblock, ?_, ?_⟩
  · intro x y hxy
    have ⟨graph, hg, hp⟩ := mem_sUnion.mp hxy
    have ha := (mem_sep.mp hg).2
    rw [app_map (pair_mem_dom hxy), ← (mem_pi.mp ha.isFunction).1.app_eq hp]
    exact ha.app_mem (pair_mem_dom hp)
  · intro x hx
    have ⟨graph, hg, hx⟩ := hdom.mp hx
    exact hmono (subset_trans (mem_sep.mp hg).2.memBlock lfp_subset)
      (subset_trans hblock lfp_subset) (fun w hw => hdom.mpr ⟨graph, hg, hw⟩)
      ((mem_sep.mp hg).2.closed hx)
  · intro x hx
    have ⟨graph, hg, hx⟩ := hdom.mp hx
    have ha := (mem_sep.mp hg).2
    rw [recGraph_app_eq hmaps hinter hcongr hg hx, ha.appEq x hx]
    exact hcongr _ _ _ x (fun w hw => (recGraph_app_eq hmaps hinter hcongr hg hw).symm)
      (ha.closed hx) (ha.memBlock hx)

include hmaps hmono hcongr in
theorem IsApprox.extend (hg : IsApprox Φ bound V F graph) {z : ZFSet}
    (hz : z ∈ Φ (dom graph)) (hzd : z ∉ dom graph) (hvalue : F graph z ∈ V z) :
    IsApprox Φ bound V F (graph ∪ {pair z (F graph z)}) := by
  have hf := (mem_pi.mp hg.isFunction).1
  have hzblock : z ∈ lfp bound Φ := by
    rw [← lfp_fixed hmaps hmono]
    exact hmono (subset_trans hg.memBlock lfp_subset) lfp_subset hg.memBlock hz
  let value := F graph z
  let extended := graph ∪ {pair z value}
  have hext := hf.union_singleton hzd value
  have hsub : graph ⊆ extended := fun _ hp => mem_union.mpr (.inl hp)
  have happ {x : ZFSet} (hx : x ∈ dom graph) : app extended x = app graph x :=
    hf.app_eq_of_subset hext hsub hx
  have hmemz : pair z value ∈ extended := mem_union.mpr (.inr (mem_singleton.mpr rfl))
  have hdomeq {x : ZFSet} : x ∈ dom extended ↔ x ∈ dom graph ∨ x = z := by
    simp [extended]
  have hextBlock : dom extended ⊆ lfp bound Φ := by
    intro x hx
    rcases hdomeq.mp hx with hx | rfl
    · exact hg.memBlock hx
    · exact hzblock
  change IsApprox Φ bound V F extended
  refine ⟨mem_pi_of_isFunc hext ?_, hextBlock, ?_, ?_⟩
  · intro x y hp
    rw [app_map (pair_mem_dom hp)]
    rcases mem_union.mp hp with hp | hp
    · rw [← hf.app_eq hp]
      exact hg.app_mem (pair_mem_dom hp)
    · obtain ⟨rfl, rfl⟩ := pair_inj.mp (mem_singleton.mp hp)
      exact hvalue
  · intro x hx
    apply hmono (subset_trans hg.memBlock lfp_subset)
      (subset_trans hextBlock lfp_subset) (dom_mono hsub)
    rcases hdomeq.mp hx with hx | rfl
    · exact hg.closed hx
    · exact hz
  · intro x hx
    rcases hdomeq.mp hx with hx | rfl
    · rw [happ hx, hg.appEq x hx]
      exact hcongr _ _ _ x (fun w hw => (happ hw).symm) (hg.closed hx) (hg.memBlock hx)
    · rw [hext.app_eq hmemz]
      exact hcongr _ _ _ x (fun w hw => (happ hw).symm) hz hzblock

include hmaps hmono hinter hcongr in
theorem recGraph_app_of_empty {z : ZFSet} (hz : z ∈ Φ ∅) (hvalue : F ∅ z ∈ V z) :
    app (recGraph Φ bound V F) z = F ∅ z := by
  have he : IsApprox Φ bound V F ∅ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [IsPi, IsFunc]
  have hx := he.extend hmaps hmono hcongr (by simpa using hz) (by simp) hvalue
  have hm : pair z (F ∅ z) ∈ (∅ : ZFSet) ∪ {pair z (F ∅ z)} := by simp
  rw [recGraph_app_eq hmaps hinter hcongr hx.mem_approxSet (pair_mem_dom hm)]
  exact (mem_pi.mp hx.isFunction).1.app_eq hm

include hmaps hmono hinter hcongr in
theorem dom_recGraph
    (hstep : ∀ x ⊆ lfp bound Φ, ∀ graph, (∀ z ∈ x, app graph z ∈ V z) →
      ∀ z ∈ Φ x, F graph z ∈ V z) : dom (recGraph Φ bound V F) = lfp bound Φ := by
  have hr := recGraph_isApprox hmaps hmono hinter hcongr (V := V)
  refine subset_antisymm hr.memBlock (lfp_least (subset_trans hr.memBlock lfp_subset) ?_)
  intro z hz
  by_cases hzd : z ∈ dom (recGraph Φ bound V F)
  · exact hzd
  have hext := hr.extend hmaps hmono hcongr hz hzd
    (hstep _ hr.memBlock _ (fun _ hx => hr.app_mem hx) z hz)
  exact pair_mem_dom (mem_sUnion.mpr ⟨_, hext.mem_approxSet,
    mem_union.mpr (.inr (mem_singleton.mpr rfl))⟩)

end ZFSet
