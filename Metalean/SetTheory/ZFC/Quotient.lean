/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import Metalean.Meta.ZF
public import Metalean.SetTheory.ZFC.Aczel
import Metalean.SetTheory.ZFC.FixedPoint

public section

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {a b c r s t v w x y : ZFSet}

def neighborhood (a r w : ZFSet) : ZFSet :=
  a.sep fun v => [zf|r w v] = verum ∨ [zf|r v w] = verum

@[simp] theorem mem_neighborhood :
    v ∈ neighborhood a r w ↔ v ∈ a ∧ ([zf|r w v] = verum ∨ [zf|r v w] = verum) :=
  mem_sep

noncomputable def relationStep (a r s : ZFSet) : ZFSet :=
  ⋃₀ image (neighborhood a r) s

@[simp] theorem mem_relationStep :
    v ∈ relationStep a r s ↔ ∃ w ∈ s, v ∈ a ∧ ([zf|r w v] = verum ∨ [zf|r v w] = verum) :=
  mem_sUnion_image.trans (exists_congr fun _ => and_congr_right fun _ => mem_neighborhood)

theorem relationStep_subset (a r s : ZFSet) : relationStep a r s ⊆ a := fun _ hv =>
  have ⟨_, _, hva, _⟩ := mem_relationStep.mp hv
  hva

theorem relationStep_mono (h : s ⊆ t) :
    relationStep a r s ⊆ relationStep a r t := fun _ hv =>
  have ⟨w, hw, hv⟩ := mem_relationStep.mp hv
  mem_relationStep.mpr ⟨w, h hw, hv⟩

noncomputable def closureOp (a r x s : ZFSet) : ZFSet :=
  {x} ∪ relationStep a r s

@[simp] theorem mem_closureOp :
    v ∈ closureOp a r x s ↔ v = x ∨ v ∈ relationStep a r s := by
  rw [closureOp, mem_union, mem_singleton]

noncomputable def equivClosure (a b r x : ZFSet) : ZFSet :=
  lfp b (closureOp a r x)

theorem closureOp_mapsTo (hab : a ⊆ b) (hx : x ∈ a) :
    Set.MapsTo (closureOp a r x) (Set.Iic b) (Set.Iic b) := by
  intro s _ v hv
  rcases mem_closureOp.mp hv with rfl | hv
  · exact hab hx
  · exact hab (relationStep_subset a r s hv)

theorem monotoneOn_closureOp (a r x b : ZFSet) :
    MonotoneOn (closureOp a r x) (Set.Iic b) := by
  intro s _ t _ hst v hv
  rcases mem_closureOp.mp hv with rfl | hv
  · exact mem_closureOp.mpr (.inl rfl)
  · exact mem_closureOp.mpr (.inr (relationStep_mono hst hv))

theorem equivClosure_subset (hab : a ⊆ b) (hx : x ∈ a) : equivClosure a b r x ⊆ a :=
  lfp_least hab fun v hv => by
    rcases mem_closureOp.mp hv with rfl | hv
    · exact hx
    · exact relationStep_subset a r _ hv

theorem equivClosure_least (hsb : s ⊆ b) (hxs : x ∈ s)
    (hstep : ∀ v ∈ s, ∀ w ∈ a, [zf|r v w] = verum ∨ [zf|r w v] = verum → w ∈ s) :
    equivClosure a b r x ⊆ s :=
  lfp_least hsb fun v hv => by
    rcases mem_closureOp.mp hv with rfl | hv
    · exact hxs
    · obtain ⟨w, hw, hva, hr⟩ := mem_relationStep.mp hv
      exact hstep w hw v hva hr

theorem closureOp_subset_equivClosure (hab : a ⊆ b) (hx : x ∈ a) :
    closureOp a r x (equivClosure a b r x) ⊆ equivClosure a b r x :=
  lfp_closed (closureOp_mapsTo hab hx) (monotoneOn_closureOp a r x b)

theorem self_mem_equivClosure (hab : a ⊆ b) (hx : x ∈ a) : x ∈ equivClosure a b r x :=
  closureOp_subset_equivClosure hab hx (mem_closureOp.mpr (.inl rfl))

theorem equivClosure_step (hab : a ⊆ b) (hx : x ∈ a) (hv : v ∈ equivClosure a b r x)
    (hw : w ∈ a) (hr : [zf|r v w] = verum ∨ [zf|r w v] = verum) :
    w ∈ equivClosure a b r x :=
  closureOp_subset_equivClosure hab hx
    (mem_closureOp.mpr (.inr (mem_relationStep.mpr ⟨v, hv, hw, hr⟩)))

theorem equivClosure_eq_of_rel (hab : a ⊆ b) (hx : x ∈ a) (hy : y ∈ a)
    (hr : [zf|r x y] = verum) : equivClosure a b r x = equivClosure a b r y := by
  apply subset_antisymm
  · refine equivClosure_least (fun _ hz => hab (equivClosure_subset hab hy hz)) ?_ ?_
    · exact equivClosure_step hab hy (self_mem_equivClosure hab hy) hx (.inr hr)
    · exact fun v hv w hw hr => equivClosure_step hab hy hv hw hr
  · refine equivClosure_least (fun _ hz => hab (equivClosure_subset hab hx hz)) ?_ ?_
    · exact equivClosure_step hab hx (self_mem_equivClosure hab hx) hy (.inl hr)
    · exact fun v hv w hw hr => equivClosure_step hab hx hv hw hr

theorem app_eq_of_mem_equivClosure {fn : ZFSet} (hab : a ⊆ b) (hx : x ∈ a)
    (hcompat : ∀ u ∈ a, ∀ v ∈ a, [zf|r u v] = verum → [zf|fn u] = [zf|fn v])
    (hv : v ∈ equivClosure a b r x) : [zf|fn v] = [zf|fn x] := by
  have hsub : equivClosure a b r x ⊆ a.sep fun z => [zf|fn z] = [zf|fn x] := by
    refine equivClosure_least (fun _ hz => hab (mem_sep.mp hz).1)
      (mem_sep.mpr ⟨hx, rfl⟩) ?_
    intro w hw z hz hor
    have ⟨hwA, hwf⟩ := mem_sep.mp hw
    refine mem_sep.mpr ⟨hz, ?_⟩
    rcases hor with h | h
    · rw [← hcompat w hwA z hz h]
      exact hwf
    · rw [hcompat z hz w hwA h]
      exact hwf
  exact (mem_sep.mp (hsub hv)).2

@[expose] noncomputable def quotient (a b r : ZFSet) : ZFSet :=
  image (equivClosure a b r) a

@[simp] theorem mem_quotient : c ∈ quotient a b r ↔ ∃ x ∈ a, c = equivClosure a b r x :=
  mem_image'

noncomputable def quotientLift (fn c : ZFSet) : ZFSet :=
  ⋃₀ image (fun value => [zf|fn value]) c

theorem quotientLift_equivClosure {fn : ZFSet} (hab : a ⊆ b) (hx : x ∈ a)
    (hcompat : ∀ u ∈ a, ∀ v ∈ a, [zf|r u v] = verum → [zf|fn u] = [zf|fn v]) :
    quotientLift fn (equivClosure a b r x) = [zf|fn x] := by
  ext z
  rw [quotientLift, mem_sUnion]
  constructor
  · intro ⟨s, hs, hz⟩
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hs
    rwa [app_eq_of_mem_equivClosure hab hx hcompat hy] at hz
  · intro hz
    exact ⟨[zf|fn x], mem_image.mpr ⟨x, self_mem_equivClosure hab hx, rfl⟩, hz⟩

end ZFSet
