/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Accessibility
public import Metalean.SetTheory.ZFC.Universe.Type
import Metalean.SetTheory.ZFC.Family

public section

open ZFSet

namespace Metalean

universe u

attribute [local instance 2000] Classical.allZFSetDefinable

variable {n : Nat} {Φ : ZFSet → ZFSet}
  {Λ T X X₀ α r β γ a b f g h i j q t x y z : ZFSet}

@[expose] def SmallOver (Λ X : ZFSet) : Prop :=
  ∃ i ∈ Λ, ∃ g : ZFSet → ZFSet, X ⊆ image g i

theorem SmallOver.mono {Λ' : ZFSet} (h : SmallOver Λ X) (hΛ : Λ ⊆ Λ') : SmallOver Λ' X :=
  have ⟨i, hi, g, hX⟩ := h
  ⟨i, hΛ hi, g, hX⟩

theorem succ_inj (h : insert x x = insert y y) : x = y := by
  have hx : x ∈ insert y y := by rw [← h]; exact mem_insert x x
  have hy : y ∈ insert x x := by rw [h]; exact mem_insert y y
  rcases mem_insert_iff.mp hx with hxy | hxy
  · exact hxy
  · rcases mem_insert_iff.mp hy with hyx | hyx
    · exact hyx.symm
    · exact absurd hyx (mem_asymm hxy)

def ordPath (T : ZFSet) : ZFSet :=
  (powerset (prod omega T)).sep fun f => dom f ∈ omega

noncomputable def ordExt (fn x : ZFSet) : ZFSet := fn ∪ {pair (dom fn) x}

theorem mem_ordPath : q ∈ ordPath T ↔ q ⊆ prod omega T ∧ dom q ∈ omega := by
  simp [ordPath]

theorem mem_ordExt : z ∈ ordExt q x ↔ z ∈ q ∨ z = pair (dom q) x := by
  simp [ordExt]

theorem dom_ordExt (fn x : ZFSet) : dom (ordExt fn x) = insert (dom fn) (dom fn) := by
  simp [ordExt]
  ext z
  simp [Or.comm]

theorem empty_mem_ordPath (T : ZFSet) : ∅ ∈ ordPath T := by
  have hd : dom ∅ = ∅ := by ext; simp
  exact mem_ordPath.mpr ⟨by simp, by rw [hd]; exact omega_zero⟩

theorem ordExt_mem_ordPath (hf : q ∈ ordPath T) (hx : x ∈ T) :
    ordExt q x ∈ ordPath T := by
  have ⟨hsub, hdom⟩ := mem_ordPath.mp hf
  refine mem_ordPath.mpr ⟨fun z hz => ?_, by rw [dom_ordExt]; exact omega_succ hdom⟩
  rcases mem_ordExt.mp hz with h | rfl
  · exact hsub h
  · exact mem_prod.mpr ⟨dom q, hdom, x, hx, rfl⟩

theorem kpair_dom_not_mem : pair (dom q) x ∉ q := fun h =>
  mem_irrefl (dom q) (pair_mem_dom h)

theorem ordExt_ne_empty (q x : ZFSet) : ordExt q x ≠ ∅ := fun h =>
  notMem_empty _ (h ▸ mem_ordExt.mpr (.inr rfl))

theorem ordExt_inj (h : ordExt f x = ordExt g y) : f = g ∧ x = y := by
  have hdom : dom f = dom g := succ_inj (by rw [← dom_ordExt, ← dom_ordExt, h])
  have hkey : pair (dom f) x = pair (dom g) y := by
    have hm : pair (dom f) x ∈ ordExt g y := by
      rw [← h]; exact mem_ordExt.mpr (.inr rfl)
    rcases mem_ordExt.mp hm with hm' | hm'
    · rw [hdom] at hm'; exact absurd hm' kpair_dom_not_mem
    · exact hm'
  refine ⟨subset_antisymm (fun z hz => ?_) fun z hz => ?_, (pair_inj.mp hkey).2⟩
  · have hz' : z ∈ ordExt g y := by rw [← h]; exact mem_ordExt.mpr (.inl hz)
    rcases mem_ordExt.mp hz' with h' | h'
    · exact h'
    · rw [← hkey] at h'
      rw [h'] at hz
      exact absurd hz kpair_dom_not_mem
  · have hz' : z ∈ ordExt f x := by rw [h]; exact mem_ordExt.mpr (.inl hz)
    rcases mem_ordExt.mp hz' with h' | h'
    · exact h'
    · rw [hkey] at h'
      rw [h'] at hz
      exact absurd hz kpair_dom_not_mem

def ordTree (T : ZFSet) : ZFSet := (powerset (ordPath T)).sep fun t => ∅ ∈ t

def ordSub (T t x : ZFSet) : ZFSet := (ordPath T).sep fun f => ordExt f x ∈ t

def ordChild (T t : ZFSet) : ZFSet := T.sep fun x => ordExt ∅ x ∈ t

noncomputable def ordChildSet (T t : ZFSet) : ZFSet := image (ordSub T t) (ordChild T t)

def ordRel (T : ZFSet) : ZFSet :=
  (prod (ordTree T) (ordTree T)).sep fun z => fst z ∈ ordChildSet T (snd z)

def ordSet (T : ZFSet) : ZFSet := accSet (ordTree T) (ordRel T)

theorem mem_ordTree : t ∈ ordTree T ↔ t ⊆ ordPath T ∧ ∅ ∈ t := by
  simp [ordTree]

theorem mem_ordChildSet : z ∈ ordChildSet T t ↔ ∃ x ∈ ordChild T t, z = ordSub T t x :=
  mem_image'

theorem mem_ordRel {u v : ZFSet} :
    pair u v ∈ ordRel T ↔ (u ∈ ordTree T ∧ v ∈ ordTree T) ∧ u ∈ ordChildSet T v := by
  simp [ordRel]

theorem ordPath_mem_type (hT : T ∈ U_ n) : ordPath T ∈ U_ n :=
  sep_mem_type (powerset_mem_type (prod_mem_type omega_mem_type hT))

theorem ordTree_mem_type (hT : T ∈ U_ n) : ordTree T ∈ U_ n :=
  sep_mem_type (powerset_mem_type (ordPath_mem_type hT))

theorem ordSet_subset : ordSet T ⊆ ordTree T := accSet_subset

noncomputable def ordGraft (i h : ZFSet) : ZFSet :=
  {∅} ∪ ⋃₀ image (fun j => image (fun f => ordExt f j) (app h j)) i

theorem mem_ordGraft :
    z ∈ ordGraft i h ↔ z = ∅ ∨ ∃ j ∈ i, ∃ f ∈ app h j, z = ordExt f j := by
  rw [ordGraft, mem_union, mem_singleton]
  exact or_congr_right
    (mem_sUnion_image.trans (exists_congr fun _ => and_congr_right fun _ => mem_image'))

theorem ordGraft_mem_ordTree (hi : i ⊆ T) (hh : ∀ j ∈ i, app h j ∈ ordTree T) :
    ordGraft i h ∈ ordTree T := by
  refine mem_ordTree.mpr ⟨fun z hz => ?_, mem_ordGraft.mpr (.inl rfl)⟩
  rcases mem_ordGraft.mp hz with rfl | ⟨j, hj, f, hf, rfl⟩
  · exact empty_mem_ordPath T
  · exact ordExt_mem_ordPath ((mem_ordTree.mp (hh j hj)).1 hf) (hi hj)

theorem ordSub_ordGraft (hh : ∀ j ∈ i, app h j ∈ ordTree T) (hj : j ∈ i) :
    ordSub T (ordGraft i h) j = app h j := by
  refine subset_antisymm (fun f hf => ?_) fun f hf => ?_
  · have ⟨_, hmem⟩ := mem_sep.mp hf
    rcases mem_ordGraft.mp hmem with hz | ⟨j', hj', f', hf', hz⟩
    · exact absurd hz (ordExt_ne_empty f j)
    · have ⟨h₁, h₂⟩ := ordExt_inj hz
      rw [h₁, h₂]
      exact hf'
  · exact mem_sep.mpr ⟨(mem_ordTree.mp (hh j hj)).1 hf,
      mem_ordGraft.mpr (.inr ⟨j, hj, f, hf, rfl⟩)⟩

theorem ordChild_ordGraft : ordChild T (ordGraft i h) ⊆ i := by
  intro x hx
  have ⟨_, hmem⟩ := mem_sep.mp hx
  rcases mem_ordGraft.mp hmem with hz | ⟨j, hj, f, hf, hz⟩
  · exact absurd hz (ordExt_ne_empty ∅ x)
  · exact (ordExt_inj hz).2 ▸ hj

theorem mem_ordChild_ordGraft (hi : i ⊆ T) (hh : ∀ j ∈ i, app h j ∈ ordTree T)
    (hj : j ∈ i) : j ∈ ordChild T (ordGraft i h) :=
  mem_sep.mpr ⟨hi hj,
    mem_ordGraft.mpr (.inr ⟨j, hj, ∅, (mem_ordTree.mp (hh j hj)).2, rfl⟩)⟩

theorem ordGraft_mem_ordSet (hi : i ⊆ T) (hh : ∀ j ∈ i, app h j ∈ ordSet T) :
    ordGraft i h ∈ ordSet T := by
  have hht : ∀ j ∈ i, app h j ∈ ordTree T := fun j hj => ordSet_subset (hh j hj)
  refine accSet_intro (ordGraft_mem_ordTree hi hht) fun y _ hr => ?_
  have ⟨x, hx, hy⟩ := mem_ordChildSet.mp (mem_ordRel.mp hr).2
  rw [hy, ordSub_ordGraft hht (ordChild_ordGraft hx)]
  exact hh x (ordChild_ordGraft hx)

theorem ordRel_ordGraft (hi : i ⊆ T) (hh : ∀ j ∈ i, app h j ∈ ordSet T) (hj : j ∈ i) :
    pair (app h j) (ordGraft i h) ∈ ordRel T := by
  have hht : ∀ j ∈ i, app h j ∈ ordTree T := fun j hj => ordSet_subset (hh j hj)
  refine mem_ordRel.mpr ⟨⟨hht j hj, ordGraft_mem_ordTree hi hht⟩, ?_⟩
  exact mem_ordChildSet.mpr ⟨j, mem_ordChild_ordGraft hi hht hj,
    (ordSub_ordGraft hht hj).symm⟩

def stagePred (α r a : ZFSet) : ZFSet := α.sep fun b => pair b a ∈ r

def stageBody (Φ : ZFSet → ZFSet) (γ b : ZFSet) : ZFSet := fibreOp γ b ∪ Φ (fibreOp γ b)

noncomputable def stageStep (Φ : ZFSet → ZFSet) (α r γ a : ZFSet) : ZFSet :=
  ⋃₀ image (stageBody Φ γ) (stagePred α r a)

def stageOp (Φ : ZFSet → ZFSet) (α r β γ : ZFSet) : ZFSet :=
  (prod (accSet α r) β).sep fun p => snd p ∈ stageStep Φ α r γ (fst p)

def stageSet (Φ : ZFSet → ZFSet) (α r β : ZFSet) : ZFSet :=
  lfp (prod (accSet α r) β) (stageOp Φ α r β)

noncomputable def stageUnion (Φ : ZFSet → ZFSet) (α r β : ZFSet) : ZFSet :=
  ⋃₀ image (stageBody Φ (stageSet Φ α r β)) (accSet α r)

theorem mem_stageStep :
    z ∈ stageStep Φ α r γ a ↔ ∃ b ∈ stagePred α r a, z ∈ stageBody Φ γ b :=
  mem_sUnion_image

theorem mem_stageUnion :
    z ∈ stageUnion Φ α r β ↔ ∃ a ∈ accSet α r, z ∈ stageBody Φ (stageSet Φ α r β) a :=
  mem_sUnion_image

theorem stageOp_mapsTo (α r β : ZFSet) :
    Set.MapsTo (stageOp Φ α r β) (Set.Iic (prod (accSet α r) β))
      (Set.Iic (prod (accSet α r) β)) :=
  fun _ _ _ hz => (mem_sep.mp hz).1

variable (hmono : Monotone Φ) (hUΦ : ∀ X, X ∈ U_ n → Φ X ∈ U_ n) (hα : α ∈ U_ n)

include hmono

theorem stageBody_mono (h : γ ⊆ β) (b : ZFSet) :
    stageBody Φ γ b ⊆ stageBody Φ β b := fun z hz => by
  rcases mem_union.mp hz with hz' | hz'
  · exact mem_union.mpr (.inl (fibre_mono h b hz'))
  · exact mem_union.mpr (.inr (hmono (fibre_mono h b) hz'))

theorem stageStep_mono (h : γ ⊆ β) :
    stageStep Φ α r γ a ⊆ stageStep Φ α r β a := fun _ hz =>
  have ⟨b, hb, hzb⟩ := mem_stageStep.mp hz
  mem_stageStep.mpr ⟨b, hb, stageBody_mono hmono h b hzb⟩

theorem monotoneOn_stageOp (α r β : ZFSet) :
    MonotoneOn (stageOp Φ α r β) (Set.Iic (prod (accSet α r) β)) :=
  fun _ _ _ _ hγ _ hz => mem_sep.mpr ⟨(mem_sep.mp hz).1,
    stageStep_mono hmono hγ (mem_sep.mp hz).2⟩

theorem stage_intro (ha : a ∈ accSet α r) (hz : z ∈ β)
    (hstep : z ∈ stageStep Φ α r (stageSet Φ α r β) a) :
    z ∈ fibreOp (stageSet Φ α r β) a := by
  refine mem_fibre.mpr (lfp_closed (stageOp_mapsTo α r β) (monotoneOn_stageOp hmono α r β)
    (mem_sep.mpr ⟨mem_prod.mpr ⟨a, ha, z, hz, rfl⟩, ?_⟩))
  simp only [fst_pair, snd_pair]
  exact hstep

theorem stage_elim (hz : z ∈ fibreOp (stageSet Φ α r β) a) :
    z ∈ stageStep Φ α r (stageSet Φ α r β) a := by
  have h := lfp_unfold (stageOp_mapsTo α r β) (monotoneOn_stageOp hmono α r β)
    (mem_fibre.mp hz)
  have h₂ := (mem_sep.mp h).2
  simp at h₂
  exact h₂

include hUΦ hα

theorem stage_mem_type :
    ∀ a ∈ accSet α r, fibreOp (stageSet Φ α r (U_ n)) a ∈ U_ n := by
  refine accSet_induction fun a ha ih => ?_
  have hstepU : stageStep Φ α r (stageSet Φ α r (U_ n)) a ∈ U_ n := by
    refine sUnion_mem_type (image_mem_type
      (mem_type_of_subset hα fun b hb => (mem_sep.mp hb).1) fun b hb => ?_)
    have hb' := mem_sep.mp hb
    have hfib := ih b (accSet_inv ha b hb'.1 hb'.2) hb'.2
    exact union_mem_type hfib (hUΦ _ hfib)
  exact mem_type_of_subset hstepU fun z hz => stage_elim hmono hz

theorem stage_mono (hb : b ∈ accSet α r) (ha : a ∈ accSet α r) (hr : pair b a ∈ r) :
    stageBody Φ (stageSet Φ α r (U_ n)) b ⊆ fibreOp (stageSet Φ α r (U_ n)) a := by
  intro z hz
  have hfb := stage_mem_type hmono hUΦ hα b hb
  have hzU : z ∈ U_ n := by
    rcases mem_union.mp hz with h | h
    · exact mem_type_of_mem hfb h
    · exact mem_type_of_mem (hUΦ _ hfb) h
  exact stage_intro hmono ha hzU
    (mem_stageStep.mpr ⟨b, mem_sep.mpr ⟨accSet_subset hb, hr⟩, hz⟩)

theorem stageUnion_mem_type : stageUnion Φ α r (U_ n) ∈ U_ n :=
  sUnion_mem_type (image_mem_type (mem_type_of_subset hα accSet_subset) fun a ha =>
    union_mem_type (stage_mem_type hmono hUΦ hα a ha)
      (hUΦ _ (stage_mem_type hmono hUΦ hα a ha)))

omit hmono hUΦ hα

def stageIdxSet (Φ : ZFSet → ZFSet) (α r β X₀ : ZFSet) (g : ZFSet → ZFSet)
    (j : ZFSet) : ZFSet :=
  (accSet α r).sep fun a => ∀ w ∈ X₀, w = g j → w ∈ stageBody Φ (stageSet Φ α r β) a

include hmono hUΦ in
theorem exists_stage_of_smallOver (hT : ordTree (⋃₀ Λ) ∈ U_ n)
    (hX₀ : X₀ ⊆ stageUnion Φ (ordTree (⋃₀ Λ)) (ordRel (⋃₀ Λ)) (U_ n))
    (hsm : SmallOver Λ X₀) :
    ∃ a, a ∈ ordSet (⋃₀ Λ) ∧
      X₀ ⊆ fibreOp (stageSet Φ (ordTree (⋃₀ Λ)) (ordRel (⋃₀ Λ)) (U_ n)) a := by
  have ⟨i, hiΛ, g, hX₀g⟩ := hsm
  have hiT : i ⊆ ⋃₀ Λ := fun w hw => mem_sUnion.mpr ⟨i, hiΛ, hw⟩
  have hne : ∀ d, d ∈ i →
      ∃ w, w ∈ app (fn i (stageIdxSet Φ (ordTree (⋃₀ Λ))
        (ordRel (⋃₀ Λ)) (U_ n) X₀ g)) d := by
    intro j hj
    rw [app_map hj]
    by_cases hgj : g j ∈ X₀
    · have ⟨a, ha, hga⟩ := mem_stageUnion.mp (hX₀ hgj)
      exact ⟨a, mem_sep.mpr ⟨ha, fun w _ hwg => by rw [hwg]; exact hga⟩⟩
    · exact ⟨ordGraft ∅ ∅, mem_sep.mpr
        ⟨ordGraft_mem_ordSet (empty_subset _) fun _ hj => by simp at hj,
          fun w hw hwg => absurd (hwg ▸ hw) hgj⟩⟩
  have ⟨hf, hfmem⟩ := pi_nonempty hne
  have hha : ∀ j ∈ i, app hf j ∈ stageIdxSet Φ (ordTree (⋃₀ Λ))
      (ordRel (⋃₀ Λ)) (U_ n) X₀ g j := by
    intro j hj
    have h := app_mem_of_mem_pi hfmem hj
    rwa [app_map hj] at h
  have hhOrd : ∀ j ∈ i, app hf j ∈ ordSet (⋃₀ Λ) := fun j hj =>
    (mem_sep.mp (hha j hj)).1
  refine ⟨ordGraft i hf, ordGraft_mem_ordSet hiT hhOrd, fun x hx => ?_⟩
  have ⟨j, hj, hxg⟩ := mem_image.mp (hX₀g hx)
  exact stage_mono hmono hUΦ hT (hhOrd j hj) (ordGraft_mem_ordSet hiT hhOrd)
    (ordRel_ordGraft hiT hhOrd hj) ((mem_sep.mp (hha j hj)).2 x hx hxg.symm)

include hmono hUΦ in
theorem exists_closed_of_smallSupport (hΛ : Λ ∈ U_ n)
    (hsupp : ∀ X z, z ∈ Φ X → ∃ X₀, X₀ ⊆ X ∧ SmallOver Λ X₀ ∧ z ∈ Φ X₀) :
    ∃ W, W ∈ U_ n ∧ Φ W ⊆ W := by
  have hT : ordTree (⋃₀ Λ) ∈ U_ n := ordTree_mem_type (sUnion_mem_type hΛ)
  refine ⟨stageUnion Φ (ordTree (⋃₀ Λ)) (ordRel (⋃₀ Λ)) (U_ n),
    stageUnion_mem_type hmono hUΦ hT, fun z hz => ?_⟩
  have ⟨X₀, hX₀W, hsm, hzX₀⟩ := hsupp _ z hz
  have ⟨a, ha, hX₀a⟩ := exists_stage_of_smallOver hmono hUΦ hT hX₀W hsm
  exact mem_stageUnion.mpr ⟨a, ha, mem_union.mpr (.inr (hmono hX₀a hzX₀))⟩

end Metalean
