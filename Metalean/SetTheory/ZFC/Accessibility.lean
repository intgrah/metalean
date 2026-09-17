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

variable {α r e a a₁ a₂ b c g m p s t u v : ZFSet}

def truthOf (s a : ZFSet) : ZFSet := fibreOp (image (fun b => pair b proof) s) a

theorem mem_truthOf : c ∈ truthOf s a ↔ a ∈ s ∧ c = proof := by
  change c ∈ fibreOp (image (fun b => pair b proof) s) a ↔ _
  rw [mem_fibre, mem_image]
  constructor
  · intro ⟨w, hw, hk⟩
    have ⟨h₁, h₂⟩ := pair_inj.mp hk
    exact ⟨h₁ ▸ hw, h₂.symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨a, hx, rfl⟩

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

theorem app_subset_image_snd (fn a : ZFSet) : [zf|fn a] ⊆ image snd fn := fun _ hz =>
  have ⟨p, hp, _, hzp⟩ := Aczel.mem_app.mp hz
  mem_image.mpr ⟨p, hp, hzp.symm⟩

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

def accBound (e : ZFSet) : ZFSet := image snd (image snd (image snd e))

def accStep (α r e g a₂ : ZFSet) : ZFSet :=
  [zf|e a₂ ∅ $([zf|fun (a₁ : α) (_proof : $(truthOf r [zf|(a₁, a₂)])) => g a₁])]

theorem accStep_subset_accBound : accStep α r e g a ⊆ accBound e :=
  subset_trans (app_subset_image_snd _ _)
    (image_mono (subset_trans (app_subset_image_snd _ _)
      (image_mono (app_subset_image_snd _ _))))

theorem accStep_congr {g₁ g₂ : ZFSet}
    (h : ∀ b ∈ α, pair b a ∈ r → [zf|g₁ b] = [zf|g₂ b]) :
    accStep α r e g₁ a = accStep α r e g₂ a :=
  congrArg (fun step => [zf|e a ∅ step])
    (Aczel.lam_congr fun b hy => Aczel.lam_congr fun _ hz => h b hy (mem_truthOf.mp hz).1)

structure IsAccApprox (α r e p : ZFSet) : Prop where
  dom_subset : fst p ⊆ accSet α r
  dom_lower : ∀ a ∈ fst p, ∀ b ∈ α, pair b a ∈ r → b ∈ fst p
  graph_subset : snd p ⊆ prod (fst p) (accBound e)
  graph_step : ∀ a ∈ fst p, [zf|$(snd p) a] = accStep α r e (snd p) a

def accApproxSet (α r e : ZFSet) : ZFSet :=
  (prod (powerset (accSet α r))
    (powerset (prod (accSet α r) (accBound e)))).sep (IsAccApprox α r e)

def accDom (α r e : ZFSet) : ZFSet := ⋃₀ image fst (accApproxSet α r e)

def accGr (α r e : ZFSet) : ZFSet := ⋃₀ image snd (accApproxSet α r e)

theorem accApprox_agree (hu : IsAccApprox α r e u) (hv : IsAccApprox α r e v) :
    ∀ a ∈ accSet α r, a ∈ fst u → a ∈ fst v → [zf|$(snd u) a] = [zf|$(snd v) a] := by
  refine accSet_induction
    (p := fun a => a ∈ fst u → a ∈ fst v → [zf|$(snd u) a] = [zf|$(snd v) a])
    fun a _ ih hxu hxv => ?_
  rw [hu.graph_step a hxu, hv.graph_step a hxv]
  refine accStep_congr fun b hy hr => ?_
  have hyu : b ∈ fst u := hu.dom_lower a hxu b hy hr
  exact ih b (hu.dom_subset hyu) hr hyu (hv.dom_lower a hxv b hy hr)

theorem app_accGr_eq (hu : u ∈ accApproxSet α r e) (hx : a ∈ fst u) :
    [zf|$(accGr α r e) a] = [zf|$(snd u) a] := by
  ext c
  constructor
  · intro hz
    have ⟨w, hw, hfw, hzw⟩ := Aczel.mem_app.mp hz
    have ⟨v, hv, hwv⟩ := mem_sUnion_image.mp hw
    have hva := (mem_sep.mp hv).2
    have ⟨input, hinput, _, _, hwk⟩ := mem_prod.mp (hva.graph_subset hwv)
    have hinputEq : input = a := by rw [← hfw, hwk, fst_pair]
    have hxv : a ∈ fst v := by rw [← hinputEq]; exact hinput
    rw [← accApprox_agree hva (mem_sep.mp hu).2 a (hva.dom_subset hxv) hxv hx]
    exact Aczel.mem_app.mpr ⟨w, hwv, hfw, hzw⟩
  · intro hz
    have ⟨w, hw, hfw, hzw⟩ := Aczel.mem_app.mp hz
    exact Aczel.mem_app.mpr ⟨w, mem_sUnion_image.mpr ⟨u, hu, hw⟩, hfw, hzw⟩

theorem accDom_mem_accSet (hx : a ∈ accDom α r e) : a ∈ accSet α r :=
  have ⟨_, hu, hxu⟩ := mem_sUnion_image.mp hx
  (mem_sep.mp hu).2.dom_subset hxu

theorem accDom_lower (hx : a ∈ accDom α r e) (hy : b ∈ α) (hr : pair b a ∈ r) :
    b ∈ accDom α r e :=
  have ⟨u, hu, hxu⟩ := mem_sUnion_image.mp hx
  mem_sUnion_image.mpr ⟨u, hu, (mem_sep.mp hu).2.dom_lower a hxu b hy hr⟩

theorem accGr_subset_prod (hz : c ∈ accGr α r e) :
    c ∈ prod (accDom α r e) (accBound e) :=
  have ⟨u, hu, hzu⟩ := mem_sUnion_image.mp hz
  have ⟨a, hx, b, hy, hzk⟩ := mem_prod.mp ((mem_sep.mp hu).2.graph_subset hzu)
  mem_prod.mpr ⟨a, mem_sUnion_image.mpr ⟨u, hu, hx⟩, b, hy, hzk⟩

theorem app_accGr_eq_empty (hx : a ∉ accDom α r e) :
    [zf|$(accGr α r e) a] = ∅ :=
  (eq_empty _).2 fun _ hz => by
    have ⟨w, hw, hfw, _⟩ := Aczel.mem_app.mp hz
    have ⟨b, hy, v, _, hwk⟩ := mem_prod.mp (accGr_subset_prod hw)
    rw [hwk, fst_pair] at hfw
    exact hx (by rw [← hfw]; exact hy)

theorem accGr_unfold_dom (hx : a ∈ accDom α r e) :
    [zf|$(accGr α r e) a] = accStep α r e (accGr α r e) a := by
  have ⟨u, hu, hxu⟩ := mem_sUnion_image.mp hx
  have hua := (mem_sep.mp hu).2
  rw [app_accGr_eq hu hxu, hua.graph_step a hxu]
  exact accStep_congr fun b hy hr => (app_accGr_eq hu (hua.dom_lower a hxu b hy hr)).symm

theorem accSet_subset_accDom : ∀ a ∈ accSet α r, a ∈ accDom α r e := by
  refine accSet_induction (p := fun a => a ∈ accDom α r e) fun a hx ih => ?_
  by_cases hxd : a ∈ accDom α r e
  · exact hxd
  have hlow : ∀ b ∈ α, pair b a ∈ r → b ∈ accDom α r e :=
    fun b hy hr => ih b (accSet_inv hx b hy hr) hr
  have hne : ∀ b ∈ accDom α r e, b ≠ a := fun _ hy h => hxd (h ▸ hy)
  have happ : ∀ b ∈ accDom α r e,
      [zf|$(accGr α r e ∪ [zf|fun _ : $({a}) =>
        $(accStep α r e (accGr α r e) a)]) b] = [zf|$(accGr α r e) b] := by
    intro b hy
    rw [app_union, app_lam_singleton_ne (hne b hy)]
    ext c
    simp
  have happx : [zf|$(accGr α r e ∪ [zf|fun _ : $({a}) =>
      $(accStep α r e (accGr α r e) a)]) a] =
      accStep α r e (accGr α r e) a := by
    rw [app_union, app_accGr_eq_empty hxd,
      Aczel.app_lam (mem_singleton.mpr rfl)]
    ext c
    simp
  have hdom : accDom α r e ∪ {a} ⊆ accSet α r := by
    intro c hz
    rcases mem_union.mp hz with h | h
    · exact accDom_mem_accSet h
    · rw [mem_singleton.mp h]
      exact hx
  have hgr : accGr α r e ∪ [zf|fun _ : $({a}) => $(accStep α r e (accGr α r e) a)] ⊆
      prod (accDom α r e ∪ {a}) (accBound e) := by
    intro c hz
    rcases mem_union.mp hz with h | h
    · have ⟨u, hu, v, hv, hzk⟩ := mem_prod.mp (accGr_subset_prod h)
      exact mem_prod.mpr ⟨u, mem_union.mpr (.inl hu), v, hv, hzk⟩
    · have ⟨u, hu, v, hv, hzk⟩ := Aczel.mem_lam.mp h
      refine mem_prod.mpr ⟨u, mem_union.mpr (.inr hu), v, ?_, hzk⟩
      exact accStep_subset_accBound hv
  refine mem_sUnion_image.mpr ⟨pair (accDom α r e ∪ {a})
    (accGr α r e ∪ [zf|fun _ : $({a}) => $(accStep α r e (accGr α r e) a)]),
    mem_sep.mpr ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact mem_prod.mpr ⟨_, mem_powerset.mpr hdom, _,
      mem_powerset.mpr fun c hz =>
        have ⟨u, hu, v, hv, hzk⟩ := mem_prod.mp (hgr hz)
        mem_prod.mpr ⟨u, hdom hu, v, hv, hzk⟩, rfl⟩
  · rw [fst_pair]
    exact hdom
  · intro x hx b hb hr
    rw [fst_pair] at hx ⊢
    rcases mem_union.mp hx with h | h
    · exact mem_union.mpr (.inl (accDom_lower h hb hr))
    · rw [mem_singleton.mp h] at hr
      exact mem_union.mpr (.inl (hlow b hb hr))
  · rw [fst_pair, snd_pair]
    exact hgr
  · simp only [fst_pair, snd_pair]
    intro c hz
    rcases mem_union.mp hz with h | h
    · rw [happ c h, accGr_unfold_dom h]
      exact accStep_congr fun b hy hr => (happ b (accDom_lower h hy hr)).symm
    · rw [mem_singleton.mp h, happx]
      exact accStep_congr fun b hy hr => (happ b (hlow b hy hr)).symm
  · simp

theorem accGr_unfold (hx : a₂ ∈ accSet α r) :
    [zf|$(accGr α r e) a₂] = [zf|e a₂ ∅
      $([zf|fun (a₁ : α) (_proof : $(truthOf r [zf|(a₁, a₂)])) =>
        $(accGr α r e) a₁])] :=
  accGr_unfold_dom (accSet_subset_accDom a₂ hx)

theorem accGr_mem
    (he : ∀ a₂ ∈ accSet α r,
      (∀ a₁ ∈ accSet α r, pair a₁ a₂ ∈ r → [zf|$(accGr α r e) a₁] ∈ app m a₁) →
      [zf|e a₂ ∅ $([zf|fun (a₁ : α)(_proof : $(truthOf r [zf|(a₁, a₂)])) =>
        $(accGr α r e) a₁])] ∈ app m a₂) :
    ∀ a ∈ accSet α r, [zf|$(accGr α r e) a] ∈ app m a := by
  refine accSet_induction (p := fun a => [zf|$(accGr α r e) a] ∈ app m a)
    fun a hx ih => ?_
  rw [accGr_unfold hx]
  exact he a hx ih

end ZFSet
