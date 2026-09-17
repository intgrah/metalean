/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Batteries.Data.Fin.Coding
public import Metalean.SetSemantics.ConstructorValue
public import Metalean.SetTheory.ZFC.FixedPoint

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {n m level : Nat} {nctors : Fin m → Nat} {s : Fin m} {c : Fin (nctors s)}
  {block blockW bound motive step graph minors z vargs : ZFSet}
  {γ : Slots n} {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
  {args : CtorCode n → ZFSet}
  {emit val : CtorCode n → Nat → ZFSet → ZFSet}

def tagOf (s : Fin m) (c : Fin (nctors s)) : Nat :=
  (Fin.encodeSigma nctors ⟨s, c⟩).val

theorem tagOf_injective {s₁ s₂ : Fin m} {c₁ : Fin (nctors s₁)} {c₂ : Fin (nctors s₂)}
    (h : tagOf s₁ c₁ = tagOf s₂ c₂) :
    (⟨s₁, c₁⟩ : (s : Fin m) × Fin (nctors s)) = ⟨s₂, c₂⟩ := by
  simpa using congrArg (Fin.decodeSigma nctors)
    (Fin.ext h : Fin.encodeSigma nctors ⟨s₁, c₁⟩ = Fin.encodeSigma nctors ⟨s₂, c₂⟩)

noncomputable def tagGraph (args : CtorCode.{u} n → ZFSet.{u})
    (emit : CtorCode.{u} n → Nat → ZFSet.{u} → ZFSet.{u})
    (codes : (s : Fin m) → Fin (nctors s) → CtorCode.{u} n) : ZFSet.{u} :=
  ⋃₀ range fun s => ⋃₀ range fun c =>
    image (emit (codes s c) (tagOf s c)) (args (codes s c))

theorem mem_tagGraph :
    z ∈ tagGraph args emit codes ↔
      ∃ s c, ∃ vargs ∈ args (codes s c), emit (codes s c) (tagOf s c) vargs = z := by
  simp [tagGraph]

noncomputable def pairGraph (γ : Slots n) (args : CtorCode n → ZFSet)
    (val : CtorCode n → Nat → ZFSet → ZFSet) :
    ((s : Fin m) → Fin (nctors s) → CtorCode n) → ZFSet :=
  tagGraph args fun code tag vargs =>
    [zf|($(entry (code.targetIndex γ vargs) tag vargs), $(val code tag vargs))]

theorem pairGraph_pair (hz : z ∈ pairGraph γ args val codes) :
    ∃ x y, z = [zf|(x, y)] := by
  have ⟨_, _, _, _, heq⟩ := mem_tagGraph.mp hz
  exact ⟨_, _, heq.symm⟩

theorem pairGraph_unique {x t₁ t₂ : ZFSet}
    (h₁ : [zf|(x, t₁)] ∈ pairGraph γ args val codes)
    (h₂ : [zf|(x, t₂)] ∈ pairGraph γ args val codes) : t₁ = t₂ := by
  have ⟨_, _, _, _, heq₁⟩ := mem_tagGraph.mp h₁
  have ⟨_, _, _, _, heq₂⟩ := mem_tagGraph.mp h₂
  have ⟨hkey₁, hval₁⟩ := pair_inj.mp heq₁
  have ⟨hkey₂, hval₂⟩ := pair_inj.mp heq₂
  have hentry := hkey₁.trans hkey₂.symm
  cases tagOf_injective (entry_tag_eq hentry)
  cases entry_args_eq hentry
  exact hval₁.symm.trans hval₂

theorem pairGraph_isFunc :
    IsFunc (dom (pairGraph γ args val codes))
      (image snd (pairGraph γ args val codes)) (pairGraph γ args val codes) :=
  isFunc_dom_image_snd (fun _ hz => pairGraph_pair hz)
    fun _ _ _ h h' => pairGraph_unique h h'

theorem app_pairGraph (hargs : vargs ∈ args (codes s c)) :
    app (pairGraph γ args val codes)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs) =
      val (codes s c) (tagOf s c) vargs :=
  pairGraph_isFunc.app_eq (mem_tagGraph.mpr ⟨s, c, vargs, hargs, rfl⟩)

noncomputable def indOp (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (γ : Slots n) (block : ZFSet) : ZFSet :=
  tagGraph (fun code => code.argSet block γ)
    (fun code tag vargs => entry (code.targetIndex γ vargs) tag vargs) codes

theorem mem_indOp :
    z ∈ indOp codes γ block ↔
      ∃ s c, ∃ vargs ∈ (codes s c).argSet block γ,
        entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs = z :=
  mem_tagGraph

noncomputable def blockPredecessorRel (block : ZFSet) (γ : Slots n)
    (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) : ZFSet :=
  ⋃₀ tagGraph (fun code => code.argSet block γ)
    (fun code tag vargs => image
      (fun predecessor => [zf|(predecessor, $(entry (code.targetIndex γ vargs) tag vargs))])
      (code.predecessors γ vargs))
    codes

theorem mem_blockPredecessorRel {predecessor current : ZFSet} :
    [zf|(predecessor, current)] ∈ blockPredecessorRel block γ codes ↔
      ∃ s c, ∃ vargs ∈ (codes s c).argSet block γ,
        predecessor ∈ (codes s c).predecessors γ vargs ∧
        current = entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs := by
  constructor
  · intro h
    have ⟨edges, hedges, hedge⟩ := mem_sUnion.mp h
    obtain ⟨s, c, vargs, hargs, rfl⟩ := mem_tagGraph.mp hedges
    have ⟨_, hpredecessor, heq⟩ := mem_image.mp hedge
    have ⟨rfl, rfl⟩ := pair_inj.mp heq
    exact ⟨s, c, vargs, hargs, hpredecessor, rfl⟩
  · intro ⟨s, c, vargs, hargs, hpredecessor, hcurrent⟩
    rw [hcurrent]
    exact mem_sUnion.mpr ⟨_, mem_tagGraph.mpr ⟨s, c, vargs, hargs, rfl⟩,
      mem_image.mpr ⟨predecessor, hpredecessor, rfl⟩⟩

theorem mem_indOp_inter {block₁ block₂ : ZFSet}
    (hz₁ : z ∈ indOp codes γ block₁)
    (hz₂ : z ∈ indOp codes γ block₂) :
    ∃ s c, ∃ vargs ∈ (codes s c).argSet block₁ γ,
      vargs ∈ (codes s c).argSet block₂ γ ∧
        entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs = z := by
  obtain ⟨_, _, _, hargs₁, rfl⟩ := mem_indOp.mp hz₁
  have ⟨_, _, _, hargs₂, heq⟩ := mem_indOp.mp hz₂
  cases tagOf_injective (entry_tag_eq heq)
  cases entry_args_eq heq
  exact ⟨_, _, _, hargs₁, hargs₂, rfl⟩

theorem indOp_mono {block₁ block₂ : ZFSet} (h : block₁ ⊆ block₂) :
    indOp codes γ block₁ ⊆ indOp codes γ block₂ := fun _ hz =>
  have ⟨s, c, vargs, hargs, heq⟩ := mem_indOp.mp hz
  mem_indOp.mpr ⟨s, c, vargs, CtorCode.argSet_mono h _ γ hargs, heq⟩

noncomputable def indSet
    (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) (bound : ZFSet) (γ : Slots n) : ZFSet :=
  lfp bound (indOp codes γ)

noncomputable def blockMapGraph (block graph : ZFSet) (γ : Slots n) :
    ((s : Fin m) → Fin (nctors s) → CtorCode n) → ZFSet :=
  pairGraph γ (fun code => code.argSet block γ)
    fun code tag vargs =>
      entry (code.targetIndex γ (code.argMap graph γ vargs)) tag (code.argMap graph γ vargs)

noncomputable def stepGraph (level : Nat) (block motive : ZFSet) (γ : Slots n)
    (minors : ZFSet) : ((s : Fin m) → Fin (nctors s) → CtorCode n) → ZFSet :=
  pairGraph γ (fun code => code.ihArgSet block motive γ)
    fun code tag vargs => code.applyMinor level γ [zf|minors $(encode tag)] vargs

theorem indOp_inter {block₁ block₂ : ZFSet}
    (hw : ∀ value, value ∈ block₁ → value ∈ block₂ → value ∈ blockW)
    (hz₁ : z ∈ indOp codes γ block₁) (hz₂ : z ∈ indOp codes γ block₂) :
    z ∈ indOp codes γ blockW := by
  obtain ⟨s, c, vargs, hargs₁, hargs₂, rfl⟩ := mem_indOp_inter hz₁ hz₂
  exact mem_indOp.mpr ⟨s, c, vargs, CtorCode.argSet_inter hw _ γ vargs hargs₁ hargs₂, rfl⟩

theorem app_blockMapGraph (hargs : vargs ∈ (codes s c).argSet block γ) :
    app (blockMapGraph block graph γ codes)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs) =
      entry ((codes s c).targetIndex γ ((codes s c).argMap graph γ vargs)) (tagOf s c)
        ((codes s c).argMap graph γ vargs) :=
  app_pairGraph hargs

theorem blockMapGraph_app_cand {block₁ block₂ : ZFSet}
    (hz₁ : z ∈ indOp codes γ block₁) (hz₂ : z ∈ indOp codes γ block₂) :
    app (blockMapGraph block₁ graph γ codes) z = app (blockMapGraph block₂ graph γ codes) z := by
  obtain ⟨_, _, _, hargs₁, hargs₂, rfl⟩ := mem_indOp_inter hz₁ hz₂
  rw [app_blockMapGraph hargs₁, app_blockMapGraph hargs₂]

theorem blockMapGraph_app_congr {inner outer graph₁ graph₂ : ZFSet}
    (hagree : ∀ value ∈ inner, app graph₁ value = app graph₂ value)
    (hinner : z ∈ indOp codes γ inner) (houter : z ∈ indOp codes γ outer) :
    app (blockMapGraph outer graph₁ γ codes) z = app (blockMapGraph outer graph₂ γ codes) z := by
  obtain ⟨_, _, vargs, hinnerArgs, hargs, rfl⟩ := mem_indOp_inter hinner houter
  rw [app_blockMapGraph hargs, app_blockMapGraph hargs,
    CtorCode.argMap_congr hagree _ γ vargs hinnerArgs]

def StepSound (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (block motive step : ZFSet) (γ : Slots n) : Prop :=
  ∀ s c, ∀ vargs ∈ (codes s c).ihArgSet block motive γ,
  app step (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)
    ∈ fibreOp motive
      (entry ((codes s c).targetIndex γ ((codes s c).forgetIhs vargs)) (tagOf s c)
        ((codes s c).forgetIhs vargs))

theorem snd_mem_sUnion_sUnion {carrier key value : ZFSet} (h : [zf|(key, value)] ∈ carrier) :
    value ∈ ⋃₀ ⋃₀ carrier :=
  mem_sUnion.mpr
    ⟨{key, value}, mem_sUnion.mpr ⟨[zf|(key, value)], h, by simp [pair]⟩, by simp⟩

noncomputable def motiveFamily (motive domain : ZFSet) : ZFSet :=
  map (fibreOp motive) domain

structure IsApprox (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (bound motive step graph : ZFSet)
    (γ : Slots n) : Prop where
  isFunction : graph ∈ pi (dom graph) (motiveFamily motive (dom graph))
  memBlock : ∀ value ∈ dom graph, value ∈ indSet codes bound γ
  closed : ∀ value ∈ dom graph, value ∈ indOp codes γ (dom graph)
  appEq : ∀ value ∈ dom graph,
    app graph value
      = app step (app (blockMapGraph (indSet codes bound γ) graph γ codes) value)

noncomputable def approxSet (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (bound motive step : ZFSet)
    (γ : Slots n) : ZFSet :=
  (powerset (prod (indSet codes bound γ) (⋃₀ ⋃₀ motive))).sep
    (IsApprox codes bound motive step · γ)

noncomputable def recGraph (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (bound motive step : ZFSet)
    (γ : Slots n) : ZFSet :=
  ⋃₀ approxSet codes bound motive step γ

theorem indOp_monotoneOn {bound : ZFSet} :
    MonotoneOn (indOp codes γ) (Set.Iic bound) :=
  fun _ _ _ _ h => indOp_mono h

theorem indSet_unfold {bound : ZFSet}
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound)) :
    indOp codes γ (indSet codes bound γ) = indSet codes bound γ :=
  lfp_fixed hmaps indOp_monotoneOn

theorem IsApprox.agree {bound motive step graph₁ graph₂ : ZFSet}
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hg₁ : IsApprox codes bound motive step graph₁ γ)
    (hg₂ : IsApprox codes bound motive step graph₂ γ) (value : ZFSet)
    (hvalue : value ∈ indSet codes bound γ) (hd₁ : value ∈ dom graph₁)
    (hd₂ : value ∈ dom graph₂) : app graph₁ value = app graph₂ value := by
  have key : indSet codes bound γ ⊆
      bound.sep fun z => z ∈ dom graph₁ → z ∈ dom graph₂ → app graph₁ z = app graph₂ z := by
    refine lfp_least (fun _ hz => (mem_sep.mp hz).1) fun z hz => ?_
    refine mem_sep.mpr ⟨hmaps (fun _ hw => (mem_sep.mp hw).1) hz, fun hzg₁ hzg₂ => ?_⟩
    have h₁ := indOp_inter (fun _ hw hw' => mem_sep.mpr ⟨hw, hw'⟩) hz (hg₁.closed z hzg₁)
    have h₂ := indOp_inter (fun _ hw hw' => mem_sep.mpr ⟨hw, hw'⟩) h₁ (hg₂.closed z hzg₂)
    have hagree : ∀ w ∈ ((bound.sep fun z =>
        z ∈ dom graph₁ → z ∈ dom graph₂ → app graph₁ z = app graph₂ z).sep
        fun w => w ∈ dom graph₁).sep fun w => w ∈ dom graph₂,
        app graph₁ w = app graph₂ w := by
      intro w hw
      have ⟨hw1, hw2⟩ := mem_sep.mp hw
      have ⟨hw3, hw4⟩ := mem_sep.mp hw1
      exact (mem_sep.mp hw3).2 hw4 hw2
    rw [hg₁.appEq z hzg₁, hg₂.appEq z hzg₂]
    refine congrArg _ (blockMapGraph_app_congr hagree h₂ ?_)
    rw [indSet_unfold hmaps]
    exact hg₁.memBlock z hzg₁
  exact (mem_sep.mp (key hvalue)).2 hd₁ hd₂

theorem IsApprox.app_eq {bound motive step graph key value : ZFSet}
    (hg : IsApprox codes bound motive step graph γ)
    (h : [zf|(key, value)] ∈ graph) : app graph key = value :=
  (mem_pi.mp hg.isFunction).1.app_eq h

theorem mem_pi_motiveFamily {motive graph : ZFSet}
    (hfunc : IsFunc (dom graph) (image (fun value => [zf|value.2]) graph) graph)
    (hpair : ∀ z ∈ graph, ∃ key value, z = [zf|(key, value)] ∧ value ∈ fibreOp motive key) :
    graph ∈ pi (dom graph) (motiveFamily motive (dom graph)) := by
  have hsigma : graph ⊆ σ (dom graph) (motiveFamily motive (dom graph)) := by
    intro z hz
    obtain ⟨key, value, rfl, hval⟩ := hpair z hz
    have hkey : key ∈ dom graph := pair_mem_dom hz
    refine mem_sigma.mpr ⟨key, hkey, value, ?_, rfl⟩
    rwa [motiveFamily, app_map hkey]
  refine mem_pi.mpr ⟨⟨?_, hfunc.2⟩, hsigma⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sigma.mp (hsigma hz)
  exact pair_mem_prod.mpr ⟨ha, mem_sUnion.mpr
    ⟨app (motiveFamily motive (dom graph)) a, mem_image.mpr ⟨a, ha, rfl⟩, hb⟩⟩

theorem recGraph_unique (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    {key value₁ value₂ : ZFSet} (h₁ : [zf|(key, value₁)] ∈ recGraph codes bound motive step γ)
    (h₂ : [zf|(key, value₂)] ∈ recGraph codes bound motive step γ) : value₁ = value₂ := by
  have ⟨graph₁, hgs₁, hkey₁⟩ := mem_sUnion.mp h₁
  have ⟨graph₂, hgs₂, hkey₂⟩ := mem_sUnion.mp h₂
  have hg₁ := (mem_sep.mp hgs₁).2
  have hg₂ := (mem_sep.mp hgs₂).2
  have hmem : key ∈ indSet codes bound γ := hg₁.memBlock key (pair_mem_dom hkey₁)
  have hagree := IsApprox.agree hmaps hg₁ hg₂ key hmem
    (pair_mem_dom hkey₁) (pair_mem_dom hkey₂)
  rwa [IsApprox.app_eq hg₁ hkey₁, IsApprox.app_eq hg₂ hkey₂] at hagree

theorem pair_of_mem_recGraph {bound motive step z : ZFSet}
    (hz : z ∈ recGraph codes bound motive step γ) :
    ∃ key value, z = [zf|(key, value)] := by
  have ⟨graph, hgs, hzg⟩ := mem_sUnion.mp hz
  obtain ⟨key, _, value, _, rfl⟩ := mem_prod.mp (mem_powerset.mp (mem_sep.mp hgs).1 hzg)
  exact ⟨key, value, rfl⟩

theorem recGraph_isFunc (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound)) :
    IsFunc (dom (recGraph codes bound motive step γ))
      (image (fun value => [zf|value.2]) (recGraph codes bound motive step γ))
      (recGraph codes bound motive step γ) :=
  isFunc_dom_image_snd (fun _ hz => pair_of_mem_recGraph hz)
    fun _ _ _ h h' => recGraph_unique hmaps h h'

theorem recGraph_app {bound motive step key value : ZFSet}
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (h : [zf|(key, value)] ∈ recGraph codes bound motive step γ) :
    app (recGraph codes bound motive step γ) key = value :=
  (recGraph_isFunc hmaps).app_eq h

theorem mem_dom_recGraph {bound motive step key : ZFSet} :
    key ∈ dom (recGraph codes bound motive step γ) ↔
      ∃ graph ∈ approxSet codes bound motive step γ, key ∈ dom graph := by
  constructor
  · intro hkey
    obtain ⟨z, hz, rfl⟩ := mem_dom.mp hkey
    have ⟨graph, hgs, hzg⟩ := mem_sUnion.mp hz
    exact ⟨graph, hgs, mem_dom.mpr ⟨z, hzg, rfl⟩⟩
  · intro ⟨graph, hgs, hkey⟩
    obtain ⟨z, hz, rfl⟩ := mem_dom.mp hkey
    exact mem_dom.mpr ⟨z, mem_sUnion.mpr ⟨graph, hgs, hz⟩, rfl⟩

theorem recGraph_app_eq {bound motive step graph : ZFSet}
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hgs : graph ∈ approxSet codes bound motive step γ) {key : ZFSet}
    (hkey : key ∈ dom graph) :
    app (recGraph codes bound motive step γ) key = app graph key := by
  have hg := (mem_sep.mp hgs).2
  obtain ⟨z, hz, rfl⟩ := mem_dom.mp hkey
  obtain ⟨a, _, b, _, rfl⟩ := mem_prod.mp (mem_powerset.mp (mem_sep.mp hgs).1 hz)
  change [zf|(a, b)] ∈ graph at hz
  change app (recGraph codes bound motive step γ) [zf|(a, b).1] =
    app graph [zf|(a, b).1]
  rw [fst_pair, recGraph_app hmaps (mem_sUnion.mpr ⟨graph, hgs, hz⟩), IsApprox.app_eq hg hz]

theorem IsApprox.app_mem {bound motive step graph key : ZFSet}
    (hg : IsApprox codes bound motive step graph γ)
    (hkey : key ∈ dom graph) : app graph key ∈ fibreOp motive key := by
  have h := app_mem_of_mem_pi hg.isFunction hkey
  rwa [motiveFamily, app_map hkey] at h

theorem recGraph_subset_prod :
    recGraph codes bound motive step γ ⊆ prod (indSet codes bound γ) (⋃₀ ⋃₀ motive) :=
  fun _ hz =>
    have ⟨_, hgs, hzg⟩ := mem_sUnion.mp hz
    mem_powerset.mp (mem_sep.mp hgs).1 hzg

theorem recGraph_isApprox (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound)) :
    IsApprox codes bound motive step (recGraph codes bound motive step γ) γ := by
  refine ⟨mem_pi_motiveFamily (recGraph_isFunc hmaps) fun z hz => ?_, ?_, ?_, ?_⟩
  · have ⟨graph, hgs, hzg⟩ := mem_sUnion.mp hz
    obtain ⟨a, _, b, _, rfl⟩ := mem_prod.mp (mem_powerset.mp (mem_sep.mp hgs).1 hzg)
    have hg := (mem_sep.mp hgs).2
    have happ := IsApprox.app_mem hg (pair_mem_dom hzg)
    rw [IsApprox.app_eq hg hzg] at happ
    exact ⟨a, b, rfl, happ⟩
  · intro w hw
    have ⟨graph, hgs, hwg⟩ := mem_dom_recGraph.mp hw
    exact (mem_sep.mp hgs).2.memBlock w hwg
  · intro key hkey
    have ⟨graph, hgs, hkg⟩ := mem_dom_recGraph.mp hkey
    exact indOp_mono (fun _ hw => mem_dom_recGraph.mpr ⟨graph, hgs, hw⟩)
      ((mem_sep.mp hgs).2.closed key hkg)
  · intro key hkey
    have ⟨graph, hgs, hkg⟩ := mem_dom_recGraph.mp hkey
    have hg := (mem_sep.mp hgs).2
    rw [recGraph_app_eq hmaps hgs hkg, hg.appEq key hkg]
    refine congrArg _ (blockMapGraph_app_congr
      (fun w hw => (recGraph_app_eq hmaps hgs hw).symm) (hg.closed key hkg) ?_)
    rw [indSet_unfold hmaps]
    exact hg.memBlock key hkg

theorem blockMapGraph_app_mem {inner outer graph motive step : ZFSet} (hsub : inner ⊆ outer)
    (hgraph : ∀ value ∈ inner, app graph value ∈ fibreOp motive value)
    (hstep : StepSound codes outer motive step γ)
    (z : ZFSet) (hz : z ∈ indOp codes γ inner) :
    app step (app (blockMapGraph inner graph γ codes) z) ∈ fibreOp motive z := by
  obtain ⟨s, c, vargs, hargs, rfl⟩ := mem_indOp.mp hz
  have hmem : (codes s c).argMap graph γ vargs ∈ (codes s c).ihArgSet outer motive γ :=
    CtorCode.ihArgSet_mono hsub motive _ γ (CtorCode.argMap_mem hgraph _ γ vargs hargs)
  have h := hstep s c _ hmem
  rw [CtorCode.forgetIhs_argMap _ γ vargs hargs] at h
  rwa [app_blockMapGraph hargs]

theorem recGraph_app_mem {bound motive step key : ZFSet}
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hkey : key ∈ dom (recGraph codes bound motive step γ)) :
    app (recGraph codes bound motive step γ) key ∈ fibreOp motive key :=
  IsApprox.app_mem (recGraph_isApprox hmaps) hkey

theorem recGraph_pair {bound motive step key : ZFSet}
    (hkey : key ∈ dom (recGraph codes bound motive step γ)) :
    ∃ value, [zf|(key, value)] ∈ recGraph codes bound motive step γ := by
  obtain ⟨q, hq, rfl⟩ := mem_dom.mp hkey
  obtain ⟨_, _, b, _, rfl⟩ := mem_prod.mp (recGraph_subset_prod hq)
  simpa using ⟨b, hq⟩

theorem dom_recGraph_eq (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hstep : StepSound codes (indSet codes bound γ) motive step γ) :
    indSet codes bound γ ⊆ dom (recGraph codes bound motive step γ) := by
  have hR : IsApprox codes bound motive step (recGraph codes bound motive step γ) γ :=
    recGraph_isApprox hmaps
  refine lfp_least (fun _ hw => lfp_subset (hR.memBlock _ hw)) fun z hz => ?_
  by_cases hzd : z ∈ dom (recGraph codes bound motive step γ)
  · exact hzd
  set graph := recGraph codes bound motive step γ
  have hzI : z ∈ indSet codes bound γ := by
    have h : z ∈ indOp codes γ (indSet codes bound γ) :=
      indOp_mono hR.memBlock hz
    rwa [indSet_unfold hmaps] at h
  set value := app step (app (blockMapGraph (dom graph) graph γ codes) z) with hvalue
  have hval : value ∈ fibreOp motive z :=
    blockMapGraph_app_mem (fun _ hw => hR.memBlock _ hw)
      (fun _ hx => recGraph_app_mem hmaps hx) hstep z hz
  set extended := graph ∪ {[zf|(z, value)]} with hext
  have hfunc : IsFunc (dom extended) (image (fun value => [zf|value.2]) extended) extended := by
    refine isFunc_dom_image_snd (fun q hq => ?_) fun x t t' hxt ht' => ?_
    · rcases mem_union.mp hq with h | h
      · exact pair_of_mem_recGraph h
      · rw [mem_singleton.mp h]
        exact ⟨_, _, rfl⟩
    · rcases mem_union.mp hxt with h | h
      · rcases mem_union.mp ht' with h' | h'
        · exact recGraph_unique hmaps h h'
        · exact absurd ((pair_inj.mp (mem_singleton.mp h')).1 ▸ pair_mem_dom h) hzd
      · obtain ⟨rfl, ht⟩ := pair_inj.mp (mem_singleton.mp h)
        rcases mem_union.mp ht' with h' | h'
        · exact absurd (pair_mem_dom h') hzd
        · exact ht.trans (pair_inj.mp (mem_singleton.mp h')).2.symm
  have hmemz : [zf|(z, value)] ∈ extended := mem_union.mpr (.inr (mem_singleton.mpr rfl))
  have hzdom : z ∈ dom extended := pair_mem_dom hmemz
  have hsubdom : dom graph ⊆ dom extended := fun x hx => by
    have ⟨t, hxt⟩ := recGraph_pair hx
    exact pair_mem_dom (mem_union.mpr (.inl hxt))
  have happ : ∀ x ∈ dom graph, app extended x = app graph x := fun x hx => by
    have ⟨t, hxt⟩ := recGraph_pair hx
    rw [hfunc.app_eq (mem_union.mpr (.inl hxt)), recGraph_app hmaps hxt]
  have happz : app extended z = value := hfunc.app_eq hmemz
  have hdomeq : ∀ x ∈ dom extended, x ∈ dom graph ∨ x = z := fun x hx => by
    obtain ⟨q, hq, rfl⟩ := mem_dom.mp hx
    rcases mem_union.mp hq with h | h
    · exact .inl (mem_dom.mpr ⟨q, h, rfl⟩)
    · simp [mem_singleton.mp h]
  refine mem_dom_recGraph.mpr ⟨extended, mem_sep.mpr ⟨mem_powerset.mpr ?_, ?_, ?_, ?_, ?_⟩,
    hzdom⟩
  · intro q hq
    rcases mem_union.mp hq with h | h
    · exact recGraph_subset_prod h
    · rw [mem_singleton.mp h]
      exact mem_prod.mpr ⟨z, hzI, value, snd_mem_sUnion_sUnion (mem_fibre.mp hval), rfl⟩
  · refine mem_pi_motiveFamily hfunc fun q hq => ?_
    rcases mem_union.mp hq with h | h
    · obtain ⟨a, _, b, _, rfl⟩ := mem_prod.mp (recGraph_subset_prod h)
      have hv := recGraph_app_mem hmaps (pair_mem_dom h)
      rw [recGraph_app hmaps h] at hv
      exact ⟨a, b, rfl, hv⟩
    · exact ⟨z, value, mem_singleton.mp h, hval⟩
  · intro w hw
    rcases hdomeq w hw with h | rfl
    · exact hR.memBlock w h
    · exact hzI
  · intro x hx
    rcases hdomeq x hx with h | rfl
    · exact indOp_mono hsubdom (hR.closed x h)
    · exact indOp_mono hsubdom hz
  · intro x hx
    rcases hdomeq x hx with h | rfl
    · rw [happ x h, hR.appEq x h]
      refine congrArg _ (blockMapGraph_app_congr (fun w hw => (happ w hw).symm)
        (hR.closed x h) ?_)
      rw [indSet_unfold hmaps]
      exact hR.memBlock x h
    · have hzIop : x ∈ indOp codes γ (indSet codes bound γ) := by
        rwa [indSet_unfold hmaps]
      rw [happz, hvalue]
      exact congrArg _ ((blockMapGraph_app_cand hz hzIop).trans
        (blockMapGraph_app_congr (fun w hw => (happ w hw).symm) hz hzIop))

end Metalean
