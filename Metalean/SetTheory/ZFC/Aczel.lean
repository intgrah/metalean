/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Function
public import Metalean.SetTheory.ZFC.Truth

@[expose] public noncomputable section

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

namespace Aczel

def app (fn x : ZFSet) : ZFSet := image snd (fn.sep fun p => fst p = x)

def lam (a : ZFSet) (fn : ZFSet → ZFSet) : ZFSet := ⋃₀ image (fun x => image (pair x) (fn x)) a

def piMap (a b : ZFSet) : ZFSet := image (fun f => lam a (ZFSet.app f)) (ZFSet.pi a b)

def pi (a : ZFSet) (fn : ZFSet → ZFSet) : ZFSet := piMap a (map fn a)

theorem mem_app {fn x z : ZFSet} : z ∈ app fn x ↔ ∃ p ∈ fn, fst p = x ∧ z = snd p := by
  rw [app, mem_image]
  exact exists_congr fun p =>
    ⟨fun ⟨hp, hz⟩ => ⟨(mem_sep.mp hp).1, (mem_sep.mp hp).2, hz.symm⟩,
      fun ⟨hp, h₂, hz⟩ => ⟨mem_sep.mpr ⟨hp, h₂⟩, hz.symm⟩⟩

theorem mem_lam {a z : ZFSet} {fn : ZFSet → ZFSet} :
    z ∈ lam a fn ↔ ∃ x ∈ a, ∃ y ∈ fn x, z = pair x y :=
  mem_sUnion_image.trans (exists_congr fun _ => and_congr_right fun _ => mem_image')

theorem app_lam {a x : ZFSet} {fn : ZFSet → ZFSet} (hx : x ∈ a) :
    app (lam a fn) x = fn x := by
  ext z
  rw [mem_app]
  constructor
  · rintro ⟨p, hp, hfst, rfl⟩
    obtain ⟨x', hx', y, hy, rfl⟩ := mem_lam.mp hp
    rw [fst_pair] at hfst
    subst hfst
    simpa using hy
  · intro hz
    exact ⟨pair x z, mem_lam.mpr ⟨x, hx, z, hz, rfl⟩, by simp, by simp⟩

theorem lam_congr {a : ZFSet} {f g : ZFSet → ZFSet}
    (h : ∀ x ∈ a, f x = g x) : lam a f = lam a g := by
  ext z
  rw [mem_lam, mem_lam]
  exact exists_congr fun x => and_congr_right fun hx => by rw [h x hx]

theorem pi_congr {a : ZFSet} {f g : ZFSet → ZFSet}
    (h : ∀ x ∈ a, f x = g x) : pi a f = pi a g :=
  congrArg (piMap a) (map_congr h)

theorem mem_piMap {a b z : ZFSet} :
    z ∈ piMap a b ↔ ∃ f ∈ ZFSet.pi a b, z = lam a (ZFSet.app f) :=
  mem_image'

theorem lam_mem_piMap {a b : ZFSet} {fn : ZFSet → ZFSet}
    (hb : ∀ x ∈ a, fn x ∈ ZFSet.app b x) : lam a fn ∈ piMap a b :=
  mem_piMap.mpr ⟨map fn a, map_mem_pi hb,
    lam_congr fun _ hx => (app_map hx).symm⟩

theorem app_mem {a b fn x : ZFSet} (hf : fn ∈ piMap a b) (hx : x ∈ a) : app fn x ∈ ZFSet.app b x := by
  obtain ⟨g, hg, rfl⟩ := mem_piMap.mp hf
  rw [app_lam hx]
  exact app_mem_of_mem_pi hg hx

theorem app_empty (x : ZFSet) : app ∅ x = ∅ :=
  (eq_empty _).2 fun z hz => by
    have ⟨p, hp, _⟩ := mem_app.mp hz
    simp at hp

theorem lam_app {a b fn : ZFSet} (hf : fn ∈ piMap a b) : lam a (app fn) = fn := by
  obtain ⟨g, _, rfl⟩ := mem_piMap.mp hf
  exact lam_congr fun _ hx => app_lam hx

theorem piMap_mono_cod {a b b' : ZFSet} (hb : ∀ x ∈ a, ZFSet.app b x ⊆ ZFSet.app b' x) :
    piMap a b ⊆ piMap a b' := fun f hf => by
  rw [← lam_app hf]
  exact lam_mem_piMap fun x hx => hb x hx (app_mem hf hx)

theorem piMap_inter {a b b' c fn : ZFSet} (hf : fn ∈ piMap a b) (hf' : fn ∈ piMap a b')
    (h : ∀ x ∈ a, ∀ z, z ∈ ZFSet.app b x → z ∈ ZFSet.app b' x → z ∈ ZFSet.app c x) : fn ∈ piMap a c := by
  rw [← lam_app hf]
  exact lam_mem_piMap fun x hx => h x hx _ (app_mem hf hx) (app_mem hf' hx)

theorem lam_eq_empty {a : ZFSet} {fn : ZFSet → ZFSet} (h : ∀ x ∈ a, fn x = ∅) :
    lam a fn = ∅ :=
  (eq_empty _).2 fun _ hz =>
    have ⟨x, hx, _, hy, _⟩ := mem_lam.mp hz
    notMem_empty _ (h x hx ▸ hy)

theorem piMap_mem_truth {a b : ZFSet} (hb : ∀ x ∈ a, ZFSet.app b x ∈ truth) :
    piMap a b ∈ truth := by
  rw [mem_powerset]
  intro w hw
  obtain ⟨f, hf, rfl⟩ := mem_piMap.mp hw
  refine mem_verum.mpr (lam_eq_empty fun x hx => ?_)
  have hmem := app_mem_of_mem_pi hf hx
  rcases mem_truth.mp (hb x hx) with he | he
  · simp [he, falsum] at hmem
  · rw [he] at hmem
    exact mem_verum.mp hmem

theorem pi_truth_id_eq_falsum : pi truth (fun x => x) = falsum :=
  (eq_empty _).2 fun z hz => by
    rw [pi] at hz
    obtain ⟨f, hf, _⟩ := mem_piMap.mp hz
    have hmem := app_mem_of_mem_pi hf falsum_mem_truth
    rw [app_map falsum_mem_truth, falsum] at hmem
    exact notMem_empty _ hmem

end Aczel

def branch (c a b : ZFSet) : ZFSet := fibreOp (image (pair falsum) a ∪ image (pair verum) b) c

@[simp] theorem branch_falsum (a b : ZFSet) : branch falsum a b = a := by
  ext
  simp [branch, eq_comm]

@[simp] theorem branch_verum (a b : ZFSet) : branch verum a b = b := by
  ext
  simp [branch]

def squash (s : ZFSet) : ZFSet := image (fun _ => proof) s

theorem mem_squash {s z : ZFSet} : z ∈ squash s ↔ ∃ w, w ∈ s ∧ z = proof :=
  mem_image'

theorem proof_mem_squash {s x : ZFSet} (hx : x ∈ s) : proof ∈ squash s :=
  mem_squash.mpr ⟨x, hx, rfl⟩

theorem squash_eq_verum {s x : ZFSet} (hx : x ∈ s) : squash s = verum := by
  ext
  rw [mem_squash, mem_verum]
  exact ⟨fun ⟨_, _, hz⟩ => hz, fun hz => ⟨x, hx, hz⟩⟩

@[simp] theorem squash_falsum : squash falsum = falsum :=
  (eq_empty _).2 fun _ hz =>
    have ⟨_, hw, _⟩ := mem_squash.mp hz
    notMem_empty _ hw

theorem squash_mem_truth (s : ZFSet) : squash s ∈ truth :=
  mem_powerset.mpr fun _ hw =>
    have ⟨_, _, hz⟩ := mem_squash.mp hw
    mem_verum.mpr hz

end ZFSet
