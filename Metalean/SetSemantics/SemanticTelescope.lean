/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.SuccPred
public import Metalean.Meta.ZF
public import Metalean.Tele

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

abbrev Slots (n : Nat) : Type (u + 1) := Fin n → ZFSet.{u}
abbrev Dom (n : Nat) : Type (u + 1) := Slots n → ZFSet.{u}
abbrev DomAt (n : Nat) : Type (u + 1) := Slots n → ZFSet.{u} → ZFSet.{u}
abbrev SemTele := Tele Dom

namespace Slots

abbrev snoc {n : Nat} (s : Slots n) (x : ZFSet) : Slots (n + 1) :=
  Fin.snoc s x

theorem natAdd_snoc {a k : Nat} (γ : Slots (a + k)) (value : ZFSet) :
    (fun f : Fin (k + 1) => γ.snoc value (Fin.natAdd a f)) =
      Fin.snoc (fun f : Fin k => γ (Fin.natAdd a f)) value := by
  simpa [Function.comp_def] using Fin.snoc_comp_natAdd (f := γ) (a := value)

theorem natAdd_eq_snoc {a k : Nat} (γ : Slots (a + k + 1)) :
    (fun f : Fin (k + 1) => γ (Fin.natAdd a f)) =
      Fin.snoc (fun f : Fin k => Fin.init γ (Fin.natAdd a f))
        (γ (Fin.last (a + k))) := by
  rw [← Fin.snoc_init_self γ]
  simpa [Function.comp_def] using
    Fin.snoc_comp_natAdd (f := Fin.init γ) (a := γ (Fin.last (a + k)))

def pull {a a₁ count : Nat} (project : Slots a₁ → Slots a)
    (γ : Slots (a₁ + count)) : Slots (a + count) :=
  Fin.addCases (project fun base => γ (base.castAdd count))
    fun f => γ (f.natAdd a₁)

@[simp] theorem pull_append {a a₁ count : Nat}
    (project : Slots a₁ → Slots a) (base : Slots a₁)
    (tail : Slots count) :
    pull project (Fin.append base tail) = Fin.append (project base) tail := by
  funext slot
  cases slot using Fin.addCases <;> simp [pull]

@[simp] theorem pull_castAdd {a a₁ count : Nat}
    (project : Slots a₁ → Slots a) (γ : Slots (a₁ + count)) (base : Fin a) :
    pull project γ (base.castAdd count) =
      project (fun base => γ (base.castAdd count)) base := by
  simp [pull]

@[simp] theorem pull_natAdd {a a₁ count : Nat}
    (project : Slots a₁ → Slots a) (γ : Slots (a₁ + count)) (f : Fin count) :
    pull project γ (Fin.natAdd a f) = γ (Fin.natAdd a₁ f) := by
  simp [pull]

@[simp] theorem pull_zero {a a₁ : Nat} (project : Slots a₁ → Slots a)
    (γ : Slots a₁) : pull (count := 0) project γ = project γ := by
  funext slot
  cases slot using Fin.addCases with
  | left base =>
    rw [pull, Fin.addCases_left]
    apply congrArg fun current => project current base
    funext current
    rfl
  | right field => nomatch field

@[simp] theorem pull_init {a a₁ count : Nat}
    (project : Slots a₁ → Slots a) (γ : Slots (a₁ + count + 1)) :
    Fin.init (pull (count := count + 1) project γ) =
      pull (count := count) project (Fin.init γ) := by
  funext slot
  cases slot using Fin.addCases with
  | left base =>
    simp [Fin.init, pull,
      show (base.castAdd count).castSucc = base.castAdd (count + 1) from rfl]
    rfl
  | right field =>
    simp [Fin.init, pull,
      show (Fin.natAdd a field).castSucc = Fin.natAdd a field.castSucc from rfl]

@[simp] theorem pull_last {a a₁ count : Nat}
    (project : Slots a₁ → Slots a) (γ : Slots (a₁ + count + 1)) :
    pull (count := count + 1) project γ (Fin.last (a + count)) =
      γ (Fin.last (a₁ + count)) := by
  rw [show Fin.last (a + count) = Fin.natAdd a (Fin.last count) from
    rfl, pull, Fin.addCases_right]
  rfl

@[simp] theorem pull_snoc {a a₁ count : Nat}
    (project : Slots a₁ → Slots a) (γ : Slots (a₁ + count))
    (value : ZFSet) :
    pull (count := count + 1) project (γ.snoc value) =
      (pull (count := count) project γ).snoc value :=
  (Fin.snoc_init_self _).symm.trans (by simp)

end Slots

namespace SemTele

variable {a b : Nat}

noncomputable def pull {a₁ : Nat} (project : Slots a₁ → Slots a) :
    (count : Nat) → SemTele a (a + count) → SemTele a₁ (a₁ + count)
  | 0, _ => .nil
  | count + 1, .snoc Δ domain =>
    (pull project count Δ).snoc fun γ =>
      domain (Slots.pull project γ)

noncomputable def ofDoms : {count : Nat} → (Fin count → Dom a) → SemTele a (a + count)
  | 0 => fun _ => .nil
  | count + 1 => fun domains =>
    (ofDoms fun i => domains i.castSucc).snoc fun γ =>
      domains (Fin.last count) fun base => γ (base.castAdd count)

noncomputable def fold (former : ZFSet → (ZFSet → ZFSet) → ZFSet) :
    Dom b → SemTele a b → Dom a :=
  Tele.foldr fun domain rest γ => former (domain γ) fun d => rest (γ.snoc d)

noncomputable def foldAt (former : ZFSet → (ZFSet → ZFSet) → ZFSet) :
    DomAt b → SemTele a b → DomAt a :=
  Tele.foldr fun domain rest γ f =>
    former (domain γ) fun d => rest (γ.snoc d) [zf|f d]

noncomputable def pi : Dom b → SemTele a b → Dom a := fold Aczel.pi
noncomputable def lam : Dom b → SemTele a b → Dom a := fold Aczel.lam
noncomputable def piAt : DomAt b → SemTele a b → DomAt a := foldAt Aczel.pi
noncomputable def lamAt : DomAt b → SemTele a b → DomAt a := foldAt Aczel.lam

theorem pi_congr_base {cod₁ cod₂ : Dom b} (Δ : SemTele a b) (γ : Slots a)
    (h : ∀ final : Slots b, (fun base => final (base.castLE Δ.le)) = γ →
      cod₁ final = cod₂ final) :
    Δ.pi cod₁ γ = Δ.pi cod₂ γ := by
  induction Δ with
  | nil => exact h γ rfl
  | snoc Δ domain ih =>
    refine ih fun current hcurrent => Aczel.pi_congr fun value _ => h _ ?_
    rw [← hcurrent]
    funext base
    exact Fin.snoc_castSucc (α := fun _ => ZFSet) (p := current) (x := value)
      (i := base.castLE Δ.le)

theorem pi_base (Δ : SemTele a b) (cod : Slots a → Dom b)
    (γ : Slots a) :
    Δ.pi (fun final => cod (fun base => final (base.castLE Δ.le)) final) γ =
      Δ.pi (cod γ) γ :=
  Δ.pi_congr_base γ fun final hfinal => congrArg (fun base => cod base final) hfinal

theorem foldAt_pull {a₁ count : Nat} (former : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (project : Slots a₁ → Slots a)
    (Δ : SemTele a (a + count)) (leaf : DomAt (a + count))
    (γ : Slots a₁) (value : ZFSet) :
    foldAt former (fun final result => leaf (Slots.pull project final) result)
        (Δ.pull project count) γ value =
      foldAt former leaf Δ (project γ) value := by
  induction Δ using Tele.addInduction generalizing value with
  | nil => simp [SemTele.pull, foldAt]
  | snoc _ prior domain ih =>
    simpa [SemTele.pull, foldAt] using ih
      (leaf := fun final result =>
        former (domain final) fun field => leaf (final.snoc field) [zf|result field]) value

theorem piAt_pull {a₁ count : Nat} (project : Slots a₁ → Slots a)
    (Δ : SemTele a (a + count)) (leaf : DomAt (a + count))
    (γ : Slots a₁) (value : ZFSet) :
    (Δ.pull project count).piAt
        (fun final result => leaf (Slots.pull project final) result)
        γ value =
      Δ.piAt leaf (project γ) value :=
  foldAt_pull Aczel.pi project Δ leaf γ value

theorem lamAt_pull {a₁ count : Nat} (project : Slots a₁ → Slots a)
    (Δ : SemTele a (a + count)) (leaf : DomAt (a + count))
    (γ : Slots a₁) (value : ZFSet) :
    (Δ.pull project count).lamAt
        (fun final result => leaf (Slots.pull project final) result)
        γ value =
      Δ.lamAt leaf (project γ) value :=
  foldAt_pull Aczel.lam project Δ leaf γ value

noncomputable def collect : DomAt b → SemTele a b → DomAt a :=
  foldAt fun domain rest => ⋃₀ image rest domain

noncomputable def support : Dom b → SemTele a b → Dom a :=
  fold fun domain rest => σ domain (map rest domain)

noncomputable def readSupport :
    (Slots b → ZFSet → ZFSet → ZFSet) → SemTele a b →
    Slots a → ZFSet → ZFSet → ZFSet :=
  Tele.foldr (S := fun scope => Slots scope → ZFSet → ZFSet → ZFSet)
    fun _ rest γ value address =>
      rest (γ.snoc (fst address)) [zf|value address.1] (snd address)

theorem pi_replace {source target address : Dom b}
    {read : Slots b → ZFSet → ZFSet → ZFSet} (Δ : SemTele a b)
    (P : ZFSet → Prop)
    (hleaf : ∀ (γ : Slots b) (value : ZFSet), value ∈ source γ →
      (∀ point ∈ address γ, P (read γ value point)) →
      value ∈ target γ)
    (γ : Slots a) (value : ZFSet) (hvalue : value ∈ Δ.pi source γ)
    (hread : ∀ point ∈ Δ.support address γ,
      P (Δ.readSupport read γ value point)) :
    value ∈ Δ.pi target γ := by
  induction Δ with
  | nil =>
    exact hleaf γ value hvalue (by simpa [support, readSupport, fold] using hread)
  | @snoc c Δ domain ih =>
    refine ih
      (source := fun current =>
        [zf|(argument : $(domain current)) → $(source (current.snoc argument))])
      (target := fun current =>
        [zf|(argument : $(domain current)) → $(target (current.snoc argument))])
      (address := fun current => σ (domain current)
        (map (fun argument => address (current.snoc argument)) (domain current)))
      (read := fun current function point =>
        read (current.snoc (fst point)) [zf|function point.1] (snd point))
      ?_
      (by simpa [pi, fold] using hvalue)
      (by simpa [support, readSupport, fold] using hread)
    intro current function hfunction hpoints
    rw [← Aczel.lam_app hfunction]
    refine Aczel.lam_mem_piMap fun argument hargument => ?_
    rw [app_map hargument]
    refine hleaf (current.snoc argument) [zf|function argument]
      (by
        have happ := Aczel.app_mem hfunction hargument
        rwa [app_map hargument] at happ) ?_
    intro point hpoint
    simpa using hpoints (pair argument point) (mem_sigma.mpr
      ⟨argument, hargument, point, by rwa [app_map hargument], rfl⟩)

theorem collect_property {leaf : DomAt b} {domain : Dom b} (Δ : SemTele a b)
    (P : ZFSet → Prop)
    (hleaf : ∀ (γ : Slots b) (value : ZFSet), value ∈ domain γ →
      ∀ result ∈ leaf γ value, P result)
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ Δ.pi domain γ) :
    ∀ result ∈ Δ.collect leaf γ fn, P result := by
  induction Δ with
  | nil => exact hleaf γ fn hf
  | snoc Δ next ih =>
    refine ih
      (leaf := fun current value =>
        ⋃₀ image (fun argument => leaf (current.snoc argument) [zf|value argument])
          (next current))
      (domain := fun current =>
        [zf|(argument : $(next current)) → $(domain (current.snoc argument))]) ?_ hf
    intro current value hvalue result hresult
    have ⟨results, hresults, hresult⟩ := mem_sUnion.mp hresult
    obtain ⟨argument, hargument, rfl⟩ := mem_image.mp hresults
    have happ := Aczel.app_mem hvalue hargument
    rw [app_map hargument] at happ
    exact hleaf _ _ happ result hresult

theorem pi_mono_cod {cod cod' : Dom b} (Δ : SemTele a b)
    (h : ∀ γ : Slots b, cod γ ⊆ cod' γ) (γ : Slots a) :
    Δ.pi cod γ ⊆ Δ.pi cod' γ := by
  induction Δ with
  | nil => exact h γ
  | snoc Δ domain ih =>
    refine ih fun s => ?_
    refine Aczel.piMap_mono_cod fun d hd => ?_
    rw [app_map hd, app_map hd]
    exact h _

theorem pi_inter_cod {cod cod' codW : Dom b} (Δ : SemTele a b)
    (h : ∀ (γ : Slots b) (value : ZFSet),
      value ∈ cod γ → value ∈ cod' γ → value ∈ codW γ)
    (γ : Slots a) (value : ZFSet) (hv : value ∈ Δ.pi cod γ)
    (hv' : value ∈ Δ.pi cod' γ) : value ∈ Δ.pi codW γ := by
  induction Δ generalizing value with
  | nil => exact h γ value hv hv'
  | snoc Δ domain ih =>
    refine ih (fun s v hv₁ hv₂ => Aczel.piMap_inter hv₁ hv₂ fun d hd w hw hw' => ?_) value hv hv'
    rw [app_map hd] at hw hw' ⊢
    exact h _ w hw hw'

theorem lamAt_congr {leaf leaf' : DomAt b} {cod : Dom b} (Δ : SemTele a b)
    (h : ∀ (s : Slots b) (value : ZFSet), value ∈ cod s → leaf s value = leaf' s value)
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ Δ.pi cod γ) :
    Δ.lamAt leaf γ fn = Δ.lamAt leaf' γ fn := by
  induction Δ generalizing fn with
  | nil => exact h γ fn hf
  | snoc Δ domain ih =>
    refine ih (fun s value hvalue => ?_) fn hf
    refine Aczel.lam_congr fun d hd => ?_
    have hv := Aczel.app_mem hvalue hd
    rw [app_map hd] at hv
    exact h _ _ hv

theorem lamAt_eq_of_mem {leftDomain rightDomain : Dom b}
    {leftLeaf rightLeaf : DomAt b} (Δ : SemTele a b)
    (hleaf : ∀ (final : Slots b) (left right : ZFSet),
      left ∈ leftDomain final → right ∈ rightDomain final →
      leftLeaf final left = rightLeaf final right)
    (γ : Slots a) {left right : ZFSet}
    (hleft : left ∈ Δ.pi leftDomain γ)
    (hright : right ∈ Δ.pi rightDomain γ) :
    Δ.lamAt leftLeaf γ left = Δ.lamAt rightLeaf γ right := by
  induction Δ generalizing left right with
  | nil => exact hleaf γ left right hleft hright
  | snoc Δ domain ih =>
    refine ih
      (leftDomain := fun current =>
        [zf|(argument : $(domain current)) → $(leftDomain (current.snoc argument))])
      (rightDomain := fun current =>
        [zf|(argument : $(domain current)) → $(rightDomain (current.snoc argument))])
      (fun current leftFunction rightFunction hleftFunction hrightFunction => ?_) hleft hright
    refine Aczel.lam_congr fun argument hargument => ?_
    have hleftValue := Aczel.app_mem hleftFunction hargument
    have hrightValue := Aczel.app_mem hrightFunction hargument
    rw [app_map hargument] at hleftValue hrightValue
    exact hleaf (current.snoc argument) _ _ hleftValue hrightValue

theorem lamAt_comp {source middle : Dom b} (Δ : SemTele a b)
    (outer inner : DomAt b)
    (hinner : ∀ (final : Slots b) (value : ZFSet),
      value ∈ source final → inner final value ∈ middle final)
    (γ : Slots a) (value : ZFSet)
    (hfield : value ∈ Δ.pi source γ) :
    Δ.lamAt outer γ (Δ.lamAt inner γ value) =
      Δ.lamAt (fun final value => outer final (inner final value))
        γ value := by
  induction Δ generalizing value with
  | nil => rfl
  | snoc Δ domain ih =>
    let source' : Dom _ := fun current =>
      [zf|(argument : $(domain current)) → $(source (current.snoc argument))]
    let middle' : Dom _ := fun current =>
      [zf|(argument : $(domain current)) → $(middle (current.snoc argument))]
    let outer' : DomAt _ := fun current function =>
      [zf|fun argument : $(domain current) =>
        $(outer (current.snoc argument) [zf|function argument])]
    let inner' : DomAt _ := fun current function =>
      [zf|fun argument : $(domain current) =>
        $(inner (current.snoc argument) [zf|function argument])]
    have hfield' : value ∈ SemTele.pi source' Δ γ := hfield
    have hinner' : ∀ (current : Slots _) (function : ZFSet),
        function ∈ source' current → inner' current function ∈ middle' current := by
      intro current function hfunction
      apply Aczel.lam_mem_piMap
      intro argument hargument
      rw [app_map hargument]
      have hvalue := Aczel.app_mem hfunction hargument
      rw [app_map hargument] at hvalue
      exact hinner (current.snoc argument) _ hvalue
    have hcomp := ih outer' inner' hinner' value hfield'
    simp only [SemTele.lamAt, SemTele.foldAt, Tele.foldr_snoc] at hcomp ⊢
    rw [hcomp]
    refine SemTele.lamAt_congr Δ
      (fun current function hfunction => Aczel.lam_congr fun argument hargument => ?_) γ value hfield'
    dsimp only [inner']
    rw [Aczel.app_lam hargument]

theorem lamAt_id (Δ : SemTele a b) (cod : Dom b)
    (γ : Slots a) (value : ZFSet) (hvalue : value ∈ Δ.pi cod γ) :
    Δ.lamAt (fun _ value => value) γ value = value := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    let cod' : Dom _ := fun current =>
      [zf|(field : $(domain current)) → $(cod (current.snoc field))]
    have hvalue' : value ∈ SemTele.pi cod' Δ γ := hvalue
    have hcongr := SemTele.lamAt_congr Δ
      (leaf := fun current value =>
        [zf|fun field : $(domain current) => value field])
      (fun _ value hvalue => Aczel.lam_app hvalue) γ value hvalue'
    change SemTele.lamAt
      (fun current value => [zf|fun field : $(domain current) => value field])
      Δ γ value = value
    rw [hcongr]
    exact ih cod' hvalue'

theorem lamAt_mem_piAt {leaf cod : DomAt b} {domain : Dom b} (Δ : SemTele a b)
    (h : ∀ (s : Slots b) (value : ZFSet), value ∈ domain s → leaf s value ∈ cod s value)
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ Δ.pi domain γ) :
    Δ.lamAt leaf γ fn ∈ Δ.piAt cod γ fn := by
  induction Δ generalizing fn with
  | nil => exact h γ fn hf
  | snoc Δ domain' ih =>
    refine ih (fun s value hvalue => ?_) fn hf
    refine Aczel.lam_mem_piMap fun d hd => ?_
    have hv := Aczel.app_mem hvalue hd
    rw [app_map hd] at hv ⊢
    exact h _ _ hv

theorem piAt_const (Δ : SemTele a b) (cod : Dom b)
    (γ : Slots a) (value : ZFSet) :
    Δ.piAt (fun final _ => cod final) γ value = Δ.pi cod γ := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    exact ih fun current =>
      [zf|(field : $(domain current)) → $(cod (current.snoc field))]

theorem pi_pull {a₁ count : Nat} (project : Slots a₁ → Slots a)
    (Δ : SemTele a (a + count)) (domain : Dom (a + count))
    (γ : Slots a₁) :
    (Δ.pull project count).pi
        (fun final => domain (Slots.pull project final)) γ =
      Δ.pi domain (project γ) := by
  have h := piAt_pull project Δ (fun final _ => domain final) γ ∅
  rwa [piAt_const, piAt_const] at h

end SemTele
end Metalean
