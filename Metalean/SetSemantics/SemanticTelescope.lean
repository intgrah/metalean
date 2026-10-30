/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.SuccPred
public import Metalean.Meta.ZF
public import Metalean.Data.Tele
public import Metalean.Data.Fin
public import Metalean.SetTheory.ZFC.AczelUniverse
import Metalean.Grind

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
    rfl
  | right field => nomatch field

@[simp] theorem pull_init {a a₁ count : Nat}
    (project : Slots a₁ → Slots a) (γ : Slots (a₁ + count + 1)) :
    Fin.init (pull (count := count + 1) project γ) =
      pull (count := count) project (Fin.init γ) := by
  funext slot
  cases slot using Fin.addCases with
  | left base =>
    simp [Fin.init, show (base.castAdd count).castSucc = base.castAdd (count + 1) from rfl]
    rfl
  | right field => simp [Fin.init]

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

noncomputable def app : {b : Nat} → SemTele a b → Slots b → ZFSet → ZFSet
  | _, .nil => fun _ fn => fn
  | _, .snoc Δ _ => fun γ fn => Aczel.app (app Δ (Fin.init γ) fn) (γ (Fin.last _))

theorem app_append {c : Nat} (Δ : SemTele a b) (Θ : SemTele b c) (γ : Slots c) (fn : ZFSet) :
    SemTele.app (Δ ++ Θ) γ fn =
      SemTele.app Θ γ (SemTele.app Δ (fun v => γ (v.castLE Θ.le)) fn) := by
  induction Θ with
  | nil => rfl
  | snoc Θ domain ih =>
    simpa [app, Fin.init, Fin.castSucc_castLE] using
      congrArg (fun value => Aczel.app value (γ (Fin.last _))) (ih (Fin.init γ))

theorem app_eq_apps {count : Nat} (Δ : SemTele a (a + count)) (γ : Slots (a + count))
    (fn : ZFSet) :
    SemTele.app Δ γ fn = Aczel.apps fn (fun f => γ (Fin.natAdd a f)) := by
  induction Δ using Tele.addInduction with
  | nil => rfl
  | snoc count Δ domain ih =>
    change Aczel.app (SemTele.app Δ (Fin.init γ) fn) (γ (Fin.last (a + count))) = _
    rw [ih, Fin.comp_natAdd_eq_snoc]
    simp

end SemTele

variable {a b : Nat} {reach : Set (Slots a)}

inductive Reachable {a : Nat} (reach : Set (Slots a)) : {b : Nat} → SemTele a b → Set (Slots b)
  | nil {s : Slots a} :
    s ∈ reach →
    Reachable reach .nil s
  | snoc {b : Nat} {Δ : SemTele a b} {domain : Dom b} {s : Slots (b + 1)} :
    Fin.init s ∈ Reachable reach Δ →
    s (Fin.last b) ∈ domain (Fin.init s) →
    Reachable reach (Δ.snoc domain) s

@[reachability →] theorem Reachable.base {Δ : SemTele a b} {γ : Slots b}
    (h : γ ∈ Reachable reach Δ) :
    (fun base => γ (base.castLE Δ.le)) ∈ reach := by
  induction h with
  | nil hreach => simpa using hreach
  | snoc hprefix hlast ih => simpa [Fin.init] using ih

theorem Reachable.app_mem_of_base {Δ : SemTele a b} {γ : Slots a} {final : Slots b}
    {domain : Dom b} {fn : ZFSet} (h : final ∈ Reachable reach Δ)
    (hbase : ∀ v : Fin a, final (v.castLE Δ.le) = γ v) (hf : fn ∈ Δ.pi domain γ) :
    SemTele.app Δ final fn ∈ domain final := by
  induction Δ with
  | nil =>
    obtain rfl : final = γ := funext hbase
    exact hf
  | snoc Δ next ih =>
    have .snoc hprior hlast := h
    have hresult := Aczel.app_mem (ih hprior hbase hf) hlast
    rw [app_map hlast] at hresult
    simpa [SemTele.app] using hresult

theorem Reachable.apps_mem_of_base {k : Nat}
    {Δ : SemTele a (a + k)} {γ : Slots a}
    {final : Slots (a + k)} {domain : Dom (a + k)} {fn : ZFSet}
    (h : final ∈ Reachable reach Δ)
    (hbase : ∀ v : Fin a, final (v.castAdd k) = γ v)
    (hf : fn ∈ Δ.pi domain γ) :
    [zf|fn $(fun f : Fin k => final (Fin.natAdd a f))...] ∈ domain final := by
  rw [← SemTele.app_eq_apps Δ]
  exact Reachable.app_mem_of_base h hbase hf

theorem Reachable.app_lam {Δ : SemTele a b} {base : Slots a} {final : Slots b}
    {leaf : Dom b} (h : final ∈ Reachable {base} Δ) :
    SemTele.app Δ final (Δ.lam leaf base) = leaf final := by
  induction Δ with
  | nil =>
    have .nil hbase := h
    subst final
    rfl
  | snoc Δ domain ih =>
    have .snoc hprior hlast := h
    change Aczel.app
      (SemTele.app Δ (Fin.init final) (SemTele.lam (fun current =>
        Aczel.lam (domain current) fun value => leaf (current.snoc value)) Δ base))
      (final (Fin.last _)) = _
    rw [ih hprior, Aczel.app_lam hlast]
    exact congrArg leaf (Fin.snoc_init_self final)

theorem Reachable.apps_lam_of_base {k : Nat}
    {Δ : SemTele a (a + k)} {base : Slots a} {final : Slots (a + k)} {leaf : Dom (a + k)}
    (h : final ∈ Reachable {base} Δ) :
    [zf|$(Δ.lam leaf base) $(fun f : Fin k => final (Fin.natAdd a f))...] = leaf final := by
  rw [← SemTele.app_eq_apps Δ]
  exact Reachable.app_lam h

theorem SemTele.fold_applyAt (Δ : SemTele a b)
    (F : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (leaf : DomAt b) (γ : Slots a) (fn : ZFSet) :
    Δ.fold F (fun final => leaf final (SemTele.app Δ final fn)) γ =
      Δ.foldAt F leaf γ fn := by
  induction Δ generalizing fn with
  | nil => rfl
  | snoc Δ domain ih =>
    change SemTele.fold F (fun current => F (domain current) fun value =>
      leaf (current.snoc value) (SemTele.app (Δ.snoc domain) (current.snoc value) fn)) Δ γ = _
    simpa [SemTele.app, SemTele.foldAt] using ih
      (fun current fn => F (domain current) fun value => leaf (current.snoc value) [zf|fn value]) fn

theorem Reachable.app_mem {Δ : SemTele a b} {γ : Slots a} {final : Slots b}
    {domain : Dom b} {fn : ZFSet} (h : final ∈ Reachable {γ} Δ) (hf : fn ∈ Δ.pi domain γ) :
    SemTele.app Δ final fn ∈ domain final :=
  Reachable.app_mem_of_base h (congrFun (Set.eq_of_mem_singleton (Reachable.base h))) hf

theorem Reachable.app_lamAt {Δ : SemTele a b} {γ : Slots a} {final : Slots b}
    {leaf : DomAt b} {fn : ZFSet} (h : final ∈ Reachable {γ} Δ) :
    SemTele.app Δ final (Δ.lamAt leaf γ fn) = leaf final (SemTele.app Δ final fn) := by
  rw [SemTele.lamAt, ← SemTele.fold_applyAt]
  exact Reachable.app_lam h

namespace SemTele

theorem fold_congr (Δ : SemTele a b) (F : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (hF : ∀ A f₁ f₂, (∀ x ∈ A, f₁ x = f₂ x) → F A f₁ = F A f₂)
    {leaf₁ leaf₂ : Dom b} (γ : Slots a)
    (h : ∀ final ∈ Reachable {γ} Δ, leaf₁ final = leaf₂ final) :
    Δ.fold F leaf₁ γ = Δ.fold F leaf₂ γ := by
  induction Δ with
  | nil => exact h γ (.nil rfl)
  | snoc Δ domain ih =>
    refine ih fun current hcurrent => hF _ _ _ fun value hvalue => ?_
    exact h (current.snoc value) (.snoc (by simpa using hcurrent) (by simpa using hvalue))

theorem lamAt_ext (Δ : SemTele a b) {leaf₁ leaf₂ : DomAt b}
    (γ : Slots a) (fn₁ fn₂ : ZFSet)
    (h : ∀ final ∈ Reachable {γ} Δ,
      leaf₁ final (SemTele.app Δ final fn₁) = leaf₂ final (SemTele.app Δ final fn₂)) :
    Δ.lamAt leaf₁ γ fn₁ = Δ.lamAt leaf₂ γ fn₂ := by
  simp only [lamAt, ← fold_applyAt]
  exact Δ.fold_congr Aczel.lam (fun _ _ _ h => Aczel.lam_congr h) γ h

theorem pi_base (Δ : SemTele a b) (cod : Slots a → Dom b)
    (γ : Slots a) :
    Δ.pi (fun final => cod (fun base => final (base.castLE Δ.le)) final) γ =
      Δ.pi (cod γ) γ :=
  Δ.fold_congr Aczel.pi (fun _ _ _ h => Aczel.pi_congr h) γ fun final hfinal =>
    congrArg (fun base => cod base final) (Set.eq_of_mem_singleton (Reachable.base hfinal))

theorem fold_pull {a₁ count : Nat} (former : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (project : Slots a₁ → Slots a) (Δ : SemTele a (a + count)) (leaf : Dom (a + count))
    (γ : Slots a₁) :
    fold former (fun final => leaf (Slots.pull project final)) (Δ.pull project count) γ =
      fold former leaf Δ (project γ) := by
  induction Δ using Tele.addInduction with
  | nil => simp [pull, fold]
  | snoc count prior domain ih =>
    simpa [SemTele.pull, fold] using ih
      (leaf := fun final => former (domain final) fun field => leaf (final.snoc field))

theorem foldAt_pull {a₁ count : Nat} (former : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (project : Slots a₁ → Slots a)
    (Δ : SemTele a (a + count)) (leaf : DomAt (a + count))
    (γ : Slots a₁) (value : ZFSet) :
    foldAt former (fun final result => leaf (Slots.pull project final) result)
        (Δ.pull project count) γ value =
      foldAt former leaf Δ (project γ) value := by
  induction Δ using Tele.addInduction generalizing value with
  | nil => simp! [foldAt]
  | snoc _ prior domain ih =>
    simpa [SemTele.pull, foldAt] using ih
      (leaf := fun final result =>
        former (domain final) fun field => leaf (final.snoc field) [zf|result field]) value

noncomputable def collect : DomAt b → SemTele a b → DomAt a :=
  foldAt fun domain rest => ⋃₀ image rest domain

theorem mem_collect (Δ : SemTele a b) (leaf : DomAt b) (γ : Slots a) (fn result : ZFSet) :
    result ∈ Δ.collect leaf γ fn ↔
      ∃ final ∈ Reachable {γ} Δ, result ∈ leaf final (SemTele.app Δ final fn) := by
  induction Δ with
  | nil =>
    constructor
    · exact fun h => ⟨γ, .nil rfl, h⟩
    · rintro ⟨final, hfinal, h⟩
      have .nil hfinal := hfinal
      subst final
      exact h
  | snoc Δ domain ih =>
    change result ∈ SemTele.collect (fun current value =>
      ⋃₀ image (fun argument => leaf (current.snoc argument) [zf|value argument])
        (domain current)) Δ γ fn ↔ _
    rw [ih]
    constructor
    · rintro ⟨current, hcurrent, hresult⟩
      obtain ⟨argument, hargument, hresult⟩ := mem_sUnion_image.mp hresult
      refine ⟨current.snoc argument, .snoc (by simpa using hcurrent)
        (by simpa using hargument), ?_⟩
      simpa [SemTele.app] using hresult
    · rintro ⟨final, hfinal, hresult⟩
      have .snoc hcurrent hargument := hfinal
      refine ⟨Fin.init final, hcurrent,
        mem_sUnion_image.mpr ⟨final (Fin.last _), hargument, ?_⟩⟩
      simpa [SemTele.app] using hresult

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
    simpa using hpoints (pair argument point) (pair_mem_sigma_map.mpr ⟨hargument, hpoint⟩)

theorem collect_property {leaf : DomAt b} {domain : Dom b} (Δ : SemTele a b)
    (P : ZFSet → Prop)
    (hleaf : ∀ (γ : Slots b) (value : ZFSet), value ∈ domain γ →
      ∀ result ∈ leaf γ value, P result)
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ Δ.pi domain γ) :
    ∀ result ∈ Δ.collect leaf γ fn, P result := by
  intro result hresult
  obtain ⟨final, hfinal, hresult⟩ := (Δ.mem_collect leaf γ fn result).mp hresult
  exact hleaf final _ (Reachable.app_mem hfinal hf) result hresult

theorem lamAt_congr_of_collect {a b : Nat} (P : ZFSet → Prop)
    {domain : Dom b} {leaf leaf' keys : DomAt b} (tele : SemTele a b)
    (hleaf : ∀ (final : Slots b) (value : ZFSet), value ∈ domain final →
      (∀ key ∈ keys final value, P key) → leaf final value = leaf' final value)
    (γ : Slots a) (value : ZFSet) (hfield : value ∈ tele.pi domain γ)
    (hkeys : ∀ key ∈ tele.collect keys γ value, P key) :
    tele.lamAt leaf γ value = tele.lamAt leaf' γ value := by
  apply tele.lamAt_ext
  intro final hfinal
  apply hleaf final _ (Reachable.app_mem hfinal hfield)
  exact fun key hkey => hkeys key ((tele.mem_collect keys γ value key).mpr ⟨final, hfinal, hkey⟩)

theorem collect_rel
    {leftDomain rightDomain : Dom b} {leaf₁ leaf₂ : DomAt b}
    (r : ZFSet → ZFSet → Prop) (tele : SemTele a b)
    (hleaf : ∀ (final : Slots b) (left right : ZFSet),
      left ∈ leftDomain final → right ∈ rightDomain final →
      ∀ result ∈ leaf₂ final right,
        ∃ recovered ∈ leaf₁ final left, r recovered result)
    (γ : Slots a) {left right : ZFSet}
    (hleft : left ∈ tele.pi leftDomain γ)
    (hright : right ∈ tele.pi rightDomain γ) :
    ∀ result ∈ tele.collect leaf₂ γ right,
      ∃ recovered ∈ tele.collect leaf₁ γ left,
        r recovered result := by
  intro result hresult
  obtain ⟨final, hfinal, hresult⟩ := (tele.mem_collect leaf₂ γ right result).mp hresult
  obtain ⟨recovered, hrecovered, hrel⟩ := hleaf final _ _
    (Reachable.app_mem hfinal hleft) (Reachable.app_mem hfinal hright) result hresult
  exact ⟨recovered, (tele.mem_collect leaf₁ γ left recovered).mpr ⟨final, hfinal, hrecovered⟩, hrel⟩

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
  apply Δ.lamAt_ext
  exact fun final hfinal => h final _ (Reachable.app_mem hfinal hf)

theorem lamAt_eq_of_mem {leftDomain rightDomain : Dom b}
    {leftLeaf rightLeaf : DomAt b} (Δ : SemTele a b)
    (hleaf : ∀ (final : Slots b) (left right : ZFSet),
      left ∈ leftDomain final → right ∈ rightDomain final →
      leftLeaf final left = rightLeaf final right)
    (γ : Slots a) {left right : ZFSet}
    (hleft : left ∈ Δ.pi leftDomain γ)
    (hright : right ∈ Δ.pi rightDomain γ) :
    Δ.lamAt leftLeaf γ left = Δ.lamAt rightLeaf γ right := by
  apply Δ.lamAt_ext
  exact fun final hfinal => hleaf final _ _
    (Reachable.app_mem hfinal hleft) (Reachable.app_mem hfinal hright)

theorem piAt_lamAt
    {a b : Nat} (tele : SemTele a b)
    {domain : Dom b} (map leaf leaf' : DomAt b)
    (h : ∀ final value, value ∈ domain final →
      leaf final value = leaf' final (map final value))
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ tele.pi domain γ) :
    tele.piAt leaf γ fn =
      tele.piAt leaf' γ (tele.lamAt map γ fn) := by
  simp only [piAt, ← fold_applyAt]
  apply tele.fold_congr Aczel.pi (fun _ _ _ h => Aczel.pi_congr h)
  intro final hfinal
  rw [Reachable.app_lamAt hfinal]
  exact h final _ (Reachable.app_mem hfinal hf)

theorem lamAt_comp (Δ : SemTele a b) (outer inner : DomAt b)
    (γ : Slots a) (value : ZFSet) :
    Δ.lamAt outer γ (Δ.lamAt inner γ value) =
      Δ.lamAt (fun final value => outer final (inner final value)) γ value := by
  apply Δ.lamAt_ext
  intro final hfinal
  rw [Reachable.app_lamAt hfinal]

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

end SemTele
variable {a b level : Nat} {reach : Set (Slots a)}

abbrev SemTele.DomsIn (level : Nat) {a b : Nat} (Δ : SemTele a b) : Prop :=
  Tele.Forall (fun _ domain => ∀ γ, domain γ ∈ U_ level) Δ

theorem SemTele.DomsIn.mono {level level' : Nat} (hle : level ≤ level')
    {tele : SemTele a b} (h : tele.DomsIn level) : tele.DomsIn level' := by
  induction h <;> constructor <;> solve_by_elim [type_mono]

theorem SemTele.DomsIn.append {d : Nat} {base : SemTele a b}
    {extension : SemTele b d} (hbase : base.DomsIn level) :
    extension.DomsIn level →
    SemTele.DomsIn level (base ++ extension)
  | .nil => hbase
  | .snoc htele hdomain => .snoc (append hbase htele) hdomain

theorem SemTele.pi_mem_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {cod : Dom b} (hcod : ∀ γ : Slots b, cod γ ∈ U_ level) (γ : Slots a) :
    Δ.pi cod γ ∈ U_ level := by
  induction hdoms with
  | nil => exact hcod γ
  | snoc _ hdomain ih =>
    refine ih fun s => ?_
    refine piMap_mem_type (hdomain s) fun d hd => ?_
    rw [app_map hd]
    exact hcod _

theorem SemTele.support_mem_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {leaf : Dom b} (hleaf : ∀ γ : Slots b, leaf γ ∈ U_ level)
    (γ : Slots a) : Δ.support leaf γ ∈ U_ level := by
  induction hdoms with
  | nil => exact hleaf γ
  | snoc _ hdomain ih => exact ih fun current => by grind only [zfBounds]

theorem SemTele.pi_subset_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {cod : Dom b} (hcod : ∀ γ : Slots b, cod γ ⊆ U_ level) (γ : Slots a) :
    Δ.pi cod γ ⊆ U_ level := by
  induction hdoms with
  | nil => exact hcod γ
  | snoc _ hdomain ih =>
    refine ih fun s f hf => ?_
    refine type_mem_of_mem_piMap (hdomain s) hf fun d hd => ?_
    have hv := Aczel.app_mem hf hd
    rw [app_map hd] at hv
    exact hcod _ hv

@[reachability ←] theorem Reachable.append {d : Nat} {Δ : SemTele a b} {Θ : SemTele b d}
    {s : Slots d} :
    s ∈ Reachable (Reachable reach Δ) Θ →
    s ∈ Reachable reach (Δ ++ Θ) := by
  intro h
  induction h with
  | nil h => exact h
  | snoc _ hlast ih => exact .snoc ih hlast

@[reachability →] theorem Reachable.of_append {d : Nat} {Δ : SemTele a b} {Θ : SemTele b d}
    {s : Slots d} :
    s ∈ Reachable reach (Δ ++ Θ) →
    s ∈ Reachable (Reachable reach Δ) Θ := by
  intro h
  induction Θ with
  | nil => exact .nil h
  | snoc Θ domain ih =>
    have .snoc hrest hlast := h
    exact .snoc (ih hrest) hlast

@[reachability →] theorem Reachable.init {Δ : SemTele a b} {domain : Dom b}
    {γ : Slots (b + 1)} :
    γ ∈ Reachable reach (Δ.snoc domain) →
    Fin.init γ ∈ Reachable reach Δ
  | .snoc hprefix _ => hprefix

@[reachability →] theorem Reachable.last {Δ : SemTele a b} {domain : Dom b}
    {γ : Slots (b + 1)} :
    γ ∈ Reachable reach (Δ.snoc domain) →
    γ (Fin.last b) ∈ domain (Fin.init γ)
  | .snoc _ hlast => hlast

theorem Reachable.ofDoms_mem {count : Nat} {domains : Fin count → Dom a}
    {γ : Slots (a + count)} (h : γ ∈ Reachable reach (SemTele.ofDoms domains)) (f : Fin count) :
    γ (Fin.natAdd a f) ∈ domains f fun base => γ (base.castAdd count) := by
  induction count with
  | zero => exact f.elim0
  | succ count ih =>
    cases f using Fin.lastCases with
    | last => exact Reachable.last h
    | cast f => exact ih (Reachable.init h) f

theorem Reachable.ofDoms_append {count : Nat} {domains : Fin count → Dom a}
    {γ : Slots a} {values : Fin count → ZFSet} (hbase : γ ∈ reach)
    (hvalues : ∀ f, values f ∈ domains f γ) :
    Fin.append γ values ∈ Reachable reach (SemTele.ofDoms domains) := by
  induction count with
  | zero => exact .nil (by simpa using hbase)
  | succ count ih =>
    rw [← Fin.snoc_init_self values, Fin.append_snoc]
    exact .snoc (by simpa using ih (values := Fin.init values) fun f => hvalues f.castSucc)
      (by simpa using hvalues (Fin.last count))

theorem Reachable.mem_type_of_domsIn {Δ : SemTele a b} {γ : Slots b} {level : Nat}
    (h : γ ∈ Reachable reach Δ) (hdoms : Δ.DomsIn level) (v : Fin b) (hv : a ≤ v.val) :
    γ v ∈ U_ level := by
  induction h with
  | nil =>
    omega
  | @snoc b Δ domain γ _ hlast ih =>
    have .snoc hdoms hdomain := hdoms
    cases v using Fin.lastCases with
    | last => exact mem_type_of_mem (hdomain (Fin.init γ)) hlast
    | cast v => exact ih hdoms v (by simpa using hv)

theorem Reachable.mono {reach₁ reach₂ : Set (Slots a)}
    {Δ : SemTele a b} {γ : Slots b}
    (h : γ ∈ Reachable reach₁ Δ) (hle : reach₁ ⊆ reach₂) :
    γ ∈ Reachable reach₂ Δ := by
  induction h <;> solve_by_elim

theorem Reachable.pull {a₁ count : Nat} {reach₁ : Set (Slots a₁)}
    {project : Slots a₁ → Slots a}
    {Δ : SemTele a (a + count)} {γ : Slots (a₁ + count)}
    (h : γ ∈ Reachable reach₁ (Δ.pull project count))
    (hbase : Set.MapsTo project reach₁ reach) :
    Slots.pull project γ ∈ Reachable reach Δ := by
  induction Δ using Tele.addInduction with
  | nil =>
    have .nil hreach := h
    exact .nil (by simpa using hbase hreach)
  | snoc count prior domain ih =>
    have .snoc hprior hlast := h
    exact .snoc (by simpa using ih hprior) (by simpa using hlast)

theorem Reachable.of_pull {a₁ count : Nat} {reach₁ : Set (Slots a₁)}
    {project : Slots a₁ → Slots a}
    {Δ : SemTele a (a + count)} {γ : Slots (a₁ + count)}
    (h : Slots.pull project γ ∈ Reachable reach Δ)
    (hbase : (fun base => γ (base.castAdd count)) ∈ reach₁) :
    γ ∈ Reachable reach₁ (Δ.pull project count) := by
  induction Δ using Tele.addInduction with
  | nil => exact .nil (by simpa using hbase)
  | snoc count prior domain ih =>
    have .snoc hprior hlast := h
    exact Reachable.snoc (ih (by simpa using hprior) hbase) (by simpa using hlast)

theorem Reachable.lam_mem_pi {cod leaf : Dom b} {Δ : SemTele a b} :
    (∀ γ ∈ Reachable reach Δ, leaf γ ∈ cod γ) →
    ∀ γ ∈ reach, Δ.lam leaf γ ∈ Δ.pi cod γ := by
  intro h γ hγ
  induction Δ with
  | nil => exact h γ (.nil hγ)
  | snoc Δ domain ih =>
    refine ih fun current hcurrent => ?_
    refine Aczel.lam_mem_piMap fun value hvalue => ?_
    rw [app_map hvalue]
    exact h _ (.snoc (by simpa using hcurrent) (by simpa using hvalue))

end Metalean
