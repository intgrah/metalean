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
public import Metalean.SetTheory.ZFC.Aczel.Universe
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

noncomputable def pi : Dom b → SemTele a b → Dom a := fold Aczel.pi
noncomputable def lam : Dom b → SemTele a b → Dom a := fold Aczel.lam

theorem pi_ofDoms {count : Nat} (domains : Fin count → Dom a)
    (leaf : Dom (a + count)) (γ : Slots a) :
    (ofDoms domains).pi leaf γ = Aczel.pis (fun i => domains i γ)
      (fun values => leaf (Fin.append γ values)) := by
  induction count with
  | zero => simp [ofDoms, pi, fold, Aczel.pis]
  | succ count ih =>
    change (ofDoms fun i => domains i.castSucc).pi (fun current =>
      Aczel.pi (domains (Fin.last count) fun base => current (base.castAdd count))
        fun value => leaf (current.snoc value)) γ = _
    rw [ih]
    congr 1
    funext values
    simp [Fin.append_snoc]

noncomputable def app : {b : Nat} → SemTele a b → Slots b → ZFSet → ZFSet
  | _, .nil => fun _ fn => fn
  | _, .snoc Δ _ => fun γ fn => Aczel.app (app Δ (Fin.init γ) fn) (γ (Fin.last _))

noncomputable def foldAt (former : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (leaf : DomAt b) (Δ : SemTele a b) (γ : Slots a) (fn : ZFSet) : ZFSet :=
  Δ.fold former (fun final => leaf final (app Δ final fn)) γ

@[simp] theorem foldAt_snoc (F : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (leaf : DomAt (b + 1)) (Δ : SemTele a b) (domain : Dom b) (γ : Slots a) (fn : ZFSet) :
    foldAt F leaf (Δ.snoc domain) γ fn =
      foldAt F (fun current value => F (domain current) fun x =>
        leaf (current.snoc x) [zf|value x]) Δ γ fn := by
  simp [foldAt, fold, app]

noncomputable def piAt : DomAt b → SemTele a b → DomAt a := foldAt Aczel.pi
noncomputable def lamAt : DomAt b → SemTele a b → DomAt a := foldAt Aczel.lam

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

variable {a b : Nat} {reach : Set (Slots.{u} a)}

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

noncomputable def Reachable.snocEquiv (Δ : SemTele a b) (domain : Dom b) :
    Reachable reach (Δ.snoc domain) ≃ (current : Reachable reach Δ) × domain current.1 where
  toFun final := ⟨⟨Fin.init final.1, Reachable.init final.2⟩,
    ⟨final.1 (Fin.last b), Reachable.last final.2⟩⟩
  invFun point := ⟨point.1.1.snoc point.2.1,
    .snoc (by simp [point.1.2]) (by simp [point.2.2])⟩
  left_inv final := Subtype.ext (Fin.snoc_init_self final.1)
  right_inv point := by
    rcases point with ⟨⟨current, hcurrent⟩, ⟨value, hvalue⟩⟩
    apply Sigma.ext (Subtype.ext (show Fin.init (current.snoc value) = current from
      Fin.init_snoc (α := fun _ => ZFSet.{u}) (p := current) (x := value)))
    simp [Slots.snoc, Subtype.heq_iff_coe_eq]

instance Reachable.small (Δ : SemTele.{u} a b) [Small.{u} reach] :
    Small.{u} (Reachable reach Δ) := by
  induction Δ with
  | nil =>
    exact small_of_injective (f := fun final : Reachable reach (.nil : SemTele a a) =>
        (⟨final.1, Reachable.base final.2⟩ : reach))
      (fun _ _ h => Subtype.ext (congrArg (fun p : reach => p.1) h))
  | snoc Δ domain ih =>
    have := ih
    exact small_of_injective (Reachable.snocEquiv Δ domain).injective

theorem Reachable.card_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {Δ : SemTele a b}
    (hdoms : Tele.Forall (fun _ domain => ∀ γ, domain γ ∈ V_ κ.ord) Δ)
    (hreach : Cardinal.mk reach < Cardinal.lift.{u + 1} κ) :
    Cardinal.mk (Reachable reach Δ) < Cardinal.lift.{u + 1} κ := by
  induction hdoms with
  | nil =>
    exact (Cardinal.mk_le_of_injective
      (f := fun final : Reachable reach (.nil : SemTele a a) =>
        (⟨final.1, Reachable.base final.2⟩ : reach))
      (fun _ _ h => Subtype.ext (congrArg (fun p : reach => p.1) h))).trans_lt hreach
  | snoc Δ domain ih =>
    rw [Cardinal.mk_congr (Reachable.snocEquiv _ _), Cardinal.mk_sigma]
    exact Cardinal.sum_lt_of_isRegular hκ.isRegular.lift ih fun current => by
      rw [ZFSet.cardinalMk_coe_sort]
      exact Cardinal.lift_lt.mpr (card_lt_of_mem_vonNeumann hκ (domain current.1))

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

theorem Reachable.app_mem {Δ : SemTele a b} {γ : Slots a} {final : Slots b}
    {domain : Dom b} {fn : ZFSet} (h : final ∈ Reachable {γ} Δ) (hf : fn ∈ Δ.pi domain γ) :
    SemTele.app Δ final fn ∈ domain final :=
  Reachable.app_mem_of_base h (congrFun (Set.eq_of_mem_singleton (Reachable.base h))) hf

theorem Reachable.app_lamAt {Δ : SemTele a b} {γ : Slots a} {final : Slots b}
    {leaf : DomAt b} {fn : ZFSet} (h : final ∈ Reachable {γ} Δ) :
    SemTele.app Δ final (Δ.lamAt leaf γ fn) = leaf final (SemTele.app Δ final fn) := by
  rw [SemTele.lamAt, SemTele.foldAt]
  exact Reachable.app_lam h

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
  simp only [lamAt, foldAt]
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
  | nil => simp [foldAt, fold, pull, app]
  | snoc _ prior domain ih =>
    simpa [SemTele.pull] using ih
      (leaf := fun final result =>
        former (domain final) fun field => leaf (final.snoc field) [zf|result field]) value

noncomputable def sigma : Dom b → SemTele a b → Dom a :=
  fold fun domain rest => σ domain (map rest domain)

noncomputable def tail {b : Nat} (vargs : ZFSet) : SemTele a b → ZFSet
  | .nil => vargs
  | .snoc Δ _ => snd (tail vargs Δ)

noncomputable def values {b : Nat} (γ : Slots a) (vargs : ZFSet) : SemTele a b → Slots b
  | .nil => γ
  | .snoc Δ _ => Fin.snoc (values γ vargs Δ) (fst (tail vargs Δ))

theorem values_base (Δ : SemTele a b) (γ : Slots a) (vargs : ZFSet) (base : Fin a) :
    Δ.values γ vargs (base.castLE Δ.le) = γ base := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    exact (Fin.snoc_castSucc (α := fun _ => ZFSet) (p := values γ vargs Δ)
      (i := base.castLE Δ.le) ..).trans ih

theorem values_eq_append {count : Nat} (Δ : SemTele a (a + count)) (γ : Slots a)
    (vargs : ZFSet) :
    Δ.values γ vargs = Fin.append γ fun f => Δ.values γ vargs (Fin.natAdd a f) :=
  Fin.append_castAdd_natAdd.symm.trans
    (congrArg (Fin.append · _) (funext (Δ.values_base γ vargs)))

noncomputable def pack {b : Nat} : SemTele a b → Slots b → ZFSet → ZFSet
  | .nil => fun _ tail => tail
  | .snoc Δ _ => fun γ tail => pack Δ (Fin.init γ) (pair (γ (Fin.last _)) tail)

theorem tail_pack (Δ : SemTele a b) (γ : Slots b) (tail : ZFSet) :
    Δ.tail (Δ.pack γ tail) = tail := by
  induction Δ generalizing tail with
  | nil => rfl
  | snoc Δ domain ih => exact (congrArg snd (ih (Fin.init γ) _)).trans (snd_pair ..)

theorem values_pack (Δ : SemTele a b) (γ : Slots b) (tail : ZFSet) :
    Δ.values (fun base => γ (base.castLE Δ.le)) (Δ.pack γ tail) = γ := by
  induction Δ generalizing tail with
  | nil => rfl
  | snoc Δ domain ih =>
    change Slots.snoc
      (values (fun base => Fin.init γ (base.castLE Δ.le))
        (pack Δ (Fin.init γ) (pair (γ (Fin.last _)) tail)) Δ)
      (fst (SemTele.tail (pack Δ (Fin.init γ) (pair (γ (Fin.last _)) tail)) Δ)) = γ
    rw [ih, tail_pack, fst_pair]
    exact Fin.snoc_init_self γ

theorem pack_mem {Δ : SemTele a b} {leaf : Dom b}
    {reach : Set (Slots a)} {final : Slots b} {tail : ZFSet}
    (hfinal : final ∈ Reachable reach Δ) (htail : tail ∈ leaf final) :
    Δ.pack final tail ∈ Δ.sigma leaf (fun base => final (base.castLE Δ.le)) := by
  induction Δ generalizing tail with
  | nil => exact htail
  | snoc Δ domain ih =>
    have .snoc hprefix hlast := hfinal
    refine ih hprefix (pair_mem_sigma_map.mpr ⟨hlast, ?_⟩)
    simpa [Slots.snoc] using htail

theorem mem_sigma {Δ : SemTele a b} {leaf : Dom b} {γ : Slots a} {vargs : ZFSet} :
    vargs ∈ Δ.sigma leaf γ ↔
      Δ.values γ vargs ∈ Reachable {γ} Δ ∧
      Δ.tail vargs ∈ leaf (Δ.values γ vargs) ∧
      Δ.pack (Δ.values γ vargs) (Δ.tail vargs) = vargs := by
  constructor
  · intro h
    induction Δ with
    | nil => exact ⟨.nil rfl, h, rfl⟩
    | snoc Δ domain ih =>
      obtain ⟨hprior, htail, hpack⟩ := ih h
      obtain ⟨value, hvalue, tail, htail, heq⟩ := mem_sigma_map.mp htail
      simp only [values, SemTele.tail, pack, Fin.init_snoc, Fin.snoc_last]
      rw [heq, fst_pair, snd_pair]
      exact ⟨.snoc (by simpa using hprior) (by simpa using hvalue), htail, heq ▸ hpack⟩
  · rintro ⟨hfinal, htail, hpack⟩
    have hbase := Set.eq_of_mem_singleton (Reachable.base hfinal)
    have h := pack_mem hfinal htail
    rw [hbase] at h
    exact hpack ▸ h

theorem sigma_mono_cod {leaf₁ leaf₂ : Dom b} (Δ : SemTele a b)
    (h : ∀ γ, leaf₁ γ ⊆ leaf₂ γ) (γ : Slots a) :
    Δ.sigma leaf₁ γ ⊆ Δ.sigma leaf₂ γ := fun _ hv =>
  let ⟨hreach, htail, hpack⟩ := SemTele.mem_sigma.mp hv
  SemTele.mem_sigma.mpr ⟨hreach, h _ htail, hpack⟩

theorem sigma_inter_cod {leaf₁ leaf₂ leaf₃ : Dom b} (Δ : SemTele a b)
    (h : ∀ γ, ∀ value ∈ leaf₁ γ, value ∈ leaf₂ γ → value ∈ leaf₃ γ)
    (γ : Slots a) {value : ZFSet} (h₁ : value ∈ Δ.sigma leaf₁ γ)
    (h₂ : value ∈ Δ.sigma leaf₂ γ) : value ∈ Δ.sigma leaf₃ γ :=
  let ⟨hreach, htail, hpack⟩ := SemTele.mem_sigma.mp h₁
  SemTele.mem_sigma.mpr ⟨hreach, h _ _ htail (SemTele.mem_sigma.mp h₂).2.1, hpack⟩

theorem pi_mem_iff {source target : Dom b} (Δ : SemTele a b)
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ Δ.pi source γ) :
    fn ∈ Δ.pi target γ ↔
      ∀ final ∈ Reachable {γ} Δ, SemTele.app Δ final fn ∈ target final := by
  constructor
  · exact fun h _ hfinal => Reachable.app_mem hfinal h
  · intro h
    induction Δ with
    | nil => exact h γ (.nil rfl)
    | snoc Δ domain ih =>
      refine ih (source := fun current => Aczel.pi (domain current)
        fun value => source (current.snoc value)) hf fun current hcurrent => ?_
      rw [← Aczel.lam_app (Reachable.app_mem hcurrent hf)]
      refine Aczel.lam_mem_piMap fun value hvalue => ?_
      rw [app_map hvalue]
      simpa [SemTele.app] using h (current.snoc value)
        (.snoc (by simpa using hcurrent) (by simpa using hvalue))

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
  simp only [piAt, foldAt]
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
    rw [lamAt, foldAt_snoc]
    let cod' := fun current => Aczel.pi (domain current) fun field => cod (current.snoc field)
    have hvalue' : value ∈ SemTele.pi cod' Δ γ := hvalue
    exact (SemTele.lamAt_congr Δ (cod := cod')
      (leaf := fun current value => Aczel.lam (domain current) (Aczel.app value))
      (fun _ _ h => Aczel.lam_app h) γ value hvalue').trans (ih cod' hvalue')

theorem lamAt_mem_piAt {leaf cod : DomAt b} {domain : Dom b} (Δ : SemTele a b)
    (h : ∀ (s : Slots b) (value : ZFSet), value ∈ domain s → leaf s value ∈ cod s value)
    (γ : Slots a) (fn : ZFSet) (hf : fn ∈ Δ.pi domain γ) :
    Δ.lamAt leaf γ fn ∈ Δ.piAt cod γ fn :=
  Reachable.lam_mem_pi (reach := {γ})
    (fun final hfinal => h final _ (Reachable.app_mem hfinal hf)) γ (Set.mem_singleton γ)

end SemTele
variable {a b level : Nat} {reach : Set (Slots.{u} a)}

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

theorem SemTele.sigma_mem_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {leaf : Dom b} (hleaf : ∀ γ : Slots b, leaf γ ∈ U_ level)
    (γ : Slots a) : Δ.sigma leaf γ ∈ U_ level := by
  induction hdoms with
  | nil => exact hleaf γ
  | snoc _ hdomain ih => exact ih fun current => by grind only [zfBounds]

theorem SemTele.sigma_subset_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {leaf : Dom b} (hleaf : ∀ γ, leaf γ ⊆ U_ level) (γ : Slots a) :
    Δ.sigma leaf γ ⊆ U_ level := by
  induction hdoms with
  | nil => exact hleaf γ
  | snoc _ hdomain ih =>
    refine ih fun current value hv => ?_
    obtain ⟨head, hhead, tail, htail, rfl⟩ := mem_sigma_map.mp hv
    exact pair_mem_type (mem_type_of_mem (hdomain current) hhead) (hleaf _ htail)

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

end Metalean
