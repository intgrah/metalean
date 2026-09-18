/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Denotation
public import Metalean.SetSemantics.Eliminator
public import Metalean.SetSemantics.InductiveUniverse
import Metalean.Grind
import Metalean.Syntax.Substitution

public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

inductive Reachable {a : Nat} (reach : Set (Slots a)) : {b : Nat} → SemTele a b → Set (Slots b)
  | nil {s : Slots a} :
    s ∈ reach →
    Reachable reach .nil s
  | snoc {b : Nat} {Δ : SemTele a b} {domain : Dom b} {s : Slots (b + 1)} :
    Fin.init s ∈ Reachable reach Δ →
    s (Fin.last b) ∈ domain (Fin.init s) →
    Reachable reach (Δ.snoc domain) s

variable {ζ : Sigs} {E : Env ζ} {ℓ ℓ' : Nat}
  {ε : Atom ζ ℓ → ZFSet} {ν : Param ℓ → Nat}
  {a b : Nat} {Γ : Ctx ζ ℓ 0 a} {reach : Set (Slots a)}
  {Δsyn : Ctx ζ ℓ a b} {Δsem : SemTele a b} {s : Slots a}

@[expose] def DenotesOver (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) {a b : Nat}
    (reach : Set (Slots a)) (Δsem : SemTele a b)
    (e : Expr ζ ℓ b) (domain : Dom b) : Prop :=
  ∀ s ∈ Reachable reach Δsem, ε[ν; s]⟦e⟧ = domain s

abbrev Realizes (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) {a b : Nat}
    (reach : Set (Slots a)) :
    Ctx ζ ℓ a b → SemTele a b → Prop :=
  Tele.Forall₂ fun _ Θsem A => DenotesOver ε ν reach Θsem A

theorem Realizes.denotes_pi {e : Expr ζ ℓ b} {cod : Dom b} (hs : s ∈ reach) :
    DenotesOver ε ν reach Δsem e cod →
    Realizes ε ν reach Δsyn Δsem →
    ε[ν; s]⟦Δsyn.pi e⟧ = Δsem.pi cod s := by
  intro he h
  induction h with
  | nil => exact he s (.nil hs)
  | snoc _ hdomain ih =>
    apply ih
    intro s hs
    simp only [Expr.denote, hdomain s hs]
    apply Aczel.pi_congr
    intro x hx
    simpa using he (s.snoc x) (.snoc (by simpa using hs) (by simpa using hx))

theorem Realizes.denotes_piAt {k : Nat}
    {Δsyn : Ctx ζ ℓ a (a + k)} {Δsem : SemTele a (a + k)}
    {e : Expr ζ ℓ (a + k)} {leaf : DomAt (a + k)}
    {fn : ZFSet} (hs : s ∈ reach)
    (he : ∀ final ∈ Reachable reach Δsem,
      ε[ν; final]⟦e⟧ = leaf final [zf|fn $(fun f : Fin k => final (Fin.natAdd a f))...])
    (h : Realizes ε ν reach Δsyn Δsem) :
    ε[ν; s]⟦Δsyn.pi e⟧ = Δsem.piAt leaf s fn := by
  induction Δsyn using Tele.addInduction with
  | nil =>
    have .nil := h
    simpa [SemTele.piAt, SemTele.foldAt, Aczel.apps] using he s (.nil hs)
  | snoc k Δsyn t ih =>
    have .snoc hprefix hdomain := h
    apply ih
    · intro current hcurrent
      simp only [Expr.denote, hdomain current hcurrent]
      apply Aczel.pi_congr
      intro x hx
      simpa [Slots.natAdd_snoc] using
        he (current.snoc x) (.snoc (by simpa using hcurrent) (by simpa using hx))
    · exact hprefix

theorem Reachable.apps_mem_of_base {k : Nat}
    {Δ : SemTele a (a + k)} {γ : Slots a}
    {final : Slots (a + k)} {domain : Dom (a + k)} {fn : ZFSet}
    (h : final ∈ Reachable reach Δ)
    (hbase : ∀ v : Fin a, final (v.castAdd k) = γ v)
    (hf : fn ∈ Δ.pi domain γ) :
    [zf|fn $(fun fn : Fin k => final (Fin.natAdd a fn))...] ∈
      domain final := by
  induction Δ using Tele.addInduction with
  | nil =>
    have .nil _ := h
    obtain rfl : final = γ := funext hbase
    simpa [SemTele.pi, SemTele.fold, Aczel.apps] using hf
  | snoc k prior next ih =>
    have .snoc hprior hlast := h
    have hresult := Aczel.app_mem (ih hprior hbase hf) hlast
    rw [app_map hlast] at hresult
    rw [Slots.natAdd_eq_snoc]
    simpa using hresult

theorem Reachable.apps_lam_of_base {k : Nat}
    {Δ : SemTele a (a + k)} {base : Slots a}
    {final : Slots (a + k)} {leaf : Dom (a + k)}
    (h : final ∈ Reachable {base} Δ) :
    [zf|$(Δ.lam leaf base) $(fun f : Fin k => final (Fin.natAdd a f))...] =
      leaf final := by
  induction Δ using Tele.addInduction with
  | nil =>
    have .nil hbase := h
    subst final
    simp [Aczel.apps, SemTele.lam, SemTele.fold]
  | snoc k prior domain ih =>
    have .snoc hprior hlast := h
    rw [Slots.natAdd_eq_snoc, Aczel.apps_snoc]
    change [zf|$(SemTele.lam (fun current =>
          [zf|fun value : $(domain current) => $(leaf (Fin.snoc current value))])
        prior base)
      $(fun f : Fin k => Fin.init final (Fin.natAdd a f))...
      $(final (Fin.last (a + k)))] = leaf final
    rw [ih hprior]
    calc
      [zf|$([zf|fun value : $(domain (Fin.init final)) =>
          $(leaf (Fin.snoc (Fin.init final) value))])
        $(final (Fin.last (a + k)))] =
          leaf (Fin.snoc (Fin.init final)
            (final (Fin.last (a + k)))) := Aczel.app_lam hlast
      _ = leaf final := congrArg leaf (Fin.snoc_init_self final)

theorem SemTele.lam_applyAt {k : Nat} (Δ : SemTele a (a + k))
    (leaf : DomAt (a + k)) (γ : Slots a) (fn : ZFSet) :
    Δ.lam (fun final => leaf final
        [zf|fn $(fun fn : Fin k => final (Fin.natAdd a fn))...]) γ =
      Δ.lamAt leaf γ fn := by
  induction Δ using Tele.addInduction generalizing fn with
  | nil =>
    simp [SemTele.lam, SemTele.fold, SemTele.lamAt, SemTele.foldAt, Aczel.apps]
  | snoc k prior domain ih =>
    let leaf₁ : DomAt (a + k) := fun current g =>
      [zf|fun d : $(domain current) => $(leaf (current.snoc d) [zf|g d])]
    have hleaf : (fun current => [zf|fun d : $(domain current) =>
          $(leaf (current.snoc d)
            [zf|fn $(fun fn : Fin (k + 1) =>
              current.snoc d (Fin.natAdd a fn))...])]) =
        fun current => leaf₁ current
          [zf|fn $(fun fn : Fin k => current (Fin.natAdd a fn))...] := by
      funext current
      apply Aczel.lam_congr
      intro d hd
      simp [Slots.natAdd_snoc]
    change SemTele.lam (fun current => [zf|fun d : $(domain current) =>
        $(leaf (current.snoc d)
          [zf|fn $(fun fn : Fin (k + 1) =>
            current.snoc d (Fin.natAdd a fn))...])]) prior γ =
      SemTele.lamAt leaf₁ prior γ fn
    rw [hleaf]
    exact ih leaf₁ fn

theorem Reachable.mem_collect {count : Nat} {Δ : SemTele a (a + count)}
    {γ : Slots a} {final : Slots (a + count)}
    (hfinal : final ∈ Reachable {γ} Δ) (leaf : DomAt (a + count))
    (value result : ZFSet)
    (hresult : result ∈ leaf final
      [zf|value $(fun f : Fin count => final (Fin.natAdd a f))...]) :
    result ∈ Δ.collect leaf γ value := by
  induction Δ using Tele.addInduction with
  | nil =>
    have .nil hbase := hfinal
    subst final
    simpa [SemTele.collect, SemTele.foldAt, Aczel.apps] using hresult
  | snoc count prior domain ih =>
    have .snoc hprior hlast := hfinal
    apply ih hprior
      fun current function => ⋃₀ image (fun argument =>
        leaf (current.snoc argument) [zf|function argument])
        (domain current)
    rw [mem_sUnion]
    refine ⟨_, mem_image.mpr
      ⟨final (Fin.last (a + count)), hlast, rfl⟩, ?_⟩
    simpa [Slots.natAdd_eq_snoc] using hresult

theorem Realizes.denotes_motivePiAt {k count : Nat}
    {Δsyn : Ctx ζ ℓ a (a + k)} {Δsem : SemTele a (a + k)}
    {motive : Expr ζ ℓ a}
    {is : Fin count → Expr ζ ℓ (a + k)}
    {vis : Slots (a + k) → Fin count → ZFSet}
    {e : Expr ζ ℓ a} {domain : Dom (a + k)}
    {leaf : DomAt (a + k)}
    (hs : s ∈ reach) (hvalue : ε[ν; s]⟦e⟧ ∈ Δsem.pi domain s)
    (hbase : ∀ final ∈ Reachable reach Δsem,
      ∀ v : Fin a, final (v.castAdd k) = s v)
    (his : ∀ final ∈ Reachable reach Δsem,
      ∀ index, ε[ν; final]⟦is index⟧ = vis final index)
    (hleaf : ∀ final ∈ Reachable reach Δsem, ∀ value,
      value ∈ domain final →
      [zf|$(ε[ν; s]⟦motive⟧) $(vis final)... value] = leaf final value)
    (h : Realizes ε ν reach Δsyn Δsem) :
    ε[ν; s]⟦Δsyn.pi (Inductive.motiveResult (motive.wkN k)
        is (e.applyBound k))⟧ = Δsem.piAt leaf s ε[ν; s]⟦e⟧ := by
  apply h.denotes_piAt hs
  intro final hfinal
  have hb : (fun v => final (v.castAdd k)) = s := funext (hbase final hfinal)
  simpa [Inductive.motiveResult, Expr.denote, hb, his final hfinal] using
    hleaf final hfinal _ (Reachable.apps_mem_of_base hfinal (hbase final hfinal) hvalue)

theorem Realizes.denotes_lam {e : Expr ζ ℓ b} {leaf : Dom b} (hs : s ∈ reach) :
    DenotesOver ε ν reach Δsem e leaf →
    Realizes ε ν reach Δsyn Δsem →
    ε[ν; s]⟦Δsyn.lam e⟧ = Δsem.lam leaf s := by
  intro he h
  induction h with
  | nil => exact he s (.nil hs)
  | snoc _ hdomain ih =>
    apply ih
    intro s hs
    simp! [hdomain s hs]
    apply Aczel.lam_congr
    intro x hx
    simpa using he (s.snoc x) (.snoc (by simpa using hs) (by simpa using hx))

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
    have := v.isLt
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

theorem Realizes.pull {a₁ count : Nat}
    {Δsyn : Ctx ζ ℓ a (a + count)}
    {Δsem : SemTele a (a + count)}
    {reach₁ : Set (Slots a₁)}
    (h : Realizes ε ν reach Δsyn Δsem)
    (σ : Subst ζ ℓ a a₁) (project : Slots a₁ → Slots a)
    (hreach : Set.MapsTo project reach₁ reach)
    (hσ : ∀ γ ∈ reach₁, ∀ v, ε[ν; γ]⟦σ v⟧ = project γ v) :
    Realizes ε ν reach₁ (Ctx.substN σ count Δsyn) (Δsem.pull project count) := by
  induction Δsyn using Tele.addInduction with
  | nil =>
    have .nil := h
    exact .nil
  | snoc count Δsyn t ih =>
    have .snoc Δsem domain := Δsem
    have .snoc hprefix hdomain := h
    refine .snoc (ih hprefix) fun γ hγ => ?_
    rw [Expr.denote_subst, Expr.denote_substLiftN,
      funext (hσ (fun v => γ (v.castAdd count)) (Reachable.base hγ))]
    exact hdomain _ (Reachable.pull hγ hreach)

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

theorem Realizes.of_le (hba : b ≤ a) (Δsyn : Ctx ζ ℓ a b) :
    ∃ Δsem : SemTele a b, Realizes ε ν reach Δsyn Δsem := by
  cases Δsyn with
  | nil => exact ⟨.nil, .nil⟩
  | snoc Δ t =>
    have := Δ.le
    omega

theorem Realizes.append {d : Nat} {Θsyn : Ctx ζ ℓ b d}
    {Θsem : SemTele b d} :
    Realizes ε ν reach Δsyn Δsem →
    Realizes ε ν (Reachable reach Δsem) Θsyn Θsem →
    Realizes ε ν reach (Δsyn ++ Θsyn) (Δsem ++ Θsem) := by
  intro hΔ hΘ
  induction hΘ with
  | nil => exact hΔ
  | snoc _ hdomain ih =>
    exact .snoc ih fun s hs => hdomain s (Reachable.of_append hs)

theorem Realizes.ofTypes {count : Nat} {types : Fin count → Expr ζ ℓ a}
    {domains : Fin count → Dom a}
    (h : ∀ f, ∀ γ ∈ reach, ε[ν; γ]⟦types f⟧ = domains f γ) :
    Realizes ε ν reach (Ctx.ofTypes types) (SemTele.ofDoms domains) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
    exact .snoc (ih fun f => h f.castSucc) fun γ hγ =>
      (Expr.denote_wkN γ _).trans (h (Fin.last count) _ (Reachable.base hγ))

@[expose] noncomputable def Ctx.denote (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) :
    Ctx ζ ℓ a b → SemTele a b :=
  Tele.map fun _ t γ => ε[ν; γ]⟦t⟧

theorem Realizes.denote : Realizes ε ν reach Δsyn (Δsyn.denote ε ν) := by
  induction Δsyn with
  | nil => exact .nil
  | snoc _ _ ih => exact .snoc ih fun _ _ => rfl

theorem Reachable.of_denote (h : Realizes ε ν reach Δsyn Δsem) {γ : Slots a} (hγ : γ ∈ reach)
    {slots : Slots b} (hslots : slots ∈ Reachable {γ} (Δsyn.denote ε ν)) :
    slots ∈ Reachable reach Δsem := by
  induction h with
  | nil =>
    have .nil hbase := hslots
    exact .nil (hbase ▸ hγ)
  | snoc _ hdomain ih =>
    have .snoc hprefix hlast := hslots
    have hprefix := ih hprefix
    refine .snoc hprefix ?_
    rwa [← hdomain _ hprefix]

theorem Realizes.monoReach {reach₁ reach₂ : Set (Slots a)}
    (h : Realizes ε ν reach₁ Δsyn Δsem)
    (hreaches : reach₂ ⊆ reach₁) :
    Realizes ε ν reach₂ Δsyn Δsem := by
  induction h with
  | nil => exact .nil
  | snoc hrest hdomain ih =>
    exact .snoc ih fun γ hγ => hdomain γ (Reachable.mono hγ hreaches)

theorem Realizes.reachable_subst
    {n : Nat} {γ : Slots n}
    (h : Realizes ε ν reach Δsyn Δsem)
    (σ : Subst ζ ℓ b n) (γ₁ : Slots b)
    (hbase : (fun base => γ₁ (base.castLE Δsem.le)) ∈ reach)
    (hσ : ∀ v, ε[ν; γ]⟦σ v⟧ = γ₁ v)
    (hmem : ∀ v, a ≤ v.val →
      γ₁ v ∈ ε[ν; γ]⟦(Ctx.get v (Γ ++ Δsyn)).subst σ⟧) :
    γ₁ ∈ Reachable reach Δsem := by
  induction h with
  | nil => exact .nil (by simpa using hbase)
  | @snoc scope Δsyn Δsem t domain hrest hdomain ih =>
    let σ' : Subst ζ ℓ scope n := Subst.wk.comp σ
    have hprefix : Fin.init γ₁ ∈ Reachable reach Δsem := by
      refine ih σ' (Fin.init γ₁) (by simpa [Fin.init] using hbase) (fun v => hσ v.castSucc)
        fun v hv => ?_
      simpa [Expr.wk_subst, σ', Fin.init] using hmem v.castSucc hv
    refine .snoc hprefix ?_
    have hvalues : (ε[ν; γ]⟦σ' ·⟧) = Fin.init γ₁ :=
      funext fun v => hσ v.castSucc
    have hdomain' : ε[ν; γ]⟦t.subst σ'⟧ = domain (Fin.init γ₁) := by
      rw [Expr.denote_subst, hvalues]
      exact hdomain (Fin.init γ₁) hprefix
    have hlast := hmem (Fin.last scope) Δsem.le
    rwa [Tele.append_snoc, Ctx.get_last, Expr.wk_subst, hdomain'] at hlast

theorem Realizes.map {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    {ε₁ : Atom ζ₁ ℓ → ZFSet} {ε₂ : Atom ζ₂ ℓ → ZFSet}
    {Δsyn : Ctx ζ₁ ℓ a b}
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    Realizes ε₁ ν reach Δsyn Δsem →
    Realizes ε₂ ν reach (Δsyn.map pre.sigs) Δsem := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc _ hdomain ih =>
    exact .snoc ih fun s hs => by
      simpa [Expr.denote_map pre.sigs hatoms] using hdomain s hs

theorem appTuple_encode {count : Nat} (fn : ZFSet) (γ : Slots count) :
    appTuple count fn (encode γ) = [zf|fn γ...] := by
  induction count with
  | zero =>
    obtain rfl : γ = ![] := Subsingleton.elim _ _
    simp [appTuple, Aczel.apps]
  | succ count ih =>
    rw [show encode γ = pair (encode (Fin.init γ))
        (γ (Fin.last count)) from rfl]
    simp [appTuple, ih, ← Aczel.apps_snoc]

theorem fibre_bundleMotive_typed {count level : Nat}
    {arities : Fin count → Nat} {vms : Fin count → ZFSet}
    {block value : ZFSet} (s : Fin count)
    (vis : Slots (arities s))
    (hvalue : value ∈ propSet level
      (fibreOp block (sortKey s.val (encode vis)))) :
    fibreOp (bundleMotive level arities vms block)
        (pair (sortKey s.val (encode vis)) value) =
      [zf|$(vms s) vis... value] := by
  let carrier := fibreOp block (sortKey s.val (encode vis))
  let raw := propGet level carrier value
  have hraw : raw ∈ carrier := propGet_mem hvalue
  have hval : propVal level raw = value := propVal_propGet hvalue
  have hvalueEq : propVal level value = value := by
    cases level with
    | zero =>
      rw [propSet_zero, mem_squash] at hvalue
      have ⟨_, _, heq⟩ := hvalue
      simpa using heq.symm
    | succ level => simp
  have hentry : pair (sortKey s.val (encode vis)) raw ∈ block :=
    mem_fibre.mp hraw
  have htag : fst (fst (pair (sortKey s.val (encode vis)) raw)) =
      numeral s.val := by
    simp [sortKey, encode]
  have his : snd (sortKey s.val (encode vis)) = encode vis := by
    simp [sortKey, encode]
  simpa [motiveAt, his, appTuple_encode, hval, hvalueEq] using
    fibre_bundleMotive_value (level := level) (arities := arities) s hentry htag

end Metalean
