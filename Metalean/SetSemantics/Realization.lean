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
      simpa [← Function.comp_def, Fin.snoc_comp_natAdd] using
        he (current.snoc x) (.snoc (by simpa using hcurrent) (by simpa using hx))
    · exact hprefix

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
  simpa! [Inductive.motiveResult, hb, his final hfinal] using
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
  simpa [motiveAt, his, Aczel.appTuple_encode, hval, hvalueEq] using
    fibre_bundleMotive_value (level := level) (arities := arities) s hentry htag

end Metalean
