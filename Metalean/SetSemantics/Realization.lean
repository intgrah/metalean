/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Denotation
public import Metalean.SetSemantics.Telescope
import Metalean.Grind
import Metalean.Syntax.Substitution

public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {ζ : Sigs} {ℓ : Nat}
  {ε : Atom ζ ℓ → ZFSet} {ν : Param ℓ → Nat}
  {a b : Nat} {reach : Set (Slots a)}
  {Δsyn : Ctx ζ ℓ a b} {Δsem : SemTele a b} {s : Slots a}

@[expose] def DenotesOver (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) {a b : Nat}
    (reach : Set (Slots a)) (Δsem : SemTele a b)
    (e : Expr ζ ℓ b) (domain : Dom b) : Prop :=
  ∀ s ∈ Reachable reach Δsem, ε[ν; s]⟦e⟧ = domain s

abbrev Realizes (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) {a b : Nat}
    (reach : Set (Slots a)) :
    Ctx ζ ℓ a b → SemTele a b → Prop :=
  Tele.Forall₂ fun _ Θsem A => DenotesOver ε ν reach Θsem A

theorem Realizes.denotes_fold
    (h : Realizes ε ν reach Δsyn Δsem)
    (K : {n : Nat} → Expr ζ ℓ n → Expr ζ ℓ (n + 1) → Expr ζ ℓ n)
    (F : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (hK : ∀ {n} (γ : Slots n) t e,
      ε[ν; γ]⟦K t e⟧ = F ε[ν; γ]⟦t⟧ (fun x => ε[ν; γ.snoc x]⟦e⟧))
    (hF : ∀ A f₁ f₂, (∀ x ∈ A, f₁ x = f₂ x) → F A f₁ = F A f₂)
    {e : Expr ζ ℓ b} {leaf : Dom b} (hs : s ∈ reach)
    (he : DenotesOver ε ν reach Δsem e leaf) :
    ε[ν; s]⟦Tele.foldr K e Δsyn⟧ = Δsem.fold F leaf s := by
  induction h with
  | nil => exact he s (.nil hs)
  | snoc _ hdomain ih =>
    apply ih
    intro γ hγ
    rw [hK, hdomain γ hγ]
    exact hF _ _ _ fun x hx => he (γ.snoc x)
      (.snoc (by simpa using hγ) (by simpa using hx))

theorem Realizes.denotes_pi {e : Expr ζ ℓ b} {cod : Dom b} (hs : s ∈ reach) :
    DenotesOver ε ν reach Δsem e cod →
    Realizes ε ν reach Δsyn Δsem →
    ε[ν; s]⟦Δsyn.pi e⟧ = Δsem.pi cod s := by
  intro he h
  exact h.denotes_fold Expr.forallE Aczel.pi (fun _ _ _ => rfl)
    (fun _ _ _ h => Aczel.pi_congr h) hs he

theorem Realizes.denotes_piAt {k : Nat}
    {Δsyn : Ctx ζ ℓ a (a + k)} {Δsem : SemTele a (a + k)}
    {e : Expr ζ ℓ (a + k)} {leaf : DomAt (a + k)}
    {fn : ZFSet} (hs : s ∈ reach)
    (he : ∀ final ∈ Reachable reach Δsem,
      ε[ν; final]⟦e⟧ = leaf final [zf|fn $(fun f : Fin k => final (Fin.natAdd a f))...])
    (h : Realizes ε ν reach Δsyn Δsem) :
    ε[ν; s]⟦Δsyn.pi e⟧ = Δsem.piAt leaf s fn := by
  simpa only [SemTele.pi, SemTele.piAt, SemTele.foldAt, SemTele.app_eq_apps] using h.denotes_pi hs he

theorem Realizes.denotes_lam {e : Expr ζ ℓ b} {leaf : Dom b} (hs : s ∈ reach) :
    DenotesOver ε ν reach Δsem e leaf →
    Realizes ε ν reach Δsyn Δsem →
    ε[ν; s]⟦Δsyn.lam e⟧ = Δsem.lam leaf s := by
  intro he h
  exact h.denotes_fold Expr.lam Aczel.lam (fun _ _ _ => rfl)
    (fun _ _ _ h => Aczel.lam_congr h) hs he

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

theorem Realizes.denotes_fold_subst {n count : Nat}
    {Δsyn : Ctx ζ ℓ a (a + count)} {Δsem : SemTele a (a + count)}
    (h : Realizes ε ν reach Δsyn Δsem)
    (K : {n : Nat} → Expr ζ ℓ n → Expr ζ ℓ (n + 1) → Expr ζ ℓ n)
    (F : ZFSet → (ZFSet → ZFSet) → ZFSet)
    (hK : ∀ {n} (γ : Slots n) t e,
      ε[ν; γ]⟦K t e⟧ = F ε[ν; γ]⟦t⟧ (fun x => ε[ν; γ.snoc x]⟦e⟧))
    (hF : ∀ A f₁ f₂, (∀ x ∈ A, f₁ x = f₂ x) → F A f₁ = F A f₂)
    (σ : Subst ζ ℓ a n) (γ : Slots n) (δ : Slots a)
    (hδ : δ ∈ reach) (hσ : (ε[ν; γ]⟦σ ·⟧) = δ)
    {e : Expr ζ ℓ (n + count)} {leaf : Dom (a + count)}
    (he : ∀ values : Slots count, Fin.append δ values ∈ Reachable {δ} Δsem →
      ε[ν; Fin.append γ values]⟦e⟧ = leaf (Fin.append δ values)) :
    ε[ν; γ]⟦Tele.foldr K e (Ctx.substN σ count Δsyn)⟧ = Δsem.fold F leaf δ := by
  have hp := h.pull σ (fun _ => δ) (reach₁ := {γ}) (fun _ _ => hδ)
    (fun current hcurrent v => by subst current; exact congrFun hσ v)
  have hd : DenotesOver ε ν {γ} (Δsem.pull (fun _ : Slots n => δ) count) e
      (fun final => leaf (Slots.pull (fun _ : Slots n => δ) final)) := by
    intro final hfinal
    let values := fun f => final (Fin.natAdd n f)
    have hbase : (fun v : Fin n => final (v.castAdd count)) = γ := by
      simpa [Fin.castAdd, Fin.castLE] using Set.eq_of_mem_singleton (Reachable.base hfinal)
    have hvalues : final = Fin.append γ values := by
      rw [← hbase]
      exact Fin.append_castAdd_natAdd.symm
    have hs := Reachable.pull hfinal (reach := {δ}) (fun _ _ => rfl)
    have hs' : Fin.append δ values ∈ Reachable {δ} Δsem := by
      simpa [hvalues] using hs
    simpa [hvalues] using he values hs'
  have hd := hp.denotes_fold K F hK hF (Set.mem_singleton γ) hd
  rwa [SemTele.fold_pull] at hd

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

theorem Expr.denote_pi_ofTypes {count : Nat} (types : Fin count → Expr ζ ℓ a)
    (e : Expr ζ ℓ (a + count)) (γ : Slots a) :
    ε[ν; γ]⟦(Ctx.ofTypes types).pi e⟧ =
      Aczel.pis (fun i => ε[ν; γ]⟦types i⟧) (fun values => ε[ν; Fin.append γ values]⟦e⟧) := by
  have h := Realizes.ofTypes (ε := ε) (ν := ν) (reach := Set.univ)
    (types := types) (domains := fun i δ => ε[ν; δ]⟦types i⟧) (fun _ _ _ => rfl)
  exact (h.denotes_pi (Set.mem_univ γ) (fun _ _ => rfl)).trans (SemTele.pi_ofDoms _ _ _)

@[expose] noncomputable def Ctx.denote (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) :
    Ctx ζ ℓ a b → SemTele a b :=
  Tele.map fun _ t γ => ε[ν; γ]⟦t⟧

theorem Realizes.denote : Realizes ε ν reach Δsyn (Δsyn.denote ε ν) := by
  induction Δsyn with
  | nil => exact .nil
  | snoc _ _ ih => exact .snoc ih fun _ _ => rfl

theorem Realizes.reachable_iff (h : Realizes ε ν reach Δsyn Δsem) (γ : Slots b) :
    γ ∈ Reachable reach Δsem ↔
      (fun base => γ (base.castLE Δsem.le)) ∈ reach ∧
        ∀ v hv, γ v ∈ ε[ν; fun x => γ (x.castLE v.isLt.le)]⟦Δsyn.entry hv v.isLt⟧ := by
  induction h with
  | nil =>
    constructor
    · exact fun h => ⟨Reachable.base h, fun v hv => (Nat.not_le_of_gt v.isLt hv).elim⟩
    · exact fun h => .nil (by simpa using h.1)
  | @snoc scope Δsyn Δsem t domain _ hdomain ih =>
    constructor
    · intro h
      have .snoc hprefix hlast := h
      refine ⟨Reachable.base h, fun v hv => ?_⟩
      cases v using Fin.lastCases with
      | last =>
        rw [Ctx.entry_snoc_self]
        exact (hdomain _ hprefix).symm ▸ hlast
      | cast v =>
        rw [Ctx.entry_snoc_of_lt _ _ _ _ v.isLt]
        exact ((ih _).mp hprefix).2 v hv
    · rintro ⟨hbase, hmem⟩
      have hprefix : Fin.init γ ∈ Reachable reach Δsem := by
        refine (ih _).mpr ⟨by simpa [Fin.init] using hbase, fun v hv => ?_⟩
        have hv := hmem v.castSucc hv
        rw [Ctx.entry_snoc_of_lt _ _ _ _ v.isLt] at hv
        exact hv
      refine .snoc hprefix ?_
      have hlast := hmem (Fin.last scope) Δsem.le
      rw [Ctx.entry_snoc_self] at hlast
      change γ (Fin.last scope) ∈ ε[ν; Fin.init γ]⟦t⟧ at hlast
      rwa [hdomain _ hprefix] at hlast

theorem Reachable.of_denote (h : Realizes ε ν reach Δsyn Δsem) {γ : Slots a} (hγ : γ ∈ reach)
    {slots : Slots b} (hslots : slots ∈ Reachable {γ} (Δsyn.denote ε ν)) :
    slots ∈ Reachable reach Δsem := by
  have hs := (Realizes.denote.reachable_iff slots).mp hslots
  exact (h.reachable_iff slots).mpr ⟨Set.eq_of_mem_singleton hs.1 ▸ hγ, hs.2⟩

theorem Realizes.monoReach {reach₁ reach₂ : Set (Slots a)}
    (h : Realizes ε ν reach₁ Δsyn Δsem)
    (hreaches : reach₂ ⊆ reach₁) :
    Realizes ε ν reach₂ Δsyn Δsem := by
  induction h with
  | nil => exact .nil
  | snoc hrest hdomain ih =>
    exact .snoc ih fun γ hγ => hdomain γ (Reachable.mono hγ hreaches)

theorem Realizes.reachable_subst {n count : Nat} {γ : Slots n}
    {Δsyn : Ctx ζ ℓ a (a + count)} {Δsem : SemTele a (a + count)}
    (h : Realizes ε ν reach Δsyn Δsem)
    (ps : Subst ζ ℓ a n) (args : Fin count → Expr ζ ℓ n)
    (hbase : (ε[ν; γ]⟦ps ·⟧) ∈ reach)
    (hargs : ∀ f, ε[ν; γ]⟦args f⟧ ∈ ε[ν; γ]⟦(Δsyn.proj f).subst
      (Fin.append ps fun previous => args (previous.castLE f.isLt.le))⟧) :
    Fin.append (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦args ·⟧) ∈ Reachable reach Δsem := by
  apply (h.reachable_iff _).mpr
  refine ⟨?_, fun v hv => ?_⟩
  · change (fun base => Fin.append (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦args ·⟧) (base.castAdd count)) ∈ reach
    simpa using hbase
  cases v using Fin.addCases with
  | left v => exact (Nat.not_le_of_gt v.isLt hv).elim
  | right f =>
    have hf := hargs f
    rw [Expr.denote_subst, Fin.append_comp] at hf
    rw [← Ctx.proj_eq_entry]
    have hvalues : (fun v : Fin (a + f.val) =>
        Fin.append (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦args ·⟧) (v.castLE (by omega))) =
          Fin.append (ε[ν; γ]⟦ps ·⟧) (fun previous => ε[ν; γ]⟦args (previous.castLE f.isLt.le)⟧) := by
      funext v
      cases v using Fin.addCases <;> simp
    rw [← hvalues] at hf
    rw [Fin.append_right]
    exact hf

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


theorem Realizes.mapInst {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    {ℓ₁ n m : Nat} {ε₁ : Atom ζ₁ ℓ → ZFSet} {ε₂ : Atom ζ₂ ℓ → ZFSet}
    {Δ : Ctx ζ₁ ℓ₁ n m} {ls : Param ℓ₁ → Level ℓ}
    {reach : Set (Slots n)} {Δsem : SemTele n m}
    (h : Realizes ε₁ ν reach Δ{ls} Δsem)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    Realizes ε₂ ν reach (Δ.map pre.sigs){ls} Δsem :=
  (congrArg (fun Δ => Realizes ε₂ ν _ Δ _)
    (Ctx.map_instL pre.sigs ls Δ)).mp (h.map pre hatoms)

end Metalean
