/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Inversion
public import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat}
  {Γ Γ₁ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n m} {Γ₂ : Ctx ζ ℓ 0 m} {P : Level ℓ → Prop}

theorem TeleWF.appendCtxWF :
    TeleWF E P Γ Δ →
    E[Γ] ⊢ ok →
    E[Γ ++ Δ] ⊢ ok := by
  intro hWF hΓ
  induction hWF with
  | nil => exact hΓ
  | snoc hΔ ht ih =>
    obtain ⟨u, _, ht⟩ := ht
    exact ih.snoc ⟨u, ht⟩

theorem CtxWF.teleWF (hΓ : E[Γ] ⊢ ok) :
    TeleWF E (fun _ => True) .nil Γ := by
  induction hΓ with
  | nil => exact .nil
  | snoc _ ht ih =>
    have ⟨u, ht⟩ := ht
    exact .snoc ih ⟨u, trivial, by simpa using ht⟩

theorem TeleWF.append {k : Nat} {Θ : Ctx ζ ℓ m k} (hΔ : TeleWF E P Γ Δ)
    (hΘ : TeleWF E P (Γ ++ Δ) Θ) :
    TeleWF E P Γ (Δ ++ Θ) := by
  induction hΘ with
  | nil => simpa using hΔ
  | snoc _ hA ih =>
    rw [Tele.append_assoc] at hA
    exact .snoc ih hA

theorem TeleWF.of_append {k : Nat} {Θ : Ctx ζ ℓ m k} (h : TeleWF E P Γ (Δ ++ Θ)) :
    TeleWF E P Γ Δ ∧ TeleWF E P (Γ ++ Δ) Θ := by
  induction Θ with
  | nil => exact ⟨h, .nil⟩
  | snoc Θ t ih =>
    have .snoc h ht := h
    have ⟨hΔ, hΘ⟩ := ih h
    refine ⟨hΔ, .snoc hΘ ?_⟩
    rw [Tele.append_assoc]
    exact ht

theorem TeleWF.substitution_congr {m : Nat}
    {Δ : Ctx ζ ℓ 0 m} {σ₁ σ₂ : Subst ζ ℓ m n} {e₁ e₂ t : Expr ζ ℓ m} :
    TeleWF E P .nil Δ →
    E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ Δ →
    E[Δ] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ e₁.subst σ₁ ≡ e₂.subst σ₂ : t.subst σ₁ := by
  intro hΔ hσ he
  induction hΔ with
  | nil =>
    obtain rfl : σ₁ = σ₂ := Subsingleton.elim _ _
    exact he.substitution hσ.left
  | @snoc m Δ t₁ hΔ ht₁ ih =>
    have ⟨u₁, _, ht₁⟩ := ht₁
    simp at ht₁
    have ⟨u, ht⟩ := he.regular
    have hσ' := hσ.wk_comp
    have hlast : E[Γ] ⊢ σ₁ (Fin.last m) ≡ σ₂ (Fin.last m) : t₁.subst (Subst.wk.comp σ₁) := by
      simpa [Expr.wk_subst] using hσ (Fin.last m)
    have hprefix' : E[Γ] ⊢ Subst.wk.comp σ₂ ⊣ Δ := fun p => by
      have ⟨l, hp⟩ := (TeleWF.appendCtxWF hΔ .nil).get p
      simp at hp
      exact .defeqDF (ih hσ' hp) (hσ' p).right
    have ht₁σ := ht₁.substitution hσ'.left
    have ht₁σ' := ht₁.substitution hprefix'
    have hlast' : E[Γ] ⊢ σ₂ (Fin.last m) : t₁.subst (Subst.wk.comp σ₂) :=
      .defeqDF (ih hσ' ht₁) hlast.right
    have hprefixLift := hσ'.left.lift ⟨u₁, ht₁⟩
    have hprefixLift' := hprefix'.lift ⟨u₁, ht₁⟩
    have hσfull : E[Γ] ⊢ Subst.extend (Subst.wk.comp σ₁) (σ₁ (Fin.last m)) ⊣ Δ.snoc t₁ :=
      hσ'.left.extend hlast.left
    have hσfull' : E[Γ] ⊢ Subst.extend (Subst.wk.comp σ₂) (σ₂ (Fin.last m)) ⊣ Δ.snoc t₁ :=
      hprefix'.extend hlast'
    have htinst : E[Γ] ⊢ (t.subst (Subst.wk.comp σ₁).lift).inst (σ₁ (Fin.last m)) : .sort u := by
      simpa [Expr.inst] using ht.substitution hσfull
    have htinst' : E[Γ] ⊢ (t.subst (Subst.wk.comp σ₂).lift).inst (σ₂ (Fin.last m)) : .sort u := by
      simpa [Expr.inst] using ht.substitution hσfull'
    have htapp := Defeq.appDF ht₁σ .sortDF
      (ih hσ' (.lamDF ht₁ .sortDF .sortDF ht ht)) hlast .sortDF
    have htbeta := Defeq.beta ht₁σ .sortDF (ht.substitution hprefixLift) hlast.left .sortDF
      (by simpa [Expr.inst] using htinst)
    have htbeta' := Defeq.beta ht₁σ' .sortDF (ht.substitution hprefixLift') hlast' .sortDF
      (by simpa [Expr.inst] using htinst')
    have hteq := htbeta.symm.trans (htapp.trans htbeta')
    have heapp := Defeq.appDF ht₁σ (ht.substitution hprefixLift)
      (ih hσ' (.lamDF ht₁ ht ht he he)) hlast ((ht.substitution hprefixLift).inst_congr hlast)
    have hebeta := Defeq.beta ht₁σ (ht.substitution hprefixLift)
      (he.left.substitution hprefixLift) hlast.left htinst
      (by simpa [Expr.inst] using he.left.substitution hσfull)
    have hebeta' := Defeq.beta ht₁σ' (ht.substitution hprefixLift')
      (he.right.substitution hprefixLift') hlast' htinst'
      (by simpa [Expr.inst] using he.right.substitution hσfull')
    simpa [Expr.inst] using
      hebeta.symm.trans (heapp.trans (.defeqDF hteq.symm hebeta'))

theorem Defeq.substitution_congr (hΓ : E[Γ₁] ⊢ ok) {σ₁ σ₂ : Subst ζ ℓ n m}
    (hσ : E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁) {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ₁] ⊢ e₁ ≡ e₂ : t →
    E[Γ₂] ⊢ e₁.subst σ₁ ≡ e₂.subst σ₂ : t.subst σ₁ :=
  TeleWF.substitution_congr hΓ.teleWF hσ

theorem TeleWF.extendFamily {a b k : Nat} {Γ₀ : Ctx ζ ℓ 0 a} {Γ : Ctx ζ ℓ 0 b}
    {Δ : Ctx ζ ℓ a (a + k)} (hΔ : TeleWF E P Γ₀ Δ) {σ : Subst ζ ℓ a b} {xs : Fin k → Expr ζ ℓ b} :
    E[Γ] ⊢ σ ⊣ Γ₀ →
    (∀ p, E[Γ] ⊢ xs p :
      (Δ.entry (by omega) (by omega)).subst
        (Fin.append σ fun previous : Fin p.val =>
          xs (previous.castLE p.isLt.le))) →
    E[Γ] ⊢ Fin.append σ xs ⊣ Γ₀ ++ Δ := by
  intro hσ hxs
  induction Δ using Tele.addInduction with
  | nil => simpa using hσ
  | snoc k Δ t ih =>
    have .snoc hΔ hA := hΔ
    have hprefix (p : Fin k) : E[Γ] ⊢ xs p.castSucc :
      (Ctx.entry Δ (by omega) (by omega)).subst
        (Fin.append σ fun previous : Fin p.val =>
          xs (previous.castLE p.castSucc.isLt.le)) := by
      simpa using hxs p.castSucc
    have hlast := hxs (Fin.last k)
    simpa [Subst.extend, ← Fin.append_snoc,
      show Fin.snoc (fun previous : Fin k => xs (previous.castLE (Nat.le_succ k))) (xs (Fin.last k)) = xs from Fin.snoc_init_self xs] using
      (ih hΔ hprefix).extend hlast

theorem TeleWF.entry_isType {a b k : Nat} {Γ₀ : Ctx ζ ℓ 0 a} {Γ : Ctx ζ ℓ 0 b}
    {Δ : Ctx ζ ℓ a (a + k)} (hΔ : TeleWF E P Γ₀ Δ) {σ : Subst ζ ℓ a b}
    {xs : Fin k → Expr ζ ℓ b} (p : Fin k) :
    E[Γ] ⊢ σ ⊣ Γ₀ →
    (∀ q : Fin k, q < p → E[Γ] ⊢ xs q :
      (Δ.entry (by omega) (by omega)).subst
        (Fin.append σ fun previous : Fin q.val =>
          xs (previous.castLE q.isLt.le))) →
    E[Γ] ⊢ (Δ.entry (p := a + p.val) (by omega) (by omega)).subst
      (Fin.append σ fun previous : Fin p.val =>
        xs (previous.castLE p.isLt.le)) typ := by
  intro hσ hxs
  induction Δ using Tele.addInduction with
  | nil => exact p.elim0
  | snoc k Δ t ih =>
    have .snoc hΔ hA := hΔ
    by_cases hp : p.val < k
    · have hprefix (q : Fin k) (hq : q < (⟨p.val, hp⟩ : Fin k)) : E[Γ] ⊢ xs q.castSucc :
          (Ctx.entry Δ (by omega) (by omega)).subst
            (Fin.append σ fun previous : Fin q.val =>
              xs (previous.castLE q.castSucc.isLt.le)) := by
        simpa using hxs q.castSucc (by simpa [Fin.lt_def] using hq)
      simpa [Ctx.entry, hp.ne] using ih (xs := fun q => xs q.castSucc) hΔ ⟨p.val, hp⟩ hprefix
    · obtain rfl : p = Fin.last k := Fin.ext (by have := p.isLt; simp only [Fin.val_last]; omega)
      have hprefix (q : Fin k) : E[Γ] ⊢ xs q.castSucc :
          (Ctx.entry Δ (by omega) (by omega)).subst
            (Fin.append σ fun previous : Fin q.val =>
              xs (previous.castLE q.castSucc.isLt.le)) := by
        simpa using
          hxs q.castSucc (by simp)
      have hfam := TeleWF.extendFamily (xs := fun q => xs q.castSucc) hΔ hσ hprefix
      have ⟨u, _, ht⟩ := hA
      refine ⟨u, ?_⟩
      have := ht.substitution hfam
      simpa

theorem TeleWF.entry_isType_nil {m : Nat} {Θ : Ctx ζ ℓ 0 m}
    (hΘ : TeleWF E P .nil Θ) {xs : Fin m → Expr ζ ℓ n} (p : Nat) (hp : p < m) :
    (∀ q (hq : q < p), E[Γ] ⊢ xs ⟨q, by omega⟩ :
      (Θ.entry (Nat.zero_le q) (by omega)).subst
        fun w : Var q => xs (w.castLE (by omega))) →
    E[Γ] ⊢ (Θ.entry (Nat.zero_le p) hp).subst
      (fun w : Var p => xs (w.castLE (by omega))) typ := by
  intro hxs
  induction hΘ with
  | nil => omega
  | @snoc m Δ t hΔ ht ih =>
    have ⟨u, _, ht⟩ := ht
    simp at ht
    by_cases hpm : p = m
    · subst hpm
      have hσ : E[Γ] ⊢ (fun w : Var p => xs (w.castLE (by omega))) ⊣ Δ := fun v => by
        rw [Ctx.get_subst Δ _ v v.val v.isLt rfl]
        have := hxs v.val v.isLt
        simp only [Ctx.entry, v.isLt.ne] at this
        exact this
      exact ⟨u, by simpa using ht.substitution hσ⟩
    · have := ih (xs := fun w => xs w.castSucc) (by omega) fun q hq => by
        have := hxs q hq
        simpa [Ctx.entry, show q ≠ m by omega] using this
      simpa [Ctx.entry, hpm] using this

theorem SubstEq.extendFamily {a b k : Nat} {Γ₀ : Ctx ζ ℓ 0 a} {Γ₁ : Ctx ζ ℓ 0 b}
    {Δ : Ctx ζ ℓ a (a + k)} {P : Level ℓ → Prop} (hΔ : TeleWF E P Γ₀ Δ) {σ₁ σ₂ : Subst ζ ℓ a b}
    {xs₁ xs₂ : Fin k → Expr ζ ℓ b} :
    E[Γ₁] ⊢ σ₁ ≡ σ₂ ⊣ Γ₀ →
    (∀ p, E[Γ₁] ⊢ xs₁ p ≡ xs₂ p :
      (Δ.entry (by omega) (by omega)).subst
        (Fin.append σ₁ fun previous : Fin p.val =>
          xs₁ (previous.castLE p.isLt.le))) →
    E[Γ₁] ⊢ Fin.append σ₁ xs₁ ≡ Fin.append σ₂ xs₂ ⊣ Γ₀ ++ Δ := by
  intro hσ hxs
  induction Δ using Tele.addInduction with
  | nil => simpa using hσ
  | snoc k Δ₀ t ih =>
    have .snoc hΔ _ := hΔ
    have hprefix (p : Fin k) : E[Γ₁] ⊢ xs₁ p.castSucc ≡ xs₂ p.castSucc :
        (Ctx.entry Δ₀ (by omega) (by omega)).subst
          (Fin.append σ₁ fun previous : Fin p.val =>
            xs₁ (previous.castLE p.castSucc.isLt.le)) := by
      simpa using hxs p.castSucc
    have hlast := hxs (Fin.last k)
    simpa [Subst.extend, ← Fin.append_snoc, ← Fin.init_def,
      show Fin.snoc (fun previous : Fin k => xs₁ (previous.castLE (Nat.le_succ k))) (xs₁ (Fin.last k)) = xs₁ from Fin.snoc_init_self xs₁] using
      (ih hΔ hprefix).extend hlast

theorem SubstEq.lift {t : Expr ζ ℓ n} {σ₁ σ₂ : Subst ζ ℓ n m} :
    E[Γ₁] ⊢ t typ →
    E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₂.snoc (t.subst σ₁)] ⊢ σ₁.lift ≡ σ₂.lift ⊣ Γ₁.snoc t := by
  intro ht hσ v
  cases v using Fin.lastCases with
  | last => simpa using hσ.left.lift ht (Fin.last n)
  | cast v =>
    simpa [Expr.wk_subst_lift] using (hσ v).wk (t.subst σ₁)

theorem SubstEq.liftN {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ n (n + k)} {σ₁ σ₂ : Subst ζ ℓ n m}
    (hΔ : TeleWF E P Γ₁ Δ) :
    E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₂ ++ Ctx.substN σ₁ k Δ] ⊢ σ₁.liftN k ≡ σ₂.liftN k ⊣ Γ₁ ++ Δ := by
  intro hσ
  induction Δ using Tele.addInduction with
  | nil => exact hσ
  | snoc k Δ t ih =>
    have .snoc hΔ ⟨u, _, ht⟩ := hΔ
    exact (ih hΔ).lift ⟨u, ht⟩

theorem Defeq.wkN {k : Nat} {Δ : Ctx ζ ℓ n (n + k)} {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ ++ Δ] ⊢ e₁.wkN k ≡ e₂.wkN k : t.wkN k := by
  intro h
  induction Δ using Tele.addInduction with
  | nil => exact h
  | snoc k Δ t ih => simpa! using ih.wk t

theorem Ctx.pi_isType {e : Expr ζ ℓ m} {l : Level ℓ} :
    E[Γ ++ Δ] ⊢ ok →
    E[Γ ++ Δ] ⊢ e : .sort l →
    ∃ l₁ : Level ℓ, E[Γ] ⊢ Δ.pi e : .sort l₁ := by
  intro hΓΔ he
  induction Δ generalizing l with
  | nil => exact ⟨l, he⟩
  | snoc Δ t ih =>
    have .snoc hΓΔ ⟨l₁, ht⟩ := hΓΔ
    exact ih hΓΔ (.forallEDF ht he he)

theorem Ctx.pi_isType_inv (Δ : Ctx ζ ℓ n m) {e : Expr ζ ℓ m} {l : Level ℓ} :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ Δ.pi e : .sort l →
    E[Γ ++ Δ] ⊢ ok ∧
    E[Γ ++ Δ] ⊢ e typ := by
  intro hΓ h
  induction Δ with
  | nil => exact ⟨hΓ, l, h⟩
  | snoc Δ t ih =>
    have ⟨hΓΔ, v, hforall⟩ := ih h
    have ⟨ht, he⟩ := hforall.forallE_inv
    exact ⟨hΓΔ.snoc ht, he⟩

theorem Ctx.lam_congr {e₁ e₂ t : Expr ζ ℓ m} :
    E[Γ ++ Δ] ⊢ ok →
    E[Γ ++ Δ] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ Δ.lam e₁ ≡ Δ.lam e₂ : Δ.pi t := by
  intro hΓΔ he
  induction Δ with
  | nil => exact he
  | snoc Δ t₁ ih =>
    have .snoc hΓΔ ⟨_, ht₁⟩  := hΓΔ
    have ⟨_, ht⟩ := he.regular
    exact ih hΓΔ (.lamDF ht₁ ht ht he he)

theorem Ctx.pi_applyBound {k : Nat} {Δ : Ctx ζ ℓ n (n + k)}
    {e : Expr ζ ℓ n} {t : Expr ζ ℓ (n + k)} {l : Level ℓ} :
    E[Γ ++ Δ] ⊢ ok →
    E[Γ ++ Δ] ⊢ t : .sort l →
    E[Γ] ⊢ e : Δ.pi t →
    E[Γ ++ Δ] ⊢ e.applyBound k : t := by
  intro hΓΔ ht he
  induction Δ using Tele.addInduction generalizing l with
  | nil => exact he
  | snoc k Δ t₁ ih =>
    have .snoc (hΓΔ : E[Γ ++ Δ] ⊢ ok) ⟨v, (ht' : E[Γ ++ Δ] ⊢ t₁ : .sort v)⟩ := hΓΔ
    simpa [Expr.applyBound, Expr.inst_wkFrom_last] using
      Defeq.appDF (ht'.wk t₁) (ht.wkFrom (Γ ++ Δ) #t[t₁] t₁)
        (by simpa [Expr.wk] using (ih hΓΔ (.forallEDF ht' ht ht) he).wk t₁)
        (by simpa using CtxWF.var (Fin.last (n + k)) (hΓΔ.snoc ⟨v, ht'⟩))
        (show E[(Γ ++ Δ).snoc t₁] ⊢ (t.wkFrom (n + k)).inst (.var (Fin.last (n + k))) : .sort l by
          simpa [Expr.inst_wkFrom_last])

theorem Ctx.pi_applyFamily {k : Nat} {Δ : Ctx ζ ℓ n (n + k)}
    {e₁ e₂ : Expr ζ ℓ n} {t : Expr ζ ℓ (n + k)}
    {xs₁ xs₂ : Fin k → Expr ζ ℓ n} :
    E[Γ] ⊢ ok →
    TeleWF E P Γ Δ →
    E[Γ ++ Δ] ⊢ t typ →
    (∀ p, E[Γ] ⊢ xs₁ p ≡ xs₂ p :
      (Δ.entry (by omega) (by omega)).subst
        (Fin.append Subst.id fun previous => xs₁ (previous.castLE p.isLt.le))) →
    E[Γ] ⊢ e₁ ≡ e₂ : Δ.pi t →
    E[Γ] ⊢ e₁.apps xs₁ ≡ e₂.apps xs₂ : t.subst (Fin.append Subst.id xs₁) := by
  intro hΓ hΔ ht hxs he
  induction Δ using Tele.addInduction with
  | nil => simpa using he
  | snoc k Δ₀ t₁ ih =>
    have .snoc hΔ ⟨u₁, _, ht₁⟩ := hΔ
    have ⟨_, ht⟩ := ht
    let init₁ : Fin k → Expr ζ ℓ n := fun p => xs₁ p.castSucc
    let init₂ : Fin k → Expr ζ ℓ n := fun p => xs₂ p.castSucc
    have hprefix (p : Fin k) : E[Γ] ⊢ init₁ p ≡ init₂ p :
        (Ctx.entry (p := n + p.val) Δ₀ (by omega) (by omega)).subst
          (Fin.append Subst.id fun previous =>
            init₁ (previous.castLE p.isLt.le)) := by
      simpa [init₁] using hxs p.castSucc
    have hlast : E[Γ] ⊢ xs₁ (Fin.last k) ≡ xs₂ (Fin.last k) :
        t₁.subst (Fin.append Subst.id init₁) := by
      have h := hxs (Fin.last k)
      simp at h
      exact h
    have hid : E[Γ] ⊢ Subst.id ⊣ Γ := fun v => by
      simp
      exact hΓ.var v
    have hσ := TeleWF.extendFamily hΔ hid fun p => (hprefix p).left
    have hΔt₁ : TeleWF E (fun _ => True) (Γ ++ Δ₀) #t[t₁] :=
      .snoc .nil ⟨u₁, trivial, ht₁⟩
    have htσ := ht.substitution (hσ.liftN hΔt₁)
    rw [Expr.apps_last, Expr.apps_last]
    simpa [init₁, init₂, Subst.liftN, Expr.inst_subst_lift, Subst.extend,
      ← Fin.append_snoc, ← Fin.init_def] using Defeq.appDF
      (ht₁.substitution hσ) htσ
      (ih hΔ ⟨_, .forallEDF ht₁ ht ht⟩ hprefix he)
      hlast
      (htσ.inst_congr hlast)

theorem Ctx.lam_applyFamily {k : Nat} {Δ : Ctx ζ ℓ n (n + k)}
    {e t : Expr ζ ℓ (n + k)} {xs : Fin k → Expr ζ ℓ n} :
    E[Γ] ⊢ ok →
    TeleWF E P Γ Δ →
    (∀ p, E[Γ] ⊢ xs p :
      (Δ.entry (by omega) (by omega)).subst
        (Fin.append Subst.id fun previous =>
          xs (previous.castLE p.isLt.le))) →
    E[Γ ++ Δ] ⊢ e : t →
    E[Γ] ⊢ (Δ.lam e).apps xs ≡
      e.subst (Fin.append Subst.id xs) :
      t.subst (Fin.append Subst.id xs) := by
  intro hΓ hΔ hxs he
  induction Δ using Tele.addInduction with
  | nil => simpa using he
  | snoc k Δ₀ t₁ ih =>
    have .snoc hΔ ⟨u₁, _, ht₁⟩ := hΔ
    have ⟨_, ht⟩ := he.regular
    let xs₀ : Fin k → Expr ζ ℓ n := fun p => xs p.castSucc
    have hprefix (p : Fin k) : E[Γ] ⊢ xs₀ p :
        (Ctx.entry (p := n + p.val) Δ₀ (by omega) (by omega)).subst
          (Fin.append Subst.id fun previous =>
            xs₀ (previous.castLE p.isLt.le)) := by
      simpa [xs₀] using hxs p.castSucc
    have hlast : E[Γ] ⊢ xs (Fin.last k) :
        t₁.subst (Fin.append Subst.id xs₀) := by
      have h := hxs (Fin.last k)
      simp at h
      exact h
    have hlam : E[Γ ++ Δ₀] ⊢ .lam t₁ e : .forallE t₁ t :=
      .lamDF ht₁ ht ht he he
    have hfun := ih hΔ hprefix hlam
    have hid : E[Γ] ⊢ Subst.id ⊣ Γ := fun v => by
      rw [Expr.subst_id]
      exact hΓ.var v
    have hσ := TeleWF.extendFamily hΔ hid hprefix
    have ht₁σ := ht₁.substitution hσ
    have hΔt₁ : TeleWF E (fun _ => True) (Γ ++ Δ₀) #t[t₁] :=
      .snoc .nil ⟨u₁, trivial, ht₁⟩
    have hσlift := hσ.liftN hΔt₁
    have htσ := ht.substitution hσlift
    have he₀ := he.substitution hσlift
    have hresult := htσ.inst_congr hlast
    have heresult := he₀.inst_congr hlast
    have happ := Defeq.appDF ht₁σ htσ hfun hlast hresult
    have hbeta := Defeq.beta ht₁σ htσ he₀ hlast hresult heresult
    rw [Expr.apps_last]
    simpa [xs₀, Ctx.lam, Subst.liftN, Expr.inst_subst_lift,
      Subst.extend, ← Fin.append_snoc, ← Fin.init_def] using happ.trans hbeta

theorem TeleWF.ofTypes {k : Nat} {ts : Fin k → Expr ζ ℓ n}
    (hts : ∀ i, ∃ u, P u ∧ E[Γ] ⊢ ts i : .sort u) :
    TeleWF E P Γ (Ctx.ofTypes ts) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    have ⟨u, hu, ht⟩ := hts (Fin.last k)
    exact .snoc (ih fun i => hts i.castSucc) ⟨u, hu, by simpa using ht.wkN⟩

theorem Ctx.pi_ofTypes_congr {k : Nat} {ts₁ ts₂ : Fin k → Expr ζ ℓ n}
    {e₁ e₂ : Expr ζ ℓ (n + k)} {u : Level ℓ} :
    (∀ i, ∃ u, E[Γ] ⊢ ts₁ i ≡ ts₂ i : .sort u) →
    E[Γ ++ Ctx.ofTypes ts₁] ⊢ e₁ ≡ e₂ : .sort u →
    ∃ v, E[Γ] ⊢ Ctx.pi e₁ (Ctx.ofTypes ts₁) ≡
      Ctx.pi e₂ (Ctx.ofTypes ts₂) : .sort v := by
  intro hts he
  induction k generalizing u with
  | zero => exact ⟨u, he⟩
  | succ k ih =>
    have ⟨v, ht⟩ := hts (Fin.last k)
    have ht := ht.wkN (Δ := Ctx.ofTypes fun i => ts₁ i.castSucc)
    simp at ht
    exact ih (fun i => hts i.castSucc) (.forallEDF ht he (ht.snocConv he))

theorem SubstEq.get {σ₁ σ₂ : Subst ζ ℓ n m} (v : Var n) :
    E[Γ₁] ⊢ ok →
    E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁ →
    ∃ u, E[Γ₂] ⊢ (Γ₁.get v).subst σ₁ ≡ (Γ₁.get v).subst σ₂ : .sort u :=
  fun hΓ h =>
    have ⟨u, ht⟩ := hΓ.get v
    ⟨u, Defeq.substitution_congr hΓ h ht⟩

namespace SubstEq

variable {σ₁ σ₂ σ₃ : Subst ζ ℓ n m}

theorem symm :
    E[Γ₁] ⊢ ok →
    E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₂] ⊢ σ₂ ≡ σ₁ ⊣ Γ₁ :=
  fun hΓ h v => have ⟨_, ht⟩ := h.get v hΓ; .defeqDF ht (h v).symm

theorem trans :
    E[Γ₁] ⊢ ok →
    E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₂] ⊢ σ₂ ≡ σ₃ ⊣ Γ₁ →
    E[Γ₂] ⊢ σ₁ ≡ σ₃ ⊣ Γ₁ :=
  fun hΓ h₁ h₂ v => have ⟨_, ht⟩ := h₁.get v hΓ; (h₁ v).trans (.defeqDF ht.symm (h₂ v))

end SubstEq

theorem IsTypeEq.substitution_congr {σ₁ σ₂ : Subst ζ ℓ n m}
    {t₁ t₂ : Expr ζ ℓ n} :
    E[Γ₁] ⊢ ok →
    E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₁] ⊢ t₁ ≡ t₂ typ →
    E[Γ₂] ⊢ t₁.subst σ₁ ≡ t₂.subst σ₂ typ :=
  fun hΓ hσ h =>
    have ⟨_, ht₂⟩ := h.isType.2
    (h.substitution hσ.left).trans (.ofDefEq (Defeq.substitution_congr hΓ hσ ht₂))

section

variable {p : Nat} {Γ₃ : Ctx ζ ℓ 0 p}

theorem SubstWF.comp {σ₁ : Subst ζ ℓ n m} {σ₂ : Subst ζ ℓ m p} :
    E[Γ₂] ⊢ σ₁ ⊣ Γ₁ →
    E[Γ₃] ⊢ σ₂ ⊣ Γ₂ →
    E[Γ₃] ⊢ σ₁.comp σ₂ ⊣ Γ₁ := by
  intro hσ₁ hσ₂ v
  simpa using (hσ₁ v).substitution hσ₂

theorem SubstEq.comp {σ₁ σ₁' : Subst ζ ℓ n m} {σ₂ σ₂' : Subst ζ ℓ m p} :
    E[Γ₂] ⊢ ok →
    E[Γ₂] ⊢ σ₁ ≡ σ₁' ⊣ Γ₁ →
    E[Γ₃] ⊢ σ₂ ≡ σ₂' ⊣ Γ₂ →
    E[Γ₃] ⊢ σ₁.comp σ₂ ≡ σ₁'.comp σ₂' ⊣ Γ₁ :=
  fun hΓ₂ hσ₁ hσ₂ v => by
    simpa using Defeq.substitution_congr hΓ₂ hσ₂ (hσ₁ v)

end

end Metalean
