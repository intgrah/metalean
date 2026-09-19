/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Metatheory.Injectivity
import Metalean.Strong
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {e t t₁ t₂ : Expr ζ ℓ n}

abbrev UniqTyFrom (E : Env ζ) (Γ : Ctx ζ ℓ 0 n) (e t₁ : Expr ζ ℓ n) : Prop :=
  ∀ {t₂}, E[Γ] ⊢ₛ e : t₂ → E[Γ] ⊢ₛ t₁ ≡ t₂ typ

local notation:65 E "[" Γ "]" " ⊢ " e " !: " t:lead => UniqTyFrom E Γ e t

namespace UniqTyFrom

theorem conv {l : Level ℓ} :
    E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort l →
    E[Γ] ⊢ e !: t₂ →
    E[Γ] ⊢ e !: t₁ :=
  fun ht h _ hc => (IsTypeEq.ofDefEq ht).trans (h hc)

theorem var {v : Var n} : E[Γ] ⊢ .var v !: Γ.get v :=
  fun hc => hc.var_inv.symm

theorem sort {l : Level ℓ} : E[Γ] ⊢ .sort l !: .sort (.succ l) :=
  fun hc => hc.sort_inv.symm

theorem const {kind : ConstKind} {k : Nat} {η : Head ζ (.const kind k)}
    {ls : Fin k → Level ℓ} :
    E[Γ] ⊢ .const η ls !: ((E.get η).constType.instL ls).wkClosed :=
  fun hc => hc.const_inv.symm

section

variable {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
  {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ n} {ms : Fin ι.nsorts → Expr ζ ℓ n}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
  {is : Fin (ι.nindices s) → Expr ζ ℓ n} {maj : Expr ζ ℓ n}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
  {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}

theorem ind : E[Γ] ⊢ .ind η s ls ps is !: .sort ((E.get η).block.level.inst ls) :=
  fun hc =>
    have ⟨_, _, _, _, ht⟩ := hc.ind_inv
    ht.symm

theorem ctor :
    E[Γ] ⊢ .ctor η s c ls ps fds recFds !:
      .ind η s ls ps (((E.get η).block.ctors s c).targetIndex ls ps fds) :=
  fun hc =>
    have ⟨_, _, _, _, _, _, hresult, ht⟩ := hc.ctor_inv
    (ht.trans (.ofDefEq hresult)).symm

theorem recr :
    E[Γ] ⊢ .recr η s ls l ps ms mins is maj !: Inductive.motiveResult (ms s) is maj :=
  fun hc =>
    have ⟨_, _, _, _, _, _, _, _, _, _, _, hresult, ht⟩ := hc.recr_inv
    (ht.trans (.ofDefEq hresult)).symm

end

section

variable {η : Head ζ .quot} {l l₁ l₂ : Level ℓ} {α r β f h a : Expr ζ ℓ n}

theorem quot : E[Γ] ⊢ .quot η l α r !: .sort l :=
  fun hc => hc.quot_inv.symm

theorem quotMk : E[Γ] ⊢ .quotMk η l α r a !: .quot η l α r :=
  fun hc => hc.quotMk_inv.symm

theorem quotLift : E[Γ] ⊢ .quotLift η l₁ l₂ α r β f h a !: β :=
  fun hc => hc.quotLift_inv.symm

theorem quotInd : E[Γ] ⊢ .quotInd η l α r β f a !: .app β a :=
  fun hc =>
    have ⟨_, _, _, _, _, _, _, _, _, _, hresult, ht⟩ := hc.quotInd_prem
    (ht.trans (.ofDefEq hresult)).symm

end

section

variable {l l₁ l₂ : Level ℓ} {e' t' : Expr ζ ℓ (n + 1)}

theorem lam :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ t : .sort l →
    E[Γ.snoc t] ⊢ e' !: t' →
    E[Γ] ⊢ .lam t e' !: .forallE t t' :=
  fun hΓ ht hl _ hc =>
    have ⟨_, he', hres⟩ := hc.lam_inv hΓ
    (IsTypeEq.forallE_congr ht (hl he')).trans hres.symm

theorem letE {v r : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ e'.inst v !: r →
    E[Γ] ⊢ .letE t v e' !: r :=
  fun hΓ hl _ hc =>
    have ⟨_, _, _, he, hres⟩ := hc.letE_inv hΓ
    (hl he).trans hres.symm

theorem app (ho : E.Ordered) {f a : Expr ζ ℓ n} (hinst : t'.inst a = t₂) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ f !: .forallE t₁ t' →
    E[Γ] ⊢ₛ a : t₁ →
    E[Γ] ⊢ .app f a !: t₂ := by
  subst hinst
  intro hΓ hl ha _ hc
  have ⟨_, _, hf, _, ht⟩ := hc.app_inv
  have ⟨_, hcod⟩ := IsTypeEq.forallE_inj ho hΓ (hl hf)
  exact (IsTypeEq.instCongr hΓ ha hcod).trans ht.symm

theorem forallE (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ t !: .sort l₁ →
    E[Γ.snoc t] ⊢ t' !: .sort l₂ →
    E[Γ] ⊢ .forallE t t' !: .sort (.imax l₁ l₂) := by
  intro hΓ ht ht' _ hc
  have ⟨_, _, hu, hv, hres⟩ := hc.forallE_ty_inv
  obtain rfl := IsTypeEq.sort_inj ho hΓ (ht hu)
  obtain rfl := IsTypeEq.sort_inj ho (hΓ.snoc ⟨_, hu⟩) (ht' hv)
  exact hres.symm

end

end UniqTyFrom

open UniqTyFrom in
theorem DefeqStrong.uniqTy (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ e : t₁ →
    E[Γ] ⊢ₛ e : t₂ →
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ := by
  intro hΓ
  suffices huniq : ∀ {e₁ e₂ t},
      E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
      E[Γ] ⊢ e₁ !: t ∧ E[Γ] ⊢ e₂ !: t from
    fun h₁ => (huniq h₁).1
  clear uniqTy e t₁ t₂
  intro e₁ e₂ t h
  induction h with
  | var => exact ⟨UniqTyFrom.var, UniqTyFrom.var⟩
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih₁ ih₂ => exact ⟨(ih₁ hΓ).1, (ih₂ hΓ).2⟩
  | sortDF => exact ⟨sort, sort⟩
  | constDF => exact ⟨const, const⟩
  | indDF => exact ⟨ind, ind⟩
  | ctorDF _ _ _ _ _ hresult => exact ⟨ctor, conv hresult ctor⟩
  | recrDF _ _ _ _ _ _ hresult => exact ⟨recr, conv hresult recr⟩
  | appDF _ _ _ ha hresult _ _ ihf _ _ =>
    have ⟨hfl, hfr⟩ := ihf hΓ
    exact ⟨app ho rfl hΓ hfl ha.left, conv hresult (app ho rfl hΓ hfr ha.right)⟩
  | lamDF ht ht' ht₂' _ _ _ _ _ ihe' ihbody' =>
    exact ⟨lam hΓ ht.left (ihe' (hΓ.snoc ⟨_, ht.left⟩)).1,
      conv (.forallEDF ht ht'.left ht₂'.left)
        (lam hΓ ht.right (ihbody' (hΓ.snoc ⟨_, ht.right⟩)).2)⟩
  | forallEDF ht _ _ iht ihe' ihbody' =>
    have ⟨htl, htr⟩ := iht hΓ
    exact ⟨forallE ho hΓ htl (ihe' (hΓ.snoc ⟨_, ht.left⟩)).1,
      forallE ho hΓ htr (ihbody' (hΓ.snoc ⟨_, ht.right⟩)).2⟩
  | defeqDF ht _ _ ih =>
    have ⟨hl, hr⟩ := ih hΓ
    exact ⟨conv ht.symm hl, conv ht.symm hr⟩
  | beta ht _ _ ha _ _ _ _ ihe' _ _ ihbody =>
    exact ⟨app ho rfl hΓ (lam hΓ ht (ihe' (hΓ.snoc ⟨_, ht⟩)).1) ha, (ihbody hΓ).1⟩
  | zeta _ _ _ _ _ _ _ ihbody =>
    have ⟨hr, _⟩ := ihbody hΓ
    exact ⟨letE hΓ hr, hr⟩
  | @eta _ Γ _ _ _ _ _ ht _ _ _ _ _ _ _ ihfn ihe =>
    have hΓt : E[Γ.snoc _] ⊢ₛ ok := hΓ.snoc ⟨_, ht⟩
    have hvar := hΓt.var (Fin.last _)
    rw [Ctx.get_last] at hvar
    exact ⟨lam hΓ ht (app ho (Expr.inst_wkFrom_last _) hΓt (ihfn hΓt).1 hvar), (ihe hΓ).1⟩
  | proofIrrel _ _ _ _ ih₁ ih₂ => exact ⟨(ih₁ hΓ).1, (ih₂ hΓ).1⟩
  | iota _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihlhs ihrhs => exact ⟨(ihlhs hΓ).1, (ihrhs hΓ).1⟩
  | etaStruct _ _ _ _ _ ihmaj ihrebuild => exact ⟨(ihrebuild hΓ).1, (ihmaj hΓ).1⟩
  | quotDF => exact ⟨quot, quot⟩
  | quotMkDF hα hr => exact ⟨quotMk, conv (.quotDF hα hr) quotMk⟩
  | quotLiftDF _ _ hβ => exact ⟨quotLift, conv hβ quotLift⟩
  | quotIndDF _ _ _ _ _ hresult => exact ⟨quotInd, conv hresult quotInd⟩
  | quotIota _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihlhs ihrhs => exact ⟨(ihlhs hΓ).1, (ihrhs hΓ).1⟩
  | delta _ _ _ ihvalue => exact ⟨const, (ihvalue hΓ).1⟩

theorem IsTypeEq.sort_uniq (ho : E.Ordered) :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    ∃ l, E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort l := by
  intro hΓ h
  induction h using Relation.TransGen.trans_induction_on with
  | single h => exact h
  | trans _ _ ih₁ ih₂ =>
    have ⟨l₁, h₁⟩ := ih₁
    have ⟨l₂, h₂⟩ := ih₂
    obtain rfl := IsTypeEq.sort_inj ho hΓ (DefeqStrong.uniqTy ho hΓ h₁.right h₂.left)
    exact ⟨l₁, h₁.trans h₂⟩

end Metalean
