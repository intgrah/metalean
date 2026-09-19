/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Defs
public import Metalean.Syntax.Substitution
public import Metalean.Syntax.Weakening
import Metalean.Syntax.Structure.Projection

@[expose] public section

namespace Metalean

variable {ζ : Sigs} (E : Env ζ) {ℓ n m : Nat}
  (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m) (σ : Subst ζ ℓ n m)

private inductive SubstImage (v : Var n) : Prop where
  | typed (h : E[Γ₂] ⊢ₛ σ v ≡ σ v : (Γ₁.get v).subst σ)
  | renamed (w : Var m) (hσ : σ v = .var w)
      (htype : Γ₂.get w = (Γ₁.get v).subst σ)

private def SubstRen : Prop :=
  ∀ v : Var n, SubstImage E Γ₁ Γ₂ σ v

variable {E Γ₁ Γ₂ σ} {σ₁ σ₂ : Subst ζ ℓ n m} {σ' σ₁' σ₂' : Subst ζ ℓ (n + 1) m} {Γ : Ctx ζ ℓ 0 m}

namespace DefeqStrong

private theorem substOf
    (P : ∀ {n m : Nat}, Ctx ζ ℓ 0 n → Ctx ζ ℓ 0 m → Subst ζ ℓ n m → Prop)
    (image : ∀ {n m : Nat} {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {σ : Subst ζ ℓ n m},
      P Γ₁ Γ₂ σ → SubstRen E Γ₁ Γ₂ σ)
    (lift : ∀ {n m : Nat} {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {σ : Subst ζ ℓ n m}
      {t : Expr ζ ℓ n}, P Γ₁ Γ₂ σ → P (Γ₁.snoc t) (Γ₂.snoc (t.subst σ)) σ.lift)
    {n : Nat} {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {e₁ e₂ t : Expr ζ ℓ n}
    {σ : Subst ζ ℓ n m} (hσ : P Γ₁ Γ₂ σ) :
    E[Γ₁] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ₂] ⊢ₛ e₁.subst σ ≡ e₂.subst σ : t.subst σ := by
  intro h
  induction h generalizing m Γ₂ with
    try simp! [Expr.inst_subst, Expr.wk_subst_lift] at *
  | var _ ih =>
    cases image hσ _ with
    | typed d => exact d
    | renamed w hw htype =>
      simpa [hw, ← htype] using .var
        (by simpa [htype] using ih hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hσ) (ih₂ hσ)
  | sortDF => exact .sortDF
  | constDF _ ihtype =>
    exact .constDF (ihtype hσ)
  | indDF _ _ ihps ihis =>
    exact .indDF (ihps · hσ) (ihis · hσ)
  | ctorDF _ _ _ _ _ _ ihps ihfields ihrecFields ihfieldTypes ihrecFieldTypes ihtype =>
    exact .ctorDF (ihps · hσ) (ihfields · hσ) (ihrecFields · hσ)
      (ihfieldTypes · hσ) (ihrecFieldTypes · hσ) (ihtype hσ)
  | @recrDF _ _ ι head target ls u ps _ ms₁ ms₂ mins₁ mins₂
      is _ maj _ hallowed _ _ _ _ _ _ ihps ihms ihmins
      ihis ihmaj ihresult =>
    exact .recrDF hallowed (ihps · hσ) (ihms · hσ)
      (ihmins · · hσ) (ihis · hσ) (ihmaj hσ) (ihresult hσ)
  | appDF _ _ _ _ _ iht iht' ihf ihe ihres =>
    exact .appDF
      (iht hσ) (iht' (lift hσ)) (ihf hσ) (ihe hσ) (ihres hσ)
  | lamDF _ _ _ _ _ iht iht' iht₂' ihbody ihbody' =>
    exact .lamDF (iht hσ) (iht' (lift hσ)) (iht₂' (lift hσ))
      (ihbody (lift hσ)) (ihbody' (lift hσ))
  | forallEDF _ _ _ iht ihbody ihbody' =>
    exact .forallEDF (iht hσ) (ihbody (lift hσ)) (ihbody' (lift hσ))
  | defeqDF _ _ iht ihe => exact .defeqDF (iht hσ) (ihe hσ)
  | beta _ _ _ _ _ _ iht iht' ihbody ihe ihres ihresult =>
    exact .beta (iht hσ) (iht' (lift hσ)) (ihbody (lift hσ))
      (ihe hσ) (ihres hσ) (ihresult hσ)
  | zeta _ _ _ _ iht ihv ihr ihbody =>
    exact .zeta (iht hσ) (ihv hσ) (ihr hσ) (ihbody hσ)
  | @eta n Γ₁ l₁ l₂ e t t' _ _ _ _ _ iht iht' ihtwk ihewk ihe =>
    have hlift : ((fun w => σ.lift.lift (Ren.wkFrom n w)) :
        Subst ζ ℓ (n + 1) (m + 2)) = fun v => (σ.lift v).wkFrom m := by
      funext w
      cases w using Fin.lastCases with
      | last => simp
      | cast w =>
        simp
        rfl
    exact .eta
      (iht hσ) (iht' (lift hσ))
      (by simpa [Expr.wk_subst_lift] using ihtwk (lift hσ))
      (by
        have dewk := ihewk (lift hσ)
        simp! [Expr.wk_subst_lift, Expr.wkFrom_subst σ.lift.lift] at dewk
        rwa [hlift, ← Expr.subst_wkFrom σ.lift] at dewk)
      (ihe hσ)
  | etaStruct h _ _ _ ihps ihmaj ihrebuild =>
    exact .etaStruct h
      (fun p => ihps p hσ)
      (ihmaj hσ)
      (ihrebuild hσ)
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact .proofIrrel (ihp hσ) (ihh hσ) (ihh' hσ)
  | iota hallowed _ _ _ _ _ _ _ _ ihps ihms ihmins ihfields ihrecFields ihtype ihlhs ihrhs =>
    exact .iota hallowed (ihps · hσ) (ihms · hσ) (ihmins · · hσ)
      (ihfields · hσ) (ihrecFields · hσ) (ihtype hσ) (ihlhs hσ) (ihrhs hσ)
  | quotDF _ _ iht ihr =>
    exact .quotDF (iht hσ) (ihr hσ)
  | quotMkDF _ _ _ ihα ihr iha =>
    exact .quotMkDF (ihα hσ) (ihr hσ) (iha hσ)
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    exact .quotLiftDF (ihα hσ) (ihr hσ) (ihβ hσ) (ihf hσ) (ihh hσ) (iha hσ)
  | quotIndDF _ _ _ _ _ _ ihα ihr ihβ ihf iha ihresult =>
    exact .quotIndDF (ihα hσ) (ihr hσ) (ihβ hσ) (ihf hσ) (iha hσ) (ihresult hσ)
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha ihlhs ihrhs =>
    exact .quotIota (ihα hσ) (ihr hσ) (ihβ hσ) (ihf hσ) (ihh hσ)
      (iha hσ) (ihlhs hσ) (ihrhs hσ)
  | delta _ _ ihtype ihvalue =>
    exact .delta (ihtype hσ) (ihvalue hσ)

theorem wkFrom {cut n : Nat} {e₁ e₂ t : Expr ζ ℓ n}
    (Γ₀ : Ctx ζ ℓ 0 cut) (Δ : Ctx ζ ℓ cut n) (t₁ : Expr ζ ℓ cut) :
    E[Γ₀ ++ Δ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ₀.insert t₁ Δ] ⊢ₛ e₁.wkFrom cut ≡ e₂.wkFrom cut : t.wkFrom cut := by
  simpa [Expr.wkFrom_eq_subst] using
    substOf Subst.Renames
      (fun hσ v => have ⟨w, hw, htype⟩ := hσ v; .renamed w hw htype)
      Subst.Renames.lift (Subst.renames_wkFrom Γ₀ t₁ Δ)

theorem wk {e₁ e₂ t : Expr ζ ℓ m} (t₁ : Expr ζ ℓ m) :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ.snoc t₁] ⊢ₛ e₁.wk ≡ e₂.wk : t.wk :=
  wkFrom Γ #t[] t₁

end DefeqStrong

private theorem SubstRen.lift {t : Expr ζ ℓ n} (h : SubstRen E Γ₁ Γ₂ σ) :
    SubstRen E (Γ₁.snoc t) (Γ₂.snoc (t.subst σ)) σ.lift := fun v => by
  cases v using Fin.lastCases with
  | last =>
    exact .renamed (Fin.last m) (Subst.lift_last σ)
      (by simp [Expr.wk_subst_lift])
  | cast v =>
    cases h v with
    | typed d =>
      refine .typed ?_
      simpa [Expr.wk_subst_lift] using d.wk (t.subst σ)
    | renamed w hw htype =>
      refine .renamed w.castSucc ?_ ?_
      · simp [hw, Expr.wk]
      · simp [Expr.wk_subst_lift]
        exact congrArg Expr.wk htype

private theorem SubstRen.liftN (h : SubstRen E Γ₁ Γ₂ σ)
    (k : Nat) (Δ : Ctx ζ ℓ n (n + k)) :
    SubstRen E (Γ₁ ++ Δ) (Γ₂ ++ Ctx.substN σ k Δ) (σ.liftN k) := by
  induction Δ using Tele.addInduction with
  | nil => exact h
  | snoc k Δ t ih => simpa [Ctx.substN, Subst.liftN] using ih.lift

private theorem SubstRen.inst
    {t e : Expr ζ ℓ m} (he : E[Γ] ⊢ₛ e : t) :
    SubstRen E (Γ.snoc t) Γ (Subst.id.extend e) := fun v => by
  cases v using Fin.lastCases with
  | last =>
    exact .typed (by simpa [Expr.wk_subst_extend] using he)
  | cast v =>
    refine .renamed v (Subst.extend_castSucc _ _ _) ?_
    simp
    change _ = (Γ.get v).wk.inst e
    simp

namespace DefeqStrong

private theorem substRen {e₁ e₂ t : Expr ζ ℓ n} :
    SubstRen E Γ₁ Γ₂ σ →
    E[Γ₁] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ₂] ⊢ₛ e₁.subst σ ≡ e₂.subst σ : t.subst σ :=
  substOf (SubstRen E) id SubstRen.lift

theorem substitution {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ₂] ⊢ₛ σ ⊣ Γ₁ →
    E[Γ₁] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ₂] ⊢ₛ e₁.subst σ ≡ e₂.subst σ : t.subst σ :=
  fun hσ h => h.substRen fun v => .typed (hσ v)

theorem inst_congr {e₁ e₂ t : Expr ζ ℓ m} {e' t' : Expr ζ ℓ (m + 1)} :
    E[Γ.snoc t] ⊢ₛ e' : t' →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e'.inst e₁ ≡ e'.inst e₂ : t'.inst e₁ := by
  intro he' he
  have ⟨u, ht⟩ := he.regular
  have ⟨v, ht'⟩ := he'.regular
  have he₁ := he.left
  have he₂ := he.right
  have hte₁' : E[Γ] ⊢ₛ t'.inst e₁ : .sort v := ht'.substRen (SubstRen.inst he₁)
  have hte₂' : E[Γ] ⊢ₛ t'.inst e₂ : .sort v := ht'.substRen (SubstRen.inst he₂)
  have hte' :=
    (DefeqStrong.beta ht .sortDF ht' he₁ .sortDF hte₁').symm.trans
      ((DefeqStrong.appDF ht .sortDF
        (.lamDF ht .sortDF .sortDF ht' ht') he .sortDF).trans
          (.beta ht .sortDF ht' he₂ .sortDF hte₂'))
  exact (DefeqStrong.beta ht ht' he' he₁ hte₁'
    (he'.substRen (SubstRen.inst he₁))).symm.trans
      ((DefeqStrong.appDF ht ht' (.lamDF ht ht' ht' he' he') he hte').trans
        (.defeqDF hte'.symm (.beta ht ht' he' he₂ hte₂'
          (he'.substRen (SubstRen.inst he₂)))))

theorem snocConv {t₁ t₂ : Expr ζ ℓ m} {l : Level ℓ}
    {e₁' e₂' t' : Expr ζ ℓ (m + 1)} :
    E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort l →
    E[Γ.snoc t₁] ⊢ₛ e₁' ≡ e₂' : t' →
    E[Γ.snoc t₂] ⊢ₛ e₁' ≡ e₂' : t' := by
  intro ht d
  have hσ : SubstRen E (Γ.snoc t₁) (Γ.snoc t₂) Subst.id := fun v => by
    cases v using Fin.lastCases with
    | last =>
      refine .typed ?_
      rw [Ctx.get_last, Expr.subst_id]
      refine .defeqDF (l := l) (t₁ := t₂.wk) ?_ ?_
      · exact ht.symm.wk t₂
      · rw [← Ctx.get_last Γ t₂]
        refine .var (l := l) ?_
        rw [Ctx.get_last]
        exact (ht.right).wk t₂
    | cast v =>
      exact .renamed v.castSucc rfl <| by
        rw [Expr.subst_id, Γ.get_snoc t₂ v.castSucc (Nat.ne_of_lt v.isLt),
          Γ.get_snoc t₁ v.castSucc (Nat.ne_of_lt v.isLt)]
  simpa using d.substRen hσ

end DefeqStrong

theorem IsTypeStrong.substitution {t : Expr ζ ℓ n} :
    E[Γ₁] ⊢ₛ t typ →
    E[Γ₂] ⊢ₛ σ ⊣ Γ₁ →
    E[Γ₂] ⊢ₛ t.subst σ typ :=
  fun ⟨u, ht⟩ hσ => ⟨u, ht.substitution hσ⟩

theorem DefeqStrong.inst_congr₂ {t e₁ e₂ : Expr ζ ℓ m} {e₁' e₂' t' : Expr ζ ℓ (m + 1)} :
    E[Γ.snoc t] ⊢ₛ e₁' ≡ e₂' : t' →
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e₁'.inst e₁ ≡ e₂'.inst e₂ : t'.inst e₁ :=
  fun he' h => (he'.substRen (SubstRen.inst h.left)).trans
    (he'.right.inst_congr h)

theorem SubstWFStrong.extend {t : Expr ζ ℓ n} {e : Expr ζ ℓ m} :
    E[Γ₂] ⊢ₛ e : t.subst σ →
    E[Γ₂] ⊢ₛ σ ⊣ Γ₁ →
    E[Γ₂] ⊢ₛ σ.extend e ⊣ Γ₁.snoc t := by
  intro he hσ v
  cases v using Fin.lastCases with
  | last => simpa [Expr.wk_subst_extend]
  | cast v => simpa [Expr.wk_subst_extend] using hσ v

theorem SubstEqStrong.nil {σ₁ σ₂ : Subst ζ ℓ 0 m} :
    E[Γ] ⊢ₛ σ₁ ≡ σ₂ ⊣ #t[] := nofun

theorem SubstEqStrong.extend {t : Expr ζ ℓ n} {e₁ e₂ : Expr ζ ℓ m} :
    E[Γ₂] ⊢ₛ e₁ ≡ e₂ : t.subst σ₁ →
    E[Γ₂] ⊢ₛ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₂] ⊢ₛ σ₁.extend e₁ ≡ σ₂.extend e₂ ⊣ Γ₁.snoc t := by
  intro he hσ v
  cases v using Fin.lastCases with
  | last => simpa [Expr.wk_subst_extend]
  | cast v => simpa [Expr.wk_subst_extend] using hσ v

theorem SubstWFStrong.wk_comp {t : Expr ζ ℓ n} :
    E[Γ₂] ⊢ₛ σ' ⊣ Γ₁.snoc t →
    E[Γ₂] ⊢ₛ Subst.wk.comp σ' ⊣ Γ₁ :=
  fun hσ v => by simpa [Expr.wk_subst] using hσ v.castSucc

theorem SubstEqStrong.wk_comp {t : Expr ζ ℓ n} :
    E[Γ₂] ⊢ₛ σ₁' ≡ σ₂' ⊣ Γ₁.snoc t →
    E[Γ₂] ⊢ₛ Subst.wk.comp σ₁' ≡ Subst.wk.comp σ₂' ⊣ Γ₁ :=
  fun hσ v => by simpa [Expr.wk_subst] using hσ v.castSucc

theorem WFTeleStrong.substitution {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ n (n + k)} :
    E[Γ₂] ⊢ₛ σ ⊣ Γ₁ →
    WFTeleStrong E P Γ₁ Δ →
    WFTeleStrong E P Γ₂ (Δ.substN σ k) := by
  intro hσ hΔ
  induction Δ using Tele.addInduction with
  | nil => exact .nil
  | snoc k Δ t ih =>
    have hren : SubstRen E Γ₁ Γ₂ σ := fun v => .typed (hσ v)
    have .snoc hΔ ⟨u, hu, ht⟩ := hΔ
    exact .snoc (ih hΔ) ⟨u, hu, ht.substRen (hren.liftN k Δ)⟩

theorem SubstWFStrong.lift {t : Expr ζ ℓ n} :
    E[Γ₁] ⊢ₛ t typ →
    E[Γ₂] ⊢ₛ σ ⊣ Γ₁ →
    E[Γ₂.snoc (t.subst σ)] ⊢ₛ σ.lift ⊣ Γ₁.snoc t := by
  intro ⟨u, ht⟩ hσ v
  cases v using Fin.lastCases with
  | last =>
    simp [Expr.wk_subst_lift]
    rw [← Γ₂.get_last (t.subst σ)]
    exact .var <| by
      simpa [Expr.wk] using (ht.substitution hσ).wk (t.subst σ)
  | cast v => simpa [Expr.wk_subst_lift] using (hσ v).wk (t.subst σ)

theorem SubstWFStrong.liftN {k : Nat} {P : Level ℓ → Prop}
    {Δ : Ctx ζ ℓ n (n + k)}
    (hΔ : WFTeleStrong E P Γ₁ Δ) :
    E[Γ₂] ⊢ₛ σ ⊣ Γ₁ →
    E[Γ₂ ++ Ctx.substN σ k Δ] ⊢ₛ σ.liftN k ⊣ Γ₁ ++ Δ := by
  intro hσ
  induction Δ using Tele.addInduction with
  | nil => exact hσ
  | snoc k Δ t ih =>
    have .snoc hΔ ⟨u, _, ht⟩ := hΔ
    exact (ih hΔ).lift ⟨u, ht⟩

end Metalean
