/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Defs
public import Metalean.Syntax.Eq
import Metalean.Strong.Substitution
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

namespace Quot

variable {α α' : Expr ζ ℓ n} {u : Level ℓ}

theorem relType_congr :
    E[Γ] ⊢ₛ α ≡ α' : .sort u →
    E[Γ] ⊢ₛ relType α ≡ relType α' : .sort (.imax u (.imax u .one)) :=
  fun hα =>
    .forallEDF hα
      (.forallEDF (hα.wk α) .sortDF .sortDF)
      (.forallEDF (hα.wk α') .sortDF .sortDF)

end Quot

section TypeFormers

variable {η : Head ζ .quot} {l : Level ℓ} {α r β f : Expr ζ ℓ n}

theorem Quot.motiveType_isTypeStrong :
    E[Γ] ⊢ₛ α : .sort l →
    E[Γ] ⊢ₛ r : Quot.relType α →
    E[Γ] ⊢ₛ Quot.motiveType η l α r typ :=
  fun hα hr => ⟨_, .forallEDF (.quotDF hα hr) .sortDF .sortDF⟩

theorem Quot.minorType_isTypeStrong :
    E[Γ] ⊢ₛ α : .sort l →
    E[Γ] ⊢ₛ r : Quot.relType α →
    E[Γ] ⊢ₛ β : Quot.motiveType η l α r →
    E[Γ] ⊢ₛ Quot.minorType η l α r β typ := by
  intro hα hr hβ
  have hαwk : E[Γ.snoc α] ⊢ₛ α.wk : .sort l := hα.wk α
  have hrwk : E[Γ.snoc α] ⊢ₛ r.wk : Quot.relType α.wk := by
    simpa [Expr.wk] using hr.wk α
  have hvar : E[Γ.snoc α] ⊢ₛ .var (Fin.last n) : α.wk := by
    have := DefeqStrong.var (Γ := Γ.snoc α) (v := Fin.last n) (by rw [Ctx.get_last]; exact hαwk)
    rwa [Ctx.get_last] at this
  have hquotwk : E[Γ.snoc α] ⊢ₛ .quot η l α.wk r.wk : .sort l := .quotDF hαwk hrwk
  have hmk : E[Γ.snoc α] ⊢ₛ Quot.minorQuotMk η l α r : .quot η l α.wk r.wk :=
    .quotMkDF hαwk hrwk hvar
  have hβwk : E[Γ.snoc α] ⊢ₛ β.wk : .forallE (.quot η l α.wk r.wk) .prop := by
    simpa [Quot.motiveType, Expr.wk] using hβ.wk α
  have happ : E[Γ.snoc α] ⊢ₛ .app β.wk (Quot.minorQuotMk η l α r) : .prop :=
    .appDF (t' := .prop) hquotwk .sortDF hβwk hmk .sortDF
  exact ⟨_, .forallEDF hα happ happ⟩

theorem Quot.eqApp_typed {ηeq : Head ζ (.inductive Eq.sig)}
    (hEq : (E.get ηeq).block = Eq.block) {l : Level ℓ} {α e₁ e₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ α : .sort l →
    E[Γ] ⊢ₛ e₁ : α →
    E[Γ] ⊢ₛ e₂ : α →
    E[Γ] ⊢ₛ Quot.eqApp ηeq l α e₁ e₂ : .prop := by
  intro hα h₁ h₂
  have h := DefeqStrong.indDF (E := E) (Γ := Γ) (η := ηeq) (s := ⟨0, by decide⟩)
    (ls := fun _ => l) (ps₁ := fun i => if i.val = 0 then α else e₁)
    (ps₂ := fun i => if i.val = 0 then α else e₁) (is₁ := fun _ => e₂) (is₂ := fun _ => e₂)
    (fun
      | ⟨0, _⟩ => by simpa! [hEq, Inductive.paramType] using hα
      | ⟨1, _⟩ => by simpa! [hEq, Inductive.paramType] using h₁)
    (fun
      | ⟨0, _⟩ => by simpa! [hEq, Inductive.indexType, Ctx.proj] using h₂)
  rw [hEq] at h
  simpa [Quot.eqApp] using h

theorem Quot.compatType_isTypeStrong {ηeq : Head ζ (.inductive Eq.sig)}
    (hEq : (E.get ηeq).block = Eq.block) {u l : Level ℓ} {α r β f : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ α : .sort u →
    E[Γ] ⊢ₛ r : Quot.relType α →
    E[Γ] ⊢ₛ β : .sort l →
    E[Γ] ⊢ₛ f : .forallE α β.wk →
    E[Γ] ⊢ₛ Quot.compatType ηeq l α r β f typ := by
  intro hα hr hβ hf
  have hα₁ : E[Γ.snoc α] ⊢ₛ α.wk : .sort u := hα.wk α
  have hα₂ : E[(Γ.snoc α).snoc α.wk] ⊢ₛ α.wk.wk : .sort u := hα₁.wk α.wk
  have ha₁ : E[Γ.snoc α] ⊢ₛ .var (Fin.last n) : α.wk := by
    have := DefeqStrong.var (Γ := Γ.snoc α) (v := Fin.last n) (by rw [Ctx.get_last]; exact hα₁)
    rwa [Ctx.get_last] at this
  have ha₂ : E[(Γ.snoc α).snoc α.wk] ⊢ₛ .var ⟨n, by omega⟩ : α.wk.wk := by
    have h := ha₁.wk α.wk
    have hv : (Expr.var (Fin.last n) : Expr ζ ℓ (n + 1)).wk = .var ⟨n, by omega⟩ := by
      simp [Expr.wk, Expr.wkFrom, Expr.rename]
      exact Fin.ext rfl
    rwa [hv] at h
  have hb₂ : E[(Γ.snoc α).snoc α.wk] ⊢ₛ .var ⟨n + 1, by omega⟩ : α.wk.wk := by
    have := DefeqStrong.var (Γ := (Γ.snoc α).snoc α.wk) (v := Fin.last (n + 1))
      (by rw [Ctx.get_last]; exact hα₂)
    rwa [Ctx.get_last] at this
  have hr₂ : E[(Γ.snoc α).snoc α.wk] ⊢ₛ r.wk.wk : Quot.relType α.wk.wk := by
    simpa [Expr.wk] using (hr.wk α).wk α.wk
  have hcod : E[((Γ.snoc α).snoc α.wk).snoc α.wk.wk] ⊢ₛ
      Expr.forallE α.wk.wk.wk .prop : .sort (.imax u .one) :=
    .forallEDF (hα₂.wk _) .sortDF .sortDF
  have h₁ := DefeqStrong.appDF hα₂ hcod hr₂ ha₂ (hcod.inst_congr ha₂)
  have h₁' : E[(Γ.snoc α).snoc α.wk] ⊢ₛ r.wk.wk.app (.var ⟨n, by omega⟩) :
      .forallE α.wk.wk .prop := by
    have hty : (Expr.forallE α.wk.wk.wk .prop).inst (.var ⟨n, by omega⟩) =
        Expr.forallE α.wk.wk (.prop : Expr ζ ℓ (n + 2 + 1)) := by
      rw [Expr.inst, Expr.subst, ← Expr.inst, Expr.inst_wk]
      rfl
    rwa [hty] at h₁
  have hP : E[(Γ.snoc α).snoc α.wk] ⊢ₛ
      (r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩) : .prop :=
    .appDF (t' := .prop) hα₂ .sortDF h₁' hb₂ .sortDF
  have hβ₃ := ((hβ.wk α).wk α.wk).wk
    ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))
  have hf₃ := ((hf.wk α).wk α.wk).wk
    ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))
  have hf₃' : E[((Γ.snoc α).snoc α.wk).snoc
      ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))] ⊢ₛ
      f.wk.wk.wk : .forallE α.wk.wk.wk β.wk.wk.wk.wk := by
    simpa [Expr.wk] using hf₃
  have hα₃ := hα₂.wk ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))
  have ha₃ : E[((Γ.snoc α).snoc α.wk).snoc
      ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))] ⊢ₛ
      .var ⟨n, by omega⟩ : α.wk.wk.wk := by
    have h := ha₂.wk ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))
    have hv : (Expr.var ⟨n, by omega⟩ : Expr ζ ℓ (n + 2)).wk = .var ⟨n, by omega⟩ := by
      simp [Expr.wk, Expr.wkFrom, Expr.rename]
    rwa [hv] at h
  have hb₃ : E[((Γ.snoc α).snoc α.wk).snoc
      ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))] ⊢ₛ
      .var ⟨n + 1, by omega⟩ : α.wk.wk.wk := by
    have h := hb₂.wk ((r.wk.wk.app (.var ⟨n, by omega⟩)).app (.var ⟨n + 1, by omega⟩))
    have hv : (Expr.var ⟨n + 1, by omega⟩ : Expr ζ ℓ (n + 2)).wk = .var ⟨n + 1, by omega⟩ := by
      simp [Expr.wk, Expr.wkFrom, Expr.rename]
    rwa [hv] at h
  have hβ₄ := hβ₃.wk α.wk.wk.wk
  have hfa := DefeqStrong.appDF hα₃ hβ₄ hf₃' ha₃ (hβ₄.inst_congr ha₃)
  have hfb := DefeqStrong.appDF hα₃ hβ₄ hf₃' hb₃ (hβ₄.inst_congr hb₃)
  rw [Expr.inst_wk] at hfa hfb
  have heq := Quot.eqApp_typed hEq hβ₃ hfa hfb
  have h₃ := DefeqStrong.forallEDF hP heq heq
  have h₂ := DefeqStrong.forallEDF hα₁ h₃ h₃
  exact ⟨_, .forallEDF hα h₂ h₂⟩

end TypeFormers

end Metalean
