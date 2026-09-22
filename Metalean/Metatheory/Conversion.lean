/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Context
public import Metalean.Typing.Env.Defs
import Metalean.Metatheory.Unique

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem TypeEq.forallE_dom_congr (ho : E.Ordered)
    {t₁ t₂ : Expr ζ ℓ n} {t' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ.snoc t₁] ⊢ t' typ →
    E[Γ] ⊢ .forallE t₁ t' ≡ .forallE t₂ t' typ :=
  fun hΓ hd hc =>
    have ⟨_, hdl⟩ := hd.sort_uniq ho hΓ
    have ⟨_, hcl₁⟩ := hc
    have hcl₂ := Defeq.snocConvTy hd hcl₁
    .ofDefEq (.forallEDF hdl hcl₁ hcl₂)

theorem TypeEq.forallE_congr' (ho : E.Ordered)
    {t₁ t₂ : Expr ζ ℓ n} {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ ok →
    E[Γ] ⊢ t₁ ≡ t₂ typ →
    E[Γ.snoc t₁] ⊢ t₁' ≡ t₂' typ →
    E[Γ] ⊢ .forallE t₁ t₁' ≡ .forallE t₂ t₂' typ :=
  fun hΓ hd hc =>
    have ⟨_, hdl⟩ := hd.sort_uniq ho hΓ
    (TypeEq.forallE_congr hdl.left hc).trans
      (TypeEq.forallE_dom_congr ho hΓ hd hc.right)

end Metalean
