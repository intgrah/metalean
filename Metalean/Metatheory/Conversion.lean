/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Context
public import Metalean.Typing.Env
import Metalean.Metatheory.Unique

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem IsTypeEq.forallE_dom_congr (ho : E.Ordered)
    {t₁ t₂ : Expr ζ ℓ n} {t' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ.snoc t₁] ⊢ₛ t' typ →
    E[Γ] ⊢ₛ .forallE t₁ t' ≡ .forallE t₂ t' typ :=
  fun hΓ hd hc =>
    have ⟨_, hdl⟩ := hd.sort_uniq ho hΓ
    have ⟨_, hcl₁⟩ := hc
    have hcl₂ := DefeqStrong.snocConvTy hd hcl₁
    .ofDefEq (.forallEDF hdl hcl₁ hcl₂)

theorem IsTypeEq.forallE_congr' (ho : E.Ordered)
    {t₁ t₂ : Expr ζ ℓ n} {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Γ] ⊢ₛ ok →
    E[Γ] ⊢ₛ t₁ ≡ t₂ typ →
    E[Γ.snoc t₁] ⊢ₛ t₁' ≡ t₂' typ →
    E[Γ] ⊢ₛ .forallE t₁ t₁' ≡ .forallE t₂ t₂' typ :=
  fun hΓ hd hc =>
    have ⟨_, hdl⟩ := hd.sort_uniq ho hΓ
    (IsTypeEq.forallE_congr hdl.left hc).trans
      (IsTypeEq.forallE_dom_congr ho hΓ hd hc.isType.2)

end Metalean
