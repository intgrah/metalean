/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Defeq

@[expose] public section

namespace Metalean

variable {ζ : Sigs}

def CtxWF (E : Env ζ) {ℓ : Nat} {n : Nat} (Γ : Ctx ζ ℓ 0 n) : Prop :=
  Γ.Forall fun Γ₁ t => E[Γ₁] ⊢ t typ

notation:65 E "[" Γ "]" " ⊢ " "ok" => CtxWF E Γ

@[app_unexpander CtxWF]
meta def CtxWF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $_ℓ $Γ) => `($E[$Γ] ⊢ ok)
  | _ => throw ()

end Metalean
