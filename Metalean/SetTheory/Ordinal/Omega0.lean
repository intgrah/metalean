/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

public section

universe u

namespace Ordinal

noncomputable def natOrderIsoIioOmega0 : Nat ≃o {o : Ordinal.{u} // o < ω} :=
  StrictMono.orderIsoOfSurjective
    (fun n => ⟨n, natCast_lt_omega0 n⟩)
    (fun _ _ h => by simpa using h)
    fun ⟨o, ho⟩ => have ⟨n, hn⟩ := lt_omega0.mp ho; ⟨n, Subtype.ext hn.symm⟩

end Ordinal
