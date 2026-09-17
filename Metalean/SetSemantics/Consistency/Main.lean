/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Consistency.Axioms
public import Metalean.SetSemantics.Consistency.Extension
public import Metalean.Typing.Builtin.Env

/-!
# Consistency

Here we prove that the standard axioms in Lean have a model in set theory
-/

public section

universe u

namespace Metalean

noncomputable def Env.Model.classical : Model.{u} classicalEnv := by
  let pre : Env.nil.as ⟶ Nonempty.env.as := .step (.step (.step (.step .refl)))
  have hfree : pre.Forall fun entry => ¬ IsAxiom entry := by
    repeat constructor
    all_goals intro h; cases h
  let m := Model.nil.extend pre hfree
    (classicalEnv_ordered.ofPrefix (.step (.step (.step .refl))))
  let m := m.addAxiom (Quot.Sound.valid m)
  let m := m.addAxiom (Propext.valid m)
  exact m.addAxiom (Choice.valid m)

def Con : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ (pre : classicalEnv.as ⟶ E.as),
    (pre.Forall fun entry => ¬ IsAxiom entry) → E.Ordered → E.Con

theorem consistency : Con := by
  intro ζ E pre hax ho
  have m := Env.Model.classical.{0}.extend pre hax ho
  exact con_ordered m.atoms zeroNs m.semDecls m.semDeclRules ho

end Metalean
