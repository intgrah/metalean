/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Consistency.Axioms
public import Metalean.SetSemantics.Consistency.Extension

/-!
# Consistency

Here we prove that the standard axioms in Lean have a model in set theory
-/

public section

universe u

namespace Metalean

open ClassicalEnv in
noncomputable def Env.Model.classical : Model.{u} ClassicalEnv.E :=
  let pre : Env.nil.as ⟶ env₄.as := .step (.step (.step (.step .refl)))
  have hfree : pre.Forall fun entry => ¬ IsAxiom entry := by
    (repeat constructor) <;> nofun
  let m₄ := Model.nil.extend pre hfree wf₄
  let m₅ := m₄.addAxiom (quotSound_valid m₄ (by simp! [Env.get, Entry.block]))
  let m₆ := m₅.addAxiom (propext_valid m₅
    (by simp! [Env.get, Entry.block])
    (by simp! [Env.get, Entry.block]))
  let m₇ := m₆.addAxiom (classicalChoice_valid m₆ (by
    simp [Env.get, Entry.map, Entry.block]))
  m₇

def Con : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ (pre : ClassicalEnv.E.as ⟶ E.as),
    (pre.Forall fun entry => ¬ IsAxiom entry) → EnvWF E → E.Con

theorem consistency : Con := by
  intro ζ E pre hax hE
  have m := Env.Model.classical.{0}.extend pre hax hE
  exact con_wf zeroNs m.semDecls m.semDeclRules hE

end Metalean
