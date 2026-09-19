/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Choice
public import Metalean.SetSemantics.Consistency.Builtin.Eq
public import Metalean.SetSemantics.Consistency.Builtin.Iff
public import Metalean.SetSemantics.Consistency.Builtin.Nonempty
public import Metalean.SetSemantics.Environment.Quot
import Metalean.Typing.Builtin.Eq
import Metalean.Typing.Builtin.Iff
import Metalean.Typing.Builtin.Nonempty
import Mathlib.Tactic.FinCases

public section

universe u

namespace Metalean

open ZFSet

private theorem lam_mem_pi {a : ZFSet.{u}} {fn op : ZFSet.{u} → ZFSet.{u}}
    (hb : ∀ x ∈ a, fn x ∈ op x) :
    Aczel.lam a fn ∈ Aczel.pi a op :=
  Aczel.lam_mem_piMap fun x hx => (app_map hx).symm ▸ hb x hx

namespace Choice

noncomputable def value (ε : Atom Propext.sigs 0 → ZFSet.{u}) (l : Level 0) : ZFSet.{u} :=
  [zf|fun (α : $(S_ (l.eval zeroNs))) (_h : $(ε (.ind Choice.nonemptyHead 0 (fun _ => l) ![α] ![]))) =>
    $(Classical.epsilon (· ∈ α))]

theorem value_mem {ε : Atom Propext.sigs 0 → ZFSet.{u}}
    (h : Nonempty.Sem ε Choice.nonemptyHead) (ls : Fin 1 → Level 0) :
    value ε (ls 0) ∈ ε[![]]⟦Choice.type.instL ls⟧ := by
  have htype : ε[![]]⟦Choice.type.instL ls⟧ =
      [zf|(α : $(S_ ((ls 0).eval zeroNs))) →
        $(ε (.ind Choice.nonemptyHead 0 (fun _ => ls 0) ![α] ![])) → α] := by
    simp only [Choice.type, Expr.instL, Expr.denote]
    refine Aczel.pi_congr fun α hα => ?_
    congr 1
    congr 2 <;> funext i <;> fin_cases i
    rfl
  rw [htype]
  exact lam_mem_pi fun α hα => lam_mem_pi fun witness hwitness =>
    Classical.epsilon_spec (h.exists_mem hα hwitness)

theorem valid (m : Env.Model.{u} Propext.env) (ls : Fin 1 → Level 0) :
    ∃ v, v ∈ m.atoms[![]]⟦Choice.type.instL ls⟧ :=
  ⟨value m.atoms (ls 0),
    value_mem (.of_model m (by
      simp! [Choice.nonemptyHead, Propext.env, Quot.Sound.env, Nonempty.env,
        Env.get, Entry.weakenEnv, Entry.block])) ls⟩

end Choice

namespace Quot.Sound

noncomputable def value (l : Level 0) : ZFSet.{u} :=
  [zf|fun (α : $(S_ (l.eval zeroNs))) (r : $(quotientRel α)) (a₁ a₂ : α) (_h : r a₁ a₂) => proof]

theorem value_mem {ε : Atom Nonempty.sigs 0 → ZFSet.{u}}
    (hquot : Quot.RulesSound Nonempty.env ε Quot.Sound.quotHead)
    (heq : Eq.Sem ε Quot.Sound.eqHead) (ls : Fin 1 → Level 0) :
    value (ls 0) ∈ ε[![]]⟦Quot.Sound.type.instL ls⟧ := by
  have htype : ε[![]]⟦Quot.Sound.type.instL ls⟧ =
      [zf|(α : $(S_ ((ls 0).eval zeroNs))) → (r : $(quotientRel α)) →
        (a₁ a₂ : α) → r a₁ a₂ →
        $(ε <| .ind Quot.Sound.eqHead 0 (fun _ => ls 0)
          ![quotientCarrier ((ls 0).eval zeroNs) α r, quotientMk ((ls 0).eval zeroNs) α r a₁]
          ![quotientMk ((ls 0).eval zeroNs) α r a₂])] := by
    simp only [Quot.Sound.type, Quot.eqApp, Expr.instL, Expr.denote]
    refine Aczel.pi_congr fun α hα => Aczel.pi_congr fun r hr => Aczel.pi_congr fun a₁ ha₁ =>
      Aczel.pi_congr fun a₂ ha₂ => Aczel.pi_congr fun witness hwitness => ?_
    congr 2 <;> funext i <;> fin_cases i <;>
      simp [Expr.denote, Atom.instL, hquot.quotAtom, hquot.quotMkAtom]
  rw [htype]
  refine lam_mem_pi fun α hα => lam_mem_pi fun r hr => lam_mem_pi fun a ha =>
    lam_mem_pi fun b hb => lam_mem_pi fun witness hwitness => ?_
  have hra := Aczel.app_mem hr ha
  rw [app_map ha] at hra
  have hrab := Aczel.app_mem hra hb
  rw [app_map hb] at hrab
  rw [quotientMk_eq_of_rel hα ha hb (eq_verum_of_mem hrab hwitness)]
  exact heq.refl (quotientCarrier_mem_sort hα) (quotientMk_mem hb)

theorem valid (m : Env.Model.{u} Nonempty.env) (ls : Fin 1 → Level 0) :
    ∃ v, v ∈ m.atoms[![]]⟦Quot.Sound.type.instL ls⟧ :=
  ⟨value (ls 0),
    value_mem (m.sound.quotientRules Quot.Sound.quotHead)
      (.of_model m (by
        simp [Nonempty.env, Iff.env, Quot.env, Eq.env, Env.get, Entry.weakenEnv, Entry.map,
          Entry.block])) ls⟩

end Quot.Sound

namespace Propext

noncomputable def value (ε : Atom Quot.Sound.sigs 0 → ZFSet.{u}) : ZFSet.{u} :=
  [zf|fun (a₁ a₂ : $(S_ 0)) (_h : $(ε <| .ind Propext.iffHead 0 ![] ![a₁, a₂] ![])) => proof]

theorem value_mem {ε : Atom Quot.Sound.sigs 0 → ZFSet.{u}}
    (hiff : Iff.Sem ε Propext.iffHead)
    (heq : Eq.Sem ε Propext.eqHead) (ls : Fin 0 → Level 0) :
    value ε ∈ ε[![]]⟦Propext.type.instL ls⟧ := by
  have htype : ε[![]]⟦Propext.type.instL ls⟧ =
      [zf|(a₁ a₂ : $(S_ 0)) → $(ε <| .ind Propext.iffHead 0 ![] ![a₁, a₂] ![]) →
        $(ε <| .ind Propext.eqHead 0 (fun _ => .succ .zero) ![S_ 0, a₁] ![a₂])] := by
    simp! [Propext.type]
    refine Aczel.pi_congr fun a₁ ha₁ => ?_
    refine Aczel.pi_congr fun a₂ ha₂ => ?_
    congr 1
    · congr 2 <;> funext i <;> fin_cases i <;> rfl
    · funext witness
      congr 2 <;> funext i <;> fin_cases i <;> rfl
  rw [htype]
  refine lam_mem_pi fun a ha => lam_mem_pi fun b hb => lam_mem_pi fun witness hwitness => ?_
  obtain rfl := hiff.sound ha hb hwitness
  exact heq.refl (by simpa using sort_mem_succ 0) ha

theorem valid (m : Env.Model.{u} Quot.Sound.env) (ls : Fin 0 → Level 0) :
    ∃ v, v ∈ m.atoms[![]]⟦Propext.type.instL ls⟧ :=
  ⟨value m.atoms,
    value_mem
      (.of_model m (by
        simp [Quot.Sound.env, Nonempty.env, Iff.env, Env.get, Entry.weakenEnv, Entry.map,
          Entry.block]))
      (.of_model m (by
        simp [Quot.Sound.env, Nonempty.env, Iff.env, Quot.env, Eq.env,
          Env.get, Entry.weakenEnv, Entry.map, Entry.block])) ls⟩

end Propext

end Metalean
