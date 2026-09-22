/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Env
public import Metalean.SetSemantics.Consistency.Builtin.Eq
public import Metalean.SetSemantics.Consistency.Builtin.Iff
public import Metalean.SetSemantics.Consistency.Builtin.Nonempty
public import Metalean.SetSemantics.Environment.Quot
import Mathlib.Tactic.FinCases

public section

universe u

namespace Metalean.ClassicalEnv

open ZFSet

variable {ζ : Sigs} {E : Env ζ}

private theorem lam_mem_pi {a : ZFSet.{u}} {fn op : ZFSet.{u} → ZFSet.{u}}
    (hb : ∀ x ∈ a, fn x ∈ op x) :
    Aczel.lam a fn ∈ Aczel.pi a op :=
  Aczel.lam_mem_piMap fun x hx => (app_map hx).symm ▸ hb x hx

section

variable {η : Head ζ (.inductive Nonempty.sig)}

noncomputable def classicalChoiceValue (ε : Atom ζ 0 → ZFSet.{u})
    (η : Head ζ (.inductive Nonempty.sig)) (l : Level 0) : ZFSet.{u} :=
  [zf|fun (α : $(S_ (l.eval ![]))) (_h : $(ε (.ind η 0 (fun _ => l) ![α] ![]))) =>
    $(Classical.epsilon (· ∈ α))]

theorem classicalChoiceValue_mem {ε : Atom ζ 0 → ZFSet.{u}}
    (h : Nonempty.Sem ε η) (ls : Fin 1 → Level 0) :
    classicalChoiceValue ε η (ls 0) ∈ ε[![]]⟦(classicalChoiceType η).instL ls⟧ := by
  have htype : ε[![]]⟦(classicalChoiceType η).instL ls⟧ =
      [zf|(α : $(S_ ((ls 0).eval ![]))) →
        $(ε (.ind η 0 (fun _ => ls 0) ![α] ![])) → α] := by
    simp only [classicalChoiceType, Expr.instL, Expr.denote]
    refine Aczel.pi_congr fun α hα => ?_
    congr 1
    congr 2 <;> funext i <;> fin_cases i
    rfl
  rw [htype]
  exact lam_mem_pi fun α hα => lam_mem_pi fun witness hwitness =>
    Classical.epsilon_spec (h.exists_mem hα hwitness)

theorem classicalChoice_valid (m : Env.Model.{u} E) (hblock : (E.get η).block = Nonempty.block)
    (ls : Fin 1 → Level 0) :
    ∃ v, v ∈ m.atoms[![]]⟦(classicalChoiceType η).instL ls⟧ :=
  ⟨classicalChoiceValue m.atoms η (ls 0), classicalChoiceValue_mem (.of_model m hblock) ls⟩

end

section

variable {ηeq : Head ζ (.inductive Eq.sig)} {ηquot : Head ζ .quot}

noncomputable def quotSoundValue (l : Level 0) : ZFSet.{u} :=
  [zf|fun (α : $(S_ (l.eval ![]))) (r : $(quotientRel α)) (a₁ a₂ : α) (_h : r a₁ a₂) => proof]

theorem quotSoundValue_mem {ε : Atom ζ 0 → ZFSet.{u}}
    (hquot : Quot.RulesSound E ε ηquot)
    (heq : Eq.Sem ε ηeq) (ls : Fin 1 → Level 0) :
    quotSoundValue (ls 0) ∈ ε[![]]⟦(quotSoundType ηeq ηquot).instL ls⟧ := by
  have htype : ε[![]]⟦(quotSoundType ηeq ηquot).instL ls⟧ =
      [zf|(α : $(S_ ((ls 0).eval ![]))) → (r : $(quotientRel α)) →
        (a₁ a₂ : α) → r a₁ a₂ →
        $(ε <| .ind ηeq 0 (fun _ => ls 0)
          ![quotientCarrier ((ls 0).eval ![]) α r, quotientMk ((ls 0).eval ![]) α r a₁]
          ![quotientMk ((ls 0).eval ![]) α r a₂])] := by
    simp only [quotSoundType, Quot.eqApp, Expr.instL, Expr.denote]
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

theorem quotSound_valid (m : Env.Model.{u} E) (heq : (E.get ηeq).block = Eq.block)
    (ls : Fin 1 → Level 0) :
    ∃ v, v ∈ m.atoms[![]]⟦(quotSoundType ηeq ηquot).instL ls⟧ :=
  ⟨quotSoundValue (ls 0), quotSoundValue_mem (m.sound.quotientRules ηquot) (.of_model m heq) ls⟩

end

section

variable {ηeq : Head ζ (.inductive Eq.sig)} {ηiff : Head ζ (.inductive Iff.sig)}

noncomputable def propextValue (ε : Atom ζ 0 → ZFSet.{u}) (ηiff : Head ζ (.inductive Iff.sig)) : ZFSet.{u} :=
  [zf|fun (a₁ a₂ : $(S_ 0)) (_h : $(ε <| .ind ηiff 0 ![] ![a₁, a₂] ![])) => proof]

theorem propextValue_mem {ε : Atom ζ 0 → ZFSet.{u}}
    (hiff : Iff.Sem ε ηiff)
    (heq : Eq.Sem ε ηeq) (ls : Fin 0 → Level 0) :
    propextValue ε ηiff ∈ ε[![]]⟦(propextType ηeq ηiff).instL ls⟧ := by
  have htype : ε[![]]⟦(propextType ηeq ηiff).instL ls⟧ =
      [zf|(a₁ a₂ : $(S_ 0)) → $(ε <| .ind ηiff 0 ![] ![a₁, a₂] ![]) →
        $(ε <| .ind ηeq 0 (fun _ => .succ .zero) ![S_ 0, a₁] ![a₂])] := by
    simp! [propextType]
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

theorem propext_valid (m : Env.Model.{u} E) (hiff : (E.get ηiff).block = Iff.block)
    (heq : (E.get ηeq).block = Eq.block) (ls : Fin 0 → Level 0) :
    ∃ v, v ∈ m.atoms[![]]⟦(propextType ηeq ηiff).instL ls⟧ :=
  ⟨propextValue m.atoms ηiff, propextValue_mem (.of_model m hiff) (.of_model m heq) ls⟩

end

end Metalean.ClassicalEnv
