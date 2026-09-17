module

public import Mathlib.Data.Quot

@[expose] public section

namespace Quotient

variable {α : Sort*} {β : Sort*} {s : Setoid α}

def liftFibre (q : Quotient s) (f : (a : α) → ⟦a⟧ = q → β)
    (hf : ∀ a b (ha : ⟦a⟧ = q) (hb : ⟦b⟧ = q), f a ha = f b hb) : β :=
  Quotient.hrecOn q (motive := fun r => r = q → β) (fun a ha => f a ha)
    (fun a b hab => Function.hfunext (congrArg (· = q) (Quotient.sound hab))
      fun ha hb _ => heq_of_eq (hf a b ha hb)) rfl

theorem liftFibre_eq (q : Quotient s) (f : (a : α) → ⟦a⟧ = q → β)
    (hf : ∀ a b (ha : ⟦a⟧ = q) (hb : ⟦b⟧ = q), f a ha = f b hb) (a : α) (ha : ⟦a⟧ = q) :
    liftFibre q f hf = f a ha := by
  subst ha
  rfl

end Quotient
