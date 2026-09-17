/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Heyting.Basic

@[expose] public section

universe u

class CondSemilatticeSup (α : Type*) extends Preorder α, OrderBot α where
  cSup (a b : α) (h : ∃ c, a ≤ c ∧ b ≤ c) : α
  le_cSup_left (a b : α) (h : ∃ c, a ≤ c ∧ b ≤ c) : a ≤ cSup a b h
  le_cSup_right (a b : α) (h : ∃ c, a ≤ c ∧ b ≤ c) : b ≤ cSup a b h
  cSup_le {a b c : α} (h : ∃ d, a ≤ d ∧ b ≤ d) : a ≤ c → b ≤ c → cSup a b h ≤ c

export CondSemilatticeSup (cSup le_cSup_left le_cSup_right cSup_le)

instance {α β : Type*} [CondSemilatticeSup α] [CondSemilatticeSup β] :
    CondSemilatticeSup (α × β) where
  cSup := fun (a₁, a₂) (b₁, b₂) h =>
    (cSup a₁ b₁ (h.elim fun (c₁, _) ⟨⟨ha, _⟩, ⟨hb, _⟩⟩ => ⟨c₁, ha, hb⟩),
      cSup a₂ b₂ (h.elim fun (_, c₂) ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ => ⟨c₂, ha, hb⟩))
  le_cSup_left _ _ _ := ⟨le_cSup_left _ _ _, le_cSup_left _ _ _⟩
  le_cSup_right _ _ _ := ⟨le_cSup_right _ _ _, le_cSup_right _ _ _⟩
  cSup_le _ := fun ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩ => ⟨cSup_le _ ha₁ hb₁, cSup_le _ ha₂ hb₂⟩

instance : CondSemilatticeSup PUnit.{u + 1} where
  cSup _ _ _ := PUnit.unit
  le_cSup_left _ _ _ := le_rfl
  le_cSup_right _ _ _ := le_rfl
  cSup_le _ _ _ := le_rfl
