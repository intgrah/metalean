/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Sig
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

variable {ζ ζ₁ ζ₂ : Sigs} {sig : Sig}

theorem Head.position_lt (η : Head ζ sig) : η.position < ζ.length := by
  induction η with
  | here => exact Nat.lt_succ_self _
  | there η ih => exact Nat.lt_succ_of_lt ih

@[simp] theorem Head.position_map (pre : ζ ⟶ ζ₂) (η : Head ζ sig) :
    (η.map pre).position = η.position := by
  induction pre with
  | refl => rfl
  | step pre ih => exact ih

namespace Sigs

def lookup (p : Nat) : (ζ : Sigs) → Option (Σ sig : Sig, Head ζ sig)
  | .nil => none
  | .snoc ζ sig =>
    if p = ζ.length then some ⟨sig, .here⟩
    else (ζ.lookup p).map fun ⟨sig', η⟩ => ⟨sig', .there η⟩

@[simp] theorem lookup_position (η : Head ζ sig) :
    ζ.lookup η.position = some ⟨sig, η⟩ := by
  induction η with
  | here => simp [lookup, Head.position]
  | there η ih => simp [lookup, Head.position, Nat.ne_of_lt η.position_lt, ih]

theorem position_of_lookup {p : Nat} {x : Σ sig, Head ζ sig} (h : ζ.lookup p = some x) :
    x.2.position = p := by
  induction ζ with
  | nil => simp [lookup] at h
  | snoc ζ sig₁ ih =>
    unfold lookup at h
    split at h
    · cases h
      simp [Head.position, *]
    · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ih hy

theorem lookup_head_eq {p : Nat} {η₁ η₂ : Head ζ sig} (h₁ : ζ.lookup p = some ⟨sig, η₁⟩)
    (h₂ : ζ.lookup p = some ⟨sig, η₂⟩) :
    η₁ = η₂ := by
  rw [h₁] at h₂
  injection h₂ with hmk
  injection hmk

@[transport] theorem lookup_map (pre : ζ₁ ⟶ ζ₂) {p : Nat} {η : Head ζ₁ sig}
    (h : ζ₁.lookup p = some ⟨sig, η⟩) :
    ζ₂.lookup p = some ⟨sig, η.map pre⟩ := by
  rw [← position_of_lookup h, ← Head.position_map pre η]
  exact lookup_position _

end Sigs

end Metalean
