/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

@[expose] public section

universe u v

/--
If the proposition `p` is true, does nothing, returning a proof of `p`, else fails (using `failure`).
-/
@[always_inline, inline] def guardProof {f : Type → Type u} [Alternative f]
    (p : Prop) [Decidable p] : f (PLift p) :=
  if h : p then pure ⟨h⟩ else failure

@[always_inline, inline] def guardProofOr {ε : Type u} {m : Type → Type v} [Monad m]
    [MonadExcept ε m] (p : Prop) [Decidable p] (e : ε) : m (PLift p) :=
  if h : p then pure ⟨h⟩ else throw e

namespace Array

def forallM {m : Type → Type v} [Monad m] {α : Type} (xs : Array α)
    (P : (i : Nat) → i < xs.size → Prop)
    (check : (i : Nat) → (h : i < xs.size) → m (PLift (P i h))) :
    m (PLift (∀ i (h : i < xs.size), P i h)) :=
  go 0 ⟨fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩
where
  go (j : Nat) (acc : PLift (∀ i (h : i < xs.size), i < j → P i h)) :
      m (PLift (∀ i (h : i < xs.size), P i h)) :=
    if hj : j < xs.size then do
      let ⟨h⟩ ← check j hj
      go (j + 1) ⟨fun i hi hij => by
        by_cases hij' : i < j
        · exact acc.down i hi hij'
        · obtain rfl : i = j := by omega
          exact h⟩
    else pure ⟨fun i hi => acc.down i hi (by omega)⟩

end Array

namespace Fin

def mapM {m : Type u → Type v} [Applicative m] {k : Nat} {α : Fin k → Type u}
    (f : (i : Fin k) → m (α i)) : m ((i : Fin k) → α i) :=
  match k with
  | 0 => pure fun i => i.elim0
  | _ + 1 =>
    (fun a r i => match i with
      | ⟨0, _⟩ => a
      | ⟨j + 1, h⟩ => r ⟨j, Nat.lt_of_succ_lt_succ h⟩) <$> f 0 <*> mapM fun i => f i.succ

def sequenceM {m : Type → Type v} [Monad m] {k : Nat} {P : Fin k → Prop}
    (f : (i : Fin k) → m (PLift (P i))) : m (PLift (∀ i, P i)) :=
  go 0 (Nat.zero_le k) fun _ h => absurd h (Nat.not_lt_zero _)
where
  go (j : Nat) (hj : j ≤ k) (acc : ∀ i : Fin k, i.val < j → P i) :
      m (PLift (∀ i, P i)) :=
    if hlt : j < k then do
      let ⟨h⟩ ← f ⟨j, hlt⟩
      go (j + 1) hlt fun i hij =>
        if hi : i.val = j then (Fin.ext hi : i = ⟨j, hlt⟩) ▸ h else acc i (by omega)
    else pure ⟨fun i => acc i (by omega)⟩

end Fin
