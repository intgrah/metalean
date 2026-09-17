/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
public import Metalean.Level.Decide

@[expose] public section

namespace Metalean

instance instDecidableForallParam {ℓ : Nat} (p : Param ℓ → Prop) [DecidablePred p] :
    Decidable (∀ x, p x) := inferInstanceAs (Decidable (∀ x : Fin ℓ, p x))

namespace Ctor

variable {ζ : Sigs} {ι : IndSig} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}

instance instDecidableEligible (ctor : Ctor ζ ι s csig)
    (l : Level ι.nlevels) : Decidable (ctor.Eligible l) :=
  decidable_of_iff
    ((∀ f, (ctor.ordinary f).level = .zero ∨
      ∃ i, (ctor.targetIndices i).isVar = some (ι.nparams + f.val)) ∧
    ∀ _ : Fin csig.nrecFields, l = .zero)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.ordinary, h.recursive⟩⟩

end Ctor

namespace Inductive

variable {ζ : Sigs} {ι : IndSig} (I : Inductive ζ ι)

instance LevelOK.instDecidable (l : Level ι.nlevels) : Decidable (I.LevelOK l) := by
  unfold Inductive.LevelOK
  infer_instance

instance SortLargeElim.instDecidablePred : DecidablePred I.SortLargeElim := fun s =>
  decidable_of_iff
    (Level.one ≤ I.level ∨
      ι.nsorts = 1 ∧ (∀ c c' : Fin (ι.nctors s), c = c') ∧
        ∀ c, (I.ctors s c).Eligible I.level)
    ⟨fun h => h.elim .large fun h => .subsingleton h.1 h.2.1 h.2.2, fun h => by
      cases h with
      | large hlevel => exact .inl hlevel
      | subsingleton hsorts hunique heligible => exact .inr ⟨hsorts, hunique, heligible⟩⟩

instance LargeElim.instDecidable : Decidable I.LargeElim := by
  unfold LargeElim
  infer_instance

instance IsStructure.instDecidable (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Decidable (I.IsStructure s c) :=
  decidable_of_iff
    ((∀ other : Fin ι.nsorts, other = s) ∧ (∀ other : Fin (ι.nctors s), other = c) ∧
      (∀ _ : Fin (ι.nindices s), False) ∧ (∀ _ : Fin (ι.ctors s c).nrecFields, False) ∧
      I.SortLargeElim s)
    ⟨fun ⟨hs, hc, hi, hf, hl⟩ => ⟨hs, hc, ⟨hi⟩, ⟨hf⟩, hl⟩,
      fun h => ⟨h.sort_unique, h.ctor_unique, h.no_indices.elim, h.no_recursive.elim,
        h.sortLargeElim⟩⟩

instance RecAllowed.instDecidable {ℓ : Nat} (l : Level ℓ) : Decidable (I.RecAllowed l) := by
  unfold Inductive.RecAllowed
  infer_instance

end Inductive

end Metalean
