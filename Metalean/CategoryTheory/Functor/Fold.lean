module

public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

@[expose] public section

namespace CategoryTheory.NatTrans

open MonoidalCategory

variable {C : Type*} [Category* C] {F : C ⥤ Type}

@[reducible] def finFold (α : F ⊗ F ⟶ F) (k : Nat) :
    F ⊗ (F ⋙ ofTypeFunctor (ReaderT (Fin k) Id)) ⟶ F where
  app X := ↾fun ⟨e, args⟩ => Fin.foldl k (fun e i => α.app X ⟨e, args i⟩) e
  naturality {X₁ X₂} σ := by
    ext ⟨e, args⟩
    exact (Fin.foldl_eq_finRange_foldl (fun e i => α.app X₂ ⟨e, F.map σ (args i)⟩) (F.map σ e)).trans
      ((List.foldl_hom (F.map σ) (fun e i => α.naturality_apply σ ⟨e, args i⟩)).trans
        (congrArg (F.map σ) (Fin.foldl_eq_finRange_foldl (fun e i => α.app X₁ ⟨e, args i⟩) e).symm))

@[reducible] def listFold (α : F ⊗ F ⟶ F) :
    F ⊗ (F ⋙ ofTypeFunctor List) ⟶ F where
  app X := ↾fun ⟨e, args⟩ => args.foldl (fun e a => α.app X ⟨e, a⟩) e
  naturality {X₁ X₂} σ := by
    ext ⟨e, args⟩
    exact List.foldl_map_hom (g := F.map σ) (fun e a => α.naturality_apply σ ⟨e, a⟩)

end CategoryTheory.NatTrans
