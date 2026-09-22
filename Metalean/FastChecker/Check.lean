/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.CheckInductive
public import Metalean.FastChecker.Translate
public import Metalean.Syntax.Eq

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

namespace FEq

variable {L : Literals} {E : Σ ζ, Env ζ}

def fctor : FCtor where
  ordinary := #[]
  recursive := #[]
  targetIndices := #[.fvar 1]

def raw : FInductive where
  params := #[.sort (.param 0), .fvar 0]
  indices := #[#[.fvar 0]]
  level := .zero
  ctors := #[#[fctor]]

theorem denotes_ctor : FCtor.Denotes L E fctor (Eq.ctorDecl (ζ := E.1)) where
  ordinarySize := rfl
  ordinary f := f.elim0
  recursiveSize := rfl
  recursive f := f.elim0
  targetSize := rfl
  targetIndices := fun ⟨0, _⟩ => .fvar (by decide)

theorem denotes : FInductive.Denotes L E raw (Eq.block (ζ := E.1)) where
  params :=
    (FCtx.Denotes.nil.snoc (.sort (.param (by decide)))).snoc (.fvar (by decide))
  indicesSize := rfl
  indices := fun ⟨0, _⟩ => .snoc .nil (.fvar (by decide))
  level := ⟨.zero, .zero, rfl⟩
  ctorsSize := rfl
  ctorsRow := fun ⟨0, _⟩ => rfl
  ctors := fun ⟨0, _⟩ ⟨0, _⟩ => denotes_ctor

theorem noProj_ctor : fctor.NoProj where
  ordinary := by simp [fctor]
  recursive := by simp [fctor]
  targetIndices := by
    intro i hi
    obtain rfl : i = .fvar 1 := by simpa [fctor] using hi
    exact .fvar 1

theorem noProj : raw.NoProj where
  params := by
    intro t ht
    rcases (by simpa [raw] using ht : t = .sort (.param 0) ∨ t = .fvar 0) with rfl | rfl
    · exact .sort _
    · exact .fvar 0
  indices := by
    intro ts hts t ht
    obtain rfl : ts = #[.fvar 0] := by simpa [raw] using hts
    obtain rfl : t = .fvar 0 := by simpa using ht
    exact .fvar 0
  ctors := by
    intro cs hcs c hc
    obtain rfl : cs = #[fctor] := by simpa [raw] using hcs
    obtain rfl : c = fctor := by simpa using hc
    exact noProj_ctor

end FEq

variable (L : Literals) (F : FEnv) (hints : Array Export.Hints) (accel : Accel L F)

def EntryWFSpec (fe : FEntry) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃entry₀ : Entry ζ fe.sig⦄,
  FEnv.Denotes L F E →
  EnvWF E →
  L.NatTrust E →
  FEntry.Denotes L ⟨ζ, E⟩ fe entry₀ →
  ∃ entry : Entry ζ fe.sig, FEntry.Denotes L ⟨ζ, E⟩ fe entry ∧ Metalean.EntryWF E entry

def checkAxiom (nlevels : Nat) (ft : FExpr) :
    CheckM L F nlevels (PLift (EntryWFSpec L F (.axiom nlevels ft))) := do
  let ⟨ht⟩ ← inferSorted L F nlevels hints accel #[] ft
  pure ⟨fun {_ _ _} hF hE htr (.axiom ht') =>
    have hS := Sem.nil (ℓ := nlevels) hF hE htr
    have ⟨_, l, ht'', hty⟩ := ht hS ht'
    ⟨_, .axiom ht'', .axiom ⟨l, hty⟩⟩⟩

def checkDef (nlevels : Nat) (ft v : FExpr) :
    CheckM L F nlevels (PLift (EntryWFSpec L F (.def nlevels ft v))) := do
  let _ ← inferSorted L F nlevels hints accel #[] ft
  let ⟨hv⟩ ← checkTyped L F nlevels hints accel #[] v ft
  pure ⟨fun {_ _ _} hF hE htr (.def ht' hv') =>
    have hS := Sem.nil (ℓ := nlevels) hF hE htr
    have ⟨_, _, hv'', ht'', hty⟩ := hv hS hv' ht'
    have ⟨l, hsort⟩ := hty.regular
    ⟨_, .def ht'' hv'', .def ⟨l, hsort⟩ hty⟩⟩
def checkTheorem (nlevels : Nat) (ft v : FExpr) :
    CheckM L F nlevels (PLift (EntryWFSpec L F (.def nlevels ft v))) := do
  let some _ ← isProp L F nlevels hints accel #[] ft | throw (.reject .nonPropTheorem)
  checkDef L F hints accel nlevels ft v

def checkOpaque (nlevels : Nat) (ft v : FExpr) :
    CheckM L F nlevels (PLift (EntryWFSpec L F (.opaque nlevels ft))) := do
  let _ ← inferSorted L F nlevels hints accel #[] ft
  let ⟨hvex⟩ ← FExpr.wf L F nlevels 0 0 v
  let ⟨hv⟩ ← checkTyped L F nlevels hints accel #[] v ft
  pure ⟨fun {_ _ _} hF hE htr (.opaque ht') =>
    have hS := Sem.nil (ℓ := nlevels) hF hE htr
    have ⟨_, hv'⟩ := hvex hF
    have ⟨_, _, _, ht'', hty⟩ := hv hS hv' ht'
    have ⟨l, hsort⟩ := hty.regular
    ⟨_, .opaque ht'', .opaque hty ⟨l, hsort⟩⟩⟩

def checkQuot (eqPos : Nat) :
    Except Failure (PLift (EntryWF L F (.quot eqPos)) × PLift (EntryWFSpec L F (.quot eqPos))) :=
  match hfe : F[eqPos]? with
  | some (.inductive ι I) => do
    let ⟨hι⟩ ← guardProofOr (ι = Eq.sig) (Failure.reject .eqShape)
    let ⟨hI⟩ ← guardProofOr (I = FEq.raw) (Failure.reject .eqShape)
    let hex : EntryWF L F (.quot eqPos) := fun {_} hF => by
      obtain rfl : ι = Eq.sig := hι
      have ⟨η, hη, _⟩ := hF.get hfe
      exact ⟨.quot η, .quot hη⟩
    pure ⟨⟨hex⟩, ⟨fun {ζ E _} hF _ _ hd => by
      obtain rfl : ι = Eq.sig := hι
      obtain rfl : I = FEq.raw := hI
      have .quot (η := η) hη := hd
      have ⟨η', hη', hden⟩ := hF.get hfe
      have hη'' : ζ.lookup eqPos = some ⟨Sig.inductive Eq.sig, η'⟩ := hη'
      obtain rfl : η' = η := Sigs.lookup_head_eq hη'' hη
      have ⟨I', hI', hentry'⟩ := hden.inductive_inv
      have hentry'' : E.get (sig := Sig.inductive Eq.sig) η' = Entry.inductive I' := hentry'
      refine ⟨_, .quot hη, .quot ?_⟩
      rw [hentry'']
      exact hI'.unique FEq.denotes FEq.noProj⟩⟩
  | _ => throw (Failure.reject .eqShape)

def checkInductiveEntry (ι : IndSig) (I : FInductive) :
    CheckM L F ι.nlevels (PLift (EntryWFSpec L F (.inductive ι I))) := do
  let ⟨h⟩ ← checkInductive L F hints accel ι I
  pure ⟨fun {_ E _} hF hE htr hd => by
    obtain ⟨I', hI', rfl⟩ := hd.inductive_inv
    have ⟨_, hI, hwf⟩ := h hF hE htr hI'
    exact ⟨_, .inductive hI, .inductive hwf⟩⟩

def inferOrdLevels (ι : IndSig) (pre : FPreInductive) :
    CheckM L F ι.nlevels ((s : Fin pre.ctors.size) → (c : Fin pre.ctors[s].size) →
      Fin pre.ctors[s][c].ordinary.size → FLevel) :=
  Fin.mapM fun s => Fin.mapM fun c => Fin.mapM fun f => do
    let r ← inferSortedLevel L F ι.nlevels hints accel
      (pre.params ++ pre.ctors[s][c].ordinary.extract 0 f.val) pre.ctors[s][c].ordinary[f]
    pure r.1

end Metalean.FastChecker
