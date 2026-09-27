/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Spec

@[expose] public section

namespace Metalean.Checker.Fast

namespace FList

def nil : FCtor where
  ordinary := #[]
  recursive := #[]
  targetIndices := #[]

def cons : FCtor where
  ordinary := #[⟨.fvar 0, .succ (.param 0)⟩]
  recursive := #[⟨#[], #[]⟩]
  targetIndices := #[]

def raw : FInductive where
  params := #[.sort (.succ (.param 0))]
  indices := #[#[]]
  level := .succ (.param 0)
  ctors := #[#[nil, cons]]

variable {E : Σ ζ, Env ζ}

theorem denotes_nil : FCtor.Denotes E nil (List.nilDecl (ζ := E.1)) where
  ordinarySize := rfl
  ordinary f := f.elim0
  recursiveSize := rfl
  recursive f := f.elim0
  targetSize := rfl
  targetIndices f := f.elim0

theorem denotes_cons : FCtor.Denotes E cons (List.consDecl (ζ := E.1)) where
  ordinarySize := rfl
  ordinary := fun ⟨0, _⟩ => ⟨.fvar (by simp), ⟨_, .succ (.param (by decide)), rfl⟩⟩
  recursiveSize := rfl
  recursive := fun ⟨0, _⟩ => ⟨.nil, rfl, nofun⟩
  targetSize := rfl
  targetIndices f := f.elim0

theorem denotes : FInductive.Denotes E raw (List.block (ζ := E.1)) where
  params := FCtx.Denotes.nil.snoc (.sort (.succ (.param (by decide))))
  indicesSize := rfl
  indices := fun ⟨0, _⟩ => .nil
  level := ⟨_, .succ (.param (by decide)), rfl⟩
  ctorsSize := rfl
  ctorsRow := fun ⟨0, _⟩ => rfl
  ctors
    | ⟨0, _⟩, ⟨0, _⟩ => denotes_nil
    | ⟨0, _⟩, ⟨1, _⟩ => denotes_cons

theorem noProj : raw.NoProj where
  params := by simp [raw, FExpr.NoProj.sort]
  indices := by simp [raw]
  ctors := by
    intro cs hcs c hc
    obtain rfl : cs = #[nil, cons] := by simpa [raw] using hcs
    rcases (by simpa using hc : c = nil ∨ c = cons) with rfl | rfl
    · exact ⟨by simp [nil], by simp [nil], by simp [nil]⟩
    · exact ⟨by simp [cons, FExpr.NoProj.fvar], by simpa [cons] using (⟨by simp, by simp⟩ : FRecField.NoProj ⟨#[], #[]⟩),
      by simp [cons]⟩

end FList

def FExpr.listChar (P : StrPos) : FExpr :=
  .ind P.list 0 #[.zero] #[FExpr.char P.char] #[]

theorem FExpr.Denotes.listChar {ζ : Sigs} {E : Env ζ} {ℓ n k : Nat} {P : StrPos}
    {ηList : Head ζ (.inductive List.sig)} {ηChar : Head ζ (.inductive Char.sig)}
    (hList : ζ.lookup P.list = some ⟨.inductive List.sig, ηList⟩)
    (hChar : ζ.lookup P.char = some ⟨.inductive Char.sig, ηChar⟩) :
    FExpr.Denotes E.as k (FExpr.listChar P)
      (Expr.list ηList .zero (Expr.char ηChar) : Expr ζ ℓ n) := by
  have h : FExpr.Denotes E.as k (FExpr.listChar P)
      (.ind ηList 0 (⟦![RawLevel.zero] ·⟧) ![Expr.char ηChar] ![] : Expr ζ ℓ n) := by
    refine FExpr.Denotes.ind rfl rfl rfl hList rfl ?_ ?_ nofun
    · intro i
      rw [Fin.fin_one_eq_zero i]
      exact .zero
    · intro i
      rw [Fin.fin_one_eq_zero i]
      exact FExpr.Denotes.charType hChar
  convert h using 2
  funext i
  rw [Fin.fin_one_eq_zero i]
  rfl

theorem FExpr.listChar_noProj (P : StrPos) : (FExpr.listChar P).NoProj :=
  .ind (by simpa [FExpr.char] using (.ind (by simp) (by simp) : (FExpr.char P.char).NoProj))
    (by simp)

theorem InferSpec.strLit {F : FEnv} {ℓ : Nat} {G : FCtx} {P : StrPos} {str : String}
    {cod : FExpr} {IChar : FInductive}
    (hOfNat : InferSpec F ℓ G (.const P.ofNat #[]) (.forallE (FExpr.nat P.nat) (FExpr.char P.char)))
    (hOfList : InferSpec F ℓ G (.const P.ofList #[]) (.forallE (FExpr.listChar P) cod))
    (hList : F[P.list]? = some (.inductive List.sig FList.raw))
    (hChar : F[P.char]? = some (.inductive Char.sig IChar))
    (hCharLevel : IChar.level = .succ .zero)
    (hcod : cod.NoProj) (hc : cod.data.looseBVarRange.toNat = 0) (hr : cod.fvarRange ≤ G.size) :
    InferSpec F ℓ G (.strLit P str) cod := by
  intro ζ E n Γ e₀ hS hden
  have .strLit (ηNat := ηNat) (ηList := ηList) (ηChar := ηChar) (ηOfNat := ηOfNat)
    (ηOfList := ηOfList) hηNat hηList hηChar hηOfNat hηOfList := hden
  have ⟨_, _, hd₁, ht₁, hty₁⟩ := hOfNat hS (FExpr.Denotes.const₀ hηOfNat)
  obtain rfl := hd₁.unique (FExpr.Denotes.const₀ hηOfNat) (.const _ _)
  obtain rfl := ht₁.unique (.forallE (.nat hηNat) (.charType hηChar))
    (.forallE (.ind (by simp) (by simp)) (.ind (by simp) (by simp)))
  have ⟨_, _, hd₂, ht₂, hty₂⟩ := hOfList hS (FExpr.Denotes.const₀ hηOfList)
  obtain rfl := hd₂.unique (FExpr.Denotes.const₀ hηOfList) (.const _ _)
  have .forallE hdom hC := ht₂
  obtain rfl := hdom.unique (.listChar hηList hηChar) (FExpr.listChar_noProj P)
  have ⟨ηL, hηL, hI⟩ := hS.env.inductive hList
  cases hηList.symm.trans hηL
  have hL : (E.get ηList).block = List.block := hI.unique FList.denotes FList.noProj
  have ⟨ηC, hηC, hIC⟩ := hS.env.inductive hChar
  cases hηChar.symm.trans hηC
  have hCl : (E.get ηChar).block.level = .succ .zero := by
    have ⟨l, hl, hleq⟩ := hIC.level
    rw [hCharLevel] at hl
    have .succ .zero := hl
    exact hleq.symm
  have hn := hS.size
  subst hn
  have h₀ := hC.unbind (Nat.le_add_left _ _) hc
  have ⟨S, hSd⟩ := h₀.strengthen hr hc
  obtain rfl := h₀.unique hSd.wk hcod
  have ⟨_, hsort⟩ := hty₂.regular
  have ⟨_, _, _, hcodT, _⟩ := hsort.forallE_ty_inv
  refine ⟨_, _, .strLit hηNat hηList hηChar hηOfNat hηOfList, hSd, ?_⟩
  simpa using Expr.strLit_typed hL hCl hty₁ hty₂ hcodT str

end Metalean.Checker.Fast
