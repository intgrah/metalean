/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Acceleration.Literal
public import Metalean.Typing.Defs
public import Metalean.Typing.Substitution

@[expose] public section

namespace Metalean

namespace List

variable {ζ : Sigs}

def nilDecl : Ctor ζ List.sig 0 List.nil.sig where
  ordinary f := f.elim0
  recursive f := f.elim0
  targetIndices f := f.elim0

def consDecl : Ctor ζ List.sig 0 List.cons.sig where
  ordinary _ := ⟨.var ⟨0, Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right _ _)⟩, .succ (.param 0)⟩
  recursive | ⟨0, _⟩ => ⟨.nil, nofun⟩
  targetIndices f := f.elim0

/-- `List.{u} (α : Type u) : Type u` -/
@[reducible] def block : Inductive ζ List.sig where
  params := #t[.sort (.succ (.param 0))]
  indices _ := .nil
  level := .succ (.param 0)
  ctors
    | ⟨0, _⟩, ⟨0, _⟩ => nilDecl
    | ⟨0, _⟩, ⟨1, _⟩ => consDecl

end List

namespace Expr

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {η : Head ζ (.inductive Nat.sig)}

theorem natTypeIndexDF (is : Fin 0 → Expr ζ ℓ n) :
    E[Γ] ⊢ (.ind η 0 ![] ![] is : Expr ζ ℓ n) ≡ .ind η 0 ![] ![] is :
      .sort (E.get η).block.level{(![] : Param 0 → Level ℓ)} :=
  .indDF nofun nofun

theorem nat_typed :
    E[Γ] ⊢ (Expr.nat η : Expr ζ ℓ n) ≡ Expr.nat η :
      .sort (E.get η).block.level{(![] : Param 0 → Level ℓ)} :=
  natTypeIndexDF ![]

theorem zero_typed :
    E[Γ] ⊢ (Expr.zero η : Expr ζ ℓ n) : Expr.nat η := by
  have h := @Defeq.ctorDF ζ E ℓ n Γ Nat.sig η 0 0 ![] ![] ![] ![] ![] ![] ![] ![] ![]
    nofun nofun nofun nofun nofun (natTypeIndexDF _)
  rwa [Fin.emptyFun (((E.get η).block.ctors 0 0).targetIndex ![] ![] ![]) ![]] at h

theorem succ_congr {e₁ e₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ e₁ ≡ e₂ : Expr.nat η →
    E[Γ] ⊢ Expr.succ η e₁ ≡ Expr.succ η e₂ : Expr.nat η := by
  intro he
  have hty : ∀ f : Fin (Nat.sig.ctors 0 1).nrecFields,
      (((E.get η).block.ctors 0 1).recursive f).instantiatedType η ![] ![] (Fin.append ![] ![]) =
        (Expr.nat η : Expr ζ ℓ n) := fun ⟨0, _⟩ => by
    simp [RecField.instantiatedType, RecField.instantiatedTelescope, Matrix.empty_eq, Expr.nat]
  have h := @Defeq.ctorDF ζ E ℓ n Γ Nat.sig η 0 1 ![] ![] ![] ![] ![] ![e₁] ![e₂] ![]
      ![(E.get η).block.level{(![] : Param 0 → Level ℓ)}]
    nofun nofun
    (fun ⟨0, _⟩ => by rw [hty]; exact he)
    nofun
    (fun ⟨0, _⟩ => by
      change E[Γ] ⊢ (((E.get η).block.ctors 0 1).recursive ⟨0, _⟩).instantiatedType η ![] ![]
          (Fin.append ![] ![]) : _
      rw [hty]
      exact Expr.nat_typed)
    (natTypeIndexDF _)
  rwa [Fin.emptyFun (((E.get η).block.ctors 0 1).targetIndex ![] ![] ![]) ![]] at h

theorem natLit_typed (η : Head ζ (.inductive Nat.sig)) (num : Nat) :
    E[Γ] ⊢ (natLit η num : Expr ζ ℓ n) : Expr.nat η := by
  induction num with
  | zero => exact Expr.zero_typed
  | succ num ih => exact Expr.succ_congr ih

section String

variable {ηList : Head ζ (.inductive List.sig)} {ηChar : Head ζ (.inductive Char.sig)}

theorem char_typed (hC : (E.get ηChar).block.level = .succ .zero) :
    E[Γ] ⊢ (char ηChar : Expr ζ ℓ n) : .sort (.succ .zero) := by
  have h := @Defeq.indDF ζ E ℓ n Γ Char.sig ηChar 0 ![] ![] ![] ![] ![] nofun nofun
  rw [hC] at h
  simpa using h

theorem list_typed (hL : (E.get ηList).block = List.block)
    (hC : (E.get ηChar).block.level = .succ .zero) :
    E[Γ] ⊢ (list ηList .zero (char ηChar) : Expr ζ ℓ n) : .sort (.succ .zero) := by
  have h := @Defeq.indDF ζ E ℓ n Γ List.sig ηList 0 ![.zero] ![char ηChar] ![char ηChar] ![] ![]
    (fun ⟨0, _⟩ => by rw [hL]; simpa [Inductive.paramType] using char_typed hC) nofun
  rw [hL] at h
  simpa using h

theorem listNil_typed (hL : (E.get ηList).block = List.block)
    (hC : (E.get ηChar).block.level = .succ .zero) :
    E[Γ] ⊢ (listNil ηList .zero (char ηChar) : Expr ζ ℓ n) : list ηList .zero (char ηChar) := by
  have h := @Defeq.ctorDF ζ E ℓ n Γ List.sig ηList 0 0 ![.zero] ![char ηChar] ![char ηChar]
    ![] ![] ![] ![] ![] ![]
    (fun ⟨0, _⟩ => by rw [hL]; simpa [Inductive.paramType] using char_typed hC)
    nofun nofun nofun nofun
    (by rw [hL]; simpa [Matrix.empty_eq] using list_typed hL hC)
  rw [hL] at h
  simpa [Matrix.empty_eq] using h

theorem listCons_typed (hL : (E.get ηList).block = List.block)
    (hC : (E.get ηChar).block.level = .succ .zero) {h t : Expr ζ ℓ n} :
    E[Γ] ⊢ h : char ηChar →
    E[Γ] ⊢ t : list ηList .zero (char ηChar) →
    E[Γ] ⊢ listCons ηList .zero (char ηChar) h t : list ηList .zero (char ηChar) := by
  intro hh ht
  have h := @Defeq.ctorDF ζ E ℓ n Γ List.sig ηList 0 1 ![.zero] ![char ηChar] ![char ηChar]
    ![h] ![h] ![t] ![t] ![.succ .zero] ![.succ .zero]
    (fun ⟨0, _⟩ => by rw [hL]; simpa [Inductive.paramType] using char_typed hC)
    (fun ⟨0, _⟩ => by rw [hL]; simpa [List.consDecl] using hh)
    (fun ⟨0, _⟩ => by rw [hL]; simpa [List.consDecl, RecField.instantiatedType,
      RecField.instantiatedTelescope, RecField.instantiatedIndices, Matrix.empty_eq,
      Fin.const_fin_one, Expr.wkN] using ht)
    (fun ⟨0, _⟩ => by rw [hL]; simpa [Ctor.ordinaryFieldExpr, List.consDecl] using char_typed hC)
    (fun ⟨0, _⟩ => by rw [hL]; simpa [Ctor.recursiveFieldExpr, List.consDecl,
      RecField.instantiatedType, RecField.instantiatedTelescope, RecField.instantiatedIndices,
      Matrix.empty_eq, Fin.const_fin_one, Expr.wkN] using list_typed hL hC)
    (by rw [hL]; simpa [Matrix.empty_eq] using list_typed hL hC)
  rw [hL] at h
  simpa [Matrix.empty_eq] using h

variable {ηNat : Head ζ (.inductive Nat.sig)} {ηOfNat ηOfList : Head ζ (.const .def 0)}

theorem charOfNat_typed (hC : (E.get ηChar).block.level = .succ .zero)
    (hOfNat : E[Γ] ⊢ (.const ηOfNat ![] : Expr ζ ℓ n) : .forallE (nat ηNat) (char ηChar))
    (num : Nat) :
    E[Γ] ⊢ (charOfNat ηOfNat (natLit ηNat num) : Expr ζ ℓ n) : char ηChar := by
  have ha := natLit_typed (E := E) (Γ := Γ) ηNat num
  simpa [char, charOfNat, Expr.inst, Fin.fun_vecEmpty] using
    Defeq.appDF nat_typed (char_typed hC) hOfNat ha ((char_typed hC).inst_congr ha)

theorem charList_typed (hL : (E.get ηList).block = List.block)
    (hC : (E.get ηChar).block.level = .succ .zero)
    (hOfNat : E[Γ] ⊢ (.const ηOfNat ![] : Expr ζ ℓ n) : .forallE (nat ηNat) (char ηChar))
    (cs : List Char) :
    E[Γ] ⊢ (charList ηNat ηList ηChar ηOfNat cs : Expr ζ ℓ n) : list ηList .zero (char ηChar) := by
  induction cs with
  | nil => exact listNil_typed hL hC
  | cons c cs ih => exact listCons_typed hL hC (charOfNat_typed hC hOfNat c.toNat) ih

theorem strLit_typed {C : Expr ζ ℓ (n + 1)} {l : Level ℓ} (hL : (E.get ηList).block = List.block)
    (hC : (E.get ηChar).block.level = .succ .zero)
    (hOfNat : E[Γ] ⊢ (.const ηOfNat ![] : Expr ζ ℓ n) : .forallE (nat ηNat) (char ηChar))
    (hOfList : E[Γ] ⊢ (.const ηOfList ![] : Expr ζ ℓ n) : .forallE (list ηList .zero (char ηChar)) C)
    (hcod : E[Γ.snoc (list ηList .zero (char ηChar))] ⊢ C : .sort l) (str : String) :
    E[Γ] ⊢ (strLit ηNat ηList ηChar ηOfNat ηOfList str : Expr ζ ℓ n) :
      C.inst (charList ηNat ηList ηChar ηOfNat str.toList) := by
  have ha := charList_typed hL hC hOfNat str.toList
  exact Defeq.appDF (list_typed hL hC) hcod hOfList ha (hcod.inst_congr ha)

end String

end Expr

end Metalean
