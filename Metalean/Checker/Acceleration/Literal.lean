/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Expr
public import Metalean.Syntax.Substitution
public import Metalean.Frontend.Lookup

@[expose] public section

namespace Metalean

protected abbrev Nat.zero.sig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

protected abbrev Nat.succ.sig : CtorSig 1 where
  nfields := 0
  nrecFields := 1
  recursiveArity := ![0]
  recursiveTarget := ![0]

protected abbrev Nat.sig : IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _
    | 0 => Nat.zero.sig
    | 1 => Nat.succ.sig

protected abbrev List.nil.sig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

protected abbrev List.cons.sig : CtorSig 1 where
  nfields := 1
  nrecFields := 1
  recursiveArity := ![0]
  recursiveTarget := ![0]

protected abbrev List.sig : IndSig where
  nlevels := 1
  nparams := 1
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _
    | 0 => List.nil.sig
    | 1 => List.cons.sig

protected abbrev Bool.false.sig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

protected abbrev Bool.true.sig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

protected abbrev Bool.sig : IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _
    | 0 => Bool.false.sig
    | 1 => Bool.true.sig

protected abbrev Char.mk.sig : CtorSig 1 where
  nfields := 2
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

protected abbrev Char.sig : IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 1
  ctors _
    | 0 => Char.mk.sig

namespace Expr

variable {ζ ζ₂ : Sigs} {ℓ n : Nat}
  (ηNat : Head ζ (.inductive Nat.sig))
  (ηBool : Head ζ (.inductive Bool.sig))
  (ηList : Head ζ (.inductive List.sig))
  (ηChar : Head ζ (.inductive Char.sig))
  (ηOfNat : Head ζ (.const .def 0))
  (ηOfList : Head ζ (.const .def 0))
  {kind : ConstKind}
  (η : Head ζ (.const kind 0))

abbrev nat : Expr ζ ℓ n := ind ηNat 0 ![] ![] ![]
local notation "ℕ" => nat ηNat
abbrev zero : Expr ζ ℓ n := .ctor ηNat 0 0 ![] ![] ![] ![]
abbrev succ (e : Expr ζ ℓ n) : Expr ζ ℓ n := .ctor ηNat 0 1 ![] ![] ![] ![e]
abbrev natToNat : Expr ζ ℓ n := .forallE ℕ ℕ
abbrev natToNatToNat : Expr ζ ℓ n := .forallE ℕ (natToNat ηNat)

@[simp] def natLit : Nat → Expr ζ ℓ n
  | 0 => zero ηNat
  | k + 1 => succ ηNat (natLit k)

abbrev bool : Expr ζ ℓ n := ind ηBool 0 ![] ![] ![]
local notation "𝔹" => bool ηBool
abbrev boolFalse : Expr ζ ℓ n := .ctor ηBool 0 0 ![] ![] ![] ![]
abbrev boolTrue : Expr ζ ℓ n := .ctor ηBool 0 1 ![] ![] ![] ![]

def boolLit : Bool → Expr ζ ℓ n
  | false => boolFalse ηBool
  | true => boolTrue ηBool

abbrev op₁ (e : Expr ζ ℓ n) : Expr ζ ℓ n := Expr.const η ![] |>.app e
abbrev op₂ (e₁ e₂ : Expr ζ ℓ n) : Expr ζ ℓ n := .appList (.const η ![]) [e₁, e₂]

abbrev list (u : Level ℓ) (α : Expr ζ ℓ n) : Expr ζ ℓ n := ind ηList 0 ![u] ![α] ![]
abbrev listNil (u : Level ℓ) (α : Expr ζ ℓ n) : Expr ζ ℓ n := .ctor ηList 0 0 ![u] ![α] ![] ![]
abbrev listCons (u : Level ℓ) (α h t : Expr ζ ℓ n) : Expr ζ ℓ n := .ctor ηList 0 1 ![u] ![α] ![h] ![t]

abbrev char : Expr ζ ℓ n := ind ηChar 0 ![] ![] ![]

abbrev charOfNat (e : Expr ζ ℓ n) : Expr ζ ℓ n := Expr.const η ![] |>.app e
abbrev stringOfList (e : Expr ζ ℓ n) : Expr ζ ℓ n := Expr.const η ![] |>.app e

def charList : List Char → Expr ζ ℓ n
  | [] => listNil ηList .zero (char ηChar)
  | c :: cs =>
    listCons ηList .zero (char ηChar)
      (charOfNat ηOfNat (natLit ηNat c.toNat)) (charList cs)

abbrev strLit (str : String) : Expr ζ ℓ n :=
  stringOfList ηOfList (charList ηNat ηList ηChar ηOfNat str.toList)

variable {ηNat ηBool ηList ηChar ηOfNat η}

@[simp] theorem boolLit_subst {m : Nat} (σ : Subst ζ ℓ m n) (b : Bool) :
    (boolLit ηBool b : Expr ζ ℓ m).subst σ = boolLit ηBool b := by
  cases b <;> simp [boolLit, Fin.fun_vecEmpty]

@[simp] theorem boolLit_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') (b : Bool) :
    (boolLit ηBool b : Expr ζ ℓ n){σ} = boolLit ηBool b := by
  cases b <;> simp [boolLit]

@[simp] theorem boolLit_map (pre : ζ ⟶ ζ₂) (b : Bool) :
    (boolLit ηBool b : Expr ζ ℓ n).map pre = boolLit (ηBool.map pre) b := by
  cases b <;> simp [boolLit, Fin.fun_vecEmpty]

theorem charListLevels :
    (![.zero] : Fin 1 → Level ℓ) = (⟦(![.zero] : Fin 1 → RawLevel ℓ) ·⟧) :=
  funext (Fin.cases rfl nofun)

theorem charList_nil :
    (charList ηNat ηList ηChar ηOfNat [] : Expr ζ ℓ n) =
      .ctor ηList 0 0 (⟦(![.zero] : Fin 1 → RawLevel ℓ) ·⟧) ![ind ηChar 0 ![] ![] ![]] ![] ![] :=
  congr(.ctor ηList 0 0 $charListLevels ![ind ηChar 0 ![] ![] ![]] ![] ![])

theorem charList_cons (c : Char) (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat (c :: cs) : Expr ζ ℓ n) =
      .ctor ηList 0 1 (⟦(![.zero] : Fin 1 → RawLevel ℓ) ·⟧) ![ind ηChar 0 ![] ![] ![]]
        ![.app (.const ηOfNat ![]) (natLit ηNat c.toNat)]
        ![charList ηNat ηList ηChar ηOfNat cs] :=
  congr(.ctor ηList 0 1 $charListLevels ![ind ηChar 0 ![] ![] ![]]
    ![.app (.const ηOfNat ![]) (natLit ηNat c.toNat)]
    ![charList ηNat ηList ηChar ηOfNat cs])

@[simp] theorem natLit_subst {m : Nat} (σ : Subst ζ ℓ m n) (η : Head ζ (.inductive Nat.sig))
    (num : Nat) :
    (natLit η num).subst σ = natLit η num := by
  induction num <;> simp_all [Fin.fun_vecEmpty, Fin.const_fin_one]

@[simp] theorem charList_subst {m : Nat} (σ : Subst ζ ℓ m n)
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat cs).subst σ = charList ηNat ηList ηChar ηOfNat cs := by
  induction cs <;> simp_all [charList, Fin.fun_vecEmpty, Fin.const_fin_one]

@[simp] theorem natLit_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ')
    (η : Head ζ (.inductive Nat.sig)) (num : Nat) :
    (natLit η num : Expr ζ ℓ n){σ} = natLit η num := by
  induction num <;> simp_all []

@[simp] theorem charList_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ')
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat cs : Expr ζ ℓ n){σ} =
      charList ηNat ηList ηChar ηOfNat cs := by
  induction cs <;> simp_all [charList]

@[simp] theorem natLit_map {ζ₂ : Sigs} (pre : ζ ⟶ ζ₂) (η : Head ζ (.inductive Nat.sig))
    (num : Nat) :
    (natLit η num : Expr ζ ℓ n).map pre = natLit (η.map pre) num := by
  induction num <;> simp_all [Fin.fun_vecEmpty, Fin.const_fin_one]

@[simp] theorem charList_map {ζ₂ : Sigs} (pre : ζ ⟶ ζ₂)
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat cs : Expr ζ ℓ n).map pre =
      charList (ηNat.map pre) (ηList.map pre) (ηChar.map pre) (ηOfNat.map pre) cs := by
  induction cs <;> simp_all [charList, Fin.fun_vecEmpty, Fin.const_fin_one]

@[simp] theorem boolLit_rename {m : Nat} (ρ : Ren n m) (b : Bool) :
    (boolLit ηBool b : Expr ζ ℓ n).rename ρ = boolLit ηBool b := by
  cases b <;> simp [boolLit, Fin.fun_vecEmpty]

@[simp] theorem natLit_rename {m : Nat} (ρ : Ren n m) (num : Nat) :
    (natLit ηNat num : Expr ζ ℓ n).rename ρ = natLit ηNat num := by
  induction num <;> simp_all [Fin.fun_vecEmpty, Fin.const_fin_one]

@[simp] theorem charList_rename {m : Nat} (ρ : Ren n m) (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat cs : Expr ζ ℓ n).rename ρ =
      charList ηNat ηList ηChar ηOfNat cs := by
  induction cs <;> simp_all [charList, Fin.fun_vecEmpty, Fin.const_fin_one]

@[simp] theorem nat_wkClosed : (ℕ : Expr ζ ℓ 0).wkClosed = (ℕ : Expr ζ ℓ n) :=
  wkClosed_of_rename (f := fun _ => ℕ) (fun _ => by simp [Fin.fun_vecEmpty]) n

@[simp] theorem bool_wkClosed : (𝔹 : Expr ζ ℓ 0).wkClosed = (𝔹 : Expr ζ ℓ n) :=
  wkClosed_of_rename (f := fun _ => 𝔹) (fun _ => by simp [Fin.fun_vecEmpty]) n

@[simp] theorem boolLit_wkClosed (b : Bool) :
    (boolLit ηBool b : Expr ζ ℓ 0).wkClosed (n := n) = boolLit ηBool b :=
  wkClosed_of_rename (boolLit_rename · b) n

@[simp] theorem natLit_wkClosed (num : Nat) :
    (natLit ηNat num : Expr ζ ℓ 0).wkClosed (n := n) = natLit ηNat num :=
  wkClosed_of_rename (natLit_rename · num) n

end Expr

end Metalean
