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

namespace Metalean.FastChecker

structure Literals where
  nat : Nat
  list : Nat
  char : Nat
  charOfNat : Nat
  stringOfList : Nat
  bool : Nat
  pred : Nat
  add : Nat
  sub : Nat
  mul : Nat
  pow : Nat
  beq : Nat
  ble : Nat
  div : Nat
  mod : Nat
  gcd : Nat
  land : Nat
  lor : Nat
  xor : Nat
  shiftLeft : Nat
  shiftRight : Nat

namespace Literals

@[reducible] def Nat.zeroSig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def Nat.succSig : CtorSig 1 where
  nfields := 0
  nrecFields := 1
  recursiveArity := ![0]
  recursiveTarget := ![0]

@[reducible] def Nat.sig : IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _ := ![zeroSig, succSig]

@[reducible] def List.nilSig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def List.consSig : CtorSig 1 where
  nfields := 1
  nrecFields := 1
  recursiveArity := ![0]
  recursiveTarget := ![0]

@[reducible] def List.sig : IndSig where
  nlevels := 1
  nparams := 1
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _ := ![nilSig, consSig]

@[reducible] def Bool.ctorSig : CtorSig 1 where
  nfields := 0
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def Bool.sig : IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 2
  ctors _ := ![ctorSig, ctorSig]

@[reducible] def Char.mkSig : CtorSig 1 where
  nfields := 2
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def Char.sig : IndSig where
  nlevels := 0
  nparams := 0
  nsorts := 1
  nindices _ := 0
  nctors _ := 1
  ctors _ := ![mkSig]

variable {ζ : Sigs} {ℓ n : Nat}

def natType (η : Head ζ (.inductive Nat.sig)) : Expr ζ ℓ n :=
  .ind η 0 ![] ![] ![]

def natZero (η : Head ζ (.inductive Nat.sig)) : Expr ζ ℓ n :=
  .ctor η 0 0 ![] ![] ![] ![]

def natSucc (η : Head ζ (.inductive Nat.sig)) (e : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ctor η 0 1 ![] ![] ![] ![e]

def boolType (ηBool : Head ζ (.inductive Bool.sig)) : Expr ζ ℓ n :=
  .ind ηBool 0 ![] ![] ![]

def boolFalse (ηBool : Head ζ (.inductive Bool.sig)) : Expr ζ ℓ n :=
  .ctor ηBool 0 0 ![] ![] ![] ![]

def boolTrue (ηBool : Head ζ (.inductive Bool.sig)) : Expr ζ ℓ n :=
  .ctor ηBool 0 1 ![] ![] ![] ![]

def boolLit (ηBool : Head ζ (.inductive Bool.sig)) : Bool → Expr ζ ℓ n
  | false => boolFalse ηBool
  | true => boolTrue ηBool

def natArrow (η : Head ζ (.inductive Nat.sig)) : Expr ζ ℓ n :=
  .forallE (natType η) (natType η)

def natArrow₂ (η : Head ζ (.inductive Nat.sig)) : Expr ζ ℓ n :=
  .forallE (natType η) (natArrow η)

def natOp₁ {kind : ConstKind} (ηOp : Head ζ (.const kind 0)) (e : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .app (.const ηOp ![]) e

def natOp₂ {kind : ConstKind} (ηOp : Head ζ (.const kind 0)) (e₁ e₂ : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .app (.app (.const ηOp ![]) e₁) e₂

def natLit (η : Head ζ (.inductive Nat.sig)) : Nat → Expr ζ ℓ n
  | 0 => .ctor η 0 0 ![] ![] ![] ![]
  | k + 1 => .ctor η 0 1 ![] ![] ![] ![natLit η k]

def charList (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0)) :
    List Char → Expr ζ ℓ n
  | [] => .ctor ηList 0 0 ![.zero] ![.ind ηChar 0 ![] ![] ![]] ![] ![]
  | c :: cs =>
    .ctor ηList 0 1 ![.zero] ![.ind ηChar 0 ![] ![] ![]]
      ![.app (.const ηOfNat ![]) (natLit ηNat c.toNat)] ![charList ηNat ηList ηChar ηOfNat cs]

def strLit (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (ηOfList : Head ζ (.const .def 0)) (str : String) : Expr ζ ℓ n :=
  .app (.const ηOfList ![]) (charList ηNat ηList ηChar ηOfNat str.toList)

variable {ηNat : Head ζ (.inductive Nat.sig)} {ηBool : Head ζ (.inductive Bool.sig)}
  {ηList : Head ζ (.inductive List.sig)} {ηChar : Head ζ (.inductive Char.sig)}
  {ηOfNat : Head ζ (.const .def 0)} {kind : ConstKind} {ηOp : Head ζ (.const kind 0)}

theorem natType_subst {m : Nat} (σ : Subst ζ ℓ m n) :
    (natType ηNat : Expr ζ ℓ m).subst σ = natType ηNat := by
  simp only [natType, Expr.subst]
  congr 1 <;> exact Fin.emptyFun _ _

theorem natZero_subst {m : Nat} (σ : Subst ζ ℓ m n) :
    (natZero ηNat : Expr ζ ℓ m).subst σ = natZero ηNat := by
  simp only [natZero, Expr.subst]
  congr 1 <;> exact Fin.emptyFun _ _

theorem natSucc_subst {m : Nat} (σ : Subst ζ ℓ m n) (e : Expr ζ ℓ m) :
    (natSucc ηNat e).subst σ = natSucc ηNat (e.subst σ) := by
  have hrec : (fun f : Fin (Nat.sig.ctors 0 1).nrecFields => ((![e] : Fin 1 → _) f).subst σ) =
      ![e.subst σ] :=
    funext fun ⟨0, _⟩ => rfl
  simp only [natSucc, Expr.subst]
  congr 1 <;> exact Fin.emptyFun _ _

theorem natOp₂_subst {m : Nat} (σ : Subst ζ ℓ m n) (x y : Expr ζ ℓ m) :
    (natOp₂ ηOp x y).subst σ = natOp₂ ηOp (x.subst σ) (y.subst σ) := by
  simp [natOp₂, Expr.subst]

theorem natOp₁_subst {m : Nat} (σ : Subst ζ ℓ m n) (x : Expr ζ ℓ m) :
    (natOp₁ ηOp x).subst σ = natOp₁ ηOp (x.subst σ) := by
  simp [natOp₁, Expr.subst]

theorem natType_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') :
    (natType ηNat : Expr ζ ℓ n).instL σ = natType ηNat := by
  simp only [natType, Expr.instL]
  congr 1 <;> exact Fin.emptyFun _ _

theorem natZero_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') :
    (natZero ηNat : Expr ζ ℓ n).instL σ = natZero ηNat := by
  simp only [natZero, Expr.instL]
  congr 1 <;> exact Fin.emptyFun _ _

theorem natSucc_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') (e : Expr ζ ℓ n) :
    (natSucc ηNat e).instL σ = natSucc ηNat (e.instL σ) := by
  have hrec : (fun f : Fin (Nat.sig.ctors 0 1).nrecFields => ((![e] : Fin 1 → _) f).instL σ) =
      ![e.instL σ] :=
    funext fun ⟨0, _⟩ => rfl
  simp! only [natSucc]
  congr 1 <;> exact Fin.emptyFun _ _

theorem natConst_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') :
    (Expr.const ηOp fun a => Level.inst σ (![] a) : Expr ζ ℓ' n) = .const ηOp ![] :=
  congrArg (Expr.const ηOp) (Fin.emptyFun _ _)

theorem natOp₂_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') (x y : Expr ζ ℓ n) :
    (natOp₂ ηOp x y).instL σ = natOp₂ ηOp (x.instL σ) (y.instL σ) := by
  simp! only [natOp₂, natConst_instL]

theorem natOp₁_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') (x : Expr ζ ℓ n) :
    (natOp₁ ηOp x).instL σ = natOp₁ ηOp (x.instL σ) := by
  simp! only [natOp₁, natConst_instL]

theorem boolType_subst {m : Nat} (σ : Subst ζ ℓ m n) :
    (boolType ηBool : Expr ζ ℓ m).subst σ = boolType ηBool := by
  simp only [boolType, Expr.subst]
  congr 1 <;> exact Fin.emptyFun _ _

theorem boolType_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') :
    (boolType ηBool : Expr ζ ℓ n).instL σ = boolType ηBool := by
  simp only [boolType, Expr.instL]
  congr 1 <;> exact Fin.emptyFun _ _

theorem boolLit_subst {m : Nat} (σ : Subst ζ ℓ m n) :
    (b : Bool) →
    (boolLit ηBool b : Expr ζ ℓ m).subst σ = boolLit ηBool b
  | false => by
    simp only [boolLit, boolFalse, Expr.subst]
    congr 1 <;> exact Fin.emptyFun _ _
  | true => by
    simp only [boolLit, boolTrue, Expr.subst]
    congr 1 <;> exact Fin.emptyFun _ _

theorem boolLit_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') :
    (b : Bool) →
    (boolLit ηBool b : Expr ζ ℓ n).instL σ = boolLit ηBool b
  | false => by
    simp only [boolLit, boolFalse, Expr.instL]
    congr 1 <;> exact Fin.emptyFun _ _
  | true => by
    simp only [boolLit, boolTrue, Expr.instL]
    congr 1 <;> exact Fin.emptyFun _ _

theorem natArrow_subst {m : Nat} (σ : Subst ζ ℓ m n) :
    (natArrow ηNat : Expr ζ ℓ m).subst σ = natArrow ηNat := by
  simp [natArrow, natType_subst]

theorem natArrow_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') :
    (natArrow ηNat : Expr ζ ℓ n).instL σ = natArrow ηNat := by
  simp [natArrow, Expr.instL, natType_instL]

theorem natArrow₂_subst {m : Nat} (σ : Subst ζ ℓ m n) :
    (natArrow₂ ηNat : Expr ζ ℓ m).subst σ = natArrow₂ ηNat := by
  simp [natArrow₂, natType_subst, natArrow_subst]

theorem natArrow₂_instL {ℓ' : Nat} (σ : Param ℓ → Level ℓ') :
    (natArrow₂ ηNat : Expr ζ ℓ n).instL σ = natArrow₂ ηNat := by
  simp [natArrow₂, Expr.instL, natType_instL, natArrow_instL]

variable {ζ₂ : Sigs}

theorem natType_map (pre : ζ ⟶ ζ₂) :
    (natType ηNat : Expr ζ ℓ n).map pre = natType (ηNat.map pre) := by
  simp only [natType, Expr.map]
  congr 1 <;> exact Fin.emptyFun _ _

theorem boolType_map (pre : ζ ⟶ ζ₂) :
    (boolType ηBool : Expr ζ ℓ n).map pre = boolType (ηBool.map pre) := by
  simp only [boolType, Expr.map]
  congr 1 <;> exact Fin.emptyFun _ _

theorem boolLit_map (pre : ζ ⟶ ζ₂) :
    (b : Bool) →
    (boolLit ηBool b : Expr ζ ℓ n).map pre = boolLit (ηBool.map pre) b
  | false => by
    simp only [boolLit, boolFalse, Expr.map]
    congr 1 <;> exact Fin.emptyFun _ _
  | true => by
    simp only [boolLit, boolTrue, Expr.map]
    congr 1 <;> exact Fin.emptyFun _ _

theorem natOp₂_map (pre : ζ ⟶ ζ₂) (x y : Expr ζ ℓ n) :
    (natOp₂ ηOp x y).map pre = natOp₂ (ηOp.map pre) (x.map pre) (y.map pre) := by
  simp [natOp₂, Expr.map]

theorem charListLevels :
    (![.zero] : Fin 1 → Level ℓ) = (⟦(![.zero] : Fin 1 → RawLevel ℓ) ·⟧) :=
  funext (Fin.cases rfl nofun)

theorem charList_nil :
    (charList ηNat ηList ηChar ηOfNat [] : Expr ζ ℓ n) =
      .ctor ηList 0 0 (⟦(![.zero] : Fin 1 → RawLevel ℓ) ·⟧) ![.ind ηChar 0 ![] ![] ![]] ![] ![] :=
  congr(.ctor ηList 0 0 $charListLevels ![.ind ηChar 0 ![] ![] ![]] ![] ![])

theorem charList_cons (c : Char) (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat (c :: cs) : Expr ζ ℓ n) =
      .ctor ηList 0 1 (⟦(![.zero] : Fin 1 → RawLevel ℓ) ·⟧) ![.ind ηChar 0 ![] ![] ![]]
        ![.app (.const ηOfNat ![]) (Literals.natLit ηNat c.toNat)]
        ![charList ηNat ηList ηChar ηOfNat cs] :=
  congr(.ctor ηList 0 1 $charListLevels ![.ind ηChar 0 ![] ![] ![]]
    ![.app (.const ηOfNat ![]) (Literals.natLit ηNat c.toNat)]
    ![charList ηNat ηList ηChar ηOfNat cs])

@[simp] theorem subst_natLit {m : Nat} (σ : Subst ζ ℓ m n) (η : Head ζ (.inductive Nat.sig))
    (num : Nat) :
    (natLit η num).subst σ = natLit η num := by
  induction num with
  | zero => exact natZero_subst σ
  | succ num ih => exact (natSucc_subst σ _).trans congr(natSucc η $ih)

@[simp] theorem subst_charList {m : Nat} (σ : Subst ζ ℓ m n)
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat cs).subst σ = charList ηNat ηList ηChar ηOfNat cs := by
  have hChar : Expr.subst σ (.ind ηChar 0 ![] ![] ![]) = .ind ηChar 0 ![] ![] ![] := by
    simp only [Expr.subst]
    congr <;> funext i <;> exact i.elim0
  induction cs with
  | nil =>
    simp only [charList, Expr.subst]
    congr 1 <;> funext i <;> obtain ⟨_ | _, hi⟩ := i
    all_goals first
      | exact hChar
      | simp at hi
  | cons c cs ih =>
    simp only [charList, Expr.subst]
    congr 1 <;> funext i <;> obtain ⟨_ | _, hi⟩ := i
    all_goals first
      | exact hChar
      | exact ih
      | exact congrArg (Expr.app (.const ηOfNat ![])) (subst_natLit σ ηNat c.toNat)
      | simp at hi

@[simp] theorem subst_strLit {m : Nat} (σ : Subst ζ ℓ m n)
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (ηOfList : Head ζ (.const .def 0)) (str : String) :
    (strLit ηNat ηList ηChar ηOfNat ηOfList str).subst σ =
      strLit ηNat ηList ηChar ηOfNat ηOfList str := by
  simp [strLit, Expr.subst, subst_charList]

@[simp] theorem instL_natLit {ℓ' : Nat} (σ : Param ℓ → Level ℓ')
    (η : Head ζ (.inductive Nat.sig)) (num : Nat) :
    (natLit η num : Expr ζ ℓ n).instL σ = natLit η num := by
  induction num with
  | zero => exact natZero_instL σ
  | succ num ih => exact (natSucc_instL σ _).trans congr(natSucc η $ih)

@[simp] theorem instL_charList {ℓ' : Nat} (σ : Param ℓ → Level ℓ')
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat cs : Expr ζ ℓ n).instL σ =
      charList ηNat ηList ηChar ηOfNat cs := by
  have hChar : Expr.instL σ (.ind ηChar 0 ![] ![] ![] : Expr ζ ℓ n) = .ind ηChar 0 ![] ![] ![] := by
    simp only [Expr.instL]
    congr <;> funext i <;> exact i.elim0
  induction cs with
  | nil =>
    simp only [charList, Expr.instL]
    congr 1 <;> funext i <;> obtain ⟨_ | _, hi⟩ := i
    all_goals first
      | exact hChar
      | rfl
      | simp at hi
  | cons c cs ih =>
    simp only [charList, Expr.instL]
    congr 1 <;> funext i <;> obtain ⟨_ | _, hi⟩ := i
    all_goals first
      | exact hChar
      | exact ih
      | rfl
      | exact (natOp₁_instL σ _).trans congr(natOp₁ ηOfNat $(instL_natLit σ ηNat c.toNat))
      | simp at hi

@[simp] theorem instL_strLit {ℓ' : Nat} (σ : Param ℓ → Level ℓ')
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (ηOfList : Head ζ (.const .def 0)) (str : String) :
    (strLit ηNat ηList ηChar ηOfNat ηOfList str : Expr ζ ℓ n).instL σ =
      strLit ηNat ηList ηChar ηOfNat ηOfList str := by
  simp only [strLit, Expr.instL, instL_charList]
  rw [Fin.emptyFun (fun i => Level.inst σ (![] i)) ![]]

@[simp] theorem map_natLit {ζ₂ : Sigs} (pre : ζ ⟶ ζ₂) (η : Head ζ (.inductive Nat.sig))
    (num : Nat) :
    (natLit η num : Expr ζ ℓ n).map pre = natLit (η.map pre) num := by
  induction num with
  | zero =>
    simp only [natLit, Expr.map]
    congr <;> funext i <;> exact i.elim0
  | succ num ih =>
    simp only [natLit, Expr.map]
    congr 1 <;> funext i <;> obtain ⟨_ | _, hi⟩ := i
    all_goals first
      | exact ih
      | simp at hi

@[simp] theorem map_charList {ζ₂ : Sigs} (pre : ζ ⟶ ζ₂)
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (cs : List Char) :
    (charList ηNat ηList ηChar ηOfNat cs : Expr ζ ℓ n).map pre =
      charList (ηNat.map pre) (ηList.map pre) (ηChar.map pre) (ηOfNat.map pre) cs := by
  have hChar : Expr.map pre (.ind ηChar 0 ![] ![] ![] : Expr ζ ℓ n) =
      .ind (ηChar.map pre) 0 ![] ![] ![] := by
    simp only [Expr.map]
    congr <;> funext i <;> exact i.elim0
  induction cs with
  | nil =>
    simp only [charList, Expr.map]
    congr 1 <;> funext i <;> obtain ⟨_ | _, hi⟩ := i
    all_goals first
      | exact hChar
      | simp at hi
  | cons c cs ih =>
    simp only [charList, Expr.map]
    congr 1 <;> funext i <;> obtain ⟨_ | _, hi⟩ := i
    all_goals first
      | exact hChar
      | exact ih
      | change Expr.map pre (.app (.const ηOfNat ![]) (natLit ηNat c.toNat)) = _
        simp only [Expr.map, map_natLit]
        rfl
      | simp at hi

@[simp] theorem map_strLit {ζ₂ : Sigs} (pre : ζ ⟶ ζ₂)
    (ηNat : Head ζ (.inductive Nat.sig)) (ηList : Head ζ (.inductive List.sig))
    (ηChar : Head ζ (.inductive Char.sig)) (ηOfNat : Head ζ (.const .def 0))
    (ηOfList : Head ζ (.const .def 0)) (str : String) :
    (strLit ηNat ηList ηChar ηOfNat ηOfList str : Expr ζ ℓ n).map pre =
      strLit (ηNat.map pre) (ηList.map pre) (ηChar.map pre) (ηOfNat.map pre) (ηOfList.map pre)
        str := by
  simp [strLit, Expr.map, map_charList]

theorem natType_rename {m : Nat} (ρ : Ren n m) :
    (natType ηNat : Expr ζ ℓ n).rename ρ = natType ηNat := by
  rw [← Expr.subst_vars]
  exact natType_subst _

theorem boolType_rename {m : Nat} (ρ : Ren n m) :
    (boolType ηBool : Expr ζ ℓ n).rename ρ = boolType ηBool := by
  rw [← Expr.subst_vars]
  exact boolType_subst _

theorem boolLit_rename {m : Nat} (ρ : Ren n m) (b : Bool) :
    (boolLit ηBool b : Expr ζ ℓ n).rename ρ = boolLit ηBool b := by
  rw [← Expr.subst_vars]
  exact boolLit_subst _ b

theorem natLit_rename {m : Nat} (ρ : Ren n m) (num : Nat) :
    (natLit ηNat num : Expr ζ ℓ n).rename ρ = natLit ηNat num := by
  rw [← Expr.subst_vars]
  exact subst_natLit _ _ num

theorem natOp₂_rename {m : Nat} (ρ : Ren n m) (x y : Expr ζ ℓ n) :
    (natOp₂ ηOp x y).rename ρ = natOp₂ ηOp (x.rename ρ) (y.rename ρ) := by
  simp [natOp₂, Expr.rename]

theorem natType_wkClosed :
    (natType ηNat : Expr ζ ℓ 0).wkClosed (n := n) = natType ηNat :=
  Expr.wkClosed_of_rename natType_rename n

theorem boolType_wkClosed :
    (boolType ηBool : Expr ζ ℓ 0).wkClosed (n := n) = boolType ηBool :=
  Expr.wkClosed_of_rename boolType_rename n

theorem boolLit_wkClosed (b : Bool) :
    (boolLit ηBool b : Expr ζ ℓ 0).wkClosed (n := n) = boolLit ηBool b :=
  Expr.wkClosed_of_rename (boolLit_rename · b) n

theorem natLit_wkClosed (num : Nat) :
    (natLit ηNat num : Expr ζ ℓ 0).wkClosed (n := n) = natLit ηNat num :=
  Expr.wkClosed_of_rename (natLit_rename · num) n

theorem natOp₂_wkClosed (x y : Expr ζ ℓ 0) :
    (natOp₂ ηOp x y).wkClosed (n := n) = natOp₂ ηOp x.wkClosed y.wkClosed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Expr.wkClosed, ih]
    rfl

end Literals

end Metalean.FastChecker
