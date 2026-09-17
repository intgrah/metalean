/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Acceleration.Context
public import Metalean.FastChecker.Acceleration.Equations
public import Metalean.FastChecker.Acceleration.Extension
public import Metalean.FastChecker.Infer
public import Metalean.FastChecker.WF

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

variable (L : Literals) (F : FEnv) (hints : Array Export.Hints)

def ConstHeadSpec (pos : Nat) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
  FEnv.Denotes L F E →
  ∃ η : Head ζ (.const .def 0), ζ.lookup pos = some ⟨.const .def 0, η⟩

def constHead (pos : Nat) : Except Failure (PLift (ConstHeadSpec L F pos)) :=
  match hfe : F[pos]? with
  | some (.def 0 _ _) => pure ⟨fun {_ _} hE => FEnv.Denotes.lookup (E := ⟨_, _⟩) hE hfe rfl⟩
  | _ => throw .internal

def bound (pos : Nat) : Except Failure (PLift (pos < F.size)) :=
  if h : pos < F.size then pure ⟨h⟩ else throw .internal

def entryBoolSig :
    (fe? : Option FEntry) → Option {I : FInductive // fe? = some (.inductive Literals.Bool.sig I)}
  | some (.inductive ι I) => if hι : ι = Literals.Bool.sig then some ⟨I, by rw [hι]⟩ else none
  | _ => none

def boolSig :
    Except Failure
      (PLift (∃ I : FInductive, F[L.bool]? = some (.inductive Literals.Bool.sig I))) :=
  match entryBoolSig F[L.bool]? with
  | some r => pure ⟨r.val, r.property⟩
  | none => throw Failure.internal

def natDefEq (ft fe₁ fe₂ : FExpr) :
    Except Failure (PLift (DefEqAtSpec L F 0 (natCtx L) ft fe₁ fe₂)) :=
  (isDefEqAt L F 0 hints {} (natCtx L) ft fe₁ fe₂).eval

def UnaryTypeSpec (pos : Nat) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃ηNat : Head ζ (.inductive Literals.Nat.sig)⦄ ⦃kind : ConstKind⦄
    ⦃ηOp : Head ζ (.const kind 0)⦄,
  FEnv.Denotes L F E →
  E.Ordered →
  L.NatTrust E →
  ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ →
  ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
  Literals.UnaryType E ηNat ηOp

def BinaryTypeSpec (pos : Nat) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃ηNat : Head ζ (.inductive Literals.Nat.sig)⦄ ⦃kind : ConstKind⦄
    ⦃ηOp : Head ζ (.const kind 0)⦄,
  FEnv.Denotes L F E →
  E.Ordered →
  L.NatTrust E →
  ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ →
  ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
  Literals.BinaryType E ηNat ηOp

def PredEqsSpec (pos : Nat) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃ηNat : Head ζ (.inductive Literals.Nat.sig)⦄ ⦃kind : ConstKind⦄
    ⦃ηOp : Head ζ (.const kind 0)⦄,
  FEnv.Denotes L F E →
  E.Ordered →
  L.NatTrust E →
  ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ →
  ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
  Literals.PredEqs E ηNat ηOp

def AddEqsSpec (pos : Nat) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃ηNat : Head ζ (.inductive Literals.Nat.sig)⦄ ⦃kind : ConstKind⦄
    ⦃ηOp : Head ζ (.const kind 0)⦄,
  FEnv.Denotes L F E →
  E.Ordered →
  L.NatTrust E →
  ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ →
  ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
  Literals.AddEqs E ηNat ηOp

def MulEqsSpec (pos : Nat) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃ηNat : Head ζ (.inductive Literals.Nat.sig)⦄
    ⦃kindAdd : ConstKind⦄ ⦃ηAdd : Head ζ (.const kindAdd 0)⦄ ⦃kind : ConstKind⦄
    ⦃ηOp : Head ζ (.const kind 0)⦄,
  FEnv.Denotes L F E →
  E.Ordered →
  L.NatTrust E →
  ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩ →
  ζ.lookup L.add = some ⟨.const kindAdd 0, ηAdd⟩ →
  ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
  Literals.MulEqs E ηNat ηAdd ηOp

def checkUnaryType (pos : Nat) : Except Failure (PLift (UnaryTypeSpec L F pos)) := do
  let ⟨h⟩ ← natDefEq L F hints (.natArrow L) (.const pos #[]) (.const pos #[])
  pure ⟨fun {_ _ _ _ _} hE ho htr hη hηOp =>
    (NatAt.mk hE ho htr hη Literals.natZeroTyped Literals.natZeroTyped).eq h
      (.natArrow hη) (.const hηOp) (.const hηOp)⟩

def checkBinaryType (pos : Nat) : Except Failure (PLift (BinaryTypeSpec L F pos)) := do
  let ⟨h⟩ ← natDefEq L F hints (.natArrow₂ L) (.const pos #[]) (.const pos #[])
  pure ⟨fun {_ _ _ _ _} hE ho htr hη hηOp =>
    (NatAt.mk hE ho htr hη Literals.natZeroTyped Literals.natZeroTyped).eq h
      (.natArrow₂ hη) (.const hηOp) (.const hηOp)⟩

def checkPredEqs (pos : Nat) : Except Failure (PLift (PredEqsSpec L F pos)) := do
  let ⟨hzero⟩ ← natDefEq L F hints (.nat L)
    (.op₁ pos (.zero L)) (.zero L)
  let ⟨hsucc⟩ ← natDefEq L F hints (.nat L)
    (.op₁ pos (.succ L (.fvar 1))) (.fvar 1)
  pure ⟨fun {_ _ _ _ _} hE ho htr hη hηOp =>
    { zero :=
        (NatAt.mk hE ho htr hη Literals.natZeroTyped Literals.natZeroTyped).eq hzero
          (.natType hη) (.op1 hηOp (.zero hη)) (.zero hη)
      succ := fun _y hy =>
        (NatAt.mk hE ho htr hη Literals.natZeroTyped hy).eq hsucc
          (.natType hη) (.op1 hηOp (.succ hη .varY)) .varY }⟩

def checkAddEqs (pos : Nat) : Except Failure (PLift (AddEqsSpec L F pos)) := do
  let ⟨hzero⟩ ← natDefEq L F hints (.nat L)
    (.op₂ pos (.fvar 0) (.zero L)) (.fvar 0)
  let ⟨hsucc⟩ ← natDefEq L F hints (.nat L)
    (.op₂ pos (.fvar 0) (.succ L (.fvar 1)))
    (.succ L (.op₂ pos (.fvar 0) (.fvar 1)))
  pure ⟨fun {_ _ _ _ _} hE ho htr hη hηOp =>
    { zero := fun _x hx =>
        (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hzero
          (.natType hη) (.op hηOp .varX (.zero hη)) .varX
      succ := fun _x _y hx hy =>
        (NatAt.mk hE ho htr hη hx hy).eq hsucc
          (.natType hη) (.op hηOp .varX (.succ hη .varY))
          (.succ hη (.op hηOp .varX .varY)) }⟩

def checkMulEqs (pos : Nat) : Except Failure (PLift (MulEqsSpec L F pos)) := do
  let ⟨hzero⟩ ← natDefEq L F hints (.nat L)
    (.op₂ pos (.fvar 0) (.zero L)) (.zero L)
  let ⟨hsucc⟩ ← natDefEq L F hints (.nat L)
    (.op₂ pos (.fvar 0) (.succ L (.fvar 1)))
    (.op₂ L.add (.op₂ pos (.fvar 0) (.fvar 1)) (.fvar 0))
  pure ⟨fun {_ _ _ _ _ _ _} hE ho htr hη hηAdd hηOp =>
    { zero := fun _x hx =>
        (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hzero
          (.natType hη) (.op hηOp .varX (.zero hη)) (.zero hη)
      succ := fun _x _y hx hy =>
        (NatAt.mk hE ho htr hη hx hy).eq hsucc
          (.natType hη) (.op hηOp .varX (.succ hη .varY))
          (.op hηAdd (.op hηOp .varX .varY) .varX) }⟩

def verifyAdd : Except Failure (PLift (NatOpSpec L F L.add (· + ·))) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hop⟩ ← bound F L.add
  let ⟨hadd⟩ ← checkAddEqs L F hints L.add
  pure ⟨{ natBound := hnat, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηOp =>
            Literals.add_natLit num₁ num₂ (hadd hE ho htr hη hηOp) }⟩

def verifySub : Except Failure (PLift (NatOpSpec L F L.sub (· - ·))) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hop⟩ ← bound F L.sub
  let ⟨hhead⟩ ← constHead L F L.pred
  let ⟨htype⟩ ← checkUnaryType L F hints L.pred
  let ⟨hpred⟩ ← checkPredEqs L F hints L.pred
  let ⟨hzero⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.sub (.fvar 0) (.zero L)) (.fvar 0)
  let ⟨hsucc⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.sub (.fvar 0) (.succ L (.fvar 1)))
    (.op₁ L.pred (.op₂ L.sub (.fvar 0) (.fvar 1)))
  pure ⟨{ natBound := hnat, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηOp =>
            have ⟨_, hηPred⟩ := hhead hE
            Literals.sub_natLit num₁ num₂
              (htype hE ho htr hη hηPred)
              (hpred hE ho htr hη hηPred)
              { zero := fun _x hx =>
                  (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hzero
                    (.natType hη) (.op hηOp .varX (.zero hη)) .varX
                succ := fun _x _y hx hy =>
                  (NatAt.mk hE ho htr hη hx hy).eq hsucc
                    (.natType hη) (.op hηOp .varX (.succ hη .varY))
                    (.op1 hηPred (.op hηOp .varX .varY)) } }⟩

def verifyMul : Except Failure (PLift (NatOpSpec L F L.mul (· * ·))) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hop⟩ ← bound F L.mul
  let ⟨hhead⟩ ← constHead L F L.add
  let ⟨htype⟩ ← checkBinaryType L F hints L.add
  let ⟨hadd⟩ ← checkAddEqs L F hints L.add
  let ⟨hmul⟩ ← checkMulEqs L F hints L.mul
  pure ⟨{ natBound := hnat, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηOp =>
            have ⟨_, hηAdd⟩ := hhead hE
            Literals.mul_natLit num₁ num₂
              (htype hE ho htr hη hηAdd)
              (hadd hE ho htr hη hηAdd)
              (hmul hE ho htr hη hηAdd hηOp) }⟩

def verifyPow : Except Failure (PLift (NatOpSpec L F L.pow (· ^ ·))) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hop⟩ ← bound F L.pow
  let ⟨haddHead⟩ ← constHead L F L.add
  let ⟨hmulHead⟩ ← constHead L F L.mul
  let ⟨haddType⟩ ← checkBinaryType L F hints L.add
  let ⟨hmulType⟩ ← checkBinaryType L F hints L.mul
  let ⟨hadd⟩ ← checkAddEqs L F hints L.add
  let ⟨hmul⟩ ← checkMulEqs L F hints L.mul
  let ⟨hzero⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.pow (.fvar 0) (.zero L)) (.succ L (.zero L))
  let ⟨hsucc⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.pow (.fvar 0) (.succ L (.fvar 1)))
    (.op₂ L.mul (.op₂ L.pow (.fvar 0) (.fvar 1)) (.fvar 0))
  pure ⟨{ natBound := hnat, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηOp =>
            have ⟨_, hηAdd⟩ := haddHead hE
            have ⟨_, hηMul⟩ := hmulHead hE
            Literals.pow_natLit num₁ num₂
              (hmulType hE ho htr hη hηMul)
              (haddType hE ho htr hη hηAdd)
              (hadd hE ho htr hη hηAdd)
              (hmul hE ho htr hη hηAdd hηMul)
              { zero := fun _x hx =>
                  (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hzero
                    (.natType hη) (.op hηOp .varX (.zero hη)) (.succ hη (.zero hη))
                succ := fun _x _y hx hy =>
                  (NatAt.mk hE ho htr hη hx hy).eq hsucc
                    (.natType hη) (.op hηOp .varX (.succ hη .varY))
                    (.op hηMul (.op hηOp .varX .varY) .varX) } }⟩

def verifyBeq : Except Failure (PLift (BoolOpSpec L F L.beq Nat.beq)) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hbool⟩ ← bound F L.bool
  let ⟨hsig⟩ ← boolSig L F
  let ⟨hop⟩ ← bound F L.beq
  let ⟨hzeroZero⟩ ← natDefEq L F hints (.bool L)
    (.op₂ L.beq (.zero L) (.zero L)) (FExpr.boolLit L true)
  let ⟨hzeroSucc⟩ ← natDefEq L F hints (.bool L)
    (.op₂ L.beq (.zero L) (.succ L (.fvar 1))) (FExpr.boolLit L false)
  let ⟨hsuccZero⟩ ← natDefEq L F hints (.bool L)
    (.op₂ L.beq (.succ L (.fvar 0)) (.zero L)) (FExpr.boolLit L false)
  let ⟨hsuccSucc⟩ ← natDefEq L F hints (.bool L)
    (.op₂ L.beq (.succ L (.fvar 0)) (.succ L (.fvar 1)))
    (.op₂ L.beq (.fvar 0) (.fvar 1))
  pure ⟨{ natBound := hnat, boolBound := hbool, boolSig := hsig, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηBool hηOp =>
            Literals.beq_natLit
              { zeroZero :=
                  (NatAt.mk hE ho htr hη Literals.natZeroTyped Literals.natZeroTyped).eq hzeroZero
                    (.boolType hηBool) (.op hηOp (.zero hη) (.zero hη)) (.boolLit hηBool true)
                zeroSucc := fun _y hy =>
                  (NatAt.mk hE ho htr hη Literals.natZeroTyped hy).eq hzeroSucc
                    (.boolType hηBool) (.op hηOp (.zero hη) (.succ hη .varY))
                    (.boolLit hηBool false)
                succZero := fun _x hx =>
                  (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hsuccZero
                    (.boolType hηBool) (.op hηOp (.succ hη .varX) (.zero hη))
                    (.boolLit hηBool false)
                succSucc := fun _x _y hx hy =>
                  (NatAt.mk hE ho htr hη hx hy).eq hsuccSucc
                    (.boolType hηBool) (.op hηOp (.succ hη .varX) (.succ hη .varY))
                    (.op hηOp .varX .varY) }
              num₁ num₂ }⟩

def verifyBle : Except Failure (PLift (BoolOpSpec L F L.ble Nat.ble)) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hbool⟩ ← bound F L.bool
  let ⟨hsig⟩ ← boolSig L F
  let ⟨hop⟩ ← bound F L.ble
  let ⟨hzero⟩ ← natDefEq L F hints (.bool L)
    (.op₂ L.ble (.zero L) (.fvar 1)) (FExpr.boolLit L true)
  let ⟨hsuccZero⟩ ← natDefEq L F hints (.bool L)
    (.op₂ L.ble (.succ L (.fvar 0)) (.zero L)) (FExpr.boolLit L false)
  let ⟨hsuccSucc⟩ ← natDefEq L F hints (.bool L)
    (.op₂ L.ble (.succ L (.fvar 0)) (.succ L (.fvar 1)))
    (.op₂ L.ble (.fvar 0) (.fvar 1))
  pure ⟨{ natBound := hnat, boolBound := hbool, boolSig := hsig, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηBool hηOp =>
            Literals.ble_natLit
              { zero := fun _y hy =>
                  (NatAt.mk hE ho htr hη Literals.natZeroTyped hy).eq hzero
                    (.boolType hηBool) (.op hηOp (.zero hη) .varY) (.boolLit hηBool true)
                succZero := fun _x hx =>
                  (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hsuccZero
                    (.boolType hηBool) (.op hηOp (.succ hη .varX) (.zero hη))
                    (.boolLit hηBool false)
                succSucc := fun _x _y hx hy =>
                  (NatAt.mk hE ho htr hη hx hy).eq hsuccSucc
                    (.boolType hηBool) (.op hηOp (.succ hη .varX) (.succ hη .varY))
                    (.op hηOp .varX .varY) }
              num₁ num₂ }⟩

def verifyShiftLeft : Except Failure (PLift (NatOpSpec L F L.shiftLeft (· <<< ·))) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hop⟩ ← bound F L.shiftLeft
  let ⟨haddHead⟩ ← constHead L F L.add
  let ⟨hmulHead⟩ ← constHead L F L.mul
  let ⟨htype⟩ ← checkBinaryType L F hints L.shiftLeft
  let ⟨haddType⟩ ← checkBinaryType L F hints L.add
  let ⟨hadd⟩ ← checkAddEqs L F hints L.add
  let ⟨hmul⟩ ← checkMulEqs L F hints L.mul
  let ⟨hzero⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.shiftLeft (.fvar 0) (.zero L)) (.fvar 0)
  let ⟨hsucc⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.shiftLeft (.fvar 0) (.succ L (.fvar 1)))
    (.op₂ L.shiftLeft (.op₂ L.mul (.natLit 2) (.fvar 0)) (.fvar 1))
  pure ⟨{ natBound := hnat, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηOp =>
            have ⟨_, hηAdd⟩ := haddHead hE
            have ⟨_, hηMul⟩ := hmulHead hE
            Literals.shiftLeft_natLit num₁ num₂
              (htype hE ho htr hη hηOp)
              (haddType hE ho htr hη hηAdd)
              (hadd hE ho htr hη hηAdd)
              (hmul hE ho htr hη hηAdd hηMul)
              { zero := fun _x hx =>
                  (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hzero
                    (.natType hη) (.op hηOp .varX (.zero hη)) .varX
                succ := fun _x _y hx hy =>
                  (NatAt.mk hE ho htr hη hx hy).eq hsucc
                    (.natType hη) (.op hηOp .varX (.succ hη .varY))
                    (.op hηOp (.op hηMul (.natLit hη 2) .varX) .varY) } }⟩

def verifyShiftRight (hdiv : NatOpSpec L F L.div (· / ·)) :
    Except Failure (PLift (NatOpSpec L F L.shiftRight (· >>> ·))) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hop⟩ ← bound F L.shiftRight
  let ⟨hdivHead⟩ ← constHead L F L.div
  let ⟨hdivType⟩ ← checkBinaryType L F hints L.div
  let ⟨hzero⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.shiftRight (.fvar 0) (.zero L)) (.fvar 0)
  let ⟨hsucc⟩ ← natDefEq L F hints (.nat L)
    (.op₂ L.shiftRight (.fvar 0) (.succ L (.fvar 1)))
    (.op₂ L.div (.op₂ L.shiftRight (.fvar 0) (.fvar 1)) (.natLit 2))
  pure ⟨{ natBound := hnat, opBound := hop
          eq := fun num₁ num₂ hE ho htr hη hηOp =>
            have ⟨_, hηDiv⟩ := hdivHead hE
            Literals.shiftRight_natLit num₁ num₂
              (hdivType hE ho htr hη hηDiv)
              (fun num₃ num₄ => hdiv.eq num₃ num₄ hE ho htr hη hηDiv)
              { zero := fun _x hx =>
                  (NatAt.mk hE ho htr hη hx Literals.natZeroTyped).eq hzero
                    (.natType hη) (.op hηOp .varX (.zero hη)) .varX
                succ := fun _x _y hx hy =>
                  (NatAt.mk hE ho htr hη hx hy).eq hsucc
                    (.natType hη) (.op hηOp .varX (.succ hη .varY))
                    (.op hηDiv (.op hηOp .varX .varY) (.natLit hη 2)) } }⟩

def trustOp (pos : Nat) (f : Nat → Nat → Nat)
    (ax : ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄, L.NatAxioms E → L.NatAxiom E pos f) :
    Except Failure (PLift (NatOpSpec L F pos f)) := do
  let ⟨hnat⟩ ← bound F L.nat
  let ⟨hop⟩ ← bound F pos
  pure ⟨.ofAxiom hnat hop ax⟩

def verifyAccel (accel : Accel L F) : Accel L F :=
  let div := accel.div <|> (trustOp L F L.div _ fun _ _ h => h.div).toOption
  { add := accel.add <|> (verifyAdd L F hints).toOption
    sub := accel.sub <|> (verifySub L F hints).toOption
    mul := accel.mul <|> (verifyMul L F hints).toOption
    pow := accel.pow <|> (verifyPow L F hints).toOption
    beq := accel.beq <|> (verifyBeq L F hints).toOption
    ble := accel.ble <|> (verifyBle L F hints).toOption
    div
    mod := accel.mod <|> (trustOp L F L.mod _ fun _ _ h => h.mod).toOption
    gcd := accel.gcd <|> (trustOp L F L.gcd _ fun _ _ h => h.gcd).toOption
    land := accel.land <|> (trustOp L F L.land _ fun _ _ h => h.land).toOption
    lor := accel.lor <|> (trustOp L F L.lor _ fun _ _ h => h.lor).toOption
    xor := accel.xor <|> (trustOp L F L.xor _ fun _ _ h => h.xor).toOption
    shiftLeft := accel.shiftLeft <|> (verifyShiftLeft L F hints).toOption
    shiftRight := accel.shiftRight <|>
      div.bind fun ⟨h⟩ => (verifyShiftRight L F hints h).toOption }

end Metalean.FastChecker
