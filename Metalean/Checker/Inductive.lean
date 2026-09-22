/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Infer
public import Metalean.Syntax.Inductive.Pre
import Metalean.Typing.Env

@[expose] public section

namespace Metalean.Checker

open Frontend (Failure)

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {ι : IndSig}

def checkTele (hE : EnvWF E) {P : Level ℓ → Prop} [DecidablePred P]
    (hΓ : E[Γ] ⊢ ok) {m : Nat} :
    (Δ : Ctx ζ ℓ n m) → Except Failure (PLift (TeleWF E P Γ Δ))
  | .nil => pure ⟨.nil⟩
  | .snoc Δ t => do
    let ⟨hΔ⟩ ← checkTele hE hΓ Δ
    let ⟨l, ht⟩ ← checkIsType hE (hΔ.appendCtxWF hΓ) t
    let ⟨hP⟩ ← guardProofOr (P l) (.reject .fieldLevel)
    pure ⟨.snoc hΔ ⟨l, hP, ht⟩⟩

def checkCtx (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {m : Nat} (Δ : Ctx ζ ℓ n m) :
    Except Failure (PLift (E[Γ ++ Δ] ⊢ ok)) := do
  let ⟨h⟩ ← checkTele (P := fun _ => True) hE hΓ Δ
  pure ⟨h.appendCtxWF hΓ⟩

def checkIdx (hE : EnvWF E) (I : Inductive ζ ι) {m : Nat}
    {Δ : Ctx ζ ι.nlevels 0 m} (hΔ : E[Δ] ⊢ ok) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ι.nlevels)
    (ps : Fin ι.nparams → Expr ζ ι.nlevels m)
    (is : Fin (ι.nindices s) → Expr ζ ι.nlevels m) :
    Except Failure (PLift (I.IdxWF E Δ s ls ps is)) := do
  let ⟨h⟩ ← Fin.sequenceM fun index =>
    checkAgainst hE hΔ (is index) (I.indexType ls s ps is index)
  pure ⟨h⟩

def checkRecField (hE : EnvWF E) (I : Inductive ζ ι) {s : Fin ι.nsorts}
    {csig : CtorSig ι.nsorts} (ctor : Ctor ζ ι s csig)
    (hΓo : E[I.params ++ ctor.ordinaryTele] ⊢ ok) (f : Fin csig.nrecFields) :
    Except Failure (PLift (RecFieldWF E I (I.params ++ ctor.ordinaryTele) (ctor.recursive f))) := do
  let fd := ctor.recursive f
  let ⟨htele⟩ ← checkTele (P := I.LevelOK) hE hΓo fd.tele
  let ⟨hΓt⟩ ← checkCtx hE hΓo fd.tele
  let ⟨hidx⟩ ← checkIdx hE I hΓt (csig.recursiveTarget f) Level.param
    (fun param => .var ⟨param.val, param.isLt.trans_le
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))⟩) fd.indices
  pure ⟨htele, hidx⟩

def checkOrdField (hE : EnvWF E) (I : Inductive ζ ι) (hΓp : E[I.params] ⊢ ok)
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (f : Fin (ι.ctors s c).nfields)
    (hle : f.val ≤ (ι.ctors s c).nfields) :
    Except Failure (PLift (FieldWF E I
      (I.params ++ (I.ctors s c).ordinaryTeleAux f.val hle)
      ((I.ctors s c).ordinary f))) := do
  let ⟨hΓf⟩ ← checkCtx hE hΓp ((I.ctors s c).ordinaryTeleAux f.val hle)
  let ⟨ht⟩ ← checkAgainst hE hΓf (((I.ctors s c).ordinary f).type)
    (.sort ((I.ctors s c).ordinary f).level)
  let ⟨hOK⟩ ← guardProofOr (I.LevelOK ((I.ctors s c).ordinary f).level) (.reject .fieldLevel)
  pure ⟨⟨ht, hOK⟩⟩

def checkCtorDecl (hE : EnvWF E) (I : Inductive ζ ι)
    (hΓp : E[I.params] ⊢ ok) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Except Failure (PLift (CtorWF E I (I.ctors s c))) := do
  let ⟨hord⟩ ← Fin.sequenceM fun f =>
    checkOrdField hE I hΓp f (Nat.le_of_lt f.isLt)
  let ⟨hΓo⟩ ← checkCtx hE hΓp (I.ctors s c).ordinaryTele
  let ⟨hrec⟩ ← Fin.sequenceM fun f => checkRecField hE I (I.ctors s c) hΓo f
  let ⟨hidx⟩ ← checkIdx hE I hΓo s Level.param
    (fun param => .var ⟨param.val, param.isLt.trans_le (Nat.le_add_right _ _)⟩)
    (I.ctors s c).targetIndices
  pure ⟨hord, hrec, hidx⟩

def checkInductive (hE : EnvWF E) (I : Inductive ζ ι) :
    Except Failure (PLift (InductiveWF E I)) := do
  let ⟨hparams⟩ ← checkTele (P := fun _ => True) hE (Γ := .nil)
    Tele.Forall.nil I.params
  have hΓp : E[I.params] ⊢ ok := by
    simpa using hparams.appendCtxWF .nil
  let ⟨hindices⟩ ← Fin.sequenceM fun s =>
    checkTele (P := fun _ => True) hE hΓp (I.indices s)
  let ⟨hctors⟩ ← Fin.sequenceM fun s =>
    Fin.sequenceM fun c => checkCtorDecl hE I hΓp s c
  pure ⟨hparams, hindices, hctors⟩

def checkInductiveEntry (hE : EnvWF E) (I : Inductive ζ ι) :
    Except Failure (PLift (EntryWF E (.inductive I))) := do
  let ⟨hwf⟩ ← checkInductive hE I
  pure ⟨.inductive hwf⟩

def inferOrdLevels (hE : EnvWF E) (pre : PreInductive ζ ι) :
    Except Failure ((s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
      Fin (ι.ctors s c).nfields → Level ι.nlevels) := do
  let ⟨hparams⟩ ← checkTele (P := fun _ => True) hE (Γ := .nil) Tele.Forall.nil pre.params
  have hΓp : E[pre.params] ⊢ ok := by
    simpa using hparams.appendCtxWF .nil
  Fin.mapM fun s => Fin.mapM fun c => Fin.mapM fun f => do
    let ⟨hΓf⟩ ← checkCtx hE hΓp ((pre.ctors s c).ordinaryTeleAux f.val (Nat.le_of_lt f.isLt))
    let ⟨l, _⟩ ← checkIsType hE hΓf ((pre.ctors s c).ordinary f)
    pure l

def checkPreInductive (hE : EnvWF E) (pre : PreInductive ζ ι) :
    Except Failure ((levels : (s : Fin ι.nsorts) → (c : Fin (ι.nctors s)) →
        Fin (ι.ctors s c).nfields → Level ι.nlevels) ×'
      PLift (EntryWF E (.inductive (pre.withLevels levels)))) := do
  let levels ← inferOrdLevels hE pre
  let hwf ← checkInductiveEntry hE (pre.withLevels levels)
  pure ⟨levels, hwf⟩

end Metalean.Checker
