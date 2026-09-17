/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Recursor

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ₁ ζ₂ : Sigs} {ℓ ℓ' n nfields arity : Nat}
  {ι : IndSig} {s target : Fin ι.nsorts} {csig : CtorSig ι.nsorts}

variable (recFd : RecField ζ₁ ι nfields arity target)
  (ctor : Ctor ζ₁ ι s csig)
  (I : Inductive ζ₁ ι)
  (pre : ζ₁ ⟶ ζ₂)
  (η : Head ζ₁ (.inductive ι))
  (ls : Fin ι.nlevels → Level ℓ)
  (l : Level ℓ)
  (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
  (ms : Fin ι.nsorts → Expr ζ₁ ℓ n)
  (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₁ ℓ n)
  (fieldSubst : Subst ζ₁ ℓ (ι.nparams + nfields) n)
  (r : Expr ζ₁ ℓ n)
  (levelSubst : Param ℓ → Level ℓ')

namespace RecField

def iotaIH : Expr ζ₁ ℓ n :=
  Ctx.lam
    (.recr η target ls l
      (fun i => (ps i).wkN arity)
      (fun s => (ms s).wkN arity)
      (fun s c => (mins s c).wkN arity)
      (recFd.instantiatedIndices ls fieldSubst) (r.applyBound arity))
    (recFd.instantiatedTelescope ls fieldSubst)

@[simp] theorem iotaIH_map :
    (recFd.iotaIH η ls l ps ms mins fieldSubst r).map pre =
      (recFd.map pre).iotaIH (η.map pre) ls l
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre)
        (fun s ctor => (mins s ctor).map pre)
        (fieldSubst.map pre) (r.map pre) := by
  refine (Ctx.map_lam pre _ _).trans
    (congrArg₂ Ctx.lam ?_
      (instantiatedTelescope_map pre recFd ls fieldSubst))
  simp [instantiatedIndices, Expr.map]
  rfl

@[simp] theorem iotaIH_instL :
    (recFd.iotaIH η ls l ps ms mins fieldSubst r).instL levelSubst =
      recFd.iotaIH η (fun i => (ls i).inst levelSubst) (l.inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst)
        (fun s ctor => (mins s ctor).instL levelSubst)
        (Subst.instL levelSubst fieldSubst) (r.instL levelSubst) := by
  simp! [iotaIH]

end RecField

namespace Ctor

def iotaIH
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (recFds : Fin csig.nrecFields → Expr ζ₁ ℓ n)
    (f : Fin csig.nrecFields) : Expr ζ₁ ℓ n :=
  (ctor.recursive f).iotaIH η ls l
    ps ms mins (Fin.append ps fds) (recFds f)

@[simp] theorem iotaIH_map
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (recFds : Fin csig.nrecFields → Expr ζ₁ ℓ n)
    (f : Fin csig.nrecFields) :
    (ctor.iotaIH η ls l ps ms mins fds recFds f).map pre =
      (ctor.map pre).iotaIH (η.map pre) ls l
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre)
        (fun s c => (mins s c).map pre)
        (fun i => (fds i).map pre)
        (fun i => (recFds i).map pre) f := by
  simp [iotaIH, map]

@[simp] theorem iotaIH_instL
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (recFds : Fin csig.nrecFields → Expr ζ₁ ℓ n)
    (f : Fin csig.nrecFields) (levelSubst : Param ℓ → Level ℓ') :
    (ctor.iotaIH η ls l ps ms mins fds recFds f).instL levelSubst =
      ctor.iotaIH η (fun i => (ls i).inst levelSubst) (l.inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst)
        (fun s c => (mins s c).instL levelSubst)
        (fun i => (fds i).instL levelSubst)
        (fun i => (recFds i).instL levelSubst) f := by
  simp [iotaIH]

end Ctor

namespace Inductive

def iotaIHs
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) :
    Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n :=
  fun f => (I.ctors s c).iotaIH η ls l ps ms mins
    fds recFds f

theorem iotaIHs_map
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) :
    (fun f => (I.iotaIHs η ls l ps ms mins s c
      fds recFds f).map pre) =
      (I.map pre).iotaIHs (η.map pre) ls l
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre)
        (fun s c => (mins s c).map pre) s c
        (fun i => (fds i).map pre)
        fun i => (recFds i).map pre :=
  funext <| Ctor.iotaIH_map _ pre η ls l ps ms mins
    fds recFds

@[simp] theorem iotaIHs_instL
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n)
    (f : Fin (ι.ctors s c).nrecFields)
    (levelSubst : Param ℓ → Level ℓ') :
    (I.iotaIHs η ls l ps ms mins s c fds recFds f).instL levelSubst =
      I.iotaIHs η (fun i => (ls i).inst levelSubst) (l.inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst)
        (fun s c => (mins s c).instL levelSubst) s c
        (fun i => (fds i).instL levelSubst)
        (fun i => (recFds i).instL levelSubst) f := by
  simp [iotaIHs]

def iotaLhs
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  .recr η s ls l ps ms mins
    (fun index => (I.ctors s c).targetIndex ls ps fds index)
    (.ctor η s c ls ps fds recFds)

@[simp] theorem iotaLhs_map
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) :
    (I.iotaLhs η ls l ps ms mins s c fds recFds).map pre =
      (I.map pre).iotaLhs (η.map pre) ls l
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre)
        (fun s c => (mins s c).map pre) s c
        (fun i => (fds i).map pre)
        fun i => (recFds i).map pre := by
  simp! [iotaLhs, map]

@[simp] theorem iotaLhs_instL
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n)
    (levelSubst : Param ℓ → Level ℓ') :
    (I.iotaLhs η ls l ps ms mins s c fds recFds).instL levelSubst =
      I.iotaLhs η (fun i => (ls i).inst levelSubst) (l.inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst)
        (fun s c => (mins s c).instL levelSubst) s c
        (fun i => (fds i).instL levelSubst)
        fun i => (recFds i).instL levelSubst := by
  simp! [iotaLhs]

def iotaRhs
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  (mins s c).apps fds
    |>.apps recFds
    |>.apps (I.iotaIHs η ls l ps ms mins s c fds recFds)

@[simp] theorem iotaRhs_map
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) :
    (I.iotaRhs η ls l ps ms mins s c fds recFds).map pre =
      (I.map pre).iotaRhs (η.map pre) ls l
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre)
        (fun s c => (mins s c).map pre) s c
        (fun i => (fds i).map pre)
        fun i => (recFds i).map pre := by
  simp [iotaRhs, iotaIHs_map I pre η ls l ps ms mins s c
    fds recFds]

@[simp] theorem iotaRhs_instL
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n)
    (levelSubst : Param ℓ → Level ℓ') :
    (I.iotaRhs η ls l ps ms mins s c fds recFds).instL levelSubst =
      I.iotaRhs η (fun i => (ls i).inst levelSubst) (l.inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst)
        (fun s c => (mins s c).instL levelSubst) s c
        (fun i => (fds i).instL levelSubst)
        fun i => (recFds i).instL levelSubst := by
  simp [iotaRhs, iotaIHs_instL I η ls l ps ms mins s c
    fds recFds]

def iotaType
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  motiveResult (ms s) (fun index => (I.ctors s c).targetIndex ls ps fds index)
    (.ctor η s c ls ps fds recFds)

@[simp] theorem iotaType_map
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n) :
    (I.iotaType η ls ps ms s c fds recFds).map pre =
      (I.map pre).iotaType (η.map pre) ls
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre) s c
        (fun i => (fds i).map pre)
        fun i => (recFds i).map pre := by
  simp [iotaType, map, Expr.map]

@[simp] theorem iotaType_instL
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ₁ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₁ ℓ n)
    (levelSubst : Param ℓ → Level ℓ') :
    (I.iotaType η ls ps ms s c fds recFds).instL levelSubst =
      I.iotaType η (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst) s c
        (fun i => (fds i).instL levelSubst)
        fun i => (recFds i).instL levelSubst := by
  simp [iotaType, Expr.instL]

end Inductive

end Metalean
