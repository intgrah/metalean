/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Ctor

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ₁ ζ₂ : Sigs} {ℓ ℓ' n nfields nsorts arity k : Nat}
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
  (fieldSubst : Subst ζ₁ ℓ (ι.nparams + nfields) n)
  (r : Expr ζ₁ ℓ n)
  (levelSubst : Param ℓ → Level ℓ')

namespace Inductive

def motiveResult (motive : Expr ζ₁ ℓ n)
    (is : Fin k → Expr ζ₁ ℓ n) (maj : Expr ζ₁ ℓ n) : Expr ζ₁ ℓ n :=
  .app (motive.apps is) maj

@[simp] theorem motiveResult_map
    (motive : Expr ζ₁ ℓ n) (is : Fin k → Expr ζ₁ ℓ n)
    (maj : Expr ζ₁ ℓ n) :
    (motiveResult motive is maj).map pre =
      motiveResult (motive.map pre)
        (fun i => (is i).map pre) (maj.map pre) :=
  congrArg (Expr.app · (maj.map pre))
    ((Expr.appHom.finFold k).naturality_apply pre ⟨motive, is⟩).symm

attribute [local instance] Level.category in
@[simp] theorem motiveResult_instL
    (motive : Expr ζ₁ ℓ n)
    (is : Fin k → Expr ζ₁ ℓ n) (maj : Expr ζ₁ ℓ n)
    (levelSubst : Param ℓ → Level ℓ') :
    (motiveResult motive is maj).instL levelSubst =
      motiveResult (motive.instL levelSubst) (fun i => (is i).instL levelSubst)
        (maj.instL levelSubst) :=
  congrArg (Expr.app · (maj.instL levelSubst))
    ((Expr.appLevelHom.finFold k).naturality_apply levelSubst ⟨motive, is⟩).symm

end Inductive

namespace RecField

/-- Induction hypothesis for a recursive field BEFORE earlier binders weaken it -/
def ihType : Expr ζ₁ ℓ n :=
  (recFd.instantiatedTelescope ls fieldSubst).pi
    (Inductive.motiveResult ((ms target).wkN arity)
      (recFd.instantiatedIndices ls fieldSubst) (r.applyBound arity))

@[simp] theorem ihType_map :
    (recFd.ihType ls ms fieldSubst r).map pre =
      (recFd.map pre).ihType ls
        (fun s => (ms s).map pre)
        (fieldSubst.map pre) (r.map pre) := by
  refine (Ctx.map_pi pre _ _).trans (congrArg₂ Ctx.pi ?_ ?_)
  · simp [instantiatedIndices]
    rfl
  · exact instantiatedTelescope_map pre recFd ls fieldSubst

@[simp] theorem ihType_instL :
    (recFd.ihType ls ms fieldSubst r).instL levelSubst =
      recFd.ihType (fun i => (ls i).inst levelSubst)
        (fun s => (ms s).instL levelSubst)
        (Subst.instL levelSubst fieldSubst) (r.instL levelSubst) := by
  unfold ihType instantiatedTelescope instantiatedIndices
  simp

end RecField

namespace Ctor

def ihTypeWith
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (recFds : Fin csig.nrecFields → Expr ζ₁ ℓ n)
    (f : Fin csig.nrecFields) : Expr ζ₁ ℓ n :=
  (ctor.recursive f).ihType ls ms (Fin.append ps fds) (recFds f)

def ihType
    (f : Fin csig.nrecFields) :
    Expr ζ₁ ℓ (n + csig.nfields + csig.nrecFields) :=
  ctor.ihTypeWith ls
    (fun s => ((ms s).wkN csig.nfields).wkN csig.nrecFields)
    (csig.fieldParams ps) csig.fieldOrdinary csig.fieldRecursive f

@[simp] theorem ihType_map
    (f : Fin csig.nrecFields) :
    (ctor.ihType ls ps ms f).map pre =
      (ctor.map pre).ihType ls
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre) f := by
  simp [ihType, ihTypeWith, map]

@[simp] theorem ihType_instL
    (f : Fin csig.nrecFields) (levelSubst : Param ℓ → Level ℓ') :
    (ctor.ihType ls ps ms f).instL levelSubst =
      ctor.ihType (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst) f := by
  simp [ihType, ihTypeWith]

def ihTeleAux (count : Nat) (hcount : count ≤ csig.nrecFields) :
    Ctx ζ₁ ℓ (n + csig.nfields + csig.nrecFields)
      (n + csig.nfields + csig.nrecFields + count) :=
  Ctx.ofTypes fun f : Fin count => ctor.ihType ls ps ms (f.castLE hcount)

def ihTele :
    Ctx ζ₁ ℓ (n + csig.nfields + csig.nrecFields)
      (n + csig.nfields + csig.nrecFields + csig.nrecFields) :=
  ihTeleAux ctor ls ps ms csig.nrecFields le_rfl

@[simp] theorem ihTeleAux_map
    (count : Nat) (hcount : count ≤ csig.nrecFields) :
    (ctor.ihTeleAux ls ps ms count hcount).map pre =
      (ctor.map pre).ihTeleAux ls
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre) count hcount := by
  refine (Ctx.ofTypes_map _ pre).trans ?_
  simp [ihTeleAux]

@[simp] theorem ihTele_map :
    (ctor.ihTele ls ps ms).map pre =
      (ctor.map pre).ihTele ls
        (fun i => (ps i).map pre)
        fun s => (ms s).map pre :=
  ctor.ihTeleAux_map pre ls ps ms _ _

@[simp] theorem ihTeleAux_instL
    (count : Nat) (hcount : count ≤ csig.nrecFields)
    (levelSubst : Param ℓ → Level ℓ') :
    (ctor.ihTeleAux ls ps ms count hcount).instL levelSubst =
      ctor.ihTeleAux (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst) count hcount := by
  simp [ihTeleAux]

@[simp] theorem ihTele_instL :
    (ctor.ihTele ls ps ms).instL levelSubst =
      ctor.ihTele (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        fun s => (ms s).instL levelSubst :=
  ctor.ihTeleAux_instL ls ps ms _ _ levelSubst

end Ctor

namespace Inductive

def motiveTele (s : Fin ι.nsorts) :
    Ctx ζ₁ ℓ n (n + ι.nindices s + 1) :=
  (I.indexTele ls s ps).snoc
    (.ind η s ls (fun i => (ps i).wkN (ι.nindices s))
      fun index => .var ⟨n + index.val, by omega⟩)

def motiveType (l : Level ℓ)
    (s : Fin ι.nsorts) : Expr ζ₁ ℓ n :=
  (I.motiveTele η ls ps s).pi (.sort l)

@[simp] theorem motiveTele_instL
    (s : Fin ι.nsorts) (levelSubst : Param ℓ → Level ℓ') :
    (I.motiveTele η ls ps s).instL levelSubst =
      I.motiveTele η (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst) s := by
  unfold motiveTele
  change ((I.indexTele ls s ps).instL levelSubst).snoc
      ((Expr.ind η s ls (fun i => (ps i).wkN (ι.nindices s))
        fun index => Expr.var ⟨n + index.val, by omega⟩).instL levelSubst) = _
  simp!

@[simp] theorem motiveType_instL
    (l : Level ℓ) (s : Fin ι.nsorts) (levelSubst : Param ℓ → Level ℓ') :
    (I.motiveType η ls ps l s).instL levelSubst =
      I.motiveType η (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst) (l.inst levelSubst) s := by
  simp! [motiveType]

@[simp] theorem motiveTele_map (s : Fin ι.nsorts) :
    (I.motiveTele η ls ps s).map pre =
      (I.map pre).motiveTele (η.map pre) ls
        (fun i => (ps i).map pre) s := by
  simp! [motiveTele]

@[simp] theorem motiveType_map (l : Level ℓ) (s : Fin ι.nsorts) :
    (I.motiveType η ls ps l s).map pre =
      (I.map pre).motiveType (η.map pre) ls (fun i => (ps i).map pre) l s := by
  simp! [motiveType]

def caseTele (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Ctx ζ₁ ℓ n (n + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields + (ι.ctors s c).nrecFields) :=
  let C := I.ctors s c
  C.fieldTele η ls ps ++ C.ihTele ls ps ms

@[simp] theorem caseTele_map (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.caseTele η ls ps ms s c).map pre =
      (I.map pre).caseTele (η.map pre) ls
        (fun i => (ps i).map pre) (fun s => (ms s).map pre) s c :=
  (Ctx.map_append pre _ _).trans
    congr(Tele.append
      $(Ctor.fieldTele_map _ pre η ls ps)
      $(Ctor.ihTele_map _ pre ls ps ms))

@[simp] theorem caseTele_instL (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (levelSubst : Param ℓ → Level ℓ') :
    (I.caseTele η ls ps ms s c).instL levelSubst =
      I.caseTele η (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst) s c := by
  simp [caseTele]

end Inductive

namespace CtorSig

def caseParams {ι : IndSig} (csig : CtorSig ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n) :
    Fin ι.nparams →
      Expr ζ₁ ℓ (n + csig.nfields + csig.nrecFields + csig.nrecFields) :=
  fun i => (csig.fieldParams ps i).wkN csig.nrecFields

def caseOrdinary (csig : CtorSig nsorts) :
    Fin csig.nfields → Expr ζ₁ ℓ (n + csig.nfields + csig.nrecFields + csig.nrecFields) :=
  fun f => (csig.fieldOrdinary f).wkN csig.nrecFields

def caseRecursive (csig : CtorSig nsorts) :
    Fin csig.nrecFields → Expr ζ₁ ℓ (n + csig.nfields + csig.nrecFields + csig.nrecFields) :=
  fun f => (csig.fieldRecursive f).wkN csig.nrecFields

@[simp] theorem caseParams_map {ι : IndSig} (csig : CtorSig ι.nsorts)
    (pre : ζ₁ ⟶ ζ₂) (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (i : Fin ι.nparams) :
    (csig.caseParams ps i).map pre =
      csig.caseParams (fun i => (ps i).map pre) i := by
  simp [caseParams]

@[simp] theorem caseOrdinary_map (csig : CtorSig nsorts)
    (pre : ζ₁ ⟶ ζ₂) (i : Fin csig.nfields) :
    (csig.caseOrdinary (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).map pre =
      csig.caseOrdinary i := by
  simp [caseOrdinary]

@[simp] theorem caseRecursive_map (csig : CtorSig nsorts)
    (pre : ζ₁ ⟶ ζ₂) (i : Fin csig.nrecFields) :
    (csig.caseRecursive (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).map pre =
      csig.caseRecursive i := by
  simp [caseRecursive]

@[simp] theorem caseParams_instL {ι : IndSig} (csig : CtorSig ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n) (levelSubst : Param ℓ → Level ℓ')
    (i : Fin ι.nparams) :
    (csig.caseParams ps i).instL levelSubst =
      csig.caseParams (fun i => (ps i).instL levelSubst) i := by
  simp [caseParams]

@[simp] theorem caseOrdinary_instL (csig : CtorSig nsorts)
    (levelSubst : Param ℓ → Level ℓ') (i : Fin csig.nfields) :
    (csig.caseOrdinary (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).instL levelSubst =
      csig.caseOrdinary i := by
  simp [caseOrdinary]

@[simp] theorem caseRecursive_instL (csig : CtorSig nsorts)
    (levelSubst : Param ℓ → Level ℓ') (i : Fin csig.nrecFields) :
    (csig.caseRecursive (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).instL levelSubst =
      csig.caseRecursive i := by
  simp [caseRecursive]

end CtorSig

namespace Inductive

def caseType (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    Expr ζ₁ ℓ (n + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields + (ι.ctors s c).nrecFields) :=
  letI csig := ι.ctors s c
  motiveResult
    ((((ms s).wkN csig.nfields).wkN csig.nrecFields).wkN csig.nrecFields)
    (fun i => (I.ctors s c).targetIndex ls (csig.caseParams ps) csig.caseOrdinary i)
    (.ctor η s c ls (csig.caseParams ps) csig.caseOrdinary csig.caseRecursive)

@[simp] theorem caseType_map
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.caseType η ls ps ms s c).map pre =
      (I.map pre).caseType (η.map pre) ls
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre) s c := by
  simp [caseType]
  congr 2
  simp!

@[simp] theorem caseType_instL
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (levelSubst : Param ℓ → Level ℓ') :
    (I.caseType η ls ps ms s c).instL levelSubst =
      I.caseType η (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst) s c := by
  simp! [caseType]

def caseFnType (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) : Expr ζ₁ ℓ n :=
  (I.caseTele η ls ps ms s c).pi (I.caseType η ls ps ms s c)

@[simp] theorem caseFnType_map
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (I.caseFnType η ls ps ms s c).map pre =
      (I.map pre).caseFnType (η.map pre) ls
        (fun i => (ps i).map pre)
        (fun s => (ms s).map pre) s c :=
  (Ctx.map_pi pre _ _).trans
    (congrArg₂ Ctx.pi (I.caseType_map pre η ls ps ms s c)
      (I.caseTele_map pre η ls ps ms s c))

@[simp] theorem caseFnType_instL (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (levelSubst : Param ℓ → Level ℓ') :
    (I.caseFnType η ls ps ms s c).instL levelSubst =
      I.caseFnType η (fun i => (ls i).inst levelSubst)
        (fun i => (ps i).instL levelSubst)
        (fun s => (ms s).instL levelSubst) s c := by
  simp [caseFnType]

def motiveBinders : Ctx ζ₁ ℓ ι.nparams (ι.nparams + ι.nsorts) :=
  Ctx.ofTypes (I.motiveType η ls Expr.var l)

def caseBinders :
    Ctx ζ₁ ℓ (ι.nparams + ι.nsorts)
      (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
  Ctx.ofTypes fun tag =>
    let ⟨s, c⟩ := Fin.decodeSigma ι.nctors tag
    I.caseFnType η ls
      (fun param => Expr.var (param.castAdd ι.nsorts))
      (fun s => Expr.var (Fin.natAdd ι.nparams s)) s c

def recrTele (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) :
    Ctx ζ₁ ℓ 0 (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) :=
  letI casesEnd := ι.nparams + ι.nsorts + Fin.sum ι.nctors
  let ps : Fin ι.nparams → Expr ζ₁ ℓ casesEnd :=
    fun param => .var (param.castLE (by omega))
  let maj := Expr.ind η s ls
    (fun param => (ps param).wkN (ι.nindices s))
    fun index : Fin (ι.nindices s) =>
      .var ⟨casesEnd + index.val, by omega⟩
  I.params.instL ls ++
    I.motiveBinders η ls l ++
    I.caseBinders η ls ++
    I.indexTele ls s ps |>.snoc
    maj

@[simp] private theorem motiveBinders_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) :
    (I.motiveBinders η ls l).map pre =
      (I.map pre).motiveBinders (η.map pre) ls l :=
  (Ctx.ofTypes_map _ pre).trans <| by simp! [motiveBinders]

@[simp] private theorem caseBinders_map (I : Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ) :
    (I.caseBinders η ls).map pre =
      (I.map pre).caseBinders (η.map pre) ls :=
  (Ctx.ofTypes_map _ pre).trans <| by simp! [caseBinders]

@[simp] theorem recrTele_map
    (pre : ζ₁ ⟶ ζ₂) (η : Head ζ₁ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) :
    (I.recrTele η s ls l).map pre =
      (I.map pre).recrTele (η.map pre) s ls l := by
  change (Ctx.map pre _).snoc _ = _
  congr 1
  · refine (Ctx.map_append pre _ _).trans (congrArg₂ Tele.append ?_ ?_)
    · refine (Ctx.map_append pre _ _).trans (congrArg₂ Tele.append ?_ ?_)
      · refine (Ctx.map_append pre _ _).trans (congrArg₂ Tele.append ?_ ?_)
        · exact I.params.map_instL pre ls
        · exact I.motiveBinders_map pre η ls l
      · exact I.caseBinders_map pre η ls
    · exact I.indexTele_map pre ls s _
  · simp!

@[simp] theorem motiveBinders_instL (levelSubst : Param ℓ → Level ℓ') :
    (I.motiveBinders η ls l).instL levelSubst =
      I.motiveBinders η (fun level => (ls level).inst levelSubst)
        (l.inst levelSubst) := by
  simp! [motiveBinders]

@[simp] theorem caseBinders_instL (levelSubst : Param ℓ → Level ℓ') :
    (I.caseBinders η ls).instL levelSubst =
      I.caseBinders η fun level => (ls level).inst levelSubst := by
  simp! [caseBinders]

@[simp] theorem recrTele_instL
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (l : Level ℓ) (levelSubst : Param ℓ → Level ℓ') :
    (I.recrTele η s ls l).instL levelSubst =
      I.recrTele η s (fun level => (ls level).inst levelSubst)
        (l.inst levelSubst) := by
  change (Ctx.instL levelSubst _).snoc _ = _
  congr 1 <;> simp!

end Inductive

namespace IndSig

def recrBody (ι : IndSig) (s : Fin ι.nsorts) :
    Expr ζ₁ ℓ (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s + 1) :=
  Inductive.motiveResult
    (.var (RecrBinder.motive s).resolve)
    (fun index => .var (RecrBinder.index index).resolve)
    (.var RecrBinder.major.resolve)

@[simp] theorem recrBody_map (ι : IndSig) (pre : ζ₁ ⟶ ζ₂) (s : Fin ι.nsorts) :
    (ι.recrBody s : Expr ζ₁ ℓ _).map pre = (ι.recrBody s : Expr ζ₂ ℓ _) := by
  simp! [recrBody]

end IndSig

end Metalean
