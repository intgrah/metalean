/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.FEnv
public import Metalean.Frontend.Failure
public import Metalean.Syntax.Inductive.Iota
public import Metalean.Syntax.Structure
public import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

variable {E : Σ ζ, Env ζ} {L : Literals} {ℓ n : Nat}

abbrev minorIndex (ι : IndSig) (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) : Fin (Fin.sum ι.nctors) :=
  Fin.encodeSigma ι.nctors ⟨t, c⟩

def FExpr.motiveResult (motive : FExpr) (is : Array FExpr) (maj : FExpr) : FExpr :=
  .app (motive.apps is) maj

theorem FExpr.Denotes.motiveResult {n k : Nat} {fmotive fmaj : FExpr} {is : Array FExpr}
    {motive maj : Expr E.1 ℓ n} {is' : Fin k → Expr E.1 ℓ n} (his : is.size = k) :
    FExpr.Denotes L E 0 fmotive motive →
    (∀ i : Fin k, FExpr.Denotes L E 0 (is[i.val]'(his.symm ▸ i.isLt)) (is' i)) →
    FExpr.Denotes L E 0 fmaj maj →
    FExpr.Denotes L E 0 (FExpr.motiveResult fmotive is fmaj) (Inductive.motiveResult motive is' maj) :=
  fun hm his' hmaj => .app (hm.apps his his') hmaj

namespace FRecField

variable (ffd : FRecField) (pos target : Nat) (us : Array FLevel) (ps args : Array FExpr) (n : Nat)

def instTele : Array FExpr :=
  Array.ofFn fun j : Fin ffd.tele.size => (ffd.tele[j].instL us).instFVars (args ++ FExpr.fvars n j)

def instIndices : Array FExpr :=
  ffd.indices.map fun t => (t.instL us).instFVars (args ++ FExpr.fvars n ffd.tele.size)

def instType : FExpr :=
  FExpr.piTele n (ffd.instTele us args n) (.ind pos target us ps (ffd.instIndices us args n))

def ihType (motive r : FExpr) : FExpr :=
  FExpr.piTele n (ffd.instTele us args n)
    (.app (motive.apps (ffd.instIndices us args n)) (r.apps (FExpr.fvars n ffd.tele.size)))

def iotaIH (l : FLevel) (ms mins : Array FExpr) (r : FExpr) : FExpr :=
  FExpr.lamTele n (ffd.instTele us args n)
    (.recr pos target us l ps ms mins (ffd.instIndices us args n)
      (r.apps (FExpr.fvars n ffd.tele.size)))

end FRecField

namespace FCtor

variable (fctor : FCtor) (pos s c : Nat) (us : Array FLevel) (ps fds : Array FExpr) (n : Nat)

def ordinaryFieldExpr (f : Nat) (hf : f < fctor.ordinary.size) : FExpr :=
  (fctor.ordinary[f].type.instL us).instFVars (ps ++ fds.extract 0 f)

def recursiveFieldExpr (target : Nat) (r : Nat) (hr : r < fctor.recursive.size) : FExpr :=
  fctor.recursive[r].instType pos target us ps (ps ++ fds) n

def instTargetIndices : Array FExpr :=
  fctor.targetIndices.map fun t => (t.instL us).instFVars (ps ++ fds)

def ordinaryTys : Array FExpr :=
  Array.ofFn fun f : Fin fctor.ordinary.size =>
    (fctor.ordinary[f].type.instL us).instFVars (ps ++ FExpr.fvars n f)

def recursiveTys (target : Fin fctor.recursive.size → Nat) : Array FExpr :=
  Array.ofFn fun r => fctor.recursive[r].instType pos (target r) us ps
    (ps ++ FExpr.fvars n fctor.ordinary.size) (n + fctor.ordinary.size)

def ihTys (motive : Fin fctor.recursive.size → FExpr) : Array FExpr :=
  Array.ofFn fun r => fctor.recursive[r].ihType us (ps ++ FExpr.fvars n fctor.ordinary.size)
    (n + fctor.ordinary.size + fctor.recursive.size) (motive r)
    (.fvar (n + fctor.ordinary.size + r.val))

def caseType (motive : FExpr) : FExpr :=
  FExpr.motiveResult motive (fctor.instTargetIndices us ps (FExpr.fvars n fctor.ordinary.size))
    (.ctor pos s c us ps (FExpr.fvars n fctor.ordinary.size)
      (FExpr.fvars (n + fctor.ordinary.size) fctor.recursive.size))

def caseFnType (target : Fin fctor.recursive.size → Nat) (motive : Fin fctor.recursive.size → FExpr)
    (sortMotive : FExpr) : FExpr :=
  FExpr.piTele n
    (fctor.ordinaryTys us ps n ++ fctor.recursiveTys pos us ps n target ++
      fctor.ihTys us ps n motive)
    (fctor.caseType pos s c us ps n sortMotive)

def iotaRhs (target : Fin fctor.recursive.size → Nat) (l : FLevel) (ms mins : Array FExpr)
    (minor : FExpr) (recFds : Array FExpr) (hrecFds : recFds.size = fctor.recursive.size) : FExpr :=
  ((minor.apps fds).apps recFds).apps
    (Array.ofFn fun r : Fin fctor.recursive.size =>
      fctor.recursive[r].iotaIH pos (target r) us ps (ps ++ fds) n l ms mins
        (recFds[r.val]'(hrecFds.symm ▸ r.isLt)))

end FCtor

namespace FInductive

variable (fI : FInductive) (pos : Nat) (us : Array FLevel) (ps : Array FExpr) (n : Nat)

def paramType (p : Nat) (hp : p < fI.params.size) : FExpr :=
  (fI.params[p].instL us).instFVars (ps.extract 0 p)

def indexType (s : Nat) (hs : s < fI.indices.size) (is : Array FExpr) (i : Nat)
    (hi : i < fI.indices[s].size) : FExpr :=
  (fI.indices[s][i].instL us).instFVars (ps ++ is.extract 0 i)

def indexTele (s : Nat) (hs : s < fI.indices.size) : Array FExpr :=
  Array.ofFn fun j : Fin fI.indices[s].size =>
    (fI.indices[s][j].instL us).instFVars (ps ++ FExpr.fvars n j)

def motiveTele (s : Nat) (hs : s < fI.indices.size) : Array FExpr :=
  (fI.indexTele us ps n s hs).push (.ind pos s us ps (FExpr.fvars n fI.indices[s].size))

def motiveType (s : Nat) (hs : s < fI.indices.size) (l : FLevel) : FExpr :=
  FExpr.piTele n (fI.motiveTele pos us ps n s hs) (.sort l)

end FInductive

theorem FExpr.Denotes.isVar {n k x : Nat} {e : Expr E.1 ℓ n} :
    FExpr.Denotes L E k (.fvar x) e →
    e.isVar = some x
  | .fvar _ => rfl

def FCtor.eligible (fctor : FCtor) (nparams : Nat) (level : FLevel) : Bool :=
  (List.finRange fctor.ordinary.size).all (fun f =>
    fctor.ordinary[f].level.alwaysZero || fctor.targetIndices.any (· == .fvar (nparams + f.val))) &&
  (fctor.recursive.size == 0 || level == .zero)

def FInductive.getCtor (fI : FInductive) (s c : Nat) : Except Failure FCtor :=
  match fI.ctors[s]?.bind (·[c]?) with
  | some fctor => pure fctor
  | none => throw .internal

def FInductive.sortLargeElim (fI : FInductive) (row : Array FCtor) : Bool :=
  fI.level.isNotZero ||
    (fI.ctors.size == 1 && row.size ≤ 1 && row.all fun fctor => fctor.eligible fI.params.size fI.level)

def FInductive.largeElim (fI : FInductive) : Bool :=
  fI.ctors.all fI.sortLargeElim

def FInductive.recAllowed (fI : FInductive) (l : FLevel) : Bool :=
  l == .zero || fI.largeElim

def FInductive.isStructure (fI : FInductive) (s c : Nat) : Bool :=
  fI.ctors.size == 1 &&
  (match fI.ctors[s]? with
    | some row =>
      row.size == 1 &&
      (match row[c]? with
        | some fctor => fctor.recursive.size == 0
        | none => false) &&
      fI.sortLargeElim row
    | none => false) &&
  (match fI.indices[s]? with
    | some is => is.size == 0
    | none => false)

section Projection

def FExpr.projFields (pos s k : Nat) (e : FExpr) : Array FExpr :=
  Array.ofFn fun j : Fin k => .proj pos s j.val e

def FCtor.projType (fctor : FCtor) (pos s : Nat) (us : Array FLevel) (ps : Array FExpr) (f : Nat)
    (hf : f < fctor.ordinary.size) (e : FExpr) : FExpr :=
  fctor.ordinaryFieldExpr us ps (FExpr.projFields pos s fctor.ordinary.size e) f hf

def FCtor.rebuildTerm (fctor : FCtor) (pos s : Nat) (us : Array FLevel) (ps : Array FExpr)
    (e : FExpr) : FExpr :=
  .ctor pos s 0 us ps (FExpr.projFields pos s fctor.ordinary.size e) #[]

end Projection

section Lemmas

variable {ι : IndSig} {fI : FInductive} {I : Inductive E.1 ι} {us : Array FLevel}
  {ls' : Fin ι.nlevels → RawLevel ℓ} {n : Nat} {ps : Array FExpr} {ps' : Fin ι.nparams → Expr E.1 ℓ n}

namespace FInductive.Denotes

theorem paramsSize :
    FInductive.Denotes L E fI I →
    fI.params.size = ι.nparams := by
  intro hI
  have := hI.params.size
  omega

theorem paramLt (p : Fin ι.nparams) :
    FInductive.Denotes L E fI I →
    p.val < fI.params.size := by
  intro hI
  rw [hI.paramsSize]
  exact p.isLt

theorem indicesLt (s : Fin ι.nsorts) :
    FInductive.Denotes L E fI I →
    s.val < fI.indices.size := by
  intro hI
  rw [hI.indicesSize]
  exact s.isLt

theorem indicesRow (s : Fin ι.nsorts) :
    (hI : FInductive.Denotes L E fI I) →
    (fI.indices[s.val]'(hI.indicesLt s)).size = ι.nindices s := by
  intro hI
  have := (hI.indices s).size
  omega

theorem indexLt (s : Fin ι.nsorts) (i : Fin (ι.nindices s)) :
    (hI : FInductive.Denotes L E fI I) →
    i.val < (fI.indices[s.val]'(hI.indicesLt s)).size := by
  intro hI
  rw [hI.indicesRow s]
  exact i.isLt

theorem ctorsLt (s : Fin ι.nsorts) :
    FInductive.Denotes L E fI I →
    s.val < fI.ctors.size := by
  intro hI
  rw [hI.ctorsSize]
  exact s.isLt

theorem ctorLt (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    (hI : FInductive.Denotes L E fI I) →
    c.val < (fI.ctors[s.val]'(hI.ctorsLt s)).size := by
  intro hI
  rw [hI.ctorsRow s]
  exact c.isLt

theorem levelInst (hus : us.size = ι.nlevels) :
    FInductive.Denotes L E fI I →
    (∀ i, FLevel.Denotes (us[i.val]'(hus.symm ▸ i.isLt)) (ls' i)) →
    ∃ l : RawLevel ℓ, FLevel.Denotes (fI.level.inst us) l ∧
      ⟦l⟧ = I.level.inst (⟦ls' ·⟧) := by
  intro hI hus'
  have ⟨fl₀, hl₀, hl₀'⟩ := hI.level
  exact ⟨_, hl₀.inst hus hus', by rw [Level.mk_inst, hl₀']⟩

end FInductive.Denotes

theorem FRecField.Denotes.teleSize {nfields arity : Nat} {target : Fin ι.nsorts} {ffd : FRecField}
    {fd : RecField E.1 ι nfields arity target} :
    FRecField.Denotes L E ffd fd →
    ffd.tele.size = arity := by
  intro hfd
  have := hfd.tele.size
  omega

theorem FCtor.Denotes.ordinaryLt {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {fctor : FCtor}
    {ctor : Ctor E.1 ι s csig} (f : Fin csig.nfields) :
    FCtor.Denotes L E fctor ctor →
    f.val < fctor.ordinary.size := by
  intro hc
  rw [hc.ordinarySize]
  exact f.isLt

theorem FCtor.Denotes.recursiveLt {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {fctor : FCtor}
    {ctor : Ctor E.1 ι s csig} (r : Fin csig.nrecFields) :
    FCtor.Denotes L E fctor ctor →
    r.val < fctor.recursive.size := by
  intro hc
  rw [hc.recursiveSize]
  exact r.isLt

variable (hI : FInductive.Denotes L E fI I) (hus : us.size = ι.nlevels)
  (hus' : ∀ i, FLevel.Denotes (us[i.val]'(hus.symm ▸ i.isLt)) (ls' i))
  (hps : ArgsDenote L E ps ps')

include hus' hps in
theorem FInductive.Denotes.paramType (p : Fin ι.nparams) :
    FExpr.Denotes L E 0 (fI.paramType us ps p (hI.paramLt p))
      (I.paramType (⟦ls' ·⟧) ps' p) :=
  have h := hI.params.entry (p := p.val) (Nat.zero_le _) (by have := hI.params.size; omega)
  (h.instL hus hus').instFVars (hps.extract p.val (by omega))

include hus' hps in
theorem FInductive.Denotes.indexType (s : Fin ι.nsorts) {is : Array FExpr}
    {is' : Fin (ι.nindices s) → Expr E.1 ℓ n} (his : ArgsDenote L E is is')
    (i : Fin (ι.nindices s)) :
    FExpr.Denotes L E 0
      (fI.indexType us ps s (hI.indicesLt s) is i (hI.indexLt s i))
      (I.indexType (⟦ls' ·⟧) s ps' is' i) := by
  have h := (hI.indices s).entry (p := ι.nparams + i.val) (Nat.le_add_right _ _)
    (by have := (hI.indices s).size; omega)
  simp only [Nat.add_sub_cancel_left] at h
  unfold Inductive.indexType
  rw [Ctx.proj_eq_entry]
  exact (h.instL hus hus').instFVars (hps.append (his.extract i.val (by omega)))

include hus' hps in
theorem FInductive.Denotes.indexTele (s : Fin ι.nsorts) :
    FCtx.Denotes L E (fI.indexTele us ps n s (hI.indicesLt s))
      (I.indexTele (⟦ls' ·⟧) s ps') :=
  (hI.indices s).instTele hus hus' hps

include hus' hps in
theorem FInductive.Denotes.motiveTele {pos : Nat} {η : Head E.1 (.inductive ι)}
    (hη : E.1.lookup pos = some ⟨.inductive ι, η⟩) (s : Fin ι.nsorts) :
    FCtx.Denotes L E (fI.motiveTele pos us ps n s (hI.indicesLt s))
      (I.motiveTele η (⟦ls' ·⟧) ps' s) := by
  unfold FInductive.motiveTele Inductive.motiveTele
  refine .snoc (hI.indexTele hus hus' hps s) ?_
  rw [hI.indicesRow s]
  exact .ind hus hps.size (by simp) hη rfl hus' (fun p => (hps.denotes p).wkN _)
    fun i => by
      simp only [FExpr.getElem_fvars]
      exact .fvar (by omega)

include hus' hps in
theorem FInductive.Denotes.motiveType {pos : Nat} {η : Head E.1 (.inductive ι)}
    (hη : E.1.lookup pos = some ⟨.inductive ι, η⟩) (s : Fin ι.nsorts) {fl : FLevel}
    {l : RawLevel ℓ} (hl : FLevel.Denotes fl l) :
    FExpr.Denotes L E 0 (fI.motiveType pos us ps n s (hI.indicesLt s) fl)
      (I.motiveType η (⟦ls' ·⟧) ps' ⟦l⟧ s) :=
  (hI.motiveTele hus hus' hps hη s).piTele (.sort hl)

section Ctor

variable {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {fctor : FCtor} {ctor : Ctor E.1 ι s (ι.ctors s c)}
  (hc : FCtor.Denotes L E fctor ctor) {fds : Array FExpr}
  {fds' : Fin (ι.ctors s c).nfields → Expr E.1 ℓ n} (hfds : ArgsDenote L E fds fds')

include hus' hps hfds in
theorem FCtor.Denotes.ordinaryFieldExpr (f : Fin (ι.ctors s c).nfields) :
    FExpr.Denotes L E 0 (fctor.ordinaryFieldExpr us ps fds f (hc.ordinaryLt f))
      (ctor.ordinaryFieldExpr (⟦ls' ·⟧) ps' fds' f) :=
  ((hc.ordinary f).type.instL hus hus').instFVars (hps.append (hfds.extract f.val (by omega)))

include hc in
theorem FCtor.Denotes.instTargetIndices_size :
    (fctor.instTargetIndices us ps fds).size = ι.nindices s := by
  simp [FCtor.instTargetIndices, hc.targetSize]

include hus' hps hfds in
theorem FCtor.Denotes.instTargetIndices (i : Fin (ι.nindices s)) :
    FExpr.Denotes L E 0
      ((fctor.instTargetIndices us ps fds)[i.val]'(hc.instTargetIndices_size.symm ▸ i.isLt))
      (ctor.targetIndex (⟦ls' ·⟧) ps' fds' i) := by
  simp only [FCtor.instTargetIndices, Array.getElem_map]
  exact ((hc.targetIndices i).instL hus hus').instFVars (hps.append hfds)

include hc hus' hps hfds in
theorem FCtor.Denotes.instTargetIndicesArgs :
    ArgsDenote L E (fctor.instTargetIndices us ps fds)
      (ctor.targetIndex (⟦ls' ·⟧) ps' fds') :=
  ⟨hc.instTargetIndices_size, hc.instTargetIndices hus hus' hps hfds⟩

end Ctor

section RecField

variable {nfields arity : Nat} {target : Fin ι.nsorts} {ffd : FRecField}
  {fd : RecField E.1 ι nfields arity target} (hfd : FRecField.Denotes L E ffd fd)
  {args : Array FExpr} {σ : Subst E.1 ℓ (ι.nparams + nfields) n} (hargs : ArgsDenote L E args σ)

include hfd hus' hargs in
theorem FRecField.Denotes.instTele :
    FCtx.Denotes L E (ffd.instTele us args n) (fd.instantiatedTelescope (⟦ls' ·⟧) σ) :=
  hfd.tele.instTele hus hus' hargs

include hfd in
theorem FRecField.Denotes.instIndices_size :
    (ffd.instIndices us args n).size = ι.nindices target := by
  simp [FRecField.instIndices, hfd.size]

include hus' hargs in
theorem FRecField.Denotes.instIndices (i : Fin (ι.nindices target)) :
    FExpr.Denotes L E 0
      ((ffd.instIndices us args n)[i.val]'(hfd.instIndices_size.symm ▸ i.isLt))
      (fd.instantiatedIndices (⟦ls' ·⟧) σ i) := by
  simp only [FRecField.instIndices, Array.getElem_map, hfd.teleSize]
  exact ((hfd.indices i).instL hus hus').instFVars (hargs.liftN arity)

include hfd hus' hps hargs in
theorem FRecField.Denotes.instType {pos : Nat} {η : Head E.1 (.inductive ι)}
    (hη : E.1.lookup pos = some ⟨.inductive ι, η⟩) :
    FExpr.Denotes L E 0 (ffd.instType pos target.val us ps args n)
      (fd.instantiatedType η (⟦ls' ·⟧) ps' σ) :=
  (hfd.instTele hus hus' hargs).piTele
    (.ind hus hps.size hfd.instIndices_size hη rfl hus' (fun p => (hps.denotes p).wkN arity)
      (hfd.instIndices hus hus' hargs))

include hfd hus' hargs in
theorem FRecField.Denotes.ihType {fmotive fr : FExpr} {ms' : Fin ι.nsorts → Expr E.1 ℓ n}
    {r : Expr E.1 ℓ n} (hmotive : FExpr.Denotes L E 0 fmotive (ms' target))
    (hr : FExpr.Denotes L E 0 fr r) :
    FExpr.Denotes L E 0 (ffd.ihType us args n fmotive fr)
      (fd.ihType (⟦ls' ·⟧) ms' σ r) := by
  refine (hfd.instTele hus hus' hargs).piTele ?_
  rw [Expr.applyBound_eq_apps]
  refine .app ((hmotive.wkN arity).apps hfd.instIndices_size (hfd.instIndices hus hus' hargs)) ?_
  rw [hfd.teleSize]
  exact (hr.wkN arity).apps (by simp) fun i => by
    simp only [FExpr.getElem_fvars]
    exact .fvar (by omega)

include hfd hus' hps hargs in
theorem FRecField.Denotes.iotaIH {pos : Nat} {η : Head E.1 (.inductive ι)}
    (hη : E.1.lookup pos = some ⟨.inductive ι, η⟩) {fl : FLevel} {l : RawLevel ℓ}
    (hl : FLevel.Denotes fl l) {ms mins : Array FExpr} {ms' : Fin ι.nsorts → Expr E.1 ℓ n}
    (hms : ArgsDenote L E ms ms')
    {mins' : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr E.1 ℓ n}
    (hmins : mins.size = Fin.sum ι.nctors)
    (hmins' : ∀ t c, FExpr.Denotes L E 0
      (mins[(minorIndex ι t c).val]'(hmins.symm ▸ (minorIndex ι t c).isLt)) (mins' t c))
    {fr : FExpr} {r : Expr E.1 ℓ n} (hr : FExpr.Denotes L E 0 fr r) :
    FExpr.Denotes L E 0 (ffd.iotaIH pos target.val us ps args n fl ms mins fr)
      (fd.iotaIH η (⟦ls' ·⟧) ⟦l⟧ ps' ms' mins' σ r) := by
  refine (hfd.instTele hus hus' hargs).lamTele ?_
  rw [Expr.applyBound_eq_apps]
  refine .recr hus hps.size hms.size hmins hfd.instIndices_size hη rfl hus' hl
    (fun p => (hps.denotes p).wkN arity)
    (fun t => (hms.denotes t).wkN arity)
    (fun t c => (hmins' t c).wkN arity)
    (hfd.instIndices hus hus' hargs)
    ?_
  rw [hfd.teleSize]
  exact (hr.wkN arity).apps (by simp) fun i => by
    simp only [FExpr.getElem_fvars]
    exact .fvar (by omega)

end RecField

section CtorField

variable {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {fctor : FCtor} {ctor : Ctor E.1 ι s (ι.ctors s c)}
  (hc : FCtor.Denotes L E fctor ctor) {fds : Array FExpr}
  {fds' : Fin (ι.ctors s c).nfields → Expr E.1 ℓ n} (hfds : ArgsDenote L E fds fds')

include hc hus' hps hfds in
theorem FCtor.Denotes.recursiveFieldExpr {pos : Nat} {η : Head E.1 (.inductive ι)}
    (hη : E.1.lookup pos = some ⟨.inductive ι, η⟩) (r : Fin (ι.ctors s c).nrecFields) :
    FExpr.Denotes L E 0
      (fctor.recursiveFieldExpr pos us ps fds n ((ι.ctors s c).recursiveTarget r).val r.val
        (hc.recursiveLt r))
      (ctor.recursiveFieldExpr η (⟦ls' ·⟧) ps' fds' r) :=
  (hc.recursive r).instType hus hus' hps (hps.append hfds) hη

end CtorField

section CtorTele

variable {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {fctor : FCtor}
  (hc : FCtor.Denotes L E fctor (I.ctors s c)) {pos : Nat} {η : Head E.1 (.inductive ι)}
  (hη : E.1.lookup pos = some ⟨.inductive ι, η⟩) {target : Fin fctor.recursive.size → Nat}
  (htarget : ∀ fr, target fr = ((ι.ctors s c).recursiveTarget (fr.cast hc.recursiveSize)).val)
  {ms : Array FExpr} {ms' : Fin ι.nsorts → Expr E.1 ℓ n} (hms : ArgsDenote L E ms ms')

include hps in
theorem ArgsDenote.fieldParams {csig : CtorSig ι.nsorts} :
    ArgsDenote L E ps (csig.fieldParams ps') :=
  ⟨hps.size, fun v => ((hps.denotes v).wkN csig.nfields).wkN csig.nrecFields⟩

theorem ArgsDenote.fieldOrdinary (csig : CtorSig ι.nsorts) :
    ArgsDenote (ℓ := ℓ) L E (FExpr.fvars n csig.nfields)
      (csig.fieldOrdinary (n := n)) where
  size := by simp
  denotes v := by
    simp only [FExpr.getElem_fvars]
    exact (FExpr.Denotes.fvar (k := 0) (by omega)).wkN csig.nrecFields

theorem ArgsDenote.fieldRecursive (csig : CtorSig ι.nsorts) :
    ArgsDenote (ℓ := ℓ) L E (FExpr.fvars (n + csig.nfields) csig.nrecFields)
      (csig.fieldRecursive (n := n)) where
  size := by simp
  denotes v := by
    simp only [FExpr.getElem_fvars]
    exact .fvar (by omega)

include hps in
theorem ArgsDenote.caseParams {csig : CtorSig ι.nsorts} :
    ArgsDenote L E ps (csig.caseParams ps') :=
  ⟨hps.size, fun v => (((hps.denotes v).wkN csig.nfields).wkN csig.nrecFields).wkN csig.nrecFields⟩

theorem ArgsDenote.caseOrdinary (csig : CtorSig ι.nsorts) :
    ArgsDenote (ℓ := ℓ) L E (FExpr.fvars n csig.nfields)
      (csig.caseOrdinary (n := n)) where
  size := by simp
  denotes v := by
    simp only [FExpr.getElem_fvars]
    exact ((FExpr.Denotes.fvar (k := 0) (by omega)).wkN csig.nrecFields).wkN csig.nrecFields

theorem ArgsDenote.caseRecursive (csig : CtorSig ι.nsorts) :
    ArgsDenote (ℓ := ℓ) L E (FExpr.fvars (n + csig.nfields) csig.nrecFields)
      (csig.caseRecursive (n := n)) where
  size := by simp
  denotes v := by
    simp only [FExpr.getElem_fvars]
    exact (FExpr.Denotes.fvar (k := 0) (by omega)).wkN csig.nrecFields

include hc hus' hps in
theorem FCtor.Denotes.ordinaryTys :
    FCtx.Denotes L E (fctor.ordinaryTys us ps n)
      ((I.ctors s c).ordinaryFieldTele η (⟦ls' ·⟧) ps') :=
  FCtx.Denotes.ofFn hc.ordinarySize _ _ fun i => by
    have := hc.ordinarySize
    rw [Ctor.ordinaryFieldTele, Ctor.ordinaryFieldTeleAux_entry _ _ _ _ _ _ ⟨i.val, by omega⟩]
    exact ((hc.ordinary ⟨i.val, by omega⟩).type.instL hus hus').instFVars (hps.liftN i.val)

include hc hus' hps hη htarget in
theorem FCtor.Denotes.recursiveTys :
    FCtx.Denotes L E (fctor.recursiveTys pos us ps n target)
      ((I.ctors s c).recursiveFieldTeleAux η (⟦ls' ·⟧)
        (fun i => (ps' i).wkN (ι.ctors s c).nfields) (Expr.boundVars n (ι.ctors s c).nfields 0)
        (ι.ctors s c).nrecFields le_rfl) := by
  unfold FCtor.recursiveTys Ctor.recursiveFieldTeleAux
  simp only [hc.ordinarySize]
  refine FCtx.Denotes.ofTypes hc.recursiveSize fun fr => ?_
  rw [htarget fr]
  exact (hc.recursive (fr.cast hc.recursiveSize)).instType hus hus' (hps.wkN _)
    ((hps.wkN _).append (ArgsDenote.fvars n _)) hη

include hc hus' hps in
omit hms in
theorem FCtor.Denotes.ihTys {fmotive : Fin fctor.recursive.size → FExpr}
    (hmotive : ∀ r, FExpr.Denotes L E 0 (fmotive r)
      (ms' ((ι.ctors s c).recursiveTarget (r.cast hc.recursiveSize)))) :
    FCtx.Denotes L E
      (fctor.ihTys us ps n fmotive) ((I.ctors s c).ihTele (⟦ls' ·⟧) ps' ms') := by
  unfold FCtor.ihTys Ctor.ihTele
  simp only [hc.ordinarySize, hc.recursiveSize]
  refine FCtx.Denotes.ofTypes hc.recursiveSize fun r => ?_
  unfold Ctor.ihType Ctor.ihTypeWith
  exact (hc.recursive (r.cast hc.recursiveSize)).ihType hus hus'
    ((hps.fieldParams).append (ArgsDenote.fieldOrdinary _))
    (((hmotive r).wkN _).wkN _) (.fvar (by have := hc.recursiveSize; omega))

include hc hus' hps hη in
theorem FCtor.Denotes.caseType {fsortMotive : FExpr}
    (hsortMotive : FExpr.Denotes L E 0 fsortMotive (ms' s)) :
    FExpr.Denotes L E 0
      (fctor.caseType pos s c us ps n fsortMotive) (I.caseType η (⟦ls' ·⟧) ps' ms' s c) := by
  unfold FCtor.caseType Inductive.caseType
  simp only [hc.ordinarySize, hc.recursiveSize]
  refine (((hsortMotive.wkN _).wkN _).wkN _).motiveResult hc.instTargetIndices_size
    (hc.instTargetIndices hus hus' hps.caseParams (ArgsDenote.caseOrdinary _)) ?_
  exact .ctor hus hps.size (by simp) (by simp) hη rfl rfl hus'
    (hps.caseParams).denotes
    (ArgsDenote.caseOrdinary _).denotes
    (ArgsDenote.caseRecursive _).denotes

include hc hus' hps hη htarget in
omit hms in
theorem FCtor.Denotes.caseFnType {fmotive : Fin fctor.recursive.size → FExpr}
    (hmotive : ∀ r, FExpr.Denotes L E 0 (fmotive r)
      (ms' ((ι.ctors s c).recursiveTarget (r.cast hc.recursiveSize))))
    {fsortMotive : FExpr} (hsortMotive : FExpr.Denotes L E 0 fsortMotive (ms' s)) :
    FExpr.Denotes L E 0 (fctor.caseFnType pos s c us ps n target fmotive fsortMotive)
      (I.caseFnType η (⟦ls' ·⟧) ps' ms' s c) :=
  (((hc.ordinaryTys hus hus' hps).append (hc.recursiveTys hus hus' hps hη htarget)).append
    (hc.ihTys hus hus' hps hmotive)).piTele (hc.caseType hus hus' hps hη hsortMotive)

include hc hus' hps hη htarget hms in
theorem FCtor.Denotes.iotaRhs {fl : FLevel} {l : RawLevel ℓ} (hl : FLevel.Denotes fl l)
    {mins : Array FExpr} {mins' : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr E.1 ℓ n}
    (hmins : mins.size = Fin.sum ι.nctors)
    (hmins' : ∀ t c, FExpr.Denotes L E 0
      (mins[(minorIndex ι t c).val]'(hmins.symm ▸ (minorIndex ι t c).isLt)) (mins' t c))
    {fminor : FExpr} (hminor : FExpr.Denotes L E 0 fminor (mins' s c))
    {fds : Array FExpr} {fds' : Fin (ι.ctors s c).nfields → Expr E.1 ℓ n}
    (hfds : ArgsDenote L E fds fds') {recFds : Array FExpr}
    {recFds' : Fin (ι.ctors s c).nrecFields → Expr E.1 ℓ n}
    (hrecFds : ArgsDenote L E recFds recFds') :
    FExpr.Denotes L E 0
      (fctor.iotaRhs pos us ps fds n target fl ms mins fminor recFds
        (hrecFds.size.trans hc.recursiveSize.symm))
      (I.iotaRhs η (⟦ls' ·⟧) ⟦l⟧ ps' ms' mins' s c fds' recFds') := by
  unfold FCtor.iotaRhs Inductive.iotaRhs
  refine ((hminor.apps hfds.size hfds.denotes).apps hrecFds.size hrecFds.denotes).apps
    (by simp [hc.recursiveSize]) fun fr => ?_
  simp only [Array.getElem_ofFn]
  unfold Inductive.iotaIHs Ctor.iotaIH
  rw [htarget]
  exact (hc.recursive _).iotaIH hus hus' hps (hps.append hfds) hη hl hms hmins hmins'
    (hrecFds.denotes _)

end CtorTele

section OrdinaryTele

def FCtor.ordinaryTemplates (fctor : FCtor) (f : Nat) : FCtx :=
  (fctor.ordinary.extract 0 f).map (·.type)

theorem FCtor.Denotes.ordinaryTele {ζ : Sigs} {E : Env ζ} {ι : IndSig} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {fctor : FCtor} {ctor : Ctor ζ ι s (ι.ctors s c)}
    (hc : FCtor.Denotes L ⟨ζ, E⟩ fctor ctor) :
    (f : Nat) → (hf : f ≤ (ι.ctors s c).nfields) →
    FCtx.Denotes L ⟨ζ, E⟩ (fctor.ordinaryTemplates f) (ctor.ordinaryTeleAux f hf)
  | 0, _ => by
    have : fctor.ordinaryTemplates 0 = #[] := by simp [FCtor.ordinaryTemplates]
    rw [this]
    exact .nil
  | f + 1, hf => by
    have hsize := hc.ordinarySize
    have hprev := hc.ordinaryTele f (by omega)
    have hpush : fctor.ordinaryTemplates (f + 1) =
        (fctor.ordinaryTemplates f).push (fctor.ordinary[f]'(by omega)).type := by
      simp only [FCtor.ordinaryTemplates,
        Array.extract_succ_right (as := fctor.ordinary) (i := 0) (j := f)
          (Nat.zero_lt_succ f) (by omega),
        Array.map_push]
    rw [hpush]
    exact .snoc hprev (hc.ordinary ⟨f, by omega⟩).type

end OrdinaryTele

section Elim

theorem FCtor.Denotes.eligible {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {fctor : FCtor}
    {flevel : FLevel} {level : RawLevel ι.nlevels}
    (hlevel' : (⟦level⟧ : Level ι.nlevels) = I.level)
    (h : fctor.eligible fI.params.size flevel = true) (hparams : fI.params.size = ι.nparams) :
    FCtor.Denotes L E fctor (I.ctors s c) →
    FLevel.Denotes flevel level →
    (I.ctors s c).Eligible I.level := by
  intro hc hlevel
  simp only [FCtor.eligible, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, Array.any_eq_true, Fin.getElem_fin] at h
  refine ⟨fun ff => ?_, fun ff => ?_⟩
  · rcases h.1 ⟨ff.val, hc.ordinaryLt ff⟩ with hz | ⟨i, hi, hfv⟩
    · left
      have ⟨l, hl', hl''⟩ := (hc.ordinary ff).level
      rw [← hl'', hl'.interp_eq_zero hz]
    · right
      refine ⟨⟨i, hc.targetSize ▸ hi⟩, ?_⟩
      rw [hparams] at hfv
      exact (hfv ▸ hc.targetIndices ⟨i, hc.targetSize ▸ hi⟩).isVar
  · rcases h.2 with hz | hz
    · exact absurd (hc.recursiveLt ff) (by omega)
    · rw [hz] at hlevel
      rw [← hlevel', hlevel.eq_zero]
      rfl

theorem FInductive.Denotes.sortLargeElim (s : Fin ι.nsorts) :
    (hI : FInductive.Denotes L E fI I) →
    fI.sortLargeElim (fI.ctors[s.val]'(hI.ctorsLt s)) = true →
    I.SortLargeElim s := by
  intro hI h
  have ⟨level, hlevel, hlevel'⟩ := hI.level
  simp only [FInductive.sortLargeElim, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Array.all_eq_true] at h
  rcases h with hnz | ⟨⟨hsorts, hle⟩, hall⟩
  · refine .large fun ν => ?_
    rw [← hlevel']
    exact hlevel.one_le_of_isNotZero hnz ν
  · refine .subsingleton ?_ (fun c c' => Fin.ext ?_) fun c => ?_
    · have := hI.ctorsSize
      omega
    · have := hI.ctorsRow s
      omega
    · exact (hI.ctors s c).eligible hlevel' (hall c.val (hI.ctorLt s c)) hI.paramsSize hlevel

theorem FInductive.Denotes.largeElim (h : fI.largeElim = true) :
    FInductive.Denotes L E fI I →
    I.LargeElim := fun hI s =>
  hI.sortLargeElim s (Array.all_eq_true.mp h s.val (hI.ctorsLt s))

theorem FInductive.Denotes.recAllowed {fl : FLevel} {l : RawLevel ℓ}
    (h : fI.recAllowed fl = true) :
    FInductive.Denotes L E fI I →
    FLevel.Denotes fl l →
    I.RecAllowed ⟦l⟧ := by
  intro hI hl
  simp only [FInductive.recAllowed, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · left
    rw [hl.eq_zero]
    rfl
  · exact .inr (hI.largeElim h)

theorem FInductive.Denotes.isStructure (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (h : fI.isStructure s.val c.val = true) :
    FInductive.Denotes L E fI I →
    I.IsStructure s c := by
  intro hI
  simp only [FInductive.isStructure, Bool.and_eq_true, beq_iff_eq,
    Array.getElem?_eq_getElem (hI.ctorsLt s), Array.getElem?_eq_getElem (hI.ctorLt s c),
    Array.getElem?_eq_getElem (hI.indicesLt s)] at h
  have ⟨⟨hsorts, ⟨hrow, hrec⟩, hlarge⟩, hind⟩ := h
  have hnsorts := hI.ctorsSize
  have hnctors := hI.ctorsRow s
  have hnind := hI.indicesRow s
  refine ⟨fun s' => Fin.ext (by omega), fun c' => Fin.ext (by omega), ⟨fun i => ?_⟩, ⟨fun fr => ?_⟩,
    hI.sortLargeElim s hlarge⟩
  · have := i.isLt
    omega
  · have := (hI.ctors s c).recursiveLt fr
    omega

end Elim

section ProjectionLemmas

variable {pos : Nat} {η : Head E.1 (.inductive ι)} (hη : E.1.lookup pos = some ⟨.inductive ι, η⟩)
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (hstruct : (E.2.get η).block.IsStructure s c)
  {fe : FExpr} {e : Expr E.1 ℓ n} (he : FExpr.Denotes L E 0 fe e)

include hη he in
theorem FExpr.Denotes.projFields {k : Nat} (hk : k = (ι.ctors s c).nfields) :
    ArgsDenote L E (FExpr.projFields pos s.val k fe)
      (fun f => hstruct.projTerm η (⟦ls' ·⟧) ps' f e) where
  size := by simp [FExpr.projFields, hk]
  denotes f := by
    simp only [FExpr.projFields, Array.getElem_ofFn]
    exact .proj hstruct hη rfl rfl he

include hus' hps hη he in
theorem FCtor.Denotes.projType {fctor : FCtor}
    (hc : FCtor.Denotes L E fctor ((E.2.get η).block.ctors s c)) (f : Fin (ι.ctors s c).nfields) :
    FExpr.Denotes L E 0 (fctor.projType pos s.val us ps f.val (hc.ordinaryLt f) fe)
      (hstruct.projType η (⟦ls' ·⟧) ps' f e) := by
  rw [Inductive.IsStructure.projType_eq]
  exact hc.ordinaryFieldExpr hus hus' hps
    (FExpr.Denotes.projFields hη hstruct he hc.ordinarySize) f

include hus' hps hη he in
theorem FCtor.Denotes.rebuildTerm {fctor : FCtor}
    (hc : FCtor.Denotes L E fctor ((E.2.get η).block.ctors s c)) :
    FExpr.Denotes L E 0 (fctor.rebuildTerm pos s.val us ps fe)
      (hstruct.rebuildTerm η (⟦ls' ·⟧) ps' e) := by
  have hc0 : c.val = 0 := by
    have := Fin.eq_one_of_unique c hstruct.ctor_unique
    have := c.isLt
    omega
  have hfds := FExpr.Denotes.projFields (ls' := ls') (ps' := ps') hη hstruct he hc.ordinarySize
  unfold FCtor.rebuildTerm Inductive.IsStructure.rebuildTerm
  exact .ctor hus hps.size hfds.size
    (by simp; exact (Fin.eq_zero_of_isEmpty hstruct.no_recursive).symm)
    hη rfl hc0 hus' hps.denotes hfds.denotes (fun fr => hstruct.no_recursive.elim fr)

end ProjectionLemmas

end Lemmas

end Metalean.FastChecker
