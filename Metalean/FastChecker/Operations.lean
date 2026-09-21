/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.FExpr

@[expose] public section

namespace Metalean.FastChecker

namespace FExpr

def ReplaceCache.key (addr : USize) (off : Nat) : USize × Nat :=
  (addr, off)

structure ReplaceCache where
  map : Std.HashMap (USize × Nat) FExpr := ∅
  inverse : Std.HashMap (USize × Nat) FExpr := ∅
  alive : Array FExpr := #[]
  keep : Bool := false
  span : Option Nat := none

unsafe def ReplaceCache.record (c : ReplaceCache) (off : Nat) (fe r : FExpr) : ReplaceCache :=
  let c := { c with map := c.map.insert (ReplaceCache.key (ptrAddrUnsafe fe) off) r }
  if !c.keep then c else
  let c := { c with alive := c.alive.push fe }
  match c.span with
  | none => c
  | some k =>
    if !fe.data.hasFVar ∧ fe.data.looseBVarRange.toNat ≤ off + k
        ∧ fe.data.looseBVarRange.toNat < Data.maxRange then
      { c with inverse := c.inverse.insert (ReplaceCache.key (ptrAddrUnsafe r) off) fe, alive := c.alive.push r }
    else c

abbrev ReplaceM := StateM ReplaceCache

mutual

@[specialize] unsafe def replaceCached (pre : Nat → FExpr → Option FExpr) (off : Nat) (fe : FExpr) :
    ReplaceM FExpr := do
  if let some r := pre off fe then return r
  if (← get).span.isNone && isExclusiveUnsafe fe then return ← replaceCoreShared pre off fe
  match (← get).map.get? (ReplaceCache.key (ptrAddrUnsafe fe) off) with
  | some cached => return cached
  | none =>
    let r ← replaceCoreShared pre off fe
    modify (·.record off fe r)
    return r

@[specialize] unsafe def replaceArray (pre : Nat → FExpr → Option FExpr) (off : Nat) (xs : Array FExpr) :
    ReplaceM (Array FExpr) := do
  let ys ← xs.mapM (replaceCached pre off)
  return if FExpr.ptrEqArrayElems xs ys then xs else ys

@[specialize] unsafe def replaceCoreShared (pre : Nat → FExpr → Option FExpr) (off : Nat) (fe : FExpr) :
    ReplaceM FExpr := do
  match fe with
  | .ind pos s ls ps is =>
    let ps' ← replaceArray pre off ps
    let is' ← replaceArray pre off is
    if FExpr.ptrEqArray ps ps' && FExpr.ptrEqArray is is' then pure fe else pure (.ind pos s ls ps' is')
  | .ctor pos s c ls ps fds recFds =>
    let ps' ← replaceArray pre off ps
    let fds' ← replaceArray pre off fds
    let recFds' ← replaceArray pre off recFds
    if FExpr.ptrEqArray ps ps' && FExpr.ptrEqArray fds fds' && FExpr.ptrEqArray recFds recFds' then pure fe
    else pure (.ctor pos s c ls ps' fds' recFds')
  | .recr pos s ls l ps ms mins is maj =>
    let ps' ← replaceArray pre off ps
    let ms' ← replaceArray pre off ms
    let mins' ← replaceArray pre off mins
    let is' ← replaceArray pre off is
    let maj' ← replaceCached pre off maj
    if FExpr.ptrEqArray ps ps' && FExpr.ptrEqArray ms ms' && FExpr.ptrEqArray mins mins' && FExpr.ptrEqArray is is'
        && ptrEq maj maj' then pure fe
    else pure (.recr pos s ls l ps' ms' mins' is' maj')
  | .quot pos l α r =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    if ptrEq α α' && ptrEq r r' then pure fe else pure (.quot pos l α' r')
  | .quotMk pos l α r y =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    let y' ← replaceCached pre off y
    if ptrEq α α' && ptrEq r r' && ptrEq y y' then pure fe else pure (.quotMk pos l α' r' y')
  | .quotLift pos l₁ l₂ α r β f h y =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    let β' ← replaceCached pre off β
    let f' ← replaceCached pre off f
    let h' ← replaceCached pre off h
    let y' ← replaceCached pre off y
    if ptrEq α α' && ptrEq r r' && ptrEq β β' && ptrEq f f' && ptrEq h h'
        && ptrEq y y' then pure fe
    else pure (.quotLift pos l₁ l₂ α' r' β' f' h' y')
  | .quotInd pos l α r β f y =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    let β' ← replaceCached pre off β
    let f' ← replaceCached pre off f
    let y' ← replaceCached pre off y
    if ptrEq α α' && ptrEq r r' && ptrEq β β' && ptrEq f f' && ptrEq y y' then pure fe
    else pure (.quotInd pos l α' r' β' f' y')
  | .proj pos s idx y =>
    let y' ← replaceCached pre off y
    if ptrEq y y' then pure fe else pure (.proj pos s idx y')
  | .app f y =>
    let f' ← replaceCached pre off f
    let y' ← replaceCached pre off y
    if ptrEq f f' && ptrEq y y' then pure fe else pure (.app f' y')
  | .lam t b =>
    let t' ← replaceCached pre off t
    let b' ← replaceCached pre (off + 1) b
    if ptrEq t t' && ptrEq b b' then pure fe else pure (.lam t' b')
  | .forallE t b =>
    let t' ← replaceCached pre off t
    let b' ← replaceCached pre (off + 1) b
    if ptrEq t t' && ptrEq b b' then pure fe else pure (.forallE t' b')
  | .letE t v b =>
    let t' ← replaceCached pre off t
    let v' ← replaceCached pre off v
    let b' ← replaceCached pre (off + 1) b
    if ptrEq t t' && ptrEq v v' && ptrEq b b' then pure fe else pure (.letE t' v' b')
  | _ => pure fe

end

@[specialize] unsafe def replaceShared (pre : Nat → FExpr → Option FExpr) (fe : FExpr) : FExpr :=
  (replaceCached pre 0 fe).run' {}

unsafe def instAtShared (fa : FExpr) (d : Nat) : FExpr → FExpr :=
  replaceShared fun off fe =>
    let d' := d + off
    if fe.data.looseBVarRange.toNat ≤ d' ∧ fe.data.looseBVarRange.toNat < Data.maxRange then some fe
    else match fe with
      | .bvar i => some (if i < d' then fe else if i = d' then fa else .bvar (i - 1))
      | _ => none

unsafe def abstractAtShared (x d : Nat) : FExpr → FExpr :=
  replaceShared fun off fe =>
    if fe.fvarRange ≤ x then some fe
    else match fe with
      | .fvar i => some (if i = x then .bvar (d + off) else fe)
      | _ => none

def openStep (base k off : Nat) (fe : FExpr) : Option FExpr :=
  if fe.data.looseBVarRange.toNat ≤ off ∧ fe.data.looseBVarRange.toNat < Data.maxRange then some fe
  else match fe with
    | .bvar i =>
      some (if i < off then fe
        else if i < off + k then .fvar (base + (k - 1 - (i - off)))
        else .bvar (i - k))
    | _ => none

def closeStep (base k off : Nat) (fe : FExpr) : Option FExpr :=
  if fe.fvarRange ≤ base then some fe
  else match fe with
    | .fvar i => some (if base ≤ i ∧ i < base + k then .bvar (k - 1 - (i - base) + off) else fe)
    | _ => none

structure OpenClose where
  opens : ReplaceCache := {}
  closes : ReplaceCache := {}

unsafe def OpenClose.openShared (base k : Nat) (fe : FExpr) : OpenClose → FExpr × OpenClose
  | ⟨opens, closes⟩ =>
    if k = 0 then (fe, ⟨opens, closes⟩) else
    let (r, opens) := (replaceCached (openStep base k) 0 fe).run
      { opens with keep := true, span := some k }
    (r, ⟨opens, closes⟩)

unsafe def OpenClose.closeShared (base k : Nat) (fe : FExpr) : OpenClose → FExpr × OpenClose
  | ⟨opens, closes⟩ =>
    if k = 0 then (fe, ⟨opens, closes⟩) else
    let inverse := opens.inverse
    let step (off : Nat) (fe : FExpr) : Option FExpr :=
      match closeStep base k off fe with
      | some r => some r
      | none => inverse.get? (ReplaceCache.key (ptrAddrUnsafe fe) off)
    let (r, closes) := (replaceCached step 0 fe).run { closes with keep := true }
    (r, ⟨opens, closes⟩)

opaque closeFVars (base k : Nat) (fe : FExpr) : FExpr :=
  if k = 0 then fe else unsafe replaceShared (closeStep base k) fe

mutual

@[implemented_by instAtShared]
def instAt (fa : FExpr) (d : Nat) (fe : FExpr) : FExpr :=
  if fe.data.looseBVarRange.toNat ≤ d ∧ fe.data.looseBVarRange.toNat < Data.maxRange then fe
  else instAtCore fa d fe
termination_by (sizeOf fe, 1)

def instAtCore (fa : FExpr) (d : Nat) : FExpr → FExpr
  | .bvar i => if i < d then .bvar i else if i = d then fa else .bvar (i - 1)
  | .fvar i => .fvar i
  | .sort l => .sort l
  | .const pos ls => .const pos ls
  | .ind pos s ls ps is => .ind pos s ls (ps.map (instAt fa d)) (is.map (instAt fa d))
  | .ctor pos s c ls ps fds recFds =>
    .ctor pos s c ls (ps.map (instAt fa d)) (fds.map (instAt fa d)) (recFds.map (instAt fa d))
  | .recr pos s ls l ps ms mins is maj =>
    .recr pos s ls l
      (ps.map (instAt fa d))
      (ms.map (instAt fa d))
      (mins.map (instAt fa d))
      (is.map (instAt fa d))
      (instAt fa d maj)
  | .quot pos l α r => .quot pos l (instAt fa d α) (instAt fa d r)
  | .quotMk pos l α r x => .quotMk pos l (instAt fa d α) (instAt fa d r) (instAt fa d x)
  | .quotLift pos l₁ l₂ α r β f h x =>
    .quotLift pos l₁ l₂
      (instAt fa d α)
      (instAt fa d r)
      (instAt fa d β)
      (instAt fa d f)
      (instAt fa d h)
      (instAt fa d x)
  | .quotInd pos l α r β f x =>
    .quotInd pos l (instAt fa d α) (instAt fa d r) (instAt fa d β) (instAt fa d f) (instAt fa d x)
  | .proj pos s idx x => .proj pos s idx (instAt fa d x)
  | .app f x => .app (instAt fa d f) (instAt fa d x)
  | .lam t b => .lam (instAt fa d t) (instAt fa (d + 1) b)
  | .forallE t b => .forallE (instAt fa d t) (instAt fa (d + 1) b)
  | .letE t v b => .letE (instAt fa d t) (instAt fa d v) (instAt fa (d + 1) b)
  | .natLit num => .natLit num
  | .strLit str => .strLit str
termination_by fe => (sizeOf fe, 0)

end

mutual

@[implemented_by abstractAtShared]
def abstractAt (x d : Nat) (fe : FExpr) : FExpr :=
  if fe.data.hasFVar then abstractAtCore x d fe else fe
termination_by (sizeOf fe, 1)

def abstractAtCore (x d : Nat) : FExpr → FExpr
  | .bvar i => .bvar i
  | .fvar i => if i = x then .bvar d else .fvar i
  | .sort l => .sort l
  | .const pos ls => .const pos ls
  | .ind pos s ls ps is => .ind pos s ls (ps.map (abstractAt x d)) (is.map (abstractAt x d))
  | .ctor pos s c ls ps fds recFds =>
    .ctor pos s c ls
      (ps.map (abstractAt x d))
      (fds.map (abstractAt x d))
      (recFds.map (abstractAt x d))
  | .recr pos s ls l ps ms mins is maj =>
    .recr pos s ls l
      (ps.map (abstractAt x d))
      (ms.map (abstractAt x d))
      (mins.map (abstractAt x d))
      (is.map (abstractAt x d))
      (abstractAt x d maj)
  | .quot pos l α r => .quot pos l (abstractAt x d α) (abstractAt x d r)
  | .quotMk pos l α r y => .quotMk pos l (abstractAt x d α) (abstractAt x d r) (abstractAt x d y)
  | .quotLift pos l₁ l₂ α r β f h y =>
    .quotLift pos l₁ l₂
      (abstractAt x d α)
      (abstractAt x d r)
      (abstractAt x d β)
      (abstractAt x d f)
      (abstractAt x d h)
      (abstractAt x d y)
  | .quotInd pos l α r β f y =>
    .quotInd pos l
      (abstractAt x d α)
      (abstractAt x d r)
      (abstractAt x d β)
      (abstractAt x d f)
      (abstractAt x d y)
  | .proj pos s idx y => .proj pos s idx (abstractAt x d y)
  | .app f y => .app (abstractAt x d f) (abstractAt x d y)
  | .lam t b => .lam (abstractAt x d t) (abstractAt x (d + 1) b)
  | .forallE t b => .forallE (abstractAt x d t) (abstractAt x (d + 1) b)
  | .letE t v b => .letE (abstractAt x d t) (abstractAt x d v) (abstractAt x (d + 1) b)
  | .natLit num => .natLit num
  | .strLit str => .strLit str
termination_by fe => (sizeOf fe, 0)

end

unsafe def openBVarsShared (base k : Nat) (fe : FExpr) : FExpr :=
  if k = 0 then fe else replaceShared (openStep base k) fe

@[implemented_by openBVarsShared]
def openBVars (base : Nat) : (k : Nat) → FExpr → FExpr
  | 0, fe => fe
  | k + 1, fe => openBVars (base + 1) k (instAt (.fvar base) k fe)

@[implemented_by OpenClose.openShared]
def OpenClose.open (base k : Nat) (fe : FExpr) (c : OpenClose) : FExpr × OpenClose :=
  (openBVars base k fe, c)

@[implemented_by OpenClose.closeShared]
def OpenClose.close (base k : Nat) (fe : FExpr) (c : OpenClose) : FExpr × OpenClose :=
  (closeFVars base k fe, c)

def mkPiClosed (m : Nat) (ty : FExpr) (j : Nat) : List FExpr → FExpr
  | [] => closeFVars m j ty
  | d :: ds => .forallE (closeFVars m j d) (mkPiClosed m ty (j + 1) ds)

def mkPiBatched (m : Nat) (ty : FExpr) (ds : List FExpr) : FExpr :=
  mkPiClosed m ty 0 ds

@[implemented_by mkPiBatched]
def mkPi (m : Nat) (ty : FExpr) : List FExpr → FExpr
  | [] => ty
  | d :: ds => .forallE d (abstractAt m 0 (mkPi (m + 1) ty ds))

abbrev InstLM := StateM (Std.HashMap USize FExpr)

mutual

unsafe def instLCached (us : Array FLevel) (fe : FExpr) : InstLM FExpr := do
  if !fe.data.hasLevelParam then return fe
  if isExclusiveUnsafe fe then return ← instLCoreShared us fe
  let key := ptrAddrUnsafe fe
  if let some r := (← get).get? key then return r
  let r ← instLCoreShared us fe
  modify (·.insert key r)
  return r

unsafe def instLArray (us : Array FLevel) (xs : Array FExpr) : InstLM (Array FExpr) :=
  xs.mapM (instLCached us)

unsafe def instLCoreShared (us : Array FLevel) : FExpr → InstLM FExpr
  | .sort l => pure (.sort (l.inst us))
  | .const pos ls => pure (.const pos (ls.map (·.inst us)))
  | .ind pos s ls ps is => do
    pure (.ind pos s (ls.map (·.inst us)) (← instLArray us ps) (← instLArray us is))
  | .ctor pos s c ls ps fds recFds => do
    pure (.ctor pos s c (ls.map (·.inst us)) (← instLArray us ps) (← instLArray us fds)
      (← instLArray us recFds))
  | .recr pos s ls l ps ms mins is maj => do
    pure (.recr pos s (ls.map (·.inst us)) (l.inst us) (← instLArray us ps) (← instLArray us ms)
      (← instLArray us mins) (← instLArray us is) (← instLCached us maj))
  | .quot pos l α r => do
    pure (.quot pos (l.inst us) (← instLCached us α) (← instLCached us r))
  | .quotMk pos l α r a => do
    pure (.quotMk pos (l.inst us) (← instLCached us α) (← instLCached us r) (← instLCached us a))
  | .quotLift pos l₁ l₂ α r β f h a => do
    pure (.quotLift pos (l₁.inst us) (l₂.inst us) (← instLCached us α) (← instLCached us r)
      (← instLCached us β) (← instLCached us f) (← instLCached us h) (← instLCached us a))
  | .quotInd pos l α r β f a => do
    pure (.quotInd pos (l.inst us) (← instLCached us α) (← instLCached us r)
      (← instLCached us β) (← instLCached us f) (← instLCached us a))
  | .proj pos s idx a => do
    pure (.proj pos s idx (← instLCached us a))
  | .app f a => do pure (.app (← instLCached us f) (← instLCached us a))
  | .lam t b => do pure (.lam (← instLCached us t) (← instLCached us b))
  | .forallE t b => do pure (.forallE (← instLCached us t) (← instLCached us b))
  | .letE t v b => do
    pure (.letE (← instLCached us t) (← instLCached us v) (← instLCached us b))
  | fe => pure fe

end

unsafe def instLShared (us : Array FLevel) (fe : FExpr) : FExpr :=
  (instLCached us fe).run' ∅

mutual

@[implemented_by instLShared]
def instL (us : Array FLevel) (fe : FExpr) : FExpr :=
  if fe.data.hasLevelParam then instLCore us fe else fe
termination_by (sizeOf fe, 1)

def instLCore (us : Array FLevel) : FExpr → FExpr
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .sort l => .sort (l.inst us)
  | .const pos ls => .const pos (ls.map (·.inst us))
  | .ind pos s ls ps is => .ind pos s (ls.map (·.inst us)) (ps.map (instL us)) (is.map (instL us))
  | .ctor pos s c ls ps fds recFds =>
    .ctor pos s c
      (ls.map (·.inst us))
      (ps.map (instL us))
      (fds.map (instL us))
      (recFds.map (instL us))
  | .recr pos s ls l ps ms mins is maj =>
    .recr pos s
      (ls.map (·.inst us))
      (l.inst us)
      (ps.map (instL us))
      (ms.map (instL us))
      (mins.map (instL us))
      (is.map (instL us))
      (instL us maj)
  | .quot pos l α r => .quot pos (l.inst us) (instL us α) (instL us r)
  | .quotMk pos l α r a => .quotMk pos (l.inst us) (instL us α) (instL us r) (instL us a)
  | .quotLift pos l₁ l₂ α r β f h a =>
    .quotLift pos
      (l₁.inst us)
      (l₂.inst us)
      (instL us α)
      (instL us r)
      (instL us β)
      (instL us f)
      (instL us h)
      (instL us a)
  | .quotInd pos l α r β f a =>
    .quotInd pos (l.inst us) (instL us α) (instL us r) (instL us β) (instL us f) (instL us a)
  | .proj pos s idx a => .proj pos s idx (instL us a)
  | .app f a => .app (instL us f) (instL us a)
  | .lam t b => .lam (instL us t) (instL us b)
  | .forallE t b => .forallE (instL us t) (instL us b)
  | .letE t v b => .letE (instL us t) (instL us v) (instL us b)
  | .natLit num => .natLit num
  | .strLit str => .strLit str
termination_by fe => (sizeOf fe, 0)

end

theorem instAt_of_closed (a : FExpr) (d : Nat) {fe : FExpr}
    (h : fe.data.looseBVarRange.toNat ≤ d ∧ fe.data.looseBVarRange.toNat < Data.maxRange) :
    instAt a d fe = fe := by
  simp [instAt, h]

theorem instAt_of_not_closed (a : FExpr) (d : Nat) {fe : FExpr}
    (h : ¬(fe.data.looseBVarRange.toNat ≤ d ∧ fe.data.looseBVarRange.toNat < Data.maxRange)) :
    instAt a d fe = instAtCore a d fe := by
  simp [instAt, h]

theorem instAt_lam (a : FExpr) (d : Nat) (t b : FExpr) :
    instAt a d (.lam t b) = .lam (instAt a d t) (instAt a (d + 1) b) := by
  by_cases hc : (FExpr.lam t b).data.looseBVarRange.toNat ≤ d ∧
      (FExpr.lam t b).data.looseBVarRange.toNat < Data.maxRange
  · have hc' := hc
    rw [data_lam] at hc'
    have ⟨ht, hb⟩ := Data.closed_of_mkBinder hc'.1 hc'.2
    rw [instAt_of_closed a d hc, instAt_of_closed a d ht, instAt_of_closed a (d + 1) hb]
  · rw [instAt_of_not_closed a d hc]
    simp [instAtCore]

theorem instAt_forallE (a : FExpr) (d : Nat) (t b : FExpr) :
    instAt a d (.forallE t b) = .forallE (instAt a d t) (instAt a (d + 1) b) := by
  by_cases hc : (FExpr.forallE t b).data.looseBVarRange.toNat ≤ d ∧
      (FExpr.forallE t b).data.looseBVarRange.toNat < Data.maxRange
  · have hc' := hc
    rw [data_forallE] at hc'
    have ⟨ht, hb⟩ := Data.closed_of_mkBinder hc'.1 hc'.2
    rw [instAt_of_closed a d hc, instAt_of_closed a d ht, instAt_of_closed a (d + 1) hb]
  · rw [instAt_of_not_closed a d hc]
    simp [instAtCore]

def instManyAt (d : Nat) : List FExpr → FExpr → FExpr
  | [], b => b
  | a :: as, b => instManyAt d as (instAt a (as.length + d) b)

theorem instManyAt_forallE (d : Nat) (as : List FExpr) (t b : FExpr) :
    instManyAt d as (.forallE t b) = .forallE (instManyAt d as t) (instManyAt (d + 1) as b) := by
  induction as generalizing t b with
  | nil => rfl
  | cons a as ih =>
    simp only [instManyAt]
    rw [instAt_forallE, ih, Nat.add_assoc]

theorem instAt_instManyAt (d : Nat) (as : List FExpr) (a b : FExpr) :
    instAt a d (instManyAt (d + 1) as b) = instManyAt d (as ++ [a]) b := by
  induction as generalizing b with
  | nil => simp [instManyAt]
  | cons a' as ih =>
    simp only [instManyAt, List.cons_append, List.length_append, List.length_cons,
      List.length_nil]
    rw [ih]
    congr 2
    omega

theorem instAt_letE (a : FExpr) (d : Nat) (t v b : FExpr) :
    instAt a d (.letE t v b) = .letE (instAt a d t) (instAt a d v) (instAt a (d + 1) b) := by
  by_cases hc : (FExpr.letE t v b).data.looseBVarRange.toNat ≤ d ∧
      (FExpr.letE t v b).data.looseBVarRange.toNat < Data.maxRange
  · have hc' := hc
    rw [data_letE] at hc'
    have ⟨ht, hv, hb⟩ := Data.closed_of_mkLet hc'.1 hc'.2
    rw [instAt_of_closed a d hc, instAt_of_closed a d ht, instAt_of_closed a d hv,
      instAt_of_closed a (d + 1) hb]
  · rw [instAt_of_not_closed a d hc]
    simp [instAtCore]

theorem instManyAt_letE (d : Nat) (as : List FExpr) (t v b : FExpr) :
    instManyAt d as (.letE t v b) =
      .letE (instManyAt d as t) (instManyAt d as v) (instManyAt (d + 1) as b) := by
  induction as generalizing t v b with
  | nil => rfl
  | cons a as ih =>
    simp only [instManyAt]
    rw [instAt_letE, ih, Nat.add_assoc]

def instManyIter (as : List FExpr) (b : FExpr) : FExpr :=
  instManyAt 0 as b

unsafe def instManyShared (as : List FExpr) (b : FExpr) : FExpr :=
  let args := as.toArray
  let m := args.size
  if m = 0 then b
  else if args.all (·.data.looseBVarRange == 0) then
    replaceShared (fun off fe =>
      if fe.data.looseBVarRange.toNat ≤ off ∧ fe.data.looseBVarRange.toNat < Data.maxRange then
        some fe
      else match fe with
        | .bvar i =>
          some (if i < off then fe
            else if h : i - off < m then args[m - 1 - (i - off)]
            else .bvar (i - m))
        | _ => none) b
  else instManyIter as b

@[implemented_by instManyShared]
def instMany (as : List FExpr) (b : FExpr) : FExpr :=
  instManyIter as b

unsafe def instManyRevShared (rev : List FExpr) (b : FExpr) : FExpr :=
  instManyShared rev.reverse b

@[implemented_by instManyRevShared]
def instManyRev (rev : List FExpr) (b : FExpr) : FExpr :=
  instManyAt 0 rev.reverse b

theorem instManyRev_cons_forallE (rev : List FExpr) (a t b : FExpr) :
    ∃ t', instManyRev rev (.forallE t b) = .forallE t' (instManyAt 1 rev.reverse b) ∧
      instAt a 0 (instManyAt 1 rev.reverse b) = instManyRev (a :: rev) b := by
  refine ⟨_, instManyAt_forallE 0 rev.reverse t b, ?_⟩
  rw [instManyRev, List.reverse_cons]
  exact instAt_instManyAt 0 rev.reverse a b

theorem instManyRev_letE (rev : List FExpr) (t v b : FExpr) :
    instManyRev rev (.letE t v b) =
        .letE (instManyRev rev t) (instManyRev rev v) (instManyAt 1 rev.reverse b) ∧
      instAt (instManyRev rev v) 0 (instManyAt 1 rev.reverse b) =
        instManyRev (instManyRev rev v :: rev) b := by
  refine ⟨instManyAt_letE 0 rev.reverse t v b, ?_⟩
  rw [instManyRev, instManyRev, List.reverse_cons]
  exact instAt_instManyAt 0 rev.reverse _ b

inductive LamBody : Nat → FExpr → FExpr → Prop where
  | zero {b : FExpr} :
    LamBody 0 b b
  | succ {m : Nat} {t f b : FExpr} :
    LamBody m f b →
    LamBody (m + 1) (.lam t f) b

theorem LamBody.instAt {m : Nat} {f b : FExpr} (a : FExpr) (d : Nat) :
    LamBody m f b →
    LamBody m (FExpr.instAt a d f) (FExpr.instAt a (d + m) b) := by
  intro h
  induction h generalizing d with
  | zero => exact .zero
  | @succ m _ _ _ _ ih =>
    rw [instAt_lam]
    have := ih (d + 1)
    rw [show d + 1 + m = d + (m + 1) by omega] at this
    exact .succ this

theorem abstractAt_of_hasFVar (x d : Nat) {fe : FExpr} (h : fe.data.hasFVar = true) :
    abstractAt x d fe = abstractAtCore x d fe := by
  simp [abstractAt, h]

theorem abstractAt_of_not_hasFVar (x d : Nat) {fe : FExpr} (h : fe.data.hasFVar = false) :
    abstractAt x d fe = fe := by
  simp [abstractAt, h]

theorem instL_of_hasLevelParam (us : Array FLevel) {fe : FExpr} (h : fe.data.hasLevelParam = true) :
    instL us fe = instLCore us fe := by
  simp [instL, h]

theorem instL_of_not_hasLevelParam (us : Array FLevel) {fe : FExpr}
    (h : fe.data.hasLevelParam = false) :
    instL us fe = fe := by
  simp [instL, h]

unsafe def instFVarsShared (args : Array FExpr) (fe : FExpr) : FExpr :=
  replaceShared (fun _ fe =>
    if !fe.data.hasFVar then some fe
    else match fe with
      | .fvar i => some (args[i]?.getD fe)
      | _ => none) fe

def instFVarsCore (args : Array FExpr) : FExpr → FExpr
  | .bvar i => .bvar i
  | .fvar i => args[i]?.getD (.fvar i)
  | .sort l => .sort l
  | .const pos ls => .const pos ls
  | .ind pos s ls ps is => .ind pos s ls (ps.map (instFVarsCore args)) (is.map (instFVarsCore args))
  | .ctor pos s c ls ps fds recFds =>
    .ctor pos s c ls
      (ps.map (instFVarsCore args))
      (fds.map (instFVarsCore args))
      (recFds.map (instFVarsCore args))
  | .recr pos s ls l ps ms mins is maj =>
    .recr pos s ls l
      (ps.map (instFVarsCore args))
      (ms.map (instFVarsCore args))
      (mins.map (instFVarsCore args))
      (is.map (instFVarsCore args))
      (instFVarsCore args maj)
  | .quot pos l α r => .quot pos l (instFVarsCore args α) (instFVarsCore args r)
  | .quotMk pos l α r a => .quotMk pos l (instFVarsCore args α) (instFVarsCore args r) (instFVarsCore args a)
  | .quotLift pos l₁ l₂ α r β f h a =>
    .quotLift pos l₁ l₂
      (instFVarsCore args α)
      (instFVarsCore args r)
      (instFVarsCore args β)
      (instFVarsCore args f)
      (instFVarsCore args h)
      (instFVarsCore args a)
  | .quotInd pos l α r β f a =>
    .quotInd pos l
      (instFVarsCore args α)
      (instFVarsCore args r)
      (instFVarsCore args β)
      (instFVarsCore args f)
      (instFVarsCore args a)
  | .proj pos s idx a => .proj pos s idx (instFVarsCore args a)
  | .app f a => .app (instFVarsCore args f) (instFVarsCore args a)
  | .lam t b => .lam (instFVarsCore args t) (instFVarsCore args b)
  | .forallE t b => .forallE (instFVarsCore args t) (instFVarsCore args b)
  | .letE t v b => .letE (instFVarsCore args t) (instFVarsCore args v) (instFVarsCore args b)
  | .natLit num => .natLit num
  | .strLit str => .strLit str

@[implemented_by instFVarsShared]
def instFVars (args : Array FExpr) (fe : FExpr) : FExpr :=
  instFVarsCore args fe

def apps (f : FExpr) (args : Array FExpr) : FExpr :=
  Fin.foldl args.size (fun e i => .app e args[i]) f

def fvars (n k : Nat) : Array FExpr :=
  Array.ofFn fun i : Fin k => .fvar (n + i.val)

def teleAux (binder : FExpr → FExpr → FExpr) (n : Nat) (tys : Array FExpr) :
    (j : Nat) → j ≤ tys.size → FExpr → FExpr
  | 0 => fun _ body => body
  | j + 1 => fun h body =>
    teleAux binder n tys j (by omega) (binder tys[j] (abstractAt (n + j) 0 body))

def piTele (n : Nat) (tys : Array FExpr) (body : FExpr) : FExpr :=
  teleAux .forallE n tys tys.size le_rfl body

def lamTele (n : Nat) (tys : Array FExpr) (body : FExpr) : FExpr :=
  teleAux .lam n tys tys.size le_rfl body

theorem teleAux_push (binder : FExpr → FExpr → FExpr) (n : Nat) (tys : Array FExpr) (ft : FExpr)
    (j : Nat) (h : j ≤ tys.size) (body : FExpr) :
    teleAux binder n (tys.push ft) j (by simp; omega) body = teleAux binder n tys j h body := by
  induction j generalizing body with
  | zero => rfl
  | succ j ih =>
    simp only [teleAux]
    rw [Array.getElem_push_lt (show j < tys.size by omega)]
    exact ih (by omega) _

@[simp] theorem size_fvars (n k : Nat) : (fvars n k).size = k := by
  simp [fvars]

@[simp] theorem getElem_fvars (n k i : Nat) (h : i < (fvars n k).size) :
    (fvars n k)[i] = .fvar (n + i) := by
  simp [fvars]

unsafe def ReplaceCache.instFVarsShared (args : Array FExpr) (fe : FExpr) (c : ReplaceCache) :
    FExpr × ReplaceCache :=
  (replaceCached (fun _ fe =>
    if !fe.data.hasFVar then some fe
    else match fe with
      | .fvar i => some (args[i]?.getD fe)
      | _ => none) 0 fe).run { c with keep := true }

@[implemented_by ReplaceCache.instFVarsShared]
def ReplaceCache.instFVars (args : Array FExpr) (fe : FExpr) (c : ReplaceCache) :
    FExpr × ReplaceCache :=
  (fe.instFVars args, c)

def appList (f : FExpr) (args : List FExpr) : FExpr :=
  args.foldl .app f

unsafe def addrImpl (fe : FExpr) : USize :=
  ptrAddrUnsafe fe

@[implemented_by addrImpl]
opaque addr (fe : FExpr) : USize

def peelLams : (max : Nat) → (f : FExpr) → (m : Nat) × {b : FExpr // LamBody m f b ∧ m ≤ max}
  | max + 1, .lam _ f =>
    let ⟨m, b, h⟩ := peelLams max f
    ⟨m + 1, b, .succ h.1, by omega⟩
  | _, f => ⟨0, f, .zero, Nat.zero_le _⟩

def spineAux : FExpr → List FExpr → FExpr × List FExpr
  | .app f a, acc => spineAux f (a :: acc)
  | f, acc => (f, acc)

theorem appList_spineAux (e : FExpr) (acc : List FExpr) :
    appList (spineAux e acc).1 (spineAux e acc).2 = appList e acc := by
  fun_induction spineAux e acc with
  | case1 f a acc ih => exact ih
  | case2 f acc _ => rfl

def spine (e : FExpr) : {p : FExpr × List FExpr // appList p.1 p.2 = e} :=
  ⟨spineAux e [], appList_spineAux e []⟩

def appHead : FExpr → FExpr
  | .app f _ => appHead f
  | fe => fe

def appArity : FExpr → Nat
  | .app f _ => appArity f + 1
  | _ => 0

end FExpr

end Metalean.FastChecker
