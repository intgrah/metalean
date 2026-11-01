/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.FExpr

@[expose] public section

namespace Metalean.Checker.Fast

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
  let mut ys := Array.mkEmpty xs.size
  let mut changed := false
  for x in xs do
    let y ← replaceCached pre off x
    changed := changed || !_root_.ptrEq x y
    ys := ys.push y
  return if changed then ys else xs

@[specialize] unsafe def replaceCoreShared (pre : Nat → FExpr → Option FExpr) (off : Nat) (fe : FExpr) :
    ReplaceM FExpr := do
  match fe with
  | .ind pos s ls ps is =>
    let ps' ← replaceArray pre off ps
    let is' ← replaceArray pre off is
    if _root_.ptrEq ps ps' && _root_.ptrEq is is' then pure fe else pure (.ind pos s ls ps' is')
  | .ctor pos s c ls ps fds recFds =>
    let ps' ← replaceArray pre off ps
    let fds' ← replaceArray pre off fds
    let recFds' ← replaceArray pre off recFds
    if _root_.ptrEq ps ps' && _root_.ptrEq fds fds' && _root_.ptrEq recFds recFds' then pure fe
    else pure (.ctor pos s c ls ps' fds' recFds')
  | .recr pos s ls l ps ms mins is maj =>
    let ps' ← replaceArray pre off ps
    let ms' ← replaceArray pre off ms
    let mins' ← replaceArray pre off mins
    let is' ← replaceArray pre off is
    let maj' ← replaceCached pre off maj
    if _root_.ptrEq ps ps' && _root_.ptrEq ms ms' && _root_.ptrEq mins mins' && _root_.ptrEq is is'
        && _root_.ptrEq maj maj' then pure fe
    else pure (.recr pos s ls l ps' ms' mins' is' maj')
  | .quot pos l α r =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    if _root_.ptrEq α α' && _root_.ptrEq r r' then pure fe else pure (.quot pos l α' r')
  | .quotMk pos l α r y =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    let y' ← replaceCached pre off y
    if _root_.ptrEq α α' && _root_.ptrEq r r' && _root_.ptrEq y y' then pure fe
    else pure (.quotMk pos l α' r' y')
  | .quotLift pos l₁ l₂ α r β f h y =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    let β' ← replaceCached pre off β
    let f' ← replaceCached pre off f
    let h' ← replaceCached pre off h
    let y' ← replaceCached pre off y
    if _root_.ptrEq α α' && _root_.ptrEq r r' && _root_.ptrEq β β' && _root_.ptrEq f f'
        && _root_.ptrEq h h' && _root_.ptrEq y y' then pure fe
    else pure (.quotLift pos l₁ l₂ α' r' β' f' h' y')
  | .quotInd pos l α r β f y =>
    let α' ← replaceCached pre off α
    let r' ← replaceCached pre off r
    let β' ← replaceCached pre off β
    let f' ← replaceCached pre off f
    let y' ← replaceCached pre off y
    if _root_.ptrEq α α' && _root_.ptrEq r r' && _root_.ptrEq β β' && _root_.ptrEq f f'
        && _root_.ptrEq y y' then pure fe
    else pure (.quotInd pos l α' r' β' f' y')
  | .proj pos s idx y =>
    let y' ← replaceCached pre off y
    if _root_.ptrEq y y' then pure fe else pure (.proj pos s idx y')
  | .app f y =>
    let f' ← replaceCached pre off f
    let y' ← replaceCached pre off y
    if _root_.ptrEq f f' && _root_.ptrEq y y' then pure fe else pure (.app f' y')
  | .lam t b =>
    let t' ← replaceCached pre off t
    let b' ← replaceCached pre (off + 1) b
    if _root_.ptrEq t t' && _root_.ptrEq b b' then pure fe else pure (.lam t' b')
  | .forallE t b =>
    let t' ← replaceCached pre off t
    let b' ← replaceCached pre (off + 1) b
    if _root_.ptrEq t t' && _root_.ptrEq b b' then pure fe else pure (.forallE t' b')
  | .letE t v b =>
    let t' ← replaceCached pre off t
    let v' ← replaceCached pre off v
    let b' ← replaceCached pre (off + 1) b
    if _root_.ptrEq t t' && _root_.ptrEq v v' && _root_.ptrEq b b' then pure fe
    else pure (.letE t' v' b')
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

variable {δ : Type*}

mutual

def rewrite (under : δ → δ) (pre : δ → FExpr → Option FExpr) (level : FLevel → FLevel)
    (d : δ) (fe : FExpr) : FExpr :=
  match pre d fe with
  | some r => r
  | none => rewriteCore under pre level d fe
termination_by (sizeOf fe, 1)

def rewriteCore (under : δ → δ) (pre : δ → FExpr → Option FExpr) (level : FLevel → FLevel)
    (d : δ) : FExpr → FExpr
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .sort l => .sort (level l)
  | .const pos ls => .const pos (ls.map level)
  | .ind pos s ls ps is =>
    .ind pos s (ls.map level)
      (ps.map (rewrite under pre level d)) (is.map (rewrite under pre level d))
  | .ctor pos s c ls ps fds recFds =>
    .ctor pos s c (ls.map level)
      (ps.map (rewrite under pre level d))
      (fds.map (rewrite under pre level d))
      (recFds.map (rewrite under pre level d))
  | .recr pos s ls l ps ms mins is maj =>
    .recr pos s (ls.map level) (level l)
      (ps.map (rewrite under pre level d))
      (ms.map (rewrite under pre level d))
      (mins.map (rewrite under pre level d))
      (is.map (rewrite under pre level d))
      (rewrite under pre level d maj)
  | .quot pos l α r => .quot pos (level l) (rewrite under pre level d α) (rewrite under pre level d r)
  | .quotMk pos l α r a =>
    .quotMk pos (level l)
      (rewrite under pre level d α) (rewrite under pre level d r) (rewrite under pre level d a)
  | .quotLift pos l₁ l₂ α r β f h a =>
    .quotLift pos (level l₁) (level l₂)
      (rewrite under pre level d α) (rewrite under pre level d r) (rewrite under pre level d β)
      (rewrite under pre level d f) (rewrite under pre level d h) (rewrite under pre level d a)
  | .quotInd pos l α r β f a =>
    .quotInd pos (level l)
      (rewrite under pre level d α) (rewrite under pre level d r) (rewrite under pre level d β)
      (rewrite under pre level d f) (rewrite under pre level d a)
  | .proj pos s idx a => .proj pos s idx (rewrite under pre level d a)
  | .app f a => .app (rewrite under pre level d f) (rewrite under pre level d a)
  | .lam t b => .lam (rewrite under pre level d t) (rewrite under pre level (under d) b)
  | .forallE t b => .forallE (rewrite under pre level d t) (rewrite under pre level (under d) b)
  | .letE t v b => .letE (rewrite under pre level d t) (rewrite under pre level d v) (rewrite under pre level (under d) b)
  | .natLit p num => .natLit p num
  | .strLit P str => .strLit P str
termination_by fe => (sizeOf fe, 0)

end

def instAtStep (fa : FExpr) (d : Nat) (fe : FExpr) : Option FExpr :=
  if fe.data.looseBVarRange.toNat ≤ d ∧ fe.data.looseBVarRange.toNat < Data.maxRange then some fe
  else match fe with
    | .bvar i => some (if i < d then fe else if i = d then fa else .bvar (i - 1))
    | .fvar _ => some fe
    | _ => none

@[implemented_by instAtShared]
def instAt (fa : FExpr) (d : Nat) (fe : FExpr) : FExpr :=
  rewrite Nat.succ (instAtStep fa) id d fe

def abstractAtStep (x d : Nat) (fe : FExpr) : Option FExpr :=
  if fe.fvarRange ≤ x then some fe
  else match fe with
    | .fvar i => some (if i = x then .bvar d else fe)
    | _ => none

@[implemented_by abstractAtShared]
def abstractAt (x d : Nat) (fe : FExpr) : FExpr :=
  rewrite Nat.succ (abstractAtStep x) id d fe


unsafe def openBVarsShared (base : Nat) (fe : FExpr) (k : Nat) : FExpr :=
  if k = 0 then fe else replaceShared (openStep base k) fe

@[implemented_by openBVarsShared]
def openBVars (base : Nat) (fe : FExpr) : (k : Nat) → FExpr
  | 0 => fe
  | k + 1 => openBVars (base + 1) (instAt (.fvar base) k fe) k

@[implemented_by OpenClose.openShared]
def OpenClose.open (base k : Nat) (fe : FExpr) (c : OpenClose) : FExpr × OpenClose :=
  (openBVars base fe k, c)

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
  | .sort l => pure (.sort l{us})
  | .const pos ls => pure (.const pos ls{us})
  | .ind pos s ls ps is => do
    pure (.ind pos s ls{us} (← instLArray us ps) (← instLArray us is))
  | .ctor pos s c ls ps fds recFds => do
    pure (.ctor pos s c ls{us} (← instLArray us ps) (← instLArray us fds)
      (← instLArray us recFds))
  | .recr pos s ls l ps ms mins is maj => do
    pure (.recr pos s ls{us} l{us} (← instLArray us ps) (← instLArray us ms)
      (← instLArray us mins) (← instLArray us is) (← instLCached us maj))
  | .quot pos l α r => do
    pure (.quot pos l{us} (← instLCached us α) (← instLCached us r))
  | .quotMk pos l α r a => do
    pure (.quotMk pos l{us} (← instLCached us α) (← instLCached us r) (← instLCached us a))
  | .quotLift pos l₁ l₂ α r β f h a => do
    pure (.quotLift pos l₁{us} l₂{us} (← instLCached us α) (← instLCached us r)
      (← instLCached us β) (← instLCached us f) (← instLCached us h) (← instLCached us a))
  | .quotInd pos l α r β f a => do
    pure (.quotInd pos l{us} (← instLCached us α) (← instLCached us r)
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

def instLStep (_ : Unit) : FExpr → Option FExpr
  | fe@(.bvar _) | fe@(.fvar _) => some fe
  | _ => none

@[implemented_by instLShared]
def instL (us : Array FLevel) (fe : FExpr) : FExpr :=
  rewrite id instLStep (·{us}) () fe


instance : InstLevel (Array FLevel) FExpr FExpr := ⟨FExpr.instL⟩

theorem instAt_of_closed (a : FExpr) (d : Nat) {fe : FExpr}
    (h : fe.data.looseBVarRange.toNat ≤ d ∧ fe.data.looseBVarRange.toNat < Data.maxRange) :
    instAt a d fe = fe := by
  simp [instAt, rewrite, instAtStep, h]

theorem instAt_lam (a : FExpr) (d : Nat) (t b : FExpr) :
    instAt a d (.lam t b) = .lam (instAt a d t) (instAt a (d + 1) b) := by
  by_cases hc : (FExpr.lam t b).data.looseBVarRange.toNat ≤ d ∧
      (FExpr.lam t b).data.looseBVarRange.toNat < Data.maxRange
  · have hc' := hc
    rw [data_lam] at hc'
    have ⟨ht, hb⟩ := Data.closed_of_mkBinder hc'.1 hc'.2
    rw [instAt_of_closed a d hc, instAt_of_closed a d ht, instAt_of_closed a (d + 1) hb]
  · unfold instAt
    rw [rewrite]
    simp only [instAtStep, ite_eq_right hc]
    simp [rewriteCore]

theorem instAt_forallE (a : FExpr) (d : Nat) (t b : FExpr) :
    instAt a d (.forallE t b) = .forallE (instAt a d t) (instAt a (d + 1) b) := by
  by_cases hc : (FExpr.forallE t b).data.looseBVarRange.toNat ≤ d ∧
      (FExpr.forallE t b).data.looseBVarRange.toNat < Data.maxRange
  · have hc' := hc
    rw [data_forallE] at hc'
    have ⟨ht, hb⟩ := Data.closed_of_mkBinder hc'.1 hc'.2
    rw [instAt_of_closed a d hc, instAt_of_closed a d ht, instAt_of_closed a (d + 1) hb]
  · unfold instAt
    rw [rewrite]
    simp only [instAtStep, ite_eq_right hc]
    simp [rewriteCore]

def instManyAt (d : Nat) (b : FExpr) : List FExpr → FExpr
  | [] => b
  | a :: as => instManyAt d (instAt a (as.length + d) b) as

theorem instManyAt_forallE (d : Nat) (as : List FExpr) (t b : FExpr) :
    instManyAt d (.forallE t b) as = .forallE (instManyAt d t as) (instManyAt (d + 1) b as) := by
  induction as generalizing t b with
  | nil => rfl
  | cons a as ih =>
    simp only [instManyAt]
    rw [instAt_forallE, ih, Nat.add_assoc]

theorem instAt_instManyAt (d : Nat) (as : List FExpr) (a b : FExpr) :
    instAt a d (instManyAt (d + 1) b as) = instManyAt d b (as ++ [a]) := by
  induction as generalizing b with
  | nil => simp!
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
  · unfold instAt
    rw [rewrite]
    simp only [instAtStep, ite_eq_right hc]
    simp [rewriteCore]

theorem instManyAt_letE (d : Nat) (as : List FExpr) (t v b : FExpr) :
    instManyAt d (.letE t v b) as =
      .letE (instManyAt d t as) (instManyAt d v as) (instManyAt (d + 1) b as) := by
  induction as generalizing t v b with
  | nil => rfl
  | cons a as ih =>
    simp only [instManyAt]
    rw [instAt_letE, ih, Nat.add_assoc]

def instManyIter (as : List FExpr) (b : FExpr) : FExpr :=
  instManyAt 0 b as

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
  instManyAt 0 b rev.reverse

theorem instManyRev_cons_forallE (rev : List FExpr) (a t b : FExpr) :
    ∃ t', instManyRev rev (.forallE t b) = .forallE t' (instManyAt 1 b rev.reverse) ∧
      instAt a 0 (instManyAt 1 b rev.reverse) = instManyRev (a :: rev) b := by
  refine ⟨_, instManyAt_forallE 0 rev.reverse t b, ?_⟩
  rw [instManyRev, List.reverse_cons]
  exact instAt_instManyAt 0 rev.reverse a b

theorem instManyRev_letE (rev : List FExpr) (t v b : FExpr) :
    instManyRev rev (.letE t v b) =
        .letE (instManyRev rev t) (instManyRev rev v) (instManyAt 1 b rev.reverse) ∧
      instAt (instManyRev rev v) 0 (instManyAt 1 b rev.reverse) =
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

theorem abstractAt_of_not_hasFVar (x d : Nat) {fe : FExpr} (h : fe.data.hasFVar = false) :
    abstractAt x d fe = fe := by
  simp [abstractAt, rewrite, abstractAtStep, (hasFVar_eq_false_iff fe).mp h]

theorem instL_of_not_hasLevelParam (us : Array FLevel) {fe : FExpr}
    (h : fe.data.hasLevelParam = false) :
    instL us fe = fe := by
  induction fe using FExpr.rec
      (motive_2 := fun es => ∀ e ∈ es, e.data.hasLevelParam = false → instL us e = e)
      (motive_3 := fun es => ∀ e ∈ es, e.data.hasLevelParam = false → instL us e = e)
  case mk es ih e he hp => exact ih e (Array.mem_def.mp he) hp
  case nil e he hp => cases he
  case cons head tail ih₁ ih₂ e he hp =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ih₁ hp
    · exact ih₂ e he hp
  all_goals simp only [instL] at *
  all_goals rw [rewrite]
  all_goals simp_all [instLStep, rewriteCore, Data.hasLevelParam_mk,
    Data.hasLevelParam_mkApp, Data.hasLevelParam_mkBinder, Data.hasLevelParam_mkLet,
    Data.hasLevelParam_mkArr_eq_false, FLevel.inst_of_not_hasParam, or_imp, forall_and]
  all_goals repeat' apply And.intro
  all_goals apply Array.ext (by simp)
  all_goals intro i hi hi'
  all_goals simp_all [FLevel.inst_of_not_hasParam, Array.getElem_mem]

unsafe def instFVarsShared (args : Array FExpr) (fe : FExpr) : FExpr :=
  replaceShared (fun _ fe =>
    if !fe.data.hasFVar then some fe
    else match fe with
      | .fvar i => some (args[i]?.getD fe)
      | _ => none) fe

def instFVarsStep (args : Array FExpr) (_ : Unit) (fe : FExpr) : Option FExpr :=
  match fe with
  | .bvar _ => some fe
  | .fvar i => some (args[i]?.getD fe)
  | _ => none

@[reducible, implemented_by instFVarsShared]
def instFVars (args : Array FExpr) (fe : FExpr) : FExpr :=
  rewrite id (instFVarsStep args) id () fe

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

def peelLams : (max : Nat) → (f : FExpr) → (m : Nat) × {b : FExpr // LamBody m f b ∧ m ≤ max}
  | max + 1, .lam _ f =>
    let ⟨m, b, h⟩ := peelLams max f
    ⟨m + 1, b, .succ h.1, by omega⟩
  | _, f => ⟨0, f, .zero, Nat.zero_le _⟩

def spineAux (acc : List FExpr) : FExpr → FExpr × List FExpr
  | .app f a => spineAux (a :: acc) f
  | f => (f, acc)

theorem appList_spineAux (e : FExpr) (acc : List FExpr) :
    appList (spineAux acc e).1 (spineAux acc e).2 = appList e acc := by
  fun_induction spineAux acc e with
  | case1 f a acc ih => exact ih
  | case2 f acc _ => rfl

def spine (e : FExpr) : {p : FExpr × List FExpr // appList p.1 p.2 = e} :=
  ⟨spineAux [] e, appList_spineAux e []⟩

def appHead : FExpr → FExpr
  | .app f _ => appHead f
  | fe => fe

def appArity : FExpr → Nat
  | .app f _ => appArity f + 1
  | _ => 0

end FExpr

end Metalean.Checker.Fast
