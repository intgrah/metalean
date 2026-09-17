/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Literal
public import Metalean.FastChecker.Level
public import Metalean.Syntax.Env
public import Metalean.Syntax.Structure
import Metalean.Meta.Judgement
import Metalean.Meta.DeriveFunctor
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Lean.Meta.Constructions.CasesOnSameCtor

@[expose] public section

namespace Metalean.FastChecker

/--
Similar to `Lean.Expr.Data`

- [0..31], `hash`: hash truncated to 32 bits
- [32..39], `approxDepth`: term depth, saturating at 255
- [40], `hasFVar`: contains some subterm is a free variable
- [41..42], unused: `hasExprMVar` and `hasLevelMVar` in Lean, always 0 here because no mvars
- [43], `hasLevelParam`: some universe level mentions a parameter
- [44..63], `looseBVarRange`: one more than largest loose de Bruijn index, saturating at
  `maxRange`

`15 <<< 40` in `mkApp` is the mask for the flag 40..43
A `looseBVarRange` of `maxRange` stands for any range of `maxRange` or more, so `binderRange` does not decrement it.
-/
abbrev Data := UInt64

namespace Data

def maxRange : Nat := 2 ^ 20 - 1

def mk (h : UInt64) (looseBVarRange : Nat) (approxDepth : UInt32) (hasFVar hasLevelParam : Bool) :
    Data :=
  h.toUInt32.toUInt64 ||| ((if approxDepth ≤ 255 then approxDepth else 255).toUInt64 <<< 32) |||
    (hasFVar.toUInt64 <<< 40) ||| (hasLevelParam.toUInt64 <<< 43) |||
    ((min looseBVarRange maxRange).toUInt64 <<< 44)

def hash (d : Data) : UInt64 := d.toUInt32.toUInt64

def approxDepth (d : Data) : UInt32 := ((d >>> 32) &&& 255).toUInt32

def looseBVarRange (d : Data) : UInt32 := (d >>> 44).toUInt32

def hasFVar (d : Data) : Bool := ((d >>> 40) &&& 1) == 1

def hasLevelParam (d : Data) : Bool := ((d >>> 43) &&& 1) == 1

def mkApp (fData aData : Data) : Data :=
  let depth :=
    if fData.approxDepth ≤ aData.approxDepth then aData.approxDepth else fData.approxDepth
  let depth := if depth < 255 then depth + 1 else 255
  let range :=
    if fData.looseBVarRange ≤ aData.looseBVarRange then aData.looseBVarRange
    else fData.looseBVarRange
  ((fData ||| aData) &&& ((15 : UInt64) <<< 40)) |||
    (mixHash fData aData).toUInt32.toUInt64 ||| (depth.toUInt64 <<< 32) |||
    (range.toUInt64 <<< 44)

def binderRange (tData bData : Data) : Nat :=
  if bData.looseBVarRange.toNat = maxRange then maxRange
  else max tData.looseBVarRange.toNat (bData.looseBVarRange.toNat - 1)

def mkBinder (tData bData : Data) : Data :=
  let d :=
    (if tData.approxDepth ≤ bData.approxDepth then bData.approxDepth else tData.approxDepth) + 1
  mk (mixHash d.toUInt64 (mixHash tData.hash bData.hash)) (binderRange tData bData) d
    (tData.hasFVar || bData.hasFVar) (tData.hasLevelParam || bData.hasLevelParam)

def mkLet (tData vData bData : Data) : Data :=
  let d := (mkApp tData vData).approxDepth
  let d := (if d ≤ bData.approxDepth then bData.approxDepth else d) + 1
  mk (mixHash d.toUInt64 (mixHash tData.hash (mixHash vData.hash bData.hash)))
    (binderRange (mkApp tData vData) bData) d
    (tData.hasFVar || vData.hasFVar || bData.hasFVar)
    (tData.hasLevelParam || vData.hasLevelParam || bData.hasLevelParam)

def mkArr (h : UInt64) (hasLevelParam : Bool) (ds : Array Data) : Data :=
  ds.foldl mkApp (mk h 0 0 false hasLevelParam)

def levelsHash (init : UInt64) (ls : Array FLevel) : UInt64 :=
  ls.foldl (fun h l => mixHash h (Hashable.hash l)) init

theorem toNat_looseBVarRange_le (d : Data) : d.looseBVarRange.toNat ≤ maxRange := by
  have : d.looseBVarRange < 1048576 := by
    unfold looseBVarRange
    bv_decide
  rw [UInt32.lt_iff_toNat_lt] at this
  unfold maxRange
  simp at this
  omega

theorem toNat_looseBVarRange_mk (h : UInt64) (r : Nat) (dep : UInt32) (fv lp : Bool) :
    (mk h r dep fv lp).looseBVarRange.toNat = min r maxRange := by
  have hlt : min r maxRange < 1048576 := by
    unfold maxRange
    omega
  have hr : (min r maxRange).toUInt64.toNat = min r maxRange := by
    simp only [Nat.toUInt64_eq]
    exact UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  unfold mk looseBVarRange
  generalize (min r maxRange).toUInt64 = ru at hr ⊢
  have hru : ru < 1048576 := by
    rw [UInt64.lt_iff_toNat_lt, hr, UInt64.toNat_ofNat_of_lt (by decide)]
    exact hlt
  have hshift : (h.toUInt32.toUInt64 ||| (if dep ≤ 255 then dep else 255).toUInt64 <<< 32 |||
      fv.toUInt64 <<< 40 ||| lp.toUInt64 <<< 43 ||| ru <<< 44) >>> 44 = ru := by
    bv_decide
  rw [hshift, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega), hr]

theorem hasFVar_mk (h : UInt64) (r : Nat) (dep : UInt32) (fv lp : Bool) :
    (mk h r dep fv lp).hasFVar = fv := by
  unfold mk hasFVar
  bv_decide

theorem hasLevelParam_mk (h : UInt64) (r : Nat) (dep : UInt32) (fv lp : Bool) :
    (mk h r dep fv lp).hasLevelParam = lp := by
  unfold mk hasLevelParam
  bv_decide

theorem looseBVarRange_le_mkApp_left (f a : Data) :
    f.looseBVarRange ≤ (mkApp f a).looseBVarRange := by
  unfold mkApp looseBVarRange approxDepth
  bv_decide

theorem looseBVarRange_le_mkApp_right (f a : Data) :
    a.looseBVarRange ≤ (mkApp f a).looseBVarRange := by
  unfold mkApp looseBVarRange approxDepth
  bv_decide

theorem hasFVar_mkApp (f a : Data) : (mkApp f a).hasFVar = (f.hasFVar || a.hasFVar) := by
  unfold mkApp hasFVar looseBVarRange approxDepth
  bv_decide

theorem hasLevelParam_mkApp (f a : Data) :
    (mkApp f a).hasLevelParam = (f.hasLevelParam || a.hasLevelParam) := by
  unfold mkApp hasLevelParam looseBVarRange approxDepth
  bv_decide

theorem toNat_looseBVarRange_mkBinder (t b : Data) :
    (mkBinder t b).looseBVarRange.toNat = min (binderRange t b) maxRange :=
  toNat_looseBVarRange_mk ..

theorem hasFVar_mkBinder (t b : Data) : (mkBinder t b).hasFVar = (t.hasFVar || b.hasFVar) :=
  hasFVar_mk ..

theorem hasLevelParam_mkBinder (t b : Data) :
    (mkBinder t b).hasLevelParam = (t.hasLevelParam || b.hasLevelParam) :=
  hasLevelParam_mk ..

theorem toNat_looseBVarRange_mkLet (t v b : Data) :
    (mkLet t v b).looseBVarRange.toNat = min (binderRange (mkApp t v) b) maxRange :=
  toNat_looseBVarRange_mk ..

theorem hasFVar_mkLet (t v b : Data) :
    (mkLet t v b).hasFVar = (t.hasFVar || v.hasFVar || b.hasFVar) :=
  hasFVar_mk ..

theorem hasLevelParam_mkLet (t v b : Data) :
    (mkLet t v b).hasLevelParam = (t.hasLevelParam || v.hasLevelParam || b.hasLevelParam) :=
  hasLevelParam_mk ..

theorem looseBVarRange_le_mkArr (h : UInt64) (lp : Bool) (ds : Array Data) {d : Data}
    (hd : d ∈ ds) :
    d.looseBVarRange ≤ (mkArr h lp ds).looseBVarRange := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hd
  unfold mkArr
  refine Array.foldl_induction
    (motive := fun j (acc : Data) => ∀ i (hi : i < ds.size), i < j →
      ds[i].looseBVarRange ≤ acc.looseBVarRange)
    (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun j acc ih i hi hij => ?_)
    i hi hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | rfl
  · exact UInt32.le_trans (ih i hi hlt) (looseBVarRange_le_mkApp_left _ _)
  · exact looseBVarRange_le_mkApp_right _ _

theorem hasFVar_mkArr (h : UInt64) (lp : Bool) (ds : Array Data) {d : Data} (hd : d ∈ ds)
    (hf : d.hasFVar = true) :
    (mkArr h lp ds).hasFVar = true := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hd
  unfold mkArr
  refine Array.foldl_induction
    (motive := fun j (acc : Data) => ∀ i (hi : i < ds.size), i < j → ds[i].hasFVar = true →
      acc.hasFVar = true)
    (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun j acc ih i hi hij hf => ?_)
    i hi hi hf
  rw [hasFVar_mkApp]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | rfl
  · simp [ih i hi hlt hf]
  · simp [hf]

theorem hasLevelParam_mkArr_init (h : UInt64) (ds : Array Data) :
    (mkArr h true ds).hasLevelParam = true := by
  unfold mkArr
  refine Array.foldl_induction (motive := fun _ (acc : Data) => acc.hasLevelParam = true)
    (hasLevelParam_mk ..) fun _ acc ih => ?_
  rw [hasLevelParam_mkApp, ih]
  rfl

theorem hasLevelParam_mkArr (h : UInt64) (lp : Bool) (ds : Array Data) {d : Data} (hd : d ∈ ds)
    (hp : d.hasLevelParam = true) :
    (mkArr h lp ds).hasLevelParam = true := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hd
  unfold mkArr
  refine Array.foldl_induction
    (motive := fun j (acc : Data) => ∀ i (hi : i < ds.size), i < j → ds[i].hasLevelParam = true →
      acc.hasLevelParam = true)
    (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun j acc ih i hi hij hp => ?_)
    i hi hi hp
  rw [hasLevelParam_mkApp]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | rfl
  · simp [ih i hi hlt hp]
  · simp [hp]

theorem closed_of_mem {h : UInt64} {lp : Bool} {ds : Array Data} {d : Data} {k : Nat}
    (hle : (mkArr h lp ds).looseBVarRange.toNat ≤ k)
    (hlt : (mkArr h lp ds).looseBVarRange.toNat < maxRange) (hd : d ∈ ds) :
    d.looseBVarRange.toNat ≤ k ∧ d.looseBVarRange.toNat < maxRange :=
  have := UInt32.le_iff_toNat_le.mp (looseBVarRange_le_mkArr h lp ds hd)
  ⟨by omega, by omega⟩

theorem closed_of_mkApp_left {f a : Data} {k : Nat} (hle : (mkApp f a).looseBVarRange.toNat ≤ k)
    (hlt : (mkApp f a).looseBVarRange.toNat < maxRange) :
    f.looseBVarRange.toNat ≤ k ∧ f.looseBVarRange.toNat < maxRange :=
  have := UInt32.le_iff_toNat_le.mp (looseBVarRange_le_mkApp_left f a)
  ⟨by omega, by omega⟩

theorem closed_of_mkApp_right {f a : Data} {k : Nat} (hle : (mkApp f a).looseBVarRange.toNat ≤ k)
    (hlt : (mkApp f a).looseBVarRange.toNat < maxRange) :
    a.looseBVarRange.toNat ≤ k ∧ a.looseBVarRange.toNat < maxRange :=
  have := UInt32.le_iff_toNat_le.mp (looseBVarRange_le_mkApp_right f a)
  ⟨by omega, by omega⟩

theorem closed_of_binderRange {t b : Data} {k : Nat} (hle : min (binderRange t b) maxRange ≤ k)
    (hlt : min (binderRange t b) maxRange < maxRange) :
    (t.looseBVarRange.toNat ≤ k ∧ t.looseBVarRange.toNat < maxRange) ∧
      b.looseBVarRange.toNat ≤ k + 1 ∧ b.looseBVarRange.toNat < maxRange := by
  have := toNat_looseBVarRange_le b
  unfold binderRange at hle hlt
  by_cases hb : b.looseBVarRange.toNat = maxRange
  · simp only [hb, ↓reduceIte] at hlt
    omega
  · simp only [hb, ↓reduceIte] at hle hlt
    omega

theorem closed_of_mkBinder {t b : Data} {k : Nat} (hle : (mkBinder t b).looseBVarRange.toNat ≤ k)
    (hlt : (mkBinder t b).looseBVarRange.toNat < maxRange) :
    (t.looseBVarRange.toNat ≤ k ∧ t.looseBVarRange.toNat < maxRange) ∧
      b.looseBVarRange.toNat ≤ k + 1 ∧ b.looseBVarRange.toNat < maxRange := by
  rw [toNat_looseBVarRange_mkBinder] at hle hlt
  exact closed_of_binderRange hle hlt

theorem closed_of_mkLet {t v b : Data} {k : Nat} (hle : (mkLet t v b).looseBVarRange.toNat ≤ k)
    (hlt : (mkLet t v b).looseBVarRange.toNat < maxRange) :
    (t.looseBVarRange.toNat ≤ k ∧ t.looseBVarRange.toNat < maxRange) ∧
      (v.looseBVarRange.toNat ≤ k ∧ v.looseBVarRange.toNat < maxRange) ∧
      b.looseBVarRange.toNat ≤ k + 1 ∧ b.looseBVarRange.toNat < maxRange := by
  rw [toNat_looseBVarRange_mkLet] at hle hlt
  have ⟨htv, hb⟩ := closed_of_binderRange hle hlt
  exact ⟨closed_of_mkApp_left htv.1 htv.2, closed_of_mkApp_right htv.1 htv.2, hb⟩

theorem hasFVar_eq_false_of_mem {h : UInt64} {lp : Bool} {ds : Array Data} {d : Data}
    (hf : (mkArr h lp ds).hasFVar = false) (hd : d ∈ ds) :
    d.hasFVar = false := by
  cases hd' : d.hasFVar
  · rfl
  · rw [hasFVar_mkArr h lp ds hd hd'] at hf
    cases hf

theorem hasLevelParam_eq_false_of_mem {h : UInt64} {lp : Bool} {ds : Array Data} {d : Data}
    (hp : (mkArr h lp ds).hasLevelParam = false) (hd : d ∈ ds) :
    d.hasLevelParam = false := by
  cases hd' : d.hasLevelParam
  · rfl
  · rw [hasLevelParam_mkArr h lp ds hd hd'] at hp
    cases hp

theorem hasLevelParam_eq_false_init {h : UInt64} {lp : Bool} {ds : Array Data}
    (hp : (mkArr h lp ds).hasLevelParam = false) :
    lp = false := by
  cases lp
  · rfl
  · rw [hasLevelParam_mkArr_init] at hp
    cases hp

def maxArr (xs : Array Nat) : Nat :=
  xs.foldl max 0

theorem le_maxArr {xs : Array Nat} {x : Nat} (hx : x ∈ xs) : x ≤ maxArr xs := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  unfold maxArr
  refine Array.foldl_induction
    (motive := fun j (acc : Nat) => ∀ i (hi : i < xs.size), i < j → xs[i] ≤ acc)
    (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun j acc ih i hi hij => ?_)
    i hi hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | rfl
  · exact Nat.le_trans (ih i hi hlt) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

theorem maxArr_le {xs : Array Nat} {b : Nat} (h : ∀ x ∈ xs, x ≤ b) : maxArr xs ≤ b := by
  unfold maxArr
  refine Array.foldl_induction (motive := fun _ (acc : Nat) => acc ≤ b) (Nat.zero_le _)
    (fun i acc ih => ?_)
  exact Nat.max_le.mpr ⟨ih, h _ (Array.getElem_mem _)⟩

theorem maxArr_bound {xs : Array Nat} {x d m : Nat} (h : maxArr xs + d + 1 ≤ m) (hx : x ∈ xs) :
    x + d + 1 ≤ m := by
  have := le_maxArr hx
  omega

end Data

inductive FExpr where
  | bvar (i : Nat)
  | fvar (i : Nat)
  | sort (l : FLevel)
  | const (pos : Nat) (ls : Array (FLevel))
  | ind (pos s : Nat) (ls : Array (FLevel)) (ps is : Array (FExpr))
  | ctor (pos s c : Nat) (ls : Array (FLevel)) (ps fds recFds : Array (FExpr))
  | recr (pos s : Nat) (ls : Array (FLevel)) (l : FLevel) (ps ms mins is : Array (FExpr))
    (maj : FExpr)
  | quot (pos : Nat) (l : FLevel) (α r : FExpr)
  | quotMk (pos : Nat) (l : FLevel) (α r a : FExpr)
  | quotLift (pos : Nat) (l₁ l₂ : FLevel) (α r β f h a : FExpr)
  | quotInd (pos : Nat) (l : FLevel) (α r β f a : FExpr)
  | proj (pos s idx : Nat) (e : FExpr)
  | app (f a : FExpr)
  | lam (t b : FExpr)
  | forallE (t b : FExpr)
  | letE (t v b : FExpr)
  | natLit (num : Nat)
  | strLit (str : String)
with
  @[computed_field] data : FExpr → Data
    | .bvar i => .mk (mixHash 7 (hash i)) (i + 1) 0 false false
    | .fvar i => .mk (mixHash 13 (hash i)) 0 0 true false
    | .sort l => .mk (mixHash 11 (hash l)) 0 0 false l.hasParam
    | .const pos ls =>
      .mk (mixHash 5 (Data.levelsHash (hash pos) ls)) 0 0 false (ls.any FLevel.hasParam)
    | .ind pos s ls ps is =>
      is.foldl (fun d x => Data.mkApp d x.data) (ps.foldl (fun d x => Data.mkApp d x.data)
        (.mk (mixHash 19 (Data.levelsHash (mixHash (hash pos) (hash s)) ls)) 0 0 false
          (ls.any FLevel.hasParam)))
    | .ctor pos s c ls ps fds recFds =>
      recFds.foldl (fun d x => Data.mkApp d x.data) (fds.foldl (fun d x => Data.mkApp d x.data)
        (ps.foldl (fun d x => Data.mkApp d x.data)
          (.mk (mixHash 23 (Data.levelsHash (mixHash (hash pos) (mixHash (hash s) (hash c))) ls))
            0 0 false (ls.any FLevel.hasParam))))
    | .recr pos s ls l ps ms mins is maj =>
      Data.mkApp (is.foldl (fun d x => Data.mkApp d x.data) (mins.foldl (fun d x => Data.mkApp d x.data)
        (ms.foldl (fun d x => Data.mkApp d x.data) (ps.foldl (fun d x => Data.mkApp d x.data)
          (.mk (mixHash 29 (Data.levelsHash (mixHash (hash pos) (mixHash (hash s) (hash l))) ls))
            0 0 false (ls.any FLevel.hasParam || l.hasParam)))))) maj.data
    | .quot pos l α r =>
      Data.mkApp (Data.mkApp (.mk (mixHash 31 (mixHash (hash pos) (hash l))) 0 0 false l.hasParam)
        α.data) r.data
    | .quotMk pos l α r a =>
      Data.mkApp (Data.mkApp (Data.mkApp
        (.mk (mixHash 37 (mixHash (hash pos) (hash l))) 0 0 false l.hasParam) α.data) r.data) a.data
    | .quotLift pos l₁ l₂ α r β f h a =>
      Data.mkApp (Data.mkApp (Data.mkApp (Data.mkApp (Data.mkApp (Data.mkApp
        (.mk (mixHash 41 (mixHash (hash pos) (mixHash (hash l₁) (hash l₂)))) 0 0 false
          (l₁.hasParam || l₂.hasParam)) α.data) r.data) β.data) f.data) h.data) a.data
    | .quotInd pos l α r β f a =>
      Data.mkApp (Data.mkApp (Data.mkApp (Data.mkApp (Data.mkApp
        (.mk (mixHash 43 (mixHash (hash pos) (hash l))) 0 0 false l.hasParam) α.data) r.data)
        β.data) f.data) a.data
    | .proj pos s idx e =>
      Data.mkApp (.mk (mixHash 47 (mixHash (hash pos) (mixHash (hash s) (hash idx)))) 0 0 false false)
        e.data
    | .app f a => Data.mkApp f.data a.data
    | .lam t b => Data.mkBinder t.data b.data
    | .forallE t b => Data.mkBinder t.data b.data
    | .letE t v b => Data.mkLet t.data v.data b.data
    | .natLit num => .mk (mixHash 3 (hash num)) 0 0 false false
    | .strLit str => .mk (mixHash 3 (hash str)) 0 0 false false
  @[computed_field] fvarRange : FExpr → Nat
    | .bvar _ => 0
    | .fvar i => i + 1
    | .sort _ => 0
    | .const _ _ => 0
    | .ind _ _ _ ps is => is.foldl (fun m x => max m x.fvarRange) (ps.foldl (fun m x => max m x.fvarRange) 0)
    | .ctor _ _ _ _ ps fds recFds =>
      recFds.foldl (fun m x => max m x.fvarRange) (fds.foldl (fun m x => max m x.fvarRange)
        (ps.foldl (fun m x => max m x.fvarRange) 0))
    | .recr _ _ _ _ ps ms mins is maj =>
      max (is.foldl (fun m x => max m x.fvarRange) (mins.foldl (fun m x => max m x.fvarRange)
        (ms.foldl (fun m x => max m x.fvarRange) (ps.foldl (fun m x => max m x.fvarRange) 0)))) maj.fvarRange
    | .quot _ _ α r => max (max 0 α.fvarRange) r.fvarRange
    | .quotMk _ _ α r a => max (max (max 0 α.fvarRange) r.fvarRange) a.fvarRange
    | .quotLift _ _ _ α r β f h a =>
      max (max (max (max (max (max 0 α.fvarRange) r.fvarRange) β.fvarRange) f.fvarRange) h.fvarRange)
        a.fvarRange
    | .quotInd _ _ α r β f a =>
      max (max (max (max (max 0 α.fvarRange) r.fvarRange) β.fvarRange) f.fvarRange) a.fvarRange
    | .proj _ _ _ e => max 0 e.fvarRange
    | .app f a => max f.fvarRange a.fvarRange
    | .lam t b => max t.fvarRange b.fvarRange
    | .forallE t b => max t.fvarRange b.fvarRange
    | .letE t v b => max t.fvarRange (max v.fvarRange b.fvarRange)
    | .natLit _ => 0
    | .strLit _ => 0
deriving Inhabited

namespace FExpr

@[simp] theorem data_bvar (i : Nat) :
    (bvar i).data = .mk (mixHash 7 (hash i)) (i + 1) 0 false false := by
  simp [data]

@[simp] theorem data_fvar (i : Nat) :
    (fvar i).data = .mk (mixHash 13 (hash i)) 0 0 true false := by
  simp [data]

@[simp] theorem data_sort (l : FLevel) :
    (sort l).data = .mk (mixHash 11 (hash l)) 0 0 false l.hasParam := by
  simp [data]

@[simp] theorem data_const (pos : Nat) (ls : Array (FLevel)) :
    (const pos ls).data =
      .mk (mixHash 5 (Data.levelsHash (hash pos) ls)) 0 0 false (ls.any FLevel.hasParam) := by
  simp [data]

@[simp] theorem data_ind (pos s : Nat) (ls : Array (FLevel)) (ps is : Array (FExpr)) :
    (ind pos s ls ps is).data =
      Data.mkArr (mixHash 19 (Data.levelsHash (mixHash (hash pos) (hash s)) ls))
        (ls.any FLevel.hasParam) (ps.map data ++ is.map data) := by
  simp [data, Data.mkArr, Array.foldl_map, -Array.size_map]

@[simp] theorem data_ctor (pos s c : Nat) (ls : Array (FLevel))
    (ps fds recFds : Array (FExpr)) :
    (ctor pos s c ls ps fds recFds).data =
      Data.mkArr (mixHash 23 (Data.levelsHash (mixHash (hash pos) (mixHash (hash s) (hash c))) ls))
        (ls.any FLevel.hasParam)
        (ps.map data ++ fds.map data ++ recFds.map data) := by
  simp [data, Data.mkArr, Array.foldl_map, -Array.size_map]

@[simp] theorem data_recr (pos s : Nat) (ls : Array (FLevel)) (l : FLevel)
    (ps ms mins is : Array (FExpr)) (maj : FExpr) :
    (recr pos s ls l ps ms mins is maj).data =
      Data.mkArr (mixHash 29 (Data.levelsHash (mixHash (hash pos) (mixHash (hash s) (hash l))) ls))
        (ls.any FLevel.hasParam || l.hasParam)
        (ps.map data ++ ms.map data ++ mins.map data ++ is.map data ++
          #[maj.data]) := by
  simp [data, Data.mkArr, Array.foldl_map, -Array.size_map]

@[simp] theorem data_quot (pos : Nat) (l : FLevel) (α r : FExpr) :
    (quot pos l α r).data =
      Data.mkArr (mixHash 31 (mixHash (hash pos) (hash l))) l.hasParam #[α.data, r.data] := by
  simp only [data]
  rfl

@[simp] theorem data_quotMk (pos : Nat) (l : FLevel) (α r a : FExpr) :
    (quotMk pos l α r a).data =
      Data.mkArr (mixHash 37 (mixHash (hash pos) (hash l))) l.hasParam
        #[α.data, r.data, a.data] := by
  simp only [data]
  rfl

@[simp] theorem data_quotLift (pos : Nat) (l₁ l₂ : FLevel) (α r β f h a : FExpr) :
    (quotLift pos l₁ l₂ α r β f h a).data =
      Data.mkArr (mixHash 41 (mixHash (hash pos) (mixHash (hash l₁) (hash l₂))))
        (l₁.hasParam || l₂.hasParam) #[α.data, r.data, β.data, f.data, h.data, a.data] := by
  simp only [data]
  rfl

@[simp] theorem data_quotInd (pos : Nat) (l : FLevel) (α r β f a : FExpr) :
    (quotInd pos l α r β f a).data =
      Data.mkArr (mixHash 43 (mixHash (hash pos) (hash l))) l.hasParam
        #[α.data, r.data, β.data, f.data, a.data] := by
  simp only [data]
  rfl

@[simp] theorem data_proj (pos s idx : Nat) (e : FExpr) :
    (proj pos s idx e).data =
      Data.mkArr (mixHash 47 (mixHash (hash pos) (mixHash (hash s) (hash idx)))) false #[e.data] := by
  simp only [data]
  rfl

@[simp] theorem data_app (f a : FExpr) : (app f a).data = Data.mkApp f.data a.data := by
  simp [data]

@[simp] theorem data_lam (t b : FExpr) : (lam t b).data = Data.mkBinder t.data b.data := by
  simp [data]

@[simp] theorem data_forallE (t b : FExpr) :
    (forallE t b).data = Data.mkBinder t.data b.data := by
  simp [data]

@[simp] theorem data_letE (t v b : FExpr) :
    (letE t v b).data = Data.mkLet t.data v.data b.data := by
  simp [data]

@[simp] theorem data_natLit (num : Nat) :
    (natLit num).data = .mk (mixHash 3 (hash num)) 0 0 false false := by
  simp [data]

@[simp] theorem data_strLit (str : String) :
    (strLit str).data = .mk (mixHash 3 (hash str)) 0 0 false false := by
  simp [data]

@[simp] theorem fvarRange_bvar (i : Nat) : (bvar i).fvarRange = 0 := by
  simp [fvarRange]

@[simp] theorem fvarRange_sort (l : FLevel) : (sort l).fvarRange = 0 := by
  simp [fvarRange]

@[simp] theorem fvarRange_const (pos : Nat) (ls : Array FLevel) : (const pos ls).fvarRange = 0 := by
  simp [fvarRange]

@[simp] theorem fvarRange_natLit (num : Nat) : (natLit num).fvarRange = 0 := by
  simp [fvarRange]

@[simp] theorem fvarRange_strLit (str : String) : (strLit str).fvarRange = 0 := by
  simp [fvarRange]

@[simp] theorem fvarRange_fvar (i : Nat) : (fvar i).fvarRange = i + 1 := by
  simp [fvarRange]

@[simp] theorem fvarRange_ind (pos s : Nat) (ls : Array FLevel) (ps is : Array FExpr) :
    (ind pos s ls ps is).fvarRange = Data.maxArr (ps.map fvarRange ++ is.map fvarRange) := by
  simp [fvarRange, Data.maxArr, Array.foldl_map, -Array.size_map]

@[simp] theorem fvarRange_ctor (pos s c : Nat) (ls : Array FLevel) (ps fds recFds : Array FExpr) :
    (ctor pos s c ls ps fds recFds).fvarRange =
      Data.maxArr (ps.map fvarRange ++ fds.map fvarRange ++ recFds.map fvarRange) := by
  simp [fvarRange, Data.maxArr, Array.foldl_map, -Array.size_map]

@[simp] theorem fvarRange_recr (pos s : Nat) (ls : Array FLevel) (l : FLevel)
    (ps ms mins is : Array FExpr) (maj : FExpr) :
    (recr pos s ls l ps ms mins is maj).fvarRange =
      Data.maxArr (ps.map fvarRange ++ ms.map fvarRange ++ mins.map fvarRange ++
        is.map fvarRange ++ #[maj.fvarRange]) := by
  simp [fvarRange, Data.maxArr, Array.foldl_map, -Array.size_map]

@[simp] theorem fvarRange_quot (pos : Nat) (l : FLevel) (α r : FExpr) :
    (quot pos l α r).fvarRange = Data.maxArr #[α.fvarRange, r.fvarRange] := by
  simp only [fvarRange]
  rfl

@[simp] theorem fvarRange_quotMk (pos : Nat) (l : FLevel) (α r a : FExpr) :
    (quotMk pos l α r a).fvarRange = Data.maxArr #[α.fvarRange, r.fvarRange, a.fvarRange] := by
  simp only [fvarRange]
  rfl

@[simp] theorem fvarRange_quotLift (pos : Nat) (l₁ l₂ : FLevel) (α r β f h a : FExpr) :
    (quotLift pos l₁ l₂ α r β f h a).fvarRange =
      Data.maxArr #[α.fvarRange, r.fvarRange, β.fvarRange, f.fvarRange, h.fvarRange,
        a.fvarRange] := by
  simp only [fvarRange]
  rfl

@[simp] theorem fvarRange_quotInd (pos : Nat) (l : FLevel) (α r β f a : FExpr) :
    (quotInd pos l α r β f a).fvarRange =
      Data.maxArr #[α.fvarRange, r.fvarRange, β.fvarRange, f.fvarRange, a.fvarRange] := by
  simp only [fvarRange]
  rfl

@[simp] theorem fvarRange_proj (pos s idx : Nat) (e : FExpr) :
    (proj pos s idx e).fvarRange = Data.maxArr #[e.fvarRange] := by
  simp only [fvarRange]
  rfl

@[simp] theorem fvarRange_app (f a : FExpr) :
    (app f a).fvarRange = max f.fvarRange a.fvarRange := by
  simp [fvarRange]

@[simp] theorem fvarRange_lam (t b : FExpr) :
    (lam t b).fvarRange = max t.fvarRange b.fvarRange := by
  simp [fvarRange]

@[simp] theorem fvarRange_forallE (t b : FExpr) :
    (forallE t b).fvarRange = max t.fvarRange b.fvarRange := by
  simp [fvarRange]

@[simp] theorem fvarRange_letE (t v b : FExpr) :
    (letE t v b).fvarRange = max t.fvarRange (max v.fvarRange b.fvarRange) := by
  simp [fvarRange]

theorem fvarRange_mem_map {xs : Array FExpr} {i : Nat} (h : i < xs.size) :
    xs[i].fvarRange ∈ xs.map fvarRange :=
  Array.mem_map.mpr ⟨_, Array.getElem_mem h, rfl⟩

theorem data_mem_map {xs : Array FExpr} {i : Nat} (h : i < xs.size) :
    xs[i].data ∈ xs.map data :=
  Array.mem_map.mpr ⟨_, Array.getElem_mem h, rfl⟩


def listDecEqOf {α : Type _} : (xs ys : List α) → (∀ x ∈ xs, ∀ y, Decidable (x = y)) →
    Decidable (xs = ys)
  | [], [], _ => isTrue rfl
  | [], _ :: _, _ => isFalse nofun
  | _ :: _, [], _ => isFalse nofun
  | x :: xs, y :: ys, f =>
    match f x (List.mem_cons_self ..) y, listDecEqOf xs ys fun x hx y => f x (List.mem_cons_of_mem _ hx) y with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h₁, _ => isFalse fun h => h₁ (List.cons.inj h).1
    | _, isFalse h₂ => isFalse fun h => h₂ (List.cons.inj h).2

def arrDecEqOf {α : Type _} (xs ys : Array α) (f : ∀ x ∈ xs, ∀ y, Decidable (x = y)) :
    Decidable (xs = ys) :=
  match listDecEqOf xs.toList ys.toList fun x hx y => f x (Array.mem_def.mpr hx) y with
  | isTrue h => isTrue (Array.toList_inj.mp h)
  | isFalse h => isFalse fun h' => h (h' ▸ rfl)

run_meta Lean.mkCasesOnSameCtor `Metalean.FastChecker.FExpr.match_on_same_ctor ``FExpr

def decOfEq {P Q : Prop} (h : P = Q) [Decidable Q] : Decidable P :=
  decidable_of_decidable_of_eq h.symm

abbrev EqM := StateM (Option (Std.HashSet (USize × USize)))

unsafe def eqSeen (a b : FExpr) : EqM Bool := do
  if isExclusiveUnsafe a || isExclusiveUnsafe b then return false
  let key := (ptrAddrUnsafe a, ptrAddrUnsafe b)
  if (← get).any (·.contains key) then return true
  modify fun s => some ((s.getD ∅).insert key)
  return false

mutual

unsafe def eqCached (root : Bool) (a b : FExpr) : EqM Bool := do
  if ptrAddrUnsafe a == ptrAddrUnsafe b then return true
  if a.data.hash != b.data.hash then return false
  if a.ctorIdx != b.ctorIdx then return false
  match a, b with
  | .bvar i₁, .bvar i₂ | .fvar i₁, .fvar i₂ => return i₁ == i₂
  | .natLit n₁, .natLit n₂ => return n₁ == n₂
  | .strLit s₁, .strLit s₂ => return s₁ == s₂
  | .sort l₁, .sort l₂ => return l₁ == l₂
  | _, _ => pure ()
  if !root && (← eqSeen a b) then return true
  eqCore a b

unsafe def eqArrayFrom (xs ys : Array FExpr) : Nat → EqM Bool
  | 0 => pure true
  | i + 1 => do
    unless ← eqCached false xs[i]! ys[i]! do return false
    eqArrayFrom xs ys i

unsafe def eqArray (xs ys : Array FExpr) : EqM Bool := do
  if ptrAddrUnsafe xs == ptrAddrUnsafe ys then return true
  unless xs.size == ys.size do return false
  eqArrayFrom xs ys xs.size

unsafe def eqCore : FExpr → FExpr → EqM Bool
  | .const p₁ ls₁, .const p₂ ls₂ => pure (p₁ == p₂ && ls₁ == ls₂)
  | .ind p₁ s₁ ls₁ ps₁ is₁, .ind p₂ s₂ ls₂ ps₂ is₂ => do
    pure ((← eqArray is₁ is₂) && (← eqArray ps₁ ps₂) && p₁ == p₂ && s₁ == s₂ && ls₁ == ls₂)
  | .ctor p₁ s₁ c₁ ls₁ ps₁ fds₁ rs₁, .ctor p₂ s₂ c₂ ls₂ ps₂ fds₂ rs₂ => do
    pure ((← eqArray rs₁ rs₂) && (← eqArray fds₁ fds₂) && (← eqArray ps₁ ps₂) &&
      p₁ == p₂ && s₁ == s₂ && c₁ == c₂ && ls₁ == ls₂)
  | .recr p₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁, .recr p₂ s₂ ls₂ l₂ ps₂ ms₂ mins₂ is₂ maj₂ => do
    pure ((← eqCached false maj₁ maj₂) && (← eqArray is₁ is₂) && (← eqArray mins₁ mins₂) &&
      (← eqArray ms₁ ms₂) && (← eqArray ps₁ ps₂) &&
      p₁ == p₂ && s₁ == s₂ && ls₁ == ls₂ && l₁ == l₂)
  | .quot p₁ l₁ α₁ r₁, .quot p₂ l₂ α₂ r₂ => do
    pure ((← eqCached false r₁ r₂) && (← eqCached false α₁ α₂) && p₁ == p₂ && l₁ == l₂)
  | .quotMk p₁ l₁ α₁ r₁ a₁, .quotMk p₂ l₂ α₂ r₂ a₂ => do
    pure ((← eqCached false a₁ a₂) && (← eqCached false r₁ r₂) && (← eqCached false α₁ α₂) &&
      p₁ == p₂ && l₁ == l₂)
  | .quotLift p₁ u₁ v₁ α₁ r₁ β₁ f₁ h₁ a₁, .quotLift p₂ u₂ v₂ α₂ r₂ β₂ f₂ h₂ a₂ => do
    pure ((← eqCached false a₁ a₂) && (← eqCached false h₁ h₂) && (← eqCached false f₁ f₂) &&
      (← eqCached false β₁ β₂) && (← eqCached false r₁ r₂) && (← eqCached false α₁ α₂) &&
      p₁ == p₂ && u₁ == u₂ && v₁ == v₂)
  | .quotInd p₁ l₁ α₁ r₁ β₁ f₁ a₁, .quotInd p₂ l₂ α₂ r₂ β₂ f₂ a₂ => do
    pure ((← eqCached false a₁ a₂) && (← eqCached false f₁ f₂) && (← eqCached false β₁ β₂) &&
      (← eqCached false r₁ r₂) && (← eqCached false α₁ α₂) && p₁ == p₂ && l₁ == l₂)
  | .proj p₁ s₁ i₁ e₁, .proj p₂ s₂ i₂ e₂ => do
    pure ((← eqCached false e₁ e₂) && p₁ == p₂ && s₁ == s₂ && i₁ == i₂)
  | .app f₁ a₁, .app f₂ a₂ => do
    unless ← eqCached false a₁ a₂ do return false
    eqSpine f₁ f₂
  | .lam t₁ b₁, .lam t₂ b₂ | .forallE t₁ b₁, .forallE t₂ b₂ => do
    pure ((← eqCached false t₁ t₂) && (← eqCached false b₁ b₂))
  | .letE t₁ v₁ b₁, .letE t₂ v₂ b₂ => do
    pure ((← eqCached false t₁ t₂) && (← eqCached false v₁ v₂) && (← eqCached false b₁ b₂))
  | _, _ => pure false

unsafe def eqSpine : FExpr → FExpr → EqM Bool
  | .app f₁ a₁, .app f₂ a₂ => do
    unless ← eqCached false a₁ a₂ do return false
    eqSpine f₁ f₂
  | .app _ _, _ => pure false
  | f₁, f₂ => eqCached false f₁ f₂

end

unsafe def decEqShared (a b : FExpr) : Decidable (a = b) :=
  if ptrEq a b then isTrue lcProof
  else if a.data.hash != b.data.hash then isFalse lcProof
  else
    let same : Bool := Id.run ((eqCached true a b).run' none)
    if same then isTrue lcProof else isFalse lcProof

@[implemented_by decEqShared]
def decEq (a b : FExpr) : Decidable (a = b) :=
  withPtrEqDecEq a b fun () =>
  if hh : a.data.hash ≠ b.data.hash then isFalse fun e => hh (e ▸ rfl)
  else if h : a.ctorIdx = b.ctorIdx then
    match_on_same_ctor (motive := fun a b _ => Decidable (a = b)) a b h
    (fun _ _ => decOfEq (bvar.injEq ..))
    (fun _ _ => decOfEq (fvar.injEq ..))
    (fun _ _ => decOfEq (sort.injEq ..))
    (fun _ _ _ _ => decOfEq (const.injEq ..))
    (fun _ _ _ ps₁ is₁ _ _ _ ps₂ is₂ =>
      have hps := arrDecEqOf ps₁ ps₂ fun x _ y => decEq x y
      have his := arrDecEqOf is₁ is₂ fun x _ y => decEq x y
      decOfEq (ind.injEq ..))
    (fun _ _ _ _ ps₁ fds₁ recFds₁ _ _ _ _ ps₂ fds₂ recFds₂ =>
      have hps := arrDecEqOf ps₁ ps₂ fun x _ y => decEq x y
      have hfds := arrDecEqOf fds₁ fds₂ fun x _ y => decEq x y
      have hrecFds := arrDecEqOf recFds₁ recFds₂ fun x _ y => decEq x y
      decOfEq (ctor.injEq ..))
    (fun _ _ _ _ ps₁ ms₁ mins₁ is₁ maj₁ _ _ _ _ ps₂ ms₂ mins₂ is₂ maj₂ =>
      have hps := arrDecEqOf ps₁ ps₂ fun x _ y => decEq x y
      have hms := arrDecEqOf ms₁ ms₂ fun x _ y => decEq x y
      have hmins := arrDecEqOf mins₁ mins₂ fun x _ y => decEq x y
      have his := arrDecEqOf is₁ is₂ fun x _ y => decEq x y
      have hmaj := decEq maj₁ maj₂
      decOfEq (recr.injEq ..))
    (fun _ _ α₁ r₁ _ _ α₂ r₂ =>
      have hα := decEq α₁ α₂
      have hr := decEq r₁ r₂
      decOfEq (quot.injEq ..))
    (fun _ _ α₁ r₁ a₁ _ _ α₂ r₂ a₂ =>
      have hα := decEq α₁ α₂
      have hr := decEq r₁ r₂
      have ha := decEq a₁ a₂
      decOfEq (quotMk.injEq ..))
    (fun _ _ _ α₁ r₁ β₁ f₁ h₁ a₁ _ _ _ α₂ r₂ β₂ f₂ h₂ a₂ =>
      have hα := decEq α₁ α₂
      have hr := decEq r₁ r₂
      have hβ := decEq β₁ β₂
      have hf := decEq f₁ f₂
      have hh := decEq h₁ h₂
      have ha := decEq a₁ a₂
      decOfEq (quotLift.injEq ..))
    (fun _ _ α₁ r₁ β₁ f₁ a₁ _ _ α₂ r₂ β₂ f₂ a₂ =>
      have hα := decEq α₁ α₂
      have hr := decEq r₁ r₂
      have hβ := decEq β₁ β₂
      have hf := decEq f₁ f₂
      have ha := decEq a₁ a₂
      decOfEq (quotInd.injEq ..))
    (fun _ _ _ e₁ _ _ _ e₂ =>
      have he := decEq e₁ e₂
      decOfEq (proj.injEq ..))
    (fun f₁ a₁ f₂ a₂ =>
      have hf := decEq f₁ f₂
      have ha := decEq a₁ a₂
      decOfEq (app.injEq ..))
    (fun t₁ b₁ t₂ b₂ =>
      have ht := decEq t₁ t₂
      have hb := decEq b₁ b₂
      decOfEq (lam.injEq ..))
    (fun t₁ b₁ t₂ b₂ =>
      have ht := decEq t₁ t₂
      have hb := decEq b₁ b₂
      decOfEq (forallE.injEq ..))
    (fun t₁ v₁ b₁ t₂ v₂ b₂ =>
      have ht := decEq t₁ t₂
      have hv := decEq v₁ v₂
      have hb := decEq b₁ b₂
      decOfEq (letE.injEq ..))
    (fun _ _ => decOfEq (natLit.injEq ..))
    (fun _ _ => decOfEq (strLit.injEq ..))
  else isFalse fun e => h (congrArg FExpr.ctorIdx e)

def ptrEq (fe₁ fe₂ : FExpr) : Bool :=
  unsafe _root_.ptrEq fe₁ fe₂

def ptrEqArrayElems (fes₁ fes₂ : Array FExpr) : Bool :=
  fes₁.size == fes₂.size && (Fin.foldl fes₁.size (fun acc i => acc && unsafe _root_.ptrEq fes₁[i] (fes₂[i.val]!)) true)

def ptrEqArray (fes₁ fes₂ : Array FExpr) : Bool :=
  unsafe _root_.ptrEq fes₁ fes₂

instance : DecidableEq FExpr := decEq

instance : Hashable FExpr := ⟨fun e => e.data.hash⟩

end FExpr

namespace FExpr

variable (L : Literals)

def nat : FExpr :=
  .ind L.nat 0 #[] #[] #[]

def zero : FExpr :=
  .ctor L.nat 0 0 #[] #[] #[] #[]

def succ (fe : FExpr) : FExpr :=
  .ctor L.nat 0 1 #[] #[] #[] #[fe]

def bool : FExpr :=
  .ind L.bool 0 #[] #[] #[]

def boolLit : Bool → FExpr
  | false => .ctor L.bool 0 0 #[] #[] #[] #[]
  | true => .ctor L.bool 0 1 #[] #[] #[] #[]

def char : FExpr :=
  .ind L.char 0 #[] #[] #[]

def op₁ (pos : Nat) (fe : FExpr) : FExpr :=
  .app (.const pos #[]) fe

def op₂ (pos : Nat) (fe₁ fe₂ : FExpr) : FExpr :=
  .app (.app (.const pos #[]) fe₁) fe₂

def natArrow : FExpr :=
  .forallE (nat L) (nat L)

def natArrow₂ : FExpr :=
  .forallE (nat L) (natArrow L)

def charList : List Char → FExpr
  | [] => .ctor L.list 0 0 #[.zero] #[char L] #[] #[]
  | c :: cs =>
    .ctor L.list 0 1 #[.zero] #[char L] #[op₁ L.charOfNat (.natLit c.toNat)] #[charList cs]

def strLitExpand (str : String) : FExpr :=
  op₁ L.stringOfList (charList L str.toList)

@[derive_functor E]
judgement Denotes {ℓ : Nat} (L : Literals) (E : Σ ζ, Env ζ) :
    (k : Nat) → (fe : FExpr) → {n : Nat} → (e : Expr E.1 ℓ n) → Prop where

  j < k
  ──────────────────── bvar {n k i j : Nat} (hi : i + j + 1 = n)
  Denotes L E k (.bvar j) (.var ⟨i, by omega⟩ : Expr E.1 ℓ n)

  ──────────────────── fvar {n k i : Nat} (hi : i + k < n)
  Denotes L E k (.fvar i) (.var ⟨i, by omega⟩ : Expr E.1 ℓ n)

  FLevel.Denotes l l'
  ──────────────────── sort {n k : Nat} {l : FLevel} {l' : RawLevel ℓ}
  Denotes L E k (.sort l) (.sort ⟦l'⟧ : Expr E.1 ℓ n)

  E.1.lookup pos = some ⟨.const kind nlevels, η⟩
  ∀ i, FLevel.Denotes (ls[i.val]'(hls.symm ▸ i.isLt)) (ls' i)
  ──────────────────── const {n k pos : Nat} {kind : ConstKind} {nlevels : Nat}
    {η : Head E.1 (.const kind nlevels)} {ls : Array FLevel} {ls' : Fin nlevels → RawLevel ℓ}
    (hls : ls.size = nlevels)
  Denotes L E k (.const pos ls) (.const η (⟦ls' ·⟧) : Expr E.1 ℓ n)

  E.1.lookup pos = some ⟨.inductive ι, η⟩
  s'.val = s
  ∀ i, FLevel.Denotes (ls[i.val]'(hls.symm ▸ i.isLt)) (ls' i)
  ∀ p, Denotes L E k (ps[p.val]'(hps.symm ▸ p.isLt)) (ps' p)
  ∀ i, Denotes L E k (is[i.val]'(his.symm ▸ i.isLt)) (is' i)
  ──────────────────── ind {n k pos s : Nat} {ι : IndSig} {η : Head E.1 (.inductive ι)}
    {s' : Fin ι.nsorts} {ls : Array FLevel} {ls' : Fin ι.nlevels → RawLevel ℓ}
    {ps is : Array FExpr} {ps' : Fin ι.nparams → Expr E.1 ℓ n}
    {is' : Fin (ι.nindices s') → Expr E.1 ℓ n} (hls : ls.size = ι.nlevels)
    (hps : ps.size = ι.nparams) (his : is.size = ι.nindices s')
  Denotes L E k (.ind pos s ls ps is) (.ind η s' (⟦ls' ·⟧) ps' is')

  E.1.lookup pos = some ⟨.inductive ι, η⟩
  s'.val = s
  c'.val = c
  ∀ i, FLevel.Denotes (ls[i.val]'(hls.symm ▸ i.isLt)) (ls' i)
  ∀ p, Denotes L E k (ps[p.val]'(hps.symm ▸ p.isLt)) (ps' p)
  ∀ i, Denotes L E k (fds[i.val]'(hfds.symm ▸ i.isLt)) (fds' i)
  ∀ i, Denotes L E k (recFds[i.val]'(hrecFds.symm ▸ i.isLt)) (recFds' i)
  ──────────────────── ctor {n k pos s c : Nat} {ι : IndSig} {η : Head E.1 (.inductive ι)}
    {s' : Fin ι.nsorts} {c' : Fin (ι.nctors s')} {ls : Array FLevel}
    {ls' : Fin ι.nlevels → RawLevel ℓ} {ps fds recFds : Array FExpr}
    {ps' : Fin ι.nparams → Expr E.1 ℓ n} {fds' : Fin (ι.ctors s' c').nfields → Expr E.1 ℓ n}
    {recFds' : Fin (ι.ctors s' c').nrecFields → Expr E.1 ℓ n} (hls : ls.size = ι.nlevels)
    (hps : ps.size = ι.nparams) (hfds : fds.size = (ι.ctors s' c').nfields)
    (hrecFds : recFds.size = (ι.ctors s' c').nrecFields)
  Denotes L E k (.ctor pos s c ls ps fds recFds)
    (.ctor η s' c' (⟦ls' ·⟧) ps' fds' recFds')

  E.1.lookup pos = some ⟨.inductive ι, η⟩
  s'.val = s
  ∀ i, FLevel.Denotes (ls[i.val]'(hls.symm ▸ i.isLt)) (ls' i)
  FLevel.Denotes l l'
  ∀ p, Denotes L E k (ps[p.val]'(hps.symm ▸ p.isLt)) (ps' p)
  ∀ t, Denotes L E k (ms[t.val]'(hms.symm ▸ t.isLt)) (ms' t)
  ∀ t c, Denotes L E k
    (mins[(Fin.encodeSigma ι.nctors ⟨t, c⟩).val]'
      (hmins.symm ▸ (Fin.encodeSigma ι.nctors ⟨t, c⟩).isLt))
    (mins' t c)
  ∀ i, Denotes L E k (is[i.val]'(his.symm ▸ i.isLt)) (is' i)
  Denotes L E k maj maj'
  ──────────────────── recr {n k pos s : Nat} {ι : IndSig} {η : Head E.1 (.inductive ι)}
    {s' : Fin ι.nsorts} {ls : Array FLevel} {ls' : Fin ι.nlevels → RawLevel ℓ} {l : FLevel}
    {l' : RawLevel ℓ} {ps ms mins is : Array FExpr} {maj : FExpr}
    {ps' : Fin ι.nparams → Expr E.1 ℓ n} {ms' : Fin ι.nsorts → Expr E.1 ℓ n}
    {mins' : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr E.1 ℓ n}
    {is' : Fin (ι.nindices s') → Expr E.1 ℓ n} {maj' : Expr E.1 ℓ n} (hls : ls.size = ι.nlevels)
    (hps : ps.size = ι.nparams) (hms : ms.size = ι.nsorts) (hmins : mins.size = Fin.sum ι.nctors)
    (his : is.size = ι.nindices s')
  Denotes L E k (.recr pos s ls l ps ms mins is maj)
    (.recr η s' (⟦ls' ·⟧) ⟦l'⟧ ps' ms' mins' is' maj')

  E.1.lookup pos = some ⟨.quot, η⟩
  FLevel.Denotes l l'
  Denotes L E k α α'
  Denotes L E k r r'
  ──────────────────── quot {n k pos : Nat} {η : Head E.1 .quot} {l : FLevel} {l' : RawLevel ℓ}
    {α r : FExpr} {α' r' : Expr E.1 ℓ n}
  Denotes L E k (.quot pos l α r) (.quot η ⟦l'⟧ α' r')

  E.1.lookup pos = some ⟨.quot, η⟩
  FLevel.Denotes l l'
  Denotes L E k α α'
  Denotes L E k r r'
  Denotes L E k a a'
  ──────────────────── quotMk {n k pos : Nat} {η : Head E.1 .quot} {l : FLevel} {l' : RawLevel ℓ}
    {α r a : FExpr} {α' r' a' : Expr E.1 ℓ n}
  Denotes L E k (.quotMk pos l α r a) (.quotMk η ⟦l'⟧ α' r' a')

  E.1.lookup pos = some ⟨.quot, η⟩
  FLevel.Denotes l₁ l₁'
  FLevel.Denotes l₂ l₂'
  Denotes L E k α α'
  Denotes L E k r r'
  Denotes L E k β β'
  Denotes L E k f f'
  Denotes L E k h h'
  Denotes L E k a a'
  ──────────────────── quotLift {n k pos : Nat} {η : Head E.1 .quot} {l₁ l₂ : FLevel}
    {l₁' l₂' : RawLevel ℓ} {α r β f h a : FExpr} {α' r' β' f' h' a' : Expr E.1 ℓ n}
  Denotes L E k (.quotLift pos l₁ l₂ α r β f h a) (.quotLift η ⟦l₁'⟧ ⟦l₂'⟧ α' r' β' f' h' a')

  E.1.lookup pos = some ⟨.quot, η⟩
  FLevel.Denotes l l'
  Denotes L E k α α'
  Denotes L E k r r'
  Denotes L E k β β'
  Denotes L E k f f'
  Denotes L E k a a'
  ──────────────────── quotInd {n k pos : Nat} {η : Head E.1 .quot} {l : FLevel} {l' : RawLevel ℓ}
    {α r β f a : FExpr} {α' r' β' f' a' : Expr E.1 ℓ n}
  Denotes L E k (.quotInd pos l α r β f a) (.quotInd η ⟦l'⟧ α' r' β' f' a')

  E.1.lookup pos = some ⟨.inductive ι, η⟩
  s'.val = s
  f'.val = idx
  Denotes L E k e e'
  ──────────────────── proj {n k pos s idx : Nat} {ι : IndSig} {η : Head E.1 (.inductive ι)}
    {s' : Fin ι.nsorts} {c' : Fin (ι.nctors s')} {f' : Fin (ι.ctors s' c').nfields}
    {ls' : Fin ι.nlevels → RawLevel ℓ} {ps' : Fin ι.nparams → Expr E.1 ℓ n} {e : FExpr}
    {e' : Expr E.1 ℓ n}
    (hstruct : (E.2.get η).block.IsStructure s' c')
  Denotes L E k (.proj pos s idx e) (hstruct.projTerm η (⟦ls' ·⟧) ps' f' e')

  Denotes L E k f f'
  Denotes L E k a a'
  ──────────────────── app {n k : Nat} {f a : FExpr} {f' a' : Expr E.1 ℓ n}
  Denotes L E k (.app f a) (.app f' a')

  Denotes L E k t t'
  Denotes L E (k + 1) b b'
  ──────────────────── lam {n k : Nat} {t b : FExpr} {t' : Expr E.1 ℓ n} {b' : Expr E.1 ℓ (n + 1)}
  Denotes L E k (.lam t b) (.lam t' b')

  Denotes L E k t t'
  Denotes L E (k + 1) b b'
  ──────────────────── forallE {n k : Nat} {t b : FExpr} {t' : Expr E.1 ℓ n}
    {b' : Expr E.1 ℓ (n + 1)}
  Denotes L E k (.forallE t b) (.forallE t' b')

  Denotes L E k t t'
  Denotes L E k v v'
  Denotes L E (k + 1) b b'
  ──────────────────── letE {n k : Nat} {t v b : FExpr} {t' v' : Expr E.1 ℓ n}
    {b' : Expr E.1 ℓ (n + 1)}
  Denotes L E k (.letE t v b) (.letE t' v' b')

  E.1.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩
  ──────────────────── natLit {n k num : Nat} {ηNat : Head E.1 (.inductive Literals.Nat.sig)}
  Denotes L E k (.natLit num) (Literals.natLit ηNat num : Expr E.1 ℓ n)

  E.1.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩
  E.1.lookup L.list = some ⟨.inductive Literals.List.sig, ηList⟩
  E.1.lookup L.char = some ⟨.inductive Literals.Char.sig, ηChar⟩
  E.1.lookup L.charOfNat = some ⟨.const .def 0, ηOfNat⟩
  E.1.lookup L.stringOfList = some ⟨.const .def 0, ηOfList⟩
  ──────────────────── strLit {n k : Nat} {str : String}
    {ηNat : Head E.1 (.inductive Literals.Nat.sig)} {ηList : Head E.1 (.inductive Literals.List.sig)}
    {ηChar : Head E.1 (.inductive Literals.Char.sig)} {ηOfNat ηOfList : Head E.1 (.const .def 0)}
  Denotes L E k (.strLit str)
    (Literals.strLit ηNat ηList ηChar ηOfNat ηOfList str : Expr E.1 ℓ n)

variable {ζ : Sigs} {E : Env ζ} {L : Literals} {ℓ n k num : Nat}
  {ηNat : Head ζ (.inductive Literals.Nat.sig)}
  {ηBool : Head ζ (.inductive Literals.Bool.sig)}
  {ηList : Head ζ (.inductive Literals.List.sig)}
  {ηChar : Head ζ (.inductive Literals.Char.sig)}
  {ηOfNat ηOfList : Head ζ (.const .def 0)}
  {pos : Nat} {kind : ConstKind} {ηOp : Head ζ (.const kind 0)}

theorem Denotes.nat (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Denotes L E.as k (FExpr.nat L) (Literals.natType ηNat : Expr ζ ℓ n) := by
  rw [Literals.natType, Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
  exact Denotes.ind rfl rfl rfl hη rfl nofun nofun nofun

theorem Denotes.boolType (hη : ζ.lookup L.bool = some ⟨.inductive Literals.Bool.sig, ηBool⟩) :
    Denotes L E.as k (FExpr.bool L) (Literals.boolType ηBool : Expr ζ ℓ n) := by
  rw [Literals.boolType, Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
  exact Denotes.ind rfl rfl rfl hη rfl nofun nofun nofun

theorem Denotes.zero (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Denotes L E.as k (FExpr.zero L) (Literals.natZero ηNat : Expr ζ ℓ n) := by
  rw [Literals.natZero, Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
  exact Denotes.ctor rfl rfl rfl rfl hη rfl rfl nofun nofun nofun nofun

theorem Denotes.succ (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩)
    {fe : FExpr} {e : Expr ζ ℓ n} :
    Denotes L E.as k fe e →
    Denotes L E.as k (FExpr.succ L fe) (Literals.natSucc ηNat e) := by
  intro h
  rw [Literals.natSucc, Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
  exact Denotes.ctor rfl rfl rfl rfl hη rfl rfl nofun nofun nofun fun ⟨0, _⟩ => h

theorem Denotes.succLit (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Denotes L E.as k (FExpr.succ L (.natLit num)) (Literals.natLit ηNat (num + 1) : Expr ζ ℓ n) :=
  Denotes.succ hη (.natLit hη)

theorem Denotes.boolLit (hη : ζ.lookup L.bool = some ⟨.inductive Literals.Bool.sig, ηBool⟩) :
    (b : Bool) →
    Denotes L E.as k (FExpr.boolLit L b) (Literals.boolLit ηBool b : Expr ζ ℓ n)
  | false => by
    rw [Literals.boolLit, Literals.boolFalse, Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
    exact Denotes.ctor rfl rfl rfl rfl hη rfl rfl nofun nofun nofun nofun
  | true => by
    rw [Literals.boolLit, Literals.boolTrue, Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
    exact Denotes.ctor rfl rfl rfl rfl hη rfl rfl nofun nofun nofun nofun

theorem Denotes.const₀ (hη : ζ.lookup pos = some ⟨.const kind 0, ηOp⟩) :
    Denotes L E.as k (.const pos #[]) (.const ηOp ![] : Expr ζ ℓ n) := by
  rw [Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
  exact Denotes.const rfl hη nofun

theorem Denotes.op₁ (hη : ζ.lookup pos = some ⟨.const kind 0, ηOp⟩)
    {fe : FExpr} {e : Expr ζ ℓ n} :
    Denotes L E.as k fe e →
    Denotes L E.as k (FExpr.op₁ pos fe) (Literals.natOp₁ ηOp e) :=
  fun h => .app (Denotes.const₀ hη) h

theorem Denotes.op₂ (hη : ζ.lookup pos = some ⟨.const kind 0, ηOp⟩)
    {fe₁ fe₂ : FExpr} {e₁ e₂ : Expr ζ ℓ n} :
    Denotes L E.as k fe₁ e₁ →
    Denotes L E.as k fe₂ e₂ →
    Denotes L E.as k (FExpr.op₂ pos fe₁ fe₂) (Literals.natOp₂ ηOp e₁ e₂) :=
  fun h₁ h₂ => .app (.app (Denotes.const₀ hη) h₁) h₂

theorem Denotes.charType (hη : ζ.lookup L.char = some ⟨.inductive Literals.Char.sig, ηChar⟩) :
    Denotes L E.as k (FExpr.char L) (.ind ηChar 0 ![] ![] ![] : Expr ζ ℓ n) := by
  rw [Fin.emptyFun ![] (⟦(![] : Fin 0 → RawLevel ℓ) ·⟧)]
  exact Denotes.ind rfl rfl rfl hη rfl nofun nofun nofun

theorem Denotes.charList (hNat : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩)
    (hList : ζ.lookup L.list = some ⟨.inductive Literals.List.sig, ηList⟩)
    (hChar : ζ.lookup L.char = some ⟨.inductive Literals.Char.sig, ηChar⟩)
    (hOfNat : ζ.lookup L.charOfNat = some ⟨.const .def 0, ηOfNat⟩) :
    (cs : List Char) →
    Denotes L E.as k (FExpr.charList L cs)
      (Literals.charList ηNat ηList ηChar ηOfNat cs : Expr ζ ℓ n)
  | [] => by
    rw [Literals.charList_nil]
    exact Denotes.ctor rfl rfl rfl rfl hList rfl rfl
      (fun ⟨0, _⟩ => .zero)
      (fun ⟨0, _⟩ => Denotes.charType hChar)
      nofun nofun
  | c :: cs => by
    rw [Literals.charList_cons]
    exact Denotes.ctor rfl rfl rfl rfl hList rfl rfl
      (fun ⟨0, _⟩ => .zero)
      (fun ⟨0, _⟩ => Denotes.charType hChar)
      (fun ⟨0, _⟩ => Denotes.op₁ hOfNat (.natLit hNat))
      (fun ⟨0, _⟩ => Denotes.charList hNat hList hChar hOfNat cs)

theorem Denotes.strLitExpand (hNat : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩)
    (hList : ζ.lookup L.list = some ⟨.inductive Literals.List.sig, ηList⟩)
    (hChar : ζ.lookup L.char = some ⟨.inductive Literals.Char.sig, ηChar⟩)
    (hOfNat : ζ.lookup L.charOfNat = some ⟨.const .def 0, ηOfNat⟩)
    (hOfList : ζ.lookup L.stringOfList = some ⟨.const .def 0, ηOfList⟩) (str : String) :
    Denotes L E.as k (FExpr.strLitExpand L str)
      (Literals.strLit ηNat ηList ηChar ηOfNat ηOfList str : Expr ζ ℓ n) :=
  Denotes.op₁ hOfList (Denotes.charList hNat hList hChar hOfNat str.toList)

theorem Denotes.ofStrLit {str : String} {e : Expr ζ ℓ n} :
    Denotes L E.as k (.strLit str) e →
    Denotes L E.as k (FExpr.strLitExpand L str) e
  | .strLit hNat hList hChar hOfNat hOfList =>
    .strLitExpand hNat hList hChar hOfNat hOfList str

theorem Denotes.natArrow (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Denotes L E.as k (FExpr.natArrow L) (Literals.natArrow ηNat : Expr ζ ℓ n) :=
  .forallE (Denotes.nat hη) (Denotes.nat hη)

theorem Denotes.natArrow₂ (hη : ζ.lookup L.nat = some ⟨.inductive Literals.Nat.sig, ηNat⟩) :
    Denotes L E.as k (FExpr.natArrow₂ L) (Literals.natArrow₂ ηNat : Expr ζ ℓ n) :=
  .forallE (Denotes.nat hη) (Denotes.natArrow hη)

end FExpr

end Metalean.FastChecker
