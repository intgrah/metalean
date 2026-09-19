/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Lean.Data.Json.Parser
public import Std.Data.HashMap.Basic

@[expose] public section

namespace Metalean.Export

open Lean (Name Json)

inductive Level where
  | zero
  | succ (l : Level)
  | max (l₁ l₂ : Level)
  | imax (l₁ l₂ : Level)
  | param (name : Name)
deriving DecidableEq, Repr

def maskUnder (m : UInt64) : UInt64 := (m >>> 1) ||| (m &&& ((1 : UInt64) <<< 63))

inductive Expr where
  | bvar (i : Nat)
  | sort (l : Level)
  | const (name : Name) (levels : List Level)
  | app (fn arg : Expr)
  | lam (type body : Expr)
  | forallE (type body : Expr)
  | letE (type value body : Expr)
  | proj (typeName : Name) (idx : Nat) (struct : Expr)
  | natLit (n : Nat)
  | stringLit (s : String)
with
  @[computed_field] looseMask : Expr → UInt64
    | .bvar i => if i ≥ 63 then (1 : UInt64) <<< 63 else (1 : UInt64) <<< i.toUInt64
    | .sort _ | .const _ _ | .natLit _ | .stringLit _ => 0
    | .app f a => f.looseMask ||| a.looseMask
    | .lam t b | .forallE t b => t.looseMask ||| maskUnder b.looseMask
    | .letE t v b => t.looseMask ||| v.looseMask ||| maskUnder b.looseMask
    | .proj _ _ s => s.looseMask
deriving DecidableEq, Repr

inductive Safety where
  | safe
  | «unsafe»
  | «partial»
deriving DecidableEq, Repr

inductive Hints where
  | «opaque»
  | abbrev
  | regular (height : Nat)
deriving DecidableEq, Repr

inductive QuotKind where
  | type
  | ctor
  | lift
  | ind
deriving DecidableEq, Repr

structure ConstantDecl where
  name : Name
  levelParams : List Name
  type : Expr
deriving DecidableEq, Repr

structure InductiveType where
  name : Name
  levelParams : List Name
  type : Expr
  numParams : Nat
  numIndices : Nat
  ctors : List Name
  numNested : Nat
  isUnsafe : Bool
deriving DecidableEq, Repr

structure Constructor where
  name : Name
  levelParams : List Name
  type : Expr
deriving DecidableEq, Repr

inductive Decl where
  | «axiom» (c : ConstantDecl) (isUnsafe : Bool)
  | «def» (c : ConstantDecl) (value : Expr) (safety : Safety) (hints : Hints)
  | «theorem» (c : ConstantDecl) (value : Expr)
  | «opaque» (c : ConstantDecl) (value : Expr) (isUnsafe : Bool)
  | quot (c : ConstantDecl) (kind : QuotKind)
  | «inductive» (types : List InductiveType) (ctors : List Constructor) (recNames : List Name)
deriving DecidableEq, Repr

def Decl.name : Decl → Name
  | .axiom c _
  | .def c _ _ _
  | .theorem c _
  | .opaque c _ _
  | .quot c _ =>
    c.name
  | .inductive types _ _ => (types.head?.map (·.name)).getD .anonymous

def refPatterns : Array ByteArray :=
  #["\"fn\":", "\"arg\":", "\"type\":", "\"body\":", "\"value\":", "\"struct\":", "\"rhs\":",
      "\"expr\":"].map String.toUTF8

def defPattern : ByteArray := "\"ie\":".toUTF8

def matchAt (b p : ByteArray) (i : Nat) : Bool := Id.run do
  if i + p.size > b.size then return false
  for j in [0 : p.size] do
    if b[i + j]! != p[j]! then return false
  return true

def digitsAt (b : ByteArray) (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut j := i
  let mut n := 0
  while j < b.size && 48 ≤ b[j]! && b[j]! ≤ 57 do
    n := n * 10 + (b[j]!.toNat - 48)
    j := j + 1
  return if j = i then none else some (n, j)

def defIndex (b : ByteArray) : Option Nat := Id.run do
  let mut i := 0
  while i < b.size do
    if matchAt b defPattern i then
      return (digitsAt b (i + defPattern.size)).map (·.1)
    i := i + 1
  return none

@[specialize]
def foldRefs {σ : Type} (b : ByteArray) (init : σ) (f : σ → Nat → σ) : σ := Id.run do
  let mut acc := init
  let mut i := 0
  while i < b.size do
    let mut hit := 0
    if b[i]! == 34 then
      for p in refPatterns do
        if matchAt b p i then
          hit := p.size
          break
    if hit == 0 then
      i := i + 1
    else
      match digitsAt b (i + hit) with
      | some (n, j) => acc := f acc n; i := j
      | none => i := i + hit
  return acc

structure Tables where
  names : Std.HashMap Nat Name := ∅
  levels : Std.HashMap Nat Level := ∅
  exprs : Std.HashMap Nat Expr := ∅

namespace Tables

def name? (t : Tables) (j : Json) : Except String Name := do
  let i ← j.getNat?
  if i = 0 then pure .anonymous
  else
    match t.names.get? i with
    | some n => pure n
    | none => throw "name"

def level? (t : Tables) (j : Json) : Except String Level := do
  let i ← j.getNat?
  if i = 0 then pure .zero
  else
    match t.levels.get? i with
    | some l => pure l
    | none => throw "level"

def expr? (t : Tables) (j : Json) : Except String Expr := do
  let i ← j.getNat?
  match t.exprs.get? i with
  | some e => pure e
  | none => throw "expr"

def nameAt (t : Tables) (o : Json) (key : String) : Except String Name := do
  t.name? (← o.getObjVal? key)

def namesAt (t : Tables) (o : Json) (key : String) : Except String (List Name) := do
  (← (← o.getObjVal? key).getArr?).toList.mapM t.name?

def levelsAt (t : Tables) (o : Json) (key : String) : Except String (List Level) := do
  (← (← o.getObjVal? key).getArr?).toList.mapM t.level?

def exprAt (t : Tables) (o : Json) (key : String) : Except String Expr := do
  t.expr? (← o.getObjVal? key)

def levelPair (t : Tables) (o : Json) : Except String (Level × Level) := do
  let [a, b] := (← o.getArr?).toList | throw "level pair"
  pure (← t.level? a, ← t.level? b)

end Tables

def natAt (o : Json) (key : String) : Except String Nat := do
  (← o.getObjVal? key).getNat?

def boolAt (o : Json) (key : String) : Except String Bool := do
  (← o.getObjVal? key).getBool?

def stringAt (o : Json) (key : String) : Except String String := do
  (← o.getObjVal? key).getStr?

def payload (idKey : String) (j : Json) : Except String (Nat × String × Json) := do
  let kvs ← j.getObj?
  let some id := kvs.get? idKey | throw idKey
  let [(key, o)] := (kvs.erase idKey).toList | throw "payload"
  pure (← id.getNat?, key, o)

def parseName (t : Tables) (j : Json) : Except String Tables := do
  let (i, key, o) ← payload "in" j
  let pre ← t.nameAt o "pre"
  let n ← match key with
    | "str" => Name.str pre <$> stringAt o "str"
    | "num" => Name.num pre <$> natAt o "i"
    | _ => throw "name"
  have ⟨names, levels, exprs⟩ := t
  pure ⟨names.insert i n, levels, exprs⟩

def parseLevel (t : Tables) (j : Json) : Except String Tables := do
  let (i, key, o) ← payload "il" j
  let l ← match key with
    | "succ" => Level.succ <$> t.level? o
    | "max" => do let (a, b) ← t.levelPair o; pure (.max a b)
    | "imax" => do let (a, b) ← t.levelPair o; pure (.imax a b)
    | "param" => Level.param <$> t.name? o
    | _ => throw "level"
  have ⟨names, levels, exprs⟩ := t
  pure ⟨names, levels.insert i l, exprs⟩

def parseExpr (t : Tables) (j : Json) : Except String Tables := do
  let (i, key, o) ← payload "ie" j
  let e ← match key with
    | "bvar" => Expr.bvar <$> o.getNat?
    | "sort" => Expr.sort <$> t.level? o
    | "const" => do pure (.const (← t.nameAt o "name") (← t.levelsAt o "us"))
    | "app" => do pure (.app (← t.exprAt o "fn") (← t.exprAt o "arg"))
    | "lam" => do pure (.lam (← t.exprAt o "type") (← t.exprAt o "body"))
    | "forallE" => do pure (.forallE (← t.exprAt o "type") (← t.exprAt o "body"))
    | "letE" => do
      pure (.letE (← t.exprAt o "type") (← t.exprAt o "value") (← t.exprAt o "body"))
    | "proj" => do
      pure (.proj (← t.nameAt o "typeName") (← natAt o "idx") (← t.exprAt o "struct"))
    | "natVal" => do
      let some n := (← o.getStr?).toNat? | throw "natVal"
      pure (.natLit n)
    | "strVal" => Expr.stringLit <$> o.getStr?
    | "mdata" => t.exprAt o "expr"
    | _ => throw "expr"
  have ⟨names, levels, exprs⟩ := t
  pure ⟨names, levels, exprs.insert i e⟩

def parseConstant (t : Tables) (o : Json) : Except String ConstantDecl := do
  pure {
    name := ← t.nameAt o "name"
    levelParams := ← t.namesAt o "levelParams"
    type := ← t.exprAt o "type" }

def parseSafety (o : Json) : Except String Safety := do
  match ← stringAt o "safety" with
  | "safe" => pure .safe
  | "unsafe" => pure .unsafe
  | "partial" => pure .partial
  | _ => throw "safety"

def parseHints (o : Json) : Except String Hints := do
  let h ← o.getObjVal? "hints"
  match h with
  | .str "opaque" => pure .opaque
  | .str "abbrev" => pure .abbrev
  | .obj _ => pure (.regular (← natAt h "regular"))
  | _ => throw "hints"

def parseQuotKind (o : Json) : Except String QuotKind := do
  match ← stringAt o "kind" with
  | "type" => pure .type
  | "ctor" => pure .ctor
  | "lift" => pure .lift
  | "ind" => pure .ind
  | _ => throw "quot kind"

def parseInductiveType (t : Tables) (o : Json) : Except String InductiveType := do
  pure {
    name := ← t.nameAt o "name"
    levelParams := ← t.namesAt o "levelParams"
    type := ← t.exprAt o "type"
    numParams := ← natAt o "numParams"
    numIndices := ← natAt o "numIndices"
    ctors := ← t.namesAt o "ctors"
    numNested := ← natAt o "numNested"
    isUnsafe := ← boolAt o "isUnsafe" }

def parseConstructor (t : Tables) (o : Json) : Except String Constructor := do
  pure {
    name := ← t.nameAt o "name"
    levelParams := ← t.namesAt o "levelParams"
    type := ← t.exprAt o "type" }

def arrayAt (o : Json) (key : String) : Except String (List Json) := do
  pure (← (← o.getObjVal? key).getArr?).toList

def parseDecl (t : Tables) (j : Json) : Except String (Option Decl) := do
  let [(key, o)] := (← j.getObj?).toList | throw "declaration"
  match key with
  | "axiom" => do pure (some (.axiom (← parseConstant t o) (← boolAt o "isUnsafe")))
  | "def" => do
    pure (some (.def (← parseConstant t o) (← t.exprAt o "value") (← parseSafety o)
      (← parseHints o)))
  | "thm" => do pure (some (.theorem (← parseConstant t o) (← t.exprAt o "value")))
  | "opaque" => do
    pure (some (.opaque (← parseConstant t o) (← t.exprAt o "value") (← boolAt o "isUnsafe")))
  | "quot" => do pure (some (.quot (← parseConstant t o) (← parseQuotKind o)))
  | "inductive" => do
    let types ← (← arrayAt o "types").mapM (parseInductiveType t)
    let ctors ← (← arrayAt o "ctors").mapM (parseConstructor t)
    let recs ← (← arrayAt o "recs").mapM fun r => t.nameAt r "name"
    pure (some (.inductive types ctors recs))
  | "meta" => pure none
  | _ => throw "declaration"

def growTo (a : Array UInt32) (n : Nat) : Array UInt32 :=
  if a.size < n then growTo (a.push 0) n else a
termination_by n - a.size

def noteRefs (lastUse : Array UInt32) (b : ByteArray) (lineNo : Nat) : Array UInt32 :=
  let lastUse := match defIndex b with
    | some i => (growTo lastUse (i + 1)).set! i lineNo.toUInt32
    | none => lastUse
  foldRefs b lastUse fun a i => if i < a.size then a.set! i lineNo.toUInt32 else a

def evict (exprs : Std.HashMap Nat Expr) (lastUse : Array UInt32) (b : ByteArray) (lineNo : Nat) :
    Std.HashMap Nat Expr :=
  let dead (i : Nat) : Bool := lastUse[i]? == some lineNo.toUInt32
  let exprs := match defIndex b with
    | some i => if dead i then exprs.erase i else exprs
    | none => exprs
  foldRefs b exprs fun m i => if dead i then m.erase i else m

def parseLine (t : Tables) (lastUse : Array UInt32) (lineNo : Nat) (line : String) :
    Except String (Tables × Option Decl) := do
  let j ← Json.parse line
  let kvs ← j.getObj?
  if kvs.contains "in" then pure (← parseName t j, none)
  else if kvs.contains "il" then pure (← parseLevel t j, none)
  else
    let (t, d) ←
      if kvs.contains "ie" then pure (← parseExpr t j, none)
      else pure (t, ← parseDecl t j)
    have ⟨names, levels, exprs⟩ := t
    pure (⟨names, levels, evict exprs lastUse line.toUTF8 lineNo⟩, d)

def scanDecl (t : Tables) (j : Json) : Except String (Option (List Name)) := do
  let [(key, o)] := (← j.getObj?).toList | throw "declaration"
  match key with
  | "axiom" | "def" | "thm" | "opaque" => do pure (some [← t.nameAt o "name"])
  | "quot" => do
    match ← parseQuotKind o with
    | .type => pure (some [← t.nameAt o "name"])
    | _ => pure none
  | "inductive" => do
    pure (some (← (← arrayAt o "types").mapM fun ty => t.nameAt ty "name"))
  | "meta" => pure none
  | _ => throw "declaration"

def scanLine (t : Tables) (line : String) : Except String (Tables × Option (List Name)) := do
  let interesting := ["{\"in\"", "{\"str\"", "{\"num\"", "{\"def\"", "{\"thm\"", "{\"axiom\"",
    "{\"opaque\"", "{\"quot\"", "{\"inductive\"", "{\"meta\""]
  unless interesting.any (fun p => line.startsWith p) do return (t, none)
  let j ← Json.parse line
  let kvs ← j.getObj?
  if kvs.contains "in" then pure (← parseName t j, none)
  else pure (t, ← scanDecl t j)

end Metalean.Export
