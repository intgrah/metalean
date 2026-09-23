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

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

partial def skipWs (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then
    let c := b[i]
    if c == 32 || c == 9 || c == 13 || c == 10 then skipWs b (i + 1) else i
  else i

partial def digits (b : ByteArray) (i n : Nat) : Nat × Nat :=
  if h : i < b.size then
    let c := b[i]
    if isDigit c then digits b (i + 1) (n * 10 + (c - 48).toNat) else (n, i)
  else (n, i)

partial def stringEnd (b : ByteArray) (i : Nat) (escaped : Bool) : Option (Nat × Bool) :=
  if h : i < b.size then
    let c := b[i]
    if c == 34 then some (i, escaped)
    else if c == 92 then stringEnd b (i + 2) true
    else stringEnd b (i + 1) escaped
  else none

partial def spanIs (b : ByteArray) (s e : Nat) (lit : ByteArray) (k : Nat := 0) : Bool :=
  if k = 0 && e - s != lit.size then false
  else if h : k < lit.size then
    b[s + k]! == lit[k] && spanIs b s e lit (k + 1)
  else true

partial def keyCode (b : ByteArray) (s e : Nat) (k : Nat := 0) (acc : UInt64 := 0) : UInt64 :=
  if 8 < e - s then 0
  else if h : s + k < e ∧ s + k < b.size then
    keyCode b s e (k + 1) (acc ||| (b[s + k].toUInt64 <<< (8 * k).toUInt64))
  else acc

def code (key : String) : UInt64 :=
  let b := key.toUTF8
  keyCode b 0 b.size

def refCodes : Array UInt64 :=
  #["fn", "arg", "type", "body", "value", "struct", "rhs", "expr"].map code

def defCode : UInt64 := code "ie"

@[specialize]
partial def foldIds {σ : Type} (b : ByteArray) (f : σ → Bool → Nat → σ) (i : Nat) (acc : σ) : σ :=
  if h : i < b.size then
    if b[i] == 34 then
      match stringEnd b (i + 1) false with
      | none => acc
      | some (j, _) =>
        let k := skipWs b (j + 1)
        if k < b.size && b[k]! == 58 then
          let v := skipWs b (k + 1)
          if v < b.size && isDigit b[v]! then
            let (n, e) := digits b v 0
            let c := keyCode b (i + 1) j
            if c == defCode then foldIds b f e (f acc true n)
            else if refCodes.contains c then foldIds b f e (f acc false n)
            else foldIds b f e acc
          else foldIds b f v acc
        else foldIds b f (j + 1) acc
    else foldIds b f (i + 1) acc
  else acc

def literalAt (b : ByteArray) (i : Nat) (lit : ByteArray) : Bool :=
  i + lit.size ≤ b.size && spanIs b i (i + lit.size) lit

def jsonString (b : ByteArray) (s e : Nat) : Option String :=
  String.fromUTF8? (b.extract s e)

mutual

partial def jsonValue (b : ByteArray) (i : Nat) : Option (Json × Nat) :=
  let i := skipWs b i
  if h : i < b.size then
    let c := b[i]
    if c == 123 then jsonObject b (skipWs b (i + 1)) []
    else if c == 91 then jsonArray b (skipWs b (i + 1)) #[]
    else if c == 34 then do
      let (e, escaped) ← stringEnd b (i + 1) false
      if escaped then none
      pure (.str (← jsonString b (i + 1) e), e + 1)
    else if isDigit c then
      let (n, e) := digits b i 0
      if e < b.size && (b[e]! == 46 || b[e]! == 101 || b[e]! == 69) then none
      else some ((n : Json), e)
    else if literalAt b i "true".toUTF8 then some (.bool true, i + 4)
    else if literalAt b i "false".toUTF8 then some (.bool false, i + 5)
    else if literalAt b i "null".toUTF8 then some (.null, i + 4)
    else none
  else none

partial def jsonObject (b : ByteArray) (i : Nat) (acc : List (String × Json)) :
    Option (Json × Nat) := do
  if acc.isEmpty && i < b.size && b[i]! == 125 then return (Json.mkObj [], i + 1)
  unless i < b.size && b[i]! == 34 do none
  let (e, escaped) ← stringEnd b (i + 1) false
  if escaped then none
  let key ← jsonString b (i + 1) e
  let k := skipWs b (e + 1)
  unless k < b.size && b[k]! == 58 do none
  let (v, j) ← jsonValue b (k + 1)
  let acc := (key, v) :: acc
  let j := skipWs b j
  if j < b.size && b[j]! == 44 then jsonObject b (skipWs b (j + 1)) acc
  else if j < b.size && b[j]! == 125 then some (Json.mkObj acc.reverse, j + 1)
  else none

partial def jsonArray (b : ByteArray) (i : Nat) (acc : Array Json) : Option (Json × Nat) := do
  if acc.isEmpty && i < b.size && b[i]! == 93 then return (.arr #[], i + 1)
  let (v, j) ← jsonValue b i
  let acc := acc.push v
  let j := skipWs b j
  if j < b.size && b[j]! == 44 then jsonArray b (skipWs b (j + 1)) acc
  else if j < b.size && b[j]! == 93 then some (.arr acc, j + 1)
  else none

end

def parseJson (b : ByteArray) : Except String Json :=
  match jsonValue b 0 with
  | some (j, e) => if skipWs b e = b.size then pure j else fallback
  | none => fallback
where
  fallback : Except String Json := do
    let some line := String.fromUTF8? b | throw "utf8"
    Json.parse line

def put {α : Type} (a : Array (Option α)) (i : Nat) (v : α) : Array (Option α) :=
  if i < a.size then a.set! i (some v) else put (a.push none) i v
termination_by i + 1 - a.size

structure Tables where
  names : Array (Option Name) := #[]
  levels : Array (Option Level) := #[]
  exprs : Array (Option Expr) := #[]

namespace Tables

def getName? (t : Tables) (i : Nat) : Option Name :=
  if i = 0 then some .anonymous else t.names[i]?.join

def getLevel? (t : Tables) (i : Nat) : Option Level :=
  if i = 0 then some .zero else t.levels[i]?.join

def getExpr? (t : Tables) (i : Nat) : Option Expr :=
  t.exprs[i]?.join

def name? (t : Tables) (j : Json) : Except String Name := do
  let some n := t.getName? (← j.getNat?) | throw "name"
  pure n

def level? (t : Tables) (j : Json) : Except String Level := do
  let some l := t.getLevel? (← j.getNat?) | throw "level"
  pure l

def expr? (t : Tables) (j : Json) : Except String Expr := do
  let some e := t.getExpr? (← j.getNat?) | throw "expr"
  pure e

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
  pure ⟨put names i n, levels, exprs⟩

def parseLevel (t : Tables) (j : Json) : Except String Tables := do
  let (i, key, o) ← payload "il" j
  let l ← match key with
    | "succ" => Level.succ <$> t.level? o
    | "max" => do let (a, b) ← t.levelPair o; pure (.max a b)
    | "imax" => do let (a, b) ← t.levelPair o; pure (.imax a b)
    | "param" => Level.param <$> t.name? o
    | _ => throw "level"
  have ⟨names, levels, exprs⟩ := t
  pure ⟨names, put levels i l, exprs⟩

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
  pure ⟨names, levels, put exprs i e⟩

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
  foldIds b (fun a isDef i =>
    if isDef then (growTo a (i + 1)).set! i lineNo.toUInt32
    else if i < a.size then a.set! i lineNo.toUInt32 else a) 0 lastUse

def evictId (lastUse : Array UInt32) (lineNo : Nat) (exprs : Array (Option Expr)) (i : Nat) :
    Array (Option Expr) :=
  if lastUse[i]? == some lineNo.toUInt32 && i < exprs.size then exprs.set! i none else exprs

def evict (exprs : Array (Option Expr)) (lastUse : Array UInt32) (b : ByteArray) (lineNo : Nat) :
    Array (Option Expr) :=
  foldIds b (fun m _ i => evictId lastUse lineNo m i) 0 exprs

def fieldCodes : Array UInt64 :=
  #["pre", "i", "name", "fn", "arg", "type", "body", "value", "idx", "struct", "typeName",
    "expr"].map code

def exprFields : List Nat := [3, 4, 5, 6, 7, 9, 11]


partial def numArray (b : ByteArray) (i : Nat) (acc : Array Nat) : Option (Array Nat × Nat) :=
  if acc.isEmpty && i < b.size && b[i]! == 93 then some (acc, i + 1)
  else if i < b.size && isDigit b[i]! then
    let (n, j) := digits b i 0
    let j := skipWs b j
    if j < b.size && b[j]! == 44 then numArray b (skipWs b (j + 1)) (acc.push n)
    else if j < b.size && b[j]! == 93 then some (acc.push n, j + 1)
    else none
  else none

def usCode : UInt64 := code "us"
def strCode : UInt64 := code "str"
def numCode : UInt64 := code "num"
def succCode : UInt64 := code "succ"
def maxCode : UInt64 := code "max"
def imaxCode : UInt64 := code "imax"
def paramCode : UInt64 := code "param"
def bvarCode : UInt64 := code "bvar"
def sortCode : UInt64 := code "sort"
def constCode : UInt64 := code "const"
def appCode : UInt64 := code "app"
def lamCode : UInt64 := code "lam"
def forallCode : UInt64 := code "forallE"
def letCode : UInt64 := code "letE"
def projCode : UInt64 := code "proj"
def mdataCode : UInt64 := code "mdata"

structure Fields where
  nums : Array (Option Nat) := .replicate fieldCodes.size none
  str : Option String := none
  us : Array Nat := #[]

def Fields.get? (f : Fields) (k : Nat) : Option Nat := f.nums[k]?.join

partial def fieldsObject (b : ByteArray) (i : Nat) (f : Fields) : Option (Fields × Nat) := do
  if i < b.size && b[i]! == 125 then return (f, i + 1)
  unless i < b.size && b[i]! == 34 do none
  let (e, escaped) ← stringEnd b (i + 1) false
  if escaped then none
  let k := skipWs b (e + 1)
  unless k < b.size && b[k]! == 58 do none
  let v := skipWs b (k + 1)
  let c := keyCode b (i + 1) e
  let (f, j) ←
    if v < b.size && isDigit b[v]! then
      let (n, j) := digits b v 0
      match fieldCodes.idxOf? c with
      | some x => pure ({ f with nums := f.nums.set! x (some n) }, j)
      | none => pure (f, j)
    else if c == usCode && v < b.size && b[v]! == 91 then do
      let (us, j) ← numArray b (skipWs b (v + 1)) #[]
      pure ({ f with us }, j)
    else if c == strCode && v < b.size && b[v]! == 34 then do
      let (se, escaped) ← stringEnd b (v + 1) false
      if escaped then none
      pure ({ f with str := some (← jsonString b (v + 1) se) }, se + 1)
    else do
      let (_, j) ← jsonValue b v
      pure (f, j)
  let j := skipWs b j
  if j < b.size && b[j]! == 44 then fieldsObject b (skipWs b (j + 1)) f
  else if j < b.size && b[j]! == 125 then some (f, j + 1)
  else none

inductive Item where
  | name (n : Name)
  | level (l : Level)
  | expr (e : Expr) (refs : List Nat)

def fastPayload (t : Tables) (b : ByteArray) (s e v : Nat) : Option (Item × Nat) := do
  let c := keyCode b s e
  let num : Option (Nat × Nat) :=
    if v < b.size && isDigit b[v]! then some (digits b v 0) else none
  let obj : Option (Fields × Nat) :=
    if v < b.size && b[v]! == 123 then fieldsObject b (skipWs b (v + 1)) {} else none
  let pair : Option (Nat × Nat × Nat) := do
    unless v < b.size && b[v]! == 91 do none
    let (#[a, c], j) ← numArray b (skipWs b (v + 1)) #[] | none
    pure (a, c, j)
  let exprItem (x : Expr) (f : Fields) (j : Nat) : Item × Nat :=
    (.expr x (exprFields.filterMap f.get?), j)
  if c == strCode then
    let (f, j) ← obj
    pure (.name (.str (← t.getName? (← f.get? 0)) (← f.str)), j)
  else if c == numCode then
    let (f, j) ← obj
    pure (.name (.num (← t.getName? (← f.get? 0)) (← f.get? 1)), j)
  else if c == succCode then
    let (n, j) ← num
    pure (.level (.succ (← t.getLevel? n)), j)
  else if c == maxCode then
    let (a, c, j) ← pair
    pure (.level (.max (← t.getLevel? a) (← t.getLevel? c)), j)
  else if c == imaxCode then
    let (a, c, j) ← pair
    pure (.level (.imax (← t.getLevel? a) (← t.getLevel? c)), j)
  else if c == paramCode then
    let (n, j) ← num
    pure (.level (.param (← t.getName? n)), j)
  else if c == bvarCode then
    let (n, j) ← num
    pure (.expr (.bvar n) [], j)
  else if c == sortCode then
    let (n, j) ← num
    pure (.expr (.sort (← t.getLevel? n)) [], j)
  else if c == constCode then
    let (f, j) ← obj
    pure (.expr (.const (← t.getName? (← f.get? 2)) (← f.us.toList.mapM t.getLevel?)) [], j)
  else if c == appCode then
    let (f, j) ← obj
    pure (exprItem (.app (← t.getExpr? (← f.get? 3)) (← t.getExpr? (← f.get? 4))) f j)
  else if c == lamCode then
    let (f, j) ← obj
    pure (exprItem (.lam (← t.getExpr? (← f.get? 5)) (← t.getExpr? (← f.get? 6))) f j)
  else if c == forallCode then
    let (f, j) ← obj
    pure (exprItem (.forallE (← t.getExpr? (← f.get? 5)) (← t.getExpr? (← f.get? 6))) f j)
  else if c == letCode then
    let (f, j) ← obj
    pure (exprItem (.letE (← t.getExpr? (← f.get? 5)) (← t.getExpr? (← f.get? 7))
      (← t.getExpr? (← f.get? 6))) f j)
  else if c == projCode then
    let (f, j) ← obj
    pure (exprItem (.proj (← t.getName? (← f.get? 10)) (← f.get? 8)
      (← t.getExpr? (← f.get? 9))) f j)
  else if c == mdataCode then
    let (f, j) ← obj
    pure (exprItem (← t.getExpr? (← f.get? 11)) f j)
  else none

def idCodes : Array UInt64 := #["in", "il", "ie"].map code

partial def fastItem (t : Tables) (b : ByteArray) (i : Nat) (id : Option (Nat × Nat))
    (item : Option Item) : Option (Nat × Nat × Item) := do
  unless i < b.size && b[i]! == 34 do none
  let (e, escaped) ← stringEnd b (i + 1) false
  if escaped then none
  let k := skipWs b (e + 1)
  unless k < b.size && b[k]! == 58 do none
  let v := skipWs b (k + 1)
  let (id, item, j) ←
    if let some tag := idCodes.idxOf? (keyCode b (i + 1) e) then do
      unless v < b.size && isDigit b[v]! do none
      let (n, j) := digits b v 0
      pure (some (tag, n), item, j)
    else do
      let (x, j) ← fastPayload t b (i + 1) e v
      pure (id, some x, j)
  let j := skipWs b j
  if j < b.size && b[j]! == 44 then fastItem t b (skipWs b (j + 1)) id item
  else if j < b.size && b[j]! == 125 && skipWs b (j + 1) = b.size then
    match id, item with
    | some (tag, n), some x => some (tag, n, x)
    | _, _ => none
  else none

def fastLine (t : Tables) (b : ByteArray) : Option (Nat × Nat × Item) := do
  unless 0 < b.size && b[0]! == 123 do none
  fastItem t b (skipWs b 1) none none

def Tables.add (t : Tables) (lastUse : Array UInt32) (lineNo : Nat) :
    Nat × Nat × Item → Except String Tables
  | (0, i, .name n) => have ⟨names, levels, exprs⟩ := t; pure ⟨put names i n, levels, exprs⟩
  | (1, i, .level l) => have ⟨names, levels, exprs⟩ := t; pure ⟨names, put levels i l, exprs⟩
  | (2, i, .expr x refs) =>
    have ⟨names, levels, exprs⟩ := t
    pure ⟨names, levels, (i :: refs).foldl (evictId lastUse lineNo) (put exprs i x)⟩
  | _ => throw "id"

def parseLine (t : Tables) (lastUse : Array UInt32) (lineNo : Nat) (line : ByteArray) :
    Except String (Tables × Option Decl) := do
  if let some x := fastLine t line then return (← t.add lastUse lineNo x, none)
  let j ← parseJson line
  let kvs ← j.getObj?
  if kvs.contains "in" then pure (← parseName t j, none)
  else if kvs.contains "il" then pure (← parseLevel t j, none)
  else
    let (t, d) ←
      if kvs.contains "ie" then pure (← parseExpr t j, none)
      else pure (t, ← parseDecl t j)
    have ⟨names, levels, exprs⟩ := t
    pure (⟨names, levels, evict exprs lastUse line lineNo⟩, d)

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

def scanCodes : Array UInt64 :=
  #["in", "str", "num", "def", "thm", "axiom", "opaque", "quot", "meta"].map code

def inductiveKey : ByteArray := "inductive".toUTF8

def firstKey? (b : ByteArray) : Option (Nat × Nat) := do
  unless 1 < b.size && b[0]! == 123 && b[1]! == 34 do none
  let (e, _) ← stringEnd b 2 false
  pure (2, e)

def scanLine (t : Tables) (line : ByteArray) : Except String (Tables × Option (List Name)) := do
  let some (s, e) := firstKey? line | return (t, none)
  unless scanCodes.contains (keyCode line s e) || spanIs line s e inductiveKey do return (t, none)
  let j ← parseJson line
  let kvs ← j.getObj?
  if kvs.contains "in" then pure (← parseName t j, none)
  else pure (t, ← scanDecl t j)

end Metalean.Export
