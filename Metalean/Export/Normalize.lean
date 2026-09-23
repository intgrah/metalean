/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Export.Basic
public import Metalean.Level.Inst

@[expose] public section

namespace Metalean

namespace Export

namespace Expr

def rename (ρ : Nat → Nat) : Expr → Expr
  | .bvar i => .bvar (ρ i)
  | .app f a => .app (f.rename ρ) (a.rename ρ)
  | .lam t b => .lam (t.rename ρ) (b.rename fun | 0 => 0 | i + 1 => ρ i + 1)
  | .forallE t b => .forallE (t.rename ρ) (b.rename fun | 0 => 0 | i + 1 => ρ i + 1)
  | .letE t v b =>
    .letE (t.rename ρ) (v.rename ρ) (b.rename fun | 0 => 0 | i + 1 => ρ i + 1)
  | .proj name idx e => .proj name idx (e.rename ρ)
  | e => e

def subst (σ : Nat → Expr) : Expr → Expr
  | .bvar i => σ i
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .lam t b => .lam (t.subst σ) (b.subst fun | 0 => .bvar 0 | i + 1 => (σ i).rename (· + 1))
  | .forallE t b =>
    .forallE (t.subst σ) (b.subst fun | 0 => .bvar 0 | i + 1 => (σ i).rename (· + 1))
  | .letE t v b =>
    .letE (t.subst σ) (v.subst σ) (b.subst fun | 0 => .bvar 0 | i + 1 => (σ i).rename (· + 1))
  | .proj name idx e => .proj name idx (e.subst σ)
  | e => e

def inst (e' v : Expr) : Expr := e'.subst fun | 0 => v | i + 1 => .bvar i

end Expr

def Level.inst (σ : Lean.Name → Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (l.inst σ)
  | .max l r => .max (l.inst σ) (r.inst σ)
  | .imax l r => .imax (l.inst σ) (r.inst σ)
  | .param p => σ p

instance : InstLevel (Lean.Name → Level) Level Level := ⟨Level.inst⟩

def Expr.instLevels (σ : Lean.Name → Level) : Expr → Expr
  | .sort l => .sort l{σ}
  | .const name ls => .const name ls{σ}
  | .app f a => .app (f.instLevels σ) (a.instLevels σ)
  | .lam t b => .lam (t.instLevels σ) (b.instLevels σ)
  | .forallE t b => .forallE (t.instLevels σ) (b.instLevels σ)
  | .letE t v b => .letE (t.instLevels σ) (v.instLevels σ) (b.instLevels σ)
  | .proj name idx e => .proj name idx (e.instLevels σ)
  | e => e

instance : InstLevel (Lean.Name → Level) Expr Expr := ⟨Expr.instLevels⟩

abbrev Definitions := Std.HashMap Lean.Name (List Lean.Name × Export.Expr)

/--
This is a preprocessor that does simple β-δ-reduction before inductive types are checked.
This allows (regrettably) things like:

```
inductive Foo : Type where
  | mk : Id Foo → Foo

def Set (α : Type) := α → Prop

inductive Bar (α : Type) : Set α where
  | mk (a : α) : Bar α a
```
-/
partial def whnf (defs : Definitions) : Export.Expr → Export.Expr
  | .const name ls =>
    match defs.get? name with
    | some (params, value) =>
      if params.length = ls.length then
        whnf defs (value.instLevels fun p =>
          ((params.zip ls).lookup p).getD (.param p))
      else .const name ls
    | none => .const name ls
  | .app f a =>
    match whnf defs f with
    | .lam _ b => whnf defs (b.inst a)
    | f => .app f a
  | .letE _ v b => whnf defs (b.inst v)
  | e => e

end Export

end Metalean
