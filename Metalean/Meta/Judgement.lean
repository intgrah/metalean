/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public meta import Lean.Parser.Command
import Lean.Parser.Command

@[expose] public section

namespace Metalean.Meta

open Lean Parser Elab Command

syntax judgementBar := "─" (noWs "─")*

syntax judgementRule :=
  ppLine ppLine (docComment)?
  withPosition(manyIndent(withPosition(term))
    judgementBar ppSpace ident (ppSpace colGt bracketedBinder)*
    ppLine withPosition(term))

syntax (name := judgement)
  declModifiers "judgement " declId (ppSpace bracketedBinder)*
  (" : " term)? (" where")?
  manyIndent(judgementRule) : command

@[macro «judgement»]
meta def expandJudgement : Macro
  | .node _ _ #[mods, _, id, binders, sig, _, rules] => do
    let ctors ← rules.getArgs.mapM fun rule => do
      let premises : Array Term := rule[1].getArgs.map (⟨·⟩)
      let name : Ident := ⟨rule[3]⟩
      let bs : Array (TSyntax ``Term.bracketedBinder) := rule[4].getArgs.map (⟨·⟩)
      let ctorType ← premises.foldrM (fun p acc => `($p → $acc)) (⟨rule[5]⟩ : Term)
      match rule[0].getOptional? with
      | some d =>
        let doc : TSyntax ``docComment := ⟨d⟩
        `(Command.ctor| $doc:docComment | $name:ident $bs* : $ctorType)
      | none => `(Command.ctor| | $name:ident $bs* : $ctorType)
    let mods : TSyntax ``declModifiers := ⟨mods⟩
    let id : TSyntax ``declId := ⟨id⟩
    let bs : Array (TSyntax ``Term.bracketedBinder) := binders.getArgs.map (⟨·⟩)
    if sig.getNumArgs == 0 then
      `(command| $mods:declModifiers inductive $id:declId $bs* where $ctors*)
    else
      let ty : Term := ⟨sig[1]⟩
      `(command| $mods:declModifiers inductive $id:declId $bs* : $ty where $ctors*)
  | _ => Macro.throwUnsupported
