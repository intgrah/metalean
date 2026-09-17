/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Aczel.Spine

/-!
# ZF DSL
-/

@[expose] public section

declare_syntax_cat zfTerm
declare_syntax_cat zfBinder
syntax rawIdent : zfTerm
syntax "∅" : zfTerm
syntax "$(" term ")" : zfTerm
syntax "(" zfTerm ")" : zfTerm
syntax "(" zfTerm ", " zfTerm ")" : zfTerm
syntax "![" zfTerm,* "]" : zfTerm
syntax:max (name := zfIdentProj) rawIdent noWs "." noWs num : zfTerm
syntax:1023 (name := zfProj) zfTerm:1023 noWs "." noWs num : zfTerm
syntax:70 zfTerm:70 ppSpace zfTerm:71 : zfTerm
syntax:70 zfTerm:70 ppSpace zfTerm:71 noWs "..." : zfTerm
syntax "(" ident+ " : " zfTerm ")" : zfBinder
syntax:65 "fun " ident+ " : " zfTerm " => " zfTerm : zfTerm
syntax:65 "fun " hole " : " zfTerm " => " zfTerm : zfTerm
syntax:65 "fun " zfBinder+ " => " zfTerm : zfTerm
syntax:60 zfBinder " → " zfTerm:60 : zfTerm
syntax:60 zfTerm:61 " → " zfTerm:60 : zfTerm
syntax "[zf|" zfTerm "]" : term

private meta def expandBinders (binders : Array (Lean.TSyntax `zfBinder))
    (body : Lean.TSyntax `zfTerm)
    (wrap : Lean.TSyntax `zfTerm → Lean.Ident → Lean.TSyntax `term →
      Lean.MacroM (Lean.TSyntax `term)) :
    Lean.MacroM (Lean.TSyntax `term) := do
  let mut result ← `([zf|$body])
  for binder in binders.reverse do
    let `(zfBinder| ($xs:ident* : $a:zfTerm)) := binder
      | Lean.Macro.throwUnsupported
    for x in xs.reverse do result ← wrap a x result
  pure result

macro_rules
  | `([zf|$x:ident]) => `($x)
  | `([zf|∅]) => `(∅)
  | `([zf|$($e:term)]) => `($e)
  | `([zf|($e:zfTerm)]) => `([zf|$e])
  | `([zf|($x:zfTerm, $y:zfTerm)]) => `(ZFSet.pair [zf|$x] [zf|$y])
  | `([zf|![$xs,*]]) => do
      let xs ← xs.getElems.mapM fun x => `([zf|$x])
      `((![$xs,*] : Fin _ → ZFSet))
  | `([zf|$f:zfTerm $args:zfTerm...]) => `(ZFSet.Aczel.apps [zf|$f] [zf|$args])
  | `([zf|$f:zfTerm $x:zfTerm]) => `(ZFSet.Aczel.app [zf|$f] [zf|$x])
  | `([zf|fun $xs:ident* : $a:zfTerm => $body:zfTerm]) => do
      let mut result ← `([zf|$body])
      for x in xs.reverse do
        result ← `(ZFSet.Aczel.lam [zf|$a] fun $x => $result)
      pure result
  | `([zf|fun $_:hole : $a:zfTerm => $body:zfTerm]) =>
      `(ZFSet.Aczel.lam [zf|$a] fun _ => [zf|$body])
  | `([zf|fun $binders:zfBinder* => $body:zfTerm]) => do
      expandBinders binders body fun a x result =>
        `(ZFSet.Aczel.lam [zf|$a] fun $x => $result)
  | `([zf|$binder:zfBinder → $body:zfTerm]) => do
      expandBinders #[binder] body fun a x result =>
        `(ZFSet.Aczel.pi [zf|$a] fun $x => $result)
  | `([zf|$a:zfTerm → $b:zfTerm]) =>
      `(ZFSet.Aczel.pi [zf|$a] fun _ => [zf|$b])
  | `([zf|$p:zfTerm]) => do
      unless p.raw.getKind == ``zfProj || p.raw.getKind == ``zfIdentProj do
        Lean.Macro.throwUnsupported
      let args := p.raw.getArgs
      let base : Lean.TSyntax `zfTerm := ⟨args[0]!⟩
      let result ← if p.raw.getKind == ``zfIdentProj then
          let base : Lean.Ident := ⟨args[0]!⟩
          `($base)
        else `([zf|$base])
      match args[2]!.isNatLit? with
      | some 1 => `(ZFSet.fst $result)
      | some 2 => `(ZFSet.snd $result)
      | _ => Lean.Macro.throwError "ZF projections are .1 or .2"
