import Metalean.FastChecker.Loader
import Metalean.Export.Driver

open Metalean FastChecker
open Lean (Name)

structure Scan where
  pos : Nat := 0
  found : Std.HashMap Name Nat := ∅

def Scan.wanted : Std.HashSet Name :=
  {
    ``Nat,
    ``List,
    ``Char,
    ``Char.ofNat,
    ``String.ofList,
    ``Bool,
    ``Nat.pred,
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.pow,
    ``Nat.beq,
    ``Nat.ble,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.gcd,
    ``Nat.land,
    ``Nat.lor,
    ``Nat.xor,
    ``Nat.shiftLeft,
    ``Nat.shiftRight
    }

def Scan.step (sc : Scan) (names : List Name) : Scan := Id.run do
  have ⟨pos, found⟩ := sc
  let mut table := found
  for name in names do
    if name ∈ Scan.wanted && name ∉ table then
      table := table.insert name pos
  return ⟨pos + 1, table⟩

def Scan.at? (name : Name) (sc : Scan) : Nat :=
  sc.found.getD name sc.pos

def Scan.literals (sc : Scan) : Literals where
  nat := sc.at? ``Nat
  list := sc.at? ``List
  char := sc.at? ``Char
  charOfNat := sc.at? ``Char.ofNat
  stringOfList := sc.at? ``String.ofList
  bool := sc.at? ``Bool
  pred := sc.at? ``Nat.pred
  add := sc.at? ``Nat.add
  sub := sc.at? ``Nat.sub
  mul := sc.at? ``Nat.mul
  pow := sc.at? ``Nat.pow
  beq := sc.at? ``Nat.beq
  ble := sc.at? ``Nat.ble
  div := sc.at? ``Nat.div
  mod := sc.at? ``Nat.mod
  gcd := sc.at? ``Nat.gcd
  land := sc.at? ``Nat.land
  lor := sc.at? ``Nat.lor
  xor := sc.at? ``Nat.xor
  shiftLeft := sc.at? ``Nat.shiftLeft
  shiftRight := sc.at? ``Nat.shiftRight

def main (args : List String) : IO UInt32 := do
  let some h ← Export.open? args | return 3
  let some (sc, lastUse) ← Export.scan h ({} : Scan) Scan.step
    | return (Frontend.Failure.reject .parse).exitCode
  Export.run args lastUse (FState.initial sc.literals) step
