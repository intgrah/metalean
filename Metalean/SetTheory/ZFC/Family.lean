/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.ZFC.Basic

public section

open ZFSet

namespace Metalean

attribute [local instance 2000] Classical.allZFSetDefinable

noncomputable abbrev fn (a : ZFSet) (fn : ZFSet → ZFSet) : ZFSet := map fn a

end Metalean
