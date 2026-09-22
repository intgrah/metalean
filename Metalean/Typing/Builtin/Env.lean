/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Env
public import Metalean.Typing.Builtin.Choice
public import Metalean.Typing.Builtin.Eq
public import Metalean.Typing.Builtin.Iff
public import Metalean.Typing.Builtin.Nonempty
public import Metalean.Typing.Builtin.Propext
public import Metalean.Typing.Builtin.QuotSound

@[expose] public section

namespace Metalean

theorem classicalEnv_ordered : EnvWF classicalEnv :=
  .snoc
    (.snoc
      (.snoc
        (.snoc
          (.snoc
            (.snoc
              (.snoc .nil (.inductive (Eq.wf _)))
              (.quot (Eq.block_map _)))
            (.inductive (Iff.wf _)))
          (.inductive (Nonempty.wf _)))
        (.axiom Quot.Sound.isType))
      (.axiom Propext.isType))
    (.axiom Choice.isType)

end Metalean
