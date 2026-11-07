module

import TapasTest.TestingUtils

/-!
Named loop hypotheses with inferred capabilities and mutable local variables.
-/

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order

namespace TapasTest.Applications.Monad.ControlFlow.Loops

-- Standard loops keep their usual semantics and require no order instances.
def namedWhile (limit : Nat) := infer_effects% do
  let mut n := 0
  while _h : n < limit do
    set n
    n := n + 1
  pure n

example : Nat → {m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → m Nat := @namedWhile

#guard (namedWhile (m := StateM Nat) 0 9).run == (0, 9)
#guard (namedWhile (m := StateM Nat) 3 9).run == (3, 2)
#guard_uses namedWhile ⊇ [Lean.instForInLoopUnitOfMonad]
#guard_uses type namedWhile ∩ [CCPO, MonoBind] = ∅

-- The partial frontend supports deriving the loop, including proof-dependent indexing.
def namedIndexWhile (xs : Array Nat) := infer_effects_partial% do
  let mut i := 0
  while h : i < xs.size do
    set xs[i]
    i := i + 1
  pure i
derive_parametric namedIndexWhile

example : Array Nat → {m : Type → Type} → [Monad m] →
    [∀ α, CCPO (m α)] → [MonoBind m] → [MonadStateOf Nat m] → m Nat := @namedIndexWhile

#guard namedIndexWhile (m := StateT Nat Option) #[] 9 == some (0, 9)
#guard namedIndexWhile (m := StateT Nat Option) #[2, 7] 9 == some (2, 7)

-- Both loop hypotheses are used, with a local `let` between the two loops.
infer_effects_partial
def nestedNamedWhile (limit : Nat) : m Nat := do
  let mut i := 0
  let mut count := 0
  while hi : i < limit do
    let row := Fin.mk i hi
    let mut j := 0
    while hj : j < i do
      let col := Fin.mk j hj
      set (row.val + col.val)
      count := count + 1
      j := j + 1
    i := i + 1
  pure count
derive_parametric nestedNamedWhile

example : {m : Type → Type} → [Monad m] → [∀ α, CCPO (m α)] → [MonoBind m] →
    [MonadStateOf Nat m] → Nat → m Nat := @nestedNamedWhile

#guard nestedNamedWhile (m := StateT Nat Option) 0 9 == some (0, 9)
#guard nestedNamedWhile (m := StateT Nat Option) 3 9 == some (3, 3)
#guard_uses namedIndexWhile, nestedNamedWhile ⊇ [PartialLoop.instForIn]
#guard_uses namedIndexWhile.parametric, nestedNamedWhile.parametric ⊇
  [PartialLoop.forIn.parametric]

-- Named `for` hypotheses justify indexing while the body also updates a local accumulator.
def namedFor (xs : Array Nat) := infer_effects% do
  let mut total := 0
  for h : i in [0:xs.size] do
    let n := xs[i]
    set n
    total := total + n
  pure total
derive_parametric namedFor

example : Array Nat → {m : Type → Type} → [Monad m] → [MonadStateOf Nat m] → m Nat := @namedFor

#guard (namedFor (m := StateM Nat) #[] 9).run == (0, 9)
#guard (namedFor (m := StateM Nat) #[2, 7] 9).run == (9, 7)

#guard_parametric namedIndexWhile, nestedNamedWhile, namedFor

end TapasTest.Applications.Monad.ControlFlow.Loops
