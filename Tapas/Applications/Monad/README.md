# Application: Monad

This directory contains commands and definitions that are built upon the core library but specialized for monadic programs.

## Using it

```lean
import Tapas
open Tapas.LogicalRelation

class Emit (m : Type → Type v) where
  emit : String → m Unit

derive_effect_rel Emit          -- Emit.Rel, with the monad parameter guessed

def greet := infer_effects% do   -- {m} → [Monad m] → [Emit m] → m Unit
  Emit.emit "hello"

derive_parametric greet          -- defaults to the first implicit parameter, here `m`
-- greet.parametric : ∀ {m} [Monad m] [Emit m] {m'} (R) [Monad m'],
--   Monad.Rel R .. → ∀ [Emit m'], Emit.Rel R .. → R greet greet
```

`Monad.Rel` and the relations of some common Lean's capability classes are generated already, so a
body using `do`, `get`, `throw`, a lift or a `for` loop over a list or a range needs nothing
further. Write
`infer_effects_partial%` instead when the body loops and the result is to be derived.

A recursive program is not one term, so it uses the command form instead:

```lean
infer_effects
def countDown : Nat → m Nat        -- {m} → [Monad m] → [MonadStateOf Nat m] → Nat → m Nat
  | 0 => get
  | k + 1 => do set k; countDown k

derive_parametric countDown
```

`infer_effects def ...` accepts whatever `def` accepts: `termination_by`, `decreasing_by`,
`partial`, `where`, `let rec`, and a `mutual` block, whose functions then share one set of
capability parameters. `infer_effects_partial` is its counterpart for a looping body or a
`partial_fixpoint`.

The default selects the first implicit parameter (`{...}` or `⦃...⦄`) of the elaborated
declaration, skipping explicit and instance parameters. If another implicit parameter
precedes `m`, use `derive_parametric p (repr := m)`.

## Modules

| Module | Contents |
| --- | --- |
| [EffectRelation.lean](EffectRelation.lean) | `derive_effect_rel`: `derive_interface_rel` with the monad parameter guessed |
| [CommonMonadRelations.lean](CommonMonadRelations.lean) | the relations of `Monad` and Lean's capability classes, and `Monad.Rel.ofPureBind` |
| [EffectInference.lean](EffectInference.lean) | `infer_effects%` and `infer_effects`: abstract the monad and the capabilities a body leaves unresolved, for one term or for a declaration |
| [Loop.lean](Loop.lean) | a `while` loop that admits a relation, offered as a scoped `ForIn` instance |
| [StdLoops.lean](StdLoops.lean) | translations for `for x in xs` and `for i in [0:n]` |
| [PartialEffectInference.lean](PartialEffectInference.lean) | `infer_effects_partial%` and `infer_effects_partial`: the same two frontends with that loop selected |
