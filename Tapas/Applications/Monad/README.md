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
body using `read`, `get`, `throw`, a lift or a `for` loop over a list or a range needs nothing
further. For `while` and `repeat`, see [Choosing loop semantics](#choosing-loop-semantics).

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

## Choosing loop semantics

Both `infer_effects` and `infer_effects_partial` accept `while` and `repeat`; neither proves
termination. They select different loop implementations during elaboration. The same distinction
applies to the term forms `infer_effects%` and `infer_effects_partial%`.

| | `infer_effects` | `infer_effects_partial` |
| --- | --- | --- |
| Loop semantics | Lean's standard loop (`repeatM`) | Least fixpoint via `partial_fixpoint` |
| Extra requirements from the loop | None beyond `Monad m` | `[∀ α, Lean.Order.CCPO (m α)]` and `[Lean.Order.MonoBind m]` |
| `derive_parametric` | Rejected | Supported with an `AdmissibleRel` premise |

The standard loop is rejected because its logical definition chooses a fixed point classically
when one exists, without requiring it to be the least one. Even when the two loop bodies preserve
a relation, the fixed points chosen in the two monad interpretations need not be related. Tapas
therefore cannot derive a general parametricity theorem from the body relations alone. The partial
variant uses least-fixpoint induction, with admissibility as an additional premise.

For example, the same loop can be written with either entry point:

```lean
infer_effects
def countWhile (limit : Nat) := do
  let mut i := 0
  while i < limit do
    i := i + 1
  pure i

infer_effects_partial
def countWhilePartial (limit : Nat) := do
  let mut i := 0
  while i < limit do
    i := i + 1
  pure i

#eval countWhile 3 (m := Id)             -- 3
#eval countWhilePartial 3 (m := Option)  -- some 3
derive_parametric countWhilePartial
-- `derive_parametric countWhile` fails at `Lean.Loop.forIn`.
```

`CCPO` supplies a bottom element and suprema of chains, and `MonoBind` requires `bind` to be
monotone in both arguments. `Id` cannot supply the uniform CCPO family required by
`countWhilePartial`, so that version cannot be instantiated at `Id`.

The generated theorem also requires the relation between the two interpretations to satisfy
[`AdmissibleRel`](../../Parametricity/Fixpoint.lean): bottom values must be related, and taking
suprema of chains of related pairs must preserve the relation. This enables least-fixpoint
induction.

Both versions compile to recursive code that can diverge, including the standard loop at `Id`.
Successful execution alone establishes neither a logical equality nor parametricity. The standard
loop still permits manual proofs: for example, importing `Init.Internal.Order.While` provides
`Lean.Loop.forIn_eq_of_monadTail`, a one-step unfolding theorem whose `MonadTail` requirement is
available for `Id`. 

## Modules

| Module | Contents |
| --- | --- |
| [EffectRelation.lean](EffectRelation.lean) | `derive_effect_rel`: `derive_interface_rel` with the monad parameter guessed |
| [CommonMonadRelations.lean](CommonMonadRelations.lean) | the relations of `Monad` and Lean's capability classes, and `Monad.Rel.ofPureBind` |
| [EffectInference.lean](EffectInference.lean) | `infer_effects%` and `infer_effects`: abstract the monad and the capabilities a body leaves unresolved, for one term or for a declaration |
| [Loop.lean](Loop.lean) | a `while` loop that admits a relation, offered as a scoped `ForIn` instance |
| [StdLoops.lean](StdLoops.lean) | translations for `for x in xs` and `for i in [0:n]` |
| [PartialEffectInference.lean](PartialEffectInference.lean) | `infer_effects_partial%` and `infer_effects_partial`: the same two frontends with that loop selected |
