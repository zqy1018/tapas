module

public import Tapas.Applications.Monad.CommonMonadRelations
public import Tapas.Parametricity.Fixpoint
import Tapas.Parametricity.Program

public section

/-!
Opt-in least-fixpoint semantics for Lean's `while` and `repeat` syntax.

Those expand to `ForIn` over `Lean.Loop`, and the standard instance has no
translation `derive_parametric` can use: `Lean.Loop.forIn` is `whileM`, whose value is
a fixed point chosen classically rather than by a recursion the walk can follow. This
module supplies a `loop` defined by `partial_fixpoint` instead, derives its
translation, and offers it as a scoped `ForIn` instance at higher priority. The cost
is the order structure a least fixpoint needs, `[∀ α, CCPO (m α)]` and `[MonoBind m]`.

Being `scoped`, the instance changes nothing on import. Open
`Tapas.Parametricity.PartialLoop` to select it, or elaborate one term with
`infer_effects_partial%`, which introduces it locally instead.

`Parametricity.Program` is where `derive_parametric` lives, and
`CommonMonadRelations` is there because that command needs `Monad.Rel` registered
before it can translate a monadic program: the generic layer derives no monadic
relation on its clients' behalf. `Parametricity.Fixpoint` exports the admissibility
condition of the generated certificates.
-/

namespace Tapas.Parametricity.PartialLoop

open Lean.Order

/-- Iterate a loop body to its least fixpoint, continuing on `yield` and stopping
on `done`. The accumulator also carries the elaborator's mutable locals and returns. -/
@[expose] def loop {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    {β : Type u} (body : Unit → β → m (ForInStep β)) (init : β) : m β := do
  match ← body () init with
  | .done result => pure result
  | .yield next => loop body next
partial_fixpoint

derive_parametric loop

/-- The `ForIn` entry point used by the optional loop instance. -/
@[expose] def forIn {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    {β : Type u} (_ : Lean.Loop) (init : β) (body : Unit → β → m (ForInStep β)) : m β :=
  loop body init

derive_parametric forIn

scoped instance (priority := high) instForIn {m : Type u → Type v}
    [Monad m] [∀ α, CCPO (m α)] [MonoBind m] : ForIn m Lean.Loop Unit where
  forIn := forIn

end Tapas.Parametricity.PartialLoop
