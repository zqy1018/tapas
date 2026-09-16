import Tapas.Parametricity.Program

/-!
Opt-in least-fixpoint semantics for Lean's `while` and `repeat` syntax.
Open the `Tapas.Parametricity.PartialLoop` scope before elaborating a program
with explicit CCPO and MonoBind parameters. Importing this module alone does not
change the selected loop instance.
-/

namespace Tapas.Parametricity.PartialLoop

open Lean.Order

/-- Iterate a loop body to its least fixpoint, continuing on `yield` and stopping
on `done`. The accumulator also carries the elaborator's mutable locals and returns. -/
def loop {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    {β : Type u} (body : Unit → β → m (ForInStep β)) (init : β) : m β := do
  match ← body () init with
  | .done result => pure result
  | .yield next => loop body next
partial_fixpoint

derive_parametric loop

/-- The `ForIn` entry point used by the optional loop instance. -/
def forIn {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    {β : Type u} (_ : Lean.Loop) (init : β) (body : Unit → β → m (ForInStep β)) : m β :=
  loop body init

derive_parametric forIn

scoped instance (priority := high) instForIn {m : Type u → Type v}
    [Monad m] [∀ α, CCPO (m α)] [MonoBind m] : ForIn m Lean.Loop Unit where
  forIn := forIn

end Tapas.Parametricity.PartialLoop
