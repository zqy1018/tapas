module

public import Lean
public import Std.WP

public section

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Control

/-!
Scoped `grind` normalization rules for applications of `if` and dependent `if`.
The `FunctionApplication` scope supplies general function application rules. The `PredTrans`
scope adds the standard library's predicate-transformer projection rules. Neither scope is
enabled by importing this module. `match` expressions are handled by `grind` itself.
-/

/-- Move a function argument inside an `if` expression. -/
theorem ite_apply {α β : Sort _} (c : Prop) [Decidable c] (t e : α → β) (x : α) :
    (if c then t else e) x = if c then t x else e x := by
  exact apply_ite (fun f => f x) c t e

/-- Move a function argument inside a dependent `if` expression. -/
theorem dite_apply {α β : Sort _} (c : Prop) [Decidable c]
    (t : c → α → β) (e : ¬c → α → β) (x : α) :
    (dite c t e) x = dite c (fun h => t h x) (fun h => e h x) := by
  exact apply_dite (fun f => f x) c t e

namespace FunctionApplication

attribute [scoped grind norm] ite_apply dite_apply

end FunctionApplication

namespace PredTrans

attribute [scoped grind norm] Lean.Order.PredTrans.apply_ite Lean.Order.PredTrans.apply_dite

end PredTrans

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Control
