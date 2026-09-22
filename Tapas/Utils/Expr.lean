module

public meta import Lean
import Lean.Expr

public meta section

namespace Tapas.Utils

open Lean Meta

/-- Remove the `let`/`have` binders at the head of `e`. -/
partial def zetaHead (e : Expr) : Expr :=
  match e with
  | .letE _ _ value body _ => zetaHead (body.instantiate1 value)
  | .mdata _ e => zetaHead e
  | e => e

/-- `ite` or `dite`, possibly applied to further arguments when a branch selects a function. -/
def iteHead? (e : Expr) : Option Name :=
  -- NOTE: Also handling cases like `(if c then e1 else e2) a b ...` here,
  -- so only fails when there are fewer than five arguments.
  if e.getAppNumArgs < 5 then none
  else if e.isAppOf ``ite then some ``ite
  else if e.isAppOf ``dite then some ``dite
  else none

-- CHECK Is this really necessary?
/-- Let variables among match discriminants, following chains of let variables. `split`
cannot generalize a let variable, so their values are exposed before splitting. -/
def letDiscriminants (discrs : Array Expr) : MetaM (Array FVarId) := do
  let mut lets := #[]
  for discr in discrs do
    let mut current := discr.consumeMData
    repeat
      let .fvar fvarId := current | break
      let some value ← fvarId.getValue? | break
      lets := lets.push fvarId
      current := value.consumeMData
  return lets

section Recognizers

/-- Recognize `Type u → Type v`, unfolding an outer alias if necessary. This is the
one definition of "monadic kind": the entry points that predate explicit
representation selection use it to guess which parameter is the representation.
Unlike `Meta.isMonad?`, it checks the type without requiring a `Monad` instance. -/
def typeConstructorUniverses? (type : Expr) : MetaM (Option (Level × Level)) := do
  let type := type.cleanupAnnotations
  let type ← if type.isForall then pure type else whnf type
  let .forallE _ (.sort (.succ u)) (.sort (.succ v)) _ := type | return none
  return some (u, v)

end Recognizers

end Tapas.Utils
