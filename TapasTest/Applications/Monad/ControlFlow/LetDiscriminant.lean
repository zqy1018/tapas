import Tapas

/-!
A `match` whose discriminant is a do-notation `let` variable.

The elaborator introduces such a value as a let-bound free variable, and Lean's `split`
cannot split on one. The `example` below pins that down: `split` fails on the let
variable and succeeds once the discriminant is unfolded. Unfolding it is exactly what
`derive_parametric` does, so the derivation at the end of the file goes through.
-/

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.ControlFlow.LetDiscriminant

def m5 := infer_effects% do
  let n ← get
  let k := n % 3
  match k with
  | 0 => pure 0
  | _ => pure 1

/-- The same goal shape, proved by hand: `split` needs the discriminant unfolded first. -/
example {m : Type → Type} {m' : Type → Type} [Monad m] [Monad m'] (R : ComputationRelation m m')
    (hp : ∀ {α} (a : α), R (pure a) (pure a)) (n : Nat) :
    let k := n % 3
    R (match k with | 0 => pure 0 | _ => pure 1)
      (match k with | 0 => pure 0 | _ => pure 1) := by
  intro k
  fail_if_success split
  show R (match n % 3 with | 0 => pure 0 | _ => pure 1)
    (match n % 3 with | 0 => pure 0 | _ => pure 1)
  split <;> exact hp _

derive_parametric m5

example {m m' : Type → Type} [Monad m] [MonadStateOf Nat m]
    [Monad m'] [MonadStateOf Nat m'] (R : ComputationRelation m m')
    (hm : Monad.Rel R) (hs : MonadStateOf.Rel (σ := Nat) R) : R m5 m5 :=
  m5.parametric R hm hs

end TapasTest.Applications.Monad.ControlFlow.LetDiscriminant
