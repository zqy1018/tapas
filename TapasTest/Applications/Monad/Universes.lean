module

import Tapas

namespace TapasTest.Applications.Monad.Universes

universe u v w

/- The value and computation universes are independently polymorphic. -/
def pureValue {α : Type u} (x : α) :=
  infer_effects% do
    pure x

example {α : Type u} (x : α) :
    ({m : Type u → Type v} → [Monad m] → m α) :=
  @pureValue α x

/- Built-in capabilities retain their universe-polymorphic parameters. -/
def stateRoundTrip {σ : Type u} :=
  infer_effects% do
    let before ← getThe σ
    set before
    pure before

example {σ : Type u} :
    ({m : Type u → Type v} → [Monad m] →
      [MonadStateOf σ m] → m σ) :=
  @stateRoundTrip σ

/- Exception and result types may live in unrelated universes. -/
def recoverOrThrow {ε : Type u} {α : Type v}
    (error : ε) (fallback : α) (fail : Bool) :=
  infer_effects% do
    if fail then
      throwThe ε error
    else
      pure fallback

example {ε : Type u} {α : Type v} (error : ε) (fallback : α) (fail : Bool) :
    ({m : Type v → Type w} → [Monad m] →
      [MonadExceptOf ε m] → m α) :=
  @recoverOrThrow ε α error fallback fail

/- Universe polymorphism is preserved through calls to inferred programs. -/
def stateThreeTimes {σ : Type u} :=
  infer_effects% do
    let first ← stateRoundTrip (σ := σ)
    let second ← stateRoundTrip (σ := σ)
    let third ← getThe σ
    set first
    set second
    set third
    pure (first, second, third)

example {σ : Type u} :
    ({m : Type u → Type v} → [Monad m] →
      [MonadStateOf σ m] → m (σ × σ × σ)) :=
  @stateThreeTimes σ

/- Custom capabilities are not restricted to universe zero either. -/
class MonadEmit (ω : Type u) (m : Type u → Type v) where
  emit : ω → m PUnit

def emit [MonadEmit ω m] (message : ω) : m PUnit :=
  MonadEmit.emit message

def emitAndReturn {ω : Type u} (message : ω) :=
  infer_effects% do
    emit message
    pure message

example {ω : Type u} (message : ω) :
    ({m : Type u → Type v} → [Monad m] →
      [MonadEmit ω m] → m ω) :=
  @emitAndReturn ω message

/- A type itself is a value above `Type 0`, ruling out the old implementation. -/
def readType :=
  infer_effects% do
    let before ← getThe Type
    set before
    pure before

example :
    ({m : Type 1 → Type v} → [Monad m] →
      [MonadStateOf Type m] → m Type) :=
  @readType

end TapasTest.Applications.Monad.Universes
