module

import Tapas

open Tapas.LogicalRelation Tapas.Parametricity

namespace TapasTest.Parametricity.TypeRelation

universe u v w

-- A parametricity theorem can be used at its complete type relation without
-- introducing or rearranging any arguments, even across different universes.
abbrev Transformation := {A : Type u} → (A → A) → A → Nat → A
derive_type_rel Transformation (repr := A)

def once {A : Type u} (f : A → A) (x : A) (_n : Nat) : A := f x
derive_parametric once (repr := A)

example : Transformation.Rel (@once.{u}) (@once.{v}) := once.parametric

-- A named representation may be bound by the return type rather than the written signature.
def aliasedOnce : Transformation.{u} := @once

/-- error: parametricity: _private.TapasTest.Parametricity.TypeRelation.0.TapasTest.Parametricity.TypeRelation.aliasedOnce has no implicit parameter; use `(repr := name)` to select a representation -/
#guard_msgs in
derive_parametric aliasedOnce

/-- error: parametricity: _private.TapasTest.Parametricity.TypeRelation.0.TapasTest.Parametricity.TypeRelation.aliasedOnce has no parameter at index 0; there are 0 -/
#guard_msgs in
derive_parametric aliasedOnce (repr := 0)

derive_parametric aliasedOnce (repr := A)

example : Transformation.Rel (@aliasedOnce.{u}) (@aliasedOnce.{v}) := aliasedOnce.parametric

-- Finding the outer A must not count the same-named binder hidden in the result alias.
abbrev Identity := {A : Type} → A → A

def keep {A : Type} (_x : A) : Identity := fun {_} y => y

derive_parametric keep (repr := A)
derive_parametric keep as keepDefault
derive_parametric keep as keepPositional (repr := 0)

example : @keep.parametric = @keepDefault := rfl
example : @keep.parametric = @keepPositional := rfl

-- Ordinary inputs stay shared while the monad inside the result alias is related.
abbrev FinalAction (α : Type u) := {m : Type u → Type v} → [Monad m] → m α
derive_type_rel FinalAction (repr := m)

def finalPure {α : Type u} (a : α) : FinalAction.{u, v} α := fun {_} _ => pure a
derive_parametric finalPure (repr := m)

example {α : Type u} (a : α) :
    FinalAction.Rel (finalPure.{u, v} a) (finalPure.{u, w} a) := finalPure.parametric a

-- Functional induction changes how the theorem is proved, not its statement.
infer_final (A : Type u)
def iterate (f : A → A) (x : A) : Nat → A
  | 0 => x
  | n + 1 => iterate f (f x) n
derive_parametric iterate (repr := A)

example : Transformation.Rel (@iterate.{u}) (@iterate.{v}) := iterate.parametric

-- Dictionary premises and a shared type parameter occupy their signature positions.
set_option linter.checkUnivs false in
abbrev Action := {m : Type u → Type v} → [Monad m] → {α : Type u} →
  m α → (α → m α) → Nat → m α
derive_type_rel Action (repr := m)

def bindOnce {m : Type u → Type v} [Monad m] {α : Type u}
    (x : m α) (f : α → m α) (_n : Nat) : m α := x >>= f
derive_parametric bindOnce (repr := m)

example : Action.Rel (@bindOnce.{u, v}) (@bindOnce.{u, w}) := bindOnce.parametric

-- Shared arguments before the representation stay before the relation's binders.
abbrev Later := Nat → {A : Type u} → A → A
derive_type_rel Later (repr := A)

def later (_n : Nat) {A : Type u} (x : A) : A := x
derive_parametric later (repr := A)

example : Later.Rel (@later.{u}) (@later.{v}) := later.parametric

-- A type alias's own parameter and its universe are shared by both interpretations.
set_option linter.checkUnivs false in
abbrev WithInput (X : Type u) := {A : Type v} → (X → A) → X → A
derive_type_rel WithInput (repr := A)

def applyInput {X : Type u} {A : Type v} (f : X → A) (x : X) : A := f x
derive_parametric applyInput (repr := A)

example {X : Type u} :
    WithInput.Rel (@applyInput.{u, v} X) (@applyInput.{u, w} X) := applyInput.parametric

-- Markers are read by the same core and do not change the endpoints' written types.
abbrev Marked := {A : relMarker (Type u)} → A → A
derive_type_rel Marked

def marked {A : relMarker (Type u)} (x : A) : A := x
derive_parametric marked

example : Marked.Rel (@marked.{u}) (@marked.{v}) := marked.parametric

end TapasTest.Parametricity.TypeRelation
