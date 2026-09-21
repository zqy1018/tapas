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
