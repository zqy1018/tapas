import Tapas

open Lean Meta Tapas.LogicalRelation

/-!
The backend takes a rule saying which binders are representations, and `(repr := ...)`
is how one is written down. These tests cover explicit rules and the command defaults.

The case that matters is a representation bound *inside* an argument's type. It used
to be reached only by guessing at monadic kinds, which is why a carrier DSL got a
weaker relation than its monadic twin. Naming that binder alongside the outer one
reaches it, and a marker reaches it without mentioning names at all, identifying the
binder by position so that it cannot select the wrong one. Giving an outermost
binder's position marks it in the same way, without editing the declaration.
-/

namespace TapasTest.LogicalRelation.Selection

universe u v w x

inductive Ty where
  | nat

class Lang (repr : Ty → Type) where
  lit : Nat → repr .nat

derive_interface_rel Lang (repr := repr)

/-! ## An operation the selection does not reach -/

-- A field mentioning no representation is not dropped: the two dictionaries have to
-- agree on it, so the condition is an equation rather than a relation.
class Sized (A : Type u) where
  lit : Nat → A
  size : Nat

derive_interface_rel Sized (repr := A)

example {A : Type u} {A' : Type v} (R : A → A' → Prop)
    (left : Sized A) (right : Sized A') (h : Sized.Rel (left := left) (right := right) R) :
    Sized.size (self := left) = Sized.size (self := right) := h.size

/-! ## Reaching the same binders from a command -/

class Carrier (A : Type u) where
  lit : Nat → A

derive_interface_rel Carrier (repr := A)

/-- An operation taking a program polymorphic in its own representation. -/
class Named (A : Type u) where
  run : ({B : Type u} → [Carrier B] → B) → A

/-- The same operation, with the binder marked instead of named. -/
class Marked (A : Type u) where
  run : ({B : relMarker (Type u)} → [Carrier B] → B) → A

-- Naming the inner binder as well as the carrier relates the program: each side
-- receives its own, related by whatever a related carrier gives.
derive_interface_rel Named (repr := A, B)

-- The marker says the same thing without naming anything, and the program's two
-- interpretations are still introduced at the type it wraps.
derive_interface_rel Marked (repr := A)

example {A : Type u} {A' : Type v} (R : A → A' → Prop) (left : Named A) (right : Named A')
    (h : Named.Rel (left := left) (right := right) R)
    (p : {B : Type u} → [Carrier B] → B) (q : {B : Type v} → [Carrier B] → B)
    (hpq : ∀ {B : Type u} {B' : Type v} (S : B → B' → Prop) [Carrier B] [Carrier B'],
      Carrier.Rel S → S (p (B := B)) (q (B := B'))) :
    R (left.run p) (right.run q) := h.run p q hpq

example {A : Type u} {A' : Type v} (R : A → A' → Prop) (left : Marked A) (right : Marked A')
    (h : Marked.Rel (left := left) (right := right) R)
    (p : {B : Type u} → [Carrier B] → B) (q : {B : Type v} → [Carrier B] → B)
    (hpq : ∀ {B : Type u} {B' : Type v} (S : B → B' → Prop) [Carrier B] [Carrier B'],
      Carrier.Rel S → S (p (B := B)) (q (B := B'))) :
    R (left.run p) (right.run q) := h.run p q hpq

class Pair (A : Type u) (B : Type u) where
  lit : Nat → A

/--
error: logical relation: expected exactly one representation parameter of TapasTest.LogicalRelation.Selection.Pair, selected:
  [A, B]
-/
#guard_msgs in
derive_interface_rel Pair (repr := A, B)

/-! ## The same choice in a type relation -/

-- The program's universe is independent of the carrier's, since sharing the program
-- requires both interpretations to read it at the same universe.
set_option linter.checkUnivs false in
abbrev Shared := {A : Type u} → [Carrier A] → ({B : Type v} → [Carrier B] → B) → A
set_option linter.checkUnivs false in
abbrev Related := {A : Type u} → [Carrier A] → ({B : Type v} → [Carrier B] → B) → A

-- Selecting only the outer binder shares the program, which is a weaker statement
-- and a choice rather than the only reading available.
derive_type_rel Shared (repr := A)

example (p : Shared.{u, v}) (q : Shared.{w, v}) :
    Shared.Rel p q ↔
      ∀ {A : Type u} {A' : Type w} (R : A → A' → Prop) [Carrier A] [Carrier A'],
        Carrier.Rel R → ∀ (f : {B : Type v} → [Carrier B] → B), R (p f) (q f) := Iff.rfl

derive_type_rel Related (repr := A, B)

example (p : Related.{u, v}) (q : Related.{w, x}) :
    Related.Rel p q ↔
      ∀ {A : Type u} {A' : Type w} (R : A → A' → Prop) [Carrier A] [Carrier A'],
        Carrier.Rel R →
          ∀ (f : {B : Type v} → [Carrier B] → B) (g : {B : Type x} → [Carrier B] → B),
            (∀ {B : Type v} {B' : Type x} (S : B → B' → Prop) [Carrier B] [Carrier B'],
              Carrier.Rel S → S (f (B := B)) (g (B := B'))) →
            R (p f) (q g) := Iff.rfl

/-! ## Selecting an outermost binder by position -/

-- Both `A`s carry the same name, so a name reaches both and the program argument is
-- related. A position reaches only the binder meant, and the program stays shared.
abbrev ByName := ({A : Type} → A → A) → {A : Type u} → [Carrier A] → A
abbrev ByPosition := ({A : Type} → A → A) → {A : Type u} → [Carrier A] → A

derive_type_rel ByName (repr := A)

example (p : ByName.{u}) (q : ByName.{v}) :
    ByName.Rel p q ↔
      ∀ (f g : {A : Type} → A → A),
        (∀ {A A' : Type} (R : A → A' → Prop) (x : A) (y : A'), R x y → R (f x) (g y)) →
        ∀ {A : Type u} {A' : Type v} (R : A → A' → Prop) [Carrier A] [Carrier A'],
          Carrier.Rel R → R (p f) (q g) := Iff.rfl

-- The binders the type binds are the program, `A`, and the `Carrier` instance.
derive_type_rel ByPosition (repr := 1)

example (p : ByPosition.{u}) (q : ByPosition.{v}) :
    ByPosition.Rel p q ↔
      ∀ (f : {A : Type} → A → A) {A : Type u} {A' : Type v} (R : A → A' → Prop)
        [Carrier A] [Carrier A'], Carrier.Rel R → R (p f) (q f) := Iff.rfl

-- A position reads an interface's own parameters, and is spent on choosing one: the
-- generated class is declared over the parameters as the interface has them.
class Positional (A : Type u) where
  lit : Nat → A

derive_interface_rel Positional (repr := 0)

example {A : Type u} {A' : Type v} (R : A → A' → Prop)
    (left : Positional A) (right : Positional A') (h : Positional.Rel (left := left) (right := right) R) (n : Nat) :
    R (left.lit n) (right.lit n) := h.lit n

-- `derive_parametric` takes the same spec. A program's representation is one of its
-- own parameters, so a position there names that parameter rather than marking it.
def positional {A : Type u} [Carrier A] : A := Carrier.lit 1
def outOfRange {A : Type u} [Carrier A] : A := Carrier.lit 1

derive_parametric positional (repr := 0)

example {A : Type u} {A' : Type v} (R : A → A' → Prop) [la : Carrier A] [ra : Carrier A']
    (h : Carrier.Rel R) : R (positional (A := A)) (positional (A := A')) :=
  positional.parametric R h

-- Omitting the spec selects the first implicit parameter,
-- even when another parameter heads the result type.
def firstBeforeResult {A : Type u} {B : Type v} (_x : A) (y : B) : B := y

derive_parametric firstBeforeResult
derive_parametric firstBeforeResult as firstBeforeResultExplicit (repr := 0)

example {A : Type u} {A' : Type w} {B : Type v} (R : A → A' → Prop)
    (a : A) (a' : A') (ha : R a a') (b : B) :
    firstBeforeResult a b = firstBeforeResult a' b :=
  firstBeforeResult.parametric R a a' ha b

example : @firstBeforeResult.parametric = @firstBeforeResultExplicit := rfl

-- A container result needs no explicit spec when its representation is the first implicit parameter.
def firstContainer {A : Type u} [Carrier A] : Option A := some (Carrier.lit 1)

derive_parametric firstContainer

example {A : Type u} {A' : Type v} (R : A → A' → Prop) [la : Carrier A] [ra : Carrier A']
    (h : Carrier.Rel R) :
    Option.Rel R (firstContainer (A := A)) (firstContainer (A := A')) :=
  firstContainer.parametric R h

-- Explicit and instance parameters are skipped; strict implicit parameters are eligible.
def laterRepresentation (n : Nat) [Nonempty Nat] ⦃A : Type u⦄ [Carrier A] : A := Carrier.lit n

derive_parametric laterRepresentation
derive_parametric laterRepresentation as laterRepresentationExplicit (repr := 2)

example : @laterRepresentation.parametric = @laterRepresentationExplicit := rfl

example {A : Type u} {A' : Type v} (R : A → A' → Prop) [la : Carrier A] [ra : Carrier A']
    (h : Carrier.Rel R) (n : Nat) :
    R (laterRepresentation (A := A) n) (laterRepresentation (A := A') n) :=
  laterRepresentation.parametric n R h

-- Each member of a recursive block selects its own first implicit parameter.
mutual
def leftFirst (n : Nat) {A : Type u} [Carrier A] : A :=
  match n with
  | 0 => Carrier.lit 0
  | k + 1 => rightFirst k
def rightFirst {A : Type u} [Carrier A] (n : Nat) : A :=
  match n with
  | 0 => Carrier.lit 1
  | k + 1 => leftFirst k
end

derive_parametric leftFirst

example {A : Type u} {A' : Type v} (R : A → A' → Prop) [la : Carrier A] [ra : Carrier A']
    (h : Carrier.Rel R) (n : Nat) :
    R (rightFirst (A := A) n) (rightFirst (A := A') n) :=
  rightFirst.parametric R h n

-- An unsuitable first implicit parameter is an error; selection does not try a later one.
def unsuitableImplicit {n : Nat} {A : Type u} [Carrier A] : A := Carrier.lit n

/-- error: logical relation: shared-index interpretation requires a parameter whose telescope ends in a sort -/
#guard_msgs in
derive_parametric unsuitableImplicit

derive_parametric unsuitableImplicit (repr := A)

-- An explicit representation still works when selected explicitly; instances do not count.
def explicitRepresentation (A : Type u) [Carrier A] : A := Carrier.lit 1

/-- error: parametricity: TapasTest.LogicalRelation.Selection.explicitRepresentation has no implicit parameter; use `(repr := name)` to select a representation -/
#guard_msgs in
derive_parametric explicitRepresentation

derive_parametric explicitRepresentation (repr := 0)

def noParameters : Nat := 0

/-- error: parametricity: TapasTest.LogicalRelation.Selection.noParameters has no implicit parameter; use `(repr := name)` to select a representation -/
#guard_msgs in
derive_parametric noParameters

/--
error: parametricity: TapasTest.LogicalRelation.Selection.outOfRange has no parameter at index 9; there are 2
-/
#guard_msgs in
derive_parametric outOfRange (repr := 9)

abbrev TooFew := {A : Type u} → [Carrier A] → A

/-- error: logical relation: no outermost binder at index 9; there are 2 -/
#guard_msgs in
derive_type_rel TooFew (repr := 9)

end TapasTest.LogicalRelation.Selection
