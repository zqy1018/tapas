import TapasTest.TestingUtils

open TaglessFinal Tapas.LogicalRelation Tapas.Parametricity
universe u v

namespace TapasTest.EndToEnd.Shapes

/-!
Representation shapes beyond a plain carrier: indices that depend on earlier indices, an index
of higher kind, and a type that binds two representations of its own. Each interpretation shares
every index but may end in its own universe. Containers and functions over a plain carrier are
in `Carrier.lean`, which is the file for that shape.
-/

class Grid (repr : (n : Nat) → Fin n → Type u) where
  cell {n} (i : Fin n) : repr n i

derive_interface_rel Grid (repr := repr)

def grid (n : Nat) (i : Fin n) :=
  infer_final% (repr : (n : Nat) → Fin n → Type u) => Grid.cell (repr := repr) i
example : (n : Nat) → (i : Fin n) →
    {repr : (n : Nat) → Fin n → Type u} → [Grid repr] → repr n i := @grid

derive_parametric grid (repr := repr)

-- The second index depends on the first, but both interpretations share them.
example {repr : (n : Nat) → Fin n → Type u} {repr' : (n : Nat) → Fin n → Type v}
    (R : ∀ ⦃n⦄ ⦃i : Fin n⦄, repr n i → repr' n i → Prop)
    [Grid repr] [Grid repr'] (h : Grid.Rel R) (n : Nat) (i : Fin n) :
    R (grid n i (repr := repr)) (grid n i (repr := repr')) := grid.parametric n i R h

-- A higher-kinded shared index uses the same telescope rule. It is not
-- mistaken for another representation simply because it has monadic kind.
class Higher (repr : (Type → Type) → Nat → Type u) where
  value (F : Type → Type) (n : Nat) : repr F n

derive_interface_rel Higher (repr := repr)
def higher := infer_final% (repr : (Type → Type) → Nat → Type u) =>
  Higher.value (repr := repr) Option 3

derive_parametric higher (repr := repr)

example {repr : (Type → Type) → Nat → Type u} {repr' : (Type → Type) → Nat → Type v}
    (R : ∀ ⦃F n⦄, repr F n → repr' F n → Prop)
    [Higher repr] [Higher repr'] (h : Higher.Rel R) :
    R (higher (repr := repr)) (higher (repr := repr')) := higher.parametric R h

abbrev Final := {repr : (n : Nat) → Fin n → Type u} → [Grid repr] →
  (n : Nat) → (i : Fin n) → repr n i

derive_type_rel Final (repr := repr)

example : Final.Rel.{u,v} (fun {repr} _ n i => grid n i (repr := repr))
    (fun {repr} _ n i => grid n i (repr := repr)) := by
  intro repr repr' R l r h n i
  exact grid.parametric n i R h

-- A type may bind several representations of its own, each with its own base
-- relation, and a function between them is related pointwise.
set_option linter.checkUnivs false in
abbrev TwoPairs := {A : Type u} → {C : Type v} → (A → C)

derive_type_rel TwoPairs (repr := A, C)

example (p : TwoPairs.{u, v}) (q : TwoPairs.{w, x}) :
    TwoPairs.Rel p q ↔
      ∀ {A : Type u} {A' : Type w} (R : A → A' → Prop) {C : Type v} {C' : Type x}
        (S : C → C' → Prop) (a : A) (a' : A'), R a a' → S (p a) (q a') := Iff.rfl

-- Proof terms must be checked without adding axioms to make the new cases pass.
#guard_axioms grid.parametric, higher.parametric ⊆ []

end TapasTest.EndToEnd.Shapes
