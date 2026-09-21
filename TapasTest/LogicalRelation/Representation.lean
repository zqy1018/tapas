import Tapas

open Tapas.LogicalRelation

namespace TapasTest.LogicalRelation.Representation

/-!
Each example checks the base relation type expected by a generated declaration.
`guard_target =ₛ` and `guard_hyp :ₛ` compare expressions syntactically, so an
expanded type cannot pass a check expecting an alias, even when they are defeq.
-/

namespace Indexed

attribute [local base_relation_alias] IndexedRelation

class Atom (repr : Bool → Type u) where
  atom : repr true

derive_interface_rel Atom (repr := repr)

example {repr : Bool → Type u} {repr' : Bool → Type v}
    (left : Atom repr) (right : Atom repr') :
    Atom.Rel (left := left) (right := right) (by
      guard_target =ₛ IndexedRelation repr repr'
      exact fun {_} _ _ => True) := by constructor <;> intros <;> trivial

end Indexed

namespace Monadic

attribute [local base_relation_alias 1100] ComputationRelation
attribute [local base_relation_alias] IndexedRelation

class Atom (m : Type u → Type v) where
  atom {α : Type u} : α → m α

derive_interface_rel Atom (repr := m)

-- Both aliases fit, but the higher-priority ComputationRelation must be used.
example {m : Type u → Type v} {n : Type u → Type w}
    (left : Atom m) (right : Atom n) :
    Atom.Rel (left := left) (right := right) (by
      guard_target =ₛ ComputationRelation m n
      fail_if_success guard_target =ₛ IndexedRelation m n
      exact fun {_} _ _ => True) := by constructor <;> intros <;> trivial

def monadic := infer_effects% pure (1 : Nat)
derive_parametric monadic

example {m n : Type → Type} [lm : Monad m] [rn : Monad n]
    (h : Monad.Rel (left := lm) (right := rn) (fun {_} _ _ => True)) : True :=
  monadic.parametric (m := m) (m' := n) (by
    guard_target =ₛ ComputationRelation m n
    exact fun {_} _ _ => True) h

end Monadic

namespace PreferIndexed

attribute [local base_relation_alias 1100] ComputationRelation
attribute [local base_relation_alias 1200] IndexedRelation

class Atom (m : Type → Type) where
  atom : m Nat

derive_interface_rel Atom (repr := m)

example {m n : Type → Type} (left : Atom m) (right : Atom n) :
    Atom.Rel (left := left) (right := right) (by
      guard_target =ₛ IndexedRelation m n
      exact fun {_} _ _ => True) := by constructor <;> intros <;> trivial

end PreferIndexed

namespace MultipleRepresentations

attribute [local base_relation_alias 1100] ComputationRelation
attribute [local base_relation_alias] IndexedRelation

abbrev Program :=
  {m : relMarker (Type → Type)} → {repr : relMarker (Bool → Type)} →
    m Nat → repr true → m Nat

-- Both binders are marked in the declaration, so the command needs no selection.
derive_type_rel Program

example : Program.Rel (fun x _ => x) (fun x _ => x) := by
  intro m n R repr repr' S
  guard_hyp R :ₛ ComputationRelation m n
  guard_hyp S :ₛ IndexedRelation repr repr'
  intro x y h _ _ _
  exact h

end MultipleRepresentations

namespace MultipleIndices

attribute [local base_relation_alias 1100] ComputationRelation
attribute [local base_relation_alias] IndexedRelation

class Atom (repr : (i : Nat) → (j : Bool) → Type) where
  atom : repr 0 true

derive_interface_rel Atom (repr := repr)

-- Neither one-index alias fits: the generated telescope must remain expanded.
example {repr repr' : Nat → Bool → Type} (left : Atom repr) (right : Atom repr') :
    Atom.Rel (left := left) (right := right) (by
      guard_target =ₛ ∀ ⦃i : Nat⦄ ⦃j : Bool⦄, repr i j → repr' i j → Prop
      exact fun {_ _} _ _ => True) := by constructor <;> intros <;> trivial

end MultipleIndices

namespace Unregistered

-- The local registrations above have expired, although the aliases still exist.
class Atom (m : (a : Type) → Type) where
  atom : m Nat

derive_interface_rel Atom (repr := m)

example {m n : Type → Type} (left : Atom m) (right : Atom n) :
    Atom.Rel (left := left) (right := right) (by
      guard_target =ₛ ∀ ⦃a : Type⦄, m a → n a → Prop
      exact fun {_} _ _ => True) := by constructor <;> intros <;> trivial

end Unregistered

end TapasTest.LogicalRelation.Representation
