import Tapas.LogicalRelation.Registry

/-!
Relators for common data types, available to every relation generator:

| Type       | Relator             |
|------------|---------------------|
| `Option α` | `Option.Rel` (core) |
| `α ⊕ β`    | `Sum.LiftRel` (core)|
| `List α`   | `ListRel`           |
| `α × β`    | `ProdRel`           |

Each lifts every argument and lets the two sides live in different universes.
At most one relator is registered per type constructor, so these cannot be
replaced where this module is imported.
-/

namespace Tapas.LogicalRelation

/-- Lists of the same length whose elements are related pointwise. -/
inductive ListRel {α : Type u} {β : Type v} (r : α → β → Prop) : List α → List β → Prop
  | nil : ListRel r [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      r a b → ListRel r as bs → ListRel r (a :: as) (b :: bs)

/-- Pairs whose first and second components are related. -/
structure ProdRel {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
    (r : α → α' → Prop) (s : β → β' → Prop) (p : α × β) (q : α' × β') : Prop where
  fst : r p.1 q.1
  snd : s p.2 q.2

attribute [relator] Option.Rel Sum.LiftRel ListRel ProdRel

end Tapas.LogicalRelation
