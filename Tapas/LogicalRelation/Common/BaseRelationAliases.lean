import Init

namespace Tapas.LogicalRelation

/- The index is strict implicit, matching a generated relation type, which these names
have to be definitionally equal to; `withSharedIndices` says why it is bound that way.
`R x y` fills the index from `x` as an ordinary implicit one would, so only handing the
relation on as a whole needs an annotation: `ListRel (R (α := α))`. -/

/-- Relations between interpretations at a shared index. -/
abbrev IndexedRelation {I : Sort u} (repr : I → Type v) (repr' : I → Type w) :=
  ⦃i : I⦄ → repr i → repr' i → Prop

/-- The relation preserves the value type, but may change the computation universe. -/
abbrev ComputationRelation (m : Type u → Type v) (n : Type u → Type w) :=
  ⦃α : Type u⦄ → m α → n α → Prop

end Tapas.LogicalRelation
