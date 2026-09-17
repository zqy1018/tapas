import Init

namespace Tapas.LogicalRelation

/-- Relations between interpretations at a shared index. -/
abbrev IndexedRelation {I : Sort u} (repr : I → Type v) (repr' : I → Type w) :=
  {i : I} → repr i → repr' i → Prop

/-- The relation preserves the value type, but may change the computation universe. -/
abbrev ComputationRelation (m : Type u → Type v) (n : Type u → Type w) :=
  {α : Type u} → m α → n α → Prop

end Tapas.LogicalRelation
