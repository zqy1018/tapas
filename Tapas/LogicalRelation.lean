import Tapas.LogicalRelation.Derive
import Tapas.LogicalRelation.Relators

/-!
Relations between two interpretations of an effect capability:

* `LogicalRelation.Basic`: `ComputationRelation`, the table of generated capability
  relations, and the relator table with `@[effect_relator]`.
* `LogicalRelation.OperationRelation`: `operationRelation`, the relation for an
  operation type.
* `LogicalRelation.Derive`: `derive_effect_rel`, which declares the relation class `C.Rel` of a
  capability, and `derive_type_rel`, which declares the relation `T.Rel` of a type that binds
  its own monad, such as the type of a tagless final program.
* `LogicalRelation.Relators`: relators for common data types.
-/
