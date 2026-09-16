import Tapas.LogicalRelation.Monad

open Tapas.LogicalRelation

derive_effect_rel MonadStateOf
derive_effect_rel MonadReaderOf
derive_effect_rel MonadWithReaderOf
derive_effect_rel MonadExceptOf
derive_effect_rel MonadLiftT (monad := n)
