module

public import Tapas.LogicalRelation.Common.BaseRelationAliases
import Tapas.Applications.Monad.EffectRelation

public section

/-!
Relations for the monad classes Lean provides, and a shortcut for building one.

Nothing in the logical-relation layer depends on these; they are the entries a
monadic client would otherwise have to derive for itself.

`Monad.Rel.ofPureBind` is the one hand-written proof here. `Monad.Rel` has a field
per operation of the whole inheritance chain, `map` through `bind`, so relating a
pair of interpretations means discharging all seven; for a lawful monad, relating
`pure` and `bind` is enough, since the rest are definable from them.
-/

open Tapas.LogicalRelation

derive_effect_rel Monad
derive_effect_rel MonadStateOf
derive_effect_rel MonadReaderOf
derive_effect_rel MonadWithReaderOf
derive_effect_rel MonadExceptOf
derive_effect_rel MonadLiftT (monad := n)

namespace Monad.Rel

variable {m : Type u → Type v} {n : Type u → Type w}
  [left : Monad m] [right : Monad n]

private theorem unitFunction_eq {α : Sort u} (f : Unit → α) : f = (fun _ => f ()) :=
  funext fun x => by cases x; rfl

/--
For lawful monads, related `pure` and `bind` imply that every operation in the
`Monad` dictionary is related. Lawfulness is needed for the independently
overridable `map`, `mapConst`, and sequencing methods.
-/
theorem ofPureBind [LawfulMonad m] [LawfulMonad n]
    (R : ComputationRelation m n)
    (pure_rel : ∀ {α : Type u} (a : α), R (Pure.pure a) (Pure.pure a))
    (bind_rel : ∀ {α β : Type u} {x : m α} {y : n α}
      {f : α → m β} {g : α → n β},
      R x y → (∀ a, R (f a) (g a)) → R (x >>= f) (y >>= g)) :
    Monad.Rel R where
  map := by
    intro α β f x y h
    simp only [map_eq_pure_bind]
    exact bind_rel h (fun a => pure_rel (f a))
  mapConst := by
    intro α β a x y h
    simp only [map_const, Function.comp_apply, map_eq_pure_bind]
    exact bind_rel h (fun _ => pure_rel a)
  pure := pure_rel
  seq := by
    intro α β f g h x y hxy
    rw [unitFunction_eq x, unitFunction_eq y]
    simp only [seq_eq_bind_map, map_eq_pure_bind]
    exact bind_rel h (fun a => bind_rel (hxy ()) (fun b => pure_rel (a b)))
  seqLeft := by
    intro α β x y h f g hfg
    rw [unitFunction_eq f, unitFunction_eq g]
    simp only [seqLeft_eq_bind]
    exact bind_rel h (fun a => bind_rel (hfg ()) (fun _ => pure_rel a))
  seqRight := by
    intro α β x y h f g hfg
    rw [unitFunction_eq f, unitFunction_eq g]
    simp only [seqRight_eq_bind]
    exact bind_rel h (fun _ => hfg ())
  bind := by
    intro α β x y h f g hfg
    exact bind_rel h hfg

end Monad.Rel
