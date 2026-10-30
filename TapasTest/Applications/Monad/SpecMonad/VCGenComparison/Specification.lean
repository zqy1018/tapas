module

public import Tapas
public import Std.WP

public section

/-!
The specification monads and their parametricity relations to an execution model: Lean's
`PredTrans`, and our own function-type monad without an exception postcondition.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order Std.WP

universe u v w w'

namespace CustomMonad

-- NOTE: There is no built-in `Cont` monad, so define it manually here
/-- Our own predicate transformers: plain functions, without an exception postcondition. -/
abbrev Spec (Pred : Type w) (α : Type u) := (α → Pred) → Pred

instance specMonad : Monad (Spec Pred) where
  pure a := fun post => post a
  bind x f := fun post => x (fun a => f a post)

instance : LawfulMonad (Spec Pred) :=
  LawfulMonad.mk' _ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

end CustomMonad

section

variable {m : Type u → Type v} [Monad m] {Pred : Type w} {EPred : Type w'}
  [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- The calculated predicate transformer is below the execution model's weakest precondition:
`w.apply post epost ⊑ wp x post epost` for every `post` and `epost`. -/
@[expose] def Sound : ComputationRelation m (PredTrans Pred EPred) :=
  fun {_} x w => w ⊑ WP.wpTrans x

-- The monad argument is shared across stacks; operation relations are supplied separately.
theorem Sound.monad : Monad.Rel (Sound (m := m) (Pred := Pred) (EPred := EPred)) :=
  Monad.Rel.ofPureBind _
    (fun a post epost => WPMonad.pure_le_wp_pure a post epost)
    (fun hx hf post epost =>
      PartialOrder.rel_trans (hx _ epost)
        (PartialOrder.rel_trans
          (WP.wp_consequence _ _ _ _ (fun a => hf a post epost))
          (WPMonad.bind_le_wp_bind _ _ post epost)))

/-- The calculated precondition implies the weakest precondition for every exception
postcondition, so no exception may escape. -/
@[expose] def CustomMonad.Sound : ComputationRelation m (CustomMonad.Spec Pred) :=
  fun {_} x w => ∀ post epost, w post ⊑ wp x post epost

theorem CustomMonad.Sound.monad :
    Monad.Rel (CustomMonad.Sound (m := m) (Pred := Pred) (EPred := EPred)) :=
  Monad.Rel.ofPureBind _
    (fun a post epost => WPMonad.pure_le_wp_pure a post epost)
    (fun hx hf post epost =>
      PartialOrder.rel_trans (hx _ epost)
        (PartialOrder.rel_trans
          (WP.wp_consequence _ _ _ _ (fun a => hf a post epost))
          (WPMonad.bind_le_wp_bind _ _ post epost)))

end

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison
