module

public import Std.WP
import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.TimeSetup

-- `#time_setup` must observe each proof's checking.
set_option Elab.async false

public section

/-!
Registered `wp` equations for the `wp-simp` and `wp-sym` routes, which rewrite the original
program's `wp` until none is left, as Veil does with its actions' `wp` equations. Lean's own
`WPMonad` gives `bind` only an inequality, so each concrete monad gets its equations here. They are
fully applied, so that a rewrite at the top needs no beta step first. An equation cannot weaken:
a procedure with a contract must be unfolded instead, and `match` on a symbolic value has none.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison.WPEquations

open Lean.Order Std.WP

variable {σ ρ ε α β : Type}

#time_setup "order.wp.function"
/-- The order on assertions is pointwise. -/
theorem pi_rel_eq {β : α → Type} [∀ a, PartialOrder (β a)] (f g : ∀ a, β a) :
    (f ⊑ g) = ∀ a, f a ⊑ g a := rfl

#time_setup "order.wp.prop"
/-- The order on propositions is implication. -/
theorem prop_rel_eq (p q : Prop) : (p ⊑ q) = (p → q) := rfl

namespace StateM

#time_setup "state.wp.bind"
theorem wp_bind (x : StateM σ α) (f : α → StateM σ β) (post : β → σ → Prop) (epost : EStack⟨⟩)
    (s : σ) : wp (x >>= f) post epost s = wp x (fun a => wp (f a) post epost) epost s := rfl

#time_setup "state.wp.get"
theorem wp_get (post : σ → σ → Prop) (epost : EStack⟨⟩) (s : σ) :
    wp (get : StateM σ σ) post epost s = post s s := rfl

#time_setup "state.wp.set"
theorem wp_set (x : σ) (post : PUnit → σ → Prop) (epost : EStack⟨⟩) (s : σ) :
    wp (set x : StateM σ PUnit) post epost s = post ⟨⟩ x := rfl

#time_setup "state.wp.StateT_set"
/-- Unfolding the upstream programs leaves `StateT.set` itself. -/
theorem wp_StateT_set (x : σ) (post : PUnit → σ → Prop) (epost : EStack⟨⟩) (s : σ) :
    wp (StateT.set x : StateM σ PUnit) post epost s = post ⟨⟩ x := rfl

#time_setup "state.wp.pure"
theorem wp_pure (a : α) (post : α → σ → Prop) (epost : EStack⟨⟩) (s : σ) :
    wp (pure a : StateM σ α) post epost s = post a s := rfl

#time_setup "state.wp.modify"
theorem wp_modify (f : σ → σ) (post : PUnit → σ → Prop) (epost : EStack⟨⟩) (s : σ) :
    wp (modify f : StateM σ PUnit) post epost s = post ⟨⟩ (f s) := rfl

end StateM

namespace ReaderState

#time_setup "reader_state.wp.bind"
theorem wp_bind (x : ReaderT ρ (StateM σ) α) (f : α → ReaderT ρ (StateM σ) β)
    (post : β → ρ → σ → Prop) (epost : EStack⟨⟩) (r : ρ) (s : σ) :
    wp (x >>= f) post epost r s = wp x (fun a => wp (f a) post epost) epost r s := rfl

#time_setup "reader_state.wp.read"
theorem wp_read (post : ρ → ρ → σ → Prop) (epost : EStack⟨⟩) (r : ρ) (s : σ) :
    wp (read : ReaderT ρ (StateM σ) ρ) post epost r s = post r r s := rfl

#time_setup "reader_state.wp.get"
theorem wp_get (post : σ → ρ → σ → Prop) (epost : EStack⟨⟩) (r : ρ) (s : σ) :
    wp (get : ReaderT ρ (StateM σ) σ) post epost r s = post s r s := rfl

#time_setup "reader_state.wp.set"
theorem wp_set (x : σ) (post : PUnit → ρ → σ → Prop) (epost : EStack⟨⟩) (r : ρ) (s : σ) :
    wp (set x : ReaderT ρ (StateM σ) PUnit) post epost r s = post ⟨⟩ r x := rfl

#time_setup "reader_state.wp.pure"
theorem wp_pure (a : α) (post : α → ρ → σ → Prop) (epost : EStack⟨⟩) (r : ρ) (s : σ) :
    wp (pure a : ReaderT ρ (StateM σ) α) post epost r s = post a r s := rfl

end ReaderState

namespace ExceptState

#time_setup "except_state.wp.id"
/-- `Id`'s interpretation is evaluation. -/
theorem id_wp (y : Id α) (post : α → Prop) (epost : EStack⟨⟩) : wp y post epost = post y.run := rfl

#time_setup "except_state.wp.bind"
/-- The one equation that needs a case split, on the outcome of `x`. -/
theorem wp_bind (x : ExceptT ε (StateM σ) α) (f : α → ExceptT ε (StateM σ) β)
    (post : β → σ → Prop) (epost : (ε → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (x >>= f) post epost s = wp x (fun a => wp (f a) post epost) epost s := by
  simp only [ExceptT.wp_apply_eq, StateT.wp_apply_eq, id_wp, ExceptT.run_bind, StateT.run_bind,
    Id.run_bind]
  rcases x.run.run s with ⟨r, s'⟩
  cases r <;> rfl

#time_setup "except_state.wp.get"
theorem wp_get (post : σ → σ → Prop) (epost : (ε → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (get : ExceptT ε (StateM σ) σ) post epost s = post s s := rfl

#time_setup "except_state.wp.set"
theorem wp_set (x : σ) (post : PUnit → σ → Prop) (epost : (ε → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (set x : ExceptT ε (StateM σ) PUnit) post epost s = post ⟨⟩ x := rfl

#time_setup "except_state.wp.throw"
theorem wp_throw (e : ε) (post : α → σ → Prop) (epost : (ε → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (throw e : ExceptT ε (StateM σ) α) post epost s = epost.1 e s := rfl

#time_setup "except_state.wp.pure"
theorem wp_pure (a : α) (post : α → σ → Prop) (epost : (ε → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (pure a : ExceptT ε (StateM σ) α) post epost s = post a s := rfl

#time_setup "except_state.wp.ite"
theorem wp_ite (c : Prop) [Decidable c] (x y : ExceptT ε (StateM σ) α) (post : α → σ → Prop)
    (epost : (ε → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (if c then x else y) post epost s = if c then wp x post epost s else wp y post epost s := by
  split <;> rfl

#time_setup "except_state.wp.dite"
theorem wp_dite (c : Prop) [Decidable c] (x : c → ExceptT ε (StateM σ) α)
    (y : ¬c → ExceptT ε (StateM σ) α) (post : α → σ → Prop) (epost : (ε → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (dite c x y) post epost s =
      if h : c then wp (x h) post epost s else wp (y h) post epost s := by
  split <;> rfl

end ExceptState

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison.WPEquations
