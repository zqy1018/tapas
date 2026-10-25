module

import all Init.System.ST
import all Init.System.IO
import all Init.Control.Except
import TapasTest.TestingUtils
public import TapasTest.Applications.Monad.Freer.Transfer

public section

/-!
Facts about `IO` that the examples use: `IO` is a lawful monad; `relIO` relates two `IO`
computations that, started in the same world, have the same effects and related results; the
monad operations, the lifts of `BaseIO` actions and `tryFinally` are stated at a world; and
`NoError` says a computation never throws, in which case `tryFinally'` is a plain sequence. All
are proved from the definition of `IO` in terms of `EST`, which `import all` makes visible, and
none needs an axiom.
-/

namespace TapasTest.Applications.Monad.IO.Basic

open TapasTest.Applications.Monad.Freer.Transfer

-- NOTE: The same instance exists in `Batteries/Lean/LawfulMonad.lean`.
-- Essentially this is about `LawfulMonad EST`
instance lawfulIO : LawfulMonad IO :=
  LawfulMonad.mk' IO
    (fun x => by
      funext w
      change EST.bind x (fun a => EST.pure (id a)) w = x w
      simp only [EST.bind, EST.pure]
      cases x w <;> rfl)
    (fun _ _ => rfl)
    (fun x f g => by
      funext w
      change EST.bind (EST.bind x f) g w = EST.bind x (fun a => EST.bind (f a) g) w
      simp only [EST.bind]
      cases x w <;> rfl)

/-- Two `IO` computations started in the same world either both succeed, with related results
and the same final world, or both fail, with the same error and the same final world. -/
def relIO : MonadRelator IO where
  rel S x y := ∀ w, match x w, y w with
    | .ok a w₁, .ok b w₂ => S a b ∧ w₁ = w₂
    | .error e₁ w₁, .error e₂ w₂ => e₁ = e₂ ∧ w₁ = w₂
    | _, _ => False
  pure hs := fun _ => ⟨hs, rfl⟩
  bind := by
    intro α β γ δ S S' x y f g hxy hfg w
    have hw := hxy w
    change (match EST.bind x f w, EST.bind y g w with
      | .ok a w₁, .ok b w₂ => S' a b ∧ w₁ = w₂
      | .error e₁ w₁, .error e₂ w₂ => e₁ = e₂ ∧ w₁ = w₂
      | _, _ => False)
    simp only [EST.bind]
    revert hw
    cases x w <;> cases y w <;> simp only [false_implies, and_imp] <;> intros <;> subst_vars
    · exact hfg _ _ ‹_› _
    · simp
  refl x := fun w => by cases x w <;> simp

-- `relIO` is not exposed, because its proofs unfold `EST`. This states what its relations are.
theorem relIO_rel_iff {α β : Type} (S : α → β → Prop) (x : IO α) (y : IO β) :
    relIO.rel S x y ↔ ∀ w, match x w, y w with
      | .ok a w₁, .ok b w₂ => S a b ∧ w₁ = w₂
      | .error e₁ w₁, .error e₂ w₂ => e₁ = e₂ ∧ w₁ = w₂
      | _, _ => False :=
  Iff.rfl

/-- Related by equality, two `IO` computations are equal. -/
theorem relIO_eq_iff {α : Type} (x y : IO α) : relIO.rel Eq x y ↔ x = y := by
  rw [relIO_rel_iff]
  constructor
  · intro h
    funext w
    have hw := h w
    revert hw
    cases x w <;> cases y w <;> simp_all
  · rintro rfl
    exact relIO.refl x

/-! ## IO computations at a world

`IO α` is a function from the world to an outcome. The outcome of an opaque action is a stuck
`match`, and two `match` expressions on it with different matchers are not definitionally
equal, so the proofs case on the outcome. The outcome of a `BaseIO` action is a structure, which
projections reach definitionally. -/

section Pointwise

variable {α β : Type}

theorem bind_apply (x : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (x >>= f) w = match x w with
      | .ok a w => f a w
      | .error e w => .error e w := by
  show EST.bind x f w = _
  unfold EST.bind
  cases x w <;> rfl

theorem map_apply (g : α → β) (x : IO α) (w : Void IO.RealWorld) :
    (g <$> x) w = match x w with
      | .ok a w => .ok (g a) w
      | .error e w => .error e w := by
  show EST.bind x (fun a => EST.pure (g a)) w = _
  unfold EST.bind
  cases x w <;> rfl

theorem pure_apply (a : α) (w : Void IO.RealWorld) : (pure a : IO α) w = .ok a w := by rfl

theorem lift_apply (x : BaseIO α) (w : Void IO.RealWorld) :
    (liftM x : IO α) w = .ok (x w).val (x w).state := by rfl

theorem toIO_apply (x : BaseIO α) (w : Void IO.RealWorld) :
    BaseIO.toIO x w = .ok (x w).val (x w).state := by rfl

theorem bind_base_apply (x : BaseIO α) (f : α → BaseIO β) (w : Void IO.RealWorld) :
    (x >>= f) w = f (x w).val (x w).state := by rfl

theorem pure_base_apply (a : α) (w : Void IO.RealWorld) : (pure a : BaseIO α) w = .mk a w := by rfl

theorem tryFinally'_apply (x : IO α) (g : Option α → IO β) (w : Void IO.RealWorld) :
    MonadFinally.tryFinally' x g w = match x w with
      | .ok a w => (match g (some a) w with
        | .ok b w => .ok (a, b) w
        | .error e w => .error e w)
      | .error e w => (match g none w with
        | .ok _ w => .error e w
        | .error e' w => .error e' w) := by
  show instMonadFinallyEIO._aux_1 x g w = _
  unfold instMonadFinallyEIO._aux_1
  dsimp only
  cases x w with
  | ok a w' =>
    dsimp only
    cases g (some a) w' <;> rfl
  | error e w' =>
    dsimp only
    cases g none w' <;> rfl

theorem tryFinally_apply (x : IO α) (f : IO β) (w : Void IO.RealWorld) :
    tryFinally x f w = match x w with
      | .ok a w => (match f w with
        | .ok _ w => .ok a w
        | .error e w => .error e w)
      | .error e w => (match f w with
        | .ok _ w => .error e w
        | .error e' w => .error e' w) := by
  unfold tryFinally
  rw [map_apply, tryFinally'_apply]
  cases x w with
  | ok a w' =>
    dsimp only
    cases f w' <;> rfl
  | error e w' =>
    dsimp only
    cases f w' <;> rfl

end Pointwise

/-! ## Computations that do not throw -/

/-- An IO computation that never throws. -/
def NoError {α : Type} (x : IO α) : Prop := ∀ w, ∃ a w', x w = .ok a w'

namespace NoError

variable {α β : Type}

theorem pure (a : α) : NoError (pure a : IO α) := fun w => ⟨a, w, pure_apply a w⟩

theorem lift (x : BaseIO α) : NoError (liftM x : IO α) := fun w => ⟨_, _, lift_apply x w⟩

theorem toIO (x : BaseIO α) : NoError (BaseIO.toIO x) := fun w => ⟨_, _, toIO_apply x w⟩

theorem bind {x : IO α} {f : α → IO β} (hx : NoError x) (hf : ∀ a, NoError (f a)) :
    NoError (x >>= f) := by
  intro w
  obtain ⟨a, w', hx⟩ := hx w
  obtain ⟨b, w'', hf⟩ := hf a w'
  exact ⟨b, w'', by simp only [bind_apply, hx]; exact hf⟩

end NoError

/-- Without an exception, `tryFinally'` runs the computation and then the finalizer. -/
theorem tryFinally'_of_noError {α β : Type} {x : IO α} (hx : NoError x) (g : Option α → IO β) :
    MonadFinally.tryFinally' x g = x >>= fun a => g (some a) >>= fun b => pure (a, b) := by
  funext w
  obtain ⟨a, w', hx⟩ := hx w
  rw [tryFinally'_apply, bind_apply, hx]
  dsimp only
  rw [bind_apply]
  cases g (some a) w' <;> rfl

/-- Without an exception, `tryFinally` runs the computation and then the finalizer. -/
theorem tryFinally_of_noError {α β : Type} {x : IO α} (hx : NoError x) (f : IO β) :
    tryFinally x f = x >>= fun a => f >>= fun _ => pure a := by
  funext w
  obtain ⟨a, w', hx⟩ := hx w
  rw [tryFinally_apply, bind_apply, hx]
  dsimp only
  rw [bind_apply]
  cases f w' <;> rfl

#guard_axioms lawfulIO ⊆ [propext, Quot.sound]
#guard_axioms relIO, relIO_rel_iff, relIO_eq_iff ⊆ [propext, Quot.sound]
#guard_uses relIO_eq_iff ⊇ [relIO_rel_iff]
#guard_axioms bind_apply, map_apply, tryFinally'_apply, tryFinally_apply, NoError.bind,
  tryFinally'_of_noError, tryFinally_of_noError ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.IO.Basic
