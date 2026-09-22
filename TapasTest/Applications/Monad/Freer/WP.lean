module

public import TapasTest.TestingUtils
public import TapasTest.Applications.Monad.Freer.Basic
public import Std.Do
import Std.Tactic.Do
import Std.Tactic.BVDecide.Normalize.Prop

public section

/-!
Verify a reified program from operation specifications, then transfer the result
to its original final encoding. Bounded input is specified by all allowed answers;
an executable handler only needs to choose an answer satisfying that specification.
-/

namespace TapasTest.Applications.Monad.Freer.WP

open Std.Do Tapas.Parametricity TapasTest.Applications.Monad.Freer.Basic

universe u v w

-- Fixing request syntax does not fix its meaning. The caller supplies that meaning
-- as a predicate transformer for each request; fold extends it to the whole tree.
/-- Operation specifications give a weakest-precondition interpretation of request trees. -/
abbrev wpMonad {E : Type u → Type v} {ps : PostShape.{u}}
    (spec : (α : Type u) → E α → PredTrans ps α) : WPMonad (Freer E) ps where
  wp := Freer.fold spec
  wp_pure _ := rfl
  wp_bind x f := Freer.fold_bind spec x f

/-- A handler satisfying each operation specification preserves every proved precondition. -/
theorem fold_sound {E : Type u → Type v} {ps : PostShape.{u}}
    (spec : (α : Type u) → E α → PredTrans ps α)
    {m : Type u → Type w} [Monad m] [WPMonad m ps]
    (handler : (α : Type u) → E α → m α)
    (hspec : ∀ α (op : E α) Q, (spec α op).apply Q ⊢ₛ wp⟦handler α op⟧ Q)
    {α : Type u} (tree : Freer E α) (Q : PostCond α ps) :
    (Freer.fold spec tree).apply Q ⊢ₛ wp⟦Freer.fold handler tree⟧ Q := by
  induction tree with
  | pure a => simp only [Freer.fold, WPMonad.wp_pure]; exact .rfl
  | impure op k ih =>
    simp only [Freer.fold, WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine (hspec _ op _).trans ((wp (handler _ op)).mono _ _ ?_)
    exact ⟨ih, .rfl⟩

inductive InputOp : Type → Type where
  | sample : Nat → InputOp Nat

-- The predicate must hold for every permitted answer, not just one chosen answer.
-- Even at bound = 0 there is an allowed answer, so this specification is not vacuous.
def inputSpec : (α : Type) → InputOp α → PredTrans .pure α
  | _, .sample bound => {
      trans := fun Q => spred(∀ value, ⌜value ≤ bound⌝ → Q.1 value)
      conjunctiveRaw := by
        intro Q₁ Q₂
        constructor
        · intro h
          exact ⟨fun value hv => (h value hv).1, fun value hv => (h value hv).2⟩
        · rintro ⟨h₁, h₂⟩ value hv
          exact ⟨h₁ value hv, h₂ value hv⟩ }

local instance : WPMonad (Freer InputOp) .pure := wpMonad inputSpec

-- This is the only primitive specification the verification-condition generator needs.
@[spec]
theorem sample_spec (bound : Nat) :
    ⦃⌜True⌝⦄ (MonadLift.monadLift (InputOp.sample bound) : Freer InputOp Nat)
      ⦃⇓ value => ⌜value ≤ bound⌝⦄ := by
  intro _ value hv
  exact hv

/-- Request two bounded inputs and return their sum. -/
def sumInputs (bound : Nat) : Final.{0, 0, w} InputOp Nat := fun {_} _ h => do
  let first ← h _ (.sample bound)
  let second ← h _ (.sample bound)
  pure (first + second)

derive_parametric sumInputs (repr := m)

-- No executable handler has been selected here: mvcgen uses the request specification.
set_option mvcgen.warning false in
theorem sumInputs_spec (bound : Nat) :
    ⦃⌜True⌝⦄ toFreer (sumInputs bound) ⦃⇓ total => ⌜total ≤ 2 * bound⌝⦄ := by
  mvcgen [toFreer, sumInputs]
  all_goals (mleave; omega)

-- The program proof transfers to any handler satisfying the operation specifications.
-- Parametricity supplies the cross-universe roundtrip, from Freer in Type 1 to m.
theorem sumInputs_correct (bound : Nat) {m : Type → Type w} [Monad m] [WPMonad m .pure]
    (handler : (α : Type) → InputOp α → m α)
    (hspec : ∀ α (op : InputOp α) Q, (inputSpec α op).apply Q ⊢ₛ wp⟦handler α op⟧ Q) :
    ⦃⌜True⌝⦄ sumInputs bound handler ⦃⇓ total => ⌜total ≤ 2 * bound⌝⦄ := by
  rw [← toFinal_toFreer_rel (sumInputs.{1} bound) (sumInputs.{w} bound)
    (sumInputs.parametric bound) handler]
  exact SPred.entails.trans (sumInputs_spec bound)
    (fold_sound inputSpec handler hspec _ _)

/-- Execute requests using a chosen answer for each bound. -/
def runWith (choose : Nat → Nat) : (α : Type) → InputOp α → Id α
  | _, .sample bound => choose bound

theorem runWith_sound (choose : Nat → Nat) (hchoose : ∀ bound, choose bound ≤ bound) :
    ∀ α (op : InputOp α) Q, (inputSpec α op).apply Q ⊢ₛ wp⟦runWith choose α op⟧ Q := by
  intro α op Q
  cases op with
  | sample bound =>
    intro h
    exact h (choose bound) (hchoose bound)

-- This is an execution property of the original Final program. Its proof reuses the
-- syntax-level verification and handler soundness, without unfolding the program.
theorem sumInputs_run_bound (choose : Nat → Nat) (hchoose : ∀ bound, choose bound ≤ bound)
    (bound : Nat) : (sumInputs bound (runWith choose)).run ≤ 2 * bound :=
  sumInputs_correct bound (runWith choose) (runWith_sound choose hchoose) True.intro

example (bound : Nat) : (sumInputs bound (runWith (fun _ => 0))).run ≤ 2 * bound :=
  sumInputs_run_bound _ (fun _ => Nat.zero_le _) bound

example (bound : Nat) : (sumInputs bound (runWith id)).run ≤ 2 * bound :=
  sumInputs_run_bound _ (fun _ => Nat.le_refl _) bound

#guard (sumInputs 10 (runWith (fun _ => 0))).run == 0
#guard (sumInputs 10 (runWith id)).run == 20
#guard (sumInputs 0 (runWith id)).run == 0

-- The specification allows nonzero answers: it cannot establish a zero-only result.
example : ¬ (⦃⌜True⌝⦄ toFreer (sumInputs 1) ⦃⇓ total => ⌜total = 0⌝⦄) := by
  intro h
  have impossible := h True.intro 1 (Nat.le_refl 1) 1 (Nat.le_refl 1)
  cases impossible

#guard_uses sumInputs_correct ⊇ [sumInputs_spec, fold_sound, toFinal_toFreer_rel,
  sumInputs.parametric]
#guard_uses sumInputs_run_bound ⊇ [sumInputs_correct, runWith_sound]
#guard_axioms sumInputs.parametric ⊆ []
#guard_axioms wpMonad, fold_sound, inputSpec, sample_spec, sumInputs_spec,
  sumInputs_correct, runWith_sound, sumInputs_run_bound ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Freer.WP
