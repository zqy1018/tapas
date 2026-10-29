module

public import TapasTest.TestingUtils
public import TapasTest.Applications.Monad.Freer.Basic
public import Std.WP
import Std.Tactic.Do
import Std.Tactic.BVDecide.Normalize.Prop

set_option experimental.vcgen true

public section

/-!
Verify a reified program from operation specifications, then transfer the result
to its original final encoding. Bounded input is specified by all allowed answers;
an executable handler only needs to choose an answer satisfying that specification.
-/

namespace TapasTest.Applications.Monad.Freer.WP

open Std.WP Lean.Order Tapas.Parametricity TapasTest.Applications.Monad.Freer.Basic

universe u v w

-- Fixing request syntax does not fix its meaning. The caller supplies that meaning
-- as a predicate transformer for each request; fold extends it to the whole tree.
/-- Operation specifications give a weakest-precondition interpretation of request trees. -/
abbrev wpOfSpec {E : Type u → Type v} {Pred EPred : Type u} {α : Type u}
    [Assertion Pred] [Assertion EPred]
    (spec : (α : Type u) → E α → PredTrans Pred EPred α)
    (mono : ∀ α (op : E α), (spec α op).monotone) : WP (Freer E α) α Pred EPred where
  wpTrans := Freer.fold spec
  wp_trans_monotone tree := by
    induction tree with
    | pure a => exact fun _ _ _ _ _ hpost => hpost a
    | impure op k ih =>
      intro post post' epost epost' hepost hpost
      simp only [Freer.fold, PredTrans.apply_Bind_bind]
      exact mono _ op _ _ _ _ hepost (fun a => ih a _ _ _ _ hepost hpost)

/-- The request-tree interpretation is sound for the monad operations. -/
abbrev wpMonad {E : Type u → Type v} {Pred EPred : Type u}
    [Assertion Pred] [Assertion EPred]
    (spec : (α : Type u) → E α → PredTrans Pred EPred α)
    (mono : ∀ α (op : E α), (spec α op).monotone) : WPMonad (Freer E) Pred EPred where
  toWP _ := wpOfSpec spec mono
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := by
    change (Freer.fold spec x).apply (fun a => (Freer.fold spec (f a)).apply post epost) epost ⊑
      (Freer.fold spec (Freer.bind x f)).apply post epost
    rw [Freer.fold_bind]
    exact PartialOrder.rel_refl

/-- A handler satisfying each operation specification preserves every proved precondition. -/
theorem fold_sound {E : Type u → Type v} {Pred EPred : Type u}
    [Assertion Pred] [Assertion EPred]
    (spec : (α : Type u) → E α → PredTrans Pred EPred α)
    {m : Type u → Type w} [Monad m] [WPMonad m Pred EPred]
    (handler : (α : Type u) → E α → m α)
    (hspec : ∀ α (op : E α) Q E, (spec α op).apply Q E ⊑ wp (handler α op) Q E)
    {α : Type u} (tree : Freer E α) (Q : α → Pred) (E : EPred) :
    (Freer.fold spec tree).apply Q E ⊑ wp (Freer.fold handler tree) Q E := by
  induction tree with
  | pure a => exact WPMonad.pure_le_wp_pure a Q E
  | impure op k ih =>
    simp only [Freer.fold, PredTrans.apply_Bind_bind]
    exact PartialOrder.rel_trans (hspec _ op _ E)
      (PartialOrder.rel_trans (WP.wp_consequence _ _ _ E ih)
        (WPMonad.bind_le_wp_bind _ _ Q E))

inductive InputOp : Type → Type where
  | sample : Nat → InputOp Nat

-- The predicate must hold for every permitted answer, not just one chosen answer.
-- Even at bound = 0 there is an allowed answer, so this specification is not vacuous.
def inputSpec : (α : Type) → InputOp α → PredTrans Prop EStack⟨⟩ α
  | _, .sample bound => ⟨fun Q _ => ∀ value, value ≤ bound → Q value⟩

local instance : WPMonad (Freer InputOp) Prop EStack⟨⟩ :=
  wpMonad inputSpec (fun _ op => by
    cases op with
    | sample bound => exact fun _ _ _ _ _ hpost h value hv => hpost value (h value hv))

-- This is the only primitive specification the verification-condition generator needs.
@[spec]
theorem sample_spec (bound : Nat) :
    ⦃True⦄ (MonadLift.monadLift (InputOp.sample bound) : Freer InputOp Nat)
      ⦃fun value => value ≤ bound⦄ := by
  constructor
  intro _ value hv
  exact hv

/-- Request two bounded inputs and return their sum. -/
def sumInputs (bound : Nat) : Final.{0, 0, w} InputOp Nat := fun {_} _ _ => do
  let first ← liftM (InputOp.sample bound)
  let second ← liftM (InputOp.sample bound)
  pure (first + second)

derive_parametric sumInputs (repr := m)

-- No executable handler has been selected here: vcgen uses the request specification.
theorem sumInputs_spec (bound : Nat) :
    ⦃True⦄ toFreer (@sumInputs bound) ⦃fun total => total ≤ 2 * bound⦄ := by
  simp only [toFreer, sumInputs, liftM, Spec.UnfoldLift.monadLift_trans,
    Spec.UnfoldLift.monadLift_refl]
  vcgen
  all_goals omega

-- The program proof transfers to any MonadLiftT implementation satisfying the operation specifications.
-- Parametricity supplies the cross-universe roundtrip, from Freer in Type 1 to m.
theorem sumInputs_correct (bound : Nat) {m : Type → Type w} [Monad m] [WPMonad m Prop EStack⟨⟩]
    [MonadLiftT InputOp m]
    (hspec : ∀ α (op : InputOp α) Q E,
      (inputSpec α op).apply Q E ⊑ wp (monadLift op : m α) Q E) :
    ⦃True⦄ sumInputs bound (m := m) ⦃fun total => total ≤ 2 * bound⦄ := by
  rw [← toFinal_toFreer_rel (@sumInputs.{1} bound) (@sumInputs.{w} bound)
    (sumInputs.parametric bound)]
  exact ⟨PartialOrder.rel_trans (sumInputs_spec bound).le_wp
    (fold_sound inputSpec (fun _ => monadLift) hspec _ _ _)⟩

/-- Execute requests using a chosen answer for each bound. -/
@[instance_reducible] def runWith (choose : Nat → Nat) : MonadLift InputOp Id where
  monadLift
    | .sample bound => choose bound

theorem runWith_sound (choose : Nat → Nat) (hchoose : ∀ bound, choose bound ≤ bound) :
    letI := runWith choose
    ∀ α (op : InputOp α) Q E,
      (inputSpec α op).apply Q E ⊑ wp (monadLift op : Id α) Q E := by
  letI := runWith choose
  intro α op Q E
  cases op with
  | sample bound =>
    intro h
    exact h (choose bound) (hchoose bound)

-- This is an execution property of the original Final program. Its proof reuses the
-- syntax-level verification and handler soundness, without unfolding the program.
theorem sumInputs_run_bound (choose : Nat → Nat) (hchoose : ∀ bound, choose bound ≤ bound)
    (bound : Nat) :
    letI := runWith choose
    (sumInputs bound (m := Id)).run ≤ 2 * bound := by
  letI := runWith choose
  exact (sumInputs_correct bound (runWith_sound choose hchoose)).le_wp True.intro

example (bound : Nat) :
    letI := runWith (fun _ => 0)
    (sumInputs bound (m := Id)).run ≤ 2 * bound :=
  sumInputs_run_bound _ (fun _ => Nat.zero_le _) bound

example (bound : Nat) :
    letI := runWith id
    (sumInputs bound (m := Id)).run ≤ 2 * bound :=
  sumInputs_run_bound _ (fun _ => Nat.le_refl _) bound

#guard (letI := runWith (fun _ => 0); (sumInputs 10 (m := Id)).run) == 0
#guard (letI := runWith id; (sumInputs 10 (m := Id)).run) == 20
#guard (letI := runWith id; (sumInputs 0 (m := Id)).run) == 0

-- The specification allows nonzero answers: it cannot establish a zero-only result.
example : ¬ (⦃True⦄ toFreer (@sumInputs 1) ⦃fun total => total = 0⦄) := by
  intro h
  have impossible := h.le_wp True.intro 1 (Nat.le_refl 1) 1 (Nat.le_refl 1)
  cases impossible

#guard_uses sumInputs_correct ⊇ [sumInputs_spec, fold_sound, toFinal_toFreer_rel,
  sumInputs.parametric]
#guard_uses sumInputs_run_bound ⊇ [sumInputs_correct, runWith_sound]
#guard_axioms sumInputs.parametric ⊆ []
#guard_axioms wpMonad, fold_sound, inputSpec, runWith_sound ⊆ [propext, Quot.sound]
-- The assertion-lattice operations used by `Std.WP` add `Classical.choice` to these proofs.
#guard_axioms sample_spec, sumInputs_spec, sumInputs_correct, sumInputs_run_bound
  ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.Freer.WP
