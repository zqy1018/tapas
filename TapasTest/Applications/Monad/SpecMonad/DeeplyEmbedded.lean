module

public import Tapas
public import Std.WP
import TapasTest.TestingUtils
import TapasTest.Applications.Monad.SpecMonad.Normalizer

public section

/-!
A deeply embedded language with two ways to calculate preconditions.

`Cmd` is a syntax tree interpreted through its own algebra, without monads. Its execution
interpretation is a state transformer; its specification interpretation is a predicate
transformer. Parametricity proves that the latter calculates exactly the execution's WP.
The language's `WP` instance describes execution, and its `@[spec]` rules let `vcgen` reason
directly about `Cmd`. The normalization route uses the interpretation theorem and
`normalize_spec` to calculate the same WP by unfolding alone.
-/

namespace TapasTest.Applications.Monad.SpecMonad.DeeplyEmbedded

open Tapas.Parametricity Tapas.LogicalRelation Std.WP Lean.Order
open Normalizer

set_option experimental.vcgen true

/-- Commands acting on a natural-number state. -/
inductive Cmd where
  | skip
  | add (amount : Nat)
  | seq (first second : Cmd)
  | ifZero (yes no : Cmd)

/-- An interpretation of the command constructors. -/
class CmdAlg (R : Type) where
  skip : R
  add : Nat → R
  seq : R → R → R
  ifZero : R → R → R

derive_interface_rel CmdAlg (repr := R)

/-- Interpret a syntax tree using the chosen command algebra. -/
@[expose] def denote {R : Type} [CmdAlg R] : Cmd → R
  | .skip => CmdAlg.skip
  | .add amount => CmdAlg.add amount
  | .seq first second => CmdAlg.seq (denote first) (denote second)
  | .ifZero yes no => CmdAlg.ifZero (denote yes) (denote no)

derive_parametric denote (repr := R)

/-- A transformation of the natural-number state. -/
abbrev Exec := Nat → Nat

/-- A transformer from postconditions to preconditions. -/
abbrev Spec := (Nat → Prop) → Nat → Prop

instance execAlgebra : CmdAlg Exec where
  skip := fun s => s
  add amount := fun s => s + amount
  seq first second := fun s => second (first s)
  ifZero yes no := fun s => if s = 0 then yes s else no s

instance specAlgebra : CmdAlg Spec where
  skip := fun post s => post s
  add amount := fun post s => post (s + amount)
  seq first second := fun post s => first (fun s' => second post s') s
  ifZero yes no := fun post s => if s = 0 then yes post s else no post s

-- A conditional between interpretations also stays symbolic during normalization.
example (c : Prop) [Decidable c] (yes no : Spec) (post : Nat → Prop) (s : Nat) :
    (if c then yes else no) post s = (if c then yes post s else no post s) := by
  normalize_spec Spec
  guard_target = (if c then yes else no) post s = (if c then yes post s else no post s)
  exact apply_ite (fun w : Spec => w post s) c yes no

/-- The specification computes exactly the postcondition of the execution. -/
@[expose] def Exact (exec : Exec) (w : Spec) : Prop :=
  ∀ post s, w post s = post (exec s)

theorem Exact.algebra : CmdAlg.Rel Exact where
  skip := fun _ _ => rfl
  add := fun _ _ _ => rfl
  seq x w hx y v hy := by
    intro post s
    change w (fun s' => v post s') s = post (y (x s))
    rw [hx, hy]
  ifZero x w hx y v hy := by
    intro post s
    change (if s = 0 then w post s else v post s) = post (if s = 0 then x s else y s)
    by_cases hs : s = 0
    · simpa only [ite_eq_left hs] using hx post s
    · simpa only [ite_eq_right hs] using hy post s

/-- Interpreting a command in `Spec` computes its execution's weakest precondition. -/
theorem denote_exact (c : Cmd) :
    Exact (denote c (R := Exec)) (denote c (R := Spec)) :=
  denote.parametric Exact Exact.algebra c

/- The `WP` interpretation is defined from execution, independently of the specification
interpreter and of the constructor rules used by `vcgen`. -/
instance : WP Cmd Unit (Nat → Prop) Unit where
  wpTrans c := ⟨fun post _ s => post () (denote c (R := Exec) s)⟩
  wp_trans_monotone c := by
    intro post post' epost epost' _ hpost s hs
    exact hpost _ _ hs

/-- Replace the execution's weakest precondition by the specification interpretation. -/
theorem wp_eq_spec (c : Cmd) (post : Unit → Nat → Prop) (epost : Unit) (s : Nat) :
    wp c post epost s = denote c (R := Spec) (post ()) s :=
  (denote_exact c (post ()) s).symm

/-! ## `@[spec]`s

Constructor rules for the deeply embedded language. These are local registrations, so
importing this example does not change the ambient `vcgen` database. -/

theorem spec_skip (post : Unit → Nat → Prop) (epost : Unit) :
    ⦃post ()⦄ Cmd.skip ⦃post; epost⦄ := ⟨fun _ h => h⟩

theorem spec_add (amount : Nat) (post : Unit → Nat → Prop) (epost : Unit) :
    ⦃fun s => post () (s + amount)⦄ Cmd.add amount ⦃post; epost⦄ := ⟨fun _ h => h⟩

theorem spec_seq (first second : Cmd) (post : Unit → Nat → Prop) (epost : Unit) :
    ⦃wp first (fun _ => wp second post epost) epost⦄
      Cmd.seq first second ⦃post; epost⦄ := ⟨fun _ h => h⟩

theorem spec_ifZero (yes no : Cmd) (post : Unit → Nat → Prop) (epost : Unit) :
    ⦃((fun s => s = 0) ⇨ wp yes post epost) ⊓ ((fun s => s ≠ 0) ⇨ wp no post epost)⦄
      Cmd.ifZero yes no ⦃post; epost⦄ := by
  constructor
  intro s h
  simp only [meet_apply, meet_prop_eq_and, himp_apply, himp_prop_eq_imp] at h
  change post () (if s = 0 then denote yes (R := Exec) s else denote no (R := Exec) s)
  by_cases hs : s = 0
  · simpa only [wp, WP.wpTrans, ite_eq_left hs] using h.1 hs
  · simpa only [wp, WP.wpTrans, ite_eq_right hs] using h.2 hs

attribute [local spec] spec_skip spec_add spec_seq spec_ifZero

/-! ## Example 1

A straight-line command: expose the calculated WP before proving a property. -/

/-- Add two, then three. -/
@[expose] def straightLine : Cmd := .seq (.add 2) (.add 3)

theorem straightLine_wp (post : Unit → Nat → Prop) (s : Nat) :
    wp straightLine post () s = post () ((s + 2) + 3) := by
  rw [wp_eq_spec]
  fail_if_success guard_target = post () ((s + 2) + 3) = post () ((s + 2) + 3)
  normalize_spec Spec
  guard_target = post () ((s + 2) + 3) = post () ((s + 2) + 3)
  rfl

-- The same head reducer also supports the `Sym.dsimp` traversal.
example (post : Unit → Nat → Prop) (s : Nat) :
    wp straightLine post () s = post () ((s + 2) + 3) := by
  rw [wp_eq_spec]
  run_tac Lean.Elab.Tactic.liftMetaTactic fun goal => return [← normalizeSym ``Spec goal]
  guard_target = post () ((s + 2) + 3) = post () ((s + 2) + 3)
  rfl

theorem straightLine_vcgen (initial : Nat) :
    ⦃fun s => s = initial⦄ straightLine ⦃fun _ s => s = initial + 5⦄ := by
  vcgen [straightLine] with finish

theorem straightLine_normalize (initial : Nat) :
    ⦃fun s => s = initial⦄ straightLine ⦃fun _ s => s = initial + 5⦄ := by
  constructor
  intro s hs
  rw [wp_eq_spec]
  normalize_spec Spec
  omega

/-! ## Example 2

A symbolic branch: both branches must be considered for an arbitrary initial state. -/

/-- Add two at zero or three otherwise, then add one. -/
@[expose] def branching : Cmd := .seq (.ifZero (.add 2) (.add 3)) (.add 1)

/- The specification algebra defines the conditional pointwise, so normalization leaves a
proposition-valued `if` with no function applications left to push into its branches. -/
theorem branching_wp (post : Unit → Nat → Prop) (s : Nat) :
    wp branching post () s =
      (if s = 0 then post () ((s + 2) + 1) else post () ((s + 3) + 1)) := by
  rw [wp_eq_spec]
  normalize_spec Spec
  guard_target =
    (if s = 0 then post () ((s + 2) + 1) else post () ((s + 3) + 1)) =
      (if s = 0 then post () ((s + 2) + 1) else post () ((s + 3) + 1))
  rfl

theorem branching_vcgen (initial : Nat) :
    ⦃fun s => s = initial⦄ branching ⦃fun _ s => initial + 3 ≤ s⦄ := by
  vcgen [branching] with finish

theorem branching_normalize (initial : Nat) :
    ⦃fun s => s = initial⦄ branching ⦃fun _ s => initial + 3 ≤ s⦄ := by
  constructor
  intro s hs
  rw [wp_eq_spec]
  normalize_spec Spec
  grind

#guard_parametric denote
#guard_uses type denote ∩ [Monad, MonadStateOf] = ∅
#guard_uses denote, execAlgebra, specAlgebra ∩ [Pure.pure, Bind.bind] = ∅
#guard_uses denote_exact ⊇ [denote.parametric]
#guard_uses wp_eq_spec ⊇ [denote_exact]
#guard_uses straightLine_vcgen ⊇ [spec_add, spec_seq]
#guard_uses branching_vcgen ⊇ [spec_add, spec_seq, spec_ifZero]
#guard_uses straightLine_normalize, branching_normalize ⊇ [wp_eq_spec]
#guard_uses straightLine_normalize, branching_normalize ∩
  [spec_skip, spec_add, spec_seq, spec_ifZero] = ∅
#guard_axioms denote_exact, straightLine_wp, branching_wp,
  straightLine_vcgen, straightLine_normalize, branching_vcgen, branching_normalize
  ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.SpecMonad.DeeplyEmbedded
