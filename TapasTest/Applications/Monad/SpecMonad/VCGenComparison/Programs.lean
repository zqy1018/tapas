module

public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Models
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.AddSubCancel
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.LetBinding
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.ReaderState
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.GetThrowSet
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.DiteSplit
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.MatchSplit
import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.TimeSetup
import TapasTest.TestingUtils

-- `#time_setup` must observe each proof's checking.
set_option Elab.async false

public section

/-!
The programs over abstract operations, their parametricity theorems, and their equality to the
copied upstream programs; both add/sub cases share one program. [Conditions.lean](Conditions.lean)
states their VCs.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order Std.WP

namespace AddSub

-- Match the upstream get/set order; effect inference supplies only the required interfaces.
@[expose] def step (v : Nat) := infer_effects% do
  let s ← getThe Nat
  set (s + v)
  let s ← getThe Nat
  set (s - v)

infer_effects
@[expose] def loop (n : Nat) : m Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

#time_setup "AddSub.all.derive_step" derive_parametric step
#time_setup "AddSub.all.derive_loop" derive_parametric loop

#time_setup "AddSubCancel.all.fidelity"
theorem plain_loop_eq (n : Nat) : loop (m := StateM Nat) n = _root_.AddSubCancel.loop n := by
  delta loop _root_.AddSubCancel.loop
  rfl

#time_setup "AddSubCancelDeep.all.fidelity"
theorem deep_loop_eq (n : Nat) :
    loop (m := _root_.AddSubCancelDeep.M) n = _root_.AddSubCancelDeep.loop n := by
  delta loop _root_.AddSubCancelDeep.loop
  rfl

end AddSub

namespace Let

-- Keep the pure offset binding while abstracting get/set.
@[expose] def step (v : Nat) := infer_effects% do
  let s ← get
  -- Pure let binding: `let offset := ...` produces a letE node in the elaborated term
  let offset := v + 1
  set (s + offset)
  let s ← get
  set (s - offset)

infer_effects
@[expose] def loop (n : Nat) : m Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

#time_setup "LetBinding.all.derive_step" derive_parametric step
#time_setup "LetBinding.all.derive_loop" derive_parametric loop

#time_setup "LetBinding.all.fidelity"
theorem loop_eq (n : Nat) : loop (m := StateM Nat) n = _root_.LetBinding.loop n := by
  delta loop _root_.LetBinding.loop
  rfl

end Let

namespace Reader

-- Need at least one type annotation to fix the reader/state type as Nat for effect inference.
@[expose] def step := infer_effects% do
  let r : Nat ← read
  let s ← get
  set (s + r)
  let s ← get
  set (s - r)

infer_effects
@[expose] def loop (n : Nat) : m Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

#time_setup "ReaderState.all.derive_step" derive_parametric step
#time_setup "ReaderState.all.derive_loop" derive_parametric loop

#time_setup "ReaderState.all.fidelity"
theorem loop_eq (n : Nat) : loop (m := _root_.ReaderState.M) n = _root_.ReaderState.loop n := by
  delta loop _root_.ReaderState.loop
  rfl

end Reader

namespace Pure

-- Keep the two calls as separate boundaries with their original partial contracts.
@[expose] def step := infer_effects% do
  Flip.flipp true
  Flip.flipp false

infer_effects
@[expose] def loop (n : Nat) : m Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

#time_setup "PurePrecond.all.derive_step" derive_parametric step
#time_setup "PurePrecond.all.derive_loop" derive_parametric loop

#time_setup "PurePrecond.all.fidelity"
theorem loop_eq (n : Nat) : loop (m := StateM Bool) n = _root_.PurePrecond.loop n := by
  delta loop _root_.PurePrecond.loop
  rfl

end Pure

namespace ThrowSet

-- Preserve the guard and the ascending loop order from upstream.
@[expose] def step (lim : Nat) := infer_effects% do
  let s ← get
  if s > lim then
    Throw.raise "s is too large"
  set (s + 1)

infer_effects
@[expose] def loop (n : Nat) : m Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

#time_setup "GetThrowSet.all.derive_step" derive_parametric step
#time_setup "GetThrowSet.all.derive_loop" derive_parametric loop

#time_setup "GetThrowSet.all.fidelity"
theorem loop_eq (n : Nat) : loop (m := ExceptState) n = _root_.GetThrowSet.loop n := by
  delta loop _root_.GetThrowSet.loop
  rfl

end ThrowSet

namespace Dite

-- Keep the dependent guard symbolic during VC generation.
@[expose] def step (v : Nat) := infer_effects% do
  let s ← get
  if _ : s > v then
    Throw.raise "s is too large"
  set (s + v)
  let s ← get
  set (s - v)

infer_effects
@[expose] def loop (n : Nat) : m Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

#time_setup "DiteSplit.all.derive_step" derive_parametric step
#time_setup "DiteSplit.all.derive_loop" derive_parametric loop

#time_setup "DiteSplit.all.fidelity"
theorem loop_eq (n : Nat) : loop (m := ExceptState) n = _root_.DiteSplit.loop n := by
  delta loop _root_.DiteSplit.loop
  rfl

end Dite

namespace Match

-- Match the symbolic state; the zero branch still throws.
@[expose] def step := infer_effects% do
  let s ← get
  match s with
  | 0 => Throw.raise "s is zero"
  | n+1 => set n

infer_effects
@[expose] def loop (n : Nat) : m Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

#time_setup "MatchSplit.all.derive_step" derive_parametric step
#time_setup "MatchSplit.all.derive_loop" derive_parametric loop

#time_setup "MatchSplit.all.fidelity"
theorem loop_eq (n : Nat) : loop (m := ExceptState) n = _root_.MatchSplit.loop n := by
  delta loop _root_.MatchSplit.loop
  rfl

end Match

#guard_axioms AddSub.plain_loop_eq, AddSub.deep_loop_eq, Let.loop_eq, Reader.loop_eq, Pure.loop_eq, ThrowSet.loop_eq, Dite.loop_eq,
  Match.loop_eq ⊆ [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison
