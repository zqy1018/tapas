module

public import TapasTest.TestingUtils
import all Init.Internal.Order.Basic -- proofs unfold FlatOrder.mk
import Std.Tactic.BVDecide.Normalize.Prop

public section

/-!
A least-fixpoint loop in two monads, related by both a hand-written certificate and an
automatically derived one. The tests cover termination, divergence, admissibility, and the
boundaries of automatic derivation.
-/

open Tapas.Parametricity Tapas.LogicalRelation Lean.Order Lean.Order.PartialOrder

namespace TapasTest.Applications.Monad.PartialFixpoint

/-! ## Shared loop and interpretations -/

abbrev Source := ReaderT Nat Option
abbrev Target := ReaderT (Nat × Bool) Option

-- The target carries an extra configuration field. Only its first component is observed.
@[expose] def R : ComputationRelation Source Target := fun {_} x y =>
  ∀ cfg cfg', cfg = cfg'.1 → x cfg = y cfg'

theorem relation_admissible ⦃α : Type⦄ : AdmissibleRel (R (α := α)) :=
  AdmissibleRel.pi (fun _ _ _ => AdmissibleRel.eq)

theorem monadRel : Monad.Rel R :=
  Monad.Rel.ofPureBind R
    (fun _ _ _ _ => rfl)
    (by
      intro α β x y f g hxy hfg cfg cfg' hcfg
      change (x cfg).bind (fun a => f a cfg) = (y cfg').bind (fun a => g a cfg')
      rw [hxy cfg cfg' hcfg]
      cases y cfg' with
      | none => rfl
      | some a => exact hfg a cfg cfg' hcfg)

infer_effects
def body (step : Nat → m (Nat ⊕ Nat)) (recur : Nat → m Nat) (s : Nat) : m Nat := do
  match ← step s with
  | .inl s' => recur s'
  | .inr a => pure a

theorem body_monotone {m : Type → Type} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (step : Nat → m (Nat ⊕ Nat)) : monotone (body step) := by
  intro f g h s
  apply MonoBind.bind_mono_right
  intro result
  cases result with
  | inl s' => exact h s'
  | inr a => exact rel_refl

infer_effects_partial
def loop (step : Nat → m (Nat ⊕ Nat)) (s : Nat) : m Nat := do
  match ← step s with
  | .inl s' => loop step s'
  | .inr a => pure a
partial_fixpoint

-- A positive configuration counts down; zero keeps a positive counter unchanged forever.
def sourceStep (s : Nat) : Source (Nat ⊕ Nat) := fun cfg =>
  some (if s = 0 then .inr cfg else if cfg = 0 then .inl s else .inl (s - 1))

def targetStep (s : Nat) : Target (Nat ⊕ Nat) := fun cfg =>
  some (if s = 0 then .inr cfg.1 else if cfg.1 = 0 then .inl s else .inl (s - 1))

theorem steps_related (s : Nat) : R (sourceStep s) (targetStep s) := by
  rintro cfg cfg' rfl
  rfl

/-! ## Hand-written certificate -/

def CallsRelated (f : Nat → Source Nat) (g : Nat → Target Nat) : Prop :=
  ∀ s s', s = s' → R (f s) (g s')

theorem calls_admissible : AdmissibleRel CallsRelated :=
  AdmissibleRel.pi (fun _ _ _ => @relation_admissible _)

theorem bodies_related (f : Nat → Source Nat) (g : Nat → Target Nat)
    (h : CallsRelated f g) : CallsRelated (body sourceStep f) (body targetStep g) := by
  rintro s _ rfl
  apply monadRel.bind _ _ (steps_related s)
  intro result
  cases result with
  | inl s' => exact h s' s' rfl
  | inr a => exact monadRel.pure a

-- A hand-written certificate for actual `partial_fixpoint` definitions, without unfolding
-- their recursion equations or using any termination premise.
theorem loops_related : CallsRelated (loop sourceStep) (loop targetStep) := by
  delta loop
  change CallsRelated (fix (body sourceStep) (body_monotone sourceStep))
    (fix (body targetStep) (body_monotone targetStep))
  exact fix_rel (body_monotone sourceStep) (body_monotone targetStep)
    calls_admissible bodies_related

theorem exits (cfg : Nat) (hcfg : cfg ≠ 0) (s : Nat) : loop sourceStep s cfg = some cfg := by
  induction s with
  | zero => rw [loop]; rfl
  | succ s ih =>
    rw [loop]
    simpa [sourceStep, hcfg, bind, ReaderT.bind, pure, ReaderT.pure] using ih

theorem diverges (s : Nat) (hs : s ≠ 0) : loop sourceStep s 0 = none := by
  have h : ∀ s, s ≠ 0 → loop sourceStep s 0 = none := by
    apply loop.fixpoint_induct (step := sourceStep)
      (motive := fun recur => ∀ s, s ≠ 0 → recur s 0 = none)
    · apply admissible_pi
      intro s
      apply admissible_pi
      intro hs
      exact admissible_apply (fun _ (f : Source Nat) => f 0 = none) s
        (admissible_apply (fun _ (x : Option Nat) => x = none) 0
          (admissible_flatOrder _ rfl))
    · intro recur ih s hs
      simpa [sourceStep, hs, bind, ReaderT.bind, pure, ReaderT.pure] using ih s hs
  exact h s hs

theorem target_exits (cfg : Nat) (hcfg : cfg ≠ 0) (flag : Bool) (s : Nat) :
    loop targetStep s (cfg, flag) = some cfg :=
  (loops_related s s rfl cfg (cfg, flag) rfl).symm.trans (exits cfg hcfg s)

theorem target_diverges (flag : Bool) (s : Nat) (hs : s ≠ 0) :
    loop targetStep s (0, flag) = none :=
  (loops_related s s rfl 0 (0, flag) rfl).symm.trans (diverges s hs)

-- Only terminating cases are executed; divergence is checked by proofs above.
#guard loop sourceStep 5 3 == some 3
#guard loop targetStep 5 (3, true) == some 3
#guard loop sourceStep 0 0 == some 0
#guard loop targetStep 0 (0, false) == some 0

/-! ## Admissibility is necessary -/

-- Related successful computations form a Monad relation, but exclude related bottoms.
def Successful : ComputationRelation Option Option := fun {_} x y =>
  ∃ a, x = some a ∧ y = some a

theorem successful_monadRel : Monad.Rel Successful :=
  Monad.Rel.ofPureBind Successful
    (fun a => ⟨a, rfl, rfl⟩)
    (by
      rintro α β x y f g ⟨a, rfl, rfl⟩ h
      exact h a)

private theorem option_bot {α : Type} : (⊥ : Option α) = none :=
  rel_antisymm (bot_le _) FlatOrder.rel.bot

theorem successful_not_admissible : ¬ AdmissibleRel (Successful (α := Nat)) := by
  intro h
  have hb := h.bot
  rw [option_bot] at hb
  rcases hb with ⟨a, ha, _⟩
  cases ha

-- Even when the functionals preserve Successful, their least fixpoints are not related.
theorem successful_not_preserved_by_fix :
    (∀ x y : Option Nat, Successful x y → Successful (id x) (id y)) ∧
      ¬ Successful (fix id monotone_id : Option Nat) (fix id monotone_id : Option Nat) := by
  refine ⟨fun _ _ h => h, ?_⟩
  have hfix : (fix id monotone_id : Option Nat) = none := by
    apply fix_induct monotone_id (fun x => x = none)
    · exact admissible_flatOrder _ rfl
    · exact fun _ h => h
  rw [hfix]
  rintro ⟨a, ha, _⟩
  cases ha

#guard_axioms fix_rel, AdmissibleRel.pi, loops_related, exits, diverges,
  target_exits, target_diverges, successful_monadRel, successful_not_admissible,
  successful_not_preserved_by_fix ⊆ [propext, Classical.choice, Quot.sound]

-- The certificate goes through the least-fixpoint principle rather than a recursion equation.
#guard_uses loops_related ⊇ [fix_rel]

/-! ## Automatic derivation -/

derive_parametric loop

theorem generated_loops_related : CallsRelated (loop sourceStep) (loop targetStep) := by
  intro s _ rfl
  exact loop.parametric R monadRel sourceStep targetStep steps_related s relation_admissible

-- A caller reuses the registered rule and exposes the same admissibility premise.
infer_effects
def run (step : Nat → m (Nat ⊕ Nat)) (s : Nat) : m Nat := do
  let a ← loop step s
  pure (a + 1)

derive_parametric run

example (s : Nat) : R (run sourceStep s) (run targetStep s) :=
  run.parametric R monadRel sourceStep targetStep steps_related s relation_admissible

theorem generated_target_exits (cfg : Nat) (hcfg : cfg ≠ 0) (flag : Bool) (s : Nat) :
    loop targetStep s (cfg, flag) = some cfg :=
  (generated_loops_related s s rfl cfg (cfg, flag) rfl).symm.trans (exits cfg hcfg s)

theorem generated_target_diverges (flag : Bool) (s : Nat) (hs : s ≠ 0) :
    loop targetStep s (0, flag) = none :=
  (generated_loops_related s s rfl 0 (0, flag) rfl).symm.trans (diverges s hs)


-- Two varying arguments surround a fixed parameter, so Lean emits a wrapper
-- that reorders them. The computation universe may differ between interpretations.
infer_effects_partial
def accumulate {α : Type u}
    (k : Nat) (step : Nat → m (Option α)) (acc : List α) : m (List α) := do
  match ← step k with
  | none => pure acc
  | some a =>
    let next : m (List α) := pure (a :: acc)
    let xs ← next
    accumulate (k + 1) step xs
partial_fixpoint

derive_parametric accumulate (repr := m)

example {α : Type u} {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] [∀ β, CCPO (m β)] [∀ β, CCPO (n β)]
    [MonoBind m] [MonoBind n] (R : ComputationRelation m n) (hm : Monad.Rel R)
    (hadm : ∀ ⦃β⦄, AdmissibleRel (R (α := β)))
    (k : Nat) (step : Nat → m (Option α)) (step' : Nat → n (Option α))
    (hstep : ∀ k, R (step k) (step' k)) (acc : List α) :
    R (accumulate k step acc) (accumulate k step' acc) :=
  accumulate.parametric R hm k step step' hstep acc hadm

-- Merely carrying order parameters does not add an unused admissibility premise.
def immediate {m : Type → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (s : Nat) : m Nat := pure s

derive_parametric immediate

example {m : Type → Type v} {n : Type → Type w} [Monad m] [Monad n]
    [∀ α, CCPO (m α)] [∀ α, CCPO (n α)] [MonoBind m] [MonoBind n]
    (R : ComputationRelation m n) (hm : Monad.Rel R) (s : Nat) :
    R (immediate (m := m) s) (immediate (m := n) s) :=
  immediate.parametric R hm s

-- No varying arguments: the least fixpoint lives directly in the computation CCPO.
infer_effects_partial
def spin : m Nat := spin
partial_fixpoint

derive_parametric spin

example {m n : Type → Type} [Monad m] [Monad n]
    [∀ α, CCPO (m α)] [∀ α, CCPO (n α)] [MonoBind m] [MonoBind n]
    (R : ComputationRelation m n) (hm : Monad.Rel R)
    (hadm : ∀ ⦃α⦄, AdmissibleRel (R (α := α))) : R (spin (m := m)) (spin (m := n)) :=
  spin.parametric R hm hadm

example : True := by
  fail_if_success
    have : Successful (spin (m := Option)) (spin (m := Option)) :=
      spin.parametric _ successful_monadRel
  trivial

theorem spin_not_successful :
    ¬ Successful (spin (m := Option)) (spin (m := Option)) := by
  delta spin
  exact successful_not_preserved_by_fix.2

/-! ## Unsupported definitions -/

infer_effects_partial
def changing (x : m Nat) : m Nat := do
  let a ← x
  changing (pure (a + 1))
partial_fixpoint

/-- error: parametricity: partial_fixpoint currently requires shared, representation-independent recursive arguments -/
#guard_msgs in
derive_parametric changing

def onlyNat {m : Type → Type} [CCPO (m Nat)] : m Nat := onlyNat
partial_fixpoint

/-- error: parametricity: partial_fixpoint requires CCPO instances for every result type in both interpretations -/
#guard_msgs in
derive_parametric onlyNat

infer_effects_partial
mutual
def leftLoop (s : Nat) : m Nat := if s = 0 then pure 0 else rightLoop (s + 1)
partial_fixpoint
def rightLoop (s : Nat) : m Nat := leftLoop (s + 1)
partial_fixpoint
end

/-- error: parametricity: only single-function partial_fixpoint definitions are supported; register a hand-written translation for TapasTest.Applications.Monad.PartialFixpoint.leftLoop -/
#guard_msgs in
derive_parametric leftLoop

infer_effects
def unregistered : m Nat := pure 0

infer_effects_partial
def broken (s : Nat) : m Nat := if s = 0 then unregistered else broken (s + 1)
partial_fixpoint

/-- error: parametricity: no applicable translation for TapasTest.Applications.Monad.PartialFixpoint.unregistered; use `derive_parametric TapasTest.Applications.Monad.PartialFixpoint.unregistered` or `attribute [parametric] theoremName` -/
#guard_msgs in
derive_parametric broken

#guard_no_parametric changing, onlyNat, leftLoop, rightLoop, broken

-- An order parameter must not be mistaken for an effect capability.
#guard_no_interface_rel CCPO, MonoBind

#guard_uses type loop.parametric, accumulate.parametric, spin.parametric ⊇ [AdmissibleRel]
#guard_uses loop.parametric, accumulate.parametric, spin.parametric ⊇ [fix_rel]

-- A caller reuses the registered partial-fixpoint translation instead of re-deriving it.
#guard_uses run.parametric ⊇ [loop.parametric]

#guard_axioms loop.parametric, run.parametric, generated_loops_related,
  generated_target_exits, generated_target_diverges, accumulate.parametric,
  immediate.parametric, spin.parametric, spin_not_successful ⊆
  [propext, Classical.choice, Quot.sound]

end TapasTest.Applications.Monad.PartialFixpoint
