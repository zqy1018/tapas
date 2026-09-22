module

import TapasTest.TestingUtils

/-!
Hand-written translations for recursive helpers, registered with `@[parametric]`
and reused by generated theorems.
-/

open Tapas.Parametricity Tapas.LogicalRelation

namespace TapasTest.Applications.Monad.ControlFlow.RecursionManual

def tick := infer_effects% do
  let n ← get
  set (n + 1)
  pure n
derive_parametric tick

/-! ## Structural recursion -/

infer_effects
def countdown : Nat → m Nat
  | 0 => pure 0
  | k + 1 => do set k; let r ← countdown k; pure (r + 1)

@[parametric] theorem countdown_translation {m : Type → Type v} {n : Type → Type w}
    [Monad m] [Monad n] [MonadStateOf Nat m] [MonadStateOf Nat n]
    (R : ComputationRelation m n) (hm : Monad.Rel R) (hs : MonadStateOf.Rel (σ := Nat) R)
    (k : Nat) : R (countdown (m := m) k) (countdown (m := n) k) := by
  induction k with
  | zero => exact hm.pure 0
  | succ k ih =>
    exact hm.bind _ _ (hs.set k) _ _ fun _ => hm.bind _ _ ih _ _ fun r => hm.pure (r + 1)

-- Reuses `countdown_translation`.
def caller := infer_effects% do
  let a ← countdown 5
  let b ← tick
  pure (a + b)
derive_parametric caller

/-! ## `for` loops over lists -/

@[parametric] theorem forIn'_translation {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] (R : ComputationRelation m n) (hm : Monad.Rel R)
    {α : Type} {β : Type u} (xs : List α) (init : β)
    (f : (a : α) → a ∈ xs → β → m (ForInStep β)) (g : (a : α) → a ∈ xs → β → n (ForInStep β))
    (hfg : ∀ a h b, R (f a h b) (g a h b)) :
    R (List.forIn' xs init f) (List.forIn' xs init g) := by
  unfold List.forIn'
  suffices ∀ (ys : List α) (b : β) (h : ∃ bs, bs ++ ys = xs),
      R (List.forIn'.loop xs f ys b h) (List.forIn'.loop xs g ys b h) from this xs init _
  intro ys
  induction ys with
  | nil => intro b h; exact hm.pure b
  | cons y ys ih =>
    intro b h
    simp only [List.forIn'.loop]
    exact hm.bind _ _ (hfg _ _ _) _ _ fun
      | .done b => hm.pure b
      | .yield b => ih b _

-- Reuses `forIn'_translation`.
def forList (xs : List Nat) := infer_effects% do
  for x in xs do
    set x
  get
derive_parametric forList

-- An `if` inside the loop body.
def forListIf (xs : List Nat) := infer_effects% do
  for x in xs do
    if x > 3 then set x
  get
derive_parametric forListIf

#guard_parametric caller, forList, forListIf

-- Reusing a hand-written translation adds nothing to what that translation itself assumes.
#guard_axioms caller.parametric ⊆ []
#guard_axioms forList.parametric ⊆ [propext]

end TapasTest.Applications.Monad.ControlFlow.RecursionManual
