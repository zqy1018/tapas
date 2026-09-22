module

import TapasTest.TestingUtils
import TapasTest.Applications.Monad.Freer.Basic
meta import TapasTest.Applications.Monad.Freer.Basic -- shake: keep (required by #guard/#eval)

/-!
A state capability example and regression checks for freer / tagless-final conversion.
-/

namespace TapasTest.Applications.Monad.Freer.StateAdapter

open Tapas.Parametricity Tapas.LogicalRelation TapasTest.Applications.Monad.Freer.Basic

universe u w w'

-- One capability adapter. Keep modifyGet as an independent operation, since
-- MonadStateOf does not require its implementation to be derived from get/set.
inductive StateOp (σ : Type u) : Type u → Type (u + 1) where
  | get : StateOp σ σ
  | set : σ → StateOp σ PUnit
  | modifyGet {α : Type u} : (σ → α × σ) → StateOp σ α

instance {σ : Type u} : MonadStateOf σ (Freer (StateOp σ)) where
  get := monadLift (m := StateOp σ) .get
  set s := monadLift (m := StateOp σ) (.set s)
  modifyGet f := monadLift (m := StateOp σ) (.modifyGet f)

def stateHandler {σ : Type u} {m : Type u → Type w} [MonadStateOf σ m] :
    (α : Type u) → StateOp σ α → m α
  | _, .get => getThe σ
  | _, .set s => set s
  | _, .modifyGet f => MonadStateOf.modifyGet f

-- The original program uses ordinary do notation and inferred capabilities.
def tick := infer_effects% do
  let old ← get
  set (old + 1)
  pure old

def tickFinal : Final.{0, 1, w} (StateOp Nat) Nat := fun {m} _ h =>
  letI : MonadStateOf Nat m := {
    get := h _ .get
    set s := h _ (.set s)
    modifyGet f := h _ (.modifyGet f)
  }
  tick

def tickFreer : Freer (StateOp Nat) Nat := toFreer tickFinal

-- The conversion really produces requests, including the data-dependent set.
example : tickFreer = .impure .get (fun old =>
    .impure (.set (old + 1)) (fun _ => .pure old)) := rfl

derive_parametric tick

-- The generated theorem supplies a certificate for arbitrary related handlers,
-- independently of Freer or any particular concrete interpretation.
theorem tickFinal_rel : Final.Rel tickFinal.{w} tickFinal.{w'} := by
  intro m n R lm rn hm h k hop
  dsimp only [tickFinal]
  refine tick.parametric (m := m) (m' := n) (effect0 := (_)) (effect0' := (_)) R hm ?_
  exact MonadStateOf.Rel.mk (left := (_)) (right := (_)) R
    (hop _ .get) (fun s => hop _ (.set s)) (fun f => hop _ (.modifyGet f))

theorem tick_roundtrip {m : Type → Type w} [Monad m] [LawfulMonad m] [MonadStateOf Nat m] :
    toFinal tickFreer (stateHandler (m := m)) = tick (m := m) :=
  toFinal_toFreer_rel tickFinal tickFinal tickFinal_rel (stateHandler (m := m))

-- The freer computation lives in Type 1; these interpreters return values in Type.
/-- info: (5, 6) -/
#guard_msgs in
#eval tick (m := StateM Nat) 5

/-- info: (5, 6) -/
#guard_msgs in
#eval toFinal tickFreer (stateHandler (m := StateM Nat)) 5

/-- info: some (5, 6) -/
#guard_msgs in
#eval toFinal tickFreer (stateHandler (m := StateT Nat Option)) 5

#guard_axioms toFinal_rel ⊆ []
#guard_axioms toFreer_toFinal ⊆ [Quot.sound]
#guard_axioms toFinal_toFreer_rel, toFinal_toFreer, tick_roundtrip ⊆ [propext, Quot.sound]

end TapasTest.Applications.Monad.Freer.StateAdapter
