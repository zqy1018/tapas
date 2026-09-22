module

public import Tapas

open Tapas.LogicalRelation

namespace TapasTest.LogicalRelation.BaseRelationAliasing

/-!
Argument inference and metavariable isolation for `aliasBaseRelation`.
The derivation examples are in `LogicalRelation/SharedIndex.lean`.
-/

-- Apply the matcher to a written type so the examples can check its result directly.
local elab "aliased_relation% " type:term : term => do
  return ← aliasBaseRelation (← Lean.Elab.Term.elabType type)

abbrev CarrierRelation (A : Sort u) (B : Sort v) := A → B → Prop
abbrev ReversedRelation (B : Sort v) (A : Sort u) := A → B → Prop
abbrev NatRelation := Nat → Nat → Prop
abbrev WrongRelation (A B : Type) := A → B → Bool
abbrev UndeterminedRelation (_unused : Nat) (A B : Type) := A → B → Prop

section
attribute [local base_relation_alias] ReversedRelation

-- The order of an alias's parameters need not match the relation's endpoints.
example : aliased_relation% (Nat → Bool → Prop) := by
  guard_target =ₛ ReversedRelation Bool Nat
  exact fun _ _ => True
end

section
attribute [local base_relation_alias] NatRelation WrongRelation UndeterminedRelation

-- A constant alias can match without taking any arguments.
example : aliased_relation% (Nat → Nat → Prop) := by
  guard_target =ₛ NatRelation
  exact fun _ _ => True

-- Reject a wrong endpoint, wrong codomain, and an undetermined parameter.
example : aliased_relation% (Nat → Bool → Prop) := by
  guard_target =ₛ (Nat → Bool → Prop)
  exact fun _ _ => True

attribute [local base_relation_alias 500] CarrierRelation

-- Failed candidates must not prevent a lower-priority alias from succeeding.
example : aliased_relation% (Nat → Bool → Prop) := by
  guard_target =ₛ CarrierRelation Nat Bool
  exact fun _ _ => True
end

section
attribute [local base_relation_alias] NatRelation

-- NatRelation must not specialize unknown caller-owned types to Nat.
open Lean Meta in
run_meta do
  let a ← mkFreshExprMVar (mkSort (.succ .zero))
  let b ← mkFreshExprMVar (mkSort (.succ .zero))
  let relation ← mkArrowN #[a, b] (mkSort .zero)
  unless (← aliasBaseRelation relation) == relation &&
      !(← a.mvarId!.isAssigned) && !(← b.mvarId!.isAssigned) do
    throwError "a naming preference assigned the caller's type metavariables"
end

section
attribute [local base_relation_alias] CarrierRelation

-- An existing universe metavariable may remain in the alias without being fixed.
open Lean Meta in
run_meta do
  let u ← mkFreshLevelMVar
  withLocalDeclD `A (mkSort (.succ u)) fun a => do
    let relation ← mkArrowN #[a, a] (mkSort .zero)
    let named ← aliasBaseRelation relation
    let expected := mkApp2 (mkConst ``CarrierRelation [.succ u, .succ u]) a a
    unless named == expected && (← instantiateLevelMVars u) == u do
      throwError "a naming preference lost or assigned the caller's universe metavariable"
end

end TapasTest.LogicalRelation.BaseRelationAliasing
