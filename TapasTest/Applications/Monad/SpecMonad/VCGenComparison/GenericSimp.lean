module

public import TapasTest.Applications.Monad.SpecMonad.Normalizer
public meta import Lean.Elab.Tactic.Meta
public meta import Lean.Meta.Sym.DSimp

public meta section

/-!
Generic definitional simplifiers in place of our [normalizer](../Normalizer.lean). They unfold the
constants the normalizer would unfold, but traverse and unfold by their own means:

* `dsimp`: Lean's `dsimp only [...]`, listing those constants.
* `symDsimp`: `Sym.dsimp` with Sym's own beta, zeta, and match reduction.

  NOTE: On Lean 4.35, Sym's
  `dsimp [...]` cannot unfold global definitions, and `Sym.dsimp` does not visit an application's
  head, so two dsimprocs add unfolding and a `let` at the head. Sym's `proj` dsimproc would also
  turn `+` into `Nat.add`, so only the listed projections are reduced.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison.GenericSimp

open Lean Meta Elab Sym

/-- The constants the normalizer would unfold in `e`, which `dsimp only [...]` has to list: effectful
constants reachable through effectful constants and instances, and the specification monad's
projections. -/
def unfoldSet (specMonad : Name) (e : Expr) : MetaM (Array Name) := do
  let mut todo := e.getUsedConstants
  let mut seen : NameSet := {}
  let mut found := #[]
  repeat
    let some name := todo.back? | break
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let effectful ← Normalizer.effectful specMonad name
    let ofSpecMonad := name.getPrefix == specMonad
    let info ← getConstInfo name
    if effectful && info.hasValue || ofSpecMonad && (← isProjectionFn name) then
      found := found.push name
    -- NOTE: `isInstance` returns false for a scoped instance when its scope is inactive, even
    -- if the expression already refers to it. The `instance` command also assigns
    -- `.instanceReducible`, and that status remains available outside the scope.
    -- Check it too so we still traverse the definition's dependencies; this also
    -- admits non-instance definitions carrying the same status.
    let inst := (← isInstance name) || (← getReducibilityStatus name) == .instanceReducible
    if effectful || inst || ofSpecMonad then
      if let some value := info.value? then
        todo := todo ++ value.getUsedConstants
  return found

/-- Lean's `dsimp only [names]`. -/
def dsimp (names : Array Name) (goal : MVarId) : MetaM MVarId := do
  let names ← names.mapM fun name => `(Parser.Tactic.simpLemma| $(mkCIdent name):term)
  let ([goal], _) ← Lean.Elab.runTactic goal (← `(tactic| dsimp only [$names,*])).raw {} {}
    | throwError "dsimp closed the goal"
  return goal

/-- `Sym.dsimp`, unfolding `names` as Sym's `proj` dsimproc does: the whole application, then
sharing. -/
def symDsimp (names : Array Name) (goal : MVarId) : MetaM MVarId := SymM.run do
  let goal ← preprocessMVar goal
  let names := NameSet.ofArray names
  let unfold : DSimp.DSimproc := fun e => do
    let .const name _ := e.getAppFn | return .rfl
    unless names.contains name do return .rfl
    if ← isProjectionFn name then return ← DSimp.dsimpProj e
    let some e' ← unfoldDefinition? e | return .rfl
    return .step (← shareCommon e')
  -- `zeta` reduces a bare `let`, but not one applied to arguments.
  let zetaHead : DSimp.DSimproc := fun e => do
    unless e.isApp && e.getAppFn.isLet do return .rfl
    let .step f _ ← DSimp.zeta e.getAppFn | return .rfl
    return .step (← shareCommon (mkAppN f e.getAppArgs))
  let pre := DSimp.beta >> DSimp.zeta >> zetaHead >> DSimp.dsimpMatch >> unfold
  goal.withContext do
    -- `dsimp` has no step limit.
    goal.replaceTargetDefEq (← Sym.dsimp (← goal.getType) { pre } { maxSteps := 1_000_000_000 })

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison.GenericSimp
