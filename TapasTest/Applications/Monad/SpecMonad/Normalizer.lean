module

public import Lean
public meta import Lean.Meta.Sym.DSimp

public meta section

/-!
Normalize a program in a specification interpretation, leaving its data operations intact.
This should be thought of as something like `dsimp` but with a very narrow application.

`dsimp`, with an empty simp set, only traverses: before it descends into a term, `reduceHead`
reduces the term's head until it is stuck. It repeats `whnfCore`, unfolds *effectful* constants
(whose type ends in `m α` for a bound `m`, or in the named specification representation: programs,
operations, and class methods, but not data such as `+` or `ite`), resolves class methods to the
instance's field, and, for a structure such as `PredTrans`, reduces `x` in `x.apply …` to
a constructor and takes its field. Symbolic conditionals remain for the caller to split. The
result is definitionally equal to the goal, and the kernel checks it again. `normalizeSym` runs
the same `reduceHead` in `Sym.dsimp`'s traversal instead.

A non-monadic interpretation can return a bare type `R`. Once its representation parameters
are supplied, an operation returning the named specification type is also unfolded.

Why:
* Head first: continuations receive their values before they are visited, so each program node
  is unfolded once and the pass stays linear.
* Effectful constants only: the solver sees the program's data as written, and no list of
  program names is needed.
* `unfoldPrefix?` passes only the definition's own arguments: smart unfolding would traverse the
  continuation and the growing state at every step, which made the pass quadratic.
-/

namespace TapasTest.Applications.Monad.SpecMonad.Normalizer

open Lean Meta Elab Tactic

/-- Recognize program operations by their result type, rather than by a list of program names. -/
def effectful (specMonad name : Name) : MetaM Bool := do
  -- Preserve `match` functions so the solver can use their equations and splitters.
  if ← isMatcher name then return false
  let body := (← getConstInfo name).type.getForallBody
  unless body.isApp do return false
  match body.getAppFn' with
  | .bvar _ => return true
  | .const name _ => return name == specMonad
  | _ => return false

-- Smart unfolding must not traverse extra arguments: the continuation and the growing state.
private def unfoldPrefix? (specMonad name : Name) (f : Expr) (args : Array Expr) : MetaM (Option Expr) := do
  let fType ← inferType f
  let arity := min fType.getNumHeadForalls args.size
  let ownArgs := if arity == args.size then args else args.take arity
  let app := mkAppN f ownArgs
  unless ← effectful specMonad name do
    if (← isMatcher name) || app.isIte || app.isDIte then return none
    -- Recognize a bare representation after instantiation, without admitting arbitrary
    -- data operations whose result is a type variable in their declaration.
    let resultType ← instantiateForall fType ownArgs
    -- NOTE: A definitionally equal type can fail this syntactic name check if the
    -- specification alias has already unfolded to a function type. This may stop
    -- normalization early.
    unless resultType.isConstOf specMonad do return none
  let some body ← unfoldDefinition? app | return none
  return some (if arity == args.size then body else mkAppN body (args.drop arity))

-- Reduce the head before descending, including projections of the chosen operation instances.
private partial def reduceHead (specMonad : Name) (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  let (fn, args) := e.withApp fun f args => (f, args)
  match fn with
  | .const name _ =>
    -- A structure specification monad's own projections and constructor, e.g. `PredTrans.apply`.
    if name.getPrefix == specMonad then
      -- In `x.apply post …`, reduce the computation `x` head-first, then take its field.
      if let some info ← getProjectionFnInfo? name then
        if h : info.numParams < args.size then
          let x ← reduceHead specMonad args[info.numParams]
          if let some field ← projectCore? x info.i then
            let rest := args.drop (info.numParams + 1)
            return ← reduceHead specMonad (mkAppN field rest)
        return e
      if (← getConstInfo name).isCtor then return e
    if let some e' ← unfoldPrefix? specMonad name fn args then return ← reduceHead specMonad e'
    return e
  | .proj _ i inst =>
    let inst ← withTransparency .instances <| whnf inst
    if let some field ← projectCore? inst i then
      return ← reduceHead specMonad (mkAppN field args)
    return e
  | _ => return e

/-- Unfold computations in the named specification interpretation in an expression. -/
def normalizeExpr (specMonad : Name) (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext {} {} (← getSimpCongrTheorems)
  let methods : Simp.Methods := { dpre := fun e => do
    -- dsimp runs at reducible transparency; program definitions need default transparency.
    let e' ← withDefault <| reduceHead specMonad e
    return .continue e' }
  return (← Simp.dsimpMain e ctx (methods := methods)).1

/-- `normalizeExpr` with `Sym.dsimp`'s traversal. -/
def normalizeExprSym (specMonad : Name) (e : Expr) : MetaM Expr := Sym.SymM.run do
  let pre : Sym.DSimp.DSimproc := fun e => do
    let e' ← withDefault <| reduceHead specMonad e
    return if Sym.isSameExpr e e' then .rfl else .step e'
  -- `dsimp` has no step limit.
  Sym.dsimp e { pre } { maxSteps := 1_000_000_000 }

/-- Unfold computations in the named specification interpretation in the goal. -/
def normalize (specMonad : Name) (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← normalizeExpr specMonad (← goal.getType)
  goal.replaceTargetDefEq target

/-- `normalize` with `Sym.dsimp`'s traversal. -/
def normalizeSym (specMonad : Name) (goal : MVarId) : MetaM MVarId := goal.withContext do
  goal.replaceTargetDefEq (← normalizeExprSym specMonad (← goal.getType))

/-- Unfold the program's specification interpretation, preserving data expressions. -/
scoped elab "normalize_spec " specMonad:ident : tactic => do
  let name ← realizeGlobalConstNoOverloadWithInfo specMonad
  liftMetaTactic fun goal => return [← normalize name goal]

end TapasTest.Applications.Monad.SpecMonad.Normalizer
