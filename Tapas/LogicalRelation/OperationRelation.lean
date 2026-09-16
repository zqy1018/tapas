import Tapas.LogicalRelation.Basic

/-!
The relation between the two interpretations of an operation, computed from the
operation's type by `operationRelation`.

## Algorithm

This is the relational interpretation of the operation types (as in Reynolds'
parametricity), restricted to a first-order fragment. The monad is interpreted
by `R`, and every type that does not mention the monad by equality.
`operationRelation` computes the relation for the pair `(left.op, right.op)` by
recursion on the operation type `T`:

* `T = m α`: the result is `R left right`. The type `α` must not mention the
  monad, so both sides produce a value of the same type.
* `T = (x : A) → B` where `A` does not mention the monad: equality on `A` means
  both sides receive the same argument, so one variable `x` is introduced and
  the recursion continues on `left x` and `right x`.
* `T = A → B` where `A` mentions the monad (e.g. `m α` or `ε → m α`): two
  variables `x`, `x'` and a premise given by the relation for `A` on them are
  introduced, and the recursion continues on `left x` and `right x'`. The premise
  is itself computed by `operationRelation`, so higher-order handlers get
  pointwise premises such as `∀ e, R (h e) (h' e)`. `B` must not depend on `x`.
* `T = D qs` where `D` is a capability with a generated relation and `m` is
  in its monad position: the result is `D.Rel R left right`. This lets fields that
  are dictionaries (or families of dictionaries) reuse earlier derivations.
* `T = F as` where `T` mentions the monad and a relator is registered for the
  type constructor `F`: the result is the relator applied to `left` and `right`.
  Each argument the relator lifts gets the relation computed by this recursion,
  so `Option (List (m α))` gives `Option.Rel (ListRel R)`.
* `T` does not mention the monad (and is not a sort): the result is
  `left = right`.

Anything else is rejected with an error:

* A type constructor applied to a type that mentions the monad, such as
  `Array (m α)`, when no relator is registered for it. This is not a limit of
  parametricity: the parametricity translation gives a relator for every
  inductive type. Relators are not generated yet, only looked up.
* A computation whose value type mentions the monad, such as `m (m α)`. Its two
  sides have different value types (`m α` and `n α`), but `ComputationRelation`
  only relates computations with the same value type.
* A dependent computation argument, and a field that is itself a type.
-/

namespace Tapas.LogicalRelation

open Lean Meta

/-- A monad of the translated type, its second interpretation, and their computation relation.
A type such as a tagless final program binds its own monad, so a translation carries one of
these per monad in scope rather than a single fixed triple. -/
structure RelatedMonad where
  /-- The monad of the left interpretation. -/
  source : Expr
  /-- The monad of the right interpretation. -/
  target : Expr
  /-- The `ComputationRelation` between them. -/
  relation : Expr
  deriving Inhabited

/-- Recognize `Type u → Type v`, unfolding an outer alias if necessary. Unlike
`Meta.isMonad?`, this checks the type without requiring a `Monad` instance. -/
def typeConstructorUniverses? (type : Expr) : MetaM (Option (Level × Level)) := do
  let type := type.cleanupAnnotations
  let type ← if type.isForall then pure type else whnf type
  let .forallE _ (.sort (.succ u)) (.sort (.succ v)) _ := type | return none
  return some (u, v)

/-- `type` mentions no interpretation of a monad in scope. -/
private def independent (monads : Array RelatedMonad) (type : Expr) : Bool :=
  monads.all fun pair => !pair.source.occurs type && !pair.target.occurs type

/-- Does `type` quantify over a monad? Such a type is interpreted by a relation rather than by
equality, so an argument of this type is related instead of being shared, even when both
interpretations mention no monad in scope. A type constructor argument (`Type u → Type v`
itself) does not quantify over a monad and stays shared. -/
private partial def bindsMonad (type : Expr) : MetaM Bool := do
  let .forallE name dom body bi ← whnf type | return false
  if (← typeConstructorUniverses? dom).isSome then return true
  if ← bindsMonad dom then return true
  withLocalDecl name bi dom fun x => bindsMonad (body.instantiate1 x)

/-- The universe parameters that both interpretations must share.

A type free of the monads contributes all of its universes. A capability or computation
applied to a monad contributes only the universes of the arguments that are free of the
monads, as for an exception type `ULift.{v} Unit` in a monad whose output also has universe
`v`. Its remaining arguments are duplicated along with the monad rather than shared, and their
universes include the computation universe, which the second interpretation may change: the
class constant's own universe arguments, a computation type such as `m α`, and a dictionary
derived from the monad, such as the `Monad.toBind m inst` argument of `MonoBind m`. A binder
of monad kind binds a further monad, contributing only its value universe. -/
partial def sharedComputationLevels (monads : Array Expr) (type : Expr)
    (s : CollectLevelParams.State) : MetaM CollectLevelParams.State := do
  match ← whnf type with
  | .forallE name dom body bi =>
    if let some (u, _) ← typeConstructorUniverses? dom then
      withLocalDecl name bi dom fun x =>
        sharedComputationLevels (monads.push x) (body.instantiate1 x)
          (collectLevelParams s (mkSort (.succ u)))
    else
      withLocalDecl name bi dom fun x => do
        sharedComputationLevels monads (body.instantiate1 x) (← sharedComputationLevels monads dom s)
  | type =>
    if monads.any (·.occurs type) &&
        (monads.contains type.getAppFn || type.getAppFn.constName?.any (isClass (← getEnv))) then
      return type.getAppArgs.foldl (fun s arg =>
        if monads.any (·.occurs arg) then s else collectLevelParams s arg) s
    return collectLevelParams s type

/-- Apply a registered relator to `left : F as` and `right : F bs`. Shared arguments must
agree and must not mention the monads; `relationOf a b` computes the relation for a lifted
argument with types `a` and `b`. -/
private def applyRelator (monads : Array RelatedMonad) (info : EffectRelatorInfo)
    (leftType rightType left right : Expr)
    (relationOf : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let args := leftType.getAppArgs
  let args' := rightType.getAppArgs
  unless rightType.getAppFn.constName? == some info.typeConstructor &&
      args.size == info.relationParams.size && args'.size == args.size do
    throwError "effect relation: relator {info.relator} does not apply to\n{leftType}\nand\n{rightType}"
  let mut relatorArgs := Array.replicate info.numParams none
  for i in [:args.size] do
    match info.relationParams[i]! with
    | none =>
      unless independent monads args[i]! && independent monads args'[i]! &&
          (← isDefEq args[i]! args'[i]!) do
        throwError "effect relation: relator {info.relator} shares an argument, which must be independent of the monad and equal on both sides:\n{args[i]!}\nand\n{args'[i]!}"
    | some j => relatorArgs := relatorArgs.set! j (some (← relationOf args[i]! args'[i]!))
  relatorArgs := relatorArgs.set! (info.numParams - 2) (some left)
  relatorArgs := relatorArgs.set! (info.numParams - 1) (some right)
  try
    mkAppOptM info.relator relatorArgs
  catch ex =>
    throwError "effect relation: cannot apply relator {info.relator} to\n{leftType}\nand\n{rightType}\n{ex.toMessageData}\nnote: the two sides may live in different universes, which the relator must allow"

/-- Preserve exposed binders and computation types; reduce only other heads to reveal aliases.

Types that already show a binder, a sort or a computation `m α` are returned
unchanged, and so are applications of a type constructor with a registered relator,
which would otherwise be unfolded if it is a definition. Any other type is put in
weak head normal form, so that an alias such as `abbrev Handler m α := ε → m α`
reveals the binder behind it and `operationRelation` can recognize it. -/
private def operationType (monads : Array RelatedMonad) (e : Expr) : MetaM Expr := do
  let type := (← inferType e).cleanupAnnotations
  if type.isForall || type.isSort ||
      monads.any (fun pair => type.getAppFn == pair.source || type.getAppFn == pair.target) then
    return type
  if let some name := type.getAppFn.constName? then
    if (getEffectRelator? (← getEnv) name).isSome then return type
  whnf type

/--
Lift a computation relation through operation types. Ordinary arguments are
shared; computation arguments and higher-order handlers get relational premises.
No relation is invented: a container of computations needs a registered relator,
and associated types are rejected.

`left` and `right` are the two interpretations of the same operation or program,
related at the type of `left`. `monads` holds the monads in scope with their
second interpretations and relations; a type that binds its own monad extends it.
The result is a `Prop`. The cases are checked in this order:

1. `m α` / `m' α` for a monad in scope: `R α left right`.
2. `∀ x : A, B` and `∀ x : A', B'` with `A`, `A'` of monad kind: a monad bound by
   the type itself, so `∀ {m m'} (R : ComputationRelation m m'), ⟦B⟧ (left m) (right m')`
   with `m`, `m'`, `R` added to the monads in scope.
3. `∀ x : A, B` with `A` free of the monads: `∀ x, ⟦B⟧ (left x) (right x)`.
4. `∀ x : A[m], B` with `A` mentioning a monad:
   `∀ x x', ⟦A⟧ x x' → ⟦B⟧ (left x) (right x')`.
5. `D … m …` for a registered capability `D`: `D.Rel … R left right`.
6. `F as` mentioning the monads, for a type constructor `F` with a registered
   relator: the relator applied to `fun x x' => ⟦Aᵢ⟧ x x'` for each lifted
   argument `Aᵢ`, then to `left` and `right`.
7. A type free of the monads: `left = right`.

Here `⟦T⟧ a b` is the recursive call. All other shapes throw an error.
-/
partial def operationRelation (monads : Array RelatedMonad) (left right : Expr) : MetaM Expr := do
  let leftType ← operationType monads left
  let rightType ← operationType monads right
  if leftType.getAppNumArgs == 1 && rightType.getAppNumArgs == 1 then
    if let some pair := monads.find? fun pair =>
        leftType.getAppFn == pair.source && rightType.getAppFn == pair.target then
      let α := leftType.appArg!
      unless independent monads α && (← isDefEq α rightType.appArg!) do
        throwError "effect relation: computation result types must be shared and independent of the monad"
      return mkApp3 pair.relation α left right
  match leftType, rightType with
  | .forallE name dom body bi, .forallE _ dom' body' _ =>
    if (← typeConstructorUniverses? dom).isSome && (← typeConstructorUniverses? dom').isSome then
      -- The type binds its own monad, as a tagless final program does. Both
      -- interpretations are related at an arbitrary computation relation.
      withLocalDecl name bi dom fun m =>
        withLocalDecl (name.appendAfter "'") bi dom' fun m' => do
          withLocalDeclD `R (← mkAppM ``ComputationRelation #[m, m']) fun rel => do
            let result ← operationRelation (monads.push ⟨m, m', rel⟩) (mkApp left m) (mkApp right m')
            mkForallFVars #[m, m', rel] result
    else if independent monads dom && independent monads dom' &&
        !(← bindsMonad dom) && !(← bindsMonad dom') then
      unless ← isDefEq dom dom' do
        throwError "effect relation: ordinary argument types differ:\n{dom}\nand\n{dom'}"
      withLocalDecl name bi dom fun x => do
        let result ← operationRelation monads (mkApp left x) (mkApp right x)
        mkForallFVars #[x] result
    else
      -- A result type depending on two related computations would require a
      -- heterogeneous value relation, which this homogeneous fragment excludes.
      if body.hasLooseBVar 0 || body'.hasLooseBVar 0 then
        throwError "effect relation: dependent computation arguments are unsupported"
      withLocalDecl name bi dom fun x =>
        withLocalDecl (name.appendAfter "'") bi dom' fun y => do
          let premise ← operationRelation monads x y
          withLocalDeclD `related premise fun h => do
            let result ← operationRelation monads (mkApp left x) (mkApp right y)
            mkForallFVars #[x, y, h] result
  | _, _ =>
    -- A family of capability dictionaries uses the registered dictionary
    -- relation at each leaf, e.g. `∀ x, Choose.Rel R (left x) (right x)`.
    if let .const capability _ := leftType.getAppFn then
      if rightType.getAppFn.constName? == some capability then
        if let some info := getEffectRelation? (← getEnv) capability then
          let args := leftType.getAppArgs
          let args' := rightType.getAppArgs
          if let some pair := monads.find? fun pair =>
              args[info.monadParam]? == some pair.source &&
                args'[info.monadParam]? == some pair.target then
            unless args.size == args'.size do
              throwError "effect relation: capability argument counts differ"
            for i in [:args.size] do
              if i != info.monadParam then
                unless ← isDefEq args[i]! args'[i]! do
                  throwError "effect relation: non-monad capability arguments must be shared"
            return ← mkAppOptM info.relation
              ((args ++ #[pair.target, pair.relation, left, right]).map some)
    -- A container of computations uses the relator registered for its type
    -- constructor, e.g. `Option.Rel R left right` for `Option (m α)`.
    if let some typeConstructor := leftType.getAppFn.constName? then
      if let some info := getEffectRelator? (← getEnv) typeConstructor then
        unless independent monads leftType && independent monads rightType do
          return ← applyRelator monads info leftType rightType left right fun a b =>
            withLocalDeclD `x a fun x =>
              withLocalDeclD `x' b fun x' => do
                -- Eta-reduce so that e.g. `fun x x' => R x x'` becomes `R`.
                return (← mkLambdaFVars #[x, x'] (← operationRelation monads x x')).eta
    unless independent monads leftType && independent monads rightType do
      -- Suggest a relator only where one could apply: a data type whose
      -- monad-dependent arguments are types, such as `Array (m α)`.
      if let some typeConstructor := leftType.getAppFn.constName? then
        if !isClass (← getEnv) typeConstructor && !(← isProp leftType) &&
            (← leftType.getAppArgs.allM fun arg => pure (independent monads arg) <||> isType arg) then
          throwError "effect relation: unsupported monad-dependent type:\n{leftType}\nregister a relator for {typeConstructor} with `@[effect_relator]`"
      throwError "effect relation: unsupported monad-dependent type:\n{leftType}"
    unless ← isDefEq leftType rightType do
      throwError "effect relation: ordinary result types differ:\n{leftType}\nand\n{rightType}"
    if leftType.isSort then
      throwError "effect relation: associated type fields are unsupported"
    mkEq left right

end Tapas.LogicalRelation
