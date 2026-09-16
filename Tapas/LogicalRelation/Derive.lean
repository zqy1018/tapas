import Tapas.LogicalRelation.OperationRelation

/-!
Generate relations between two interpretations of an effect capability. The
generated declarations are ordinary, kernel-checked `Prop`-valued classes.

## What is generated

Let `C` be a structure typeclass with parameters `ps`, one of which is the
selected monad `m : Type u → Type v`. `derive_effect_rel C` adds

```
class C.Rel {ps} {m' : Type u → Type v'} (R : ComputationRelation m m')
    (left : C ps) (right : C ps[m := m']) : Prop
```

with one field per operation of `C`, listed in the order of
`getStructureFieldsFlattened` (inherited operations are flattened, parent
subobjects omitted). All parameters other than `m` are shared by both
dictionaries. Each field states that `left.op` and `right.op` are related. For
`Monad`, the `bind` field is

```
bind : ∀ {α β} (x : m α) (x' : m' α), R x x' →
  ∀ (f : α → m β) (f' : α → m' β), (∀ a, R (f a) (f' a)) →
  R (x >>= f) (x' >>= f')
```

`deriveEffectRelation` selects the monad, builds the two dictionaries, runs
`operationRelation` on each field and declares the class via
`addRelationClass`. It then records an `EffectRelationInfo` so that later
derivations (the dictionary case of `operationRelation`) and client code can
find the relation.

## Types that bind their own monad

A capability takes its monad as a parameter, so `C.Rel` takes the computation relation as a
parameter too. The type of a monad-polymorphic program instead binds the monad itself, as the
type of a tagless final program does:

```
abbrev Final (E : Type u → Type v) (α : Type u) :=
  {m : Type u → Type w} → [Monad m] → ((β : Type u) → E β → m β) → m α
```

`derive_type_rel Final` declares `Final.Rel p q`, which quantifies over the monads the type
binds and over the relation between them. Both commands run the same translation, so a
capability argument of such a type gets its generated relation, and a handler argument the
pointwise premise. `deriveTypeRelation` declares a `def` rather than a class: with the monads
bound inside, there is no dictionary to project from.
-/

namespace Tapas.LogicalRelation

open Lean Meta Elab Command

/-- The computation universe of the second interpretation: a fresh parameter when `v` is a
universe parameter that the shared types do not mention, and `v` itself otherwise. -/
def targetComputationLevel (v : Level) (shared : CollectLevelParams.State)
    (used : Expr) : Level :=
  match v with
  | .param name =>
    if shared.params.contains name then v
    else (collectLevelParams {} used).getUnusedLevelParam `v_target
  | _ => v

/-- Universe levels of the second interpretation of a declaration: every parameter the shared
types do not mention is replaced by a fresh one, so the two interpretations may use different
computation universes. -/
private def targetDeclLevels (levelParams : List Name) (shared : CollectLevelParams.State) :
    List Level := Id.run do
  let mut used := levelParams
  let mut levels := #[]
  for name in levelParams do
    if shared.params.contains name then
      levels := levels.push (.param name)
    else
      let mut fresh := name.appendAfter "_target"
      while used.contains fresh do fresh := fresh.appendAfter "'"
      used := fresh :: used
      levels := levels.push (.param fresh)
  return levels.toList

/-- The parameters are determined by the related values, so the generated relation takes them
implicitly. The original declaration's `outParam` annotations do not apply to its inputs. -/
private def withImplicitParams (params : Array Expr) (k : MetaM α) : MetaM α := do
  let mut lctx ← getLCtx
  for param in params do
    lctx := lctx.modifyLocalDecl param.fvarId! fun decl =>
      (decl.setType decl.type.cleanupAnnotations).setBinderInfo .implicit
  withLCtx lctx (← getLocalInstances) k

/-- Declare `name` as a `Prop`-valued structure class with the given parameters and fields.

The `structure` command cannot be used from `MetaM` with computed field types,
so the pieces it would normally produce are added by hand:
1. the single-constructor inductive `name` with constructor `name.mk`, whose
   universe parameters are those appearing in the parameter types;
2. the flat constructor alias and the structure metadata (fields, no parents);
3. the `class` attribute, the field projections, `recOn` and `casesOn`. -/
private def addRelationClass (name : Name) (params : Array Expr)
    (fields : Array (Name × Expr)) : MetaM Unit := do
  let type ← mkForallFVars params (mkSort .zero)
  let levels := (collectLevelParams {} type).params.toList
  let result := mkAppN (mkConst name (levels.map .param)) params
  let ctorBody := fields.foldr (fun (field, type) body =>
    .forallE field type body .default) result
  let ctorType ← mkForallFVars params ctorBody
  let ctorName := name ++ `mk
  let flatCtorName := mkFlatCtorOfStructCtorName ctorName
  addDecl <| .inductDecl levels params.size
    [{ name, type, ctors := [{ name := ctorName, type := ctorType }] }] false
  -- These structures have no embedded parents: their flat constructor is an
  -- alias of the constructor. Lean uses it for structure syntax and printing.
  addDecl <| .defnDecl <| ← mkDefinitionValInferringUnsafe flatCtorName levels
    ctorType (mkConst ctorName (levels.map .param)) .abbrev
  setReducibleAttribute flatCtorName
  modifyEnv fun env => registerStructure env {
    structName := name
    fields := fields.map fun (field, _) => {
      fieldName := field, projFn := name ++ field,
      binderInfo := .default, subobject? := none
    }
  }
  setStructureParents name #[]
  discard <| computeStructureResolutionOrder name false
  setEnv <| ← ofExcept <| addClass (← getEnv) name
  mkProjections name (fields.map fun (field, _) => {
    ref := Syntax.missing, projName := name ++ field
  }) true
  mkRecOn name
  mkCasesOn name

/-- Generate and register `C.Rel`, indexed by the two actual capability dictionaries.
`monadName?` selects a class parameter by binder name when several have type `Type u → Type v`.
The command elaborator rolls back declarations and metadata if generation fails.

Steps:
1. Check that `capability` is a structure class and `capability.Rel` is new.
2. Open the class parameters `ps` and select the monad `m`: the unique parameter
   of type `Type u → Type v`, or the one named `monadName?`. No other parameter's
   type may mention `m`.
3. Choose the universe of the second monad `n : Type u → Type v'`. `v'` is fresh
   if `v` is a universe parameter used nowhere else in the parameters; otherwise
   `v' = v`.
4. In the context `ps, n, R : ComputationRelation m n, left : C ps,
   right : C ps[m := n]`, compute `operationRelation m n R left.op right.op` for
   every flattened field `op`.
5. Make `ps` implicit (they are determined by `left`), declare the class with
   parameters `ps, n, R, left, right`, and register its `EffectRelationInfo`. -/
def deriveEffectRelation (capability : Name) (monadName? : Option Name := none) : MetaM Unit := do
  let env ← getEnv
  unless isClass env capability && isStructure env capability do
    throwError "effect relation: expected a structure typeclass, got {capability}"
  let info ← getConstInfo capability
  let relation := capability ++ `Rel
  if env.contains relation then
    throwError "effect relation: declaration already exists: {relation}"
  forallTelescope info.type fun params _ => do
    let mut candidates : Array (Nat × Level × Level) := #[]
    for i in [:params.size] do
      if let some (u, v) ← typeConstructorUniverses? (← inferType params[i]!) then
        candidates := candidates.push (i, u, v)
    let selected ← match monadName? with
      | none => pure candidates
      | some name => candidates.filterM fun (i, _, _) => do
          return (← params[i]!.fvarId!.getUserName) == name
    let #[(idx, u, v)] := selected
      | throwError "effect relation: select exactly one monad parameter with `(monad := name)`"
    let m := params[idx]!
    for param in params do
      if m.occurs (← inferType param) then
        throwError "effect relation: capability parameters depending on the selected monad are unsupported"
    -- Only a free output universe can vary independently. A capability such
    -- as `C (m : Type → Type)` or `C (σ : Type v) (m : Type u → Type v)`
    -- constrains both interpretations to keep that universe.
    let mut sharedLevels := collectLevelParams {} (mkSort (.succ u))
    for param in params do
      if param != m then
        sharedLevels ← sharedComputationLevels #[m] (← inferType param) sharedLevels
    let v' := targetComputationLevel v sharedLevels info.type
    let nType ← mkArrow (mkSort (.succ u)) (mkSort (.succ v'))
    withLocalDecl (← m.fvarId!.getUserName <&> (·.appendAfter "'")) .implicit nType fun n => do
      let leftType := mkAppN (mkConst capability (info.levelParams.map .param)) params
      -- Infer the target universes from the shared parameters and new monad.
      let rightType ← mkAppOptM capability ((params.set! idx n).map some)
      let rightType ← instantiateMVars rightType
      withLocalDeclD `R (← mkAppM ``ComputationRelation #[m, n]) fun rel =>
        withLocalDeclD `left leftType fun left =>
          withLocalDeclD `right rightType fun right => do
            let fieldNames := getStructureFieldsFlattened env capability false
            let fields ← fieldNames.mapM fun field => do
              try
                let l ← mkProjection left field
                let r ← mkProjection right field
                return (field, ← operationRelation #[⟨m, n, rel⟩] l r)
              catch ex =>
                throwError "while deriving {relation}.{field}:\n{ex.toMessageData}"
            withImplicitParams params do
              addRelationClass relation (params ++ #[n, rel, left, right]) fields
            modifyEnv fun env => effectRelationExt.addEntry env {
              capability, monadParam := idx, relation, fields := fieldNames
            }

/-- Generate and register `T.Rel`, the relation at the type `T`, for a definition whose value
is a type, such as the type of a tagless final program.

Unlike a capability, such a type binds its own monads, so the relation quantifies over them
instead of taking a relation as a parameter. The parameters of `T` are shared by both
interpretations.

Steps:
1. Check that `T` is a definition whose type ends in a sort, and that `T.Rel` is new.
2. Open the parameters `ps` of `T`.
3. Replace the universe parameters that carry only computation universes, giving the second
   interpretation `T.{levels'} ps`. For a type binding `m : Type u → Type w`, this lets the
   two interpretations use different `w`.
4. Translate the type with `operationRelation`, which relates every monad the type binds.
5. Declare `T.Rel {ps} (left : T ps) (right : T.{levels'} ps) : Prop`. -/
def deriveTypeRelation (declName : Name) : MetaM Unit := do
  let env ← getEnv
  let relation := declName ++ `Rel
  if env.contains relation then
    throwError "effect relation: declaration already exists: {relation}"
  let .defnInfo info ← getConstInfo declName
    | throwError "effect relation: expected a definition whose value is a type, got {declName}"
  forallTelescope info.type fun params result => do
    unless (← whnf result).isSort do
      throwError "effect relation: expected a definition whose value is a type, got {declName}"
    let leftType := mkAppN (mkConst declName (info.levelParams.map .param)) params
    -- The parameters are shared, so their universes are; the computation universes of the
    -- monads the type binds are not, and are read off the type itself.
    let mut sharedLevels : CollectLevelParams.State := {}
    for param in params do
      sharedLevels ← sharedComputationLevels #[] (← inferType param) sharedLevels
    sharedLevels ← sharedComputationLevels #[] leftType sharedLevels
    let rightType := mkAppN (mkConst declName (targetDeclLevels info.levelParams sharedLevels))
      params
    withLocalDeclD `left leftType fun left =>
      withLocalDeclD `right rightType fun right => do
        let body ← operationRelation #[] left right
        withImplicitParams params do
          let binders := params ++ #[left, right]
          let type ← mkForallFVars binders (mkSort .zero)
          let value ← mkLambdaFVars binders body
          let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
          addDecl <| .defnDecl <| ← mkDefinitionValInferringUnsafe relation levels type value
            (.regular 1)

/-- Run a command atomically: a failure restores the environment, so a failed derivation leaves
no partial declaration or registry entry. -/
def withCommandRollback (x : CommandElabM Unit) : CommandElabM Unit := do
  let saved ← getThe Command.State
  try x catch ex =>
    set saved
    throw ex

/--
`derive_effect_rel C` generates `C.Rel` and a relation rule for every inherited
operation. Use `derive_effect_rel C (monad := n)` when `C` has several monads.
-/
syntax (name := deriveEffectRel) "derive_effect_rel " ident
  (" (" &"monad" " := " ident ")")? : command

/--
`derive_type_rel T` generates `T.Rel`, the relation between two interpretations of a type
whose value is a type, such as the type of a tagless final program. The monads the type binds
are related by an arbitrary computation relation, and may use different computation universes.
-/
syntax (name := deriveTypeRel) "derive_type_rel " ident : command

@[command_elab deriveEffectRel]
def elabDeriveEffectRel : CommandElab := fun stx => do
  let `(derive_effect_rel $capability:ident $[(monad := $monadName:ident)]?) := stx
    | throwUnsupportedSyntax
  withCommandRollback <| liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo capability
    deriveEffectRelation name (monadName.map (·.getId))

@[command_elab deriveTypeRel]
def elabDeriveTypeRel : CommandElab := fun stx => do
  let `(derive_type_rel $declName:ident) := stx | throwUnsupportedSyntax
  withCommandRollback <| liftTermElabM do
    deriveTypeRelation (← realizeGlobalConstNoOverloadWithInfo declName)

end Tapas.LogicalRelation
