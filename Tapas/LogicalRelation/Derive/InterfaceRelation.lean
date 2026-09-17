import Tapas.LogicalRelation.Translation
import Tapas.LogicalRelation.Derive.SelectionFrontend

-- CHECK `derive_interface_rel` might not generate a class?
-- CHECK How would it be possible to avoid flattening inherited operations?

/-!
Generating the interface relation `C.Rel` for an interface `C`.

`derive_interface_rel C (repr := A)` declares a class `C.Rel R left right` with one
condition per operation of `C`, each saying that the two dictionaries agree on that
operation up to `R`. Every parameter of `C` other than the representation is shared,
and none of them may depend on it.

Exactly one parameter of `C` may be selected. Further names, and markers inside an
operation's type, reach the representations an operation binds of its own.

## What a generated class looks like

For an interface `C ps` whose representation parameter is `repr`, the declaration is

```lean
class C.Rel {ps} {repr' : ..} (R : ∀ {is}, repr is → repr' is → Prop)
    (left : C ps) (right : C ps[repr := repr']) : Prop
```

with one field per operation, in the order of `getStructureFieldsFlattened`:
**inherited operations are included, parent subobjects are not**.
For `Monad.Rel`, the `bind` field is

```lean
bind : ∀ {α β} (x : m α) (x' : m' α), R x x' →
  ∀ (f : α → m β) (f' : α → m' β), (∀ a, R (f a) (f' a)) →
  R (x >>= f) (x' >>= f')
```

Each generated `C.Rel` is recorded, so a later derivation whose field is itself a
dictionary reuses it rather than unfolding it, and client code can look it up.
-/

namespace Tapas.LogicalRelation

open Lean Meta Elab Command Utils

/-- Declare `name` as a `Prop`-valued structure class over the given parameters,
with the given fields: what `structure ... where ...` followed by `attribute [class]`
would produce. -/

/- NOTE: The `structure` command takes syntax, while these field types are expressions
computed by `relationAt` that mention local hypotheses. Putting them into syntax
would mean delaborating them, which is lossy and loses the hypotheses' identity, so
the pieces are added by hand instead.

The steps below are the ones `Lean.Elab.Structure` runs when it finalizes a
structure, in its order, minus those that only matter for what a generated relation
never has:

* no default field values, so no `addDefaults` or `checkDefaults`;
* no parents, so the flat constructor is a plain alias of the constructor, the
  parent list is empty, and there are no parent instances or subobject projections
  to make reducible;
* no docstrings, so no `enableRealizationsForConst`;
* no data, being `Prop`-valued, so no `sizeOf` or `injEq`.

Each of those would have to come back if a generated relation ever gained the
feature it stands for. -/
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
  -- The type itself: one constructor taking every field, over the universes its
  -- parameter types use.
  addDecl <| .inductDecl levels params.size
    [{ name, type, ctors := [{ name := ctorName, type := ctorType }] }] false
  -- These structures have no embedded parents: their flat constructor is an
  -- alias of the constructor. Lean uses it for structure syntax and printing.
  addDecl <| .defnDecl <| ← mkDefinitionValInferringUnsafe flatCtorName levels
    ctorType (mkConst ctorName (levels.map .param)) .abbrev
  setReducibleAttribute flatCtorName
  -- What makes it a structure rather than a bare inductive: which constants are
  -- its field projections.
  modifyEnv fun env => registerStructure env {
    structName := name
    fields := fields.map fun (field, _) => {
      fieldName := field, projFn := name ++ field,
      binderInfo := .default, subobject? := none
    }
  }
  setStructureParents name #[]
  discard <| computeStructureResolutionOrder name false
  -- As a class, a proof that two interpreters agree can be found by instance
  -- search even where the interpreters themselves cannot.
  setEnv <| ← ofExcept <| addClass (← getEnv) name
  -- `true` here makes each projection take its structure argument
  -- instance-implicitly, so `C.Rel.op` finds the relation instead of being handed it.
  mkProjections name (fields.map fun (field, _) => {
    ref := Syntax.missing, projName := name ++ field
  }) true
  mkRecOn name
  mkCasesOn name

/-- Generate and register `C.Rel`, the class holding one condition per operation
of `C`, indexed by the two dictionaries it relates. `C` is any structure; being a
typeclass is the usual case but is not required.

`selection` decides which binders are representations, and is asked about both
the parameters of `C` and the binders met inside an operation's type. **Exactly one**
parameter must match, and no other parameter may mention it; an operation whose
argument binds a representation of its own is related through the same rule.

`preprocess` is applied to `C`'s own type before the parameter is chosen, which is how a
caller selects one by position rather than by what the rule can see. It is spent
there: the class is declared over `C`'s parameters as written.

Failure leaves nothing behind: the command elaborators roll back both the
declarations and the registry entry. -/
def deriveInterfaceRelation (interfaceName : Name) (selection : RepresentationSelection)
    (preprocess : Expr → MetaM Expr := pure) : MetaM Unit := do
  let env ← getEnv
  unless isStructure env interfaceName do
    throwError "logical relation: expected a structure, got {interfaceName}"
  let info ← getConstInfo interfaceName
  let relation := interfaceName ++ `Rel
  if env.contains relation then
    throwError "logical relation: declaration already exists: {relation}"
  -- The original declaration's `outParam` annotations do not apply to its inputs,
  -- so the telescope clears them here.
  let idx ← forallTelescope (← preprocess info.type) (cleanupAnnotations := true) fun params _ => do
    -- The same rule that governs binders inside an operation picks the parameter.
    let candidates ← params.filterM fun param => do
      pure (← selection.select (← param.fvarId!.getUserName) (← inferType param)).isSome
    let #[selected] := candidates
      | do
        let names ← candidates.mapM (·.fvarId!.getUserName)
        throwError "logical relation: expected exactly one representation parameter of \
          {interfaceName}, selected:{indentD (toMessageData names.toList)}"
    pure <| params.idxOf selected
  forallTelescope info.type (cleanupAnnotations := true) fun params _ => do
    let some repr := params[idx]? | throwError "logical relation: unexpected error"
    for param in params do
      if repr.occurs (← inferType param) then
        throwError "logical relation: class parameters depending on the selected representation are unsupported"
    -- Only a free output universe can vary independently. An interface such
    -- as `C (m : Type → Type)` or `C (σ : Type v) (m : Type u → Type v)`
    -- constrains both interpretations to keep that universe.
    let mut sharedLevels : CollectLevelParams.State := {}
    for param in params.eraseIdx! idx do
      sharedLevels ← sharedRepresentationLevels #[repr] (← inferType param) sharedLevels selection
    let notFreshLevels := collectLevelParams {} info.type
    -- `n` is the second interpretation and `rel` the base relation between them.
    withRelatedRepresentation repr sharedLevels notFreshLevels fun repr' rel _ => do
      let leftType := mkAppN (mkConst interfaceName (info.levelParams.map .param)) params
      -- Infer the target universes from the shared parameters and new representation.
      let rightType ← mkAppOptM interfaceName ((params.set! idx repr').map some)
      let rightType ← instantiateMVars rightType
      withLocalDeclD `left leftType fun left =>
        withLocalDeclD `right rightType fun right => do
          -- One condition per operation, inherited ones flattened in.
          let fieldNames := getStructureFieldsFlattened env interfaceName false
          let fields ← fieldNames.mapM fun field => do
            try
              let l ← mkProjection left field
              let r ← mkProjection right field
              pure (field, ← relationAt #[⟨repr, repr', rel⟩] l r selection)
            catch ex =>
              throwError "while deriving {relation}.{field}:\n{ex.toMessageData}"
          -- The class parameters are determined by `left`, so they are implicit.
          withImplicitBinderInfos params do
            addRelationClass relation (interfaceRelationParamsLayout params repr' rel left right) fields
          -- Register as interface relation
          -- CHECK Need a check on existing registration to avoid duplicates?
          modifyEnv fun env => interfaceRelationExt.addEntry env {
            interfaceName, reprParamIdx := idx, relation, fields := fieldNames
          }

/-- `derive_interface_rel C (repr := A)` generates the class `C.Rel R left right`,
holding one condition per operation of the interface `C`: related arguments give
related results. `C` is any structure, typeclass or not. `A` is the parameter to
relate, named whatever its arity; every other parameter is shared, and none may
depend on it.

An operation may take a program polymorphic in a representation of its own. Name
that binder too, as in `(repr := A, n)`, or mark it in the declaration, and the
program is related rather than shared. A parameter may also be given by position,
as in `(repr := 0)`. -/
syntax (name := deriveInterfaceRel) "derive_interface_rel " ident reprSpec : command

@[command_elab deriveInterfaceRel]
def elabDeriveInterfaceRel : CommandElab := fun stx => do
  let `(derive_interface_rel $interfaceName:ident $spec:reprSpec) := stx
    | throwUnsupportedSyntax
  let spec ← elabReprSpec spec
  liftTermElabM <| commitIfNoEx do
    deriveInterfaceRelation (← realizeGlobalConstNoOverloadWithInfo interfaceName)
      (.markedOrNamed spec.names) (markOutermostBinders spec.indices)

end Tapas.LogicalRelation
