import Tapas.LogicalRelation.Translation
import Tapas.LogicalRelation.Derive.SelectionFrontend

/-!
Generating the type relation `T.Rel` for a type `T`.

`derive_type_rel T (repr := A)` declares a definition `T.Rel p q` for a type that
binds a representation of its own, such as the type of a tagless final program. It
quantifies over both interpretations and a base relation between them, and asks
that related dictionaries give related results.

Such a type takes no representation as a parameter, so every binder the selection
reaches is one the type binds: several names may be given, a binder may be given by
its position among those the type binds, and a marker written in the declaration is
read whether or not a name was. With no selection at all, only markers are read.

Generating a relation proves nothing. `T.Rel p p` is a separate goal, discharged by
`Tapas.Parametricity` for a definition, or by hand for an interpreter.

## What a generated relation looks like

For a type `T ps`, the declaration is always

```lean
def T.Rel {ps} (left : T.{ls} ps) (right : T.{ls'} ps) : Prop
```

Two values and nothing else. `T`'s own parameters come first, shared and implicit, and
`ls'` renames the universes both sides need not agree on. The representation is absent,
because `T ps` does not mention it; it is bound in the *body*, together with its second
interpretation and the base relation, by the walk:

```lean
abbrev AA := {A : Type u} → [Arith A] → A

def AA.Rel.{u, u_target} : AA → AA → Prop :=
  fun left right =>
    ∀ {A : Type u} {A' : Type u_target} (R : A → A' → Prop) [inst : Arith A] [inst' : Arith A'],
      Arith.Rel R inst inst' → R left right
```

This is where a type relation differs from `C.Rel`, which takes the base relation as a
parameter. `T.Rel` quantifies over every base relation and cannot be handed one, so a
proof of `T.Rel p q` starts by introducing them.
-/

namespace Tapas.LogicalRelation

open Lean Meta Elab Command

/-- Generate and register `T.Rel`, the relation between two values of a definition
whose value is a type, such as the type of a tagless final program.

Unlike an interface, which takes its representation as a parameter, such a type
binds one itself, so the relation quantifies over both interpretations and the
base relation between them. `T`'s own parameters are shared. A universe that only
a bound representation uses may differ between the two interpretations.

`preprocess` is applied to the type the relation walks, which is how a caller selects one of
its binders by position rather than by what the rule can see. The generated relation
still relates two values of `T` itself. -/
def deriveTypeRelation (declName : Name) (selection : RepresentationSelection)
    (preprocess : Expr → MetaM Expr := pure) : MetaM Unit := do
  let env ← getEnv
  let relation := declName ++ `Rel
  if env.contains relation then
    throwError "logical relation: declaration already exists: {relation}"
  let .defnInfo info ← getConstInfo declName
    | throwError "logical relation: expected a definition whose value is a type, got {declName}"
  forallTelescope info.type (cleanupAnnotations := true) fun params result => do
    unless (← whnf result).isSort do
      throwError "logical relation: expected a definition whose value is a type, got {declName}"
    -- NOTE: Distinguish between the *type* and *body* of `declName`, as both are
    -- types but only the body binds the representations.
    let leftBody := mkAppN (mkConst declName (info.levelParams.map .param)) params
    -- `T`'s parameters are shared, so their universes are too. The universes of
    -- the representations the type binds are not, and are read off the type.
    let mut sharedLevels : CollectLevelParams.State := {}
    for param in params do
      sharedLevels := collectLevelParams sharedLevels (← inferType param)
    -- Binders selected by position are marked here, so that the rule reaches them
    -- everywhere the type is read below.
    -- NOTE: `leftWalk` will be properly expanded by `preprocess`
    let leftWalk ← preprocess leftBody
    -- A selection matching nothing would quietly relate the two sides by equality.
    unless ← bindsRepresentation leftWalk selection do
      throwError "logical relation: {declName} binds no representation the selection matches"
    let (rel, targetLevels) ← mkTypeRelation leftWalk info.levelParams.toArray selection sharedLevels
    let rightBody := mkAppN (mkConst declName targetLevels.toList) params
    -- The marks have been read; the relation is stated of `T` as it is written.
    withLocalDeclD `left leftBody fun left =>
      withLocalDeclD `right rightBody fun right => do
        let rel ← Meta.instantiateLambda rel #[left, right]
        withImplicitBinderInfos params do
          let binders := params ++ #[left, right]
          let type ← mkForallFVars binders (mkSort .zero)
          let value ← mkLambdaFVars binders rel
          let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
          addDecl <| .defnDecl <| ← mkDefinitionValInferringUnsafe relation levels type value
            (.regular 1)

/--
`derive_type_rel T (repr := A)` generates `T.Rel p q`, the relation between two values
of a definition whose value is a type, such as the type of a tagless final program.

`(repr := ...)` ranges over the binders of `T`'s **body**, never over `T`'s own
parameters: those are shared by both sides and so can never be a representation. `A` is
therefore a binder `T` itself introduces, `(repr := 0)` is the body's first binder, and
a marker is one written inside `T`'s value. Several may be given at once, and a marked
binder is selected whether or not it is also named.

Each selected binder is interpreted over its complete shared-index telescope, and the
two interpretations may use different universes. Leaving the selection off reads only
the markers, so a type carrying none is an error rather than a guess. -/
syntax (name := deriveTypeRel) "derive_type_rel " ident (reprSpec)? : command

@[command_elab deriveTypeRel]
def elabDeriveTypeRel : CommandElab := fun stx => do
  let `(derive_type_rel $declName:ident $[$spec:reprSpec]?) := stx | throwUnsupportedSyntax
  let spec? ← spec.mapM elabReprSpec
  liftTermElabM <| commitIfNoEx do
    deriveTypeRelation (← realizeGlobalConstNoOverloadWithInfo declName)
      (spec?.elim .marked fun spec => .markedOrNamed spec.names)
      (spec?.elim (fun type => pure type) fun spec => markOutermostBinders spec.indices)

end Tapas.LogicalRelation
