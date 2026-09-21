import Tapas.LogicalRelation.Registry
import Tapas.LogicalRelation.Representation

/-!
Extending the base relation from a representation to any type.

`relationAt left right` is the relation asserting that two values are related,
computed by recursion on their type. It is the translation the whole layer is
built from: `derive_interface_rel` applies it to each field of an interface,
`derive_type_rel` to a whole type, and `derive_parametric` to the two sides of a
program. A relation it cannot build is an error, never a guess.

## Vocabulary

A *representation* is a parameter whose two interpretations are being compared,
and the *base relation* `R` relates values in it; `LogicalRelation.Representation`
builds `R`, and `LogicalRelation.Derive.SelectionFrontend` allows users to specify
which binders are representations.
A type *mentions* a representation when one occurs in it. `left` and `right` are
the two values being related, and the result is always a `Prop`.

## The translation

Writing `⟦T⟧ a b` for the relation at a type `T`. Each case below is a shape of
`T`, the type of the two values being related.

* `T = repr is`, a value in a representation: the result is `R is left right`.
  The indices `is` must mention no representation, so both sides sit at the same
  index.
* `T = (x : A) → B` where `A` mentions no representation: one variable `x` is
  introduced and shared, and the recursion continues on `left x` and `right x`.
  Being shared is what makes equality the right reading for such a type.
* `T = (x : A) → B` where `A` mentions one, say `repr i` or `ε → repr i`: two
  variables `x`, `x'` and a *relational premise* `⟦A⟧ x x'` are introduced, and
  the recursion continues on `left x` and `right x'`. Each side has its own
  argument, so nothing follows about the results until the two are assumed
  related; that assumption is the premise. Being a translation itself, it takes
  the shape of `A`: `List (repr i)` gives `ListRel R x x'`, and a higher-order
  operation such as `lam` gives `∀ e e', R e e' → R (x e) (x' e')`.
  `B` **must not** depend on `x`.
* `T = (repr : K) → B` where the binder is itself a representation: `repr`, a
  second interpretation `repr'` and a base relation `R` between them are
  introduced, and the recursion continues on `left repr` and `right repr'` with
  `R` in scope. This case only brings `R` into scope; the cases below spend it.
  For example, a field taking a program polymorphic in its own representation,
  `({n} → [Monad n] → n α) → m α`, gets the premise
  `∀ n n' R [Monad n] [Monad n'], Monad.Rel R … → R a a'`, where the dictionary
  case contributes `Monad.Rel R …` and the first case `R a a'`.
* `T = D qs` where `D` is an interface, a structure of operations, with a
  generated relation, and a representation sits in its own position: the result is
  `D.Rel R left right`. A field that is a dictionary reuses an earlier derivation
  instead of being unfolded, which is what lets an interface whose field is
  another interface work.
* `T = F as` where `F` is a type constructor with a registered relator and `T`
  mentions a representation: the result is that relator applied to `left` and
  `right`, given `⟦aᵢ⟧` for each argument it lifts. An argument it does not lift
  is shared, so it must agree on both sides. Nesting follows from the recursion,
  so `Option (List (repr i))` gives `Option.Rel (ListRel (R i))`.
* `T` mentions no representation and is not a sort: the result is `left = right`.

### Rejected

* A type constructor applied to something mentioning a representation, such as
  `Array (repr i)`, with no relator registered for it. This is not a limit of
  parametricity, which gives a relator for every inductive type; relators are
  looked up here, not generated.
* An index that itself mentions a representation, such as `m (m α)`. Its two
  sides would sit at different indices, and only values at the same index are
  related.
* A binder whose type mentions a representation and which the result type then
  depends on, and a field that is itself a type.

## Reading the implementation

The cases split across two mutually recursive functions, because the three `→`
cases introduce binders and the rest do not.

`withRelatedTelescope` walks the outer `→` spine. Its three branches are, in
order, the representation binder, the shared argument and the related argument.
It introduces what each case calls for, accumulates the binders, and stops at the
first type that is not a `→`, handing everything it gathered to a continuation as
a `RelatedTelescope`.

`relatedEndpoints` is that continuation. The *endpoints* are the two values a
relation finally relates, `left` and `right` once the spine's binders have been
applied to them, and this covers the cases that read their type rather than a
binder: a value in a representation, a dictionary, a container, and equality.
Every rejection but one is here -- the exception being the dependent binder the
spine declines.

`relationAt` is the two composed: walk the spine, then close the binders it
collected around the endpoint relation.

The split is there because a proof needs the binders, not just the finished
`Prop`. `derive_parametric` abstracts its proof over exactly the binders the
statement quantifies, so it calls `withRelatedTelescope` itself and reads the
`RelatedTelescope`; `derive_interface_rel` wants only the `Prop` and goes through
`relationAt`.

`mkTypeRelation` prepares both interpretations, including their universes, and
composes the walk with the endpoint relation to build a complete binary relation.
Both `derive_type_rel` and `derive_parametric` call this core: the former declares
the resulting relation, and the latter applies it to the program to obtain the
theorem statement.

-/

namespace Tapas.LogicalRelation

open Lean Meta Tapas Utils

/-- A representation in scope, paired with its second interpretation and the base
relation between them. A type that binds a representation of its own extends the
array of these that the translation carries. -/
structure RelatedRepresentation where
  /-- The representation as the left interpretation reads it. -/
  source : Expr
  /-- The same representation as the right interpretation reads it. -/
  target : Expr
  /-- The base relation between values in the two. -/
  relation : Expr
  deriving Inhabited

/-- `type` mentions no representation in scope. -/
def independent (representations : Array RelatedRepresentation) (type : Expr) : Bool :=
  representations.all fun pair => !pair.source.occurs type && !pair.target.occurs type

/-- Does `type` bind a representation of its own? Such an argument is related
rather than shared, even where no representation from the enclosing scope occurs
in it, because each side supplies its own. A kind such as `Type u → Type v` binds
nothing and stays shared; it is the binder *of* that kind that a rule may pick. -/
partial def bindsRepresentation (type : Expr) (selection : RepresentationSelection) : MetaM Bool := do
  let .forallE name dom body bi ← whnf type | return false
  if (← selection.select name dom).isSome then return true
  if ← bindsRepresentation dom selection then return true
  withLocalDecl name bi dom fun x => bindsRepresentation (body.instantiate1 x) selection

/-- Apply a registered relator to `left : F as` and `right : F bs`. An argument the
relator does not lift is shared, so it must agree on both sides and mention no
representation; `relationOf a b` gives the relation for a lifted one. -/
private def applyRelator (representations : Array RelatedRepresentation) (info : RelatorInfo)
    (leftType rightType left right : Expr)
    (relationOf : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let args := leftType.getAppArgs
  let args' := rightType.getAppArgs
  unless rightType.getAppFn.constName? == some info.typeConstructor &&
      args.size == info.relationParamIdxs.size && args'.size == args.size do
    throwError "logical relation: relator {info.relator} does not apply to\n{leftType}\nand\n{rightType}"
  let mut relatorArgs := Array.replicate info.numParams none
  for i in [:args.size] do
    match info.relationParamIdxs[i]! with
    | none =>
      unless independent representations args[i]! && independent representations args'[i]! &&
          (← isDefEq args[i]! args'[i]!) do
        throwError "logical relation: relator {info.relator} shares an argument, which must be independent of the representation and equal on both sides:\n{args[i]!}\nand\n{args'[i]!}"
    | some j => relatorArgs := relatorArgs.set! j (some (← relationOf args[i]! args'[i]!))
  relatorArgs := relatorArgs.set! (info.numParams - 2) (some left)
  relatorArgs := relatorArgs.set! (info.numParams - 1) (some right)
  try
    mkAppOptM info.relator relatorArgs
  catch ex =>
    throwError "logical relation: cannot apply relator {info.relator} to\n{leftType}\nand\n{rightType}\n{ex.toMessageData}\nnote: the two sides may live in different universes, which the relator must allow"

/-- The type of `e`, reduced just enough for the translation to recognize its
shape. A binder, a sort, a value in a representation and a container with a
registered relator are already recognizable and are left alone; anything else is
put in weak head normal form, so that an alias such as
`abbrev Handler m α := ε → m α` reveals the binder behind it. -/
private def exposedType (representations : Array RelatedRepresentation) (e : Expr) : MetaM Expr := do
  let type := (← inferType e).cleanupAnnotations
  if type.isForall || type.isSort ||
      representations.any (fun pair => type.getAppFn == pair.source || type.getAppFn == pair.target) then
    return type
  if let some name := type.getAppFn.constName? then
    if (getRelator? (← getEnv) name).isSome then return type
  whnf type

/-- The binders introduced while walking the outer spine of a related type, and the
two endpoints once they have been applied to them. -/
structure RelatedTelescope where
  /-- The representations in scope, including any the spine itself introduced. -/
  representations : Array RelatedRepresentation
  /-- Every binder introduced, in order. A statement and a proof of it abstract
  over exactly these. -/
  binders : Array Expr
  /-- The left endpoint, applied to its arguments. -/
  left : Expr
  /-- The right endpoint, applied to its arguments. -/
  right : Expr
  /-- The arguments given to the left endpoint, one per spine binder. -/
  leftArgs : Array Expr
  /-- The arguments given to the right endpoint, aligned with `leftArgs`. -/
  rightArgs : Array Expr
  /-- The relational premise introduced at each argument position, where there is one. -/
  premises : Array (Option Expr)
  /-- The selection that remains where the spine ends. -/
  selection : RepresentationSelection

namespace RelatedTelescope

/-- A telescope over `left` and `right` before any binder has been walked. -/
private def start (representations : Array RelatedRepresentation)
    (left right : Expr) (selection : RepresentationSelection) : RelatedTelescope :=
  { representations, binders := #[], left, right, leftArgs := #[], rightArgs := #[],
    premises := #[], selection }

/-- Extend the telescope by one binder step: what was introduced, the arguments
the two endpoints now receive, the premise relating them if there is one, and a
representation if the binder was one. Every step advances the three aligned
arrays together. -/
private def step (t : RelatedTelescope) (introduced : Array Expr)
    (leftArg rightArg : Expr) (premise : Option Expr := none)
    (representation? : Option RelatedRepresentation := none) : RelatedTelescope :=
  { t with
    representations := representation?.elim t.representations t.representations.push
    binders := t.binders ++ introduced
    left := mkApp t.left leftArg
    right := mkApp t.right rightArg
    leftArgs := t.leftArgs.push leftArg
    rightArgs := t.rightArgs.push rightArg
    premises := t.premises.push premise }

end RelatedTelescope

private def findApplicableRelatedRepresentation (representations : Array RelatedRepresentation)
    (left right : Expr) : Option RelatedRepresentation :=
  representations.find? fun pair => left == pair.source && right == pair.target

mutual

-- FIXME: Consider having some caching below?
-- CHECK `allowDependentBinders` and `relateBinder` might need more careful handling
/-- Walk what is left of the two endpoints' `→` spine, extending `t` as it goes.
`withRelatedTelescope` starts it off; see there for the other arguments. -/
private partial def withRelatedTelescopeAux {α : Type} [Inhabited α] (t : RelatedTelescope)
    (relateBinder : Expr → MetaM Bool) (allowDependentBinders : Bool)
    (k : RelatedTelescope → MetaM α) : MetaM α := do
  let leftType ← exposedType t.representations t.left
  let rightType ← exposedType t.representations t.right
  -- `T = repr is`: a value in a representation ends the spine, even where its
  -- type could still reduce to something else.
  if let some _ := findApplicableRelatedRepresentation t.representations leftType.getAppFn' rightType.getAppFn' then
    return ← k t
  let continue' (t : RelatedTelescope) := withRelatedTelescopeAux t relateBinder allowDependentBinders k
  match leftType, rightType with
  | .forallE name dom body bi, .forallE _ dom' body' _ =>
    if let some kind ← t.selection.select name dom then
      -- `T = (repr : K) → B`: the binder is itself a representation, so both
      -- interpretations and an arbitrary base relation between them enter scope,
      -- at the kind the rule hands back rather than the written one.
      -- FIXME: If `t.selection.select name dom'` is none then probably should error stop?
      let kind' := (← t.selection.select name dom').getD dom'
      withLocalDecl name bi kind fun m =>
        withLocalDecl (name.appendAfter "'") bi kind' fun m' => do
          withLocalDeclD `R (← sharedIndexRelation m m') fun rel =>
            continue' (t.step #[m, m', rel] m m' (representation? := some ⟨m, m', rel⟩))
    -- `T = (x : A) → B` with `A` mentioning no representation: one binder, shared.
    else if independent t.representations dom && independent t.representations dom' &&
        !(← bindsRepresentation dom t.selection) && !(← bindsRepresentation dom' t.selection) then
      unless ← isDefEq dom dom' do
        throwError "logical relation: ordinary argument types differ:\n{dom}\nand\n{dom'}"
      withLocalDecl name bi dom fun x => continue' (t.step #[x] x x)
    else
      -- `T = (x : A) → B` with `A` mentioning one: two binders and a premise.
      --
      -- A result type depending on both of them would need a relation between
      -- values at different types, so it is refused. A declaration's own
      -- parameter telescope is the exception the caller opts into: `[MonoBind m]`
      -- refers to the `[Monad m]` before it, and each side carries its own copy.
      -- NOTE: In this sense, `!allowDependentBinders` is a very coarse guard:
      -- it's mostly for `partial_fixpoint` definitions.
      if !allowDependentBinders && (body.hasLooseBVar 0 || body'.hasLooseBVar 0) then
        throwError "logical relation: dependent representation arguments are unsupported"
      withLocalDecl name bi dom fun x =>
        withLocalDecl (name.appendAfter "'") bi dom' fun y => do
          -- A parameter that must be duplicated but relates nothing, such as an
          -- order instance, is introduced on both sides without a premise.
          unless ← relateBinder dom do
            return ← continue' (t.step #[x, y] x y)
          let premise ← relationAt t.representations x y t.selection
          withLocalDeclD (name.appendAfter "_rel") premise fun h =>
            continue' (t.step #[x, y, h] x y (some h))
  | _, _ => k t

/-- The relation where the binder spine ends: a value in a representation, a
dictionary, a container with a registered relator, or an unrelated value. -/
private partial def relatedEndpoints (t : RelatedTelescope) : MetaM Expr := do
  let ⟨representations, _, left, right, _, _, _, selection⟩ := t
  let leftType ← exposedType representations left
  let rightType ← exposedType representations right
  -- `T = repr is`: the base relation, applied to the shared indices.
  if let some pair := findApplicableRelatedRepresentation representations leftType.getAppFn' rightType.getAppFn' then
    -- Check that the representation indices are consistent and independent
    let indices := leftType.getAppArgs
    let indices' := rightType.getAppArgs
    unless indices.size == indices'.size do
      throwError "logical relation: shared index counts differ"
    for index in indices, index' in indices' do
      unless independent representations index && independent representations index' &&
          (← isDefEq index index') do
        throwError "logical relation: representation indices must be shared and independent of the representation"
    -- If so, then apply the relation
    return mkApp2 (mkAppN pair.relation indices) left right
  -- `T = D qs`: an interface with a generated relation reuses that derivation.
  -- A family of them lands here at each leaf, e.g. `∀ x, Choose.Rel R (left x) (right x)`.
  if let some interfaceName := leftType.getAppFn'.constName? then
    if rightType.getAppFn'.constName? == some interfaceName then
      if let some info := getInterfaceRelation? (← getEnv) interfaceName then
        let args := leftType.getAppArgs
        let args' := rightType.getAppArgs
        -- These are the class's representation arguments, not the two dictionaries
        -- `left` and `right` that the generated relation is finally applied to.
        match args[info.reprParamIdx]?, args'[info.reprParamIdx]? with
        | some repr, some repr' =>
          if let some pair := findApplicableRelatedRepresentation representations repr repr' then
            -- Check
            unless args.size == args'.size do
              throwError "logical relation: class argument counts differ"
            for i in [:args.size] do
              if i != info.reprParamIdx then
                unless ← isDefEq args[i]! args'[i]! do
                  throwError "logical relation: non-representation class arguments must be shared"
            -- Apply
            return ← mkAppOptM info.relation ((interfaceRelationParamsLayout args pair.target pair.relation left right).map some)
        | _, _ => pure ()
  -- `T = F as`: a container uses the relator registered for its type
  -- constructor, e.g. `Option.Rel R left right` for `Option (repr i)`.
  if let some typeConstructor := leftType.getAppFn.constName? then
    if let some info := getRelator? (← getEnv) typeConstructor then
      unless independent representations leftType && independent representations rightType do
        return ← applyRelator representations info leftType rightType left right fun a b =>
          withLocalDeclD `x a fun x =>
            withLocalDeclD `x' b fun x' => do
              -- Eta-reduce so that e.g. `fun x x' => R x x'` becomes `R`.
              return (← mkLambdaFVars #[x, x'] (← relationAt representations x x' selection)).eta
  unless independent representations leftType && independent representations rightType do
    -- CHECK These are just error messages, but do they need to be so complicated?
    /- NOTE: Both extension points are looked up here and neither is invented, so all this
    can do is name the one that fits. A relator is registered for none of the heads that
    reach this point, since the case above returns whenever one is, so which extension
    point was meant is open by construction. `sharedRepresentationLevels` resolves the
    same ambiguity, but conservatively and for universe collection only, and its NOTE
    says as much, so its answer is not repeated as advice here. -/
    let mut suggestions : Array MessageData := #[]
    if let some head := leftType.getAppFn.constName? then
      let env ← getEnv
      if let some info := getInterfaceRelation? env head then
        -- The relation exists and the case above declined it, which it does when the
        -- representation sits somewhere other than the argument related, as in
        -- `D (List repr)`. Saying so beats suggesting what is already there.
        if rightType.getAppFn.constName? == some head then
          suggestions := suggestions.push
            m!"{info.relation} relates argument {info.reprParamIdx}, and none sits there"
      -- A relator lifts relations on a type constructor's arguments, so one could only
      -- apply where every representation-dependent argument is a type.
      if !(← isProp leftType) &&
          (← leftType.getAppArgs.allM fun arg => pure (independent representations arg) <||> isType arg) then
        suggestions := suggestions.push m!"register a relator for {head} with `@[relator]`"
      if isStructure env head && (getInterfaceRelation? env head).isNone then
        let interface := m!"generate its relation with `derive_interface_rel {head} (repr := ...)`"
        /- A class may carry a relator: `@[relator]` accepts one whose shape fits. But a
        relator premise is opaque to the proof search, which reads its rules off an
        interface relation's fields, so a program using any operation of the class then
        fails with no applicable translation for that projection. Pointing a class at the
        relation alone is that, not a claim about what the author meant. Anything else may
        be either, `Array` and a packed interpreter alike. -/
        suggestions := if isClass env head then #[interface]
          else suggestions.push m!"or, if it is an interface, {interface}"
    let detail := if suggestions.isEmpty then m!"" else
      m!"\n{MessageData.joinSep suggestions.toList "\n"}"
    throwError "logical relation: unsupported representation-dependent type:\n{leftType}{detail}"
  unless ← isDefEq leftType rightType do
    throwError "logical relation: ordinary result types differ:\n{leftType}\nand\n{rightType}"
  if leftType.isSort then
    throwError "logical relation: associated type fields are unsupported"
  -- `T` mentions no representation: both sides receive the same value.
  mkEq left right

/-- The relation asserting that `left` and `right` are related, read off their
type by the translation in this module's docstring.

`representations` holds the representations already in scope with their second
interpretations and base relations; a binder that `selection` picks extends it.
A shape the translation has no rule for is an error, not a guess. -/
partial def relationAt (representations : Array RelatedRepresentation) (left right : Expr)
    (selection : RepresentationSelection) : MetaM Expr :=
  withRelatedTelescopeAux (.start representations left right selection)
      (fun _ => pure true) false fun t => relatedEndpoints t >>= mkForallFVars t.binders

end

/-- Walk the outer `→` spine of the two endpoints' types, introducing the binders
a relation between them quantifies over, and run `k` on what was gathered.

`relateBinder` says whether a binder mentioning a representation carries a
relational premise, and `allowDependentBinders` whether a later binder's type may
mention an earlier related one. -/
def withRelatedTelescope {α : Type} [Inhabited α]
    (representations : Array RelatedRepresentation) (left right : Expr)
    (selection : RepresentationSelection) (relateBinder : Expr → MetaM Bool)
    (k : RelatedTelescope → MetaM α) (allowDependentBinders : Bool := false) : MetaM α :=
  withRelatedTelescopeAux (.start representations left right selection) relateBinder
    allowDependentBinders k

/-- Build the complete binary relation for a type, allowing the two interpretations
to live in different universes. -/
def mkTypeRelation (type : Expr) (levelParams : Array Name) (selection : RepresentationSelection)
    (sharedLevels : CollectLevelParams.State := {})
    (relateBinder : Expr → MetaM Bool := fun _ => pure true)
    (allowDependentBinders : Bool := false) : MetaM (Expr × Array Level) := do
  let sharedLevels ← sharedRepresentationLevels #[] type sharedLevels selection
  -- The second interpretation is the same constant at the renamed universes.
  let targetLevels := renameLevelParams levelParams sharedLevels
  let targetType := type.instantiateLevelParamsArray levelParams targetLevels
  let relation ← withLocalDeclD `left type fun left =>
    withLocalDeclD `right targetType fun right => do
      -- No representation is in scope yet: the type is expected to bind its own.
      let body ← withRelatedTelescope #[] left right selection relateBinder
        (allowDependentBinders := allowDependentBinders)
        fun t => relatedEndpoints t >>= mkForallFVars t.binders
      mkLambdaFVars #[left, right] body
  return (relation, targetLevels)

end Tapas.LogicalRelation
