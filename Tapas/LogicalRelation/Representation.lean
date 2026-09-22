module

public import Tapas.LogicalRelation.Registry
public import Tapas.LogicalRelation.BaseRelationAliasing
public import Tapas.Utils
public meta import Tapas.LogicalRelation.Registry
public import Lean.Meta.Basic

public meta section

/-!
The representation parameter: the base relation between its two interpretations,
and the universes the two must share.

The representation parameter is the one selected with `(repr := A)`, the parameter
whose two interpretations a logical relation compares. Because every other relation
in this layer is built from the base relation, this file fixes what "two
interpretations are related" means before any operation type is translated.

The construction opens the parameter's whole telescope, keeps the indices shared,
and places a binary relation at the final sort:

```lean
repr  : (i : I) → J i → Type v
repr' : (i : I) → J i → Type w
R     : ∀ ⦃i⦄ ⦃j : J i⦄, repr i j → repr' i j → Prop
```

Here `i` and `j` are the *shared indices* for the two interpretations. They are bound
strict implicit; the comment on `withSharedIndices` says what goes wrong otherwise.
A later index type may mention earlier indices, and only the index domains have to
agree: the two interpretations may end in different universes, so `repr i j` can be
a runtime value where `repr' i j` is a syntax tree. Zero indices use the same
construction as any other arity, which is why the API accepts a carrier `A : Type u`
directly instead of asking for it wrapped.

For `m : Type u → Type v` this gives the homogeneous relation the monadic layer
uses. It is not full heterogeneous parametricity: relating values at *different*
indices, or dependent values, needs another interpretation and its own rules.

NOTE: this is a narrower notion of representation parameter than `infer_final%` in
`Tapas.TaglessFinal.Inference` abstracts over. Instance inference places no
requirement on a selected parameter's kind and will happily abstract over a value,
turning `infer_final% (n : Nat) => ...` into `{n : Nat} → [ValueAt n] → ...`. A
representation here must be a telescope ending in a sort, since only then are there
values to relate. Selecting one that is not fails rather than quietly sharing it.

`withRelatedRepresentation` puts the pieces together for a caller that already has
the representation in hand and wants its second interpretation and base relation
introduced; `derive_interface_rel` uses it for an interface parameter. A caller relating
two values of a type instead walks the type with `withRelatedTelescope`, which
introduces a representation wherever the type binds one. Which binders those are is
a `RepresentationSelection`.

## Universe parameters

The following notation describes sets of universe parameter names, ignoring the
discovery order and caches in `CollectLevelParams.State`:

* `U(e)` is the set of universe parameters occurring **syntactically** in `e`, as
  collected by `collectLevelParams`. It collects names such as `u` and `v` from
  levels such as `max u v`; it does not follow free variables to their types.
* `I(K)` is the set contributed by the index domains of a representation kind.
  Opening `K = (i₁ : D₁) → ... → (iₙ : Dₙ) → Sort ℓ` gives
  `I(K) = ⋃ⱼ U(Dⱼ)`, computed by `sharedIndexLevels`. Each domain is read with
  the preceding indices in scope. The final sort contributes nothing by itself:
  `I(Type u → Type v) = {u}`, and `I(Type u → Type u) = {u}` as well.
-/

namespace Tapas.LogicalRelation
open Lean Meta Utils

/-- Which binders of a type introduce a representation of their own.

The representation a relation starts from is chosen by the caller. This answers the
separate question of what happens further in, which arises because a type can bind
its own representation, as the type of a tagless final program does.

`select` is given a binder's name and its type. It answers `none` when the binder
is an ordinary one, and otherwise the kind at which to introduce the binder's two
interpretations. -/
structure RepresentationSelection where
  /-- Given a binder's name and its type, the kind at which to introduce that
  binder's two interpretations, or `none` when it is an ordinary binder. -/
  select : Name → Expr → MetaM (Option Expr)

-- FIXME: The `inferType` below might be optimized
/-- Run `k` on the two interpretations applied to a shared list of indices, once
the whole telescope has been opened. Both must end in a sort, and their index
domains must agree, since one list of indices stands for both. -/

/- NOTE: The indices are bound **strict implicit**, as are those of the aliases in
`Common/BaseRelationAliases.lean`, which have to match. What forces this is that a
generated relation is routinely passed on as a whole rather than applied: `C.Rel R`
recovers both representations from the type of `R` alone, and a relator such as
`ListRel` takes a relation as an argument.

An ordinary implicit index is instantiated as soon as the bare `R` is elaborated,
giving `R : repr ?i → repr' ?i → Prop` with `?i` created outside any binder. Fitting
that back under an expected `∀ {i}, ?repr i → ?repr' i → Prop` asks the unifier to
solve `?repr i =?= repr ?i`, which is not a pattern, so it takes the approximation
`?repr := fun i => repr ?i` and leaves `?i` unconstrained. Both representations then
read as constant functions of a metavariable that nothing will ever solve, and any
instance search over them is stuck. A strict implicit index is not instantiated until
the relation meets a value, so the bare `R` keeps its shape, the expected type matches
it structurally, and the representations come out as themselves.

Applying a relation is unaffected, since `R x y` takes the index from `x`. What needs
an annotation is handing one to something that expects a relation at a single index,
as in `ListRel (R (α := α))`. -/
partial def withSharedIndices (source target : Expr)
    (k : Array Expr → Expr → Expr → MetaM Expr) : MetaM Expr := go #[] source target
where
  go (indices : Array Expr) (left right : Expr) : MetaM Expr := do
    match ← whnf (← inferType left), ← whnf (← inferType right) with
    | .forallE name dom _ _, .forallE _ dom' _ _ =>
      unless ← isDefEq dom dom' do
        throwError "logical relation: shared index domains differ:\n{dom}\nand\n{dom'}"
      withLocalDecl name .strictImplicit dom fun x => go (indices.push x) (mkApp left x) (mkApp right x)
    | .sort _, .sort _ => k indices left right
    | _, _ => throwError "logical relation: shared-index interpretation requires a parameter whose telescope ends in a sort"

/-- The type of the base relation between two interpretations, using a registered
abbreviation when one applies. -/
def sharedIndexRelation (source target : Expr) : MetaM Expr := do
  -- The complete type comes first; a name is only ever a way of displaying it.
  let generated ← withSharedIndices source target fun indices left right => do
    mkArrowN #[left, right] (mkSort .zero) >>= mkForallFVars indices
  aliasBaseRelation generated

/-- Accumulate the universe parameters shared by a representation's index domains:
`s.params ∪ I(kind)`. The final sort contributes no parameters of its own, though
its parameters may also occur in an index domain. -/
def sharedIndexLevels (kind : Expr) (s : CollectLevelParams.State := {}) :
    MetaM CollectLevelParams.State :=
  -- An index domain may mention earlier indices, so the telescope is opened rather
  -- than matched.
  forallTelescopeReducing kind fun indices result => do
    -- Ending in a sort is what makes "the values themselves" well defined.
    unless result.isSort do
      throwError "logical relation: shared-index interpretation requires a parameter whose telescope ends in a sort"
    indices.foldlM (fun s x => return collectLevelParams s (← inferType x)) s

/-- Accumulate the universe parameters to keep shared between the source and target
interpretations when preparing types for logical-relation translation.
This is typically for computing the `sharedLevels` to be passed into the other
functions in this file. -/
partial def sharedRepresentationLevels (representations : Array Expr) (type : Expr)
    (sharedLevels : CollectLevelParams.State) (selection : RepresentationSelection) : MetaM CollectLevelParams.State := do
  -- The shape forms of `T` follow `LogicalRelation.Translation`
  match ← whnf type with
  | .forallE name dom body bi =>
    if let some kind ← selection.select name dom then
      -- `T = (repr : K) → B`, with `repr` is a representation parameter
      let sharedLevels ← sharedIndexLevels kind sharedLevels
      withLocalDecl name bi kind fun x =>
        sharedRepresentationLevels (representations.push x) (body.instantiate1 x) sharedLevels selection
    else
      -- `T = (x : A) → B`, with `x` not selected: just recurse
      withLocalDecl name bi dom fun x => do
        sharedRepresentationLevels representations (body.instantiate1 x)
          (← sharedRepresentationLevels representations dom sharedLevels selection) selection
  | type =>
    let env ← getEnv
    let reprAppears := representations.any (·.occurs type)
    let typeFn := type.getAppFn'
    if reprAppears then
      if (representations.contains typeFn || typeFn.constName?.any (fun name =>
          isStructure env name &&
            ((getInterfaceRelation? env name).isSome
               /- NOTE: An interface relation takes precedence over a relator in this scan.
                  With neither registered, a structure is still scanned as an interface,
                  because order parameters such as `CCPO` and `MonoBind` are copied
                  without a relation and must not fix representation universes.
                  Requiring a registered interface relation here would instead collect the
                  structure's own universe arguments, unnecessarily fixing representation universes.
                  A structure with only a relator, such as `Prod`, must reach the recursive scan
                  below so that shared constraints inside lifted arguments are retained.
                  This classification does not guarantee that relation translation accepts the type. -/
              || (getRelator? env name).isNone))) then
        -- `T = repr is`, a value in a representation, or `T = D qs`, a structure
        -- mentioning a representation and handled as an interface dictionary
        return type.getAppArgs.foldl (init := sharedLevels) fun s arg =>
          if representations.any (·.occurs arg) then
            -- NOTE: Do not recurse here according to the applicability condition, see `README.md` for details
            s
          else collectLevelParams s arg
      if let some name := typeFn.constName? then
        if let some info := getRelator? env name then
          -- `T = F as`, mentioning a representation and using a registered relator
          let sharedLevels ← type.getAppArgs.zip info.relationParamIdxs |>.foldlM (init := sharedLevels) fun s (arg, lifted) => do
            if lifted.isSome
            then sharedRepresentationLevels representations arg s selection
            else pure (collectLevelParams s arg)
          return sharedLevels
    -- Independent leaves and unsupported shapes: conservatively retain all
    -- syntactically occurring universe parameters.
    return collectLevelParams sharedLevels type

/-- Introduce the second interpretation of the representation parameter `repr` and
their base relation, then run `k` with both and with the level renaming.

`sharedLevels` records additional universe parameters that both interpretations
must share; those required by the representation's indices are included automatically.
`notFreshLevels` records the universe parameter names that fresh names must avoid. -/
def withRelatedRepresentation {α : Type} (repr : Expr)
    (sharedLevels notFreshLevels : CollectLevelParams.State)
    (k : Expr → Expr → (Expr → Expr) → MetaM α) : MetaM α := do
  let kind := (← inferType repr).cleanupAnnotations
  let sharedLevels ← sharedIndexLevels kind sharedLevels
  -- FIXME: This really should have a more efficient and possibly shorter implementation,
  -- based on the check in `sharedIndexLevels`
  let sourceLevels := (collectLevelParams {} kind).params
  /- Given `kind = (i₁ : D₁) → ... → (iₙ : Dₙ) → Sort ℓ`, this computes a substitution
  for certain level parameters in `ℓ` into **fresh** ones that are not in `notFreshLevels`.
  Those level parameters should satisfy that they are not in `sharedLevels ∪ I(K)`. -/
  let targetLevels := renameLevelParams sourceLevels sharedLevels notFreshLevels
  let targetType := kind.instantiateLevelParamsArray sourceLevels targetLevels
  -- Introduce the second interpretation of the representation parameter
  withLocalDecl (← repr.fvarId!.getUserName <&> (·.appendAfter "'")) .implicit targetType
      fun target => do
    let relation ← sharedIndexRelation repr target
    -- Introduce the base relation
    withLocalDeclD `R relation fun rel =>
      k target rel (·.instantiateLevelParamsArray sourceLevels targetLevels)

end Tapas.LogicalRelation
