import Tapas.LogicalRelation.Representation

/-!
`RepresentationSelection` is the rule the translation consults. The translation itself
never looks at names or kinds, so a way of specifying a representation is a *rule* here
rather than a change to the backend.

`(repr := ...)` is the spelling the relation commands share. Each comma-separated item
is one rule, in the syntax category `Tapas.reprRule`, and a binder is a representation
when any of them selects it. Adding a way of saying which binders are representations
is a `syntax ... : Tapas.reprRule` and one case of `ReprSpec.add`; the commands do not
change.

Two rules are written, and a third is always on:

* a name, `A`, reaches every binder carrying it, at any depth of the type, which is
  enough whenever the binders meant to differ have different names, and is why a
  binder shadowing the one meant has to be renamed or told apart by position;
* a position, `1`, reaches that *outermost* binder whatever it is called, which is
  what tells two binders sharing a name apart, and what reaches one that has no name
  worth giving;
* a binder whose type the author wrapped in `relMarker` is selected either way, so a
  marker needs no syntax of its own. Identifying a binder by position rather than by
  name, it is the one rule that cannot select the wrong binder.

Without `(repr := ...)`, `derive_type_rel` uses `marked` alone, selecting nothing in a
declaration carrying no marker. `derive_interface_rel` requires the spec;
`derive_parametric` selects the first implicit parameter (`{...}` or `⦃...⦄`), skipping
explicit and instance parameters, and requires a spec if there is no implicit parameter.
-/

/- NOTE: The rules are told apart by the kind of their first token, a name from a
numeral, rather than by a leading keyword as Aesop's `safe`/`apply` features are.
A leading `&"index"` does not work: a non-reserved symbol is not entered in a syntax
category's leading-token table, so the alternative is never reached. Reserving `index`
would work and is what Aesop does for its own feature words, at the cost of taking the
word away from every user of this library. -/

namespace Tapas.LogicalRelation

open Lean Meta

/-- A marker that is definitionally the identity, like `outParam`, written around
the type of a binder to say that the binder is a representation. It survives
elaboration, so the generator can see it, and it disappears again when the binder
is reintroduced at the type it wraps. -/
abbrev relMarker (α : Sort u) : Sort u := α

/-- Select every binder whose type the caller wrapped in `relMarker`, at the type
it wraps. The only rule written on its own: selecting by name is what a spec's
`names` do, and selecting by position is `markOutermost` followed by this. -/
def RepresentationSelection.marked : RepresentationSelection :=
  ⟨fun _ kind => return if kind.isAppOf ``relMarker then kind.getAppArgs[0]? else Option.none⟩

/-- Which binders a `(repr := ...)` spec selects, by name and by position. -/
structure ReprSpec where
  /-- Binders selected by user name, wherever that name occurs. -/
  names : Array Name := #[]
  /-- Positions among the outermost binders, whatever those binders are called. -/
  indices : Array Nat := #[]
  deriving Inhabited

/-- One way of saying that a binder is a representation. -/
declare_syntax_cat Tapas.reprRule

/-- `A` selects every binder named `A`, at any depth of the type. -/
syntax (name := namedRule) ident : Tapas.reprRule
/-- `1` selects the outermost binder at that position, whatever it is called. -/
syntax (name := positionalRule) num : Tapas.reprRule

/-- `(repr := A, 1)`, the binders to relate. -/
syntax reprSpec := " (" &"repr" " := " Tapas.reprRule,+ ")"

/-- Record what one rule selects. -/
def ReprSpec.add [Monad m] [MonadError m] (spec : ReprSpec) :
    TSyntax `Tapas.reprRule → m ReprSpec
  | `(Tapas.reprRule| $name:ident) => return { spec with names := spec.names.push name.getId }
  | `(Tapas.reprRule| $i:num) => return { spec with indices := spec.indices.push i.getNat }
  | rule => throwErrorAt rule "logical relation: unknown representation rule"

/-- Read a list of rules. Commands spelling the list differently, such as the monadic
`(monad := ...)`, share this. -/
def elabReprRules [Monad m] [MonadError m] (rules : Array (TSyntax `Tapas.reprRule)) :
    m ReprSpec :=
  rules.foldlM ReprSpec.add {}

/-- Read a `(repr := ...)` spec. -/
def elabReprSpec [Monad m] [MonadError m] : TSyntax ``reprSpec → m ReprSpec
  | `(reprSpec| (repr := $rules,*)) => elabReprRules rules.getElems
  | spec => throwErrorAt spec "logical relation: expected `(repr := ...)`"

-- CHECK Maybe split this into an `orElse`?
/-- Select any binder named in `targets`, and any marked one. -/

/- NOTE: Reading the marker first is load-bearing rather than a preference. A rule
answers with the kind at which to introduce the binder's two interpretations, and only
`marked` hands back the type the marker wraps. Testing the name first on a binder that
is both marked and named would introduce it at `relMarker K`: definitionally the
intended kind, but printed and elaborated with the marker still around it. -/
def RepresentationSelection.markedOrNamed (targets : Array Name) : RepresentationSelection :=
  ⟨fun name kind => do
    if let some kind ← RepresentationSelection.marked.select name kind then
      return some kind
    return if targets.contains name then some kind else none⟩

/-- Mark the outermost binders of `type` at the given positions, so that a rule finds
them where a name cannot. No positions leaves the type unchanged. -/
partial def markOutermostBinders (indices : Array Nat) (type : Expr) : MetaM Expr := do
  if indices.isEmpty then return type
  let (marked, read) ← go (indices.max? |>.getD 0) 0 type
  if let some i := indices.find? (· ≥ read) then
    throwError "logical relation: no outermost binder at index {i}; there are {read}"
  return marked
where
  /- `read` counts the binders the walk got through. It is the whole spine only when the
  type ran out first, which is the one case the caller reports it in: stopping at `last`
  instead means every position asked for was reached. -/
  go (last i : Nat) (type : Expr) : MetaM (Expr × Nat) := do
    -- Nothing further is marked, so the rest of the spine is left as the declaration
    -- wrote it rather than reduced through to the end.
    if i > last then return (type, i)
    -- Up to there the spine is read as the translation reads it, through an alias to the
    -- binders behind it, so that a position means the same thing to both.
    let .forallE name dom body bi ← whnf type | return (type, i)
    let dom ← if indices.contains i then mkAppM ``relMarker #[dom] else pure dom
    withLocalDecl name bi dom fun x => do
      let (rest, read) ← go last (i + 1) (body.instantiate1 x)
      return (← mkForallFVars #[x] rest, read)

end Tapas.LogicalRelation
