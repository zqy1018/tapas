module

public meta import Lean
import Std.Tactic.BVDecide.Normalize.Prop
import Lean.Exception

public meta section

/-!
The two persistent tables that `relationAt` consults.

That recursion decomposes a type structurally. On reaching a head symbol it cannot
decompose further it looks the relation up here rather than inventing one, and
reports an error when no entry exists. The tables differ only in what an entry is
attached to and where it comes from:

|             | relator                    | interface relation                               |
| attached to | a type constructor `F`     | an interface `C`, a structure of operations      |
| entry       | `RelatorInfo`              | `InterfaceRelationInfo`                          |
| supplied by | the user, via `@[relator]` | `derive_interface_rel`, recording its own result |

Entries survive module import, so a relation derived in one module is reused by
derivations in another.

## Relators

A relator for a type constructor `F` lifts relations on its arguments to a
relation on `F`, e.g. `Option.Rel : (α → β → Prop) → Option α → Option β → Prop`.
`@[relator]` registers one in a persistent table keyed by `F`; see
`registerRelator` for the accepted shapes. Registering a second relator for
a type constructor that already has a visible one is an error.
Arguments the relator does not lift are shared, as in a relator for
`Except ε α` that only lifts `α`. `LogicalRelation.Relators` registers relators
for common data types.
-/

namespace Tapas.LogicalRelation

open Lean Meta

/-- Metadata for consumers of a generated interface relation. -/
structure InterfaceRelationInfo where
  /-- Fully qualified name of the interface the relation was generated from. -/
  interfaceName : Name
  /-- Zero-based index of the selected representation among the class parameters,
  counting implicit ones. -/
  reprParamIdx : Nat
  /-- Fully qualified name of the generated relation class, `interfaceName.Rel`. -/
  relation : Name
  /-- Unqualified operation field names in constructor order, with inherited fields flattened
  and parent subobjects omitted. -/
  fields : Array Name
  deriving Inhabited

initialize interfaceRelationExt : SimplePersistentEnvExtension InterfaceRelationInfo
    (NameMap InterfaceRelationInfo) ← registerSimplePersistentEnvExtension {
  addEntryFn := fun s info => s.insert info.interfaceName info
  addImportedFn := fun entries => entries.foldl (fun s es =>
    es.foldl (fun s info => s.insert info.interfaceName info) s) {}
}

/-- Look up a successfully generated relation, including relations from imported modules. -/
def getInterfaceRelation? (env : Environment) (interfaceName : Name) : Option InterfaceRelationInfo :=
  interfaceRelationExt.getState env |>.find? interfaceName

/-- The convention of building the parameter layout for an interface relation. -/
def interfaceRelationParamsLayout (existingParams : Array Expr)
    (repr' rel left right : Expr) : Array Expr :=
  existingParams ++ #[repr', rel, left, right]

/-- A registered relator, which lifts relations through the arguments of a type constructor. -/
structure RelatorInfo where
  /-- Fully qualified name of the type constructor, e.g. `Option`. -/
  typeConstructor : Name
  /-- Fully qualified name of the relator, e.g. `Option.Rel`. -/
  relator : Name
  /-- For each argument of the type constructor, the index of the relator parameter that
  takes the relation for it, or `none` if both sides share the argument. -/
  relationParamIdxs : Array (Option Nat)
  /-- Number of relator parameters, including the two related values at the end. -/
  numParams : Nat
  deriving Inhabited

private initialize relatorExt : SimplePersistentEnvExtension RelatorInfo
    (NameMap RelatorInfo) ← registerSimplePersistentEnvExtension {
  addEntryFn := fun s info => s.insert info.typeConstructor info
  addImportedFn := mkStateFromImportedEntries (fun s info => s.insert info.typeConstructor info) {}
}

/-- Look up the relator registered for a type constructor, including imported registrations. -/
def getRelator? (env : Environment) (typeConstructor : Name) : Option RelatorInfo :=
  relatorExt.getState env |>.find? typeConstructor

/-- Register `relator : ∀ ps, F as → F bs → Prop` as the relator for `F`.

Each argument position `i` of `F` is either shared, when `asᵢ` and `bsᵢ` are the same
parameter, or lifted: then exactly one parameter must have type `asᵢ → bsᵢ → Prop`,
and it receives the relation for that argument. For example `Option.Rel` lifts the
only argument of `Option`. At most one relator can be registered per type constructor.

The universes of the two representations may differ, so a lifted argument should
be allowed to live in different universes on the two sides, as in `Option.Rel`
(`{α : Type u_1} {β : Type u_2}`). -/
def registerRelator (relator : Name) : MetaM Unit := do
  let info ← getConstInfo relator
  let entry ← forallTelescopeReducing info.type fun xs body => do
    let shapeError := m!"logical relation: relator {relator} must have type `… → F α … → F β … → Prop`"
    unless body.isProp do throwError shapeError
    if h : xs.size < 2
    then throwError shapeError
    else
      let leftType := (← inferType xs[xs.size - 2]).cleanupAnnotations
      let rightType := (← inferType xs[xs.size - 1]).cleanupAnnotations
      let some typeConstructor := leftType.getAppFn.constName? | throwError shapeError
      unless rightType.getAppFn.constName? == some typeConstructor &&
          leftType.getAppNumArgs == rightType.getAppNumArgs do
        throwError shapeError
      -- Classify each argument position of `F` by comparing the two sides. Both
      -- argument lists are expressed in the relator's own binders, so a shared
      -- position is literally the same fvar twice and a lifted one is two
      -- different fvars. `applyRelator` consumes the classification positionally.
      let mut relationParamIdxs := #[]
      for a in leftType.getAppArgs, b in rightType.getAppArgs do
        if a == b then
          -- Shared: both interpretations receive this argument unchanged, so no
          -- parameter carries a relation for it.
          relationParamIdxs := relationParamIdxs.push none
        else
          -- Lifted: locate the parameter that takes the relation between the two
          -- sides. Searching by type rather than by position lets a relator order
          -- its parameters freely; `xs.size - 2` drops the two related values.
          let mut candidates := #[]
          for h' : i in [:xs.size - 2] do
            have h'' : i < xs.size := by simp [Membership.mem] at h' ; omega
            -- A non-dependent `a' → b' → Prop`, where `.sort .zero` is `Prop`.
            -- FIXME: Might need a better check here, e.g., using `isDefEq` instead of `==`
            if let .forallE _ a' (.forallE _ b' (.sort .zero) _) _ ← inferType xs[i] then
              if a' == a && b' == b then candidates := candidates.push i
          -- Exactly one is required in both directions: with none the relator fails
          -- to lift a position whose two sides differ, and with several the index
          -- recorded here, and hence the parameter `applyRelator` fills, would be an
          -- arbitrary choice.
          let #[i] := candidates
            | throwError "logical relation: relator {relator} must take exactly one relation of type{indentExpr (← mkArrow a (← mkArrow b (mkSort .zero)))}"
          relationParamIdxs := relationParamIdxs.push (some i)
      return { typeConstructor, relator, relationParamIdxs, numParams := xs.size : RelatorInfo }
  if let some existing := getRelator? (← getEnv) entry.typeConstructor then
    throwError "logical relation: relator {existing.relator} is already registered for {entry.typeConstructor}"
  modifyEnv fun env => relatorExt.addEntry env entry

/-- `@[relator]` registers a relator for the relation generators; see
`registerRelator`. -/
initialize registerBuiltinAttribute {
  name := `relator
  descr := "relator lifting relations through a type constructor, used when generating relations"
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do
      throwError "logical relation: relators can only be registered globally"
    MetaM.run' <| registerRelator decl
}

end Tapas.LogicalRelation
