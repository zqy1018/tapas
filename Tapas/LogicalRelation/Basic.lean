import Lean

/-!
The computation relation, and the two persistent tables that `operationRelation`
consults: the relations generated for capabilities, and the relators registered
with `@[effect_relator]`.

## Relators

A relator for a type constructor `F` lifts relations on its arguments to a
relation on `F`, e.g. `Option.Rel : (α → β → Prop) → Option α → Option β → Prop`.
`@[effect_relator]` registers one in a persistent table keyed by `F`; see
`registerEffectRelator` for the accepted shapes. Registering a second relator for
a type constructor that already has a visible one is an error.
Arguments the relator does not lift are shared, as in a relator for
`Except ε α` that only lifts `α`. `LogicalRelation.Relators` registers relators
for common data types.
-/

namespace Tapas.LogicalRelation

open Lean Meta

/-- The relation preserves the value type, but may change the computation universe. -/
abbrev ComputationRelation (m : Type u → Type v) (n : Type u → Type w) :=
  {α : Type u} → m α → n α → Prop

/-- Metadata for consumers of a generated capability relation. -/
structure EffectRelationInfo where
  /-- Fully qualified name of the original capability class. -/
  capability : Name
  /-- Zero-based index of the selected monad in the class parameters, including implicit ones. -/
  monadParam : Nat
  /-- Fully qualified name of the generated relation class, `capability.Rel`. -/
  relation : Name
  /-- Unqualified operation field names in constructor order, with inherited fields flattened
  and parent subobjects omitted. -/
  fields : Array Name
  deriving Inhabited

initialize effectRelationExt : SimplePersistentEnvExtension EffectRelationInfo
    (NameMap EffectRelationInfo) ← registerSimplePersistentEnvExtension {
  addEntryFn := fun s info => s.insert info.capability info
  addImportedFn := fun entries => entries.foldl (fun s es =>
    es.foldl (fun s info => s.insert info.capability info) s) {}
}

/-- Look up a successfully generated relation, including relations from imported modules. -/
def getEffectRelation? (env : Environment) (capability : Name) : Option EffectRelationInfo :=
  effectRelationExt.getState env |>.find? capability

/-- A registered relator, which lifts relations through the arguments of a type constructor. -/
structure EffectRelatorInfo where
  /-- Fully qualified name of the type constructor, e.g. `Option`. -/
  typeConstructor : Name
  /-- Fully qualified name of the relator, e.g. `Option.Rel`. -/
  relator : Name
  /-- For each argument of the type constructor, the index of the relator parameter that
  takes the relation for it, or `none` if both sides share the argument. -/
  relationParams : Array (Option Nat)
  /-- Number of relator parameters, including the two related values at the end. -/
  numParams : Nat
  deriving Inhabited

initialize effectRelatorExt : SimplePersistentEnvExtension EffectRelatorInfo
    (NameMap EffectRelatorInfo) ← registerSimplePersistentEnvExtension {
  addEntryFn := fun s info => s.insert info.typeConstructor info
  addImportedFn := mkStateFromImportedEntries (fun s info => s.insert info.typeConstructor info) {}
}

/-- Look up the relator registered for a type constructor, including imported registrations. -/
def getEffectRelator? (env : Environment) (typeConstructor : Name) : Option EffectRelatorInfo :=
  effectRelatorExt.getState env |>.find? typeConstructor

/-- Register `relator : ∀ ps, F as → F bs → Prop` as the relator for `F`.

Each argument position `i` of `F` is either shared, when `asᵢ` and `bsᵢ` are the same
parameter, or lifted: then exactly one parameter must have type `asᵢ → bsᵢ → Prop`,
and it receives the relation for that argument. For example `Option.Rel` lifts the
only argument of `Option`. At most one relator can be registered per type constructor.

The computation universe of the two monads may differ, so a lifted argument should
be allowed to live in different universes on the two sides, as in `Option.Rel`
(`{α : Type u_1} {β : Type u_2}`). -/
def registerEffectRelator (relator : Name) : MetaM Unit := do
  let info ← getConstInfo relator
  let entry ← forallTelescopeReducing info.type fun xs body => do
    let shapeError := m!"effect relation: relator {relator} must have type `… → F α … → F β … → Prop`"
    unless body.isProp && xs.size ≥ 2 do throwError shapeError
    let leftType := (← inferType xs[xs.size - 2]!).cleanupAnnotations
    let rightType := (← inferType xs[xs.size - 1]!).cleanupAnnotations
    let some typeConstructor := leftType.getAppFn.constName? | throwError shapeError
    unless rightType.getAppFn.constName? == some typeConstructor &&
        leftType.getAppNumArgs == rightType.getAppNumArgs do
      throwError shapeError
    let mut relationParams := #[]
    for a in leftType.getAppArgs, b in rightType.getAppArgs do
      if a == b then
        relationParams := relationParams.push none
      else
        let mut candidates := #[]
        for i in [:xs.size - 2] do
          if let .forallE _ a' (.forallE _ b' (.sort .zero) _) _ ← inferType xs[i]! then
            if a' == a && b' == b then candidates := candidates.push i
        let #[i] := candidates
          | throwError "effect relation: relator {relator} must take exactly one relation of type{indentExpr (← mkArrow a (← mkArrow b (mkSort .zero)))}"
        relationParams := relationParams.push (some i)
    return { typeConstructor, relator, relationParams, numParams := xs.size : EffectRelatorInfo }
  if let some existing := getEffectRelator? (← getEnv) entry.typeConstructor then
    throwError "effect relation: relator {existing.relator} is already registered for {entry.typeConstructor}"
  modifyEnv fun env => effectRelatorExt.addEntry env entry

/-- `@[effect_relator]` registers a relator for `derive_effect_rel`; see `registerEffectRelator`. -/
initialize registerBuiltinAttribute {
  name := `effect_relator
  descr := "relator lifting relations through a type constructor, used by `derive_effect_rel`"
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do
      throwError "effect relation: relators can only be registered globally"
    MetaM.run' <| registerEffectRelator decl
}

end Tapas.LogicalRelation
