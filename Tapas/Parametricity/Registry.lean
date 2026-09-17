import Lean

/-!
Parametricity rules available to subsequent derivations.

`derive_parametric p`, defined in `Tapas.Parametricity.Program`, generates and
registers `p.parametric`. `@[parametric]` or `attribute [parametric] h` registers
an existing theorem, inferring the program from its conclusion. Registrations are
global and survive module imports.
-/

namespace Tapas.Parametricity

open Lean Meta

initialize parametricExt : SimplePersistentEnvExtension (Name × Name)
    -- `Array Name` since for a single program there can be multiple parametricity theorems.
    (NameMap (Array Name)) ← do
  let addEntry : NameMap (Array Name) → Name × Name → NameMap (Array Name) := fun s (source, proof) =>
    let proofs := (s.find? source).getD #[]
    s.insert source (if proofs.contains proof then proofs else proofs.push proof)
  registerSimplePersistentEnvExtension {
    addEntryFn := addEntry
    addImportedFn := mkStateFromImportedEntries addEntry {}
  }

/-- Look up program translations, including hand-written and imported rules. -/
def getParametricRules (env : Environment) (source : Name) : Array Name :=
  (parametricExt.getState env |>.find? source).getD #[]

/-- Register a checked proof whose conclusion relates two applications of the same constant.
Its premises are checked when it is applied; no equivalence or functionality law
is required of the relation. -/
def registerParametric (proof : Name) : MetaM Unit := do
  let info ← getConstInfo proof
  unless ← isProp info.type do
    throwError "parametricity: {proof} is not a proof"
  let source ← forallTelescope info.type fun _ body => do
    let args := body.getAppArgs
    let shapeError := m!"parametricity: {proof} must conclude `R (f ...) (f ...)` for the same constant `f`"
    unless args.size ≥ 2 do throwError shapeError
    let some source := args[args.size - 2]!.getAppFn.constName?
      | throwError shapeError
    unless args[args.size - 1]!.getAppFn.constName? == some source do
      throwError shapeError
    return source
  modifyEnv fun env => parametricExt.addEntry env (source, proof)

/-- Register a hand-written program translation for subsequent derivations. -/
initialize registerBuiltinAttribute {
  name := `parametric
  descr := "parametricity theorem for subsequent derivations"
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do
      throwError "parametricity: parametricity theorems can only be registered globally"
    MetaM.run' <| registerParametric decl
}

end Tapas.Parametricity
