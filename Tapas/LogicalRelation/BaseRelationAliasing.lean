import Lean

/-!
Optional names for already constructed base relation types.

`@[base_relation_alias]` registers a definition as a candidate abbreviation, with
an optional priority (default 1000). Higher priorities are tried first; ties are
ordered by fully qualified name. Registrations may be global, local, or scoped.
For example, a specialized monadic abbreviation can have higher priority than
one for arbitrary shared indices.

`aliasBaseRelation` uses a candidate only when its application is definitionally
equal to the given type and its arguments can be inferred. Otherwise it keeps the
original type. Registering a name does not change the interpretation of a relation
or rewrite declarations that have already been generated.
-/

namespace Tapas.LogicalRelation

open Lean Meta

private initialize baseRelationAliasExt :
    SimpleScopedEnvExtension (Name × Nat) (Array (Name × Nat)) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun entries entry =>
      ((entries.filter (·.1 != entry.1)).push entry).qsort fun a b =>
        if a.2 == b.2 then Name.lt a.1 b.1 else a.2 > b.2
  }

/-- Register an optional name for a base relation type, with an optional priority. -/
initialize registerBuiltinAttribute {
  name := `base_relation_alias
  descr := "abbreviation for a generated base relation type"
  add := fun decl stx kind => do
    let priority ← Attribute.Builtin.getPrio stx
    MetaM.run' do
      let info ← getConstInfo decl
      unless info.hasValue do
        throwError "logical relation: base relation alias {decl} must be a definition"
      forallTelescopeReducing info.type fun _ result => do
        unless result.isSort do
          throwError "logical relation: base relation alias {decl} must return a sort"
      baseRelationAliasExt.add (decl, priority) kind
}

/-- Abbreviate a base relation type with a registered name, or leave it unchanged. -/
def aliasBaseRelation (relation : Expr) : MetaM Expr := do
  let original ← getMCtx
  for (name, _) in baseRelationAliasExt.getState (← getEnv) do
    -- Each attempt can assign only its own metavariables, including universe
    -- metavariables. Leaving this scope restores the original context even on
    -- success, so the returned expression must be instantiated inside it.
    let named? ← withNewMCtxDepth <| observing? <| withDefault do
      let constant ← mkConstWithFreshMVarLevels name
      let (args, _, _) ← forallMetaTelescopeReducing (← inferType constant)
      let candidate := mkAppN constant args
      unless ← isDefEq relation candidate do failure
      let candidate ← instantiateMVars candidate
      -- Caller-owned metavariables may remain; an undetermined argument or
      -- universe created for this candidate may not escape the attempt.
      -- CHECK Is there a better way to do this check, from Lean's built-in stuff?
      unless (← getMVars candidate).all (fun id => original.decls.contains id) &&
          (collectLevelMVars {} candidate).result.all (fun id => original.lDecls.contains id) do
        failure
      return candidate
    if let some named := named? then return named
  return relation

end Tapas.LogicalRelation
