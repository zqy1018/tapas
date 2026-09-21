import Tapas

namespace TapasTest

open Lean Elab Command Term

/-- Assert that each program has a registered parametricity theorem. -/
elab "#guard_parametric " programs:ident,+ : command => liftTermElabM do
  for program in programs.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo program
    if (Tapas.Parametricity.getParametricRules (← getEnv) name).isEmpty then
      throwErrorAt program "{name} has no registered parametricity theorem"

/-- Assert that each program has neither a parametricity theorem nor a registry entry,
as a derivation that failed must leave behind. -/
elab "#guard_no_parametric " programs:ident,+ : command => liftTermElabM do
  for program in programs.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo program
    if (← getEnv).contains (name ++ `parametric) then
      throwErrorAt program "a failed derivation left the theorem {name ++ `parametric}"
    unless (Tapas.Parametricity.getParametricRules (← getEnv) name).isEmpty do
      throwErrorAt program "a failed derivation left a registry entry for {name}"

/-- Assert that each interface has neither a generated relation, nor one of the auxiliary
declarations that come with it, nor a registry entry. -/
elab "#guard_no_interface_rel " interfaces:ident,+ : command => liftTermElabM do
  for interface in interfaces.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo interface
    let relation := name ++ `Rel
    for leftover in [relation, relation ++ `mk, relation ++ `mk._flat_ctor, relation ++ `rec] do
      if (← getEnv).contains leftover then
        throwErrorAt interface "a failed generation left the declaration {leftover}"
    if (Tapas.LogicalRelation.getInterfaceRelation? (← getEnv) name).isSome then
      throwErrorAt interface "a failed generation left a registry entry for {name}"

/- `#guard_uses` reads a declaration's own value or type, not the declarations it reaches
through. A proof that delegates to an auxiliary declaration therefore does not mention what
that auxiliary one mentions. -/

/-- The expression `#guard_uses` scans, and the word naming it in an error message. -/
private def scannedExpr (inType : Bool) (decl : Ident) (name : Name) :
    TermElabM (Expr × String) := do
  let info ← getConstInfo name
  if inType then
    return (info.type, "type")
  let some value := info.value? (allowOpaque := true)
    | throwErrorAt decl "{name} has no value to scan"
  return (value, "value")

private def guardMentions (inType required : Bool) (decls constants : Array Ident) :
    TermElabM Unit := do
  let wanted ← constants.mapM fun constant => do
    return (constant, ← realizeGlobalConstNoOverloadWithInfo constant)
  for decl in decls do
    let name ← realizeGlobalConstNoOverloadWithInfo decl
    let (scanned, position) ← scannedExpr inType decl name
    for (stx, constant) in wanted do
      let occurs := (scanned.find? (·.isConstOf constant)).isSome
      if required && !occurs then
        throwErrorAt stx "the {position} of {name} does not mention {constant}"
      if !required && occurs then
        throwErrorAt stx "the {position} of {name} mentions {constant}"

/-- Assert that each declaration's value, or its type after `type`, mentions every listed
constant. -/
elab "#guard_uses " inType:(&"type")? decls:ident,+ " ⊇ " "[" constants:ident,* "]" : command =>
  liftTermElabM <| guardMentions inType.isSome true decls.getElems constants.getElems

/-- Assert that each declaration's value, or its type after `type`, mentions none of the
listed constants. -/
elab "#guard_uses " inType:(&"type")? decls:ident,+ " ∩ " "[" constants:ident,* "]" " = " "∅" :
    command =>
  liftTermElabM <| guardMentions inType.isSome false decls.getElems constants.getElems

/- `Expr.foldConsts` visits each constant once, so it cannot count occurrences. -/

/-- Occurrences of a constant in a term. Repeated subterms count separately, but a value the
term binds once and then uses through its variable counts once, which is what makes the number
a statement about sharing. -/
private partial def constOccurrences (name : Name) : Expr → Nat
  | .const n _ => if n == name then 1 else 0
  | .app f a => constOccurrences name f + constOccurrences name a
  | .lam _ t b _ | .forallE _ t b _ => constOccurrences name t + constOccurrences name b
  | .letE _ t v b _ => constOccurrences name t + constOccurrences name v + constOccurrences name b
  | .mdata _ e | .proj _ _ e => constOccurrences name e
  | _ => 0

/-- Assert that each declaration's value mentions every listed constant exactly this often. -/
elab "#guard_num_uses " decls:ident,+ " [" constants:ident,* "]" " = " count:num : command =>
  liftTermElabM do
    let expected := count.getNat
    let wanted ← constants.getElems.mapM fun constant =>
      return (constant, ← realizeGlobalConstNoOverloadWithInfo constant)
    for decl in decls.getElems do
      let name ← realizeGlobalConstNoOverloadWithInfo decl
      let some value := (← getConstInfo name).value? (allowOpaque := true)
        | throwErrorAt decl "{name} has no value to scan"
      for (stx, constant) in wanted do
        let occurrences := constOccurrences constant value
        unless occurrences == expected do
          throwErrorAt stx
            "the value of {name} mentions {constant} {occurrences} times, not {expected}"

/-- Assert that each declaration's value binds every listed name, which is how a local value or
a join point of the elaborated program survives into the generated proof. These are local binder
names rather than declarations, and are compared with macro scopes erased. -/
elab "#guard_binds " decls:ident,+ " ⊇ " "[" binders:ident,* "]" : command => liftTermElabM do
  for decl in decls.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo decl
    let some value := (← getConstInfo name).value? (allowOpaque := true)
      | throwErrorAt decl "{name} has no value to scan"
    for binder in binders.getElems do
      let bound := binder.getId
      let found := value.find? fun
        | .letE n .. => n.eraseMacroScopes == bound
        | _ => false
      if found.isNone then
        throwErrorAt binder "the value of {name} does not bind {bound}"

/-- Assert that each declaration's value has fewer than the given number of `Expr` objects.
Shared subexpressions count once. -/
elab "#guard_num_objs " decls:ident,+ " < " bound:num : command => liftTermElabM do
  for decl in decls.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo decl
    let some value := (← getConstInfo name).value? (allowOpaque := true)
      | throwErrorAt decl "{name} has no value to measure"
    let objs ← (value.numObjs : IO Nat)
    unless objs < bound.getNat do
      throwErrorAt decl "{name} has {objs} expression objects; expected fewer than {bound.getNat}"

/-- Assert that each declaration depends only on axioms from the given list. -/
elab "#guard_axioms " decls:ident,+ " ⊆ " "[" allowed:ident,* "]" : command => liftTermElabM do
  let allowed ← allowed.getElems.mapM fun ax => realizeGlobalConstNoOverloadWithInfo ax
  for decl in decls.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo decl
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwErrorAt decl "unexpected axioms in {name}: {unexpected}"

end TapasTest
