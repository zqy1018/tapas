import Tapas

namespace TapasTest

open Lean Elab Command

/-- Assert that each program has a registered parametricity theorem. -/
elab "#guard_parametric " programs:ident,+ : command => liftTermElabM do
  for program in programs.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo program
    if (Tapas.Parametricity.getParametricRules (← getEnv) name).isEmpty then
      throwErrorAt program "{name} has no registered parametricity theorem"

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
