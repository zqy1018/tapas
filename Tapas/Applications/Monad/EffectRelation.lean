import Tapas.LogicalRelation

/-!
`derive_effect_rel`, the monadic entry to interface relations.

It is `derive_interface_rel` with one addition: given no selection at all, it guesses
that `C`'s unique parameter of monadic kind is the one to relate. Written out,
`(monad := ...)` takes the same rules as `(repr := ...)` and means the same thing, so
that guess is all the monadic spelling still carries.

It is also why the command stays. `typeConstructorUniverses?` matches a kind
`Sort (u+1) → Sort (v+1)` literally, and requiring that arity is what makes the choice
unique for a capability that also carries a state or an error: `MonadStateOf σ m` has
two parameters whose kinds end in a sort, and one of monadic kind. A default stated
generally enough for `derive_interface_rel` would be ambiguous there, where this one
is not.

The guess covers the interface's own parameter only. An operation may itself take a
monad-polymorphic program, and that binder has to be reached: `(monad := m, n)`, a
position, or a marker written in the declaration.
-/

namespace Tapas.LogicalRelation

open Lean Meta Elab Command Tapas Utils

/-- Pick the representation by monadic kind where the caller named none, and hand over
to `deriveInterfaceRelation`, which does the work. The general command always names
it. -/
def deriveEffectRelation (interfaceName : Name) (spec? : Option ReprSpec := none) : MetaM Unit := do
  let spec ← match spec? with
    | some spec => pure spec
    | none => do
      let idx ← forallTelescope (← getConstInfo interfaceName).type fun xs _ => do
        let candidates ← xs.zipIdx |>.filterM fun (x, _) => do
          pure (← typeConstructorUniverses? (← inferType x)).isSome
        let #[(_, idx)] := candidates
          | throwError "logical relation: select exactly one monad parameter with `(monad := name)`"
        pure idx
      pure { indices := #[idx] }
  deriveInterfaceRelation interfaceName (.markedOrNamed spec.names)
    (markOutermostBinders spec.indices)

/--
`derive_effect_rel C` generates `C.Rel` and a relation rule for every inherited
operation, guessing that `C`'s unique parameter of monadic kind is the one to relate.
Say which with `derive_effect_rel C (monad := n)` when `C` has several, and name an
operation's own monad alongside it, as in `(monad := m, n)`, to relate a program it
takes rather than share it.
-/
syntax (name := deriveEffectRel) "derive_effect_rel " ident
  (" (" &"monad" " := " Tapas.reprRule,+ ")")? : command

@[command_elab deriveEffectRel]
def elabDeriveEffectRel : CommandElab := fun stx => do
  let `(derive_effect_rel $interfaceName:ident $[(monad := $rules,*)]?) := stx
    | throwUnsupportedSyntax
  let spec? ← rules.mapM fun rules => elabReprRules rules.getElems
  liftTermElabM <| commitIfNoEx do
    deriveEffectRelation (← realizeGlobalConstNoOverloadWithInfo interfaceName) spec?

end Tapas.LogicalRelation
