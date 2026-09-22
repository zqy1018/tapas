module

public import Tapas.TaglessFinal.Inference
public import Tapas.TaglessFinal.LeanInternals
import Lean.Elab.DefView

public meta section

/-!
Infer the typeclass instance parameters of a *declaration*, including a recursive one.

`infer_final%` and `infer_effects%` are term elaborators, so they apply to a definition whose
value is one term. A recursive definition is not: `termination_by`, `decreasing_by`, `mutual`,
`partial`, `partial_fixpoint` and `where` belong to the `def` command, and a term elaborator
never sees them. Nor can the restriction be worked around inside a term, because recursion needs
a signature before the body while inference reads the signature off the body, and a recursive
occurrence needs its instance arguments at the use site.

`addInferredDefinitions` is the command-level mechanism that resolves this, and `infer_final` is
its general frontend, as `infer_effects` is the monadic one. It elaborates each body once, with
the function bound as an ordinary local hypothesis carrying the signature as written, collects
the instance arguments the bodies leave unresolved, abstracts them into every signature in the
block, and hands the result to Lean's own `addPreDefinitions`. Structural and
well-founded recursion, `mutual`, `partial`, `partial_fixpoint`, `where` and `let rec` follow
from that last step rather than needing anything of their own.

## Why one elaboration suffices

The local hypothesis standing for a recursive occurrence carries the signature *without* the
inferred parameters, so a recursive call contributes no instance argument of its own. The
constraints collected are therefore exactly those of the block's non-recursive operations, and
the finished signature binds exactly those. Under it, a recursive occurrence needs the very
dictionaries the enclosing function binds, which are in scope there; passing them is what
`MutualClosure` already does with section variables. The collected set is thus a fixed point by
construction, and no second pass can find more.

A `mutual` block settles one shared set for all of its functions. Splitting it per function would
mean a fixpoint over the call graph, and would still have to close a caller's set over its
callees'; one shared set is what the recursive occurrences can always supply.

## How the inferred parameters reach every declaration

The collected constraints are turned into ordinary local hypotheses and passed to
`Lean.Elab.Term.MutualClosure.main` as *section variables*, after the section variables the block
really uses. `MutualClosure` then treats them as it treats any variable the block is elaborated
under:

* each main definition's signature gains them, and every recursive occurrence -- an
  `withAuxDecl` free variable until this point -- becomes the constant applied to them;
* each `where` or `let rec` helper is lifted with the ones it uses, by the free-variable fixpoint
  `MutualClosure` computes for the group anyway.

The helpers are elaborated before the hypotheses exist, so the local context recorded for each
lifted function is extended with them first; otherwise the fixpoint would discard them as
out of scope and leave the lifted body with a free variable.

## Boundaries

An inferred constraint becomes a parameter of the *signature*, which is built outside every body.
A constraint mentioning a definition's own parameter is generalized over it, so
`Indexed k m` under `(k : Nat)` becomes the parameter `[(k : Nat) → Indexed k m]`. One mentioning
something only a body has in scope -- a `where` helper's view of its parent's parameters, or a
recursive occurrence -- cannot be, and is reported.

A section variable is kept when the block uses it, transitively, which is the rule the `def`
command uses for definitions. `include` and `omit` are not consulted.

This module decides which arguments become parameters and where they are bound. It does not
choose a logical relation or prove parametricity; those operations consume the resulting
declarations in their own modules.
-/

/- NOTE: The alternative is to reach declaration level through the *delaborator*: infer the
instance types, print them back into binder syntax, and re-issue the declaration for Lean to
elaborate a second time. Veil, which `abstractTCArgsCore` and `simplifyAndAbstractMVar` come
from, does that, and has to emit an `abbrev` for each inferred type first to avoid delaboration
round-trips that can fail or be slow; Mathlib's `variable?` does the same one binder at a time
and states outright that it does not guarantee the result. Elaborating once and abstracting the
metavariables in place avoids both the round-trip and the second elaboration of `where` and
`let rec` helpers. -/

/- NOTE: The `def` command's own pipeline cannot be reused as it stands: header elaboration,
value elaboration, closure construction and `addPreDefinitions` sit inside one `private` block of
`Lean.Elab.Term.elabMutualDef`, with no seam between the elaborated values and the
`PreDefinition`s -- which is exactly where the collected constraints have to be abstracted. The
steps around that seam are reproduced in `Tapas.TaglessFinal.LeanInternals`, one definition per
private original; what is left here is the inference itself. -/

namespace TaglessFinal

open Lean Elab Command Term Meta LeanInternals

-- A frontend deciding whether a parameter it offers is required by the recursion itself, rather
-- than by anything in a body, reads the termination hints; it should not have to know where the
-- reader lives.
export LeanInternals (declValTerminationHints)

/- A lifted `where` or `let rec` function closes over the free variables it uses, chosen from the
local context recorded when its body was elaborated. The inferred hypotheses are created after
that, so without this they would be filtered out as out of scope and the lifted body would keep a
free variable the kernel rejects.

`addDecl` renumbers each declaration to the end of the context it joins, so the hypotheses stay
last in the closure's binder order and may depend on everything already there. Its CPS sibling
`withExistingLocalDecls` does not fit: what is needed is a context to store back into
`LetRecToLift.lctx`, not one to run something in. -/
/-- Add `fvars` to the local context recorded for each lifted function. -/
private def extendLiftedContexts (letRecsToLift : List LetRecToLift) (fvars : Array Expr) :
    MetaM (List LetRecToLift) :=
  letRecsToLift.mapM fun toLift => do
    let mut lctx := toLift.lctx
    for fvar in fvars do
      unless lctx.contains fvar.fvarId! do
        lctx := lctx.addDecl (← fvar.fvarId!.getDecl)
    return { toLift with lctx }

private partial def withConstraintHypotheses (args : Array AbstractTCArg)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  /- NOTE: `Meta.withLocalDecls` cannot do this: it computes each binder's type from the hypotheses
  introduced so far, but gives no chance to *assign* a metavariable in between. Introducing all of
  them first and assigning afterwards would leave each hypothesis's recorded type mentioning the
  metavariables rather than the hypotheses. Hence the explicit loop, which is also how Lean's own
  `withFunLocalDecls` introduces the declarations of a `mutual` block.

  `args` is ordered so that a constraint occurring in another's type comes first, so instantiating
  one type after assigning the previous hypotheses is what makes a dependent constraint refer to
  the hypothesis rather than to the metavariable it replaced. -/
  let rec loop (i : Nat) (constraints : Array Expr) : TermElabM α := do
    if h : i < args.size then
      let arg := args[i]
      withLocalDecl (← arg.mvar.mvarId!.getDecl).userName .instImplicit (← instantiateMVars arg.type) fun constraint => do
        arg.mvar.mvarId!.assign constraint
        loop (i + 1) (constraints.push constraint)
    else
      k constraints
  loop 0 #[]

/- The variable is by definition not in the local context the signature is built in, so the
message is rendered in whichever recorded context does name it. -/
/-- Report an inferred constraint that cannot become a parameter of the signature. -/
private def throwLocalConstraint (type : Expr) (fvarId : FVarId)
    (contexts : Array LocalContext) : TermElabM α := do
  let lctx := contexts.find? (·.contains fvarId) |>.getD (← getLCtx)
  withLCtx lctx {} <|
    throwError m!"interface inference: the inferred requirement{indentExpr type}\n\
      mentions `{Expr.fvar fvarId}`, which is local to a body of this block and so cannot appear \
      in a signature. Write the requirement out as a binder instead."

/-- Elaborate `views` as one block of (mutually) recursive definitions and add them to the
environment, abstracting the instance arguments their bodies leave unresolved.

`params` are the parameters the constraints are selected by, already introduced by the caller
along with any local instances to use; they are bound by every signature. `optParams` are bound
only where the block uses them. `vars` are the section variables in scope, kept by the same rule.

A constraint qualifies when its head is a class and `select` accepts its type; `selected` names
that choice for the error message reporting a constraint that was not abstracted. `post` is
applied to each elaborated value before the constraints are collected, which is how a frontend
spends a local instance it introduced only for elaboration. `defaultDefType` stands in for the
`:` part of a definition that writes none, which is how a frontend says what shape such a body
has; without it that part is an ordinary hole for the body to determine. `nameGen` names the
generated binders.

The resulting signatures bind, in order: the section variables used, `params`, the `optParams`
used, the inferred constraints as instance-implicit parameters, and then the parameters each
definition writes itself. -/
def addInferredDefinitions (views : Array DefView) (vars : Array Expr)
    (params : Array Expr) (select : Expr → Bool)
    (optParams : Array Expr := #[])
    (selected : MessageData := m!"a selected parameter")
    (post : Expr → TermElabM Expr := pure)
    (defaultDefType : Option (TermElabM Expr) := none)
    (nameGen : String := "interface") : TermElabM Unit := do
  let isInterface := isInterfaceConstraint (← getEnv) select

  -- From Lean: how `elabMutualDef` opens, and the forbidden-name predicate `elabHeaders` guards
  -- auto-bound implicits with, so that a definition's own name in a signature is an error rather
  -- than a new parameter.
  -- NOTE: The ref is the `declId` rather than the `headerRef` this module has no use for.
  let expanded ← views.mapM fun view => withRef view.declId do
    Term.expandDeclId (← getCurrNamespace) (← getLevelNames) view.declId view.modifiers
  for view in views, declId in expanded do
    match view.modifiers.computeKind with
    | .meta => modifyEnv (markMeta · declId.declName)
    | .noncomputable => modifyEnv (addNoncomputable · declId.declName)
    | .regular => pure ()
  withExporting (isExporting := expanded.any (!isPrivateName ·.declName)) do
  let headers ← (views.zip expanded).mapM fun (view, declId) =>
    elabDefHeader declId view (fun n => expanded.any (·.shortName == n)) defaultDefType
  -- End from Lean.

  -- As in `elabMutualDef`, check public signatures before making unexposed bodies private.
  withoutExporting (when := headers.all fun header =>
    header.modifiers.anyAttr (·.name == `no_expose) ||
      !(header.kind == .abbrev || header.kind == .instance ||
        header.modifiers.anyAttr (·.name == `expose))) do
  let headers := headers.map fun header =>
    { header with modifiers.attrs := header.modifiers.attrs.filter (!·.name ∈ [`expose, `no_expose]) }
  withFunLocalDecls headers fun recFVars => do

    -- From Lean: the core of the private `elabFunValues` in `Lean/Elab/MutualDef.lean`, with the
    -- tolerant synthesis in place of its `synthesizeSyntheticMVarsNoPostponing` and `post`
    -- applied to the result. Dropped: the incrementality snapshots, the `cleanupAnnotations` pass
    -- over the local context, the `withInfoContext'` body node, the after-the-fact check of an
    -- elided type, and the unused-section-variable linter.
    let values ← withTolerantElaboration <| headers.mapM fun header =>
      withDeclName header.declName <| withLevelNames header.levelNames do
        let valStx ← declValToTerm header.value header.type
        forallBoundedTelescope header.type header.numParams (cleanupAnnotations := true)
          fun xs type => do
            -- Relating each binder to the syntax it came from is what hovers, go-to-definition
            -- and the unused-variable linter read.
            for h : i in *...header.binderIds.size do
              addLocalVarInfo header.binderIds[i] xs[header.numParams - header.binderIds.size + i]!
            let value ← Term.elabTermEnsuringType valStx type
            Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
            post (← Meta.mkLambdaFVars xs value)
    -- End from Lean.

    -- A `where` or `let rec` helper's body is held aside for lifting, so its own constraints are
    -- collected from there rather than from the value that will be lifted around it.
    let letRecs := (← getLetRecsToLift).toArray
    let elaborated := values ++ headers.map (·.type) ++ letRecs.map (·.val) ++ letRecs.map (·.type)
    let args ← abstractTCMVars elaborated isInterface nameGen { simplifyType := true }
    -- The placeholder standing for such a helper is resolved by `MutualClosure` below rather
    -- than by inference, so it is not an unresolved argument. Abstracting a value over its
    -- parameters replaces the placeholder by a delayed assignment applied to them, which is why
    -- the test is on the **root** of that chain rather than on the placeholder itself.
    let placeholders := letRecs.map (·.mvarId)
    let args ← refineConstraints isInterface selected args elaborated
      (ignored := fun mvarId => do pure <| placeholders.contains (← getDelayedMVarRoot mvarId))
    /- NOTE: The constraints are about to become binders of a signature, which is built in the local
    context outside every body, so their types may not mention anything a body binds.

    A definition's own parameters are not a problem. The `mkLambdaFVars xs` above abstracts its
    value over them, and that generalizes the constraints along with it: `Indexed k m` under
    `(k : Nat)` becomes the parameter `(k : Nat) → Indexed k m`. A `where` or `let rec` helper's
    body is held aside in `letRecsToLift` and never abstracted that way, so a constraint it
    leaves can still mention the *parent's* parameters:
    ```
    def atIndex (k : Nat) : Nat → m Nat
      | 0 => go 3
      | j + 1 => atIndex k j
    where
      go : Nat → m Nat
        | 0 => Indexed.peek (n := k)
        | i + 1 => go i
    ```
    `go` needs `Indexed k m` for `atIndex`'s `k`, which is not in scope where the signature is
    built. Left alone, `mkForallFVars` would produce a binder holding a free variable nothing
    binds, and the kernel would report `unknown free variable`; reporting it here names the
    requirement and the variable instead. A recursive occurrence is rejected for the same reason:
    it *is* in the local context, but `MutualClosure` is about to replace it by the constant
    being declared. -/
    let lctx ← getLCtx
    for arg in args do
      let type ← instantiateMVars arg.type
      for fvarId in (Lean.collectFVars {} type).fvarIds do
        if recFVars.contains (.fvar fvarId) || !lctx.contains fvarId then
          throwLocalConstraint type fvarId (letRecs.map (·.lctx))
    /- This is the first half of what `mkLambdaFVars (binderInfoForMVars := .instImplicit)` does for a
    term in `inferInterfaceBody` and `abstractTCargs%`: give each metavariable a binder of its own.
    The second half, abstracting the occurrences, is left to `MutualClosure`, which does it with
    `mkLambdaFVars sectionVars` over every declaration of the block at once -- and, for a `where` or
    `let rec` helper, over the subset that helper actually uses. One `mkLambdaFVars` cannot serve
    several declarations, which is why the two halves come apart here. -/
    withConstraintHypotheses args fun constraints => do
      let values ← values.mapM instantiateMVars
      let mut seed := values ++ headers.map (·.type) ++ letRecs.map (·.type)
      for param in params ++ constraints do
        seed := seed.push (← param.fvarId!.getType)
      let kept ← keepUsedParams (vars ++ optParams) seed
      let sectionVars := kept.filter (vars.contains ·) ++ params ++ kept.filter (optParams.contains ·) ++ constraints
      let letRecsToLift ← extendLiftedContexts letRecs.toList constraints
      addMutualPreDefinitions sectionVars headers recFVars values letRecsToLift

/-- The definitions of `stx`, which is either one `def`-like declaration or a `mutual` block of
them. -/
def inferredDeclViews (stx : Syntax) : CommandElabM (Array DefView) := do
  let scope ← getScope
  withExporting (isExporting := scope.isPublic) do
  let elems := if stx.isOfKind ``Parser.Command.mutual then stx[1].getArgs else #[stx]
  elems.mapM fun elem => do
    -- Adapted from `isMutualDefLike` in `Lean/Elab/Declaration.lean`
    unless elem.isOfKind ``Parser.Command.declaration && isDefLike elem[1] do
      throwErrorAt elem "interface inference applies to a definition or a `mutual` block of \
        definitions"

    -- From Lean: the view-building half of `elabMutualDef` in `Lean/Elab/MutualDef.lean`
    -- without incrementality promises and `markDefEq` for a `:= rfl` body.
    let modifiers ← elabModifiers ⟨elem[0]⟩
    -- Preserve the command's visibility when its views enter `TermElabM`.
    let visibility := if modifiers.isInferredPublic (← getEnv) then .public else .private
    let modifiers := { modifiers with visibility }
    if elems.size > 1 && modifiers.isNonrec then
      throwErrorAt elem "invalid use of 'nonrec' modifier in 'mutual' block"
    let mut view ← withExporting (isExporting := modifiers.isPublic) do
      mkDefView modifiers elem[1]
    if view.kind == .def && (!view.modifiers.isMeta || scope.isMeta) &&
        scope.attrs.any (· matches `(Parser.Term.attrInstance| expose)) &&
        !view.modifiers.anyAttr (·.name ∈ [`expose, `no_expose]) then
      let attr ← Elab.elabAttr (← `(Parser.Term.attrInstance| expose))
      view := { view with modifiers.attrs := view.modifiers.attrs.push attr }
    -- End from Lean.

    -- `deriving` runs after the declaration is added, which this command does not reach.
    if view.deriving?.isSome then
      throwErrorAt elem "interface inference does not support a `deriving` clause"
    pure view

/-- `infer_final (A : kindA) (B : kindB) def f ...` infers the interface a *declaration* requires
of the named parameters.

It is `infer_final%` for a declaration rather than a term, so it reaches a recursive definition,
and a `mutual` block of them, which then share one set of interface parameters:

```lean
infer_final (A : Type u)
def evaluate (env : Nat → A) : Formula → A
  | .literal n => Arithmetic.literal n
  | .variable i => env i
  | .add lhs rhs => Arithmetic.add (evaluate env lhs) (evaluate env rhs)
-- {A : Type u} → [Arithmetic A] → (Nat → A) → Formula → A
```

The parameters are bound implicitly, in the order written, before the inferred constraints, and
each is introduced as a rigid local hypothesis; see `Tapas.TaglessFinal.Inference` for what that
means and why they are named rather than inferred. Kinds are arbitrary and may mention earlier
parameters. Unlike `infer_final%`, the result type is the one the definition writes. -/
syntax (name := inferFinalDeclStx) "infer_final " ("(" ident " : " term ")")+ command : command

@[command_elab inferFinalDeclStx]
def elabInferFinalDecl : CommandElab := fun stx => do
  let `(infer_final $[($names:ident : $kinds:term)]* $decl:command) := stx
    | throwUnsupportedSyntax
  let views ← inferredDeclViews decl
  runTermElabM fun vars =>
    withInferFinalConfig names kinds fun params select selected =>
      addInferredDefinitions views vars params select (selected := selected)

end TaglessFinal
