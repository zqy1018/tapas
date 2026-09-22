module

public meta import Lean
import Lean.Elab.Term.TermElabM

public meta section

/-!
The parts of Lean's own `def` command that this library has to reproduce.

`Lean.Elab.Term.elabMutualDef` runs header elaboration, value elaboration, closure construction
and `addPreDefinitions` inside one `private` block. Inferring a declaration's instance parameters
means acting between the elaborated values and the `PreDefinition`s, and there is no seam there,
so the surrounding steps have to be reproduced rather than called.

Everything here is a copy or a reduction of a *private* definition of the `def` command, checked
against **Lean 4.34.0**; each one names its original. Nothing here is specific to interface
inference, and nothing that Lean exports is copied -- `MutualClosure.main`, `addPreDefinitions`,
`fixLevelParams`, `expandMatchAltsWhereDecls`, `withAuxDecl` and `mkDefView` are called directly
by their users.

On a toolchain bump this file is what to re-check against upstream. Each definition also records
what was dropped, so a difference can be told apart from an omission.
-/
namespace TaglessFinal.LeanInternals

open Lean Elab Command Term Meta

/- From the private `declValToTerm` in `Lean/Elab/MutualDef.lean`, without its `whereStructInst`
case: that shape belongs to `instance ... where`, which the callers here do not accept. -/
/-- The value of a definition, as a term to elaborate at `expectedType`. -/
def declValToTerm (declVal : Syntax) (expectedType : Expr) : TermElabM Syntax :=
  withRef declVal do
    if declVal.isOfKind ``Parser.Command.declValSimple then
      liftMacroM <| expandWhereDeclsOpt declVal[3] declVal[1]
    else if declVal.isOfKind ``Parser.Command.declValEqns then
      expandMatchAltsWhereDecls declVal[0] expectedType
    else if declVal.isMissing then
      throwErrorAt declVal "declaration body is missing"
    else
      throwErrorAt declVal "unexpected declaration body"

/- From the private `declValToTerminationHint` in `Lean/Elab/MutualDef.lean`. `MutualClosure`
calls its own copy when it builds the `PreDefinition`s, so this one exists only for a caller that
needs to consult the hints beforehand. -/
/-- The termination hints written after a definition's value. -/
def declValTerminationHints (declVal : Syntax) : CommandElabM TerminationHints :=
  if declVal.isOfKind ``Parser.Command.declValSimple then
    elabTerminationHints ⟨declVal[2]⟩
  else if declVal.isOfKind ``Parser.Command.declValEqns then
    elabTerminationHints ⟨declVal[0][1]⟩
  else
    return .none

/- From the body of the private `elabHeaders` in `Lean/Elab/MutualDef.lean`, reduced to its
binder, auto-bound-implicit and universe handling. Dropped: the incrementality snapshots, the
deprecation context of the attributes, the `instance`-specific `cleanupOfNat`,
`registerFailedToInferDefTypeInfo`, the report of the metavariables a written type leaves
unassigned, and the `check` comparing a header against its predecessors in the block.

`defaultDefType` is the one addition: it stands in for the `:` part of a definition that writes
none, where upstream always elaborates a hole and leaves the body to determine it. A caller that
knows the shape such a body must have -- `m ?α`, say -- supplies it here instead. -/
/-- Elaborate one definition's signature, in the caller's local context. -/
def elabDefHeader (declId : ExpandDeclIdResult) (view : DefView) (forbidden : Name → Bool)
    (defaultDefType : Option (TermElabM Expr)) : TermElabM DefViewElabHeader := do
  applyAttributesAt declId.declName view.modifiers.attrs .beforeElaboration
  withDeclName declId.declName <| withAutoBoundImplicitForbiddenPred forbidden <|
    withAutoBoundImplicit <| withLevelNames declId.levelNames <|
      elabBindersEx view.binders.getArgs fun xs => do
        let type ← match view.type?, defaultDefType with
          | some typeStx, _ => elabType typeStx
          | none, some shape => shape
          | none, none => elabType (mkHole view.value)
        Term.synthesizeSyntheticMVarsNoPostponing
        let (binderIds, xs) := xs.unzip
        let xs ← addAutoBoundImplicits xs (view.declId.getTailPos? (canonicalOnly := true))
        let type ← instantiateMVars (← Meta.mkForallFVars' xs type)
        return { view with
          shortDeclName := declId.shortName, declName := declId.declName
          levelNames := ← getLevelNames, binderIds, numParams := xs.size, type
          tacSnap? := none, bodySnap? := none }

/- From the private `withFunLocalDecls` in `Lean/Elab/MutualDef.lean`. -/
/-- Bind each definition of the block as an auxiliary local hypothesis of its written signature,
and run `k` with them. This is what a recursive occurrence elaborates against. -/
partial def withFunLocalDecls (headers : Array DefViewElabHeader)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (fvars : Array Expr) := do
    if h : i < headers.size then
      let header := headers[i]
      if header.modifiers.isNonrec then
        loop (i + 1) fvars
      else
        withAuxDecl header.shortDeclName header.type header.declName fun fvar =>
          loop (i + 1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

/- The rule of the private `collectUsed` and `withUsed` in `Lean/Elab/MutualDef.lean`, which is
how a definition selects the section variables it keeps. Rewritten to return the variables kept
rather than a restricted local context, so that a caller can apply it to other candidates too.
`include` and `omit` are not consulted. -/
/-- Keep the candidates that `exprs` use, closing the selection under the types of the candidates
kept. Later candidates are examined first, so that one kept for its use in `exprs` can retain an
earlier one its type mentions. -/
def keepUsedParams (candidates : Array Expr) (exprs : Array Expr) : MetaM (Array Expr) := do
  let mut used : CollectFVars.State := {}
  for e in exprs do
    used := Lean.collectFVars used (← instantiateMVars e)
  let mut kept : Array Expr := #[]
  for candidate in candidates.reverse do
    if used.fvarSet.contains candidate.fvarId! then
      used := Lean.collectFVars used (← instantiateMVars (← candidate.fvarId!.getType))
      kept := kept.push candidate
  return kept.reverse

/- From the tail of `finishElab`, private inside `elabMutualDef` in `Lean/Elab/MutualDef.lean`:
its sequence of public calls, unchanged. Dropped: `checkAllDeclNamesDistinct`, which
`addPreDefinitions` reports anyway, and `where ... finally`, whose holes the callers here do not
fill. -/
/-- Close the elaborated block over `sectionVars` and add it to the environment.

`funFVars` are the local hypotheses standing for the definitions, which become applications of
the constants being declared; `letRecsToLift` are the `where` and `let rec` helpers, which are
lifted to declarations of their own. -/
def addMutualPreDefinitions (sectionVars : Array Expr) (headers : Array DefViewElabHeader)
    (funFVars : Array Expr) (values : Array Expr) (letRecsToLift : List LetRecToLift) :
    TermElabM Unit := do
  let preDefs ← MutualClosure.main sectionVars headers funFVars values letRecsToLift
  let userLevelNames := if h : 0 < headers.size then headers[0].levelNames else []
  let preDefs ← withLevelNames userLevelNames <| levelMVarToParamTypesPreDecls preDefs
  let preDefs ← instantiateMVarsAtPreDecls preDefs
  let preDefs ← shareCommonPreDefs preDefs
  let preDefs ← fixLevelParams preDefs (← getLevelNames) userLevelNames
  addPreDefinitions (← getLCtx, ← getLocalInstances) preDefs
  for header in headers, funFVar in funFVars do
    addLocalVarInfo header.declId funFVar

end TaglessFinal.LeanInternals
