module

public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.Driver    -- only uses its `timeItMs`
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.GenericSimp
public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Control

public meta section

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Harness

open Lean Meta Elab Sym

section Defs

/-- How much of the interpretation is written for the case rather than taken from Lean.
vcgen's predicate transformers are fixed to `PredTrans`, so it has no `customMonad` tier. -/
inductive Tier where
  /-- Our own specification monad, with hand-written specs. -/
  | customMonad
  /-- `PredTrans` with hand-written specs; for vcgen, the case's own specs. -/
  | handWrittenSpecs
  /-- `PredTrans` with Lean's instances; for vcgen, the library's specs alone. -/
  | library
  deriving BEq

def Tier.label : Tier → String
  | .customMonad => "custom-monad"
  | .handWrittenSpecs => "hand-written-specs"
  | .library => "library"

/-- A normalization tier: its specification monad, the VC calculated there, and the bridge from
that VC to the execution goal. -/
structure Normalization where
  specMonad : Name
  vc : Name
  sound : Name

/-- How a route turns the execution goal into VCs and solves them. -/
inductive Route where
  /-- `vcgen`, then `grind` on each VC separately, as upstream's add/sub driver does. -/
  | vcgen
  /-- `vcgen … with finish`: grind shares vcgen's E-graph and drops unreachable branches. -/
  | vcgenFinish
  /-- `vcgenFinish` with the case's `simplifying_assumptions` lemmas, as upstream tunes it. -/
  | vcgenFinishSimp
  /-- Upstream's hand-written Sym baseline, without vcgen or WP. -/
  | sym
  /-- Our normalizer in a specification monad, with the parametricity bridge to the goal. -/
  | normalize
  /-- `normalize` with `Sym.dsimp`'s traversal instead of `dsimp`'s. -/
  | normalizeSym
  /-- Lean's `dsimp only [...]` in place of our normalizer, unfolding the same constants. -/
  | dsimp
  /-- `Sym.dsimp` with its own dsimprocs in place of our normalizer, unfolding the same constants. -/
  | symDsimp
  /-- `simp only` rewrites the original program's `wp` with the case's registered `wp` equations,
  applied before descending (`↓`), until no `wp` is left. -/
  | wpSimp
  /-- `wpSimp` with `Sym.simp`, which also needs zeta and beta steps for the programs' `have`s. -/
  | wpSym
  deriving BEq

def Route.label : Route → String
  | .vcgen => "vcgen"
  | .vcgenFinish => "vcgen-finish"
  | .vcgenFinishSimp => "vcgen-finish-simp"
  | .sym => "sym"
  | .normalize => "normalize"
  | .normalizeSym => "normalize-sym"
  | .dsimp => "dsimp"
  | .symDsimp => "sym-dsimp"
  | .wpSimp => "wp-simp"
  | .wpSym => "wp-sym"

def Route.isVCGen : Route → Bool
  | .vcgen | .vcgenFinish | .vcgenFinishSimp => true
  | _ => false

/-- Routes that normalize the VC in a specification monad, sharing its bridge to the goal. -/
def Route.isNormalization : Route → Bool
  | .normalize | .normalizeSym | .dsimp | .symDsimp => true
  | _ => false

/-- Generic simplifiers, which must be told what to unfold. -/
def Route.isGeneric : Route → Bool
  | .dsimp | .symDsimp => true
  | _ => false

/-- Routes that rewrite the original program's `wp` with equations; they have no tier. -/
def Route.isWP : Route → Bool
  | .wpSimp | .wpSym => true
  | _ => false

/-- Whether VCs are proved, or closed by `sorry` as in upstream's generation-only benchmarks. -/
inductive Mode where
  | complete
  | generation
  deriving BEq

def Mode.label : Mode → String
  | .complete => "complete"
  | .generation => "generation"

/-- The declarations connecting each route to one execution goal. -/
structure Case where
  /-- The case name shown in benchmark reports. -/
  label : String
  /-- The execution goal, indexed by benchmark size. -/
  goal : Name
  /-- Program definitions unfolded during goal preparation. -/
  programs : List Name
  /-- Normalization in our own specification monad with hand-written specs. -/
  customMonad : Normalization
  /-- Normalization in `PredTrans` with hand-written specs. -/
  handWrittenSpecs : Normalization
  /-- Normalization in `PredTrans` with Lean's instances. -/
  library : Normalization
  /-- The case's own operation specs, which vcgen uses in the hand-written-specs tier. -/
  specs : List Name := []
  /-- Procedure contracts, which vcgen uses in both tiers. -/
  contracts : List Name := []
  /-- Upstream's `simplifying_assumptions` lemmas for integrated vcgen, when upstream tunes it. -/
  finishSimp : List Name := []
  /-- Routes that fail on this case. The runners record their failures; `runTwo` skips them. -/
  failing : List (Route × Tier) := []
  /-- The Sym baseline's goal, indexed by benchmark size; anonymous for a case without one. -/
  symGoal : Name := .anonymous
  /-- A theorem deriving the execution goal from the Sym goal. -/
  symSound : Name := .anonymous
  /-- The solver used by the Sym baseline. -/
  symSolve : MVarId → MetaM (List MVarId) := fun _ => throwError "no Sym solver for this case"
  /-- The registered `wp` equations of the case's monad, with the order rules turning a triple
  into implications; empty for a case the `wp` routes do not support. -/
  wpEquations : List Name := []
  /-- Procedures the `wp` routes unfold, since an equation cannot use their contracts. -/
  wpUnfold : List Name := []

def Case.normalization (case : Case) : Tier → Normalization
  | .customMonad => case.customMonad
  | .handWrittenSpecs => case.handWrittenSpecs
  | .library => case.library

/-- Every route and tier of a case in a mode. Integrated vcgen and Sym solve while generating, so
generation-only mode leaves them out. Sym and the `wp` routes have no tier; they are listed under
hand-written specs. -/
def routes (case : Case) (mode : Mode) : List (Route × Tier) :=
  let solving := if mode == .generation then [] else
    [(.vcgenFinish, .handWrittenSpecs), (.vcgenFinish, .library)] ++
      (if case.finishSimp.isEmpty then []
       else [(.vcgenFinishSimp, .handWrittenSpecs), (.vcgenFinishSimp, .library)]) ++
      if case.symGoal.isAnonymous then [] else [(.sym, .handWrittenSpecs)]
  [(.vcgen, .handWrittenSpecs), (.vcgen, .library)] ++ solving ++
    ([Route.normalize, .normalizeSym, .dsimp, .symDsimp].flatMap fun route =>
      [Tier.customMonad, .handWrittenSpecs, .library].map (route, ·)) ++
    if case.wpEquations.isEmpty then [] else [(.wpSimp, .handWrittenSpecs), (.wpSym, .handWrittenSpecs)]

/-- The tier shown in reports; Sym and the `wp` routes have none. -/
def tierLabel (route : Route) (tier : Tier) : String :=
  if route == .sym || route.isWP then "-" else tier.label

/-- Per-measurement wall-clock times in hundredths of a millisecond. -/
private structure Times where
  /-- Unfold the goal and programs for vcgen/Sym, or unfold the VC and introduce its binders
  for normalization. -/
  prepare : UInt64
  /-- Run vcgen (including integrated `finish`), Sym's solver, or the normalizer/generic
  simplifier, including loop unfolding. -/
  generate : UInt64
  /-- Run `grind` on remaining VCs, including control-flow reasoning, or close them with
  `sorry` in generation-only mode. -/
  grind : UInt64
  /-- Instantiate metavariables in the proof. -/
  instantiate : UInt64
  /-- Share the proof's common subterms before the kernel check. -/
  share : UInt64
  /-- Check the whole proof with the kernel, including any soundness bridge. -/
  kernel : UInt64
  /-- Elapsed time from preparation through kernel checking, including bridge attachment. -/
  total : UInt64

end Defs

-- Adapted from the `_unfoldMs` preparation block in `Upstream/Driver.lean`:
-- `preprocessMVar` through `Sym.simpGoal`, preserving the equation order
-- (programs first, then the goal).
private def prepare (case : Case) (root : Name) (goal : MVarId) : MetaM MVarId := SymM.run do
  let goal ← preprocessMVar goal
  let eqns ← (case.programs ++ [root]).toArray.mapM fun name => getEqnsFor? name
  let methods ← mkMethods (eqns.flatMap (·.getD #[]))
  let .goal goal ← Sym.simpGoal goal methods | throwError "preparation did not leave a goal"
  return goal

/-- Share common subterms. As an action, it runs inside the timer it is passed to; a pure `let`
could be evaluated outside. -/
@[noinline] private def shareProof (proof : Expr) : MetaM Expr :=
  return Lean.ShareCommon.shareCommon proof

/-- Quantify a VC over its local context for comparison across proof routes. -/
private def turnVCIntoClosedTerm (goal : MVarId) : MetaM Expr := goal.withContext do
  instantiateMVars (← mkForallFVars (← getLCtx).getFVars (← goal.getType))

/-- The case's own specs take priority over equivalent specs imported by other cases; the library
tier instead erases every upstream spec. Contracts stay in both tiers. -/
private def vcgenTactic (case : Case) (route : Route) (tier : Tier) (upstream : List Name) :
    MetaM (TSyntax `tactic) := do
  let used ← ((if tier == .library then [] else case.specs) ++ case.contracts).toArray.mapM
    fun name => `(Parser.Tactic.simpLemma| $(mkIdent name):term)
  let erased ← (if tier == .library then upstream else []).toArray.mapM
    fun name => `(Parser.Tactic.simpErase| -$(mkIdent name):term)
  let args : Array (TSyntax ``Parser.Tactic.simpLemma) := erased.map (⟨·.raw⟩) ++ used
  let simps := case.finishSimp.toArray.map mkIdent
  match route, args.isEmpty with
  | .vcgen, true => `(tactic| vcgen)
  | .vcgen, false => `(tactic| vcgen [$args,*])
  | .vcgenFinish, true => `(tactic| vcgen with finish)
  | .vcgenFinish, false => `(tactic| vcgen [$args,*] with finish)
  | .vcgenFinishSimp, true => `(tactic| vcgen simplifying_assumptions [$simps,*] with finish)
  | .vcgenFinishSimp, false =>
    `(tactic| vcgen [$args,*] simplifying_assumptions [$simps,*] with finish)
  | _, _ => throwError "{route.label} is not a vcgen route"

/-- Rewrite with `simp only`, each rule applied before descending into its result's subterms. Unlike
the normalizer, every rewrite adds to the proof term relating the VC to the goal. -/
private def wpSimp (rules : Array Name) (goal : MVarId) : MetaM (List MVarId) := do
  let rules ← rules.mapM fun name => `(Parser.Tactic.simpLemma| ↓ $(mkIdent name):term)
  let tactic ← `(tactic| simp (config := { maxSteps := 1000000000 }) only [$rules,*])
  return (← Lean.Elab.runTactic goal tactic {} {}).1

/-- Zeta-reduce a `have`, which programs use for `let`s and join points. -/
private def zetaHave : Sym.Simp.Simproc := fun e => do
  let .letE _ _ value body _ := e | return .rfl
  let e' := body.instantiate1 value
  return .step e' (mkExpectedPropHint (← Meta.mkEqRefl e') (← Meta.mkEq e e'))

/-- Beta-reduce at the head, where zeta leaves a join point applied to its argument. -/
private def betaHead : Sym.Simp.Simproc := fun e => do
  unless e.isHeadBetaTarget do return .rfl
  let e' := e.headBeta
  return .step e' (mkExpectedPropHint (← Meta.mkEqRefl e') (← Meta.mkEq e e'))

/-- `wpSimp` with `Sym.simp`, the rules applied both before and after descending. -/
private def wpSym (rules : Array Name) (goal : MVarId) : MetaM (List MVarId) := SymM.run do
  let rewrite := zetaHave >> betaHead >> (← mkSimprocFor rules)
  match ← Sym.simpGoal goal { pre := rewrite, post := rewrite } { maxSteps := 1000000000 } with
  | .goal goal => return [goal]
  | _ => return []

private def measure (case : Case) (mode : Mode) (route : Route) (tier : Tier) (count : Nat)
    (upstream : List Name) : MetaM (Times × List MVarId) := do
  if route.isVCGen && tier == .customMonad then
    throwError "vcgen's predicate transformers are fixed; it has no custom-monad tier"
  unless (routes case mode).contains (route, tier) do
    throwError "{case.label} has no {route.label} {tierLabel route tier} route in {mode.label} mode"
  let n := mkNatLit count
  let normalization := case.normalization tier
  -- What a user would list for a generic simplifier; computed before the caches are reset.
  let unfold ← if route.isGeneric then
      GenericSimp.unfoldSet normalization.specMonad (← whnf (mkApp (mkConst normalization.vc) n))
    else pure #[]
  resetCache
  let start ← IO.monoNanosNow
  let root := match route with
    | .vcgen | .vcgenFinish | .vcgenFinishSimp | .wpSimp | .wpSym => case.goal
    | .sym => case.symGoal
    | .normalize | .normalizeSym | .dsimp | .symDsimp => normalization.vc
  let proof ← mkFreshExprMVar (mkApp (mkConst root) n)
  let (goal, prepareTime) ← timeItMs do
    if route.isNormalization then
      let goal ← proof.mvarId!.replaceTargetDefEq (← whnf (← inferType proof))
      return (← goal.intros).2
    else
      prepare case root proof.mvarId!
  -- Match the official timer: the initial program unfolding is outside vcgen/Sym generation.
  -- Normalization includes loop unfolding in its generation time.
  let (goals, generateTime) ← timeItMs do
    match route with
    | .vcgen | .vcgenFinish | .vcgenFinishSimp =>
      return (← Lean.Elab.runTactic goal (← vcgenTactic case route tier upstream) {} {}).1
    | .sym => case.symSolve goal
    | .normalize | .normalizeSym | .dsimp | .symDsimp =>
      let goal ← match route with
        | .normalizeSym => Normalizer.normalizeSym normalization.specMonad goal
        | .dsimp => GenericSimp.dsimp unfold goal
        | .symDsimp => GenericSimp.symDsimp unfold goal
        | _ => Normalizer.normalize normalization.specMonad goal
      return [goal]
    | .wpSimp | .wpSym =>
      let unfold ← case.wpUnfold.toArray.mapM fun name => getEqnsFor? name
      let rules := case.wpEquations.toArray ++ unfold.flatMap (·.getD #[])
      let goals ← if route == .wpSimp then wpSimp rules goal else wpSym rules goal
      for goal in goals do
        if ((← instantiateMVars (← goal.getType)).find? (·.isConstOf ``Std.WP.WP.wp)).isSome then
          throwError "{route.label} left a `wp` it has no equation for"
      return goals
  -- Upstream's generation-only benchmarks close every VC with `sorry`.
  let (_, grindTime) ← timeItMs do
    let useControlRules := route.isNormalization && mode == .complete
    -- Restore the normalization rule set after this measurement, including on failure.
    if useControlRules then modifyEnv Grind.normExt.pushScope
    try
      if useControlRules then
        modifyEnv fun env => Grind.normExt.activateScoped env
          `TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Control.FunctionApplication
        if tier != .customMonad then
          modifyEnv fun env => Grind.normExt.activateScoped env
            `TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Control.PredTrans
      for goal in goals do
        if mode == .generation then
          goal.admit
        else
          let ([], _) ← Lean.Elab.runTactic goal (← `(tactic| grind)).raw {} {}
            | throwError "grind did not close a VC"
    finally
      if useControlRules then modifyEnv Grind.normExt.popScope
  let (proof, instantiateTime) ← timeItMs <| instantiateMVars proof
  -- Attach the separately checked bridge before checking the entire upstream goal. The `wp`
  -- routes need none: their rewriting proved the goal from the VC, for this n.
  let proof := match route with
    | .vcgen | .vcgenFinish | .vcgenFinishSimp | .wpSimp | .wpSym => proof
    | .sym => mkApp2 (mkConst case.symSound) n proof
    | .normalize | .normalizeSym | .dsimp | .symDsimp => mkApp2 (mkConst normalization.sound) n proof
  let (proof, shareTime) ← timeItMs <| shareProof proof
  let (_, kernelTime) ← timeItMs <| checkWithKernel proof
  let totalTime := (((← IO.monoNanosNow) - start) / 10000).toUInt64
  -- Checks happen after timing; no route can omit execution soundness or leave a goal open.
  if proof.hasMVar then throwError "unfinished proof"
  -- A failing `finish` is reported and its goal admitted, which would hide the failure.
  if mode == .complete && proof.hasSorry then
    throwError "{route.label} left a VC unproved"
  if route.isVCGen then
    let used := proof.getUsedConstants
    let selected := (if tier == .library then [] else case.specs) ++ case.contracts
    if route == .vcgen then
      for spec in selected do
        unless used.contains spec do
          throwError "vcgen did not use the spec {spec}"
    -- Integrated vcgen drops an unreachable branch, such as a throw, before applying its spec.
    else unless selected.isEmpty || selected.any used.contains do
      throwError "{route.label} used none of the selected specs {selected}"
    if tier == .library then
      for spec in upstream do
        if used.contains spec then
          throwError "vcgen used the erased upstream spec {spec}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++
    if mode == .generation then [``sorryAx] else []
  for name in proof.getUsedConstants do
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "proof depends on unexpected axiom {ax}"
  unless ← isDefEq (← inferType proof) (mkApp (mkConst case.goal) n) do
    throwError "proof does not establish the original upstream goal"
  return (⟨prepareTime, generateTime, grindTime, instantiateTime, shareTime, kernelTime, totalTime⟩,
    goals)

private def report (case : Case) (mode : Mode) (route : Route) (tier : Tier) (n : Nat)
    (times : Times) : MetaM Unit := do
  let result := Json.mkObj [
    ("case", toJson case.label), ("mode", toJson mode.label), ("route", toJson route.label),
    ("tier", toJson (tierLabel route tier)), ("n", toJson n),
    ("prepare_hms", toJson times.prepare), ("generate_hms", toJson times.generate),
    ("grind_hms", toJson times.grind), ("solve_hms", toJson (times.generate + times.grind)),
    ("instantiate_hms", toJson times.instantiate), ("share_hms", toJson times.share),
    ("kernel_hms", toJson times.kernel), ("total_hms", toJson times.total)]
  IO.println s!"RESULT {result.compress}"

/-- Check every route and tier in both modes, skipping the case's known failures. Where vcgen in
the hand-written-specs tier and another route each leave a single VC, the two must be
definitionally equal. -/
def runTwo (cases : List Case) (counts : List Nat) : MetaM Unit := do
  let upstream := cases.flatMap (·.specs)
  let mut complete := 0
  let mut generation := 0
  for case in cases do
    for n in counts do
      for mode in [Mode.complete, .generation] do
        let mut expected := []
        for (route, tier) in routes case mode do
          if case.failing.contains (route, tier) then
            IO.println s!"SKIPPED {case.label} {n} {mode.label} {route.label} {tierLabel route tier}"
            continue
          let (times, goals) ← measure case mode route tier n upstream
          report case mode route tier n times
          -- Only the checks compare VCs: closing many VCs over their contexts grows quickly with n.
          let actual ← goals.mapM turnVCIntoClosedTerm
          if mode == .complete then complete := complete + 1 else generation := generation + 1
          if route == .vcgen && tier == .handWrittenSpecs then expected := actual
          -- Splitting and pure precondition discharge can produce different VC shapes/counts.
          -- Record definitional equality with vcgen's hand-written-specs VCs when available.
          let same ← match expected, actual with
            | [e], [a] => isDefEq e a
            | [], [] => pure true
            | _, _ => pure false
          IO.println s!"VCS {case.label} {n} {mode.label} {route.label} {tierLabel route tier} \
            {expected.length} {actual.length} {same}"
          if expected.length == 1 && actual.length == 1 && !same then
            throwError "{case.label}({n}) {mode.label} {route.label} {tier.label}: \
              the VC differs from vcgen's"
  IO.println s!"All {complete} complete proofs passed the kernel and axiom audit; all \
    {generation} generation-only proofs passed the kernel and goal check."

/-- Measure one proof, allowing an external runner to isolate resource limits. -/
def runOne (cases : List Case) (label : String) (mode : Mode) (route : Route) (tier : Tier)
    (n : Nat) : MetaM Unit := do
  let some case := cases.find? (·.label == label) | throwError "missing case {label}"
  let (times, goals) ← measure case mode route tier n (cases.flatMap (·.specs))
  report case mode route tier n times
  IO.println s!"CHECKED {goals.length} VCs; {mode.label} proof passed the kernel and audits."

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Harness
