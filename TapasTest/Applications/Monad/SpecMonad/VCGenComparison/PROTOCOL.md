# Benchmark protocol

The comparison has four axes: case, mode, route, and tier. `n` is the loop iteration
count. [BenchmarkCases.lean](BenchmarkCases.lean) selects the goals and specifications;
[Harness.lean](Harness.lean) constructs and checks proofs; [run.py](run.py) selects
sizes and collects measurements. Source provenance, run commands, and archived runs
are documented in the [README](README.md).

## Proof routes

The table describes complete mode; generation-only mode is defined below.

| Route | Complete-mode proof | Cases |
|---|---|---|
| `vcgen` | `vcgen [specs]`, then `grind` on each remaining VC | All eight |
| `vcgen-finish` | `vcgen [specs] with finish`, solving during generation in vcgen's E-graph | All eight |
| `vcgen-finish-simp` | `vcgen-finish` with `simplifying_assumptions [Nat.add_assoc]` | GetThrowSet |
| `normalize` | Instantiate the polymorphic program in a specification monad, normalize its VC, prove it with `grind`, and apply its parametricity soundness bridge | All eight |
| `normalize-sym` | As `normalize`, using `Sym.dsimp`'s traversal with the same head reducer | All eight |
| `dsimp` | As `normalize`, replacing the normalizer with `dsimp only [...]` | All eight |
| `sym-dsimp` | As `normalize`, replacing the normalizer with `Sym.dsimp` and unfolding hooks | All eight |
| `sym` | The upstream AddSubCancel Sym solver with `Exec` rules; the deep variant adapts those rules to its WP | Both AddSubCancel cases |
| `wp-simp` | Rewrite the original program's `wp` with registered equations using `simp only`, then prove the remaining VCs with `grind` | All except AddSubCancelDeep and MatchSplit |
| `wp-sym` | The same equations with `Sym.simp`, then `grind` | All except AddSubCancelDeep and MatchSplit |

The four normalization routes share a bridge `VC n → Goal n`, proved once for all
`n`. The `wp` routes build a rewriting proof for each `n`; in PurePrecond they unfold
`flipp` instead of using its partial contracts. `wp-simp` applies its rules before
traversal; `wp-sym` applies them before and after traversal, with beta and zeta
reduction for `let`s and join points.

The generic simplifiers receive an unfold list computed before timing.
[`sym-dsimp`'s hooks](GenericSimp.lean) provide global unfolding, selected projection
reduction, and reduction of a `let` at an application's head.

During complete normalization proofs, `grind` uses the scoped function application
rules in [Control.lean](Control.lean). The `PredTrans` tiers additionally enable
`PredTrans.apply_ite` and `apply_dite`. Grind includes activating and restoring these
rules. Symbolic `match` expressions are left for `grind`'s match equations and splitters.

## Tiers

| Tier | Normalization routes | vcgen routes |
|---|---|---|
| `custom-monad` | Function-type `Spec` with hand-written operation specs | — |
| `hand-written-specs` | Lean's `PredTrans` with hand-written operation specs | The case's upstream operation specs |
| `library` | `PredTrans` with Lean's instances | Library operation specs, with all imported upstream operation specs erased |

`sym` and the `wp` routes have no tier and are reported as `-`. PurePrecond's
procedure contracts remain in both vcgen tiers and all normalization tiers; its two
`PredTrans` tiers coincide. [SPECIALIZATION.md](SPECIALIZATION.md#the-tiers) explains
the choices, and [Models.lean](Models.lean) supplies the instances and soundness proofs.

## Modes and sizes

- **Complete:** every remaining VC is proved, and the assembled proof establishes
  the original upstream `Goal n`.
- **Generation only:** remaining VCs are admitted with `sorry`. This mode measures
  generation and the subsequent proof assembly and kernel check. It runs `vcgen`,
  the four normalization routes, and the two `wp` routes.

The configured sizes in [run.py](run.py) are:

| Case | Complete | Generation only |
|---|---|---|
| AddSubCancel | 200, 1200, 2200 | — |
| AddSubCancelDeep | 100, 500, 900 | — |
| LetBinding | 10, 50, 100 | — |
| ReaderState | 10, 50, 100 | 600, 1600, 2600 |
| PurePrecond | 400, 2400, 4400 | — |
| GetThrowSet | 10, 50, 100, 200, 300 | 200, 500, 800 |
| DiteSplit | 10, 50, 100 | — |
| MatchSplit | 10, 50, 100 | 500, 1000, 1500 |

## Timers

| Phase | Work measured |
|---|---|
| Prepare | For vcgen, Sym, and the `wp` routes: unfold the goal and program definitions using their equations. For normalization: unfold the VC and introduce its binders. |
| Generate | Run the selected tactic or normalizer. This includes loop unfolding for normalization and integrated solving for `vcgen-finish` and `vcgen-finish-simp`. |
| Grind | Solve the remaining VCs, including normalization's scoped control-flow rules; admit them in generation-only mode. |
| Instantiate | Instantiate proof metavariables. |
| Share | Share common subterms of the assembled proof, including any soundness bridge. |
| Kernel | Check the assembled proof with the kernel. |

**Solve** is Generate + Grind. **Total** covers initial goal creation through Kernel,
including bridge attachment between Instantiate and Share. Imports, startup,
compilation, unfold-list construction, VC comparison, and the audits below are
outside Total.

Samples use `LEAN_NUM_THREADS=1` and `Elab.async false`. Kernel checking of `grind`'s
auxiliary theorems therefore happens inside the tactic that creates them: Grind for
ordinary routes, Generate for integrated vcgen.

**One-time** sums per-declaration medians over three fresh elaborations of each
setup file, timed by [TimeSetup.lean](TimeSetup.lean). Normalization charges each case
and tier for its parametricity derivations, fidelity proof, operation soundness,
and bridge. The `wp` routes charge for their equations and order rules. Shared
setup declarations are counted for each case that uses them. **Total + one-time**
adds this separate setup estimate to the per-size Total; imported infrastructure
and upstream specification proofs are outside this estimate.

**Peak** uses MiB, labelled MB in the reports, and includes imports and post-timer
audits. The runner takes the maximum of sampled `lake` + `lean` RSS and exit-time
`ru_maxrss`. Reports also include an import-only baseline, without subtracting it from Peak.

## Sampling, limits, and checks

Each per-size measurement uses three fresh Lean processes. Reports give the median
of each metric when all three repetitions succeed. A median of a sum, such as Solve,
need not equal the sum of the component medians.

A sample whose Total exceeds 60 s is recorded as a timeout. The runner also kills a
per-size process group after 90 s of wall time or when sampled RSS exceeds 8192 MiB;
these limits cover imports and post-timer audits too. After a failure, the remaining
repetitions and larger sizes of that case/mode/route/tier are skipped.

The runner first builds [Verify.lean](Verify.lean), which checks routes and tiers at
`n = 2, 3` in both modes. Its known-failure skips are ReaderState's two
`vcgen-finish` tiers; timed runs still attempt those configurations. Where vcgen's
hand-written-specs route and another route each leave one VC, Verify requires them
to be definitionally equal.

Each successful sample passes the kernel and original-goal type checks, has no unresolved
metavariables, and uses only `propext`, `Classical.choice`, and `Quot.sound`, plus
`sorryAx` in generation-only mode. For vcgen, the harness also checks use of the
selected specifications: ordinary vcgen must use all selected specs, integrated
vcgen must use at least one when present, and the library
tier must use none of the erased upstream operation specs.

## Saved runs

`results.json` records the Lean version, upstream commits, settings, and per-session
module/settings fingerprints. Resuming a run retains completed samples and reports
changed fingerprints. Starting a new run or selecting measurements to repeat is
covered in [README.md](README.md#run).
