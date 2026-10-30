# `vcgen` versus specification normalization

This directory compares `vcgen` and specification normalization on eight upstream
cases with Lean 4.35.0, alongside Sym and simplifier baselines.

- [PROTOCOL.md](PROTOCOL.md): proof routes, tiers, sizes, timers, and checks.
- [SPECIALIZATION.md](SPECIALIZATION.md): the specialization tiers and their results.
- [Playground.lean](Playground.lean): five cases with ordinary tactic proofs, timed by `#time`.

## Source map

- [Programs.lean](Programs.lean) abstracts the upstream programs, derives
  parametricity, and proves equality to the originals for every iteration count.
- [Specification.lean](Specification.lean) defines the shared specification monads
  and soundness relations; [Models.lean](Models.lean) supplies operation specs.
- [Conditions.lean](Conditions.lean) defines the VCs and their parametricity soundness bridges.
- [Harness.lean](Harness.lean) constructs, measures, and checks proofs selected by
  [BenchmarkCases.lean](BenchmarkCases.lean), using the shared [normalizer](../Normalizer.lean).
- [SymBaseline.lean](SymBaseline.lean), [GenericSimp.lean](GenericSimp.lean), and
  [WPEquations.lean](WPEquations.lean) supply the comparison baselines.

## Run

From the repository root:

```sh
sh TapasTest/Applications/Monad/SpecMonad/VCGenComparison/run.sh --name trial
```

The wrapper starts the runner in the background and writes console logs to
`results/trial/console/`. It prepares the upstream sources and builds
[Verify.lean](Verify.lean) before measuring. Run [run.py](run.py) directly with
`python3` for a foreground run.

The default name is `all`. Repeating a name resumes its unfinished measurements;
use a new name for a separate run. `--only` selects configurations by
`CASE/MODE/ROUTE/TIER` patterns, and `--rerun` repeats matching measurements.
`--dry-run` lists the selection; the runner's `--help` gives examples.

To plot the results:

```sh
python3 TapasTest/Applications/Monad/SpecMonad/VCGenComparison/plot.py --name trial
```

This writes a self-contained page to `results/trial/figures/index.html`, with
scoreboards, phase breakdowns, and time and memory plots. Raw samples are in
`results.json`; measurement logs and `RESULTS.md` are in the same folder.

For editor use or checks without running the benchmark:

```sh
python3 TapasTest/Applications/Monad/SpecMonad/VCGenComparison/fetch_upstream.py
lake build TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Verify
```

## Upstream sources

`Upstream/*.lean` are reconstructed locally and ignored by Git. The preparation
script downloads pinned sources, checks their hashes, and applies the recorded
patches. The manifests and patches retain the source and porting details:

- LetBinding, ReaderState, PurePrecond, GetThrowSet, DiteSplit, and MatchSplit:
  commit `ece9cbd7`, [manifest](Upstream/SOURCES.json), [patch](Upstream/PORT.patch).
- Ordinary and deep AddSubCancel, including the upstream driver and Sym baseline:
  commit `5fe62b1f`, [manifest](Upstream/SOURCES-addsub.json), [patch](Upstream/PORT-addsub.patch).

The upstream [Apache-2.0 license](Upstream/LICENSE) is retained.

Seven other cases from the inspected snapshot are excluded:

- AdcChain and MatchIota have false stated goals in the inspected examples.
- AddSubCancelSimp's alternative equality specs are commented out.
- IfsJP, MatchesJP, and WideJP need newer join-point support in `vcgen`.
- RegFile needs the newer `vcgen_simp` attribute.
