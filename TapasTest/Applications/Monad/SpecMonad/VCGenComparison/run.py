#!/usr/bin/env python3
"""Measure every case in fresh single-threaded Lean processes; see PROTOCOL.md.

A configuration is a case, mode, route, and tier, measured at each of its sizes. A run is named
(--name, default `all`) and kept in results/NAME/, or in --out: results.json, saved after every
measurement, a log per measurement, and RESULTS.md at the end. Running a name again continues
that run: it measures the selected configurations (all, unless --only) that it has not recorded,
and warns if the benchmark's Lean modules or the runner's settings changed since the run
started. To start a name over, delete its folder. Patterns select configurations by
CASE/MODE/ROUTE/TIER or a prefix of it, with `*` as a wildcard; Sym and the wp routes have tier
`-`. --rerun measures the matching configurations again, and only those, setting their earlier
measurements aside in results.json (`replaced`) and their logs in replaced-<time>/; an
interrupted --rerun X is continued with --only X.

  python3 run.py                                   # the run `all`: start it, or continue it
  python3 run.py --name tonight                    # the run `tonight`, in results/tonight/
  python3 run.py --only GetThrowSet DiteSplit      # some cases
  python3 run.py --rerun MatchSplit '*/*/dsimp'    # run these again, keeping the rest
  python3 run.py --rerun setup                     # measure the one-time costs again
  python3 run.py --rerun PurePrecond --dry-run     # list what would run
"""

import argparse
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import statistics
import subprocess
import sys
import time

from fetch_upstream import ensure_upstream


FOLDER = Path(__file__).resolve().parent
REPO = FOLDER.parents[4]
# The default run's name; a run named NAME is kept in results/NAME/.
NAME = "all"
RESULTS = FOLDER / "results" / NAME
MODULE = "TapasTest.Applications.Monad.SpecMonad.VCGenComparison"
ENV = dict(os.environ, LEAN_NUM_THREADS="1")
CASES = ["AddSubCancel", "AddSubCancelDeep", "LetBinding", "ReaderState", "PurePrecond", "GetThrowSet",
         "DiteSplit", "MatchSplit"]
# Upstream's bench sizes (tests/bench/vcgen/vcgen_*.lean) where it has an entry. Upstream measures
# ReaderState, GetThrowSet, and MatchSplit by generation alone; complete proofs use small sizes,
# and GetThrowSet adds the sizes of upstream's integrated entry.
SIZES = {
    "AddSubCancel": {"complete": [200, 1200, 2200]},
    "AddSubCancelDeep": {"complete": [100, 500, 900]},
    "LetBinding": {"complete": [10, 50, 100]},
    "ReaderState": {"complete": [10, 50, 100], "generation": [600, 1600, 2600]},
    "PurePrecond": {"complete": [400, 2400, 4400]},
    "GetThrowSet": {"complete": [10, 50, 100, 200, 300], "generation": [200, 500, 800]},
    "DiteSplit": {"complete": [10, 50, 100]},
    "MatchSplit": {"complete": [10, 50, 100], "generation": [500, 1000, 1500]},
}
# Cases with upstream's tuned integrated configuration (`Case.finishSimp`).
TUNED = {"GetThrowSet"}
# Cases with upstream's Sym baseline (`Case.symGoal`).
SYM = {"AddSubCancel", "AddSubCancelDeep"}
# Cases with registered wp equations (`Case.wpEquations`), and the equations' `#time_setup` group.
WP = {"AddSubCancel": "state", "LetBinding": "state", "PurePrecond": "state",
      "ReaderState": "reader_state", "GetThrowSet": "except_state", "DiteSplit": "except_state"}
# Routes that rewrite the original program's wp: (Lean, reported).
WP_ROUTES = [("wpSimp", "wp-simp"), ("wpSym", "wp-sym")]
TIERS = {"customMonad": "custom-monad", "handWrittenSpecs": "hand-written-specs", "library": "library"}
# Routes that normalize a VC in a specification monad and share its one-time bridge: (Lean, reported).
NORMALIZATION = [("normalize", "normalize"), ("normalizeSym", "normalize-sym"), ("dsimp", "dsimp"),
                 ("symDsimp", "sym-dsimp")]
# (Lean route, reported route, Lean tier); mirrors `Harness.routes`, which lists Sym and the wp
# routes under hand-written specs.
ROUTES = {
    "complete": [("vcgen", "vcgen", "handWrittenSpecs"), ("vcgen", "vcgen", "library"),
                 ("vcgenFinish", "vcgen-finish", "handWrittenSpecs"),
                 ("vcgenFinish", "vcgen-finish", "library"),
                 ("vcgenFinishSimp", "vcgen-finish-simp", "handWrittenSpecs"),
                 ("vcgenFinishSimp", "vcgen-finish-simp", "library"),
                 ("sym", "sym", "handWrittenSpecs")] +
                [(route, label, tier) for route, label in NORMALIZATION for tier in TIERS] +
                [(route, label, "handWrittenSpecs") for route, label in WP_ROUTES],
    "generation": [("vcgen", "vcgen", "handWrittenSpecs"), ("vcgen", "vcgen", "library")] +
                  [(route, label, tier) for route, label in NORMALIZATION for tier in TIERS] +
                  [(route, label, "handWrittenSpecs") for route, label in WP_ROUTES],
}
# The one-time declarations each case uses besides its own, by their `#time_setup` labels: the
# program both add/sub cases share, and the operations of its bridge (Models.lean).
USES = {"AddSubCancel": ["AddSub", "state"], "AddSubCancelDeep": ["AddSub", "deep_state"],
        "LetBinding": ["state"], "ReaderState": ["reader_state", "reader_read"],
        "PurePrecond": ["flip"], "GetThrowSet": ["except_state", "throw"],
        "DiteSplit": ["except_state", "throw"], "MatchSplit": ["except_state", "throw"]}
SETUP_FILES = ["Programs.lean", "Models.lean", "Conditions.lean", "WPEquations.lean"]
REPETITIONS = 3
# A measurement fails when its timed part takes longer than TIMEOUT seconds. A process may take
# PROCESS_TIMEOUT seconds in all, since importing and the audits after the timers take time too.
TIMEOUT = 60
PROCESS_TIMEOUT = 90
# Resident memory of `lake` and its `lean` together.
MEMORY_MB = 8192
# Seconds between the runner's time and memory checks.
POLL = 0.5
# `ru_maxrss` is in bytes on macOS and in kilobytes on Linux.
MAXRSS_PER_MB = 2 ** 20 if sys.platform == "darwin" else 2 ** 10


def routes(case, mode):
    return [route for route in ROUTES[mode]
            if (route[0] != "vcgenFinishSimp" or case in TUNED) and (route[0] != "sym" or case in SYM)
            and (route[0] not in dict(WP_ROUTES) or case in WP)]


def tier_label(route, tier):
    """The reported tier; Sym and the wp routes have none."""
    return "-" if route == "sym" or route in dict(WP_ROUTES) else TIERS[tier]


# With `Elab.async`, the kernel would check the auxiliary theorem in which `grind` wraps each proof
# on another thread, outside the timers and in parallel with the measured work.
def source(case, mode, route, tier, n):
    return f'''import {MODULE}.BenchmarkCases
set_option Elab.async false
set_option experimental.vcgen true
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open TapasTest.Applications.Monad.SpecMonad Std.WP
#eval VCGenComparison.Harness.runOne VCGenComparison.cases "{case}" .{mode} .{route} .{tier} {n}
'''


def group_rss_mb(group):
    """Resident memory of a process group in MB."""
    table = subprocess.run(["ps", "-A", "-o", "pgid=,rss="], capture_output=True, text=True).stdout
    return sum(int(rss) for pgid, rss in map(str.split, table.splitlines()) if int(pgid) == group) / 1024


def run_lean(arguments, log, source="", timeout=None):
    """Run `lake env lean` with its output in `log`, enforcing the time and memory limits. Returns the
    status, the output, and the peak resident memory in MB. `lean` is `lake`'s child, so the whole
    process group is killed: killing `lake` alone leaves `lean` running, and Lean's own `-M` limit
    is not enforced."""
    with log.open("w") as output:
        process = subprocess.Popen(["lake", "env", "lean", *arguments], cwd=REPO, env=ENV, text=True,
                                   stdin=subprocess.PIPE, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        status = None
        # The largest sampled memory of the group; only a lower bound for a killed process.
        peak = 0
        try:
            try:
                process.stdin.write(source)
                process.stdin.close()
            except BrokenPipeError:
                pass
            start = check = time.monotonic()
            while True:
                # When `lake` exits, it has waited for `lean`, so `ru_maxrss` covers both.
                pid, code, usage = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    process.returncode = os.waitstatus_to_exitcode(code)
                    peak = max(peak, usage.ru_maxrss / MAXRSS_PER_MB)
                    break
                if time.monotonic() >= check:
                    rss = group_rss_mb(process.pid)
                    peak = max(peak, rss)
                    if timeout is not None and time.monotonic() - start > timeout:
                        status = "timeout"
                    elif rss > MEMORY_MB:
                        status = "memory"
                    if status:
                        break
                    check = time.monotonic() + POLL
                time.sleep(0.02)
        finally:
            # On a limit, and also when the runner itself is interrupted or terminated.
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
    if status:
        limit = f"after {timeout} seconds" if status == "timeout" else f"above {MEMORY_MB} MB"
        with log.open("a") as output:
            output.write(f"\n{status.upper()}: lake and lean killed {limit}.\n")
    return (status or ("ok" if process.returncode == 0 else "error"), log.read_text(errors="replace"),
            peak)


def measure_setup():
    """One-time declaration costs: medians over fresh elaborations of each file."""
    samples = {}
    for repetition in range(1, REPETITIONS + 1):
        for name in SETUP_FILES:
            status, output, _ = run_lean([str(FOLDER / name)],
                                         RESULTS / f"setup-{Path(name).stem}-{repetition}.log")
            if status != "ok":
                raise SystemExit(output[-8000:])
            for label, value in re.findall(r"SETUP (\S+): (\d+\.\d{2}) ms", output):
                samples.setdefault(label, []).append(float(value))
    return {label: statistics.median(values) for label, values in samples.items()}


def measure_baseline():
    """The median peak memory in MB of a process that imports the benchmark and measures nothing."""
    samples = []
    for repetition in range(1, REPETITIONS + 1):
        status, output, peak = run_lean(["--stdin"], RESULTS / f"baseline-{repetition}.log",
                                        f"import {MODULE}.BenchmarkCases\n")
        if status != "ok":
            raise SystemExit(output[-8000:])
        samples.append(peak)
    return statistics.median(samples)


def one_time(setup, case, tier):
    """Everything normalization needs once for this case and tier, independently of n."""
    tiers = {"all", tier} | ({"predtrans"} if tier != "custom-monad" else set())
    return sum(value for label, value in setup.items()
               if label.split(".")[0] in [case] + USES[case] and label.split(".")[1] in tiers)


def wp_one_time(setup, case):
    """The wp equations the wp routes use for this case, and the order rules."""
    return sum(value for label, value in setup.items()
               if label.split(".")[0] in ["order", WP[case]] and label.split(".")[1] == "wp")


def fingerprint():
    """What the measurements depend on: the benchmark's Lean modules, by lake's hash of BenchmarkCases
    and everything it imports, and the runner's settings."""
    trace = REPO / ".lake" / "build" / "lib" / "lean" / (MODULE.replace(".", "/") + "/BenchmarkCases.trace")
    settings = json.dumps([source("CASE", "MODE", "ROUTE", "TIER", 0), SIZES, REPETITIONS, TIMEOUT,
                           PROCESS_TIMEOUT, MEMORY_MB])
    return {"lean modules": json.loads(trace.read_text())["depHash"],
            "runner settings": hashlib.sha256(settings.encode()).hexdigest()[:16]}


def configurations():
    """Every configuration in measurement order: (case, mode, Lean route, reported route, Lean tier)."""
    return [(case, mode, route, label, tier) for case in CASES for mode in SIZES[case]
            for route, label, tier in routes(case, mode)]


def name(config):
    case, mode, route, label, tier = config
    return f"{case}/{mode}/{label}/{tier_label(route, tier)}"


def matches(config, patterns):
    """Whether a pattern matches the configuration's name, or the first components of it."""
    parts = name(config).split("/")
    return any(len(pattern.split("/")) <= len(parts) and
               all(fnmatch.fnmatchcase(part, glob) for part, glob in zip(parts, pattern.split("/")))
               for pattern in patterns)


def belongs(record, config):
    case, mode, route, label, tier = config
    return ((record["case"], record["mode"], record["route"], record["tier"]) ==
            (case, mode, label, tier_label(route, tier)))


def log_path(config, n, repetition):
    case, mode, route, label, tier = config
    parts = [case, mode, label, tier_label(route, tier), str(n), str(repetition)]
    return RESULTS / ("-".join(part for part in parts if part != "-") + ".log")


def complete(state, config):
    """Whether every size was measured in each repetition, failed, or was skipped after a failure."""
    statuses = [s for s in state["statuses"] if belongs(s, config)]
    for n in SIZES[config[0]][config[1]]:
        at = [s["status"] for s in statuses if s["n"] == n]
        if all(status == "ok" for status in at) and at.count("ok") < state["repetitions"]:
            return False
    return True


def save(state):
    """Write results.json, so that an interrupted run can be resumed."""
    temporary = RESULTS / "results.json.tmp"
    temporary.write_text(json.dumps(state, indent=2) + "\n")
    temporary.replace(RESULTS / "results.json")


def set_aside(state, config, folder):
    """Move a configuration's recorded measurements to `replaced`, and their logs to `folder`."""
    now = time.strftime("%Y-%m-%d %H:%M:%S")
    for key in ["runs", "statuses"]:
        state["replaced"] += [dict(r, record=key, replaced_on=now) for r in state[key] if belongs(r, config)]
        state[key] = [r for r in state[key] if not belongs(r, config)]
    for n in SIZES[config[0]][config[1]]:
        for repetition in range(1, state["repetitions"] + 1):
            log = log_path(config, n, repetition)
            if log.exists():
                folder.mkdir(exist_ok=True)
                log.rename(folder / log.name)


def result(output, key, mode):
    """The measurement reported by a successful Lean process for `key`, or None if its output does not
    contain exactly that, with the passed audits."""
    matched = re.findall(r"RESULT (\{[^\n]+\})", output)
    checked = re.search(r"CHECKED (\d+) VCs", output)
    if len(matched) != 1 or not checked or f"{mode} proof passed the kernel and audits." not in output:
        return None
    try:
        row = json.loads(matched[0])
    except json.JSONDecodeError:
        return None
    if {k: row.get(k) for k in key} != key:
        return None
    row = {k: int(v) if k.endswith("_hms") else v for k, v in row.items()}
    row["vc_count"] = int(checked[1])
    return row


def measure(state, config):
    """Measure a configuration at its sizes, saving every measurement. After a failure, the remaining
    repetitions and the larger sizes are skipped."""
    case, mode, route, label, tier = config
    failed = False
    for n in SIZES[case][mode]:
        key = dict(case=case, mode=mode, route=label, tier=tier_label(route, tier), n=n)
        if failed:
            state["statuses"].append(dict(key, status="skipped after smaller failure"))
            continue
        for repetition in range(1, state["repetitions"] + 1):
            status, output, peak = run_lean(["--stdin"], log_path(config, n, repetition),
                                            source(case, mode, route, tier, n), PROCESS_TIMEOUT)
            peak = round(peak)
            row = result(output, key, mode) if status == "ok" else None
            reason = f"process killed after {PROCESS_TIMEOUT} s" if status == "timeout" else ""
            if row is not None and row["total_hms"] > TIMEOUT * 100000:
                status, reason, row = "timeout", f"measured {row['total_hms'] / 100000:.1f} s", None
            if row is not None:
                row["repetition"] = repetition
                row["peak_mb"] = peak
                state["runs"].append(row)
            else:
                failed = True
                if status == "ok":
                    # An unexpected output is recorded as a failure rather than ending the run.
                    status, reason = "error", "no single RESULT line with the passed audits"
                elif status == "error":
                    reason = next((line.split("error:", 1)[1].strip() for line in output.splitlines()
                                   if "error:" in line), "Lean exited unsuccessfully")
                elif status == "memory":
                    reason = f"over {MEMORY_MB} MB"
            state["statuses"].append(dict(key, repetition=repetition, status=status, reason=reason,
                                          peak_mb=peak))
            save(state)
            print(f"{case} {mode} {label} {key['tier']} n={n} run={repetition}: {status}", flush=True)
            if failed:
                break
    save(state)


def report(state):
    """Record the medians in results.json and write RESULTS.md."""
    setup, runs, statuses = state["setup_ms"], state["runs"], state["statuses"]
    medians = []
    for case in CASES:
        for mode, sizes in SIZES[case].items():
            for n in sizes:
                for route, route_label, tier in routes(case, mode):
                    key = dict(case=case, mode=mode, route=route_label, tier=tier_label(route, tier), n=n)
                    samples = [row for row in runs if {k: row[k] for k in key} == key]
                    if len(samples) != state["repetitions"]:
                        continue
                    row = dict(key, vc_count=samples[0]["vc_count"])
                    for field in samples[0]:
                        if field.endswith("_hms"):
                            row[field.replace("_hms", "_ms")] = statistics.median(s[field] for s in samples) / 100
                    if all("peak_mb" in s for s in samples):
                        row["peak_mb"] = statistics.median(s["peak_mb"] for s in samples)
                    if route_label in {label for _, label in NORMALIZATION}:
                        row["one_time_ms"] = one_time(setup, case, TIERS[tier])
                    elif route_label in {label for _, label in WP_ROUTES}:
                        row["one_time_ms"] = wp_one_time(setup, case)
                    medians.append(row)
    state["medians_ms"] = medians
    save(state)

    def total_with_setup(row):
        return f"{row['total_ms'] + row['one_time_ms']:.2f}" if "one_time_ms" in row else "-"

    def cells(row, fields):
        """Times and peak memory; runs recorded before a column existed show `-`."""
        times = [f"{row[k + '_ms']:.2f}" if k + "_ms" in row else "-" for k in fields]
        peak = f"{row['peak_mb']:.0f}" if "peak_mb" in row else "-"
        return " | ".join(times + [total_with_setup(row), peak])

    upstream = ", ".join(f"`{commit}` ({cases})" for cases, commit in state["upstream_commits"].items())
    baseline = (f"; a process that only imports the benchmark peaks at {state['baseline_mb']:.0f} MB"
                if "baseline_mb" in state else "")
    lines = ["# Recorded comparison", "", state["lean"], "", f"Upstream: {upstream}.", "",
             "Times in milliseconds; each cell is the median of three fresh single-threaded Lean processes.",
             "A median of a per-run sum need not equal the sum of the displayed component medians.",
             "Total also covers instantiating metavariables (`instantiate_ms` in results.json).",
             "Share is the structural sharing of the proof before the kernel check. Peak is the peak resident",
             f"memory of the Lean process in MB, including the audits after the timers{baseline}.",
             "Routes, modes, sizes, and timer boundaries are described in [PROTOCOL.md](../PROTOCOL.md).",
             f"A measurement fails when its timed part takes longer than {TIMEOUT} seconds; the runner kills a process",
             f"after {PROCESS_TIMEOUT} seconds or above {MEMORY_MB} MB of resident memory. After a failure, the remaining",
             "repetitions and larger sizes of that configuration are skipped.", "",
             "## Complete proofs", "",
             "| Case | n | Route | Tier | VCs | Prepare | Generate | Grind | Solve | Share | Kernel | Total | "
             "Total + one-time | Peak |",
             "|---|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for row in medians:
        if row["mode"] == "complete":
            lines.append(f"| {row['case']} | {row['n']} | {row['route']} | {row['tier']} | {row['vc_count']} | "
                         f"{cells(row, ['prepare', 'generate', 'grind', 'solve', 'share', 'kernel', 'total'])} |")
    lines += ["", "## Generation only", "",
              "VCs are closed by `sorry`, as in upstream's entries for these cases. The kernel still",
              "checks the rest of the proof, including the parametricity bridge.", "",
              "| Case | n | Route | Tier | VCs | Prepare | Generate | Share | Kernel | Total | Total + one-time | Peak |",
              "|---|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for row in medians:
        if row["mode"] == "generation":
            lines.append(f"| {row['case']} | {row['n']} | {row['route']} | {row['tier']} | {row['vc_count']} | "
                         f"{cells(row, ['prepare', 'generate', 'share', 'kernel', 'total'])} |")
    lines += ["", "## One-time costs", "",
              "Independent of n. Normalization: `derive_parametric` for `step` and `loop`, the fidelity proof",
              "`loop_eq`, the operation soundness theorems, and the bridge to the upstream goal. The wp routes:",
              "their registered wp equations (`*.wp.*` below). Medians of three runs.", "",
              "| Case | custom-monad | hand-written-specs | library | wp routes |", "|---|---:|---:|---:|---:|"]
    for case in CASES:
        wp = f"{wp_one_time(setup, case):.2f}" if case in WP else "-"
        lines.append(f"| {case} | " + " | ".join(f"{one_time(setup, case, tier):.2f}" for tier in
                                                   ["custom-monad", "hand-written-specs", "library"]) + f" | {wp} |")
    lines += ["", "| Declaration | ms |", "|---|---:|"]
    lines += [f"| {label} | {value:.2f} |" for label, value in setup.items()]
    failures = [s for s in statuses if s["status"] != "ok"]
    lines += ["", f"All {len(runs)} successful samples passed the kernel, the original-goal check, and the axiom audit.", ""]
    missing = [name(config) for config in configurations() if not complete(state, config)]
    if missing:
        lines += [f"Not measured yet: {len(missing)} configurations, such as {missing[0]}; running this "
                  "run's name again measures them, and `--dry-run` lists them.", ""]
    if failures:
        lines += ["## Failures and resource limits", "", "| Case | Mode | Route | Tier | n | Status |",
                  "|---|---|---|---|---:|---|"]
        lines += [f"| {s['case']} | {s['mode']} | {s['route']} | {s['tier']} | {s['n']} | "
                  f"{s['status']}{': ' + s['reason'] if s.get('reason') else ''} |" for s in failures]
        lines.append("")
    (RESULTS / "RESULTS.md").write_text("\n".join(lines))


def main():
    global RESULTS
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--name", default=NAME,
                        help=f"the run, kept in results/NAME/ (default {NAME}); an existing run is continued")
    parser.add_argument("--out", type=Path, help="keep the run in this directory instead")
    parser.add_argument("--only", nargs="+", metavar="PATTERN", help="only these configurations (default: all)")
    parser.add_argument("--rerun", nargs="+", metavar="PATTERN",
                        help="measure these configurations of the run again, and only these; "
                             "`setup` measures the one-time costs again")
    parser.add_argument("--resume", action="store_true",
                        help="insist that the run exists, against a mistyped name; it is continued either way")
    parser.add_argument("--dry-run", action="store_true", help="list the configurations that would run, and exit")
    # For run.sh: print the run's directory, and exit.
    parser.add_argument("--where", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if not re.fullmatch(r"[\w.-]+", args.name):
        sys.exit(f"--name {args.name!r}: use letters, digits, `_`, `-`, and `.`")
    RESULTS = (args.out or FOLDER / "results" / args.name).resolve()
    if args.where:
        print(RESULTS)
        return
    path = RESULTS / "results.json"
    if (args.rerun or args.resume) and not path.exists():
        sys.exit(f"{'--rerun' if args.rerun else '--resume'}: there is no run in {RESULTS}")
    state = json.loads(path.read_text()) if path.exists() else None
    again = [pattern for pattern in args.rerun or [] if pattern != "setup"]
    selected = [config for config in configurations() if not args.only or matches(config, args.only)]
    for pattern in (args.only or []) + again:
        if not any(matches(config, [pattern]) for config in selected):
            sys.exit(f"{pattern} matches no selected configuration (CASE/MODE/ROUTE/TIER, e.g. "
                     "GetThrowSet or '*/generation/dsimp/*')")
    if args.rerun:
        selected = [config for config in selected if matches(config, again)]
    todo = [config for config in selected if state is None or args.rerun or not complete(state, config)]
    setup = state is None or not state["setup_ms"] or "setup" in (args.rerun or [])
    if args.dry_run:
        sessions = (state or {}).get("sessions") or [{}]
        print(f"continuing the run in {RESULTS}, started {sessions[0].get('started', 'earlier')}" if state
              else f"starting a run in {RESULTS}")
        for config in todo:
            print(("again: " if state is not None and complete(state, config) else "") + name(config))
        repetitions = state["repetitions"] if state else REPETITIONS
        processes = repetitions * sum(len(SIZES[config[0]][config[1]]) for config in todo)
        print(f"{len(todo)} of {len(selected)} selected configurations to run, at most {processes} Lean "
              f"processes" + (", after the one-time costs." if setup else "."))
        return

    ensure_upstream()
    RESULTS.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%d-%H%M%S")
    if state is None:
        # Move an earlier, unsaved start's loose files aside rather than mixing them with this run's.
        loose = [file for file in RESULTS.iterdir() if file.is_file()]
        if loose:
            (RESULTS / f"previous-{stamp}").mkdir()
            for file in loose:
                file.rename(RESULTS / f"previous-{stamp}" / file.name)
    build = subprocess.run(["lake", "build", MODULE + ".Verify"], cwd=REPO, env=ENV,
                           capture_output=True, text=True)
    (RESULTS / "build.log").write_text(build.stdout + build.stderr)
    if build.returncode:
        raise SystemExit(build.stdout + build.stderr)
    lean = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=REPO, text=True).strip()
    current = fingerprint()
    if state is None:
        commits = {cases: json.loads((FOLDER / "Upstream" / manifest).read_text())["commit"]
                   for cases, manifest in [("add/sub", "SOURCES-addsub.json"), ("other cases", "SOURCES.json")]}
        state = dict(lean=lean, upstream_commits=commits, threads=1, repetitions=REPETITIONS,
                     timeout_seconds=TIMEOUT, process_timeout_seconds=PROCESS_TIMEOUT,
                     memory_limit_mb=MEMORY_MB, sizes=SIZES,
                     setup_ms={}, runs=[], statuses=[])
    else:
        print(f"Continuing the run in {RESULTS}.", flush=True)
        if state["lean"] != lean:
            print(f"warning: the run in {RESULTS} was started on {state['lean']}, not {lean}", flush=True)
        first = next((s["fingerprint"] for s in state.get("sessions", []) if "fingerprint" in s), None)
        changed = [part for part, value in current.items() if first is not None and first.get(part) != value]
        if changed:
            print(f"warning: the {' and the '.join(changed)} changed since this run started, so its "
                  "measurements so far may not be comparable; start another --name, or --rerun them", flush=True)
    state.setdefault("replaced", [])
    # Each invocation, with what it measured on.
    state.setdefault("sessions", []).append(dict(started=time.strftime("%Y-%m-%d %H:%M:%S"), fingerprint=current,
                                                 only=args.only, rerun=args.rerun))
    save(state)
    if setup:
        state["setup_ms"] = measure_setup()
        state["baseline_mb"] = measure_baseline()
        save(state)
        print(f"One-time setup: {len(state['setup_ms'])} declarations; a process that only imports the "
              f"benchmark peaks at {state['baseline_mb']:.0f} MB.", flush=True)
    # Set aside the earlier measurements of everything that runs (again) first, so that an
    # interrupted --rerun can be continued with --only.
    for config in todo:
        set_aside(state, config, RESULTS / f"replaced-{stamp}")
    save(state)
    for config in todo:
        measure(state, config)
    report(state)
    print(f"Recorded results in {RESULTS}")


if __name__ == "__main__":
    # `pkill` sends SIGTERM; exiting through Python lets `run_lean` kill the running Lean process.
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    main()
