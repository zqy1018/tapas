#!/bin/sh
# Run run.py in the background with these arguments, e.g. --name tonight or --rerun GetThrowSet
# (see `python3 run.py --help` and PROTOCOL.md). Running a name again continues that run. It takes
# hours. Usage, from any directory:
#   sh path/to/run.sh [arguments of run.py]
set -eu
folder=$(cd "$(dirname "$0")" && pwd)
if pgrep -f "python.*VCGenComparison/run\.py" >/dev/null; then
  echo "A run is already in progress; stop it with: pkill -f 'python.*VCGenComparison/run\.py'" >&2
  exit 1
fi
# A leftover Lean process, e.g. after `kill -9` of the runner, would slow down every measurement.
# `lake env lean` starts it as `lean --stdin`; the anchor skips other commands that mention it.
if pgrep -f "^lean --stdin" >/dev/null; then
  echo "Lean processes from an earlier run are still running; stop them with: pkill -f '^lean --stdin'" >&2
  exit 1
fi
# Check the arguments and say what will run before starting: the run's folder and how much is left.
plan=$(python3 "$folder/run.py" --dry-run "$@")
echo "$plan" | sed -n '1p;$p'
# The console log goes with the run's results.
out=$(python3 "$folder/run.py" --where "$@")
mkdir -p "$out/console"
log="$out/console/$(date +%Y%m%d-%H%M%S).log"
# Keep the machine awake while it runs, where macOS's `caffeinate` exists.
awake=""
if command -v caffeinate >/dev/null; then awake="caffeinate -i"; fi
nohup $awake python3 -u "$folder/run.py" "$@" >"$log" 2>&1 &
echo "Started; follow with: tail -f $log"
echo "Results will be in $out/RESULTS.md; stop with: pkill -f 'python.*VCGenComparison/run\.py'"
