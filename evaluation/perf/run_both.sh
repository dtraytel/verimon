#!/usr/bin/env bash
# Run the performance suite twice, one run after the other on the same machine:
#   1. the starting point: a build of master ($MASTER), where -verified is the original VeriMon;
#   2. the current checkout (refine).
# Each run times both systems (MonPoly and -verified) on every formula of suite.txt.
#
# Results:
#   results_master/{results.json,results.csv,report.md,ratios.svg}
#   results/{results.json,results.csv,report.md,ratios.svg}
# and, as the README describes, report0.md/ratios0.svg (master) and report.md/ratios.svg
# (refine) in this directory, with a provenance line under the title.
#
# Usage: evaluation/perf/run_both.sh
# Environment (defaults in brackets): MASTER [025a1423], JOBS [2], REPS [3], TIMEOUT [5],
#   BUDGET [3600] (seconds of wall time per run), SKIP_MASTER=1 to rerun refine only,
#   NAMES=a,b,c to run only those formulas (a smoke test: nothing is copied into this directory).
set -euo pipefail

PERF=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$PERF/../.." && pwd)
MASTER=${MASTER:-025a1423}
JOBS=${JOBS:-2}
REPS=${REPS:-3}
TIMEOUT=${TIMEOUT:-5}
BUDGET=${BUDGET:-3600}
WORK=$(mktemp -d)
trap 'git -C "$ROOT" worktree remove --force "$WORK/master" 2>/dev/null || true; rm -rf "$WORK"' EXIT

cd "$ROOT"
REFINE=$(git rev-parse --short HEAD)
MASTER_SHORT=$(git rev-parse --short "$MASTER")
[ -z "$(git status --porcelain --untracked-files=no)" ] || echo "warning: the checkout has uncommitted changes; the refine run uses them"

echo "== building refine ($REFINE)"
dune build ./src/main.exe
cp _build/default/src/main.exe "$WORK/monpoly_refine"

if [ "${SKIP_MASTER:-0}" != 1 ]; then
  echo "== building master ($MASTER_SHORT)"
  git worktree add --quiet --detach "$WORK/master" "$MASTER" >/dev/null
  (cd "$WORK/master" && dune build ./src/main.exe)
  cp "$WORK/master/_build/default/src/main.exe" "$WORK/monpoly_master"
fi

cd "$PERF"
need_logs=0
for l in $(grep -v '^#' suite.txt | awk -F'|' 'NF >= 3 {gsub(/ /, "", $2); print $2}' | sort -u); do
  [ -f "logs/$l.log" ] || need_logs=1
done
[ -f logs/perf.sig ] || need_logs=1
if [ "$need_logs" = 1 ]; then
  echo "== generating logs"
  python3 gen_logs.py
fi

run() {  # run BIN OUT
  python3 run_suite.py --bin "$1" --out "$2" --jobs "$JOBS" --reps "$REPS" \
    --timeout "$TIMEOUT" --budget "$BUDGET" ${NAMES:+--names "$NAMES"}
  python3 plot.py "$2/results.json" "$2/ratios.svg"
}

# install REPORT SVG DEST_REPORT DEST_SVG TEXT: copy, inserting TEXT as the provenance line
install_report() {
  [ -z "${NAMES:-}" ] || return 0
  { head -n 2 "$1"; printf '%s\n\n' "$5"; tail -n +3 "$1"; } > "$3"
  cp "$2" "$4"
}

DAY=$(date +%F)
HOST=$(hostname)

if [ "${SKIP_MASTER:-0}" != 1 ]; then
  echo "== suite on master ($MASTER_SHORT)"
  run "$WORK/monpoly_master" results_master
  install_report results_master/report.md results_master/ratios.svg report0.md ratios0.svg \
    "The starting point: both systems from a build of master ($MASTER_SHORT), where \`-verified\` is the original VeriMon, on the same suite and logs as \`report.md\`.  Run on $DAY on $HOST, one run after the other with \`report.md\`, so the two compare."
fi

echo "== suite on refine ($REFINE)"
run "$WORK/monpoly_refine" results
install_report results/report.md results/ratios.svg report.md ratios.svg \
  "Both systems from refine ($REFINE).  Run on $DAY on $HOST, after the starting point on master (\`report0.md\`), so the two compare."

echo "== done"
grep -h "geometric mean" report0.md report.md || true
