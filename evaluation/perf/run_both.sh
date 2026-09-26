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
# The script first pulls the current branch (fast-forward only), builds, runs, and at the end
# commits the four report files (only those) and pushes the branch.
#
# Usage: evaluation/perf/run_both.sh
# Environment (defaults in brackets): MASTER [025a1423], JOBS [2], REPS [3], TIMEOUT [5],
#   BUDGET [3600] (seconds of wall time per run), SKIP_MASTER=1 to rerun refine only,
#   PULL [1] and PUSH [1] (0 to skip the pull, or the commit and push),
#   NAMES=a,b,c to run only those formulas (a smoke test: nothing is copied into this
#   directory, committed or pushed).
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

PULL=${PULL:-1}
PUSH=${PUSH:-1}
[ -z "${NAMES:-}" ] || PUSH=0
REPORTS="evaluation/perf/report.md evaluation/perf/ratios.svg"
[ "${SKIP_MASTER:-0}" = 1 ] || REPORTS="$REPORTS evaluation/perf/report0.md evaluation/perf/ratios0.svg"

cd "$ROOT"
BRANCH=$(git rev-parse --abbrev-ref HEAD)
[ "$BRANCH" != HEAD ] || { echo "error: detached HEAD; check out a branch first" >&2; exit 1; }
# tracked changes other than the report files themselves
dirty=$(git status --porcelain --untracked-files=no | grep -Ev ' evaluation/perf/(report0?\.md|ratios0?\.svg)$' || true)
if [ -n "$dirty" ]; then
  if [ "$PUSH" = 1 ]; then
    echo "error: uncommitted changes; commit or stash them, or run with PUSH=0:" >&2
    echo "$dirty" >&2
    exit 1
  fi
  echo "warning: the checkout has uncommitted changes; the refine run uses them"
fi

if [ "$PULL" = 1 ]; then
  echo "== pulling $BRANCH"
  git pull --ff-only origin "$BRANCH"
fi
REFINE=$(git rev-parse --short HEAD)
MASTER_SHORT=
if [ "${SKIP_MASTER:-0}" != 1 ]; then
  git rev-parse --verify -q "$MASTER^{commit}" >/dev/null || git fetch -q origin master
  MASTER_SHORT=$(git rev-parse --short "$MASTER^{commit}")
fi

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

if [ "$PUSH" = 1 ]; then
  cd "$ROOT"
  git add -- $REPORTS
  if git diff --cached --quiet -- $REPORTS; then
    echo "== the reports did not change; nothing to push"
  else
    what="refine $REFINE"
    [ "${SKIP_MASTER:-0}" = 1 ] || what="master $MASTER_SHORT and $what"
    git commit -q -m "perf: suite run on $what ($DAY, $HOST)" -- $REPORTS
    echo "== pushing $BRANCH"
    delay=2
    for attempt in 1 2 3 4 5; do
      if git push -u origin "$BRANCH"; then break; fi
      [ "$attempt" = 5 ] && { echo "error: push failed; the results are committed locally" >&2; exit 1; }
      git pull --rebase origin "$BRANCH" || { echo "error: rebase failed; resolve and push by hand" >&2; exit 1; }
      sleep "$delay"; delay=$((delay * 2))
    done
  fi
fi
