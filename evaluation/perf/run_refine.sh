#!/usr/bin/env bash
# Run the performance suite on the current checkout only (both systems, MonPoly and -verified),
# for experiments after the master baseline (report0.md) has been run with run_both.sh.
#
# Results: results/{results.json,results.csv,report.md,ratios.svg}, copied to report.md and
# ratios.svg in this directory with a provenance line.
#
# Usage: evaluation/perf/run_refine.sh
# Environment: as for run_both.sh -- JOBS [2], REPS [3], TIMEOUT [5], BUDGET [3600], and
#   NAMES=a,b,c to run only those formulas (nothing is copied into this directory then).
exec env SKIP_MASTER=1 "$(dirname "$0")/run_both.sh" "$@"
