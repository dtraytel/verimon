#!/usr/bin/env bash
#
# Measure code coverage of the MonPoly/VeriMon test suite.
#
# Uses bisect_ppx, which records expression ("statement") coverage and per-point
# visit counts (from which branch coverage is derived). NOTE: true *path*
# coverage is not provided by any standard OCaml tool — see COVERAGE.md.
#
# Requires an opam switch that has bisect_ppx installed (the default dev switch
# usually cannot, due to a ppxlib version clash — see COVERAGE.md for a ready
# made switch). Run from anywhere:
#
#     scripts/coverage.sh            # instrument, run all tests, report
#     scripts/coverage.sh tests      # restrict to a subdir of tests
#
set -euo pipefail

cd "$(dirname "$0")/.."
ROOT="$(pwd)"
COV_DIR="$ROOT/_coverage"
RAW_DIR="$COV_DIR/raw"

if ! command -v bisect-ppx-report >/dev/null 2>&1; then
  echo "error: bisect-ppx-report not found in PATH." >&2
  echo "       Activate a switch with bisect_ppx, e.g.:" >&2
  echo "         eval \$(opam env --switch=verimon-cov)" >&2
  echo "       See COVERAGE.md for how to create it." >&2
  exit 1
fi

rm -rf "$COV_DIR"
mkdir -p "$RAW_DIR"

# Absolute prefix so the per-process .coverage files survive cram's sandbox cwd,
# which is a temporary directory that is removed after each test.
export BISECT_FILE="$RAW_DIR/bisect"

# Build everything instrumented and run the full cram suite. --force re-runs
# tests even if dune thinks they are up to date, so every run is exercised.
# A failing test still executes the binary and contributes coverage, so don't
# abort the report on test diffs — just surface them.
set +e
dune runtest --instrument-with bisect_ppx --force "$@"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  echo "warning: 'dune runtest' exited with $rc (some tests failed or differ);" >&2
  echo "         coverage below still reflects every binary invocation made." >&2
fi

echo
echo "=== Coverage summary (per file, then total) ==="
bisect-ppx-report summary --per-file --coverage-path "$RAW_DIR"

bisect-ppx-report html --coverage-path "$RAW_DIR" -o "$COV_DIR/html"
echo
echo "HTML report written to: $COV_DIR/html/index.html"
