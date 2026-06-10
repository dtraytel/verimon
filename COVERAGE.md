# Test-suite coverage

The test suite (the cram tests under `tests/` and `verimon_tests/`) can be
measured for code coverage with [`bisect_ppx`](https://github.com/aantron/bisect_ppx).

## What is measured

`bisect_ppx` instruments every *point* (expression) and counts how often it is
executed. From this it reports:

* **statement coverage** — the fraction of expressions that were executed at
  least once;
* **branch coverage** — whether both sides of every `if`/`match`/`||`/`&&`
  were taken (enabled here; see the per-file report).

There is **no path coverage**: neither `bisect_ppx` nor any other mainstream
OCaml tool records whole execution paths (the set of all branch *combinations*
along a run). Path coverage is generally infeasible to measure exhaustively, so
statement + branch coverage is the practical maximum for OCaml. Where path
sensitivity matters (e.g. the temporal-operator window logic), it is covered by
adding targeted cram tests that drive specific branch combinations.

## One-time setup: a switch with bisect_ppx

The default development switch (OCaml 5.4 + the Jane Street `ppx*` stack) pins
`ppxlib` to a version newer than `bisect_ppx` accepts, so `bisect_ppx` cannot be
installed there. Create a dedicated switch instead:

```sh
opam switch create verimon-cov 5.2.0
eval $(opam env --switch=verimon-cov)
opam install -y dune zarith qcheck dune-build-info bisect_ppx
```

(The instrumentation stanza in `src/dune` is inert unless you pass
`--instrument-with bisect_ppx`, so the normal dev switch keeps building as
before.)

## Running

```sh
eval $(opam env --switch=verimon-cov)
scripts/coverage.sh
```

This builds the instrumented binary, runs the whole cram suite, prints a
per-file summary, and writes a browsable HTML report to
`_coverage/html/index.html`. Restrict the run with e.g.
`scripts/coverage.sh tests` to a subdirectory.

`_coverage/` is build output and is git-ignored.
