VeriMon 2.0 is a verified monitor for metric first-order dynamic logic with MonPoly's command
line and input formats. The program is `verimon` (dune package `verimon`, `src/`).

Almost all of it is generated from the Isabelle/HOL formalization in `thys/`: the session
`VeriMon_CLI` exports `src/verimon_code.ml` (theory `CLI_Code`), which contains the formula
parser, the signature reader, the conversion and preparation of the formula, the log parser and
the monitor. That code is assumed to be correct and is not edited by hand; change the theories
and re-export it (`cd thys && isabelle build -b -e -d . VeriMon_CLI`, then copy
`thys/VeriMon_CLI/verimon_code.ocaml` to `src/verimon_code.ml`). The hand-written OCaml is the
driver (`src/verimon.ml`, `src/verimon_io.ml`) and the functions the export leaves to OCaml
(`src/verimon_runtime.ml`).

MonPoly is not part of this repository. To compare against it (the performance suite in
`evaluation/perf`, or by hand), use an installed MonPoly binary (`--monpoly` or `$MONPOLY`).
