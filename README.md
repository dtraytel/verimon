VeriMon 2.0
===========

VeriMon is a monitor for metric first-order dynamic logic (MFODL). It checks a log, a sequence
of time-stamped databases of events, against a policy given as a formula, and reports at which
time points and for which values of its free variables the formula is satisfied.

VeriMon 2.0 is formally verified end to end. Its decisions are made by code generated from a
formalization in Isabelle/HOL (`thys/`):

- the formula file is parsed by a verified parser for MonPoly's formula syntax;
- the signature file is read by a verified reader;
- the parsed formula is converted, type checked, and, if needed, rewritten into a monitorable
  formula;
- the log is read by a verified parser and monitored by the verified monitor.

The correctness theorem covers this whole pipeline: the verdicts output on a log are exactly
those that the semantics of MFODL prescribes for the formula on the trace prefix the log
denotes (see [Correctness](#correctness)).

VeriMon reads MonPoly's command line and input formats and words its messages as MonPoly does,
so it can be used where [MonPoly](https://bitbucket.org/jshs/monpoly) was. VeriMon 1 was a mode
of MonPoly (`monpoly -verified`), in which MonPoly's unverified front end read the inputs and
prepared the formula for the verified monitor. VeriMon 2.0 is a program of its own.


Installation
------------

VeriMon is written in OCaml (version 4.14 or later) and built with Dune. It depends on the
Zarith library. With the [OPAM package manager](https://opam.ocaml.org):

```
opam install --deps-only .
dune build --release
dune install
```

`dune install` puts the `verimon` command on the PATH of the current OPAM switch (or under
`--prefix=PATH`). For development:

```
dune build              # build _build/default/src/verimon.exe
dune test               # run the tests (tests/*.t)
dune exec -- verimon ARGS
```

VeriMon is faster when compiled with flambda: create the switch with the
`ocaml-option-flambda` package, for example
`opam switch create verimon --packages=ocaml-variants.5.5.1+options,ocaml-option-flambda`,
and build with `dune build --release`, whose profile passes `-O3`.

A web version, the same monitor compiled to JavaScript with js_of_ocaml, is built with
`dune build --profile=release web/verimon_js.zip` (see `web/README.md`); it is deployed at
<https://dtraytel.github.io/verimon/>.


Usage
-----

```
verimon -sig <file> -formula <file> [-negate] [-log <file>]
        [-help] [-version] [-verbose] [-no_rw] [-no_mw]
        [-check] [-sigout] [-unix] [-mem] [-nonewlastts] [-nofilterrel]
        [-ignore_parse_errors] [-stop_at_first_viol]
```

The main options are:

```
-sig <file>            the signature file
-formula <file>        the formula file
-log <file>            the log file (default: standard input)
-negate                monitor the negation of the formula (report violations)
-check                 only check whether the formula is monitorable
-sigout                show the signature of the output (and exit)
-verbose               print the free variables and every time point
-unix                  timestamps are Unix time, printed as dates
-nonewlastts           do not add a last maximal timestamp at the end of the log
-nofilterrel           do not skip the events of predicates the formula does not use
-ignore_parse_errors   skip ill-formed entries of the log instead of stopping
-stop_at_first_viol    stop at the first verdict
-no_rw                 do not rewrite a formula that is not monitorable as it stands
-mem                   print the peak memory usage on standard error
-gc_minor_heap <n>     the OCaml GC's minor heap size in words
-gc_space_overhead <n> the OCaml GC's space overhead in percent
```

`verimon -help` lists all options. MonPoly's options that do not apply to VeriMon are accepted
and ignored, except `-load` and `-combine`, which are refused.


Example
-------

The policy "a report that is published must have been approved within the last 7 days" is the
formula (file `rv11.mfotl`)

```
publish(r) IMPLIES ONCE[0,7d] approve(r)
```

over the signature (file `rv11.sig`)

```
publish(int)
approve(int)
```

which declares two predicates with one integer argument each. A log (file `rv11.log`) lists
the events at each time point, after its timestamp:

```
@1307955600 approve(163) publish(160)
@1308477599 approve(187) publish(163) publish(152)
@1308496000 publish(187)
```

With `-negate`, VeriMon reports the violations of the policy:

```
$ verimon -sig rv11.sig -formula rv11.mfotl -log rv11.log -negate
@1307955600 (time point 0): (160)
@1308477599 (time point 1): (152)
```

Report 160 is published without an approval, and report 152 without one in the 7 days before;
report 163 is published 6 days after its approval, and report 187 on the day of its approval.
Since the formula uses days as a time unit, timestamps are seconds (Unix time). Errors and
other messages are written to standard error.

Formulas are written in MonPoly's syntax: predicates over variables and constants, equalities
and comparisons of terms with arithmetic, the Boolean connectives, `EXISTS` and `FORALL`, the
past and future temporal operators with intervals (`PREV`, `NEXT`, `ONCE`, `EVENTUALLY`,
`PAST_ALWAYS`, `ALWAYS`, `SINCE`, `UNTIL`, `TRIGGER`, `RELEASE`; future intervals must be
bounded), the regular expressions of `MATCHF` and `MATCHP`, aggregations (`CNT`, `SUM`, `AVG`,
`MIN`, `MAX`, `MED`), and `LET` and `LETPAST` definitions. A formula is monitorable if VeriMon
can compute its finite set of satisfying valuations at each time point; otherwise it rewrites
the formula, and reports that it is not monitorable if no rewrite helps.
`thys/MFODL_Parser/README.md` and `thys/VeriMon_CLI/README.md` list where VeriMon's reading of
the inputs differs from MonPoly's.


Correctness
-----------

Theorem `verimon_correct` (theory `CLI` in `thys/VeriMon_CLI`) states that whenever VeriMon
starts monitoring:

- the formula file and the signature file are derived by the grammars of MonPoly's formulas
  and signatures, and denote the formula and the signature that VeriMon monitors (with
  `-negate`, the formula's negation);
- on a log, an error is reported exactly when the log does not denote a trace prefix;
- on a log that denotes a trace prefix, the verdicts output are exactly the time points below
  the monitor's progress, with the tuples of values of the free variables that satisfy the
  formula there on every trace that extends the prefix.

`verimon_correct_online` states the same for the log read in chunks: after each chunk, the
verdicts output so far are those of the prefix read so far, and each verdict is output as soon
as the bytes that determine it have been read.

The unverified parts are small: the OCaml driver (`src/verimon.ml`, `src/verimon_io.ml`),
which reads the files and the log, prints the texts and verdicts the generated code gives it,
and locates errors in the log by line and column; four functions implemented in OCaml
(`src/verimon_runtime.ml`); and the code generator of Isabelle, the OCaml compiler and the
libraries used. `thys/VeriMon_CLI/README.md` describes the theorems in detail.


The formalization
-----------------

| Directory | Sessions | Content |
|---|---|---|
| `thys/MFOTL_Monitor_Devel` | `MFOTL_Monitor_Devel` | Traces, intervals, tables, event data, the abstract monitor (the logic's base) |
| `thys/MFODL_Logic` | `MFODL_Logic` | MFODL: syntax, semantics, typing, safety and monitorability, rewriting, VeriMon's preparation, the specification of a monitor |
| `thys/MFODL_Frontend` | `MFODL_Frontend` | From the parsed formula and signature to typed formulas |
| `thys/Monitor_DS` | `Monitor_DS` | Generic data structures: queues, order-statistic trees, red-black-tree sets, sliding-window aggregation |
| `thys/Generic_Join_Devel` | `Generic_Join_Devel` | Multi-way joins |
| `thys/MFODL_Monitor` | `MFODL_Monitor` | The monitoring algorithm, in a locale over its auxiliary structures and joins |
| `thys/MFODL_Monitor_Proof` | `MFODL_Monitor_Proof` | Progress, the algorithm's invariant and correctness |
| `thys/Monitor_Impl` | `Monitor_Impl` | The concrete auxiliary structures and joins and the algorithm's instance with them (definitions and code equations) |
| `thys/Monitor_Impl_Proof` | `Monitor_Impl_Proof` | The invariants of the concrete structures; the instance meets the algorithm's assumptions |
| `thys/Monitor_Exec` | `Monitor_Exec` | The executable monitor, the monitor on the bytes of a log, and the code-generator setup (definitions and code equations) |
| `thys/Monitor_Exec_Proof` | `Monitor_Exec_Proof` | The executable monitor simulates the algorithm and inherits its correctness |
| `thys/Log_Parser` | `Log_Parser` | The log and signature formats and their verified parsers |
| `thys/grammar` | `Grammar_Command`, `LR_Parser` | Grammars and verified LR parsers generated from them (a submodule) |
| `thys/MFODL_Parser` | `MFODL_Grammar`, `MFODL_Parser`, `MFODL_Parser_Code` | MonPoly's formula syntax and its verified parser |
| `thys/VeriMon_CLI` | `VeriMon_CLI` | The command line, the outputs, the end-to-end theorems, and the code export |

The theories are checked with Isabelle2025-2 and the
[Archive of Formal Proofs](https://www.isa-afp.org). After `git submodule update --init`,

```
cd thys
isabelle build -b -e -d . VeriMon_CLI
cp VeriMon_CLI/verimon_code.ocaml ../src/verimon_code.ml
```

checks all theories and exports the generated code, which is in the repository as
`src/verimon_code.ml`.


Performance
-----------

`evaluation/perf` is a suite of 285 formulas on synthetic logs, each chosen to exercise one
operator or one shape of formula. It times VeriMon, and, for comparison, an installed MonPoly
(`--monpoly`), and compares their verdicts; see `evaluation/perf/README.md`. On its latest run,
VeriMon 2.0 took 0.81 times the time of MonPoly's own algorithm (geometric mean over the 264
formulas both finish; faster on 236, none more than 2x slower), with the same verdicts
everywhere; the other 21 formulas are ones MonPoly does not monitor. Against VeriMon 1
(`monpoly -verified`) the geometric mean was 0.98, on an earlier run.


Repository layout
-----------------

```
README.md                 this file
LICENSE, LGPLv2.1         the license (LGPL 2.1 with a linking exception)
AUTHORS                   the authors
dune-project, dune        the Dune project (package verimon)
src/verimon.ml            the driver: files, log, output
src/verimon_io.ml         reading the log in chunks, positions of errors, run-time settings
src/verimon_code.ml       the code generated from thys/VeriMon_CLI
src/verimon_runtime.ml    the functions the generated code leaves to OCaml
tests/                    the tests (cram tests, run with dune test)
web/                      the web version (js_of_ocaml) with its examples
thys/                     the Isabelle/HOL formalization
evaluation/perf/          the performance suite
```


References
----------

[1] J. Schneider, D. Basin, S. Krstić, D. Traytel:
    "A Formally Verified Monitor for Metric First-Order Temporal Logic".
    In: Runtime Verification (RV 2019).

[2] D. Basin, T. Dardinier, L. Heimes, S. Krstić, M. Raszyk, J. Schneider, D. Traytel:
    "A Formally Verified, Optimized Monitor for Metric First-Order Dynamic Logic".
    In: Automated Reasoning (IJCAR 2020).

[3] S. Zingg, S. Krstić, M. Raszyk, J. Schneider, D. Traytel:
    "Verified First-Order Monitoring with Recursive Rules".
    In: Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2022).

[4] D. Basin, T. Dardinier, N. Hauser, L. Heimes, J. J. Huerta y Munive, N. Kaletsch,
    S. Krstić, E. Marsicano, M. Raszyk, J. Schneider, D. L. Tirore, D. Traytel, S. Zingg:
    "VeriMon: A Formally Verified Monitoring Tool".
    In: Theoretical Aspects of Computing (ICTAC 2022).

[5] D. Basin, F. Klaedtke, E. Zalinescu:
    "The MonPoly Monitoring Tool".
    In: International Workshop on Competitions, Usability, Benchmarks, Evaluation, and
    Standardisation for Runtime Verification Tools (RV-CuBES 2017).
