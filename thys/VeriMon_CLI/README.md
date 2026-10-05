# VeriMon: the verified monitor with MonPoly's command line

This session composes the verified parts of VeriMon into one program, VeriMon 2.0
(`verimon`), whose decisions are made in Isabelle/HOL and which reads MonPoly's
command line:

- the formula file is parsed by the verified parser (session `MFODL_Parser`);
- the signature file is read by a verified reader (theory `Signature`);
- the parsed formula is converted into the monitor's formula as MonPoly's front
  end does (theory `Formula_Conv`);
- the monitor is started (`vinit`, theory `MFODL_Monitor_Exec.Log_Monitor`)
  and runs on the log in chunks (`vfeed_chunk`, `vfinish`);
- the verdicts and messages are worded as MonPoly words them (theories
  `CLI_Options` and `CLI_Output`).

The OCaml driver (`src/verimon.ml`, `src/verimon_io.ml`) only reads the files that
`cli_main` asks for, prints the texts it is given, runs the loop over the log, and locates
errors in the log by line and column.

## Theories

| Theory | Content |
|---|---|
| `Signature` | Signature files: grammar `G_sig` over the log lexer's tokens, its language `sig_lang`, the reader `read_sig` with MonPoly's messages, and `read_sig_correct` |
| `Formula_Conv` | MonPoly's free-variable order (`MFOTL.free_vars`), its syntactic sugar (`normalize_syntax`, as MonPoly's front end applied it for VeriMon 1), the conversion `conv_formula` into `Formula.formula`, the folding of ground terms, and `sat_fold_ground` |
| `CLI_Options` | MonPoly's options and `Arg.parse`'s messages: `parse_command`, `config` |
| `CLI_Output` | Verdicts (`show_results`), timestamps (`-unix`), MonPoly's tuple order, and the messages for errors in the log |
| `CLI` | `cli_main`, and the correctness theorems `cli_run` and `verimon_correct` |
| `CLI_Code` | The code export (`src/verimon_code.ml`) |

## Correctness

`CLI.verimon_correct`: if `cli_main` starts the monitor on the contents of
the formula file and the signature file, then

- the formula file is lexed into tokens that the grammar of MonPoly's formulas
  derives (`mfodl_Formula`), denoting a formula `ψ0`;
- the signature file is lexed into tokens that the grammar of signatures
  derives (`sig_lang`), denoting a signature `S`;
- the monitor's formula `φ` is the conversion of `ψ0` (its negation with
  `-negate`), and `f` gives the types that the type checker infers for it;
- the run on a log reports an error exactly when the log's events of the
  formula's predicates and of undeclared predicates (all events with
  `-nofilterrel`) denote no prefix;
- on a log that denotes a prefix `π`, there is no error, and the verdicts are
  exactly `verdict_spec L φ f π`: the time points `i` below the progress on
  `π`, with their timestamps, and the tuples `v` over the free variables of
  `φ` such that `Formula.sat σ Map.empty (val … v) i φ'` holds on every
  well-typed trace `σ` that extends `π`, where `φ'` is `φ` with the inferred
  types.

`CLI.verimon_correct_online` states the same online, as the driver runs the
monitor. After the chunks read so far:

- the outputs so far contain an error exactly when the bytes read so far
  (restricted to the events the monitor keeps) denote no prefix;
- if the bytes read so far denote a prefix `π`, the outputs so far contain no
  error and their verdicts are exactly `verdict_spec L φ f π`;
- the outputs of a further chunk, after which the bytes denote `π'`, contain no
  error, and their verdicts are exactly `verdict_spec L φ f π' -
  verdict_spec L φ f π`, so every verdict is output once, as soon as the bytes
  that determine it have been read;
- the outputs at the end of the log are those of the prefix the whole log
  denotes, minus those of `π`;
- a chunk, or the end of the log, after which the bytes no longer denote a
  prefix outputs an error.

The types matter for aggregations (an aggregation's type annotation decides,
for example, whether `SUM` is an integer or a floating point sum), so the
semantics is that of `φ'`.

Not covered: the driver's printing of the verdicts (`verdict_out`), the
location of errors in the log, what is output after the first error, and the four functions that `CLI_Code` implements in OCaml (strings of
characters as byte strings, decimal representation of integers, and the test
whether a string is quoted).

## Building

```
cd thys && isabelle build -b -e -d . VeriMon_CLI
cp VeriMon_CLI/verimon_code.ocaml ../src/verimon_code.ml
```

The session processes the grammar and the parser from source (its parent is
`MFODL_Monitor_Exec`), which takes about 22 minutes.

The parser's tables are large: under `Code_Target_Nat`, natural number
literals would be exported as calls of `nat_of_integer` that ocamlopt compiles
into code, and it fails with a stack overflow. `CLI_Code` prints them as
constructor applications (`natlit`), which OCaml compiles into static data.

## Performance

Measured on the performance suite (`evaluation/perf`: 285 formulas on synthetic
logs of about 47 MB, best of 3, 5-second timeout, 2 workers on a 4-core
machine), with `python3 run_suite.py --systems verimon,cli,monpoly`, on
482050d8:

| | `verimon-cli` / `monpoly -verified` | `monpoly` / `monpoly -verified` |
|---|---|---|
| formulas both run | 285 | 264 |
| geometric mean | 1.01 | 1.08 |
| median | 1.01 | 1.09 |
| faster / more than 2x slower | 135 / 0 | 101 / 5 |
| verdict disagreements | none | none |

`verimon-cli` runs all formulas of the suite, among them `der-equiv`,
`A(x,y) AND (C(x) EQUIV C(y))`, which VeriMon's rewriting distributes into a
disjunction (the equation of `Rewriting.rewrite` for a disjunction one level
down a conjunction, as `EQUIV` produces). The largest ratio
is `lp-chain` (1.62), whose run outputs 100 MB of verdicts: what remains of
the printing's cost is the check that the monitor's order of the tuples is
MonPoly's (`rows_of`), which `monpoly -verified` does as it streams.

Start-up (`-check` on the 285 formulas, best of 5): 4.0 ms median for both
programs, a median ratio of 1.008; the verified formula parser, signature
reader and conversion cost no measurable time.

The verdicts are printed with `verdict_fold` (theory `CLI_Output`), which
passes each piece of the text and each integer of a tuple to the driver,
which appends them to one buffer; it is proved equal to the fold over the
pieces of `verdict_out` (`verdict_fold_eq`). With `verdict_out`'s lists, the
same suite had a geometric mean of 1.06 and `lp-chain` timed out (6.4 s
against 1.8 s).

## Differences from MonPoly and from VeriMon 1

VeriMon 1 was MonPoly's mode `monpoly -verified`: MonPoly's unverified front end
read the inputs and prepared the formula for the verified monitor. Before VeriMon
became a program of its own, a differential test replayed the commands of
MonPoly's tests with `monpoly -verified` and with `verimon` and compared
standard output, standard error and exit code. All 95 commands that ran
`monpoly -verified` gave the same output. Of all 841 `monpoly` commands (run
with `-verified` added, and without the lines in which MonPoly prints the input
or analyzed formula), 631 gave the same output; the others differed as follows:

- 141 used `-debug`, which prints MonPoly's internal state.
- 47 differed in the reason why a formula is not monitorable (MonPoly prints its
  own analysis of the subformula and of safe-range-ness; `verimon` the
  verified monitor's).
- 9 grepped for the analyzed formula, which `verimon` does not print.
- 6 differed in the message of a type error, which is the verified type
  checker's.
- 5 used `-load`, which is refused.
- 1 formula is monitorable only after MonPoly's own rewriting, to which
  `monpoly -verified` fell back when VeriMon's preparation failed;
  `verimon` does not.
- 1 differed in the message for a formula that the parser rejects.

In detail:

- The verified parser rejects some formulas that MonPoly's parser accepts (see
  `thys/MFODL_Parser/README.md`), and reports a rejection with its own message.
- MonPoly's checks of the input formula (`Rewriting.check_wff` and
  `check_syntax`) are done with MonPoly's messages for intervals, unbounded
  future operators and undeclared predicates; the checks of `LET` and of
  aggregations, whose messages print subformulas, and type errors are left to
  the conversion and to the verified type checker.
- `-check` and `-verbose` do not print the input or the analyzed formula.
- `EQUIV` is `(φ IMPLIES ψ) AND (ψ IMPLIES φ)`; MonPoly's conversion without
  rewriting has `(φ IMPLIES ψ) AND (ψ IMPLIES ψ)`.
- `-load` and `-combine` are refused; `-debug`, `-stats` and the options of
  MonPoly's own algorithm are accepted and ignored.
- The usage text names `verimon` and lists its options.
- MonPoly's log commands (`> get_pos <` and the like) are refused.

The messages that the verified front end prints are MonPoly's, word for word,
also where they name MonPoly's modules (for example
`Libmonpoly.Verified_adapter.UnsupportedFragment` for a formula outside the
supported fragment).

`tests/verimon.t` runs `verimon` on examples of verdicts, errors in the log, the
checks of the input, and the command line; the other tests in `tests/` are
MonPoly's and VeriMon 1's tests, run with `verimon`.
