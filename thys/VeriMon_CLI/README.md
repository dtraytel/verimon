# The verified monitor with MonPoly's command line

This session composes the verified parts of VeriMon into one program,
`verimon-cli`, whose decisions are made in Isabelle/HOL and which reads
MonPoly's command line:

- the formula file is parsed by the verified parser (session `MFODL_Parser`);
- the signature file is read by a verified reader (theory `Signature`);
- the parsed formula is converted into the monitor's formula as MonPoly's front
  end does (theory `Formula_Conv`);
- the monitor is started (`vinit`, theory `MFODL_Monitor_Exec.Log_Monitor`)
  and runs on the log in chunks (`vfeed_chunk`, `vfinish`);
- the verdicts and messages are worded as MonPoly words them (theories
  `CLI_Options` and `CLI_Output`).

The OCaml driver `src/verimon_cli.ml` only reads the files that `cli_main`
asks for, prints the texts it is given, runs the loop over the log, and locates
errors in the log, as `monpoly -verified` does.

## Theories

| Theory | Content |
|---|---|
| `Signature` | Signature files: grammar `G_sig` over the log lexer's tokens, its language `sig_lang`, the reader `read_sig` with MonPoly's messages, and `read_sig_correct` |
| `Formula_Conv` | MonPoly's free-variable order (`MFOTL.free_vars`), its syntactic sugar (`normalize_syntax` with `-verified`), the conversion `conv_formula` into `Formula.formula`, the folding of ground terms, and `sat_fold_ground` |
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
  exactly the time points `i` below the progress on `π`, with their
  timestamps, and the tuples `v` over the free variables of `φ` such that
  `Formula.sat σ Map.empty (val … v) i φ'` holds on every well-typed trace `σ`
  that extends `π`, where `φ'` is `φ` with the inferred types.

The types matter for aggregations (an aggregation's type annotation decides,
for example, whether `SUM` is an integer or a floating point sum), so the
semantics is that of `φ'`.

Not covered: the driver's loop and its printing (the verdicts are those of
`vrun`, which the driver computes chunk by chunk), the location of errors in
the log, and the four functions that `CLI_Code` implements in OCaml (strings of
characters as byte strings, decimal representation of integers, and the test
whether a string is quoted).

## Building

```
cd thys && isabelle build -b -e -d . VeriMon_CLI
cp VeriMon_CLI/verimon_code.ml ../src/verimon_code.ml
```

The session processes the grammar and the parser from source (its parent is
`MFODL_Monitor_Exec`), which takes about 30 minutes.

The parser's tables are large: under `Code_Target_Nat`, natural number
literals would be exported as calls of `nat_of_integer` that ocamlopt compiles
into code, and it fails with a stack overflow. `CLI_Code` prints them as
constructor applications (`natlit`), which OCaml compiles into static data.

## Differences from `monpoly -verified`

`tools/verimon_cli_difftest.py` replays the commands of the cram tests with
both programs and compares their outputs. The known differences:

- The verified parser rejects some formulas that MonPoly's parser accepts (see
  `thys/MFODL_Parser/README.md`), and reports a rejection with its own message.
- `EQUIV` is `(φ IMPLIES ψ) AND (ψ IMPLIES φ)`; MonPoly's `-no_rw` path has
  `(φ IMPLIES ψ) AND (ψ IMPLIES ψ)`.
- `-check` and `-verbose` do not print the analyzed formula, and the reason
  why a formula is not monitorable is the verified monitor's.
- `-load` and `-combine` are refused.
