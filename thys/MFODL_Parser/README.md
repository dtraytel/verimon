# A verified parser for MonPoly's formula syntax

This session defines MonPoly's formula grammar
(`src/formula_parser.mly` in MonPoly's sources) with the `grammar` command of the
[grammar](https://github.com/dtraytel/grammar) package (`thys/grammar`, a git
submodule). From it, the `parser` command generates an LALR(1) parser and proves
it sound and complete:

    mfodl_parse_iff:  mfodl_parse w = Some φ ⟷ mfodl_Formula w φ

where `mfodl_Formula` is the inductive relation defined by the grammar: one
introduction rule per production, with the semantic actions as values.

## Sessions and theories

| Session (directory) | Theory | Content |
|---|---|---|
| `MFODL_Grammar` (`.`) | `MFODL_Syntax` | The syntax tree: MonPoly's `MFOTL.formula` with named variables |
| | `MFODL_Grammar` | Tokens, the grammar `mfodl` and its semantic actions |
| `MFODL_Parser` (`Parser`) | `MFODL_Lexer` | An executable model of MonPoly's `src/formula_lexer.mll` (not verified) |
| | `MFODL_Post` | What MonPoly's actions do besides building the tree: numbering `_`, `add_ex`, checks |
| | `MFODL_Parser` | The parser `mfodl_parse`, its correctness, and `parse_formula` = lexer + parser + post-processing |
| `MFODL_Parser_Code` (`Parser/Code`) | `MFODL_Lexer_Code` | Code equations for the lexer |
| | `MFODL_Parser_Code` | Examples checked by evaluation |

The sessions are separate because the `grammar` and `parser` commands are slow
on a grammar of this size (`MFODL_Grammar` takes about 4 minutes, most of it in
the inductive definitions of the relation; `MFODL_Parser` about 17 minutes, most
of it in evaluating the LR tables and the static check), and neither needs to
rerun unless the grammar changes.

VeriMon's code export (session `VeriMon_CLI`, `src/verimon_code.ml`) contains the parser. The
sessions alone are built with

```
cd thys && isabelle build -b -d . MFODL_Parser_Code
```

The `grammar` package's own session `Grammar_Command` builds its PDF
documentation, so it needs LaTeX.

## From precedences to productions

ocamlyacc resolves the ambiguities of MonPoly's grammar with precedence
declarations. The `parser` command has none: it needs a grammar without LALR(1)
conflicts. So the precedences are compiled into the productions (see the text
in `MFODL_Grammar.thy`):

- one nonterminal per level of binary operators;
- three variants of each level for formulas that end in a prefix operator whose
  body extends to the right (closed, mid prefix, low prefix);
- regular expression atoms restricted to formulas that cannot absorb what
  continues a regular expression;
- separate copies of a few nonterminals for contexts with different followers.
  The `parser` command's LR machine pools the lookaheads of a production that
  is complete after one symbol over all contexts in which that symbol starts
  something, so its static determinism check is stricter than LALR(1).

The static check is part of the `parser` command: `mfodl_parse.complete` has no
premises only if the check succeeds.

## Differences from MonPoly's parser

The grammar was checked against MonPoly's parser with a differential test on
random formulas and on all formulas of MonPoly's repository (`tools/parser_difftest.ml`,
which ran both parsers in one program before VeriMon became a program of its own). Where both accept, they build the same syntax tree. The verified
parser rejects some formulas that MonPoly accepts; in each case it accepts the
formula once parentheses are added:

1. In a regular expression, a formula with a prefix operator (`PREV`, `ONCE`,
   `EXISTS`, `LET`, an aggregation, ...) or a nested `MATCHF`/`MATCHP` must be
   parenthesised when used as an atom, with or without `?`. MonPoly accepts
   `MATCHF[0,5] PREV P(x) Q(x)`; here it is `MATCHF[0,5] (PREV P(x)) Q(x)`.
2. A comparison (`t = u`, `t < u`, `SUBSTRING`, `MATCHES` without argument
   list) is a bare regular expression atom only at the end of a concatenation that
   is not followed by `+`: `MATCHF[0,5] P(x) x > 5` is accepted,
   `MATCHF[0,5] x > 5 P(x)` must be written `MATCHF[0,5] (x > 5) P(x)` or with a
   test `x > 5?`.
3. After the `;` of an aggregation, an empty group-by list is accepted only if
   the aggregated formula is parenthesised and ends the aggregation:
   `m <- MAX s; (φ)`. MonPoly also accepts, e.g., `m <- MAX s; NOT φ`.

Differences that do not come from the grammar:

- Regular expression constants `r"..."` are not compiled. MonPoly rejects
  those that `Str.regexp` rejects; VeriMon does not support `MATCHES`, and
  rejects formulas with it as `monpoly -verified` did.
- A time unit other than `d`, `h`, `m`, `s` (as in `5x`) is rejected by the
  lexer. MonPoly lexes it and then fails in the parser, so the outcome is the
  same.

## Testing

The differential test compared the syntax trees of both parsers on the same
inputs, and the token streams of the lexer model and of MonPoly's lexer on
random strings of tricky lexemes. In this repository, `tests/verified_parser.t`
checks the messages for rejected formulas, and the other tests run VeriMon,
whose formulas all go through the parser.

## Performance

On the 201 formulas of the performance suite (`evaluation/perf/suite.txt`,
9 to 48 tokens), the verified parser is 5 to 8.5 times slower than MonPoly's
parser (median 6.7): with MonPoly's parser at 1.4 to 5.6 µs per formula
(median 2.4 µs), about 16 µs at the median. The LR driver takes 71% of the
time, the lexer 21%, post-processing and conversion 8%. In a `monpoly -check`
run (about 5.5 ms) the difference is within the noise. Measured with the
differential test's timing mode, which printed, per formula, the CPU time in
microseconds of both parsers and that of the verified lexer, LR parser and the
rest. The earlier versions of
the export, on the same suite (median per formula):

| version                                    | median | total   |
|--------------------------------------------|--------|---------|
| general driver of the `grammar` package    | 417 ms | 93.6 s  |
| simple driver (`lr/LR_Simple.thy`)         | 2.9 ms | 648 ms  |
| simple driver on indexed tables            | 381 µs | 84.1 ms |
| and code equations for the lexer           | 111 µs | 24.7 ms |
| on trie tables (`lr/LR_Trie.thy`)          | 50 µs  | 11.2 ms |
| numbered tokens (`lr/LR_Tok.thy`)          | 40 µs  | 8.8 ms  |
| product automaton (`lr/LR_Prod.thy`)       | 33 µs  | 7.2 ms  |
| one saved stack (`LR_Loop.thy`)            | 30 µs  | 6.6 ms  |
| characters as integers                     | 23 µs  | 5.1 ms  |
| one action table (`LR_Plain.thy`)          | 19 µs  | 4.2 ms  |
| tokens numbered by a case distinction      | 16 µs  | 3.6 ms  |
| MonPoly's parser (ocamlyacc)               | 2.3 µs | 0.49 ms |

In instructions (callgrind, each suite formula parsed once) the current
parser executes 30 M, 22 M of them in the LR driver (with the semantic
actions) and 5 M in the lexer.
Numbering the lookahead token by a linear search in the list of terminals at
every step took 24 M of the LR driver's instructions; numbering each token
once, when it enters the input, took 7 M, and a case distinction on the
token instead of the search takes almost nothing. Running on the product automaton
instead of pairs of states reduced the step from 20 M to 12 M. Detecting
loops of reductions with one saved stack instead of all stacks since the last
shift saved another 5 M. Exporting characters as integers, with the code
equations described below, took the lexer from 14 M to 5 M and the semantic
actions from 9 M to 4 M. One action table instead of the tables of shifts,
reduce candidates and productions took the step from 22 M to 18 M, 2.5 M of
it in trie lookups. (The last four rows were measured against the previous
version in alternating runs, 9%, 24%, 16% and 15% faster, and scaled to the
earlier rows; the machine was slower at the time.)

The grammar has no layout annotations, so the `parser` command generates code
for the simple driver of the `grammar` package (`lr/LR_Simple.thy`): a stack
of state indices of two precomputed LR(0) automata, proved to compute the same
result as the package's general driver. Its code equation runs on tables that
are binary tries keyed by the bits of the index (`lr/LR_Trie.thy`): they are
static data, and with binary naturals a lookup follows the constructors of the
numeral without arithmetic (`MFODL_Parser_Code` declares the code equations
`tlookup_binary`). Productions and nonterminals are numbered, goto rows are
keyed by lookahead or nonterminal number, and the reduces licensed at a state
are tabulated by lookahead, so a step compares no names. Each input token
is paired with its number before the run (`lr/LR_Tok.thy`), and the run on
the paired input is proved equal to the run on the tokens. The number is
computed by a case distinction on the token's constructor (`mfodl_parse_tnum`,
defined by the `parser` command and proved equal to the search in the list of
terminals constructor by constructor). Then the
driver runs on the product of the two automata (`lr/LR_Prod.thy`): the 324
reachable pairs of states are numbered, a stack entry is one pair number, and
the tables give per pair number the shift and goto targets and, per
lookahead, the candidate reduces. The step is proved equal to the step on
pairs for stacks whose pairs are all reachable; that the list of pairs is
closed under shifts and gotos is checked by evaluation. A step looks up one
action table by pair number and lookahead (`lr/LR_Plain.thy`): the shift
target if there is one, otherwise the reduces, each with its production and
the number of its left-hand side; a second table gives the reduces at the
end of the input. This step is proved equal to the step on the separate
tables of shifts, reduce candidates and productions, for every stack.
Finally, the driver
stops a run that repeats a stack between two shifts (a loop of reductions) by
comparing the stack with one saved stack, replaced after 1, 2, 4, ... steps
(`lr/LR_Loop.thy`), instead of all stacks since the last shift: any check
that fires only on a repeated stack gives the same result, since a run that
repeats a stack loops. The general driver,
which computes the closure of every new state with its layout anchors at run
time, is about 8,000 times slower on the suite.

The lexer model (`MFODL_Lexer`) is written for readability; `MFODL_Parser_Code`
gives it code equations, proved equal to its definitions, that avoid
arithmetic on naturals and try only the rules that can match at the current
character. They reduced the lexer from 427 M to 13 M instructions.
`MFODL_Parser_Code` also imports `Code_Abstract_Char`, which exports a
character as its code, an integer: comparing two characters then compares two
integers instead of eight bits, and `integer_of_char` needs no arithmetic
(OCaml strings are converted with `char_of_integer`). A pattern match on
a character literal, as in `int_of_lexeme` (`CHR ''-'' # ds`), still takes the
character apart into its bits; `digit_val`, `int_of_lexeme` and `sign_len` get
code equations that compare instead.

`MFODL_Parser_Code` exports with binary naturals (`Code_Binary_Nat`), so that
ocamlopt sees the tables as static data; with `Code_Target_Nat` the tables
become some 36,000 `Z.of_int` calls and ocamlopt fails with a stack overflow.
The `grammar` package can also run the driver on arrays with integer indices
(`declare [[parser_int_tables]]`, `lr/LR_Int.thy`), but converting the tables
when the module is loaded adds about 4.5 ms to every run. (VeriMon's export
prints the naturals of the tables as constructor applications instead, which
OCaml also compiles into static data; see `thys/VeriMon_CLI/README.md`.)

The parser's own export was about 2.6 MB, mostly the action and goto tables
of the product automaton as tries; a reduce entry holds its production.
