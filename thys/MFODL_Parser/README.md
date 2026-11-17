# A verified parser for MonPoly's formula syntax

This session defines MonPoly's formula grammar
(`src/formula_parser.mly` in MonPoly's sources) with the `grammar` command of
[TIGER_Lexer_Parser](https://www.isa-afp.org/entries/TIGER_Lexer_Parser.html) (AFP), and
MonPoly's formula lexer (`src/formula_lexer.mll`) with its `lexer` command. From the
grammar, the `parser` command generates an LALR(1) parser and proves it sound and complete:

    mfodl_parse_iff:  mfodl_parse w = Some φ ⟷ mfodl_Formula w φ

where `mfodl_Formula` is the inductive relation defined by the grammar: one
introduction rule per production, with the semantic actions as values. The lexer is
verified as well: `lex_correct` says that `lex` computes the lexing judgment of the
lexer specification (longest match, ties by rule order, as in flex and ocamllex).

## Sessions and theories

| Session (directory) | Theory | Content |
|---|---|---|
| `MFODL_Grammar` (`.`) | `MFODL_Grammar` | Tokens, the grammar `mfodl` and its semantic actions |
| `MFODL_Parser` (`Parser`) | `MFODL_Lexer` | MonPoly's `src/formula_lexer.mll` as a specification of the `lexer` command, the lexer `lex` and `lex_correct` |
| | `MFODL_Parser` | The parser `mfodl_parse`, its correctness, and `parse_formula` = lexer + parser + post-processing |
| `MFODL_Parser_Code` (`Parser/Code`) | `MFODL_Efficient_Actions` | Faster code equations for the semantic actions |
| | `MFODL_Parser_Examples` | The parser's tables in code, and examples checked by evaluation |

The syntax tree (MonPoly's `MFOTL.formula` with named variables, theory `Surface_Syntax`) and
the post-processing (what MonPoly's actions do besides building the tree: numbering `_`,
`add_ex`, checks; theory `Surface_Postprocessing`) are in session `MFODL_Syntax`
(`thys/MFODL_Syntax`), which the logic and the front end use without the parser.

The sessions are separate because the `grammar` and `parser` commands are slow
on a grammar of this size (`MFODL_Grammar` takes about 4 minutes, most of it in
the inductive definitions of the relation; `MFODL_Parser` about 4 minutes, most
of it in evaluating the tables and checks and in relating the parser to that
relation), and neither needs to rerun unless
the grammar changes.

VeriMon's code export (session `VeriMon_CLI`, `src/verimon_code.ml`) contains the parser. The
sessions alone are built with

```
cd thys && isabelle build -b -d . MFODL_Parser_Code
```

`MFODL_Grammar` is a child of the AFP session `TIGER_Lexer_Parser`, whose heap holds
both the grammar package (`TIGER_Grammar`) and the lexer package (`TIGER_Lexer`).

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
inputs, and the token streams of the earlier, hand-written lexer and of MonPoly's lexer on
random strings of tricky lexemes. The lexer of the `lexer` command was then compared with that
hand-written lexer by evaluation on 4118 random strings of the same kind of lexemes (keywords,
numbers, time units, quoted strings with escapes, `r"..."`, comments, the UTF-8 arrows, invalid
bytes): both gave the same tokens (class, offset, length and text) or both rejected. In this repository, `tests/verified_parser.t`
checks the messages for rejected formulas, and the other tests run VeriMon,
whose formulas all go through the parser.

## Performance

The measurements below were made with the earlier grammar package (a git submodule, from which
TIGER_Lexer_Parser grew) and the earlier, hand-written lexer with the code equations of
`MFODL_Efficient_Lexer`; they have not been repeated for the lexer of the `lexer` command.

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
| general driver of TIGER_Lexer_Parser    | 417 ms | 93.6 s  |
| simple driver (`grammar/lr/LR_Simple.thy`)         | 2.9 ms | 648 ms  |
| simple driver on indexed tables            | 381 µs | 84.1 ms |
| and code equations for the lexer           | 111 µs | 24.7 ms |
| on trie tables (`grammar/lr/LR_Trie.thy`)          | 50 µs  | 11.2 ms |
| numbered tokens (`grammar/lr/LR_Tok.thy`)          | 40 µs  | 8.8 ms  |
| product automaton (`grammar/lr/LR_Prod.thy`)       | 33 µs  | 7.2 ms  |
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
for the simple driver of TIGER_Lexer_Parser (`grammar/lr/LR_Simple.thy`): a stack
of state indices of two precomputed LR(0) automata, proved to compute the same
result as the package's general driver. Its code equation runs on tables that
are binary tries keyed by the bits of the index (`grammar/lr/LR_Trie.thy`): they are
static data, and with binary naturals (`Code_Binary_Nat`) a lookup follows the constructors
of the numeral without arithmetic (the code equations `tlookup_binary`); VeriMon's code,
and since the lexer package imports `Code_Target_Nat` also the examples, use target
integers instead. Productions and nonterminals are numbered, goto rows are
keyed by lookahead or nonterminal number, and the reduces licensed at a state
are tabulated by lookahead, so a step compares no names. Each input token
is paired with its number before the run (`grammar/lr/LR_Tok.thy`), and the run on
the paired input is proved equal to the run on the tokens. The number is
computed by a case distinction on the token's constructor (`mfodl_parse_tnum`,
defined by the `parser` command and proved equal to the search in the list of
terminals constructor by constructor). Then the
driver runs on the product of the two automata (`grammar/lr/LR_Prod.thy`): the 324
reachable pairs of states are numbered, a stack entry is one pair number, and
the tables give per pair number the shift and goto targets and, per
lookahead, the candidate reduces. The step is proved equal to the step on
pairs for stacks whose pairs are all reachable; that the list of pairs is
closed under shifts and gotos is checked by evaluation. A step looks up one
action table by pair number and lookahead (`grammar/lr/LR_Plain.thy`): the shift
target if there is one, otherwise the reduces, each with its production and
the number of its left-hand side; a second table gives the reduces at the
end of the input. This step is proved equal to the step on the separate
tables of shifts, reduce candidates and productions, for every stack.
Finally, the driver
stops a run that repeats a stack between two shifts (a loop of reductions) by
comparing the stack with one saved stack, replaced after 1, 2, 4, ... steps
(`grammar/lr/LR_Loop.thy`), instead of all stacks since the last shift: any check
that fires only on a repeated stack gives the same result, since a run that
repeats a stack loops. The general driver,
which computes the closure of every new state with its layout anchors at run
time, is about 8,000 times slower on the suite.

The lexer of the `lexer` command runs on DFA tables (263 states for the main mode, 5 for
comments) that the command evaluates and gives as code equations; it needs no further code
equations. The hand-written lexer it replaces needed code equations, proved equal to its
definitions, that avoided arithmetic on naturals and tried only the rules that can match at the
current character; they reduced it from 427 M to 13 M instructions.
`MFODL_Efficient_Actions` imports `Code_Abstract_Char`, which exports a
character as its code, an integer: comparing two characters then compares two
integers instead of eight bits, and `integer_of_char` needs no arithmetic
(OCaml strings are converted with `char_of_integer`). A pattern match on
a character literal, as in `int_of_lexeme` (`CHR ''-'' # ds`), still takes the
character apart into its bits; `digit_val` and `int_of_lexeme` get
code equations that compare instead.

`MFODL_Parser` generates the parser under `declare [[parser_literal_tables]]`: the
start state and the action table its code equation names are then evaluated
literals, which exported code holds as static data, instead of constants defined by
their terms, which generated code computes when it loads (and which VeriMon's export
cannot compile: under `Containers`, the grammar's symbols have no `ceq` and
`ccompare` instances).

An export of the parser by itself with binary naturals (`Code_Binary_Nat`) lets ocamlopt see
the tables as static data; with `Code_Target_Nat` the tables become some 36,000 `Z.of_int`
calls and ocamlopt fails with a stack overflow.
TIGER_Lexer_Parser can also run the driver on arrays with integer indices
(`declare [[parser_int_tables]]`, `grammar/lr/LR_Int.thy`), but converting the tables
when the module is loaded adds about 4.5 ms to every run. (VeriMon's export
prints the naturals of the tables as constructor applications instead, which
OCaml also compiles into static data; see `thys/VeriMon_CLI/README.md`.)

The parser's own export was about 2.6 MB, mostly the action and goto tables
of the product automaton as tries; a reduce entry holds its production.
