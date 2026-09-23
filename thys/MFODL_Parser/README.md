# A verified parser for MonPoly's formula syntax

This session defines MonPoly's formula grammar
(`src/formula_parser.mly`) with the `grammar` command of the
[grammar](https://github.com/dtraytel/grammar) package (`thys/grammar`, a git
submodule). From it, the `parser` command generates an LALR(1) parser and proves
it sound and complete:

    mfodl_parse_iff:  mfodl_parse w = Some φ ⟷ mfodl_Formula w φ

where `mfodl_Formula` is the inductive relation defined by the grammar: one
introduction rule per production, with the semantic actions as values.

## Sessions and theories

`MFODL_Grammar` (this directory) holds the grammar, `MFODL_Parser` (`Parser/`)
the parser generated from it. The grammar is a session of its own because the
`grammar` command takes long (about 40 minutes, most of it defining the
decoders), and it only needs to rerun when the grammar changes.

| Theory | Content |
|---|---|
| `MFODL_Syntax` | The syntax tree: MonPoly's `MFOTL.formula` with named variables |
| `MFODL_Grammar` | Tokens, the grammar `mfodl` and its semantic actions |
| `Parser/MFODL_Lexer` | An executable model of `src/formula_lexer.mll` (not verified) |
| `Parser/MFODL_Post` | What MonPoly's actions do besides building the tree: numbering `_`, `add_ex`, checks |
| `Parser/MFODL_Parser` | The parser `mfodl_parse`, its correctness, `parse_formula` = lexer + parser + post-processing, and the code export |

Building and exporting the parser:

```
cd thys && isabelle build -b -e -d . MFODL_Parser
cp MFODL_Parser/Parser/verified_parser.ocaml ../src/verified_parser.ml
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
  continues a regular expression.

## Differences from MonPoly's parser

The grammar was checked against MonPoly's parser with
`tools/parser_difftest.ml` (random formulas and all formulas in the
repository). Where both accept, they build the same syntax tree. The verified
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
  those that `Str.regexp` rejects. The OCaml adapter
  (`src/verified_parser_adapter.ml`) compiles them and rejects the same ones.
- A time unit other than `d`, `h`, `m`, `s` (as in `5x`) is rejected by the
  lexer. MonPoly lexes it and then fails in the parser, so the outcome is the
  same.
