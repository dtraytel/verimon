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

| Session (directory) | Theory | Content |
|---|---|---|
| `MFODL_Grammar` (`.`) | `MFODL_Syntax` | The syntax tree: MonPoly's `MFOTL.formula` with named variables |
| | `MFODL_Grammar` | Tokens, the grammar `mfodl` and its semantic actions |
| `MFODL_Parser` (`Parser`) | `MFODL_Lexer` | An executable model of `src/formula_lexer.mll` (not verified) |
| | `MFODL_Post` | What MonPoly's actions do besides building the tree: numbering `_`, `add_ex`, checks |
| | `MFODL_Parser` | The parser `mfodl_parse`, its correctness, and `parse_formula` = lexer + parser + post-processing |
| `MFODL_Parser_Code` (`Parser/Code`) | `MFODL_Parser_Code` | Examples checked by evaluation, and the code export |

The sessions are separate because the `grammar` and `parser` commands are slow
on a grammar of this size (`MFODL_Grammar` takes about 4 minutes, most of it in
the inductive definitions of the relation; `MFODL_Parser` about 16 minutes, most
of it in evaluating the LR tables and the static check), and neither needs to
rerun unless the grammar changes.

Building and exporting the parser:

```
cd thys && isabelle build -b -e -d . MFODL_Parser_Code
cp MFODL_Parser/Parser/Code/verified_parser.ocaml ../src/verified_parser.ml
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

## Testing

`tools/parser_difftest.ml` (`parser_difftest`) runs both parsers on the same
inputs and compares the syntax trees; with `-lex` it compares the token streams
of the lexer model and of `src/formula_lexer.mll` on random strings of tricky
lexemes. `tests/verified_parser.t` runs a small instance of both.

## Performance

The exported parser takes about 30 ms per input character (a second for a
formula of a few dozen characters). The time goes into the LR driver of the
`grammar` package, which recomputes the closure of each state with its layout
anchors at run time, at a cost quadratic in the number of productions (211
here). The grammar has no layout annotations, so a driver that precomputed the
closures would suffice for it.

`src/verified_parser.ml` is large (about 11 MB), mostly the LR tables, in which
every nonterminal name is a list of characters.
