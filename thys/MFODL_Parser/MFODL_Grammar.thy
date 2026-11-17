theory MFODL_Grammar
  imports "MFODL_Syntax.Surface_Syntax" TIGER_Grammar.LR_Prec_Parse
begin

section \<open>Grammar of MFODL formulas\<close>

subsection \<open>Tokens\<close>

text \<open>The token classes of MonPoly's formula lexer. A token with a payload carries it as its lexeme,
  which the semantic actions convert. The datatype has only the \<open>code\<close> plugin: for 73
  constructors the others (\<open>size\<close>, quickcheck, transfer) take minutes, and nothing uses them.\<close>

datatype (plugins only: code) mtok =
    FALSE | TRUE | LPA | RPA | LSB | RSB | COM | SC | DOT | QM | LD
  | LESSEQ | EQ | LESS | GTR | GTREQ | STAR | LARROW | SUBSTRING | MATCHES
  | PLUS | MINUS | SLASH | MOD | F2I | I2F | DAY_OF_MONTH | MONTH | YEAR | FORMAT_DATE
  | R2S | S2R | I2S | S2I | F2S | S2F
  | NAME | STR_CST | REGEXP_CST | INTEGER | RAT | TU
  | LET | LETPAST | FRZ | IN | NOT | AND | OR | IMPL | EQUIV | EXISTS | FORALL
  | PREV | NEXT | EVENTUALLY | ONCE | ALWAYS | PAST_ALWAYS
  | SINCE | TRIGGER | UNTIL | RELEASE | BAR | FREX | PREX
  | CNT | MIN_KW | MAX_KW | SUM_KW | AVG | MED

type_synonym mtoken = \<open>(mtok, char) token\<close>

definition lexeme :: \<open>mtoken \<Rightarrow> string\<close> where
  \<open>lexeme t = s_txt (span t)\<close>


subsection \<open>Conversions for the semantic actions\<close>

definition digit_val :: \<open>char \<Rightarrow> int\<close> where
  \<open>digit_val c = int (of_char c) - int (of_char (CHR ''0''))\<close>

definition nat_of_digits :: \<open>string \<Rightarrow> int\<close> where
  \<open>nat_of_digits ds = foldl (\<lambda>n c. 10 * n + digit_val c) 0 ds\<close>

definition int_of_lexeme :: \<open>string \<Rightarrow> int\<close> where
  \<open>int_of_lexeme s = (case s of CHR ''-'' # ds \<Rightarrow> - nat_of_digits ds | ds \<Rightarrow> nat_of_digits ds)\<close>

text \<open>The lexer emits \<open>TU\<close> only for the units \<open>d\<close>, \<open>h\<close>,
  \<open>m\<close> and \<open>s\<close>.\<close>

definition unit_factor :: \<open>char \<Rightarrow> int\<close> where
  \<open>unit_factor c = (if c = CHR ''d'' then 24 * 60 * 60 else if c = CHR ''h'' then 60 * 60
     else if c = CHR ''m'' then 60 else 1)\<close>

definition units_of_lexeme :: \<open>string \<Rightarrow> int\<close> where
  \<open>units_of_lexeme s = unit_factor (last s) * nat_of_digits (butlast s)\<close>

text \<open>String constants and regular expressions lose their delimiters; escapes stay.\<close>

definition strip_quotes :: \<open>string \<Rightarrow> string\<close> where
  \<open>strip_quotes s = butlast (tl s)\<close>

definition strip_regexp :: \<open>string \<Rightarrow> string\<close> where
  \<open>strip_regexp s = butlast (drop 2 s)\<close>

text \<open>A bare formula as an atom: a test then a step for \<open>MATCHF\<close>, the reverse for
  \<open>MATCHP\<close>.\<close>

definition bare_atom :: \<open>formula \<Rightarrow> bool \<Rightarrow> regex\<close> where
  \<open>bare_atom f fut = (if fut then RConcat (RTest f) wild else RConcat wild (RTest f))\<close>

subsection \<open>Productions\<close>

text \<open>MonPoly's grammar with its precedences, as declarations of the \<^theory_text>\<open>grammar\<close>
  command. They restrict the parse trees of the ambiguous grammar to those that respect the levels,
  tightest first: \<open>NOT\<close>, \<open>AND\<close>, \<open>OR\<close>, \<open>IMPLIES\<close>, \<open>EQUIV\<close>, the unary temporal
  operators and the quantifiers (\<open>PFX\<close>), the binary temporal operators (\<open>TMP\<close>), and \<open>LET\<close>,
  \<open>LETPAST\<close>, \<open>FRZ\<close> and the aggregations (\<open>LETS\<close>); for terms, unary minus, the
  multiplicative and the additive operators; for regular expressions, star, concatenation and
  alternation. A prefix form may stand on the right of a tighter operator, where it extends as far
  as it can, as in MonPoly.\<close>

text \<open>The \<open>forbid\<close> declarations rule out what the verified parser rejects where MonPoly does
  not (see the README of this session). An aggregation with an empty group-by list and a
  parenthesised body (\<open>AGGP\<close>) ends a formula. In a regular expression, a bare comparison
  (\<open>BARET\<close>) only ends a concatenation that is not followed by \<open>+\<close>, is not starred, and, like
  a bare formula (\<open>SAFE\<close>), is not alone in parentheses, where it is the formula in
  parentheses.\<close>

grammar mfodl =
  tokens \<open>mtoken\<close>
  terminals
    "(" = \<open>LPA\<close> and ")" = \<open>RPA\<close> and "[" = \<open>LSB\<close> and "]" = \<open>RSB\<close> and
    "," = \<open>COM\<close> and ";" = \<open>SC\<close> and "." = \<open>DOT\<close> and "?" = \<open>QM\<close> and "_" = \<open>LD\<close> and
    "<=" = \<open>LESSEQ\<close> and "=" = \<open>EQ\<close> and "<" = \<open>LESS\<close> and ">" = \<open>GTR\<close> and ">=" = \<open>GTREQ\<close> and
    "*" = \<open>STAR\<close> and "<-" = \<open>LARROW\<close> and "SUBSTRING" = \<open>SUBSTRING\<close> and
    "MATCHES" = \<open>MATCHES\<close> and "+" = \<open>PLUS\<close> and "-" = \<open>MINUS\<close> and "/" = \<open>SLASH\<close> and
    "MOD" = \<open>MOD\<close> and "f2i" = \<open>F2I\<close> and "i2f" = \<open>I2F\<close> and "DAY_OF_MONTH" = \<open>DAY_OF_MONTH\<close> and
    "MONTH" = \<open>MONTH\<close> and "YEAR" = \<open>YEAR\<close> and "FORMAT_DATE" = \<open>FORMAT_DATE\<close> and
    "r2s" = \<open>R2S\<close> and "s2r" = \<open>S2R\<close> and "i2s" = \<open>I2S\<close> and "s2i" = \<open>S2I\<close> and
    "f2s" = \<open>F2S\<close> and "s2f" = \<open>S2F\<close> and
    "FALSE" = \<open>FALSE\<close> and "TRUE" = \<open>TRUE\<close> and "LET" = \<open>LET\<close> and "LETPAST" = \<open>LETPAST\<close> and
    "FRZ" = \<open>FRZ\<close> and "IN" = \<open>IN\<close> and "NOT" = \<open>NOT\<close> and "AND" = \<open>AND\<close> and "OR" = \<open>OR\<close> and
    "IMPLIES" = \<open>IMPL\<close> and "EQUIV" = \<open>EQUIV\<close> and "EXISTS" = \<open>EXISTS\<close> and "FORALL" = \<open>FORALL\<close> and
    "PREV" = \<open>PREV\<close> and "NEXT" = \<open>NEXT\<close> and "EVENTUALLY" = \<open>EVENTUALLY\<close> and
    "ONCE" = \<open>ONCE\<close> and "ALWAYS" = \<open>ALWAYS\<close> and "PAST_ALWAYS" = \<open>PAST_ALWAYS\<close> and
    "SINCE" = \<open>SINCE\<close> and "TRIGGER" = \<open>TRIGGER\<close> and "UNTIL" = \<open>UNTIL\<close> and
    "RELEASE" = \<open>RELEASE\<close> and "|>" = \<open>FREX\<close> and "<|" = \<open>PREX\<close> and
    "CNT" = \<open>CNT\<close> and "MIN" = \<open>MIN_KW\<close> and "MAX" = \<open>MAX_KW\<close> and "SUM" = \<open>SUM_KW\<close> and
    "AVG" = \<open>AVG\<close> and "MED" = \<open>MED\<close> and
    NAME and STR_CST and REGEXP_CST and INTEGER and RAT and TU
  precedence right "NOT" > left "AND" > left "OR" > right "IMPLIES" > left "EQUIV"
  precedence left "EQUIV" > right PFX > right TMP > right LETS > nonassoc AGGP
  precedence right UMINUS > left MUL > left ADD
  precedence nonassoc RPAR SAFE BARET > left RSTAR > right RCAT > right RPLUS
  forbid RCAT @ 0 right BARET
  forbid RPLUS @ 0 right BARET
  forbid RSTAR @ 0 direct BARET
  forbid RPAR @ 1 direct SAFE BARET
  forbid "EQUIV" @ 0 right AGGP
  forbid "IMPLIES" @ 0 right AGGP
  forbid "OR" @ 0 right AGGP
  forbid "AND" @ 0 right AGGP
  forbid TMP @ 0 right AGGP
  productions
    Formula :: \<open>formula\<close>
      = Formula BOp Intv Formula (prec TMP) \<Rightarrow> \<open>\<lambda>l c i r. c i l r\<close>
      | Formula BOp Formula (prec TMP) \<Rightarrow> \<open>\<lambda>l c r. c dfintv l r\<close>
      | Formula "EQUIV" Formula \<Rightarrow> \<open>FEquiv\<close>
      | Formula "IMPLIES" Formula \<Rightarrow> \<open>FImplies\<close>
      | Formula "OR" Formula \<Rightarrow> \<open>FOr\<close>
      | Formula "AND" Formula \<Rightarrow> \<open>FAnd\<close>
      | "NOT" Formula \<Rightarrow> \<open>FNeg\<close>
      | UOp Intv Formula (prec PFX) \<Rightarrow> \<open>\<lambda>c i f. c i f\<close>
      | UOp Formula (prec PFX) \<Rightarrow> \<open>\<lambda>c f. c dfintv f\<close>
      | Quant VarList "." Formula (prec PFX) \<Rightarrow> \<open>\<lambda>c vs f. c vs f\<close>
      | "LET" Pred "=" Formula "IN" Formula (prec LETS) \<Rightarrow> \<open>FLet\<close>
      | "LETPAST" Pred "=" Formula "IN" Formula (prec LETS) \<Rightarrow> \<open>FLetPast\<close>
      | "FRZ" Pred "=" Formula "IN" Formula (prec LETS) \<Rightarrow> \<open>FFrz\<close>
      | Var "<-" AggOp NAME Formula (prec LETS) \<Rightarrow> \<open>\<lambda>y op x f. FAggreg y op (lexeme x) [] f\<close>
      | Var "<-" AggOp NAME ";" VarList1 Formula (prec LETS) \<Rightarrow> \<open>\<lambda>y op x g f. FAggreg y op (lexeme x) g f\<close>
      | Var "<-" AggOp NAME ";" "(" Formula ")" (prec AGGP) \<Rightarrow> \<open>\<lambda>y op x f. FAggreg y op (lexeme x) [] f\<close>
      | Atom
  and
    BOp :: \<open>interval \<Rightarrow> formula \<Rightarrow> formula \<Rightarrow> formula\<close>
      = "SINCE" \<Rightarrow> \<open>FSince\<close> | "TRIGGER" \<Rightarrow> \<open>FTrigger\<close>
      | "UNTIL" \<Rightarrow> \<open>FUntil\<close> | "RELEASE" \<Rightarrow> \<open>FRelease\<close>
  and
    UOp :: \<open>interval \<Rightarrow> formula \<Rightarrow> formula\<close>
      = "PREV" \<Rightarrow> \<open>FPrev\<close> | "NEXT" \<Rightarrow> \<open>FNext\<close> | "EVENTUALLY" \<Rightarrow> \<open>FEventually\<close>
      | "ONCE" \<Rightarrow> \<open>FOnce\<close> | "ALWAYS" \<Rightarrow> \<open>FAlways\<close> | "PAST_ALWAYS" \<Rightarrow> \<open>FPastAlways\<close>
  and
    Quant :: \<open>string list \<Rightarrow> formula \<Rightarrow> formula\<close>
      = "EXISTS" \<Rightarrow> \<open>FExists\<close> | "FORALL" \<Rightarrow> \<open>FForAll\<close>
  and
    AggOp :: \<open>agg_op\<close>
      = "CNT" \<Rightarrow> \<open>ACnt\<close> | "MIN" \<Rightarrow> \<open>AMin\<close> | "MAX" \<Rightarrow> \<open>AMax\<close>
      | "SUM" \<Rightarrow> \<open>ASum\<close> | "AVG" \<Rightarrow> \<open>AAvg\<close> | "MED" \<Rightarrow> \<open>AMed\<close>
  and
    VarList :: \<open>string list\<close> = \<Rightarrow> \<open>[]\<close> | VarList1
  and
    VarList1 :: \<open>string list\<close>
      = NAME \<Rightarrow> \<open>\<lambda>v. [lexeme v]\<close>
      | VarList "," NAME \<Rightarrow> \<open>\<lambda>vs v. vs @ [lexeme v]\<close>
  and
    Var :: \<open>string\<close> = NAME \<Rightarrow> \<open>lexeme\<close>
  and
    Pred :: \<open>predicate\<close> = NAME "(" TermArgs ")" \<Rightarrow> \<open>\<lambda>p ts. (lexeme p, ts)\<close>
  and
    TermArgs :: \<open>trm list\<close>
      = \<Rightarrow> \<open>[]\<close>
      | TermArg \<Rightarrow> \<open>\<lambda>t. [t]\<close>
      | TermArg "," TermArgs \<Rightarrow> \<open>(#)\<close>
  and
    TermArg :: \<open>trm\<close> = Term | "_" \<Rightarrow> \<open>TVar ''_''\<close>
  and
    Atom :: \<open>formula\<close> = AtomS | AtomT | AtomR
  and
    AtomS :: \<open>formula\<close>
      = "(" Formula ")"
      | "FALSE" \<Rightarrow> \<open>FEqual (TCst (CInt 0)) (TCst (CInt 1))\<close>
      | "TRUE" \<Rightarrow> \<open>FEqual (TCst (CInt 0)) (TCst (CInt 0))\<close>
      | Pred \<Rightarrow> \<open>FPred\<close>
      | Term "MATCHES" Term "(" OptTerms ")" \<Rightarrow> \<open>FMatches\<close>
  and
    AtomT :: \<open>formula\<close>
      = Term "=" Term \<Rightarrow> \<open>FEqual\<close>
      | Term "<=" Term \<Rightarrow> \<open>FLessEq\<close>
      | Term "<" Term \<Rightarrow> \<open>FLess\<close>
      | Term ">" Term \<Rightarrow> \<open>\<lambda>a b. FLess b a\<close>
      | Term ">=" Term \<Rightarrow> \<open>\<lambda>a b. FLessEq b a\<close>
      | Term "SUBSTRING" Term \<Rightarrow> \<open>FSubstring\<close>
      | Term "MATCHES" Term \<Rightarrow> \<open>\<lambda>a b. FMatches a b []\<close>
  and
    AtomR :: \<open>formula\<close>
      = "|>" Intv Regex \<Rightarrow> \<open>\<lambda>i r. FFrex i (r True)\<close>
      | "|>" Regex \<Rightarrow> \<open>\<lambda>r. FFrex dfintv (r True)\<close>
      | "<|" Intv Regex \<Rightarrow> \<open>\<lambda>i r. FPrex i (r False)\<close>
      | "<|" Regex \<Rightarrow> \<open>\<lambda>r. FPrex dfintv (r False)\<close>
  and
    OptTerms :: \<open>trm option list\<close>
      = \<Rightarrow> \<open>[]\<close>
      | OptTerm \<Rightarrow> \<open>\<lambda>t. [t]\<close>
      | OptTerms "," OptTerm \<Rightarrow> \<open>\<lambda>ts t. ts @ [t]\<close>
  and
    OptTerm :: \<open>trm option\<close> = "_" \<Rightarrow> \<open>None\<close> | Term \<Rightarrow> \<open>Some\<close>
  and
    Intv :: \<open>interval\<close> = LBound "," RBound \<Rightarrow> \<open>Pair\<close>
  and
    LBound :: \<open>bound\<close>
      = "(" INTEGER \<Rightarrow> \<open>\<lambda>t. OBnd (int_of_lexeme (lexeme t))\<close>
      | "(" TU \<Rightarrow> \<open>\<lambda>t. OBnd (units_of_lexeme (lexeme t))\<close>
      | "[" Units \<Rightarrow> \<open>CBnd\<close>
  and
    RBound :: \<open>bound\<close>
      = Units ")" \<Rightarrow> \<open>OBnd\<close> | Units "]" \<Rightarrow> \<open>CBnd\<close>
      | "*" ")" \<Rightarrow> \<open>BInf\<close> | "*" "]" \<Rightarrow> \<open>BInf\<close>
  and
    Units :: \<open>int\<close>
      = TU \<Rightarrow> \<open>\<lambda>t. units_of_lexeme (lexeme t)\<close>
      | INTEGER \<Rightarrow> \<open>\<lambda>t. int_of_lexeme (lexeme t)\<close>
  and
    Term :: \<open>trm\<close>
      = Term "+" Term (prec ADD) \<Rightarrow> \<open>TPlus\<close> | Term "-" Term (prec ADD) \<Rightarrow> \<open>TMinus\<close>
      | Term "*" Term (prec MUL) \<Rightarrow> \<open>TMult\<close> | Term "/" Term (prec MUL) \<Rightarrow> \<open>TDiv\<close>
      | Term "MOD" Term (prec MUL) \<Rightarrow> \<open>TMod\<close>
      | "-" Term (prec UMINUS) \<Rightarrow> \<open>TUMinus\<close>
      | "(" Term ")"
      | Fun "(" Term ")" \<Rightarrow> \<open>\<lambda>f t. f t\<close>
      | Cst \<Rightarrow> \<open>TCst\<close>
      | Var \<Rightarrow> \<open>TVar\<close>
  and
    Fun :: \<open>trm \<Rightarrow> trm\<close>
      = "f2i" \<Rightarrow> \<open>TF2i\<close> | "i2f" \<Rightarrow> \<open>TI2f\<close> | "DAY_OF_MONTH" \<Rightarrow> \<open>TDayOfMonth\<close>
      | "MONTH" \<Rightarrow> \<open>TMonth\<close> | "YEAR" \<Rightarrow> \<open>TYear\<close> | "FORMAT_DATE" \<Rightarrow> \<open>TFormatDate\<close>
      | "r2s" \<Rightarrow> \<open>TR2s\<close> | "s2r" \<Rightarrow> \<open>TS2r\<close> | "i2s" \<Rightarrow> \<open>TI2s\<close>
      | "s2i" \<Rightarrow> \<open>TS2i\<close> | "f2s" \<Rightarrow> \<open>TF2s\<close> | "s2f" \<Rightarrow> \<open>TS2f\<close>
  and
    Cst :: \<open>cst\<close>
      = INTEGER \<Rightarrow> \<open>\<lambda>t. CInt (int_of_lexeme (lexeme t))\<close>
      | RAT \<Rightarrow> \<open>\<lambda>t. CFloat (lexeme t)\<close>
      | STR_CST \<Rightarrow> \<open>\<lambda>t. CStr (strip_quotes (lexeme t))\<close>
      | REGEXP_CST \<Rightarrow> \<open>\<lambda>t. CRegexp (strip_regexp (lexeme t))\<close>
  and
    Regex :: \<open>bool \<Rightarrow> regex\<close>
      = Regex "+" Regex (prec RPLUS) \<Rightarrow> \<open>\<lambda>a b d. RPlus (a d) (b d)\<close>
      | Regex Regex (prec RCAT) \<Rightarrow> \<open>\<lambda>a b d. RConcat (a d) (b d)\<close>
      | Regex "*" (prec RSTAR) \<Rightarrow> \<open>\<lambda>a d. RStar (a d)\<close>
      | "(" Regex ")" (prec RPAR)
      | "." \<Rightarrow> \<open>\<lambda>_. wild\<close>
      | RTestF "?" \<Rightarrow> \<open>\<lambda>f _. RTest f\<close>
      | RSafe (prec SAFE) \<Rightarrow> \<open>bare_atom\<close>
      | RBareT (prec BARET) \<Rightarrow> \<open>bare_atom\<close>
  and
    RSafe :: \<open>formula\<close> = "NOT" RSafe \<Rightarrow> \<open>FNeg\<close> | AtomS
  and
    RTestF :: \<open>formula\<close> = "NOT" RTestF \<Rightarrow> \<open>FNeg\<close> | AtomS | AtomT
  and
    RBareT :: \<open>formula\<close> = "NOT" RBareT \<Rightarrow> \<open>FNeg\<close> | AtomT

end
