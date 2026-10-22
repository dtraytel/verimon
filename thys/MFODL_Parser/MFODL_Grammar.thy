theory MFODL_Grammar
  imports "MFODL_Syntax.Surface_Syntax" LR_Parser.LR_Parser
begin

section \<open>Grammar of MFODL formulas\<close>

subsection \<open>Tokens\<close>

text \<open>The token classes of MonPoly's formula lexer. A token with a payload carries it as its lexeme,
  which the semantic actions convert.\<close>

datatype mtok =
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

text \<open>MonPoly's ocamlyacc precedences are compiled into the productions, so that the grammar is
  unambiguous and passes the LALR(1) check of the \<^theory_text>\<open>parser\<close> command.\<close>

text \<open>Each Boolean level \<open>X\<close> has variants \<open>XC\<close>, \<open>XM\<close> and
  \<open>XL\<close>: formulas ending in no open prefix, in a unary temporal operator or quantifier, or in
  \<open>LET\<close>, \<open>LETPAST\<close>, \<open>FRZ\<close> or an aggregation.\<close>

text \<open>Nonterminals such as \<open>FTerm\<close>, \<open>PTerm\<close> and \<open>RAtomF\<close> separate
  contexts with different followers, since the check pools the lookaheads of a production over its
  contexts.\<close>

grammar (relation) mfodl =
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
  productions
    Formula :: \<open>formula\<close>
      = ECM
      | EL
      | ECM BOp Intv Formula \<Rightarrow> \<open>\<lambda>l c i r. c i l r\<close>
      | ECM BOp Formula \<Rightarrow> \<open>\<lambda>l c r. c dfintv l r\<close>
  and
    BOp :: \<open>interval \<Rightarrow> formula \<Rightarrow> formula \<Rightarrow> formula\<close>
      = "SINCE" \<Rightarrow> \<open>FSince\<close> | "TRIGGER" \<Rightarrow> \<open>FTrigger\<close>
      | "UNTIL" \<Rightarrow> \<open>FUntil\<close> | "RELEASE" \<Rightarrow> \<open>FRelease\<close>
  and
    ECM :: \<open>formula\<close> = EC | EM
  and
    EC :: \<open>formula\<close> = EC "EQUIV" IC \<Rightarrow> \<open>FEquiv\<close> | IC
  and
    EM :: \<open>formula\<close> = EC "EQUIV" IM \<Rightarrow> \<open>FEquiv\<close> | IM
  and
    EL :: \<open>formula\<close> = EC "EQUIV" IL \<Rightarrow> \<open>FEquiv\<close> | IL
  and
    IC :: \<open>formula\<close> = OC "IMPLIES" IC \<Rightarrow> \<open>FImplies\<close> | OC
  and
    IM :: \<open>formula\<close> = OC "IMPLIES" IM \<Rightarrow> \<open>FImplies\<close> | OM
  and
    IL :: \<open>formula\<close> = OC "IMPLIES" IL \<Rightarrow> \<open>FImplies\<close> | OL
  and
    OC :: \<open>formula\<close> = OC "OR" AC \<Rightarrow> \<open>FOr\<close> | AC
  and
    OM :: \<open>formula\<close> = OC "OR" AM \<Rightarrow> \<open>FOr\<close> | AM
  and
    OL :: \<open>formula\<close> = OC "OR" AL \<Rightarrow> \<open>FOr\<close> | AL
  and
    AC :: \<open>formula\<close> = AC "AND" NC \<Rightarrow> \<open>FAnd\<close> | NC
  and
    AM :: \<open>formula\<close> = AC "AND" NM \<Rightarrow> \<open>FAnd\<close> | NM
  and
    AL :: \<open>formula\<close> = AC "AND" NL \<Rightarrow> \<open>FAnd\<close> | NL
  and
    NC :: \<open>formula\<close> = "NOT" NC \<Rightarrow> \<open>FNeg\<close> | Atom
  and
    NM :: \<open>formula\<close> = "NOT" NM \<Rightarrow> \<open>FNeg\<close> | PM
  and
    NL :: \<open>formula\<close> = "NOT" NL \<Rightarrow> \<open>FNeg\<close> | PL
  and
    PM :: \<open>formula\<close>
      = UOp Intv ECM \<Rightarrow> \<open>\<lambda>c i f. c i f\<close>
      | UOp ECM \<Rightarrow> \<open>\<lambda>c f. c dfintv f\<close>
      | Quant VarList "." ECM \<Rightarrow> \<open>\<lambda>c vs f. c vs f\<close>
  and
    PL :: \<open>formula\<close>
      = UOp Intv EL \<Rightarrow> \<open>\<lambda>c i f. c i f\<close>
      | UOp EL \<Rightarrow> \<open>\<lambda>c f. c dfintv f\<close>
      | Quant VarList "." EL \<Rightarrow> \<open>\<lambda>c vs f. c vs f\<close>
      | "LET" Pred "=" Formula "IN" Formula \<Rightarrow> \<open>FLet\<close>
      | "LETPAST" Pred "=" Formula "IN" Formula \<Rightarrow> \<open>FLetPast\<close>
      | "FRZ" Pred "=" Formula "IN" Formula \<Rightarrow> \<open>FFrz\<close>
      | Var "<-" AggOp NAME Formula \<Rightarrow> \<open>\<lambda>y op x f. FAggreg y op (lexeme x) [] f\<close>
      | Var "<-" AggOp NAME ";" VarList1 Formula \<Rightarrow> \<open>\<lambda>y op x g f. FAggreg y op (lexeme x) g f\<close>
      | Var "<-" AggOp NAME ";" "(" Formula ")" \<Rightarrow> \<open>\<lambda>y op x f. FAggreg y op (lexeme x) [] f\<close>
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
      | FArg \<Rightarrow> \<open>\<lambda>t. [t]\<close>
      | FArg "," TermArgsR \<Rightarrow> \<open>(#)\<close>
  and
    TermArgsR :: \<open>trm list\<close>
      = \<Rightarrow> \<open>[]\<close>
      | TermArg \<Rightarrow> \<open>\<lambda>t. [t]\<close>
      | TermArg "," TermArgsR \<Rightarrow> \<open>(#)\<close>
  and
    FArg :: \<open>trm\<close> = FTerm | "_" \<Rightarrow> \<open>TVar ''_''\<close>
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
      | Term "MATCHES" PTerm "(" OptTerms ")" \<Rightarrow> \<open>FMatches\<close>
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
    PTerm :: \<open>trm\<close>
      = Term "+" PTermM \<Rightarrow> \<open>TPlus\<close> | Term "-" PTermM \<Rightarrow> \<open>TMinus\<close> | PTermM
  and
    PTermM :: \<open>trm\<close>
      = TermM "*" PTermU \<Rightarrow> \<open>TMult\<close> | TermM "/" PTermU \<Rightarrow> \<open>TDiv\<close>
      | TermM "MOD" PTermU \<Rightarrow> \<open>TMod\<close> | PTermU
  and
    PTermU :: \<open>trm\<close> = "-" PTermU \<Rightarrow> \<open>TUMinus\<close> | PTermP
  and
    PTermP :: \<open>trm\<close>
      = "(" Term ")"
      | Fun "(" Term ")" \<Rightarrow> \<open>\<lambda>f t. f t\<close>
      | Cst \<Rightarrow> \<open>TCst\<close>
      | NAME \<Rightarrow> \<open>\<lambda>v. TVar (lexeme v)\<close>
  and
    OptTerms :: \<open>trm option list\<close>
      = \<Rightarrow> \<open>[]\<close>
      | FOptTerm \<Rightarrow> \<open>\<lambda>t. [t]\<close>
      | OptTerms "," OptTerm \<Rightarrow> \<open>\<lambda>ts t. ts @ [t]\<close>
  and
    FOptTerm :: \<open>trm option\<close> = "_" \<Rightarrow> \<open>None\<close> | FTerm \<Rightarrow> \<open>Some\<close>
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
      = Term "+" TermM \<Rightarrow> \<open>TPlus\<close> | Term "-" TermM \<Rightarrow> \<open>TMinus\<close> | TermM
  and
    TermM :: \<open>trm\<close>
      = TermM "*" TermU \<Rightarrow> \<open>TMult\<close> | TermM "/" TermU \<Rightarrow> \<open>TDiv\<close>
      | TermM "MOD" TermU \<Rightarrow> \<open>TMod\<close> | TermU
  and
    TermU :: \<open>trm\<close> = "-" TermU \<Rightarrow> \<open>TUMinus\<close> | TermP
  and
    TermP :: \<open>trm\<close>
      = "(" Term ")"
      | Fun "(" Term ")" \<Rightarrow> \<open>\<lambda>f t. f t\<close>
      | Cst \<Rightarrow> \<open>TCst\<close>
      | Var \<Rightarrow> \<open>TVar\<close>
  and
    FTerm :: \<open>trm\<close>
      = FTerm "+" TermM \<Rightarrow> \<open>TPlus\<close> | FTerm "-" TermM \<Rightarrow> \<open>TMinus\<close> | FTermM
  and
    FTermM :: \<open>trm\<close>
      = FTermM "*" TermU \<Rightarrow> \<open>TMult\<close> | FTermM "/" TermU \<Rightarrow> \<open>TDiv\<close>
      | FTermM "MOD" TermU \<Rightarrow> \<open>TMod\<close> | FTermU
  and
    FTermU :: \<open>trm\<close> = "-" TermU \<Rightarrow> \<open>TUMinus\<close> | FTermP
  and
    FTermP :: \<open>trm\<close>
      = "(" Term ")"
      | Fun "(" Term ")" \<Rightarrow> \<open>\<lambda>f t. f t\<close>
      | FCst \<Rightarrow> \<open>TCst\<close>
      | Var \<Rightarrow> \<open>TVar\<close>
  and
    FCst :: \<open>cst\<close>
      = INTEGER \<Rightarrow> \<open>\<lambda>t. CInt (int_of_lexeme (lexeme t))\<close>
      | RAT \<Rightarrow> \<open>\<lambda>t. CFloat (lexeme t)\<close>
      | STR_CST \<Rightarrow> \<open>\<lambda>t. CStr (strip_quotes (lexeme t))\<close>
      | REGEXP_CST \<Rightarrow> \<open>\<lambda>t. CRegexp (strip_regexp (lexeme t))\<close>
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
      = RConcN "+" Regex \<Rightarrow> \<open>\<lambda>a b d. RPlus (a d) (b d)\<close>
      | RConc
  and
    RConc :: \<open>bool \<Rightarrow> regex\<close>
      = RAtom RConc \<Rightarrow> \<open>\<lambda>a b d. RConcat (a d) (b d)\<close>
      | RAtom
      | RBareT \<Rightarrow> \<open>bare_atom\<close>
  and
    RConcN :: \<open>bool \<Rightarrow> regex\<close>
      = RAtom RConcN \<Rightarrow> \<open>\<lambda>a b d. RConcat (a d) (b d)\<close>
      | RAtom
  and
    RAtom :: \<open>bool \<Rightarrow> regex\<close> = RAtom2 | RSafe \<Rightarrow> \<open>bare_atom\<close>
  and
    RAtom2 :: \<open>bool \<Rightarrow> regex\<close>
      = "(" Regex2 ")"
      | "." \<Rightarrow> \<open>\<lambda>_. wild\<close>
      | RTestF "?" \<Rightarrow> \<open>\<lambda>f _. RTest f\<close>
      | RAtomS "*" \<Rightarrow> \<open>\<lambda>a d. RStar (a d)\<close>
  and
    RAtomS :: \<open>bool \<Rightarrow> regex\<close> = RAtom2 | RSafeS \<Rightarrow> \<open>bare_atom\<close>
  and
    Regex2 :: \<open>bool \<Rightarrow> regex\<close>
      = RConcNF "+" Regex \<Rightarrow> \<open>\<lambda>a b d. RPlus (a d) (b d)\<close>
      | RConc2
  and
    RConcNF :: \<open>bool \<Rightarrow> regex\<close>
      = RAtomF RConcN \<Rightarrow> \<open>\<lambda>a b d. RConcat (a d) (b d)\<close>
      | RAtomF
  and
    RConc2 :: \<open>bool \<Rightarrow> regex\<close>
      = RAtomF RConc \<Rightarrow> \<open>\<lambda>a b d. RConcat (a d) (b d)\<close>
      | RAtom2
  and
    RAtomF :: \<open>bool \<Rightarrow> regex\<close> = RAtom2 | RSafeF \<Rightarrow> \<open>bare_atom\<close>
  and
    RSafe :: \<open>formula\<close> = "NOT" RSafe \<Rightarrow> \<open>FNeg\<close> | AtomS
  and
    RSafeS :: \<open>formula\<close> = "NOT" RSafeS \<Rightarrow> \<open>FNeg\<close> | AtomS
  and
    RSafeF :: \<open>formula\<close> = "NOT" RSafeF \<Rightarrow> \<open>FNeg\<close> | AtomS
  and
    RTestF :: \<open>formula\<close> = "NOT" RTestF \<Rightarrow> \<open>FNeg\<close> | AtomS | AtomT
  and
    RBareT :: \<open>formula\<close> = "NOT" RBareT \<Rightarrow> \<open>FNeg\<close> | AtomT


end
