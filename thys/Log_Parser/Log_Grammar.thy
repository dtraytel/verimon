(*<*)
theory Log_Grammar
  imports "HOL-Library.Char_ord"
begin
(*>*)

section \<open>Grammar of the log format\<close>

text \<open>MonPoly's log format, by a lexical grammar @{text Glex} and a grammar @{text G_parser} of
  entries. Unlike MonPoly, a command keeps all its arguments, and the token after it is not skipped.\<close>

subsection \<open>Tokens and entries\<close>

datatype 's token = T_AT | T_LPAREN | T_RPAREN | T_LANGLE | T_RANGLE | T_LBRACE | T_RBRACE
  | T_COMMA | T_SEMICOLON | T_STR 's

text \<open>Strings stay uninterpreted, and their type is a parameter, so that the executable parser
  can use byte strings.\<close>

datatype 's item = Entry 's "('s \<times> 's list) list" | Command 's "'s token list"

subsection \<open>Lexical grammar\<close>

definition isWhiteSpace :: "char \<Rightarrow> bool" where
  "isWhiteSpace c \<longleftrightarrow> c = CHR '' '' \<or> c = CHR 0x09 \<or> c = CHR 0x0A \<or> c = CHR 0x0D"

definition isLineCommentEnd :: "char \<Rightarrow> bool" where
  "isLineCommentEnd c \<longleftrightarrow> c = CHR 0x0A \<or> c = CHR 0x0D"

text \<open>A comment at the end of the input need not end with a line end; @{text lexes} adds this
  case, since no token can follow such a comment.\<close>

inductive isWhiteString :: "string \<Rightarrow> bool" where
  isWS_Nil: "isWhiteString []"
| isWS_Space: "isWhiteSpace c \<Longrightarrow> isWhiteString s \<Longrightarrow> isWhiteString (c # s)"
| isWS_Comment: "list_all (Not \<circ> isLineCommentEnd) s \<Longrightarrow> isLineCommentEnd c \<Longrightarrow> isWhiteString s' \<Longrightarrow>
    isWhiteString (CHR ''#'' # s @ c # s')"

definition isSimpleChar :: "char \<Rightarrow> bool" where
  "isSimpleChar c \<longleftrightarrow>
    CHR ''0'' \<le> c \<and> c \<le> CHR ''9'' \<or> CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'' \<or> CHR ''a'' \<le> c \<and> c \<le> CHR ''z'' \<or>
    c = CHR ''_'' \<or> c = CHR ''['' \<or> c = CHR '']'' \<or> c = CHR ''/'' \<or> c = CHR '':'' \<or> c = CHR ''-'' \<or>
    c = CHR ''.'' \<or> c = CHR ''!''"

abbreviation isSimpleString :: "string \<Rightarrow> bool" where
  "isSimpleString s \<equiv> s \<noteq> [] \<and> list_all isSimpleChar s"

inductive isQuoted :: "string \<Rightarrow> bool" where
  isQuoted_Nil: "isQuoted []"
| isQuoted_Char: "c \<noteq> CHR 0x22 \<Longrightarrow> c \<noteq> CHR 0x5C \<Longrightarrow> isQuoted s \<Longrightarrow> isQuoted (c # s)"
| isQuoted_Escape: "isQuoted s \<Longrightarrow> isQuoted (CHR 0x5C # c # s)"

inductive GToken :: "string \<Rightarrow> string token \<Rightarrow> bool" where
  GToken_AT: "GToken ''@'' T_AT"
| GToken_LPAREN: "GToken ''('' T_LPAREN"
| GToken_RPAREN: "GToken '')'' T_RPAREN"
| GToken_LANGLE: "GToken ''<'' T_LANGLE"
| GToken_RANGLE: "GToken ''>'' T_RANGLE"
| GToken_LBRACE: "GToken ''{'' T_LBRACE"
| GToken_RBRACE: "GToken ''}'' T_RBRACE"
| GToken_COMMA: "GToken '','' T_COMMA"
| GToken_SEMICOLON: "GToken '';'' T_SEMICOLON"
| GToken_simple: "isSimpleString s \<Longrightarrow> GToken s (T_STR s)"
| GToken_quoted: "isQuoted s \<Longrightarrow> GToken (CHR 0x22 # s @ [CHR 0x22]) (T_STR s)"
| GToken_rquoted: "isQuoted s \<Longrightarrow> GToken (CHR ''r'' # CHR 0x22 # s @ [CHR 0x22]) (T_STR s)"

text \<open>Maximal munch: a simple string is never followed by a simple character, and @{text r} never
  by a double quote, which would make it the prefix of a quoted string.\<close>

definition munch :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "munch s1 s2 \<longleftrightarrow> (isSimpleString s1 \<longrightarrow>
    s2 = [] \<or> \<not> isSimpleChar (hd s2) \<and> (s1 = ''r'' \<longrightarrow> hd s2 \<noteq> CHR 0x22))"

inductive Glex :: "string \<Rightarrow> string token list \<Rightarrow> bool" where
  Glex_WS: "isWhiteString w \<Longrightarrow> Glex w []"
| Glex_Token: "isWhiteString w \<Longrightarrow> GToken s1 t \<Longrightarrow> munch s1 s2 \<Longrightarrow> Glex s2 ts \<Longrightarrow>
    Glex (w @ s1 @ s2) (t # ts)"

definition lexes :: "string \<Rightarrow> string token list \<Rightarrow> bool" where
  "lexes s ts \<longleftrightarrow> Glex s ts \<or>
    (\<exists>s1 c. s = s1 @ CHR ''#'' # c \<and> list_all (Not \<circ> isLineCommentEnd) c \<and> Glex s1 ts)"

subsection \<open>Grammar of entries\<close>

inductive G_fields :: "'s token list \<Rightarrow> 's list \<Rightarrow> bool" where
  G_fields_one: "G_fields [T_STR f] [f]"
| G_fields_more: "G_fields fs vs \<Longrightarrow> G_fields (T_STR f # T_COMMA # fs) (f # vs)"

inductive G_tuple :: "'s token list \<Rightarrow> 's list \<Rightarrow> bool" where
  G_tuple_empty: "G_tuple [T_LPAREN, T_RPAREN] []"
| G_tuple_fields: "G_fields fs vs \<Longrightarrow> G_tuple (T_LPAREN # fs @ [T_RPAREN]) vs"

inductive G_tuples :: "'s token list \<Rightarrow> 's list list \<Rightarrow> bool" where
  G_tuples_Nil: "G_tuples [] []"
| G_tuples_Cons: "G_tuple tu v \<Longrightarrow> G_tuples tus vs \<Longrightarrow> G_tuples (tu @ tus) (v # vs)"

text \<open>A name without tuples stands for the nullary event.\<close>

inductive G_table :: "'s token list \<Rightarrow> ('s \<times> 's list) list \<Rightarrow> bool" where
  G_table_bare: "G_table [T_STR p] [(p, [])]"
| G_table_tuples: "G_tuples tus vs \<Longrightarrow> vs \<noteq> [] \<Longrightarrow> G_table (T_STR p # tus) (map (Pair p) vs)"

inductive G_db :: "'s token list \<Rightarrow> ('s \<times> 's list) list \<Rightarrow> bool" where
  G_db_empty: "G_db [] []"
| G_db_table: "G_table tb evs \<Longrightarrow> G_db db evs' \<Longrightarrow> G_db (tb @ db) (evs @ evs')"

inductive G_logentry :: "'s token list \<Rightarrow> 's item \<Rightarrow> bool" where
  G_logentry_no_sc: "G_db db evs \<Longrightarrow> G_logentry (T_AT # T_STR ts # db) (Entry ts evs)"
| G_logentry_sc: "G_db db evs \<Longrightarrow> G_logentry (T_AT # T_STR ts # db @ [T_SEMICOLON]) (Entry ts evs)"

fun cmd_arg :: "'s token \<Rightarrow> bool" where
  "cmd_arg T_AT = False"
| "cmd_arg T_SEMICOLON = False"
| "cmd_arg T_LANGLE = False"
| "cmd_arg T_RANGLE = False"
| "cmd_arg _ = True"

inductive G_command :: "'s token list \<Rightarrow> 's item \<Rightarrow> bool" where
  G_command: "list_all cmd_arg args \<Longrightarrow> G_command (T_RANGLE # T_STR c # args @ [T_LANGLE]) (Command c args)"

inductive G_parser :: "'s token list \<Rightarrow> 's item list \<Rightarrow> bool" where
  G_parser_empty: "G_parser [] []"
| G_parser_log: "G_logentry le e \<Longrightarrow> G_parser ls es \<Longrightarrow> G_parser (le @ ls) (e # es)"
| G_parser_cmd: "G_command cmd e \<Longrightarrow> G_parser ls es \<Longrightarrow> G_parser (cmd @ ls) (e # es)"

definition log_lang :: "string \<Rightarrow> string item list \<Rightarrow> bool" where
  "log_lang s es \<longleftrightarrow> (\<exists>ts. lexes s ts \<and> G_parser ts es)"

subsection \<open>Composing results of runs\<close>

lemma map_option_apfst_Nil[simp]: "map_option (apfst ((@) [])) x = x"
  by (cases x) auto

lemma map_option_apfst_append[simp]:
  "map_option (apfst ((@) a)) (map_option (apfst ((@) b)) x) = map_option (apfst ((@) (a @ b))) x"
  by (cases x) auto

lemma map_option_append[simp]: "map_option ((@) a) (map_option ((@) b) x) = map_option ((@) (a @ b)) x"
  by (cases x) auto

lemma map_option_append_Nil[simp]: "map_option ((@) []) x = x"
  by (cases x) auto

(*<*)
end
(*>*)

