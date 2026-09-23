theory Grammar imports "HOL-Library.Mapping" "HOL-Library.Char_ord" begin

datatype TokenType =
  AT | 
  LEFT_PAREN |
  RIGHT_PAREN |
  LEFT_ANGLE | 
  RIGHT_ANGLE |  
  COMMA | 
  STRING string | 
  SEMICOLON

type_synonym tuple = "string list"
type_synonym db = "(string, tuple set) mapping"
type_synonym tdb = "string \<times> db"

inductive isWhiteSpace :: "char \<Rightarrow> bool" where
"isWhiteSpace (CHR '' '')" |
"isWhiteSpace (CHR 0x09)" |
"isWhiteSpace (CHR 0x0a)" |
"isWhiteSpace (CHR 0x0D)"

fun isLineCommentEnd :: "char \<Rightarrow> bool" where
"isLineCommentEnd (CHR 0x0D) = True" |
"isLineCommentEnd (CHR 0x0A) = True" |
"isLineCommentEnd _ = False"

inductive isWhiteString :: "char list \<Rightarrow> bool" where
isWS0: "list_all isWhiteSpace s \<Longrightarrow> isWhiteString s" |
isWS1: "list_all (Not o isLineCommentEnd) s \<Longrightarrow> isLineCommentEnd c \<Longrightarrow> isWhiteString ((CHR ''#'')#s@[c])" |
isWS2:"isWhiteString s1 \<Longrightarrow> isWhiteString s2 \<Longrightarrow> isWhiteString (s1@s2)"

fun isSimpleChar :: "char \<Rightarrow> bool" where
"isSimpleChar c = (
  (((CHR ''0'') \<le> c) \<and> (c \<le> (CHR ''9''))) \<or>
  (((CHR ''A'') \<le> c) \<and> (c \<le> (CHR ''Z''))) \<or>
  (((CHR ''a'') \<le> c) \<and> (c \<le> (CHR ''z''))) \<or>
  ((CHR ''_'') = c) \<or> ((CHR ''['') = c) \<or> ((CHR '']'') = c) \<or> ((CHR ''/'') = c) \<or>
  ((CHR '':'') = c) \<or> ((CHR ''-'') = c) \<or> ((CHR ''.'') = c) \<or> ((CHR ''!'') = c)
  )"

abbreviation isSimpleString :: "char list \<Rightarrow> bool" where
"isSimpleString s \<equiv> list_all isSimpleChar s \<and> s \<noteq> []"

inductive GToken :: "char list \<Rightarrow> TokenType \<Rightarrow> bool" where
AT: "GToken ''@'' AT" |
LEFT_PAREN: "GToken ''('' LEFT_PAREN" |
RIGHT_PAREN: "GToken '')'' RIGHT_PAREN" |
LEFT_ANGLE: "GToken ''<'' LEFT_ANGLE" |
RIGHT_ANGLE: "GToken ''>'' RIGHT_ANGLE" |
COMMA: "GToken '','' COMMA" |
SEMICOLON: "GToken '';'' SEMICOLON" |
GTokenSt: "isSimpleString s \<Longrightarrow> GToken s (STRING s)" |
GTokenQSt: "list_all (\<lambda>x. x \<noteq> CHR ''\"'') s \<Longrightarrow> GToken ((CHR ''\"'')#s@''\"'') (STRING s)"


inductive Glex :: "char list \<Rightarrow> TokenType list \<Rightarrow> bool" where
GlexWS : "isWhiteString xs \<Longrightarrow> Glex xs []" |
GlexTK : "GToken s1 t \<Longrightarrow> Glex s2 ts \<Longrightarrow> isWhiteString w \<Longrightarrow> (isSimpleString s1 \<Longrightarrow> s2 = [] \<or> \<not>isSimpleChar (hd s2)) \<Longrightarrow> Glex (w@s1@s2) (t#ts)"

fun UpdateWith :: "'k \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) mapping \<Rightarrow> ('k, 'v) mapping" where
"UpdateWith key dv f m = Mapping.update key (f (Mapping.lookup_default dv m key)) m"

inductive G_command_args :: "TokenType list \<Rightarrow> bool" where
G_command_args_cmd: "G_command_args [STRING arg]" |
G_command_args_cmds: "G_command_args args \<Longrightarrow> G_command_args (STRING arg#args)"

inductive G_command :: "TokenType list \<Rightarrow> bool" where
"G_command_args args \<Longrightarrow> G_command (RIGHT_ANGLE#args@[LEFT_ANGLE])"

inductive G_fields_n :: "TokenType list \<Rightarrow> tuple \<Rightarrow> bool" where
G_fields_n_f: "G_fields_n [STRING f] [f]"|
G_fields_n_fs: "G_fields_n fs fs' \<Longrightarrow> G_fields_n (STRING f#COMMA#fs) (f#fs')"

inductive G_fields :: "TokenType list \<Rightarrow> tuple \<Rightarrow> bool" where
G_fields_empty: "G_fields [] []" |
G_fields_n: "G_fields_n fs fs' \<Longrightarrow> G_fields fs fs'"

inductive G_tuple :: "TokenType list \<Rightarrow> tuple \<Rightarrow> bool" where
"G_fields fs fs' \<Longrightarrow> G_tuple (LEFT_PAREN#fs@[RIGHT_PAREN]) fs'"

inductive G_relation :: "TokenType list \<Rightarrow> tuple set \<Rightarrow> bool" where
G_relation_empty: "G_relation [] {}" |
G_relation_n: "G_tuple tu tu' \<Longrightarrow> G_relation re re' \<Longrightarrow> G_relation (tu@re) ({tu'}\<union>re')"

inductive G_table :: "TokenType list \<Rightarrow> (string \<times> tuple set) \<Rightarrow> bool" where
"G_relation re re' \<Longrightarrow> G_table (STRING s#re) (s, re')"

inductive G_db :: "TokenType list \<Rightarrow> db \<Rightarrow> bool" where
G_db_empty: "G_db [] Mapping.empty" |
G_db_no_up: "G_table tb (s, ts) \<Longrightarrow> ts = {} \<Longrightarrow> G_db db db'\<Longrightarrow> G_db (tb@db) db'" |
G_db_up: "G_table tb (s, ts) \<Longrightarrow> ts \<noteq> {} \<Longrightarrow> G_db db db'\<Longrightarrow> G_db (tb@db) (UpdateWith s {} (\<lambda>x. x \<union> ts) db')"

inductive G_logentry :: "TokenType list \<Rightarrow> tdb \<Rightarrow> bool" where
G_logentry_sc: "G_db db db' \<Longrightarrow> G_logentry (AT#(STRING s)#db@[SEMICOLON]) (s, db')" |
G_logentry_no_sc: "G_db db db' \<Longrightarrow> G_logentry (AT#(STRING s)#db) (s, db')"

inductive G_parser :: "TokenType list \<Rightarrow> tdb list \<Rightarrow> bool" where
G_parser_empty: "G_parser [] []" |
G_parser_log: "G_logentry le le' \<Longrightarrow> G_parser ls ls' \<Longrightarrow>  G_parser (le@ls) (le'#ls')" |
G_parser_cmd: "G_command cmd \<Longrightarrow> G_parser ls ls' \<Longrightarrow> G_parser (cmd@ls) ls'"



end