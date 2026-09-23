(*<*)
theory Log_Exec
  imports Log_Stream
begin
(*>*)

section \<open>An efficient executable parser\<close>

text \<open>
  This theory refines the streaming parser into code that runs on byte strings, which the code
  generator maps to OCaml's strings. The input arrives in chunks (whatever a read from a channel
  returns), and a token may straddle chunks. Instead of the text of the incomplete lexeme, the
  lexer's state records where in the current chunk it began, together with the text from the
  preceding chunks, if any: a simple string is thus extracted by one @{text String.sub} when it
  ends. Errors do not stop the parser: they are reported in the output, with the offset of the
  offending token in the input, and the parser resumes at the next @{text "@"}, @{text ";"} or
  @{text ">"}. The main theorem, @{text eparse_correct}, states that for every division of an
  input into chunks, the output is error-free exactly if the input is a log, and it then lists
  the log's entries; @{text efeed_chunks_online} states the same for the output so far of an
  input that is still being read.
\<close>

subsection \<open>Byte strings\<close>

typedef bytes = "UNIV :: char list set" ..

text \<open>Indices into byte strings and offsets in the input are of type @{typ integer}, which the code
  generator maps to Zarith's integers; indices within a chunk are therefore unboxed machine
  integers at run time.\<close>

definition bytes_length :: "bytes \<Rightarrow> integer" where
  "bytes_length s = integer_of_nat (length (Rep_bytes s))"

definition bytes_at :: "bytes \<Rightarrow> integer \<Rightarrow> char" where
  "bytes_at s i = Rep_bytes s ! nat_of_integer i"

definition bytes_sub :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> bytes" where
  "bytes_sub s i j = Abs_bytes (take (nat_of_integer (j - i)) (drop (nat_of_integer i) (Rep_bytes s)))"

definition bytes_null :: "bytes \<Rightarrow> bool" where
  "bytes_null s \<longleftrightarrow> Rep_bytes s = []"

definition bytes_append :: "bytes \<Rightarrow> bytes \<Rightarrow> bytes" where
  "bytes_append s t = Abs_bytes (Rep_bytes s @ Rep_bytes t)"

definition bytes_empty :: bytes where
  "bytes_empty = Abs_bytes []"

lemma Rep_bytes_sub[simp]:
  "Rep_bytes (bytes_sub s i j) = take (nat_of_integer (j - i)) (drop (nat_of_integer i) (Rep_bytes s))"
  by (simp add: bytes_sub_def Abs_bytes_inverse)

lemma Rep_bytes_append[simp]: "Rep_bytes (bytes_append s t) = Rep_bytes s @ Rep_bytes t"
  by (simp add: bytes_append_def Abs_bytes_inverse)

lemma Rep_bytes_empty[simp]: "Rep_bytes bytes_empty = []"
  by (simp add: bytes_empty_def Abs_bytes_inverse)

lemmas integer_simps = nat_of_integer.rep_eq less_eq_integer.rep_eq less_integer.rep_eq integer_eq_iff

lemma nat_of_integer_add1: "0 \<le> i \<Longrightarrow> nat_of_integer (i + 1) = Suc (nat_of_integer i)"
  by (simp add: integer_simps)

lemma nat_of_integer_diff: "0 \<le> st \<Longrightarrow> st \<le> i \<Longrightarrow> nat_of_integer (i - st) = nat_of_integer i - nat_of_integer st"
  by (simp add: integer_simps nat_diff_distrib)

lemma bytes_length_nonneg[simp]: "0 \<le> bytes_length s"
  by (simp add: bytes_length_def integer_simps)

lemma nat_of_integer_less_length:
  "0 \<le> i \<Longrightarrow> i < bytes_length s \<Longrightarrow> nat_of_integer i < length (Rep_bytes s)"
  by (auto simp: bytes_length_def integer_simps)

lemma nat_of_integer_le_length:
  "0 \<le> i \<Longrightarrow> i \<le> bytes_length s \<Longrightarrow> nat_of_integer i \<le> length (Rep_bytes s)"
  by (auto simp: bytes_length_def integer_simps)

subsection \<open>The lexer\<close>

text \<open>The states of the lexer. A pending lexeme records the text of the preceding chunks, the
  index at which its part in the current chunk begins, and the offset of its first character in
  the input.\<close>

datatype elstate = E_INIT | E_SIMPLE bytes integer integer | E_QUOTED bytes integer integer
  | E_ESCAPE bytes integer integer
  | E_COMMENT

definition pend_text :: "bytes \<Rightarrow> bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> string" where
  "pend_text pre s st i = Rep_bytes pre @ take (nat_of_integer (i - st)) (drop (nat_of_integer st) (Rep_bytes s))"

fun abs_l :: "bytes \<Rightarrow> integer \<Rightarrow> elstate \<Rightarrow> lstate" where
  "abs_l s i E_INIT = L_INIT"
| "abs_l s i (E_SIMPLE pre st tp) = L_SIMPLE (pend_text pre s st i)"
| "abs_l s i (E_QUOTED pre st tp) = L_QUOTED (pend_text pre s st i)"
| "abs_l s i (E_ESCAPE pre st tp) = L_ESCAPE (pend_text pre s st i)"
| "abs_l s i E_COMMENT = L_COMMENT"

fun wf_l :: "integer \<Rightarrow> elstate \<Rightarrow> bool" where
  "wf_l i (E_SIMPLE pre st tp) \<longleftrightarrow> 0 \<le> st \<and> st \<le> i"
| "wf_l i (E_QUOTED pre st tp) \<longleftrightarrow> 0 \<le> st \<and> st \<le> i"
| "wf_l i (E_ESCAPE pre st tp) \<longleftrightarrow> 0 \<le> st \<and> st \<le> i"
| "wf_l i _ \<longleftrightarrow> True"

text \<open>The result of a step of the lexer: the state is unchanged, or there is a new state,
  possibly with one or two tokens (with their offsets) emitted, or the character cannot be
  lexed, possibly after the end of a simple string.\<close>

datatype eres = R_SAME | R_NEXT elstate | R_TOK "bytes token" integer elstate
  | R_TOK2 "bytes token" integer "bytes token" integer elstate | R_TOK_ERR "bytes token" integer | R_ERR

definition mk_str :: "bytes \<Rightarrow> bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> bytes" where
  "mk_str pre s st i = (if bytes_null pre then bytes_sub s st i else bytes_append pre (bytes_sub s st i))"

definition is_r :: "bytes \<Rightarrow> bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> bool" where
  "is_r pre s st i = (if bytes_null pre then i = st + 1 \<and> bytes_at s st = CHR ''r''
     else bytes_length pre = 1 \<and> i = st \<and> bytes_at pre 0 = CHR ''r'')"

definition elex_init :: "integer \<Rightarrow> integer \<Rightarrow> char \<Rightarrow> eres" where
  "elex_init pos i c =
    (if isWhiteSpace c then R_NEXT E_INIT
     else if c = CHR ''@'' then R_TOK T_AT pos E_INIT
     else if c = CHR ''('' then R_TOK T_LPAREN pos E_INIT
     else if c = CHR '')'' then R_TOK T_RPAREN pos E_INIT
     else if c = CHR ''<'' then R_TOK T_LANGLE pos E_INIT
     else if c = CHR ''>'' then R_TOK T_RANGLE pos E_INIT
     else if c = CHR ''{'' then R_TOK T_LBRACE pos E_INIT
     else if c = CHR ''}'' then R_TOK T_RBRACE pos E_INIT
     else if c = CHR '','' then R_TOK T_COMMA pos E_INIT
     else if c = CHR '';'' then R_TOK T_SEMICOLON pos E_INIT
     else if c = CHR ''#'' then R_NEXT E_COMMENT
     else if c = CHR 0x22 then R_NEXT (E_QUOTED bytes_empty (i + 1) pos)
     else if isSimpleChar c then R_NEXT (E_SIMPLE bytes_empty i pos)
     else R_ERR)"

definition close_tok :: "bytes token \<Rightarrow> integer \<Rightarrow> eres \<Rightarrow> eres" where
  "close_tok t tp r = (case r of
     R_NEXT l \<Rightarrow> R_TOK t tp l
   | R_TOK t' tp' l \<Rightarrow> R_TOK2 t tp t' tp' l
   | _ \<Rightarrow> R_TOK_ERR t tp)"

definition elex_step :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> char \<Rightarrow> elstate \<Rightarrow> eres" where
  "elex_step s b i c l = (case l of
     E_INIT \<Rightarrow> (if isWhiteSpace c then R_SAME else elex_init (b + i) i c)
   | E_SIMPLE pre st tp \<Rightarrow>
       (if isSimpleChar c then R_SAME
        else if c = CHR 0x22 \<and> is_r pre s st i then R_NEXT (E_QUOTED bytes_empty (i + 1) tp)
        else close_tok (T_STR (mk_str pre s st i)) tp (elex_init (b + i) i c))
   | E_QUOTED pre st tp \<Rightarrow>
       (if c = CHR 0x22 then R_TOK (T_STR (mk_str pre s st i)) tp E_INIT
        else if c = CHR 0x5C then R_NEXT (E_ESCAPE pre st tp)
        else R_SAME)
   | E_ESCAPE pre st tp \<Rightarrow> R_NEXT (E_QUOTED pre st tp)
   | E_COMMENT \<Rightarrow> (if isLineCommentEnd c then R_NEXT E_INIT else R_SAME))"

text \<open>The tokens emitted by a result and its new state.\<close>

fun eres_toks :: "eres \<Rightarrow> bytes token list" where
  "eres_toks (R_TOK t tp l) = [t]"
| "eres_toks (R_TOK2 t tp t' tp' l) = [t, t']"
| "eres_toks _ = []"

fun eres_state :: "elstate \<Rightarrow> eres \<Rightarrow> elstate option" where
  "eres_state l R_SAME = Some l"
| "eres_state l (R_NEXT l') = Some l'"
| "eres_state l (R_TOK t tp l') = Some l'"
| "eres_state l (R_TOK2 t tp t' tp' l') = Some l'"
| "eres_state l _ = None"

text \<open>A step of the lexer on the byte at index @{text i} of the chunk @{text s} refines the step
  of the specification on the abstraction of the state.\<close>

definition eres_ok :: "bytes \<Rightarrow> integer \<Rightarrow> elstate \<Rightarrow> eres \<Rightarrow> (string token list \<times> lstate) option \<Rightarrow> bool" where
  "eres_ok s i l r res = (case res of
     None \<Rightarrow> eres_state l r = None
   | Some (ts, l') \<Rightarrow> (\<exists>el. eres_state l r = Some el \<and> map (map_token Rep_bytes) (eres_toks r) = ts \<and>
       abs_l s (i + 1) el = l' \<and> wf_l (i + 1) el))"

lemma pend_text_Suc:
  assumes "0 \<le> st" "st \<le> i" "i < bytes_length s"
  shows "pend_text pre s st (i + 1) = pend_text pre s st i @ [bytes_at s i]"
proof -
  have "nat_of_integer (i + 1 - st) = Suc (nat_of_integer (i - st))"
    using assms by (simp add: integer_simps)
  moreover have "nat_of_integer st + nat_of_integer (i - st) = nat_of_integer i"
    using assms by (simp add: integer_simps)
  moreover have "nat_of_integer i < length (Rep_bytes s)"
    using assms by (auto intro: nat_of_integer_less_length)
  ultimately show ?thesis
    by (simp add: pend_text_def bytes_at_def take_Suc_conv_app_nth)
qed

lemma pend_text_start:
  "0 \<le> i \<Longrightarrow> i < bytes_length s \<Longrightarrow> pend_text bytes_empty s i (i + 1) = [bytes_at s i]"
  using pend_text_Suc[of i i s bytes_empty] by (simp add: pend_text_def)

lemma pend_text_empty: "pend_text bytes_empty s i i = []"
  by (simp add: pend_text_def)

lemma Rep_mk_str: "Rep_bytes (mk_str pre s st i) = pend_text pre s st i"
  by (simp add: mk_str_def pend_text_def bytes_null_def)

lemma is_r_iff:
  assumes "0 \<le> st" "st \<le> i" "i \<le> bytes_length s"
  shows "is_r pre s st i \<longleftrightarrow> pend_text pre s st i = ''r''"
proof -
  let ?k = "nat_of_integer (i - st)" and ?a = "nat_of_integer st"
  let ?t = "take ?k (drop ?a (Rep_bytes s))"
  have ak: "?a + ?k = nat_of_integer i" and il: "nat_of_integer i \<le> length (Rep_bytes s)"
    using assms by (auto simp: integer_simps bytes_length_def)
  then have len: "length ?t = ?k"
    by simp
  have k1: "?k = 1 \<longleftrightarrow> i = st + 1" and k0: "?k = 0 \<longleftrightarrow> i = st"
    using assms by (auto simp: integer_simps)
  show ?thesis
  proof (cases "Rep_bytes pre")
    case Nil
    have "?t = ''r'' \<longleftrightarrow> i = st + 1 \<and> bytes_at s st = CHR ''r''"
    proof
      assume t: "?t = ''r''"
      with len have "?k = 1"
        by simp
      moreover from t have "?t ! 0 = CHR ''r''"
        by simp
      ultimately show "i = st + 1 \<and> bytes_at s st = CHR ''r''"
        using k1 ak il by (simp add: bytes_at_def)
    next
      assume "i = st + 1 \<and> bytes_at s st = CHR ''r''"
      with k1 ak il show "?t = ''r''"
        by (simp add: bytes_at_def take_Suc_conv_app_nth)
    qed
    with Nil show ?thesis
      by (simp add: is_r_def pend_text_def bytes_null_def)
  next
    case (Cons a as)
    have "Rep_bytes pre @ ?t = ''r'' \<longleftrightarrow> Rep_bytes pre = ''r'' \<and> ?k = 0"
      using Cons len by (cases as) auto
    with Cons k0 show ?thesis
      by (auto simp: is_r_def pend_text_def bytes_length_def bytes_at_def bytes_null_def integer_simps)
  qed
qed

lemma elex_init_cases: "elex_init pos i c = R_ERR \<or> (\<exists>l. elex_init pos i c = R_NEXT l) \<or>
  (\<exists>t tp l. elex_init pos i c = R_TOK t tp l)"
  by (simp add: elex_init_def)

lemma elex_init_ok:
  assumes "0 \<le> i" "i < bytes_length s" "c = bytes_at s i"
  shows "eres_ok s i l (elex_init pos i c) (lex_init c)"
  using assms unfolding elex_init_def lex_init_def eres_ok_def
  by (simp add: pend_text_empty pend_text_start)

lemma eres_ok_close_tok:
  assumes "eres_ok s i l r res" "r = R_ERR \<or> (\<exists>l. r = R_NEXT l) \<or> (\<exists>t tp l. r = R_TOK t tp l)"
  shows "eres_ok s i l' (close_tok (T_STR x) tp r) (map_option (apfst (Cons (T_STR (Rep_bytes x)))) res)"
  using assms by (auto simp: eres_ok_def close_tok_def split: option.splits)

lemma elex_step_ok:
  assumes i0: "0 \<le> i" and i: "i < bytes_length s" and c: "c = bytes_at s i" and wf: "wf_l i l"
  shows "eres_ok s i l (elex_step s b i c l) (lex_step c (abs_l s i l))"
proof (cases l)
  case E_INIT
  show ?thesis
  proof (cases "isWhiteSpace c")
    case True
    then have "lex_init c = Some ([], L_INIT)"
      by (simp add: lex_init_def)
    with True E_INIT show ?thesis
      by (simp add: elex_step_def eres_ok_def)
  next
    case False
    with E_INIT elex_init_ok[OF i0 i c, of l "b + i"] show ?thesis
      by (simp add: elex_step_def)
  qed
next
  case (E_SIMPLE pre st tp)
  with wf have st0: "0 \<le> st" and st: "st \<le> i"
    by simp_all
  let ?x = "pend_text pre s st i"
  consider (more) "isSimpleChar c" | (rquote) "\<not> isSimpleChar c" "c = CHR 0x22" "is_r pre s st i"
    | (close) "\<not> isSimpleChar c" "\<not> (c = CHR 0x22 \<and> is_r pre s st i)"
    by blast
  then show ?thesis
  proof cases
    case more
    with E_SIMPLE st0 st i c show ?thesis
      by (auto simp: elex_step_def eres_ok_def pend_text_Suc)
  next
    case rquote
    with st0 st i have "?x = ''r''"
      by (simp add: is_r_iff)
    with E_SIMPLE rquote i0 show ?thesis
      by (auto simp: elex_step_def eres_ok_def pend_text_empty)
  next
    case close
    with st0 st i have "\<not> (c = CHR 0x22 \<and> ?x = ''r'')"
      by (simp add: is_r_iff)
    with close E_SIMPLE show ?thesis
      using eres_ok_close_tok[OF elex_init_ok[OF i0 i c, of l "b + i"] elex_init_cases, of l "mk_str pre s st i" tp]
      by (auto simp: elex_step_def Rep_mk_str)
  qed
next
  case (E_QUOTED pre st tp)
  with wf have st0: "0 \<le> st" and st: "st \<le> i"
    by simp_all
  with E_QUOTED i c show ?thesis
    by (auto simp: elex_step_def eres_ok_def pend_text_Suc Rep_mk_str)
next
  case (E_ESCAPE pre st tp)
  with wf have st0: "0 \<le> st" and st: "st \<le> i"
    by simp_all
  with E_ESCAPE i c show ?thesis
    by (auto simp: elex_step_def eres_ok_def pend_text_Suc)
next
  case E_COMMENT
  then show ?thesis
    by (auto simp: elex_step_def eres_ok_def)
qed

subsection \<open>Errors and the output\<close>

text \<open>What was expected where an error occurred, derived from the state of the parser. The
  messages of MonPoly's parser correspond to these.\<close>

datatype expect = X_ENTRY | X_TIMESTAMP | X_PREDICATE | X_FIELD_OR_RPAREN | X_COMMA_OR_RPAREN | X_FIELD
  | X_CMD_NAME | X_CMD_ARG

text \<open>An unexpected token (or the end of the input), a character that begins no token, or a
  quoted string that the input ends in.\<close>

datatype perror = E_TOKEN expect "bytes token option" | E_CHAR expect char | E_UNTERMINATED

text \<open>The output: an item, with the offset of its first token (the @{text "@"} of an entry or the
  @{text ">"} of a command), which locates the errors that the consumer finds in the item; or an
  error, with its offset.\<close>

datatype out = O_ITEM integer "bytes item" | O_ERROR integer perror

fun expect_of :: "'s pstate \<Rightarrow> expect" where
  "expect_of P_INIT = X_ENTRY"
| "expect_of P_TS = X_TIMESTAMP"
| "expect_of (P_DB _ _) = X_PREDICATE"
| "expect_of (P_NAME _ _ _) = X_PREDICATE"
| "expect_of (P_TUPLES _ _ _) = X_PREDICATE"
| "expect_of (P_FIELD1 _ _ _) = X_FIELD_OR_RPAREN"
| "expect_of (P_AFTER _ _ _ _) = X_COMMA_OR_RPAREN"
| "expect_of (P_FIELDN _ _ _ _) = X_FIELD"
| "expect_of P_CMD = X_CMD_NAME"
| "expect_of (P_ARGS _ _) = X_CMD_ARG"

text \<open>After an error, the parser skips tokens (state @{const None}) until a token that begins an
  entry or ends one.\<close>

definition resync :: "'s token \<Rightarrow> 's pstate option" where
  "resync t = (case t of T_AT \<Rightarrow> Some P_TS | T_SEMICOLON \<Rightarrow> Some P_INIT | T_RANGLE \<Rightarrow> Some P_CMD | _ \<Rightarrow> None)"

text \<open>The offset of the first token of the item being read, after a token at offset @{text pos}
  has led to the state @{text p}: the tokens that begin an item lead to @{const P_TS} and
  @{const P_CMD}.\<close>

definition start :: "integer \<Rightarrow> 's pstate option \<Rightarrow> integer \<Rightarrow> integer" where
  "start pos p sp = (case p of Some P_TS \<Rightarrow> pos | Some P_CMD \<Rightarrow> pos | _ \<Rightarrow> sp)"

text \<open>Feeding a token, with its offset, to the parser, where @{text sp} is the offset of the first
  token of the item being read. Outputs are accumulated in reverse.\<close>

definition efeed :: "bytes token \<Rightarrow> integer \<Rightarrow> bytes pstate option \<Rightarrow> integer \<Rightarrow> out list \<Rightarrow> out list \<times> bytes pstate option" where
  "efeed t pos p sp acc = (case p of
     None \<Rightarrow> (acc, resync t)
   | Some ps \<Rightarrow> (case pstep t ps of
       None \<Rightarrow> (O_ERROR pos (E_TOKEN (expect_of ps) (Some t)) # acc, resync t)
     | Some (es, ps') \<Rightarrow> (rev (map (O_ITEM sp) es) @ acc, Some ps')))"

definition echar_err :: "integer \<Rightarrow> char \<Rightarrow> bytes pstate option \<Rightarrow> out list \<Rightarrow> out list" where
  "echar_err pos c p acc = (case p of None \<Rightarrow> acc | Some ps \<Rightarrow> O_ERROR pos (E_CHAR (expect_of ps) c) # acc)"

subsection \<open>Chunks\<close>

text \<open>The loop over the bytes of a chunk @{text s} of length @{text n}, which begins at offset
  @{text b} of the input.\<close>

function eloop :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> elstate \<Rightarrow> bytes pstate option \<Rightarrow> integer \<Rightarrow>
  out list \<Rightarrow> out list \<times> elstate \<times> bytes pstate option \<times> integer" where
  "eloop s n b i l p sp acc = (if i < n then (case elex_step s b i (bytes_at s i) l of
       R_SAME \<Rightarrow> eloop s n b (i + 1) l p sp acc
     | R_NEXT l' \<Rightarrow> eloop s n b (i + 1) l' p sp acc
     | R_TOK t tp l' \<Rightarrow> (case efeed t tp p sp acc of (acc', p') \<Rightarrow> eloop s n b (i + 1) l' p' (start tp p' sp) acc')
     | R_TOK2 t tp t' tp' l' \<Rightarrow> (case efeed t tp p sp acc of (acc', p') \<Rightarrow>
         case efeed t' tp' p' (start tp p' sp) acc' of (acc'', p'') \<Rightarrow>
           eloop s n b (i + 1) l' p'' (start tp' p'' (start tp p' sp)) acc'')
     | R_TOK_ERR t tp \<Rightarrow> (case efeed t tp p sp acc of (acc', p') \<Rightarrow>
         eloop s n b (i + 1) E_INIT None sp (echar_err (b + i) (bytes_at s i) p' acc'))
     | R_ERR \<Rightarrow> eloop s n b (i + 1) E_INIT None sp (echar_err (b + i) (bytes_at s i) p acc))
   else (acc, l, p, sp))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, b, i, l, p, sp, acc). nat_of_integer (n - i))") (auto simp: integer_simps)

declare eloop.simps[simp del]

text \<open>At the end of a chunk, the part of a pending lexeme in it is moved into the text of the
  preceding chunks.\<close>

definition close_chunk :: "bytes \<Rightarrow> integer \<Rightarrow> elstate \<Rightarrow> elstate" where
  "close_chunk s n l = (case l of
     E_SIMPLE pre st tp \<Rightarrow> E_SIMPLE (mk_str pre s st n) 0 tp
   | E_QUOTED pre st tp \<Rightarrow> E_QUOTED (mk_str pre s st n) 0 tp
   | E_ESCAPE pre st tp \<Rightarrow> E_ESCAPE (mk_str pre s st n) 0 tp
   | _ \<Rightarrow> l)"

text \<open>The state between chunks: the offset of the next chunk, the states of the lexer and the
  parser, and the offset of the first token of the item being read.\<close>

type_synonym estate = "integer \<times> elstate \<times> bytes pstate option \<times> integer"

definition einit :: estate where
  "einit = (0, E_INIT, Some P_INIT, 0)"

definition efeed_chunk :: "bytes \<Rightarrow> estate \<Rightarrow> out list \<times> estate" where
  "efeed_chunk s st = (case st of (b, l, p, sp) \<Rightarrow> (let n = bytes_length s in
     case eloop s n b 0 l p sp [] of (acc, l', p', sp') \<Rightarrow> (rev acc, (b + n, close_chunk s n l', p', sp'))))"

definition efinish_p :: "integer \<Rightarrow> bytes pstate option \<Rightarrow> integer \<Rightarrow> out list \<Rightarrow> out list" where
  "efinish_p b p sp acc = (case p of
     None \<Rightarrow> acc
   | Some ps \<Rightarrow> (case parse_finish ps of
       None \<Rightarrow> O_ERROR b (E_TOKEN (expect_of ps) None) # acc
     | Some es \<Rightarrow> rev (map (O_ITEM sp) es) @ acc))"

text \<open>The end of the input.\<close>

definition efinish :: "estate \<Rightarrow> out list" where
  "efinish st = (case st of (b, l, p, sp) \<Rightarrow> (case l of
     E_SIMPLE pre _ tp \<Rightarrow> (case efeed (T_STR pre) tp p sp [] of (acc, p') \<Rightarrow> rev (efinish_p b p' (start tp p' sp) acc))
   | E_QUOTED pre _ tp \<Rightarrow> (case p of None \<Rightarrow> [] | Some _ \<Rightarrow> [O_ERROR tp E_UNTERMINATED])
   | E_ESCAPE pre _ tp \<Rightarrow> (case p of None \<Rightarrow> [] | Some _ \<Rightarrow> [O_ERROR tp E_UNTERMINATED])
   | _ \<Rightarrow> rev (efinish_p b p sp [])))"

fun efeed_chunks :: "bytes list \<Rightarrow> estate \<Rightarrow> out list \<times> estate" where
  "efeed_chunks [] st = ([], st)"
| "efeed_chunks (s # ss) st = (case efeed_chunk s st of (o1, st1) \<Rightarrow>
     (case efeed_chunks ss st1 of (o2, st2) \<Rightarrow> (o1 @ o2, st2)))"

definition eparse :: "bytes list \<Rightarrow> out list" where
  "eparse ss = (case efeed_chunks ss einit of (outs, st) \<Rightarrow> outs @ efinish st)"

subsection \<open>Correctness\<close>

text \<open>The entries of an output without errors.\<close>

fun oks :: "out list \<Rightarrow> bytes item list option" where
  "oks [] = Some []"
| "oks (O_ITEM _ e # xs) = map_option (Cons e) (oks xs)"
| "oks (O_ERROR _ _ # xs) = None"

abbreviation abs_items :: "bytes item list \<Rightarrow> string item list" where
  "abs_items \<equiv> map (map_item Rep_bytes)"

definition has_err :: "out list \<Rightarrow> bool" where
  "has_err xs \<longleftrightarrow> (\<exists>pos e. O_ERROR pos e \<in> set xs)"

lemma oks_None_iff: "oks xs = None \<longleftrightarrow> has_err xs"
  by (induction xs rule: oks.induct) (auto simp: has_err_def)

lemma has_err_simps[simp]:
  "has_err [] \<longleftrightarrow> False"
  "has_err (O_ERROR pos e # xs) \<longleftrightarrow> True"
  "has_err (O_ITEM sp x # xs) \<longleftrightarrow> has_err xs"
  "has_err (xs @ ys) \<longleftrightarrow> has_err xs \<or> has_err ys"
  "has_err (rev xs) \<longleftrightarrow> has_err xs"
  "has_err (map (O_ITEM sp) es) \<longleftrightarrow> False"
  by (auto simp: has_err_def)

lemma map_option_Cons_append: "map_option (Cons e) (map_option ((@) xs) X) = map_option ((@) (e # xs)) X"
  by (cases X) auto

lemma oks_append: "oks (xs @ ys) = (case oks xs of None \<Rightarrow> None | Some es \<Rightarrow> map_option ((@) es) (oks ys))"
  by (induction xs rule: oks.induct) (auto split: option.splits simp: map_option_Cons_append)

lemma oks_rev: "oks (rev xs) = map_option rev (oks xs)"
  by (induction xs rule: oks.induct) (auto simp: oks_append split: option.splits)

lemma oks_map[simp]: "oks (map (O_ITEM sp) es) = Some es"
  by (induction es) auto

lemma oks_rev_map[simp]: "oks (rev (map (O_ITEM sp) es)) = Some (rev es)"
  by (simp add: oks_rev)

lemma oks_append_Some:
  "oks xs = Some es \<Longrightarrow> oks ys = Some es' \<Longrightarrow> oks (xs @ ys) = Some (es @ es')"
  by (simp add: oks_append)

subsubsection \<open>The accumulator\<close>

lemma efeed_acc: "efeed t pos p sp acc = (case efeed t pos p sp [] of (new, p') \<Rightarrow> (new @ acc, p'))"
  by (auto simp: efeed_def split: option.splits)

lemma echar_err_acc: "echar_err pos c p acc = echar_err pos c p [] @ acc"
  by (auto simp: echar_err_def split: option.splits)

lemma eloop_acc: "eloop s n b i l p sp acc =
  (case eloop s n b i l p sp [] of (new, l', p', sp') \<Rightarrow> (new @ acc, l', p', sp'))"
proof (induction "nat_of_integer (n - i)" arbitrary: i l p sp acc)
  case 0
  then have "\<not> i < n"
    by (auto simp: integer_simps)
  then show ?case
    by (simp add: eloop.simps)
next
  case (Suc k)
  then have i: "i < n" and k: "k = nat_of_integer (n - (i + 1))"
    by (auto simp: integer_simps)
  note IH = Suc(1)[OF k]
  show ?case
  proof (cases "elex_step s b i (bytes_at s i) l")
    case R_SAME
    with i IH[of l p sp acc] IH[of l p sp "[]"] show ?thesis
      by (subst (1 2) eloop.simps) (simp split: prod.splits)
  next
    case (R_NEXT l')
    with i IH[of l' p sp acc] IH[of l' p sp "[]"] show ?thesis
      by (subst (1 2) eloop.simps) (simp split: prod.splits)
  next
    case (R_TOK t tp l')
    obtain new1 p1 where e1: "efeed t tp p sp [] = (new1, p1)"
      by fastforce
    with R_TOK i IH[of l' p1 "start tp p1 sp" "new1 @ acc"] IH[of l' p1 "start tp p1 sp" new1] show ?thesis
      by (subst (1 2) eloop.simps) (simp add: efeed_acc[of t tp p sp acc] split: prod.splits)
  next
    case (R_TOK2 t tp t' tp' l')
    obtain new1 p1 where e1: "efeed t tp p sp [] = (new1, p1)"
      by fastforce
    let ?sp1 = "start tp p1 sp"
    obtain new2 p2 where e2: "efeed t' tp' p1 ?sp1 [] = (new2, p2)"
      by fastforce
    let ?sp2 = "start tp' p2 ?sp1"
    from R_TOK2 i e1 e2 IH[of l' p2 ?sp2 "new2 @ new1 @ acc"] IH[of l' p2 ?sp2 "new2 @ new1"] show ?thesis
      by (subst (1 2) eloop.simps)
        (simp add: efeed_acc[of t tp p sp acc] efeed_acc[of t' tp' p1 ?sp1 "new1 @ acc"]
          efeed_acc[of t' tp' p1 ?sp1 new1] split: prod.splits)
  next
    case (R_TOK_ERR t tp)
    obtain new1 p1 where e1: "efeed t tp p sp [] = (new1, p1)"
      by fastforce
    let ?e = "echar_err (b + i) (bytes_at s i) p1 []"
    from R_TOK_ERR i e1 IH[of E_INIT None sp "?e @ new1 @ acc"] IH[of E_INIT None sp "?e @ new1"] show ?thesis
      by (subst (1 2) eloop.simps)
        (simp add: efeed_acc[of t tp p sp acc] echar_err_acc[of _ _ p1 "new1 @ acc"] echar_err_acc[of _ _ p1 new1]
          split: prod.splits)
  next
    case R_ERR
    let ?e = "echar_err (b + i) (bytes_at s i) p []"
    from R_ERR i IH[of E_INIT None sp "?e @ acc"] IH[of E_INIT None sp ?e] show ?thesis
      by (subst (1 2) eloop.simps) (simp add: echar_err_acc[of _ _ p acc] split: prod.splits)
  qed
qed

fun eres_tks :: "eres \<Rightarrow> (bytes token \<times> integer) list" where
  "eres_tks (R_TOK t tp l) = [(t, tp)]"
| "eres_tks (R_TOK2 t tp t' tp' l) = [(t, tp), (t', tp')]"
| "eres_tks _ = []"

lemma eres_toks_tks: "eres_toks r = map fst (eres_tks r)"
  by (cases r) auto

fun efeeds :: "(bytes token \<times> integer) list \<Rightarrow> bytes pstate option \<Rightarrow> integer \<Rightarrow> out list \<Rightarrow>
  out list \<times> bytes pstate option \<times> integer" where
  "efeeds [] p sp acc = (acc, p, sp)"
| "efeeds ((t, tp) # tks) p sp acc = (case efeed t tp p sp acc of (acc', p') \<Rightarrow> efeeds tks p' (start tp p' sp) acc')"

lemma eloop_step:
  assumes "i < n" "eres_state l (elex_step s b i (bytes_at s i) l) = Some el"
  shows "eloop s n b i l p sp acc = (case efeeds (eres_tks (elex_step s b i (bytes_at s i) l)) p sp acc of
    (acc', p', sp') \<Rightarrow> eloop s n b (i + 1) el p' sp' acc')"
  using assms by (subst eloop.simps) (auto split: eres.splits prod.splits)

lemma eres_state_None: "eres_state l r = None \<longleftrightarrow> (\<exists>t tp. r = R_TOK_ERR t tp) \<or> r = R_ERR"
  by (cases r) auto

subsubsection \<open>The parser\<close>

lemma efeeds_acc: "efeeds tks p sp acc = (case efeeds tks p sp [] of (new, p', sp') \<Rightarrow> (new @ acc, p', sp'))"
proof (induction tks arbitrary: p sp acc)
  case (Cons tk tks)
  obtain t tp where tk: "tk = (t, tp)"
    by fastforce
  obtain new1 p1 where e1: "efeed t tp p sp [] = (new1, p1)"
    by fastforce
  from Cons.IH[of p1 "start tp p1 sp" "new1 @ acc"] Cons.IH[of p1 "start tp p1 sp" new1] e1 tk show ?case
    by (simp add: efeed_acc[of t tp p sp acc] split: prod.splits)
qed simp

lemma efeeds_Some:
  assumes "efeeds tks (Some ps) sp [] = (new, p', sp')"
  shows "case parse_run (map fst tks) ps of
     None \<Rightarrow> has_err new
   | Some (es, ps') \<Rightarrow> oks (rev new) = Some es \<and> p' = Some ps'"
  using assms
proof (induction tks arbitrary: ps sp new p' sp')
  case (Cons tk tks)
  obtain t tp where tk: "tk = (t, tp)"
    by fastforce
  show ?case
  proof (cases "pstep t ps")
    case None
    with Cons.prems tk show ?thesis
      by (auto simp: efeed_def efeeds_acc[of _ _ _ "[_]"] split: prod.splits)
  next
    case (Some r)
    obtain es1 ps1 where r: "r = (es1, ps1)"
      by fastforce
    obtain new2 p2 sp2 where e2: "efeeds tks (Some ps1) (start tp (Some ps1) sp) [] = (new2, p2, sp2)"
      by (cases "efeeds tks (Some ps1) (start tp (Some ps1) sp) []") auto
    with Cons.prems tk Some r have new: "new = new2 @ rev (map (O_ITEM sp) es1)" and p2: "p' = p2"
      by (auto simp: efeed_def efeeds_acc[of _ _ _ "rev (map (O_ITEM sp) es1)"] split: prod.splits)
    from Cons.IH[OF e2] Some r new p2 tk show ?thesis
      by (auto simp: oks_append split: option.splits)
  qed
qed simp

subsubsection \<open>The loop over a chunk\<close>

lemma stream_run_Cons_lex:
  "stream_run (c # s) (L, P) = (case lex_step c L of
     None \<Rightarrow> None
   | Some (ts, L1) \<Rightarrow> (case parse_run ts P of
       None \<Rightarrow> None
     | Some (es1, P1) \<Rightarrow> map_option (apfst ((@) es1)) (stream_run s (L1, P1))))"
  by (auto simp: stream_step_def split: option.splits)

lemma eloop_correct:
  assumes "n = bytes_length s" "0 \<le> i" "i \<le> n" "wf_l i l"
  shows "case stream_run (drop (nat_of_integer i) (Rep_bytes s)) (abs_l s i l, map_pstate Rep_bytes ps) of
     None \<Rightarrow> has_err (fst (eloop s n b i l (Some ps) sp []))
   | Some (es, L', P') \<Rightarrow> (\<exists>new es' l' ps' sp'. eloop s n b i l (Some ps) sp [] = (new, l', Some ps', sp') \<and>
       oks (rev new) = Some es' \<and> abs_items es' = es \<and> abs_l s n l' = L' \<and> wf_l n l' \<and>
       map_pstate Rep_bytes ps' = P')"
  using assms
proof (induction "nat_of_integer (n - i)" arbitrary: i l ps sp)
  case 0
  then have "i = n"
    by (auto simp: integer_simps)
  with 0 show ?case
    by (simp add: eloop.simps bytes_length_def)
next
  case (Suc k)
  then have i0: "0 \<le> i" and i: "i < n" and k: "k = nat_of_integer (n - (i + 1))"
    by (auto simp: integer_simps)
  let ?c = "bytes_at s i"
  let ?r = "elex_step s b i ?c l"
  have drop: "drop (nat_of_integer i) (Rep_bytes s) = ?c # drop (nat_of_integer (i + 1)) (Rep_bytes s)"
    using i i0 Suc.prems(1)
    by (simp add: bytes_at_def nat_of_integer_add1 Cons_nth_drop_Suc nat_of_integer_less_length)
  have ok: "eres_ok s i l ?r (lex_step ?c (abs_l s i l))"
    using i Suc.prems by (intro elex_step_ok) auto
  show ?case
  proof (cases "lex_step ?c (abs_l s i l)")
    case None
    with ok have "eres_state l ?r = None"
      by (simp add: eres_ok_def)
    then consider t tp where "?r = R_TOK_ERR t tp" | "?r = R_ERR"
      by (auto simp: eres_state_None)
    then have "has_err (fst (eloop s n b i l (Some ps) sp []))"
    proof cases
      case (1 t tp)
      obtain new1 p1 where e1: "efeed t tp (Some ps) sp [] = (new1, p1)"
        by fastforce
      have "has_err (echar_err (b + i) ?c p1 new1)"
        using e1 by (auto simp: efeed_def echar_err_def split: option.splits)
      with 1 i e1 show ?thesis
        by (subst eloop.simps) (auto simp: eloop_acc[of _ _ _ _ _ _ _ "echar_err _ _ _ _"] split: prod.splits)
    next
      case 2
      with i show ?thesis
        by (subst eloop.simps) (auto simp: echar_err_def eloop_acc[of _ _ _ _ _ _ _ "[_]"] split: prod.splits)
    qed
    with None drop show ?thesis
      by (simp add: stream_run_Cons_lex del: stream_run.simps)
  next
    case (Some x)
    obtain ts L1 where x: "x = (ts, L1)"
      by fastforce
    with ok Some obtain el where el: "eres_state l ?r = Some el"
      and ts: "map (map_token Rep_bytes) (eres_toks ?r) = ts" and L1: "abs_l s (i + 1) el = L1"
      and wf1: "wf_l (i + 1) el"
      by (auto simp: eres_ok_def)
    have step: "eloop s n b i l (Some ps) sp [] =
      (case efeeds (eres_tks ?r) (Some ps) sp [] of (acc', p', sp') \<Rightarrow> eloop s n b (i + 1) el p' sp' acc')"
      by (rule eloop_step[OF i el])
    obtain new1 p1 sp1 where e1: "efeeds (eres_tks ?r) (Some ps) sp [] = (new1, p1, sp1)"
      by (cases "efeeds (eres_tks ?r) (Some ps) sp []") auto
    have pr: "parse_run ts (map_pstate Rep_bytes ps) =
      map_option (map_prod abs_items (map_pstate Rep_bytes)) (parse_run (map fst (eres_tks ?r)) ps)"
      using parse_run_map[of Rep_bytes "map fst (eres_tks ?r)" ps] ts by (simp add: eres_toks_tks)
    note E1 = efeeds_Some[OF e1]
    show ?thesis
    proof (cases "parse_run (map fst (eres_tks ?r)) ps")
      case None
      with E1 have "has_err new1"
        by simp
      then have "has_err (fst (eloop s n b i l (Some ps) sp []))"
        using step e1 by (auto simp: eloop_acc[of _ _ _ _ _ _ _ new1] split: prod.splits)
      with None drop Some x pr show ?thesis
        by (simp add: stream_run_Cons_lex del: stream_run.simps)
    next
      case (Some y)
      obtain es1 ps1 where y: "y = (es1, ps1)"
        by fastforce
      with E1 Some have new1: "oks (rev new1) = Some es1" and p1: "p1 = Some ps1"
        by auto
      have IH: "case stream_run (drop (nat_of_integer (i + 1)) (Rep_bytes s)) (abs_l s (i + 1) el, map_pstate Rep_bytes ps1) of
        None \<Rightarrow> has_err (fst (eloop s n b (i + 1) el (Some ps1) sp1 []))
      | Some (es, L', P') \<Rightarrow> (\<exists>new es' l' ps' sp'. eloop s n b (i + 1) el (Some ps1) sp1 [] = (new, l', Some ps', sp') \<and>
          oks (rev new) = Some es' \<and> abs_items es' = es \<and> abs_l s n l' = L' \<and> wf_l n l' \<and>
          map_pstate Rep_bytes ps' = P')"
      proof -
        have "0 \<le> i + 1" "i + 1 \<le> n"
          using i i0 by (auto simp: integer_simps)
        then show ?thesis
          using Suc.hyps(1)[of "i + 1" el ps1 sp1] k Suc.prems(1) wf1 by simp
      qed
      have loop: "eloop s n b i l (Some ps) sp [] = (case eloop s n b (i + 1) el (Some ps1) sp1 [] of
        (new, l', p', sp') \<Rightarrow> (new @ new1, l', p', sp'))"
        using step e1 p1 by (simp add: eloop_acc[of _ _ _ _ _ _ _ new1])
      have stream: "stream_run (drop (nat_of_integer i) (Rep_bytes s)) (abs_l s i l, map_pstate Rep_bytes ps) =
        map_option (apfst ((@) (abs_items es1))) (stream_run (drop (nat_of_integer (i + 1)) (Rep_bytes s)) (L1, map_pstate Rep_bytes ps1))"
        using drop \<open>lex_step ?c (abs_l s i l) = Some x\<close> x pr Some y
        by (simp add: stream_run_Cons_lex del: stream_run.simps)
      show ?thesis
      proof (cases "stream_run (drop (nat_of_integer (i + 1)) (Rep_bytes s)) (L1, map_pstate Rep_bytes ps1)")
        case None
        with IH L1 have "has_err (fst (eloop s n b (i + 1) el (Some ps1) sp1 []))"
          by simp
        with None stream loop show ?thesis
          by (auto split: prod.splits)
      next
        case (Some z)
        obtain es2 L2 P2 where z: "z = (es2, L2, P2)"
          by (cases z) auto
        with IH L1 Some obtain new2 es2' l2 ps2 sp2 where
          "eloop s n b (i + 1) el (Some ps1) sp1 [] = (new2, l2, Some ps2, sp2)" "oks (rev new2) = Some es2'"
          "abs_items es2' = es2" "abs_l s n l2 = L2" "wf_l n l2" "map_pstate Rep_bytes ps2 = P2"
          by auto
        with Some z stream loop new1 show ?thesis
          by (auto intro!: exI[of _ "es1 @ es2'"] simp: oks_append_Some)
      qed
    qed
  qed
qed

subsubsection \<open>Chunks and the end of the input\<close>

fun wf0 :: "elstate \<Rightarrow> bool" where
  "wf0 (E_SIMPLE pre st tp) \<longleftrightarrow> st = 0"
| "wf0 (E_QUOTED pre st tp) \<longleftrightarrow> st = 0"
| "wf0 (E_ESCAPE pre st tp) \<longleftrightarrow> st = 0"
| "wf0 _ \<longleftrightarrow> True"

definition abs_l0 :: "elstate \<Rightarrow> lstate" where
  "abs_l0 l = abs_l bytes_empty 0 l"

lemma abs_l_0: "wf0 l \<Longrightarrow> abs_l s 0 l = abs_l0 l"
  by (cases l) (auto simp: abs_l0_def pend_text_def)

lemma wf0_wf_l: "wf0 l \<Longrightarrow> wf_l 0 l"
  by (cases l) auto

lemma close_chunk_abs: "abs_l0 (close_chunk s n l) = abs_l s n l"
  by (cases l) (auto simp: close_chunk_def abs_l0_def pend_text_def Rep_mk_str)

lemma close_chunk_wf0: "wf0 (close_chunk s n l)"
  by (cases l) (auto simp: close_chunk_def)

lemma efeed_chunk_correct:
  assumes "wf0 l"
  shows "case stream_run (Rep_bytes s) (abs_l0 l, map_pstate Rep_bytes ps) of
     None \<Rightarrow> has_err (fst (efeed_chunk s (b, l, Some ps, sp)))
   | Some (es, L', P') \<Rightarrow> (\<exists>outs es' l' ps' sp'. efeed_chunk s (b, l, Some ps, sp) =
       (outs, (b + bytes_length s, l', Some ps', sp')) \<and> oks outs = Some es' \<and>
       abs_items es' = es \<and> abs_l0 l' = L' \<and> wf0 l' \<and> map_pstate Rep_bytes ps' = P')"
proof -
  obtain acc l' p' sp' where e: "eloop s (bytes_length s) b 0 l (Some ps) sp [] = (acc, l', p', sp')"
    by (cases "eloop s (bytes_length s) b 0 l (Some ps) sp []") auto
  then have chunk: "efeed_chunk s (b, l, Some ps, sp) =
    (rev acc, (b + bytes_length s, close_chunk s (bytes_length s) l', p', sp'))"
    by (simp add: efeed_chunk_def Let_def)
  from eloop_correct[where n="bytes_length s" and s=s and i=0 and l=l and ps=ps and b=b and sp=sp] assms e
  show ?thesis
    by (auto simp: chunk abs_l_0 wf0_wf_l close_chunk_abs close_chunk_wf0 split: option.splits)
qed

lemma efeed_chunks_correct:
  assumes "wf0 l"
  shows "case stream_run (concat (map Rep_bytes ss)) (abs_l0 l, map_pstate Rep_bytes ps) of
     None \<Rightarrow> has_err (fst (efeed_chunks ss (b, l, Some ps, sp)))
   | Some (es, L', P') \<Rightarrow> (\<exists>outs es' b' l' ps' sp'. efeed_chunks ss (b, l, Some ps, sp) =
       (outs, (b', l', Some ps', sp')) \<and> oks outs = Some es' \<and>
       abs_items es' = es \<and> abs_l0 l' = L' \<and> wf0 l' \<and> map_pstate Rep_bytes ps' = P')"
  using assms
proof (induction ss arbitrary: b l ps sp)
  case (Cons s ss)
  note C = efeed_chunk_correct[OF Cons.prems, where s=s and ps=ps and b=b and sp=sp]
  show ?case
  proof (cases "stream_run (Rep_bytes s) (abs_l0 l, map_pstate Rep_bytes ps)")
    case None
    with C show ?thesis
      by (auto simp: stream_run_append split: prod.splits)
  next
    case (Some x)
    obtain es1 L1 P1 where x: "x = (es1, L1, P1)"
      by (cases x) auto
    with C Some obtain outs1 es1' l1 ps1 sp1 where c1: "efeed_chunk s (b, l, Some ps, sp) =
      (outs1, (b + bytes_length s, l1, Some ps1, sp1))" and "oks outs1 = Some es1'"
      and "abs_items es1' = es1" "abs_l0 l1 = L1" "wf0 l1" "map_pstate Rep_bytes ps1 = P1"
      by auto
    moreover note IH = Cons.IH[OF \<open>wf0 l1\<close>, where b="b + bytes_length s" and ps=ps1 and sp=sp1]
    ultimately show ?thesis
      using Some x by (auto simp: stream_run_append oks_append split: option.splits prod.splits)
  qed
qed simp

lemma efinish_correct:
  assumes "wf0 l"
  shows "case stream_finish (abs_l0 l, map_pstate Rep_bytes ps) of
     None \<Rightarrow> has_err (efinish (b, l, Some ps, sp))
   | Some es \<Rightarrow> (\<exists>es'. oks (efinish (b, l, Some ps, sp)) = Some es' \<and> abs_items es' = es)"
proof (cases l)
  case (E_SIMPLE pre st tp)
  with assms have l: "abs_l0 l = L_SIMPLE (Rep_bytes pre)"
    by (simp add: abs_l0_def pend_text_def)
  have pr: "parse_run [T_STR (Rep_bytes pre)] (map_pstate Rep_bytes ps) =
    map_option (map_prod abs_items (map_pstate Rep_bytes)) (parse_run [T_STR pre] ps)"
    using parse_run_map[of Rep_bytes "[T_STR pre]" ps] by simp
  show ?thesis
    using E_SIMPLE l pr
    by (auto simp: efinish_def stream_finish_def parse_from_def efeed_def efinish_p_def parse_finish_map
      resync_def oks_append oks_rev rev_map[symmetric] split: option.splits prod.splits)
qed (use assms in \<open>auto simp: efinish_def stream_finish_def parse_from_def efinish_p_def abs_l0_def
  parse_finish_map oks_rev rev_map[symmetric] split: option.splits\<close>)

theorem eparse_correct: "map_option abs_items (oks (eparse ss)) = parse_log (concat (map Rep_bytes ss))"
proof -
  have init: "stream_init = (abs_l0 E_INIT, map_pstate Rep_bytes P_INIT)"
    by (simp add: stream_init_def abs_l0_def)
  note C = efeed_chunks_correct[of E_INIT ss 0 P_INIT 0, folded init]
  show ?thesis
  proof (cases "stream_run (concat (map Rep_bytes ss)) stream_init")
    case None
    with C show ?thesis
      by (auto simp: eparse_def parse_log_def einit_def oks_None_iff oks_append split: prod.splits option.splits)
  next
    case (Some x)
    obtain es L' P' where x: "x = (es, L', P')"
      by (cases x) auto
    with C Some obtain outs es' b' l' ps' sp' where
      c: "efeed_chunks ss (0, E_INIT, Some P_INIT, 0) = (outs, (b', l', Some ps', sp'))" "oks outs = Some es'"
      and "abs_items es' = es" "abs_l0 l' = L'" "wf0 l'" "map_pstate Rep_bytes ps' = P'"
      by auto
    moreover note F = efinish_correct[OF \<open>wf0 l'\<close>, where ps=ps' and b=b' and sp=sp']
    ultimately show ?thesis
      using Some x
      by (auto simp: eparse_def parse_log_def einit_def oks_append oks_None_iff split: option.splits)
  qed
qed

theorem efeed_chunks_online:
  "map_option abs_items (oks (fst (efeed_chunks ss einit))) =
   map_option fst (stream_run (concat (map Rep_bytes ss)) stream_init)"
proof -
  have init: "stream_init = (abs_l0 E_INIT, map_pstate Rep_bytes P_INIT)"
    by (simp add: stream_init_def abs_l0_def)
  note C = efeed_chunks_correct[of E_INIT ss 0 P_INIT 0, folded init]
  then show ?thesis
    by (auto simp: einit_def oks_None_iff split: option.splits prod.splits)
qed

(*<*)
end
(*>*)
