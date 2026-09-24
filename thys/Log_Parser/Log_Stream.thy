(*<*)
theory Log_Stream
  imports Log_Lexer Log_Parser
begin
(*>*)

section \<open>Lexing and parsing in one pass\<close>

text \<open>
  The streaming parser feeds each token to the parser as soon as the lexer emits it, so that a
  time point is output as soon as the next item begins (@{text stream_run_prompt} below): it
  reads its input online. Its state pairs the states of the lexer and of the parser.
\<close>

type_synonym sstate = "lstate \<times> string pstate"

definition stream_init :: sstate where
  "stream_init = (L_INIT, P_INIT)"

definition stream_step :: "char \<Rightarrow> sstate \<Rightarrow> (string item list \<times> sstate) option" where
  "stream_step c st = (case st of (l, p) \<Rightarrow> (case lex_step c l of
     None \<Rightarrow> None
   | Some (ts, l') \<Rightarrow> map_option (\<lambda>(es, p'). (es, (l', p'))) (parse_run ts p)))"

fun stream_run :: "string \<Rightarrow> sstate \<Rightarrow> (string item list \<times> sstate) option" where
  "stream_run [] st = Some ([], st)"
| "stream_run (c # s) st = (case stream_step c st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option (apfst ((@) es)) (stream_run s st'))"

definition stream_finish :: "sstate \<Rightarrow> string item list option" where
  "stream_finish st = (case st of (l, p) \<Rightarrow> (case lex_finish l of None \<Rightarrow> None | Some ts \<Rightarrow> parse_from p ts))"

definition parse_log :: "string \<Rightarrow> string item list option" where
  "parse_log s = (case stream_run s stream_init of
     None \<Rightarrow> None
   | Some (es, st) \<Rightarrow> map_option ((@) es) (stream_finish st))"

lemma stream_run_append:
  "stream_run (s @ s') st = (case stream_run s st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option (apfst ((@) es)) (stream_run s' st'))"
  by (induction s arbitrary: st) (auto split: option.splits)

lemma map_option_apfst_pair:
  "map_option (apfst ((@) es)) (map_option (\<lambda>(es', p'). (es', l, p')) x) =
   map_option (\<lambda>(es', p'). (es', l, p')) (map_option (apfst ((@) es)) x)"
  by (cases x) auto

lemma stream_run_lex_run:
  "stream_run s (l, p) = (case lex_run s l of
     None \<Rightarrow> None
   | Some (ts, l') \<Rightarrow> map_option (\<lambda>(es, p'). (es, (l', p'))) (parse_run ts p))"
proof (induction s arbitrary: l p)
  case (Cons c s)
  show ?case
  proof (cases "lex_step c l")
    case (Some r)
    obtain ts l1 where r: "r = (ts, l1)"
      by (cases r)
    show ?thesis
    proof (cases "parse_run ts p")
      case (Some q)
      obtain es p1 where q: "q = (es, p1)"
        by (cases q)
      show ?thesis
        using Some \<open>lex_step c l = Some r\<close> r q Cons.IH[of l1 p1]
        by (auto simp: stream_step_def parse_run_append map_option_apfst_pair split: option.splits)
    qed (use \<open>lex_step c l = Some r\<close> r in \<open>auto simp: stream_step_def parse_run_append split: option.splits\<close>)
  qed (simp add: stream_step_def)
qed simp

lemma parse_log_lex_parse: "parse_log s = (case lex s of None \<Rightarrow> None | Some ts \<Rightarrow> parse ts)"
  by (auto simp: parse_log_def stream_init_def stream_run_lex_run stream_finish_def lex_def parse_def
    parse_from_append split: option.splits)

subsection \<open>Correctness\<close>

theorem parse_log_correct: "parse_log s = Some es \<longleftrightarrow> log_lang s es"
proof
  assume "parse_log s = Some es"
  then obtain ts where "lex s = Some ts" "parse ts = Some es"
    by (auto simp: parse_log_lex_parse split: option.splits)
  then show "log_lang s es"
    by (auto simp: log_lang_def lex_correct parse_correct)
next
  assume "log_lang s es"
  then obtain ts where "lexes s ts" "G_parser ts es"
    by (auto simp: log_lang_def)
  then show "parse_log s = Some es"
    by (simp add: parse_log_lex_parse lex_complete parse_complete)
qed

corollary log_lang_unique: "log_lang s es \<Longrightarrow> log_lang s es' \<Longrightarrow> es = es'"
  by (simp flip: parse_log_correct)

text \<open>The entries that the streaming parser has emitted after reading a prefix of the input are
  a prefix of the meaning of every extension of that input; and if it fails on a prefix, then no
  extension of the prefix is a log.\<close>

corollary stream_run_prefix:
  assumes "stream_run s stream_init = Some (es, st)" "log_lang (s @ s') es'"
  obtains es'' where "es' = es @ es''"
proof -
  from assms(2) have "parse_log (s @ s') = Some es'"
    by (simp add: parse_log_correct)
  with assms(1) show ?thesis
    by (auto simp: parse_log_def stream_run_append split: option.splits intro: that)
qed

corollary stream_run_error:
  assumes "stream_run s stream_init = None"
  shows "\<not> log_lang (s @ s') es'"
proof
  assume "log_lang (s @ s') es'"
  then have "parse_log (s @ s') = Some es'"
    by (simp add: parse_log_correct)
  with assms show False
    by (simp add: parse_log_def stream_run_append)
qed

subsection \<open>Promptness\<close>

text \<open>The streaming parser passes on an entry as soon as the next item begins: once it has read a
  log and the @{text "@"} or @{text ">"} that follows it, it has output all of the log's entries.
  (@{const Glex} excludes a log that ends in a comment without a line end, in which the
  @{text "@"} would belong to the comment.)\<close>

lemma lex_run_Glex_close:
  assumes "Glex s ts" "c = CHR ''@'' \<or> c = CHR ''>''"
  shows "lex_run (s @ [c]) L_INIT = Some (ts @ [if c = CHR ''@'' then T_AT else T_RANGLE], L_INIT)"
proof -
  from Glex_lex_run[OF assms(1)] obtain ts1 l where run: "lex_run s L_INIT = Some (ts1, l)"
    and ends: "lex_ends ts ts1 l"
    by blast
  have c: "\<not> isSimpleChar c" "c \<noteq> CHR 0x22"
    using assms(2) by (auto simp: isSimpleChar_def)
  have init: "lex_run [c] L_INIT = Some ([if c = CHR ''@'' then T_AT else T_RANGLE], L_INIT)"
    using assms(2) by (auto simp: lex_init_def isWhiteSpace_def)
  from ends show ?thesis
    unfolding lex_ends_def
  proof (elim disjE exE conjE)
    assume "l = L_INIT" "ts = ts1"
    with run init show ?thesis
      by (simp add: lex_run_append)
  next
    fix x
    assume "l = L_SIMPLE x" "ts = ts1 @ [T_STR x]"
    with run init c lex_run_close_simple[of c x "[]"] show ?thesis
      by (simp add: lex_run_append)
  qed
qed

lemma parse_finish_close:
  "parse_finish p = Some es \<Longrightarrow> t = T_AT \<or> t = T_RANGLE \<Longrightarrow>
   pstep t p = Some (es, if t = T_AT then P_TS else P_CMD)"
  by (cases p) (auto simp: close_entry_def)

theorem stream_run_prompt:
  assumes "Glex s ts" "G_parser ts es" "c = CHR ''@'' \<or> c = CHR ''>''"
  obtains P where "stream_run (s @ [c]) stream_init = Some (es, L_INIT, P)"
proof -
  from assms(2) have "parse ts = Some es"
    by (rule parse_complete)
  then obtain es1 p es2 where run: "parse_run ts P_INIT = Some (es1, p)"
    and fin: "parse_finish p = Some es2" and es: "es = es1 @ es2"
    by (auto simp: parse_def parse_from_def split: option.splits)
  let ?t = "if c = CHR ''@'' then T_AT else T_RANGLE"
  have "pstep ?t p = Some (es2, if ?t = T_AT then P_TS else P_CMD)"
    using parse_finish_close[OF fin] assms(3) by auto
  with run have "parse_run (ts @ [?t]) P_INIT = Some (es, if ?t = T_AT then P_TS else P_CMD)"
    by (auto simp: parse_run_append es split: if_splits)
  with lex_run_Glex_close[OF assms(1,3)] show ?thesis
    by (auto simp: stream_run_lex_run stream_init_def intro: that)
qed

(*<*)
end
(*>*)
