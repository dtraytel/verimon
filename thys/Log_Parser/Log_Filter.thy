(*<*)
theory Log_Filter
  imports Log_Stream
begin
(*>*)

section \<open>Dropping the events of irrelevant predicates\<close>

text \<open>
  A monitor only needs the events of the predicates its formula mentions. The parser of this
  theory drops the other events while it reads them: it still reads their tuples, so that a log
  is accepted exactly as before, but it neither keeps their fields nor adds them to the time
  point. Which predicates are kept is a parameter @{text k} of the parser. Its output is the
  output of the parser of @{theory Log_Parser.Log_Parser} with the events of the other predicates
  removed (theorem @{text fparse_log_correct}); this is proved by a simulation: the states of
  the filtering parser are the images of the states of the full parser under @{text fabs}.
\<close>

definition filter_item :: "('s \<Rightarrow> bool) \<Rightarrow> 's item \<Rightarrow> 's item" where
  "filter_item k e = (case e of Entry ts evs \<Rightarrow> Entry ts (filter (k \<circ> fst) evs) | Command c args \<Rightarrow> Command c args)"

lemma filter_item_simps[simp]:
  "filter_item k (Entry ts evs) = Entry ts (filter (k \<circ> fst) evs)"
  "filter_item k (Command c args) = Command c args"
  by (simp_all add: filter_item_def)

lemma filter_item_True[simp]: "filter_item (\<lambda>_. True) = id"
  by (rule ext) (simp add: filter_item_def split: item.splits)

subsection \<open>The parser\<close>

text \<open>The states of the full parser, and for an irrelevant predicate the states that read its
  tuples without recording them (@{text F_SKIP} after its name or a tuple of it).\<close>

datatype 's fpstate = F_INIT | F_TS | F_DB 's "('s \<times> 's list) list" | F_NAME 's "('s \<times> 's list) list" 's
  | F_TUPLES 's "('s \<times> 's list) list" 's | F_FIELD1 's "('s \<times> 's list) list" 's
  | F_AFTER 's "('s \<times> 's list) list" 's "'s list" | F_FIELDN 's "('s \<times> 's list) list" 's "'s list"
  | F_SKIP 's "('s \<times> 's list) list" | F_SFIELD1 's "('s \<times> 's list) list" | F_SAFTER 's "('s \<times> 's list) list"
  | F_SFIELDN 's "('s \<times> 's list) list" | F_CMD | F_ARGS 's "'s token list"

definition fname :: "('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s \<times> 's list) list \<Rightarrow> 's \<Rightarrow> 's fpstate" where
  "fname k ts evs p = (if k p then F_NAME ts evs p else F_SKIP ts evs)"

definition fclose :: "'s token \<Rightarrow> 's item \<Rightarrow> ('s item list \<times> 's fpstate) option" where
  "fclose t e = (case t of
     T_AT \<Rightarrow> Some ([e], F_TS)
   | T_SEMICOLON \<Rightarrow> Some ([e], F_INIT)
   | T_RANGLE \<Rightarrow> Some ([e], F_CMD)
   | _ \<Rightarrow> None)"

fun fstep :: "('s \<Rightarrow> bool) \<Rightarrow> 's token \<Rightarrow> 's fpstate \<Rightarrow> ('s item list \<times> 's fpstate) option" where
  "fstep k t F_INIT = (case t of T_AT \<Rightarrow> Some ([], F_TS) | T_RANGLE \<Rightarrow> Some ([], F_CMD) | _ \<Rightarrow> None)"
| "fstep k t F_TS = (case t of T_STR ts \<Rightarrow> Some ([], F_DB ts []) | _ \<Rightarrow> None)"
| "fstep k t (F_DB ts evs) = (case t of
     T_STR p \<Rightarrow> Some ([], fname k ts evs p)
   | _ \<Rightarrow> fclose t (Entry ts (rev evs)))"
| "fstep k t (F_NAME ts evs p) = (case t of
     T_STR q \<Rightarrow> Some ([], fname k ts ((p, []) # evs) q)
   | T_LPAREN \<Rightarrow> Some ([], F_FIELD1 ts evs p)
   | _ \<Rightarrow> fclose t (Entry ts (rev ((p, []) # evs))))"
| "fstep k t (F_TUPLES ts evs p) = (case t of
     T_STR q \<Rightarrow> Some ([], fname k ts evs q)
   | T_LPAREN \<Rightarrow> Some ([], F_FIELD1 ts evs p)
   | _ \<Rightarrow> fclose t (Entry ts (rev evs)))"
| "fstep k t (F_FIELD1 ts evs p) = (case t of
     T_RPAREN \<Rightarrow> Some ([], F_TUPLES ts ((p, []) # evs) p)
   | T_STR f \<Rightarrow> Some ([], F_AFTER ts evs p [f])
   | _ \<Rightarrow> None)"
| "fstep k t (F_AFTER ts evs p fs) = (case t of
     T_COMMA \<Rightarrow> Some ([], F_FIELDN ts evs p fs)
   | T_RPAREN \<Rightarrow> Some ([], F_TUPLES ts ((p, rev fs) # evs) p)
   | _ \<Rightarrow> None)"
| "fstep k t (F_FIELDN ts evs p fs) = (case t of T_STR f \<Rightarrow> Some ([], F_AFTER ts evs p (f # fs)) | _ \<Rightarrow> None)"
| "fstep k t (F_SKIP ts evs) = (case t of
     T_STR q \<Rightarrow> Some ([], fname k ts evs q)
   | T_LPAREN \<Rightarrow> Some ([], F_SFIELD1 ts evs)
   | _ \<Rightarrow> fclose t (Entry ts (rev evs)))"
| "fstep k t (F_SFIELD1 ts evs) = (case t of
     T_RPAREN \<Rightarrow> Some ([], F_SKIP ts evs)
   | T_STR f \<Rightarrow> Some ([], F_SAFTER ts evs)
   | _ \<Rightarrow> None)"
| "fstep k t (F_SAFTER ts evs) = (case t of
     T_COMMA \<Rightarrow> Some ([], F_SFIELDN ts evs)
   | T_RPAREN \<Rightarrow> Some ([], F_SKIP ts evs)
   | _ \<Rightarrow> None)"
| "fstep k t (F_SFIELDN ts evs) = (case t of T_STR f \<Rightarrow> Some ([], F_SAFTER ts evs) | _ \<Rightarrow> None)"
| "fstep k t F_CMD = (case t of T_STR c \<Rightarrow> Some ([], F_ARGS c []) | _ \<Rightarrow> None)"
| "fstep k t (F_ARGS c args) = (case t of
     T_LANGLE \<Rightarrow> Some ([Command c (rev args)], F_INIT)
   | _ \<Rightarrow> if cmd_arg t then Some ([], F_ARGS c (t # args)) else None)"

fun fparse_finish :: "'s fpstate \<Rightarrow> 's item list option" where
  "fparse_finish F_INIT = Some []"
| "fparse_finish (F_DB ts evs) = Some [Entry ts (rev evs)]"
| "fparse_finish (F_NAME ts evs p) = Some [Entry ts (rev ((p, []) # evs))]"
| "fparse_finish (F_TUPLES ts evs p) = Some [Entry ts (rev evs)]"
| "fparse_finish (F_SKIP ts evs) = Some [Entry ts (rev evs)]"
| "fparse_finish _ = None"

fun fparse_run :: "('s \<Rightarrow> bool) \<Rightarrow> 's token list \<Rightarrow> 's fpstate \<Rightarrow> ('s item list \<times> 's fpstate) option" where
  "fparse_run k [] st = Some ([], st)"
| "fparse_run k (t # ts) st = (case fstep k t st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option (apfst ((@) es)) (fparse_run k ts st'))"

definition fparse_from :: "('s \<Rightarrow> bool) \<Rightarrow> 's fpstate \<Rightarrow> 's token list \<Rightarrow> 's item list option" where
  "fparse_from k st ts = (case fparse_run k ts st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option ((@) es) (fparse_finish st'))"

definition fparse :: "('s \<Rightarrow> bool) \<Rightarrow> 's token list \<Rightarrow> 's item list option" where
  "fparse k ts = fparse_from k F_INIT ts"

subsection \<open>Simulation\<close>

text \<open>The state of the filtering parser that corresponds to a state of the full parser.\<close>

fun fabs :: "('s \<Rightarrow> bool) \<Rightarrow> 's pstate \<Rightarrow> 's fpstate" where
  "fabs k P_INIT = F_INIT"
| "fabs k P_TS = F_TS"
| "fabs k (P_DB ts evs) = F_DB ts (filter (k \<circ> fst) evs)"
| "fabs k (P_NAME ts evs p) = fname k ts (filter (k \<circ> fst) evs) p"
| "fabs k (P_TUPLES ts evs p) =
    (if k p then F_TUPLES ts (filter (k \<circ> fst) evs) p else F_SKIP ts (filter (k \<circ> fst) evs))"
| "fabs k (P_FIELD1 ts evs p) =
    (if k p then F_FIELD1 ts (filter (k \<circ> fst) evs) p else F_SFIELD1 ts (filter (k \<circ> fst) evs))"
| "fabs k (P_AFTER ts evs p fs) =
    (if k p then F_AFTER ts (filter (k \<circ> fst) evs) p fs else F_SAFTER ts (filter (k \<circ> fst) evs))"
| "fabs k (P_FIELDN ts evs p fs) =
    (if k p then F_FIELDN ts (filter (k \<circ> fst) evs) p fs else F_SFIELDN ts (filter (k \<circ> fst) evs))"
| "fabs k P_CMD = F_CMD"
| "fabs k (P_ARGS c args) = F_ARGS c args"

lemma fstep_fabs:
  "fstep k t (fabs k st) = map_option (map_prod (map (filter_item k)) (fabs k)) (pstep t st)"
  by (cases st; cases t) (auto simp: fname_def fclose_def close_entry_def rev_filter)

lemma fparse_finish_fabs: "fparse_finish (fabs k st) = map_option (map (filter_item k)) (parse_finish st)"
  by (cases st) (auto simp: fname_def rev_filter)

lemma fparse_run_fabs:
  "fparse_run k ts (fabs k st) = map_option (map_prod (map (filter_item k)) (fabs k)) (parse_run ts st)"
proof (induction ts arbitrary: st)
  case (Cons t ts)
  show ?case
  proof (cases "pstep t st")
    case (Some r)
    then show ?thesis
      using Cons.IH by (cases r; cases "parse_run ts (snd r)") (auto simp: fstep_fabs map_option_case)
  qed (simp add: fstep_fabs)
qed simp

lemma fparse_from_fabs:
  "fparse_from k (fabs k st) ts = map_option (map (filter_item k)) (parse_from st ts)"
  by (auto simp: fparse_from_def parse_from_def fparse_run_fabs fparse_finish_fabs map_option_case
    split: option.splits)

theorem fparse_correct: "fparse k ts = map_option (map (filter_item k)) (parse ts)"
  using fparse_from_fabs[of k P_INIT ts] by (simp add: fparse_def parse_def)

subsection \<open>Lexing and parsing in one pass\<close>

type_synonym fsstate = "lstate \<times> string fpstate"

definition fstream_init :: fsstate where
  "fstream_init = (L_INIT, F_INIT)"

definition fstream_step :: "(string \<Rightarrow> bool) \<Rightarrow> char \<Rightarrow> fsstate \<Rightarrow> (string item list \<times> fsstate) option" where
  "fstream_step k c st = (case st of (l, p) \<Rightarrow> (case lex_step c l of
     None \<Rightarrow> None
   | Some (ts, l') \<Rightarrow> map_option (\<lambda>(es, p'). (es, (l', p'))) (fparse_run k ts p)))"

fun fstream_run :: "(string \<Rightarrow> bool) \<Rightarrow> string \<Rightarrow> fsstate \<Rightarrow> (string item list \<times> fsstate) option" where
  "fstream_run k [] st = Some ([], st)"
| "fstream_run k (c # s) st = (case fstream_step k c st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option (apfst ((@) es)) (fstream_run k s st'))"

definition fstream_finish :: "(string \<Rightarrow> bool) \<Rightarrow> fsstate \<Rightarrow> string item list option" where
  "fstream_finish k st = (case st of (l, p) \<Rightarrow> (case lex_finish l of None \<Rightarrow> None | Some ts \<Rightarrow> fparse_from k p ts))"

definition fparse_log :: "(string \<Rightarrow> bool) \<Rightarrow> string \<Rightarrow> string item list option" where
  "fparse_log k s = (case fstream_run k s fstream_init of
     None \<Rightarrow> None
   | Some (es, st) \<Rightarrow> map_option ((@) es) (fstream_finish k st))"

lemma fstream_run_append:
  "fstream_run k (s @ s') st = (case fstream_run k s st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option (apfst ((@) es)) (fstream_run k s' st'))"
  by (induction s arbitrary: st) (auto split: option.splits)

lemma fstream_run_fabs:
  "fstream_run k s (l, fabs k p) =
   map_option (\<lambda>(es, l', p'). (map (filter_item k) es, l', fabs k p')) (stream_run s (l, p))"
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
        by (auto simp: fstream_step_def stream_step_def fparse_run_fabs map_option_case split: option.splits)
    qed (use \<open>lex_step c l = Some r\<close> r in \<open>auto simp: fstream_step_def stream_step_def fparse_run_fabs\<close>)
  qed (simp add: fstream_step_def stream_step_def)
qed simp

lemma fstream_finish_fabs:
  "fstream_finish k (l, fabs k p) = map_option (map (filter_item k)) (stream_finish (l, p))"
  by (auto simp: fstream_finish_def stream_finish_def fparse_from_fabs split: option.splits)

lemma fstream_run_init:
  "fstream_run k s fstream_init =
   map_option (\<lambda>(es, l', p'). (map (filter_item k) es, l', fabs k p')) (stream_run s stream_init)"
  using fstream_run_fabs[of k s L_INIT P_INIT] by (simp add: fstream_init_def stream_init_def)

theorem fparse_log_correct: "fparse_log k s = map_option (map (filter_item k)) (parse_log s)"
  by (auto simp: fparse_log_def parse_log_def fstream_run_init fstream_finish_fabs map_option_case
    split: option.splits)

corollary fparse_log_log_lang:
  "fparse_log k s = Some es' \<longleftrightarrow> (\<exists>es. log_lang s es \<and> es' = map (filter_item k) es)"
  by (auto simp: fparse_log_correct parse_log_correct)

text \<open>The filtering parser reads online like the full one: it outputs the filtered entries that
  the full parser outputs, and an entry as soon as the next item begins.\<close>

theorem fstream_run_prompt:
  assumes "Glex s ts" "G_parser ts es" "c = CHR ''@'' \<or> c = CHR ''>''"
  obtains P where "fstream_run k (s @ [c]) fstream_init = Some (map (filter_item k) es, L_INIT, P)"
proof -
  obtain P where "stream_run (s @ [c]) stream_init = Some (es, L_INIT, P)"
    using stream_run_prompt[OF assms] .
  then show ?thesis
    by (auto simp: fstream_run_init intro: that)
qed

subsection \<open>Changing the representation of strings\<close>

lemma fname_map: "map_fpstate f (fname (\<lambda>x. k (f x)) ts evs p) = fname k (f ts) (map (map_prod f (map f)) evs) (f p)"
  by (simp add: fname_def)

lemma fstep_map:
  "fstep k (map_token f t) (map_fpstate f st) =
   map_option (map_prod (map (map_item f)) (map_fpstate f)) (fstep (\<lambda>x. k (f x)) t st)"
  by (cases st; cases t) (auto simp: fname_def fclose_def rev_map)

lemma fparse_finish_map:
  "fparse_finish (map_fpstate f st) = map_option (map (map_item f)) (fparse_finish st)"
  by (cases st) (auto simp: rev_map)

lemma fparse_run_map:
  "fparse_run k (map (map_token f) ts) (map_fpstate f st) =
   map_option (map_prod (map (map_item f)) (map_fpstate f)) (fparse_run (\<lambda>x. k (f x)) ts st)"
proof (induction ts arbitrary: st)
  case (Cons t ts)
  show ?case
  proof (cases "fstep (\<lambda>x. k (f x)) t st")
    case (Some r)
    then show ?thesis
      using Cons.IH by (cases r; cases "fparse_run (\<lambda>x. k (f x)) ts (snd r)") (auto simp: fstep_map map_option_case)
  qed (simp add: fstep_map)
qed simp

(*<*)
end
(*>*)
