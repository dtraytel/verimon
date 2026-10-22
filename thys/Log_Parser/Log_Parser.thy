(*<*)
theory Log_Parser
  imports Log_Grammar
begin
(*>*)

section \<open>Parser of the log format\<close>

text \<open>An automaton over tokens whose state records the partial entry, in reverse. It never inspects
  the strings, so it is polymorphic in their type and commutes with maps on them.\<close>

subsection \<open>Parser automaton\<close>

datatype 's pstate = P_INIT | P_TS | P_DB 's "('s \<times> 's list) list"
  | P_NAME 's "('s \<times> 's list) list" 's | P_TUPLES 's "('s \<times> 's list) list" 's
  | P_FIELD1 's "('s \<times> 's list) list" 's | P_AFTER 's "('s \<times> 's list) list" 's "'s list"
  | P_FIELDN 's "('s \<times> 's list) list" 's "'s list" | P_CMD | P_ARGS 's "'s token list"

definition close_entry :: "'s token \<Rightarrow> 's item \<Rightarrow> ('s item list \<times> 's pstate) option" where
  "close_entry t e = (case t of
     T_AT \<Rightarrow> Some ([e], P_TS)
   | T_SEMICOLON \<Rightarrow> Some ([e], P_INIT)
   | T_RANGLE \<Rightarrow> Some ([e], P_CMD)
   | _ \<Rightarrow> None)"

fun pstep :: "'s token \<Rightarrow> 's pstate \<Rightarrow> ('s item list \<times> 's pstate) option" where
  "pstep t P_INIT = (case t of T_AT \<Rightarrow> Some ([], P_TS) | T_RANGLE \<Rightarrow> Some ([], P_CMD) | _ \<Rightarrow> None)"
| "pstep t P_TS = (case t of T_STR ts \<Rightarrow> Some ([], P_DB ts []) | _ \<Rightarrow> None)"
| "pstep t (P_DB ts evs) = (case t of
     T_STR p \<Rightarrow> Some ([], P_NAME ts evs p)
   | _ \<Rightarrow> close_entry t (Entry ts (rev evs)))"
| "pstep t (P_NAME ts evs p) = (case t of
     T_STR q \<Rightarrow> Some ([], P_NAME ts ((p, []) # evs) q)
   | T_LPAREN \<Rightarrow> Some ([], P_FIELD1 ts evs p)
   | _ \<Rightarrow> close_entry t (Entry ts (rev ((p, []) # evs))))"
| "pstep t (P_TUPLES ts evs p) = (case t of
     T_STR q \<Rightarrow> Some ([], P_NAME ts evs q)
   | T_LPAREN \<Rightarrow> Some ([], P_FIELD1 ts evs p)
   | _ \<Rightarrow> close_entry t (Entry ts (rev evs)))"
| "pstep t (P_FIELD1 ts evs p) = (case t of
     T_RPAREN \<Rightarrow> Some ([], P_TUPLES ts ((p, []) # evs) p)
   | T_STR f \<Rightarrow> Some ([], P_AFTER ts evs p [f])
   | _ \<Rightarrow> None)"
| "pstep t (P_AFTER ts evs p fs) = (case t of
     T_COMMA \<Rightarrow> Some ([], P_FIELDN ts evs p fs)
   | T_RPAREN \<Rightarrow> Some ([], P_TUPLES ts ((p, rev fs) # evs) p)
   | _ \<Rightarrow> None)"
| "pstep t (P_FIELDN ts evs p fs) = (case t of T_STR f \<Rightarrow> Some ([], P_AFTER ts evs p (f # fs)) | _ \<Rightarrow> None)"
| "pstep t P_CMD = (case t of T_STR c \<Rightarrow> Some ([], P_ARGS c []) | _ \<Rightarrow> None)"
| "pstep t (P_ARGS c args) = (case t of
     T_LANGLE \<Rightarrow> Some ([Command c (rev args)], P_INIT)
   | _ \<Rightarrow> if cmd_arg t then Some ([], P_ARGS c (t # args)) else None)"

fun parse_finish :: "'s pstate \<Rightarrow> 's item list option" where
  "parse_finish P_INIT = Some []"
| "parse_finish (P_DB ts evs) = Some [Entry ts (rev evs)]"
| "parse_finish (P_NAME ts evs p) = Some [Entry ts (rev ((p, []) # evs))]"
| "parse_finish (P_TUPLES ts evs p) = Some [Entry ts (rev evs)]"
| "parse_finish _ = None"

fun parse_run :: "'s token list \<Rightarrow> 's pstate \<Rightarrow> ('s item list \<times> 's pstate) option" where
  "parse_run [] st = Some ([], st)"
| "parse_run (t # ts) st = (case pstep t st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option (apfst ((@) es)) (parse_run ts st'))"

definition parse_from :: "'s pstate \<Rightarrow> 's token list \<Rightarrow> 's item list option" where
  "parse_from st ts = (case parse_run ts st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option ((@) es) (parse_finish st'))"

definition parse :: "'s token list \<Rightarrow> 's item list option" where
  "parse ts = parse_from P_INIT ts"

lemma parse_run_append:
  "parse_run (ts @ ts') st = (case parse_run ts st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option (apfst ((@) es)) (parse_run ts' st'))"
  by (induction ts arbitrary: st) (auto split: option.splits)

lemma parse_from_append:
  "parse_from st (ts @ ts') = (case parse_run ts st of
     None \<Rightarrow> None
   | Some (es, st') \<Rightarrow> map_option ((@) es) (parse_from st' ts'))"
  by (auto simp: parse_from_def parse_run_append split: option.splits)

subsection \<open>Properties of the grammar\<close>

lemma G_parser_append: "G_parser ts es \<Longrightarrow> G_parser ts' es' \<Longrightarrow> G_parser (ts @ ts') (es @ es')"
  by (induction rule: G_parser.induct) (auto intro: G_parser.intros)

lemma G_db_snoc: "G_db db evs \<Longrightarrow> G_table tb evs' \<Longrightarrow> G_db (db @ tb) (evs @ evs')"
  by (induction rule: G_db.induct) (auto intro: G_db.intros dest: G_db_table[OF _ G_db_empty])

lemma G_tuples_snoc: "G_tuples tus vs \<Longrightarrow> G_tuple tu v \<Longrightarrow> G_tuples (tus @ tu) (vs @ [v])"
  by (induction rule: G_tuples.induct) (auto intro: G_tuples.intros dest: G_tuples_Cons[OF _ G_tuples_Nil])

lemma G_fields_snoc: "G_fields fs us \<Longrightarrow> G_fields (fs @ [T_COMMA, T_STR f]) (us @ [f])"
  by (induction rule: G_fields.induct) (auto intro: G_fields.intros)

subsection \<open>Soundness\<close>

text \<open>The tokens read since the last entry was emitted, for each state.\<close>

inductive pending :: "'s pstate \<Rightarrow> 's token list \<Rightarrow> bool" where
  pending_INIT: "pending P_INIT []"
| pending_TS: "pending P_TS [T_AT]"
| pending_DB: "G_db db evs \<Longrightarrow> pending (P_DB ts (rev evs)) (T_AT # T_STR ts # db)"
| pending_NAME: "G_db db evs \<Longrightarrow> pending (P_NAME ts (rev evs) p) (T_AT # T_STR ts # db @ [T_STR p])"
| pending_TUPLES: "G_db db evs \<Longrightarrow> G_tuples tus vs \<Longrightarrow> vs \<noteq> [] \<Longrightarrow>
    pending (P_TUPLES ts (rev (evs @ map (Pair p) vs)) p) (T_AT # T_STR ts # db @ T_STR p # tus)"
| pending_FIELD1: "G_db db evs \<Longrightarrow> G_tuples tus vs \<Longrightarrow>
    pending (P_FIELD1 ts (rev (evs @ map (Pair p) vs)) p) (T_AT # T_STR ts # db @ T_STR p # tus @ [T_LPAREN])"
| pending_AFTER: "G_db db evs \<Longrightarrow> G_tuples tus vs \<Longrightarrow> G_fields fs us \<Longrightarrow>
    pending (P_AFTER ts (rev (evs @ map (Pair p) vs)) p (rev us))
      (T_AT # T_STR ts # db @ T_STR p # tus @ T_LPAREN # fs)"
| pending_FIELDN: "G_db db evs \<Longrightarrow> G_tuples tus vs \<Longrightarrow> G_fields fs us \<Longrightarrow>
    pending (P_FIELDN ts (rev (evs @ map (Pair p) vs)) p (rev us))
      (T_AT # T_STR ts # db @ T_STR p # tus @ T_LPAREN # fs @ [T_COMMA])"
| pending_CMD: "pending P_CMD [T_RANGLE]"
| pending_ARGS: "list_all cmd_arg args \<Longrightarrow> pending (P_ARGS c (rev args)) (T_RANGLE # T_STR c # args)"

definition step_ok :: "'s token list \<Rightarrow> 's item list \<Rightarrow> 's pstate \<Rightarrow> bool" where
  "step_ok ts es st \<longleftrightarrow> (\<exists>ts1 ts2. ts = ts1 @ ts2 \<and> G_parser ts1 es \<and> pending st ts2)"

lemma step_okI: "ts = u @ v \<Longrightarrow> G_parser u es \<Longrightarrow> pending st v \<Longrightarrow> step_ok ts es st"
  unfolding step_ok_def by blast

lemma step_ok_cont: "pending st ts \<Longrightarrow> step_ok ts [] st"
  by (rule step_okI[of _ "[]"]) (auto intro: G_parser_empty)

lemma G_parser_logentry: "G_logentry le e \<Longrightarrow> G_parser le [e]"
  using G_parser_log[OF _ G_parser_empty] by simp

lemma close_entry_sound:
  assumes G: "G_db db evs" and close: "close_entry t (Entry ts evs) = Some (es, st')"
  shows "step_ok (T_AT # T_STR ts # db @ [t]) es st'"
proof -
  have no_sc: "G_parser (T_AT # T_STR ts # db) [Entry ts evs]"
    using G by (auto intro: G_parser_logentry G_logentry_no_sc)
  have sc: "G_parser (T_AT # T_STR ts # db @ [T_SEMICOLON]) [Entry ts evs]"
    using G by (auto intro: G_parser_logentry G_logentry_sc)
  from close show ?thesis
    by (cases t) (auto simp: close_entry_def intro: step_okI[OF _ no_sc] step_okI[OF _ sc]
      pending_TS pending_CMD pending_INIT)
qed

lemma pending_ARGS_snoc:
  "list_all cmd_arg args \<Longrightarrow> cmd_arg t \<Longrightarrow> pending (P_ARGS c (t # rev args)) (T_RANGLE # T_STR c # args @ [t])"
  using pending_ARGS[of "args @ [t]" c] by simp

lemma pstep_sound:
  assumes P: "pending st ts" and step: "pstep t st = Some (es, st')"
  shows "step_ok (ts @ [t]) es st'"
  using P
proof cases
  case pending_INIT
  with step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending.intros)
next
  case pending_TS
  with step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending.pending_DB[OF G_db_empty, simplified])
next
  case (pending_DB db evs ts0)
  with step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending.pending_NAME intro: close_entry_sound[of db evs, simplified])
next
  case (pending_NAME db evs ts0 p)
  note G' = G_db_snoc[OF pending_NAME(3) G_table_bare[of p]]
  from pending_NAME step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending.pending_NAME[OF G', simplified]
      pending.pending_FIELD1[OF pending_NAME(3) G_tuples_Nil, simplified]
      intro: close_entry_sound[OF G', simplified])
next
  case (pending_TUPLES db evs tus vs ts0 p)
  note G' = G_db_snoc[OF pending_TUPLES(3) G_table_tuples[OF pending_TUPLES(4,5), of p]]
  from pending_TUPLES step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending.pending_NAME[OF G', simplified]
      pending.pending_FIELD1[OF pending_TUPLES(3,4), simplified] intro: close_entry_sound[OF G', simplified])
next
  case (pending_FIELD1 db evs tus vs ts0 p)
  from pending_FIELD1 step show ?thesis
    by (cases t) (auto intro!: step_ok_cont
      pending.pending_TUPLES[OF pending_FIELD1(3) G_tuples_snoc[OF pending_FIELD1(4) G_tuple_empty], simplified]
      pending.pending_AFTER[OF pending_FIELD1(3,4) G_fields_one, simplified])
next
  case (pending_AFTER db evs tus vs fs us ts0 p)
  from pending_AFTER step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending.pending_FIELDN[OF pending_AFTER(3-5), simplified]
      pending.pending_TUPLES[OF pending_AFTER(3)
        G_tuples_snoc[OF pending_AFTER(4) G_tuple_fields[OF pending_AFTER(5)]], simplified])
next
  case (pending_FIELDN db evs tus vs fs us ts0 p)
  from pending_FIELDN step show ?thesis
    by (cases t) (auto intro!: step_ok_cont
      pending.pending_AFTER[OF pending_FIELDN(3,4) G_fields_snoc[OF pending_FIELDN(5)], simplified])
next
  case pending_CMD
  with step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending.pending_ARGS[of "[]", simplified])
next
  case (pending_ARGS args c)
  have "G_parser (T_RANGLE # T_STR c # args @ [T_LANGLE]) [Command c args]"
    using pending_ARGS(3) by (auto intro: G_parser_cmd[OF _ G_parser_empty, simplified] G_command)
  with pending_ARGS step show ?thesis
    by (cases t) (auto intro!: step_ok_cont pending_ARGS_snoc
      intro: step_okI[where v="[]"] pending_INIT split: if_splits)
qed

lemma parse_run_sound:
  "step_ok ts es st \<Longrightarrow> parse_run ts' st = Some (es', st') \<Longrightarrow> step_ok (ts @ ts') (es @ es') st'"
proof (induction ts' arbitrary: ts es st es')
  case Nil
  then show ?case by simp
next
  case (Cons t ts')
  from Cons.prems(2) obtain es1 st1 es2 where step: "pstep t st = Some (es1, st1)"
    and run: "parse_run ts' st1 = Some (es2, st')" and es': "es' = es1 @ es2"
    by (auto split: option.splits)
  from Cons.prems(1) obtain ts1 ts2 where ts: "ts = ts1 @ ts2" and G: "G_parser ts1 es" and P: "pending st ts2"
    unfolding step_ok_def by blast
  from pstep_sound[OF P step] obtain ts3 ts4 where
    ts2: "ts2 @ [t] = ts3 @ ts4" and G3: "G_parser ts3 es1" and P4: "pending st1 ts4"
    unfolding step_ok_def by blast
  have "step_ok (ts @ [t]) (es @ es1) st1"
    using ts ts2 G_parser_append[OF G G3] P4 by (intro step_okI[of _ "ts1 @ ts3" ts4]) auto
  from Cons.IH[OF this run] es' show ?case
    by simp
qed

lemma parse_finish_sound:
  assumes P: "pending st ts" and fin: "parse_finish st = Some es"
  shows "G_parser ts es"
  using P
proof cases
  case (pending_DB db evs ts0)
  with fin show ?thesis
    by (auto intro: G_parser_logentry G_logentry_no_sc)
next
  case (pending_NAME db evs ts0 p)
  with fin G_db_snoc[OF pending_NAME(3) G_table_bare[of p]] show ?thesis
    by (auto intro: G_parser_logentry G_logentry_no_sc[where db = "db @ [T_STR p]", simplified])
next
  case (pending_TUPLES db evs tus vs ts0 p)
  with fin G_db_snoc[OF pending_TUPLES(3) G_table_tuples[OF pending_TUPLES(4,5), of p]] show ?thesis
    by (auto intro: G_parser_logentry G_logentry_no_sc[where db = "db @ T_STR p # tus", simplified])
qed (use fin in \<open>auto intro: G_parser_empty\<close>)

lemma parse_sound: "parse ts = Some es \<Longrightarrow> G_parser ts es"
proof -
  assume "parse ts = Some es"
  then obtain es1 st es2 where run: "parse_run ts P_INIT = Some (es1, st)" and fin: "parse_finish st = Some es2"
    and es: "es = es1 @ es2"
    by (auto simp: parse_def parse_from_def split: option.splits)
  have "step_ok [] [] P_INIT"
    by (intro step_ok_cont pending_INIT)
  from parse_run_sound[OF this run] obtain ts1 ts2 where
    "ts = ts1 @ ts2" "G_parser ts1 es1" "pending st ts2"
    unfolding step_ok_def by auto
  with fin es show ?thesis
    by (auto intro: G_parser_append parse_finish_sound)
qed

subsection \<open>Completeness\<close>

text \<open>The states in which the database of a time point is complete so far; they behave alike on
  the tokens that may follow.\<close>

fun db_evs :: "'s pstate \<Rightarrow> ('s \<times> ('s \<times> 's list) list) option" where
  "db_evs (P_DB ts evs) = Some (ts, evs)"
| "db_evs (P_NAME ts evs p) = Some (ts, (p, []) # evs)"
| "db_evs (P_TUPLES ts evs p) = Some (ts, evs)"
| "db_evs _ = None"

lemma db_evs_STR: "db_evs st = Some (ts, evs) \<Longrightarrow> pstep (T_STR q) st = Some ([], P_NAME ts evs q)"
  by (cases st) auto

lemma db_evs_finish: "db_evs st = Some (ts, evs) \<Longrightarrow> parse_finish st = Some [Entry ts (rev evs)]"
  by (cases st) auto

lemma db_evs_close:
  "db_evs st = Some (ts, evs) \<Longrightarrow> t \<in> {T_AT, T_SEMICOLON, T_RANGLE} \<Longrightarrow> pstep t st = close_entry t (Entry ts (rev evs))"
  by (cases st) auto

lemma parse_run_fields:
  "G_fields fs us \<Longrightarrow> parse_run fs (P_FIELDN ts evs p acc) = Some ([], P_AFTER ts evs p (rev us @ acc))"
  by (induction arbitrary: acc rule: G_fields.induct) auto

lemma parse_run_tuple:
  assumes "G_tuple tu v" "pstep T_LPAREN st = Some ([], P_FIELD1 ts evs p)"
  shows "parse_run tu st = Some ([], P_TUPLES ts ((p, v) # evs) p)"
  using assms(1)
proof cases
  case G_tuple_empty
  with assms(2) show ?thesis
    by simp
next
  case (G_tuple_fields fs)
  from G_tuple_fields(2) obtain f fs' where fs: "fs = T_STR f # fs'"
    by (cases rule: G_fields.cases) auto
  then have "parse_run fs (P_FIELD1 ts evs p) = parse_run fs (P_FIELDN ts evs p [])"
    by simp
  with parse_run_fields[OF G_tuple_fields(2), of ts evs p "[]"] assms(2) G_tuple_fields(1) show ?thesis
    by (simp add: parse_run_append)
qed

lemma G_tuples_Nil_iff: "G_tuples tus [] \<longleftrightarrow> tus = []"
  by (auto elim: G_tuples.cases intro: G_tuples_Nil)

lemma parse_run_tuples:
  "G_tuples tus vs \<Longrightarrow> vs \<noteq> [] \<Longrightarrow> pstep T_LPAREN st = Some ([], P_FIELD1 ts evs p) \<Longrightarrow>
   parse_run tus st = Some ([], P_TUPLES ts (rev (map (Pair p) vs) @ evs) p)"
proof (induction arbitrary: st evs rule: G_tuples.induct)
  case (G_tuples_Cons tu v tus vs)
  from parse_run_tuple[OF G_tuples_Cons(1,5)]
  have run1: "parse_run tu st = Some ([], P_TUPLES ts ((p, v) # evs) p)" .
  show ?case
  proof (cases "vs = []")
    case True
    with G_tuples_Cons(2) have "tus = []"
      by (simp add: G_tuples_Nil_iff)
    with True run1 show ?thesis
      by (simp add: parse_run_append)
  next
    case False
    from G_tuples_Cons.IH[OF False, of "P_TUPLES ts ((p, v) # evs) p" "(p, v) # evs"] run1 show ?thesis
      by (simp add: parse_run_append)
  qed
qed simp

lemma parse_run_table:
  assumes "G_table tb evs'" "db_evs st = Some (ts, evs)"
  shows "\<exists>st'. parse_run tb st = Some ([], st') \<and> db_evs st' = Some (ts, rev evs' @ evs)"
  using assms(1)
proof cases
  case (G_table_bare p)
  with assms(2) show ?thesis
    by (simp add: db_evs_STR)
next
  case (G_table_tuples tus vs p)
  from parse_run_tuples[OF G_table_tuples(3,4), of "P_NAME ts evs p" ts evs p] G_table_tuples(1,2) assms(2)
  show ?thesis
    by (simp add: db_evs_STR)
qed

lemma parse_run_db:
  "G_db db evs' \<Longrightarrow> db_evs st = Some (ts, evs) \<Longrightarrow>
   \<exists>st'. parse_run db st = Some ([], st') \<and> db_evs st' = Some (ts, rev evs' @ evs)"
proof (induction arbitrary: st evs rule: G_db.induct)
  case (G_db_table tb evs1 db evs2)
  from parse_run_table[OF G_db_table(1,4)] obtain st1 where
    run1: "parse_run tb st = Some ([], st1)" and st1: "db_evs st1 = Some (ts, rev evs1 @ evs)"
    by blast
  from G_db_table.IH[OF st1] run1 show ?case
    by (auto simp: parse_run_append)
qed simp

lemma parse_run_logentry:
  assumes "G_logentry le e"
  shows "(\<exists>st ts evs. parse_run le P_INIT = Some ([], st) \<and> db_evs st = Some (ts, evs) \<and> e = Entry ts (rev evs))
    \<or> parse_run le P_INIT = Some ([e], P_INIT)"
  using assms
proof cases
  case (G_logentry_no_sc db evs ts)
  from parse_run_db[OF G_logentry_no_sc(3), of "P_DB ts []" ts "[]"] G_logentry_no_sc(1,2) show ?thesis
    by auto
next
  case (G_logentry_sc db evs ts)
  from parse_run_db[OF G_logentry_sc(3), of "P_DB ts []" ts "[]"] obtain st where
    "parse_run db (P_DB ts []) = Some ([], st)" "db_evs st = Some (ts, rev evs)"
    by auto
  with G_logentry_sc(1,2) show ?thesis
    by (auto simp: parse_run_append db_evs_close close_entry_def)
qed

lemma pstep_cmd_arg: "cmd_arg t \<Longrightarrow> pstep t (P_ARGS c acc) = Some ([], P_ARGS c (t # acc))"
  by (cases t) auto

lemma parse_run_args: "list_all cmd_arg args \<Longrightarrow> parse_run args (P_ARGS c acc) = Some ([], P_ARGS c (rev args @ acc))"
  by (induction args arbitrary: acc) (auto simp: pstep_cmd_arg simp del: pstep.simps)

lemma parse_run_command: "G_command cmd e \<Longrightarrow> parse_run cmd P_INIT = Some ([e], P_INIT)"
  by (cases rule: G_command.cases) (auto simp: parse_run_append parse_run_args)

lemma G_parser_start: "G_parser ts es \<Longrightarrow> ts = [] \<or> (\<exists>r. ts = T_AT # r) \<or> (\<exists>r. ts = T_RANGLE # r)"
  by (cases rule: G_parser.cases) (auto elim: G_logentry.cases G_command.cases)

lemma map_option_append_singleton: "map_option ((@) [x]) X = map_option (Cons x) X"
  by (cases X) auto

lemma parse_from_db_state:
  assumes "db_evs st = Some (ts, evs)" "G_parser tsl es"
  shows "parse_from st tsl = map_option (Cons (Entry ts (rev evs))) (parse_from P_INIT tsl)"
  using G_parser_start[OF assms(2)]
proof (elim disjE exE)
  assume "tsl = []"
  with assms(1) show ?thesis
    by (simp add: parse_from_def db_evs_finish)
next
  fix r
  assume "tsl = T_AT # r"
  with assms(1) show ?thesis
    using parse_from_append[of st "[T_AT]" r] parse_from_append[of P_INIT "[T_AT]" r]
    by (simp add: db_evs_close close_entry_def map_option_append_singleton)
next
  fix r
  assume "tsl = T_RANGLE # r"
  with assms(1) show ?thesis
    using parse_from_append[of st "[T_RANGLE]" r] parse_from_append[of P_INIT "[T_RANGLE]" r]
    by (simp add: db_evs_close close_entry_def map_option_append_singleton)
qed

lemma parse_complete: "G_parser ts es \<Longrightarrow> parse ts = Some es"
  unfolding parse_def
proof (induction rule: G_parser.induct)
  case G_parser_empty
  then show ?case
    by (simp add: parse_from_def)
next
  case (G_parser_log le e ls es)
  from parse_run_logentry[OF G_parser_log(1)] show ?case
  proof (elim disjE exE conjE)
    fix st ts evs
    assume "parse_run le P_INIT = Some ([], st)" "db_evs st = Some (ts, evs)" "e = Entry ts (rev evs)"
    with parse_from_db_state[OF _ G_parser_log(2)] G_parser_log.IH show ?thesis
      by (simp add: parse_from_append)
  next
    assume "parse_run le P_INIT = Some ([e], P_INIT)"
    with G_parser_log.IH show ?thesis
      by (simp add: parse_from_append)
  qed
next
  case (G_parser_cmd cmd e ls es)
  with parse_run_command[OF G_parser_cmd(1)] show ?case
    by (simp add: parse_from_append)
qed

theorem parse_correct: "parse ts = Some es \<longleftrightarrow> G_parser ts es"
  using parse_sound parse_complete by blast

corollary G_parser_unique: "G_parser ts es \<Longrightarrow> G_parser ts es' \<Longrightarrow> es = es'"
  by (simp flip: parse_correct)

subsection \<open>Changing the representation of strings\<close>

lemma cmd_arg_map[simp]: "cmd_arg (map_token f t) = cmd_arg t"
  by (cases t) auto

lemma pstep_map:
  "pstep (map_token f t) (map_pstate f st) = map_option (map_prod (map (map_item f)) (map_pstate f)) (pstep t st)"
  by (cases st; cases t) (auto simp: close_entry_def rev_map)

lemma parse_finish_map: "parse_finish (map_pstate f st) = map_option (map (map_item f)) (parse_finish st)"
  by (cases st) (auto simp: rev_map)

lemma parse_run_map:
  "parse_run (map (map_token f) ts) (map_pstate f st) =
   map_option (map_prod (map (map_item f)) (map_pstate f)) (parse_run ts st)"
proof (induction ts arbitrary: st)
  case (Cons t ts)
  show ?case
  proof (cases "pstep t st")
    case (Some r)
    then show ?thesis
      using Cons.IH by (cases r; cases "parse_run ts (snd r)") (auto simp: pstep_map)
  qed (simp add: pstep_map)
qed simp

(*<*)
end
(*>*)
