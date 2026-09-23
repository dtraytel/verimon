theory Parser imports Lexer "HOL-Library.AList_Mapping" begin

datatype ParserState =
  INITIAL |
  TIMESTAMP |
  TABLE tdb |
  TUPLE tdb string|
  FIELD_1 tdb string|
  AFTER_FIELD tdb string tuple|
  FIELD_N tdb string tuple|
  COMMAND_ARG_1 |
  COMMAND_ARG_N

(* SHORTHAND: ______________________________      ______________________________
              | t   | token                |      | tos | tokens               |
              | tdb | timestamped database |      | tu  | tuple                |
              | ts  | timestamp            |      | f   | field                |
              | db  | database             |      | cmd | command              |
              | ps  | parser state         |      | p   | predicate            |
              |____________________________|      |____________________________| *)


(*We return empty lists when there is nothing to return and the ParserState
stores all the information we need up to that point of tdb construction*)
fun ParserStep :: "TokenType \<Rightarrow> ParserState \<Rightarrow> (tdb list \<times> ParserState) option" where
"ParserStep t INITIAL = (case t of 
  AT \<Rightarrow> Some ([], TIMESTAMP) |
  RIGHT_ANGLE \<Rightarrow> Some ([], COMMAND_ARG_1) |
  _ \<Rightarrow> None
)" |
"ParserStep t TIMESTAMP = (case t of
  STRING ts \<Rightarrow> Some ([], TABLE (ts, Mapping.empty)) |
  _ \<Rightarrow> None
)" |
"ParserStep t (TABLE tdb) = (case t of
  STRING p \<Rightarrow> Some ([], TUPLE tdb p) |
  AT \<Rightarrow> Some ([tdb], TIMESTAMP) |
  SEMICOLON \<Rightarrow> Some ([tdb], INITIAL) |
  RIGHT_ANGLE \<Rightarrow> Some ([tdb], COMMAND_ARG_1) |
  _ \<Rightarrow> None
)" |
"ParserStep t (TUPLE tdb p) = (case t of
  LEFT_PAREN \<Rightarrow> Some ([], FIELD_1 tdb p) |
  STRING p' \<Rightarrow> Some ([], TUPLE tdb p') |
  AT \<Rightarrow> Some ([tdb], TIMESTAMP) |
  SEMICOLON \<Rightarrow> Some ([tdb], INITIAL) |
  RIGHT_ANGLE \<Rightarrow> Some ([tdb], COMMAND_ARG_1) |
  _ \<Rightarrow> None
)" |
"ParserStep t (FIELD_1 (ts, db) p) = (case t of
  STRING f \<Rightarrow> Some ([], AFTER_FIELD (ts, db) p [f]) |
  RIGHT_PAREN \<Rightarrow> Some ([], TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> {[]}) db) p) |
  _ \<Rightarrow> None
)" |
"ParserStep t (AFTER_FIELD (ts, db) p tu) = (case t of
  COMMA \<Rightarrow> Some ([], FIELD_N (ts, db) p tu) |
  RIGHT_PAREN \<Rightarrow> Some ([], TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> {rev tu}) db) p) |
  _ \<Rightarrow> None
)" |
"ParserStep t (FIELD_N tdb p tu) = (case t of
  STRING f \<Rightarrow> Some ([], AFTER_FIELD tdb p (f#tu)) |
  _ \<Rightarrow> None
)" |
"ParserStep t (COMMAND_ARG_1) = (case t of 
  STRING cmd \<Rightarrow> Some ([], COMMAND_ARG_N) |
  _ \<Rightarrow> None
)" |
"ParserStep t (COMMAND_ARG_N) = (case t of
  STRING cmd \<Rightarrow> Some ([], COMMAND_ARG_N) |
  LEFT_ANGLE \<Rightarrow> Some ([], INITIAL) |
  _ \<Rightarrow> None
)"

(*This function would be initailly called with empty tdb list and full TokenType list*)
(*we dont use rev strategy here bc multiple tokens could be returned, i think?*)
fun ParserStepCaller::"TokenType list\<Rightarrow>(tdb list\<times>ParserState)\<Rightarrow>(tdb list\<times>ParserState) option" where
"ParserStepCaller [] tdbp = Some tdbp" |
"ParserStepCaller (t#tos) (tdb, ps) = (case (ParserStep t ps) of
  Some (tdb', ps') \<Rightarrow> ParserStepCaller tos ((tdb @ tdb'), ps') |
  None \<Rightarrow> None
)"

type_synonym State = "(ParserState \<times> LexerState)"
(*Only one char is passed to the lexer because we want to remain flexible*)
(*What to do with LexerState*)
fun ParseOneChar :: "char \<Rightarrow> State \<Rightarrow> (tdb list \<times> State) option" where
"ParseOneChar c (ps, ls) = (case (nextToken c ls) of
  Some (tos, ls') \<Rightarrow> (case ParserStepCaller tos ([], ps) of 
    Some (tdb, ps') \<Rightarrow> Some (tdb, (ps',ls')) |
    None \<Rightarrow> None) |
  None \<Rightarrow> None
)"

fun ParseString :: "char list \<Rightarrow> (tdb list \<times> ParserState) option" where
"ParseString s = (case (LexerStepCaller s ([], Lexer.INITIAL)) of 
  Some (tos, ls) \<Rightarrow> ParserStepCaller tos ([], Parser.INITIAL) |
  None \<Rightarrow> None
)"

(*-SOUNDNESS-------------------------------------------------------------------------------------*)
(*-HELPERS-------------------*)
lemma G_parser_append: "G_parser ts\<^sub>1 tdb\<^sub>1 \<Longrightarrow> G_parser ts\<^sub>2 tdb\<^sub>2 \<Longrightarrow> G_parser (ts\<^sub>1@ts\<^sub>2) (tdb\<^sub>1@tdb\<^sub>2)"
  by (induction ts\<^sub>1 tdb\<^sub>1 rule:G_parser.induct) (simp_all add:G_parser.intros(2) G_parser.intros(3))

lemma G_relation_append: "G_relation ts\<^sub>1 tup\<^sub>1 \<Longrightarrow>
                          G_relation ts\<^sub>2 tup\<^sub>2 \<Longrightarrow> G_relation (ts\<^sub>1@ts\<^sub>2) (tup\<^sub>1\<union>tup\<^sub>2)"
  by (induction ts\<^sub>1 tup\<^sub>1 rule:G_relation.induct) (use G_relation.intros in auto)

lemma G_command_args_append: "G_command_args ts\<^sub>1 \<Longrightarrow> G_command_args ts\<^sub>2 \<Longrightarrow> G_command_args (ts\<^sub>1@ts\<^sub>2)"
  by (induction ts\<^sub>1 rule:G_command_args.induct) (simp_all add:G_command_args.intros(2))

lemma G_db_string_append: "G_db db DB \<Longrightarrow> G_db (db @ [STRING p]) DB"
  by (induction db DB rule:G_db.induct) (auto intro!:G_db.intros(2) G_db.intros(3)
      G_db.intros(2)[OF G_table.intros(1)[OF G_relation.intros(1)] _ G_db.intros(1), simplified]
      simp del:UpdateWith.simps)

lemma G_db_tuples_append_helper: "G_table tb (s,ts) \<Longrightarrow> ts \<noteq> {} \<Longrightarrow>
G_db db db' \<Longrightarrow> db'' = UpdateWith s {} (\<lambda>x. x\<union>ts) db' \<Longrightarrow> G_db (tb @ db) db''"
and G_db_tuples_append_helper': "G_relation tps T \<Longrightarrow> tps \<noteq> [] \<Longrightarrow> T \<noteq> {}"
  using G_db_up by blast (auto intro:G_relation.cases)

lemma G_db_tuples_append: "G_db db DB \<Longrightarrow>
G_relation tps T \<Longrightarrow> tps \<noteq> [] \<Longrightarrow> G_db (db @ STRING p # tps) (UpdateWith p {} (\<lambda>x. x \<union> T) DB)"
  by (induction db DB rule:G_db.induct)
    (auto simp:G_db.intros(3)[OF _ _ G_db.intros(1),simplified] G_table.intros G_db.intros(2)
               G_db_tuples_append_helper' lookup_update' lookup_default_update'
      intro!:mapping_eqI elim:G_db_tuples_append_helper)

lemma G_fields_n_append: "G_fields_n fs fs' \<Longrightarrow> G_fields_n (fs @ [COMMA, STRING f]) (fs' @ [f])"
  by (induction fs fs' rule:G_fields_n.induct) (auto intro!:G_fields_n.intros)

lemma G_parser_db_tuples_semicolon: "G_db db DB \<Longrightarrow> G_relation tps T \<Longrightarrow> tps \<noteq> [] \<Longrightarrow>
G_parser (AT # STRING ts # db @ STRING p # tps @ [SEMICOLON]) [(ts, UpdateWith p {} (\<lambda>x. x\<union>T) DB)]"
  by (simp add:G_parser.intros(2)[OF _ G_parser.intros(1), simplified]
      G_logentry.intros(1)[OF G_db_tuples_append,simplified])

(*-INVARIANT-----------------*)
(* Parser invariant: defines what state a non-outputting token sequence steps to. *)
inductive parser_inv :: "TokenType list \<Rightarrow> ParserState \<Rightarrow> bool" where
  "parser_inv [] INITIAL" |
  "parser_inv [AT] TIMESTAMP" |
  "parser_inv [AT,STRING ts] (TABLE (ts,Mapping.empty))" |
  "G_db db DB \<Longrightarrow> G_relation tps T \<Longrightarrow>parser_inv (AT#STRING ts#db@[STRING p]@tps)
    (TUPLE (ts,if tps = [] then DB else UpdateWith p {} (\<lambda> U. U\<union>T) DB) p)" |
  "G_db db DB \<Longrightarrow> G_relation tps T \<Longrightarrow> parser_inv (AT#STRING ts#db@[STRING p]@tps@[LEFT_PAREN])
    (FIELD_1 (ts,if tps = [] then DB else UpdateWith p {} (\<lambda> U. U\<union>T) DB) p)" |
  "G_db db DB \<Longrightarrow> G_relation tps T \<Longrightarrow> G_fields_n fs fs' \<Longrightarrow>
    parser_inv (AT#STRING ts#db@[STRING p]@tps@[LEFT_PAREN]@fs)
      (AFTER_FIELD (ts,if tps = [] then DB else UpdateWith p {} (\<lambda> U. U\<union>T) DB) p (rev fs'))" |
  "G_db db DB \<Longrightarrow> G_relation tps T \<Longrightarrow> G_fields_n fs fs' \<Longrightarrow>
    parser_inv (AT#STRING ts#db@[STRING p]@tps@[LEFT_PAREN]@fs@[COMMA])
      (FIELD_N (ts,if tps = [] then DB else UpdateWith p {} (\<lambda> U. U\<union>T) DB) p (rev fs'))" |
  "parser_inv [RIGHT_ANGLE] COMMAND_ARG_1" |
  "G_command_args args \<Longrightarrow> parser_inv (RIGHT_ANGLE#args) COMMAND_ARG_N"

(* Relates parser invariant to the grammar: holds for token sequence (ts\<^sub>1@ts\<^sub>2), parser state ps and
   output tdb iif 1) tokenlist ts\<^sub>1 can parse to output tdb according to the grammar, and
   2) tokenlist ts\<^sub>2 steps to parser state ps. *)
inductive parser_G_inv :: "TokenType list \<Rightarrow> ParserState \<Rightarrow> tdb list \<Rightarrow> bool" where
  "G_parser ts\<^sub>1 tdb \<Longrightarrow> parser_inv ts\<^sub>2 ps \<Longrightarrow> parser_G_inv (ts\<^sub>1@ts\<^sub>2) ps tdb"

(*-PROOF---------------------*)
(* Soundness is defined as: if the invariant holds and we step, the invariant must still hold. *)
lemma ParserStepSound: assumes "parser_G_inv ts ps tdb" and "ParserStep t ps = Some (tdb',ps')"
                       shows "parser_G_inv (ts@[t]) ps' (tdb@tdb')"
proof (cases ps)
  case INITIAL
  from this and assms show ?thesis
    by (cases t) (auto simp add:parser_inv.simps parser_G_inv.simps)
next
  case TIMESTAMP
  from this and assms show ?thesis
    by (cases t) (auto simp add:parser_inv.simps parser_G_inv.simps)
next
  case (TABLE tdb'')
  from this and assms show ?thesis
  proof (cases t)
    case (STRING p)
    from assms show ?thesis unfolding STRING TABLE parser_inv.simps parser_G_inv.simps
      apply clarsimp
      apply (rule exI conjI refl)+
       apply assumption
      apply (rule exI [where x = "[]"])
      apply (rule exI [where x = Mapping.empty])
      apply (rule exI [where x = "[]"])
      apply (rule exI [where x = "{}"])
      by (simp add:G_db.intros(1) G_relation.intros(1))
  qed (auto simp:parser_inv.simps parser_G_inv.simps  G_parser_append G_logentry.intros(2)
      G_logentry.intros(1)[OF G_db.intros(1), simplified] G_db.intros(1)
      G_parser.intros(2)[OF _ G_parser.intros(1), simplified]
)
next
  case (TUPLE tdb'' p)
  from this and assms show ?thesis
  proof (cases t)
    case LEFT_PAREN
    from assms show ?thesis unfolding TUPLE LEFT_PAREN parser_inv.simps parser_G_inv.simps
      by clarsimp metis
  next
    case (STRING f)
    from assms show ?thesis unfolding TUPLE STRING parser_inv.simps parser_G_inv.simps
      apply (clarsimp simp del:UpdateWith.simps)
      subgoal for ts\<^sub>1 db DB tps T tsa
        apply (rule exI conjI refl impI)+
          apply assumption
         apply (rule exI [where x = "db @ [STRING p]"])
         apply (rule exI [where x = DB])
         apply (rule exI [where x = tps])
         apply (rule exI [where x = T])
         apply (simp add:G_db_string_append)
        apply (rule exI conjI refl impI)+
         apply assumption
        apply (clarsimp simp del:UpdateWith.simps)
        apply (rule exI [where x = "db @ STRING p # tps"])
        apply (rule exI [where x = "UpdateWith p {} (\<lambda>U. U \<union> T) DB"])
        apply (rule exI [where x = "[]"])
        apply (rule exI [where x = "{}"])
        apply (simp add:G_relation.intros(1) G_db_tuples_append del:UpdateWith.simps)
        done
      done
  qed (auto simp add:parser_inv.simps parser_G_inv.simps G_parser_append G_db_string_append
      G_parser.intros(2)[OF _ G_parser.intros(1),simplified] G_logentry.intros(2)
      G_logentry.intros(1)[OF G_db_string_append,simplified] G_parser_db_tuples_semicolon
      G_db_tuples_append 
      simp del:UpdateWith.simps)
next
  case (FIELD_1 tdb'' p)
  from this and assms show ?thesis
  proof (cases t)
    case RIGHT_PAREN
    from assms show ?thesis unfolding RIGHT_PAREN FIELD_1 parser_inv.simps parser_G_inv.simps
      apply clarsimp
      subgoal for ts\<^sub>1 db DB tps T tsa
        apply (rule exI conjI refl impI)+
          apply assumption
         apply (rule exI [where x = db])
         apply (rule exI [where x = DB])
         apply (rule exI [where x = "[LEFT_PAREN, RIGHT_PAREN]"])
         apply (rule exI [where x = "{[]}"])
         apply (simp add:G_relation.intros(2)[OF _ G_relation.intros(1),simplified]
            G_tuple.intros(1)[OF G_fields.intros(1),simplified])
        apply clarsimp
        apply (rule exI conjI refl)+
         apply assumption
        apply (rule exI [where x = "db"])
        apply (rule exI [where x = "DB"])
        apply (rule exI [where x = "tps@[LEFT_PAREN,RIGHT_PAREN]"])
        apply (rule exI [where x = "insert [] T"])
        apply (simp add:Mapping.lookup_update' Mapping.lookup_default_update' Mapping.update_update
            G_relation_append[OF _ G_relation.intros(2)
              [OF G_tuple.intros[OF G_fields.intros(1)]G_relation.intros(1)], simplified])
        done
      done
  next
    case (STRING f)
    from assms show ?thesis unfolding STRING FIELD_1 parser_inv.simps parser_G_inv.simps
      by clarsimp (metis G_fields_n.intros(1))
  qed (auto simp add:parser_inv.simps parser_G_inv.simps)
next
  case (AFTER_FIELD tdb'' p tu)
  from this and assms show ?thesis
  proof (cases t)
    case RIGHT_PAREN
    from assms show ?thesis unfolding AFTER_FIELD RIGHT_PAREN parser_inv.simps parser_G_inv.simps
      apply clarsimp
      subgoal for ts\<^sub>1 db DB tps T fs fs' tsa
        apply (rule exI conjI refl impI)+
          apply assumption
         apply (rule exI [where x = db])
         apply (rule exI [where x = DB])
         apply (rule exI [where x = " LEFT_PAREN # fs @ [RIGHT_PAREN]"])
         apply (rule exI [where x = "{fs'}"])
         apply (simp add:G_relation.intros(2)[OF _ G_relation.intros(1),simplified]
            G_tuple.intros(1) G_fields.intros(2))
        apply clarsimp
        apply (rule exI conjI refl)+
         apply (assumption)
        apply (rule exI [where x = "db"])
        apply (rule exI [where x = "DB"])
        apply (rule exI [where x = "tps@[LEFT_PAREN]@fs@[RIGHT_PAREN]"])
        apply (rule exI[where x = "insert fs' T"])
        apply (simp add:Mapping.lookup_default_update Mapping.update_update
            G_relation_append [OF _ G_relation.intros(2)[OF G_tuple.intros[OF G_fields.intros(2)]
                G_relation.intros(1)], simplified])
        done
      done
  next
    case (COMMA)
    from assms show ?thesis unfolding AFTER_FIELD COMMA parser_inv.simps parser_G_inv.simps
      by clarsimp metis
  qed (auto simp add:parser_inv.simps parser_G_inv.simps)
next
  case (FIELD_N tdb'' p tu)
  from this and assms show ?thesis
  proof (cases t)
    case (STRING f)
    have fields_n_rev: "\<And>f fs. f # rev fs = rev (fs @ [f])" by simp
    from assms show ?thesis unfolding STRING FIELD_N parser_inv.simps parser_G_inv.simps
      by clarsimp (metis fields_n_rev G_fields_n_append)
  qed (simp_all)
next
  case COMMAND_ARG_1
  from this and assms show ?thesis
  proof (cases t)
    case (STRING arg)
    from assms show ?thesis unfolding STRING COMMAND_ARG_1 parser_inv.simps parser_G_inv.simps
      by clarsimp (auto intro!:G_command_args.intros(1))
  qed (auto simp add:parser_inv.simps parser_G_inv.simps)
next
  case COMMAND_ARG_N
  from this and assms show ?thesis
  proof (cases t)
    case (STRING arg)
    from assms show ?thesis unfolding STRING COMMAND_ARG_N parser_inv.simps parser_G_inv.simps
      by clarsimp (auto intro!:G_command_args.intros(1) G_command_args_append)
  qed (auto simp add:parser_inv.simps parser_G_inv.simps G_command.intros(1) G_parser_append
      G_parser.intros(3)[OF _ G_parser.intros(1), simplified] simp del:append_Nil2)
qed


(*-COMPLETENESS----------------------------------------------------------------------------------*)
(*-INVARIANT-----------------*)
(* The invariant holds for all pairs of parser states and lists of tokens that, if stepped through,
   produces some output and a new parser state. *)
inductive parse_run :: "ParserState \<Rightarrow> TokenType list \<Rightarrow> tdb list \<Rightarrow> ParserState \<Rightarrow> bool" where
  "parse_run ps [] [] ps" |
  "ParserStep t ps = Some (tdb, ps') \<Longrightarrow> parse_run ps' tos tdb' ps'' \<Longrightarrow>
  parse_run ps (t#tos) (tdb@tdb') ps''"

(*-HELPERS-------------------*)
lemma parse_run_append: "parse_run ps tos tdb ps'' \<Longrightarrow> parse_run ps'' tos' tdb' ps' \<Longrightarrow>
  parse_run ps (tos@tos') (tdb@tdb') ps'"
  by (induction ps tos tdb ps'' rule:parse_run.induct) (auto intro!: parse_run.intros(2))

lemma parse_run_singleton: "ParserStep t ps = Some (tdb, ps') \<Longrightarrow> parse_run ps [t] tdb ps'"
  by (simp add:parse_run.intros(2)[OF _ parse_run.intros(1),simplified])

lemma combine_UpdateWith_order:
" Mapping.combine (\<union>) m\<^sub>1 (UpdateWith key {} (\<lambda>x. x\<union>val) m\<^sub>2)
= Mapping.combine (\<union>) (UpdateWith key {} (\<lambda>x. x\<union>val) m\<^sub>1) m\<^sub>2"
  by (intro Mapping.mapping_eqI)
  (auto simp:lookup_default_def lookup_combine combine_options_def lookup_update' option.case_eq_if)

(*-PROOF-SUB-CASES-COMMAND---*)
lemma G_command_args_parse_run:
"G_command_args args \<Longrightarrow> parse_run COMMAND_ARG_1 args [] COMMAND_ARG_N" and
"G_command_args args \<Longrightarrow> parse_run COMMAND_ARG_N args [] COMMAND_ARG_N"
proof (induction args rule:G_command_args.induct)
  case (G_command_args_cmd arg)
  {
    case 1
    show ?case by (simp add:parse_run_singleton)
  next
    case 2
    show ?case by (simp add:parse_run_singleton)
  }
next
  case (G_command_args_cmds args arg)
  {
    case 1
    show ?case
      by(simp add:parse_run_append[OF parse_run_singleton G_command_args_cmds.IH(2),simplified])
  next
    case 2
    show ?case
      by(simp add:parse_run_append[OF parse_run_singleton G_command_args_cmds.IH(2),simplified])
  }
qed

lemma G_command_parse_run: assumes "G_command (RIGHT_ANGLE # args @ [LEFT_ANGLE])"
  shows "parse_run INITIAL (RIGHT_ANGLE # args @ [LEFT_ANGLE]) [] INITIAL"
  and "parse_run (TABLE tdb) (RIGHT_ANGLE # args @ [LEFT_ANGLE]) [tdb] INITIAL"
  and "parse_run (TUPLE tdb p) (RIGHT_ANGLE # args @ [LEFT_ANGLE]) [tdb] INITIAL"
proof -
  have "parse_run COMMAND_ARG_1 args [] COMMAND_ARG_N"
    using assms by (simp add:G_command_args_parse_run G_command.simps)
  moreover have "parse_run COMMAND_ARG_N [LEFT_ANGLE] [] INITIAL"
    by (simp add:parse_run_singleton)
  ultimately have r: "parse_run COMMAND_ARG_1 (args@[LEFT_ANGLE]) [] INITIAL"
    using parse_run_append by fastforce
  show "parse_run INITIAL (RIGHT_ANGLE # args @ [LEFT_ANGLE]) [] INITIAL"
  proof -
    have l: "parse_run INITIAL [RIGHT_ANGLE] [] COMMAND_ARG_1"
      by (simp add:parse_run_singleton)
    show ?thesis by (rule parse_run_append[OF l r,simplified])
  qed
  show "parse_run (TABLE tdb) (RIGHT_ANGLE # args @ [LEFT_ANGLE]) [tdb] INITIAL"
  proof -
    have l: "parse_run (TABLE tdb) [RIGHT_ANGLE] [tdb] COMMAND_ARG_1"
      by (simp add:parse_run_singleton)
    show ?thesis by (rule parse_run_append[OF l r,simplified])
  qed
  show "parse_run (TUPLE tdb p) (RIGHT_ANGLE # args @ [LEFT_ANGLE]) [tdb] INITIAL"
  proof -
    have l: "parse_run (TUPLE tdb p) [RIGHT_ANGLE] [tdb] COMMAND_ARG_1"
      by (simp add:parse_run_singleton)
    show ?thesis by (rule parse_run_append[OF l r,simplified])
  qed
qed

(*-PROOF-SUB-CASES-LOG-ENTRY-*)
lemma G_fields_n_parse_run:
  "G_fields_n fs fs' \<Longrightarrow> parse_run (FIELD_1 (ts, db) p) fs [] (AFTER_FIELD (ts, db) p (rev fs'))"
  and "G_fields_n fs fs'\<Longrightarrow>
       parse_run (FIELD_N (ts, db) p fs'') fs [] (AFTER_FIELD (ts, db) p ((rev fs')@fs''))"
proof (induction fs fs' arbitrary:fs'' rule:G_fields_n.induct)
  case (G_fields_n_f f)
  {
    case 1
    then show ?case by (simp add:parse_run_singleton)
  next
    case 2
    then show ?case by (simp add:parse_run_singleton)
  }
next
  case (G_fields_n_fs fs fs' f)
  {
    case 1
    have l: "parse_run (FIELD_1 (ts, db) p) [STRING f] [] (AFTER_FIELD (ts, db) p [f])"
      by (simp add:parse_run_singleton)
    have r: "parse_run (AFTER_FIELD (ts, db) p [f]) [COMMA] [] (FIELD_N (ts, db) p [f])"
      by (simp add:parse_run_singleton)
    have l: "parse_run (FIELD_1 (ts, db) p) [STRING f,COMMA] [] (FIELD_N (ts, db) p [f])"
      by (rule parse_run_append[OF l r, simplified])
    have r: "parse_run (FIELD_N (ts, db) p [f]) fs [] (AFTER_FIELD (ts, db) p (rev (f # fs')))"
      by (simp add:G_fields_n_fs.IH(2))
    show ?case by (simp add:parse_run_append[OF l r,simplified])
  next
    case 2
    have l: "parse_run (FIELD_N (ts, db) p fs'') [STRING f] [] (AFTER_FIELD (ts, db) p (f#fs''))"
      by (simp add:parse_run_singleton)
    have r: "parse_run (AFTER_FIELD (ts, db) p (f#fs'')) [COMMA] [] (FIELD_N (ts, db) p (f#fs''))"
      by (simp add:parse_run_singleton)
    have l: "parse_run (FIELD_N (ts, db) p fs'') [STRING f,COMMA] [] (FIELD_N (ts, db) p (f#fs''))"
      by (rule parse_run_append[OF l r,simplified])
    have r: "parse_run (FIELD_N (ts, db) p (f#fs'')) fs []
                      (AFTER_FIELD (ts, db) p (rev (f # fs') @ fs''))"
      by (simp add:G_fields_n_fs.IH(2))
    show ?case by (simp add:parse_run_append[OF l r,simplified])
  }
qed

lemma G_tuple_parse_run: assumes "G_tuple (LEFT_PAREN # fs @ [RIGHT_PAREN]) fs'"
  shows "parse_run (TUPLE (ts,db') p) (LEFT_PAREN # fs @ [RIGHT_PAREN]) []
                  (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>{fs'})db') p)"
proof -
  have l: "parse_run (TUPLE (ts,db') p) [LEFT_PAREN] [] (FIELD_1 (ts,db') p)"
    by (simp add:parse_run_singleton)
  have "G_fields fs fs'"
    using assms by (simp add:G_tuple.simps)
  then show ?thesis
  proof (cases fs fs' rule:G_fields.cases)
    case G_fields_empty
    then have "parse_run (FIELD_1 (ts,db') p) [RIGHT_PAREN] []
               (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>{fs'})db') p)" by (simp add:parse_run_singleton)
    then show ?thesis
      using G_fields_empty(1) by (simp add:parse_run_append[OF l _,simplified])
  next
    case G_fields_n
    then have "parse_run (FIELD_1 (ts,db') p) fs [] (AFTER_FIELD (ts,db') p (rev fs'))"
      by (simp add:G_fields_n_parse_run)
    then have l:"parse_run (TUPLE (ts,db') p) (LEFT_PAREN#fs) [] (AFTER_FIELD (ts,db') p (rev fs'))"
      by (rule parse_run_append[OF l _,simplified])
    have "parse_run (AFTER_FIELD (ts,db') p (rev fs')) [RIGHT_PAREN] []
            (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>{fs'})db') p)" by (simp add:parse_run_singleton)
    then show ?thesis by (simp add:parse_run_append[OF l _,simplified])
  qed
qed

lemma G_relation_parse_run: "G_relation re re' \<Longrightarrow>
    ( parse_run (TUPLE (ts,db') p) re [] (TUPLE (ts,db') p) \<and> re = [] \<and> re' = {})
  \<or> ( \<exists>re'' RE'' fs' FS'. G_relation re'' RE'' \<and> G_tuple fs' FS' \<and> re = re''@fs' \<and> re' = RE''\<union>{FS'}
    \<and> parse_run (TUPLE (ts,db') p) re [] (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>re') db') p)
    \<and> re \<noteq> [] \<and> re' \<noteq> {})"
proof (induction re re' arbitrary:db' ts p rule:G_relation.induct)
  case G_relation_empty
  then show ?case
    by (rule disjI1) (simp add:parse_run.intros(1))
next
  case (G_relation_n tu tu' re re')
  have tu_parse_run:"parse_run (TUPLE(ts,db')p) tu [] (TUPLE(ts,UpdateWith p {} (\<lambda>x. x\<union>{tu'})db')p)"
    using G_relation_n(1) by (auto simp add:G_tuple.simps G_tuple_parse_run[OF _,simplified])
  show ?case using G_relation_n.IH[where ts = ts and p = p
        and db' = "UpdateWith p {} (\<lambda>x. x\<union>{tu'})db'"]
  proof (elim disjE)
    assume "parse_run (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db') p) re []
        (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db') p) \<and> re = [] \<and> re' = {}"
    then show ?case
      using G_relation_n.hyps(1) G_relation_n.hyps(2) G_tuple.simps tu_parse_run by auto
  next
    assume "\<exists>re'' RE'' fs' FS'.
        G_relation re'' RE'' \<and> G_tuple fs' FS' \<and> re = re'' @ fs' \<and> re' = RE'' \<union> {FS'}
        \<and> parse_run (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db') p) re []
          (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> re') (UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db')) p)
        \<and> re \<noteq> [] \<and> re' \<noteq> {}"
    then obtain re'' RE'' fs' FS' where assm:
        " G_relation re'' RE'' \<and> G_tuple fs' FS' \<and> re = re'' @ fs' \<and> re' = RE'' \<union> {FS'}
        \<and> parse_run (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db') p) re []
          (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> re') (UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db')) p)
        \<and> re \<noteq> [] \<and> re' \<noteq> {}"
      by blast
    then have "parse_run (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db') p) re []
        (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> re') (UpdateWith p {} (\<lambda>x. x \<union> {tu'}) db')) p)"
      by blast
    then have "parse_run (TUPLE (ts, db') p) (tu @ re) []
        (TUPLE (ts, (UpdateWith p {} (\<lambda>x. x\<union>re') (UpdateWith p {} (\<lambda>x. x\<union>{tu'}) db'))) p)"
      using parse_run_append[OF tu_parse_run _,simplified] by simp
    moreover have "(UpdateWith p {} (\<lambda>x. x\<union>re') (UpdateWith p {} (\<lambda>x. x\<union>{tu'}) db'))
        = UpdateWith p {} (\<lambda>x. x\<union>({tu'}\<union>re')) db'"
      by (simp add:update_update lookup_default_update)
    ultimately have tu_re_parse_run:"parse_run (TUPLE (ts, db') p) (tu @ re) []
        (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> ({tu'} \<union> re')) db') p)"
      by simp
    show ?case
      apply (rule disjI2)
      apply (rule exI[where x = "tu @ re''"])
      apply (rule exI[where x = "{tu'} \<union> RE''"])
      apply (rule exI[where x = "fs'"])
      apply (rule exI[where x = "FS'"])
      using G_relation.intros(2) G_relation_n.hyps(1) assm tu_re_parse_run by auto
  qed
qed

lemma G_table_parse_run: assumes "G_table (STRING p#re) (p, re')" shows
   "( parse_run (TABLE (ts,db'))    (STRING p#re) [] (TUPLE (ts,db') p)
    \<and> parse_run (TUPLE (ts,db') p') (STRING p#re) [] (TUPLE (ts,db') p)
    \<and> re = [] \<and> re' = {})
  \<or> ( \<exists>re'' RE'' fs' FS'. G_relation re'' RE'' \<and> G_tuple fs' FS' \<and> re = re''@fs' \<and> re' = RE''\<union>{FS'}
    \<and> parse_run (TABLE (ts,db'))    (STRING p#re) [] (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>re')db')p)
    \<and> parse_run (TUPLE (ts,db') p') (STRING p#re) [] (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>re')db')p)
    \<and> re \<noteq> [] \<and> re' \<noteq> {})"
proof -
  have l1: "parse_run (TABLE (ts,db')) [STRING p] [] (TUPLE (ts,db') p)"
    by (simp add:parse_run_singleton)
  have l2: "parse_run (TUPLE (ts,db') p') [STRING p] [] (TUPLE (ts,db') p)"
    by (simp add:parse_run_singleton)
  have "G_relation re re'"
    using assms by (simp add:G_table.simps)
  then have "(parse_run (TUPLE (ts,db') p) re [] (TUPLE (ts,db') p) \<and> re = [] \<and> re' = {})
  \<or> (\<exists>re'' RE'' fs' FS'. G_relation re'' RE'' \<and> G_tuple fs' FS' \<and> re = re''@fs' \<and> re' = RE''\<union>{FS'}
      \<and> parse_run (TUPLE (ts,db') p) re [] (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>re') db') p)
      \<and> re \<noteq> [] \<and> re' \<noteq> {})"
    using G_relation_parse_run by simp
  then show ?thesis
  proof (rule disjE)
    assume assm:"parse_run (TUPLE (ts,db') p) re [] (TUPLE (ts,db') p) \<and> re = [] \<and> re' = {}"
    have "parse_run (TABLE (ts,db')) (STRING p#re) [] (TUPLE (ts,db') p)"
      by (simp add: assm l1)
    moreover have "parse_run (TUPLE (ts,db') p') (STRING p#re) [] (TUPLE (ts,db') p)"
      by (simp add: assm l2)
    ultimately show ?thesis using assm by fastforce
  next
    assume assm:"\<exists>re'' RE'' fs' FS'.
        G_relation re'' RE'' \<and> G_tuple fs' FS' \<and> re = re''@fs' \<and> re' = RE''\<union>{FS'}
        \<and> parse_run (TUPLE (ts,db') p) re [] (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>re') db') p)
        \<and> re \<noteq> [] \<and> re' \<noteq> {}"
    have "parse_run (TABLE (ts,db')) (STRING p#re) [] (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>re') db')p)"
      using assm l1 parse_run_append by fastforce
    moreover have "parse_run (TUPLE (ts,db') p') (STRING p#re) []
                                                     (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>re') db')p)"
      using assm l2 parse_run_append by fastforce
    ultimately show ?thesis  using assm by metis
  qed
qed

lemma G_db_parse_run: "G_db db DB \<Longrightarrow>
    (db = [] \<and> DB = Mapping.empty
     \<and> parse_run (TABLE (ts,Mapping.empty)) db [] (TABLE (ts,Mapping.empty)))
  \<or> (\<exists> db' DB' p. G_db db' DB' \<and> db = db'@[STRING p] \<and> DB = DB'
     \<and> parse_run (TABLE (ts,Mapping.empty)) db [] (TUPLE (ts, DB) p))
  \<or> (\<exists> db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
     \<and> db = db'@[STRING p]@re@fs \<and> DB = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
     \<and> parse_run (TABLE (ts,Mapping.empty)) db [] (TUPLE (ts, DB) p))"
  and "G_db db DB \<Longrightarrow>
    (db = [] \<and> DB = Mapping.empty \<and> parse_run (TUPLE (ts,DB'') p') db [] (TUPLE (ts,DB'') p'))
  \<or> (\<exists> db' DB' p. G_db db' DB' \<and> db = db'@[STRING p] \<and> DB = DB'
     \<and> parse_run (TUPLE (ts,DB'') p') db [] (TUPLE (ts, Mapping.combine (\<union>) DB'' DB) p))
  \<or> (\<exists> db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
     \<and> db = db'@[STRING p]@re@fs \<and> DB = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
     \<and> parse_run (TUPLE (ts,DB'') p') db [] (TUPLE (ts, Mapping.combine (\<union>) DB'' DB) p))"
proof (induction db DB arbitrary:ts DB'' p' rule:G_db.induct)
  case G_db_empty
  {
    case 1
    then show ?case by (rule disjI1) (simp add: parse_run.intros(1))
  next
    case 2
    then show ?case by (rule disjI1) (simp add: parse_run.intros(1))
  }
next
  case (G_db_no_up tb\<^sub>c p\<^sub>c ts\<^sub>c db\<^sub>c DB\<^sub>c)
  have tbpred:"tb\<^sub>c = [STRING p\<^sub>c]"
    using G_db_no_up(1) G_db_no_up(2) G_table.simps G_relation.cases by fastforce
  {
    case 1
    have l: "parse_run (TABLE (ts, Mapping.empty)) tb\<^sub>c [] (TUPLE (ts, Mapping.empty) p\<^sub>c)"
      using G_db_no_up.hyps(1) G_table_parse_run tbpred by blast
    show ?case using G_db_no_up.IH(2)[where ts = ts and DB'' = Mapping.empty and p' = p\<^sub>c]
    proof (elim disjE)
      assume "db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TUPLE (ts, Mapping.empty) p\<^sub>c) db\<^sub>c [] (TUPLE (ts, Mapping.empty) p\<^sub>c)"
      then show ?case
        using G_db_no_up.hyps(3) l tbpred by auto
    next
      assume assm: "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TUPLE (ts, Mapping.empty) p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) Mapping.empty DB\<^sub>c) p)"
      then show ?case
        by (metis G_db.G_db_no_up G_db_no_up.hyps(1) G_db_no_up.hyps(2) append_Nil append_assoc
            combine_empty(1) l parse_run_append)
    next
      assume " \<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE
          \<and> G_tuple fs FS \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs
          \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TUPLE (ts, Mapping.empty) p\<^sub>c) db\<^sub>c []
                     (TUPLE (ts, Mapping.combine (\<union>) Mapping.empty DB\<^sub>c) p)"
      then show ?case
        by (smt (verit) G_db.G_db_no_up G_db_no_up.hyps(1) G_db_no_up.hyps(2) Nil_is_append_conv
            append_eq_appendI combine_empty(1) l parse_run_append)
    qed
  next
    case 2
    show ?case using G_db_no_up.IH(2)[where ts = ts and DB'' = DB'' and p' = p\<^sub>c]
    proof (elim disjE)
      assume "db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TUPLE (ts, DB'') p\<^sub>c) db\<^sub>c [] (TUPLE (ts, DB'') p\<^sub>c)"
      then show ?case
        using G_db_no_up.hyps(1) G_db_no_up.hyps(3) G_table_parse_run tbpred by fastforce
    next
      assume assm: "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TUPLE (ts, DB'') p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) DB'' DB\<^sub>c) p)"
      then show ?case
        by (metis (no_types, lifting) G_db.G_db_no_up G_db_no_up.hyps(1) G_table_parse_run
            append_Nil append_assoc parse_run_append tbpred)
    next
      assume " \<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE
          \<and> G_tuple fs FS \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs
          \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TUPLE (ts, DB'') p\<^sub>c) db\<^sub>c []
                     (TUPLE (ts, Mapping.combine (\<union>) DB'' DB\<^sub>c) p)"
      then show ?case
        by (smt (verit) G_db.G_db_no_up G_db_no_up.hyps(1) G_table_parse_run
            Nil_is_append_conv append_eq_appendI parse_run_append tbpred)
    qed
  }
next
  case (G_db_up tb\<^sub>c p\<^sub>c RE\<^sub>c db\<^sub>c DB\<^sub>c)
  {
    case 1
    show ?case using G_db_up(1)
    proof (cases rule:G_table.cases)
      case (1 re)
      then have "\<exists>re' RE' fs' FS'. G_relation re' RE' \<and> G_tuple fs' FS' \<and> re = re' @ fs'
        \<and> RE\<^sub>c = RE'\<union>{FS'} \<and> parse_run (TABLE (ts, Mapping.empty)) tb\<^sub>c []
          (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c) \<and> re \<noteq> [] \<and> RE\<^sub>c \<noteq> {}"
        using G_db_up.hyps(1) G_db_up.hyps(2) G_table_parse_run 1(1) by meson
      then obtain re' RE' fs' FS' where tb_parse_run: "G_relation re' RE' \<and> G_tuple fs' FS'
        \<and> re = re' @ fs' \<and> RE\<^sub>c = RE'\<union>{FS'} \<and> parse_run (TABLE (ts, Mapping.empty)) tb\<^sub>c []
          (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c) \<and> re \<noteq> [] \<and> RE\<^sub>c \<noteq> {}"
        by blast
      then have l: "parse_run (TABLE (ts, Mapping.empty)) tb\<^sub>c []
          (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c)"
        by blast
      show ?thesis using G_db_up.IH(2)[where ts = ts and p' = p\<^sub>c
            and DB'' = "UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty"]
      proof (elim disjE)
        assume assm: "db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty \<and> parse_run
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c)"
        then have "parse_run (TABLE (ts, Mapping.empty)) (tb\<^sub>c@db\<^sub>c) []
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB\<^sub>c) p\<^sub>c)"
          using l by auto
        show ?thesis
          apply (rule disjI2)
          apply (rule disjI2)
          apply (rule exI[where x = "[]"])
          apply (rule exI[where x = Mapping.empty])
          apply (rule exI[where x = re'])
          apply (rule exI[where x = RE'])
          apply (rule exI[where x = fs'])
          apply (rule exI[where x = FS'])
          apply (rule exI[where x = p\<^sub>c])
          using assm G_db.intros(1) 1(1) l tb_parse_run by simp
      next
        assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) DB\<^sub>c) p)"
        then obtain db\<^sub>a DB\<^sub>a p\<^sub>a where assm: "G_db db\<^sub>a DB\<^sub>a \<and> db\<^sub>c = db\<^sub>a @ [STRING p\<^sub>a] \<and> DB\<^sub>c = DB\<^sub>a
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) DB\<^sub>c) p\<^sub>a)"
          by blast
        have "parse_run (TABLE (ts, Mapping.empty)) (tb\<^sub>c @ db\<^sub>c) []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) DB\<^sub>c) p\<^sub>a)"
          using assm l parse_run_append by fastforce
        then have tb_db_parse_run: "parse_run (TABLE (ts, Mapping.empty)) (tb\<^sub>c @ db\<^sub>c) []
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB\<^sub>c) p\<^sub>a)"
          by (metis combine_UpdateWith_order combine_empty(1))
        show ?thesis
          apply (rule disjI2)
          apply (rule disjI1)
          apply (rule exI[where x = "STRING p\<^sub>c # re @ db\<^sub>a"])
          apply (rule exI[where x = "UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB\<^sub>c"])
          apply (rule exI[where x = p\<^sub>a])
          apply (simp add:assm 1(1) del:UpdateWith.simps)
          apply (rule conjI)
           apply (metis "1"(1) G_db.intros(3) G_db_up.hyps(1) G_db_up.hyps(2) append_Cons assm)
          using 1(1) assm tb_db_parse_run by auto
      next
        assume "\<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
            \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) DB\<^sub>c) p)"
        then obtain db\<^sub>a DB\<^sub>a re\<^sub>a RE\<^sub>a fs\<^sub>a FS\<^sub>a p\<^sub>a where
          assm: "G_db db\<^sub>a DB\<^sub>a \<and> G_relation re\<^sub>a RE\<^sub>a \<and> G_tuple fs\<^sub>a FS\<^sub>a
            \<and> db\<^sub>c = db\<^sub>a @ [STRING p\<^sub>a] @ re\<^sub>a @ fs\<^sub>a \<and> DB\<^sub>c = UpdateWith p\<^sub>a {} (\<lambda>x. x \<union> RE\<^sub>a \<union> {FS\<^sub>a}) DB\<^sub>a
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) DB\<^sub>c) p\<^sub>a)"
          by blast
        have "parse_run (TABLE (ts, Mapping.empty)) (tb\<^sub>c @ db\<^sub>c) []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) Mapping.empty) DB\<^sub>c) p\<^sub>a)"
          using assm l parse_run_append by fastforce
        then have tb_db_parse_run: "parse_run (TABLE (ts, Mapping.empty)) (tb\<^sub>c @ db\<^sub>c) []
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB\<^sub>c) p\<^sub>a)"
          by (metis combine_UpdateWith_order combine_empty(1))
        show ?thesis
          apply (rule disjI2)
          apply (rule disjI2)
          apply (rule exI[where x = "STRING p\<^sub>c # re @ db\<^sub>a"])
          apply (rule exI[where x = "UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB\<^sub>a"])
          apply (rule exI[where x = re\<^sub>a])
          apply (rule exI[where x = RE\<^sub>a])
          apply (rule exI[where x = fs\<^sub>a])
          apply (rule exI[where x = FS\<^sub>a])
          apply (rule exI[where x = p\<^sub>a])
          apply (auto simp add:assm 1(1) simp del:UpdateWith.simps)
            apply (metis 1(1) G_db.G_db_up G_db_up.hyps(1) append_Cons assm tb_parse_run)
            apply (simp add:Mapping.lookup_default_update')
          apply (rule conjI)
            apply (simp add:Un_commute Un_left_commute update_update(1))
           apply (simp add:update_update(1) update_update(2))
          using 1(1) assm tb_db_parse_run by auto
      qed
    qed
  next
    case 2
    show ?case using G_db_up(1)
    proof (cases rule:G_table.cases)
      case (1 re)
      then have  "\<exists>re' RE' fs' FS'.
            G_relation re' RE' \<and> G_tuple fs' FS' \<and> re = re' @ fs' \<and> RE\<^sub>c = RE'\<union>{FS'}
          \<and> parse_run (TUPLE (ts, DB'') p') tb\<^sub>c []
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c) \<and> re \<noteq> [] \<and> RE\<^sub>c \<noteq> {}"
        using G_db_up.hyps(1) G_db_up.hyps(2) G_table_parse_run 1(1) by blast
      then obtain re' RE' fs' FS' where tb_parse_run:
          " G_relation re' RE' \<and> G_tuple fs' FS' \<and> re = re' @ fs' \<and> RE\<^sub>c = RE'\<union>{FS'}
          \<and> parse_run (TUPLE (ts, DB'') p') tb\<^sub>c []
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c) \<and> re \<noteq> [] \<and> RE\<^sub>c \<noteq> {}"
          by blast
      show ?thesis using G_db_up.IH(2)[where ts = ts and p' = p\<^sub>c
            and DB'' = "UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB''"]
      proof (elim disjE)
        assume assm: "db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c)"
        show ?thesis
          apply (rule disjI2)
          apply (rule disjI2)
          apply (rule exI[where x = "[]"])
          apply (rule exI[where x = Mapping.empty])
          apply (rule exI[where x = re'])
          apply (rule exI[where x = RE'])
          apply (rule exI[where x = fs'])
          apply (rule exI[where x = FS'])
          apply (rule exI[where x = "p\<^sub>c"])
          apply (simp add: assm G_db.intros(1) 1(1) tb_parse_run
              del: UpdateWith.simps)
          by (metis (no_types, lifting) 1(1) Un_insert_right UpdateWith.simps
              combine_UpdateWith_order combine_empty(2) sup_bot.right_neutral tb_parse_run)
      next
        assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') DB\<^sub>c) p)"
        then obtain db\<^sub>a DB\<^sub>a p\<^sub>a where assm: "G_db db\<^sub>a DB\<^sub>a \<and> db\<^sub>c = db\<^sub>a @ [STRING p\<^sub>a] \<and> DB\<^sub>c = DB\<^sub>a
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') DB\<^sub>c) p\<^sub>a)"
          by blast
        show ?thesis
          apply (rule disjI2)
          apply (rule disjI1)
          apply (rule exI[where x = "tb\<^sub>c @ db\<^sub>a"])
          apply (rule exI[where x = "UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB\<^sub>a"])
          apply (rule exI[where x = "p\<^sub>a"])
          apply (auto simp:G_db.intros(3) G_db_up.hyps(1) assm tb_parse_run)
          using G_db.G_db_up G_db_up.hyps(1) assm tb_parse_run apply fastforce
          using 1(1) assm parse_run_append tb_parse_run
            combine_UpdateWith_order[where m\<^sub>1 = DB'' and m\<^sub>2 = DB\<^sub>c and key = p\<^sub>c and val= RE\<^sub>c] by force
      next
        assume "\<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
            \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') DB\<^sub>c) p)"
        then obtain db\<^sub>a DB\<^sub>a re\<^sub>a RE\<^sub>a fs\<^sub>a FS\<^sub>a p\<^sub>a where
          assm: "G_db db\<^sub>a DB\<^sub>a \<and> G_relation re\<^sub>a RE\<^sub>a \<and> G_tuple fs\<^sub>a FS\<^sub>a
            \<and> db\<^sub>c = db\<^sub>a @ [STRING p\<^sub>a] @ re\<^sub>a @ fs\<^sub>a \<and> DB\<^sub>c = UpdateWith p\<^sub>a {} (\<lambda>x. x \<union> RE\<^sub>a \<union> {FS\<^sub>a}) DB\<^sub>a
            \<and> parse_run (TUPLE (ts, UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') p\<^sub>c) db\<^sub>c []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') DB\<^sub>c) p\<^sub>a)"
          by blast
        have tb_db_parse_run: "parse_run (TUPLE (ts, DB'') p') (tb\<^sub>c @ db\<^sub>c) []
            (TUPLE (ts, Mapping.combine (\<union>) (UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB'') DB\<^sub>c) p\<^sub>a)"
          using assm parse_run_append tb_parse_run by force
        show ?thesis
          apply (rule disjI2)
          apply (rule disjI2)
          apply (rule exI[where x = "STRING p\<^sub>c # re @ db\<^sub>a"])
          apply (rule exI[where x = "UpdateWith p\<^sub>c {} (\<lambda>x. x \<union> RE\<^sub>c) DB\<^sub>a"])
          apply (rule exI[where x = re\<^sub>a])
          apply (rule exI[where x = RE\<^sub>a])
          apply (rule exI[where x = fs\<^sub>a])
          apply (rule exI[where x = FS\<^sub>a])
          apply (rule exI[where x = p\<^sub>a])
          apply (auto simp add:assm 1(1) simp del:UpdateWith.simps)
          using 1(1) G_db.G_db_up G_db_up.hyps(1) G_db_up.hyps(2) assm apply fastforce
            apply (simp add:Mapping.lookup_default_update')
          apply (rule conjI)
            apply (simp add:Un_commute Un_left_commute update_update(1))
          apply (simp add:update_update(1) update_update(2))
          using 1(1) assm tb_db_parse_run combine_UpdateWith_order[where m\<^sub>1 = DB'' and m\<^sub>2 = DB\<^sub>c
              and key = p\<^sub>c and val = RE\<^sub>c] by auto
      qed
    qed
  }
qed

lemma G_logentry_parse_run: assumes "G_logentry le LE"
  shows "parse_run INITIAL le [LE] INITIAL
    \<or> (\<exists>ts. le = [AT,STRING ts] \<and> LE = (ts,Mapping.empty) \<and> parse_run INITIAL le [] (TABLE LE))
    \<or> (\<exists>ts db DB p. G_db db DB \<and> le = [AT,STRING ts]@db@[STRING p]
      \<and> LE = (ts,DB) \<and> parse_run INITIAL le [] (TUPLE LE p))
    \<or> (\<exists>ts db DB re RE fs FS p. G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
      \<and> le = [AT,STRING ts]@db@[STRING p]@re@fs \<and> LE = (ts,UpdateWith p {} (\<lambda>x. x\<union>RE\<union>{FS}) DB)
      \<and> parse_run INITIAL le [] (TUPLE LE p))"
  and "parse_run (TABLE tdb') le [tdb',LE] INITIAL
    \<or> (\<exists>ts. le = [AT,STRING ts] \<and> LE = (ts,Mapping.empty)
      \<and> parse_run (TABLE tdb') le [tdb'] (TABLE LE))
    \<or> (\<exists>ts db DB p. G_db db DB \<and> le = [AT,STRING ts]@db@[STRING p] \<and> LE = (ts,DB)
      \<and> parse_run (TABLE tdb') le [tdb'] (TUPLE LE p))
    \<or> (\<exists>ts db DB re RE fs FS p. G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
      \<and> le = [AT,STRING ts]@db@[STRING p]@re@fs \<and> LE = (ts,UpdateWith p {} (\<lambda>x. x\<union>RE\<union>{FS}) DB)
      \<and> parse_run (TABLE tdb') le [tdb'] (TUPLE LE p))"
  and "parse_run (TUPLE tdb' p') le [tdb',LE] INITIAL
    \<or> (\<exists>ts. le = [AT,STRING ts]\<and>LE = (ts,Mapping.empty)
      \<and> parse_run (TUPLE tdb' p') le [tdb'] (TABLE LE))
    \<or> (\<exists>ts db DB p. G_db db DB \<and> le = [AT,STRING ts]@db@[STRING p]
      \<and> LE = (ts,DB) \<and> parse_run (TUPLE tdb' p') le [tdb'] (TUPLE LE p))
    \<or> (\<exists>ts db DB re RE fs FS p. G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
      \<and> le = [AT,STRING ts]@db@[STRING p]@re@fs \<and> LE = (ts,UpdateWith p {} (\<lambda>x. x\<union>RE\<union>{FS}) DB)
      \<and> parse_run (TUPLE tdb' p') le [tdb'] (TUPLE LE p))"
proof (goal_cases)
  case 1
  have linit: "parse_run INITIAL [AT] [] TIMESTAMP"
    by (simp add:parse_run_singleton)
  show ?case using assms
  proof (cases le LE rule:G_logentry.cases)
    case (G_logentry_sc db\<^sub>c DB\<^sub>c ts\<^sub>c)
    have "parse_run TIMESTAMP [STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (simp add:parse_run_singleton)
    then have lcase: "parse_run INITIAL [AT,STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (rule parse_run_append[OF linit _,simplified])
    show ?thesis using G_db_parse_run[OF G_logentry_sc(3),where ts = ts\<^sub>c]
    proof (elim disjE)
      assume assm: "db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
      then have l: "parse_run INITIAL ([AT,STRING ts\<^sub>c]@db\<^sub>c) [] (TABLE (ts\<^sub>c, Mapping.empty))"
        by (auto simp add: parse_run_append[OF lcase _,simplified])
      have r: "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) [SEMICOLON] [(ts\<^sub>c, Mapping.empty)] INITIAL"
        by (simp add:parse_run_singleton)
      show ?thesis
        using G_logentry_sc(1) G_logentry_sc(2) assm parse_run_append[OF l r, simplified] by blast
    next
      assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain p where l: "parse_run INITIAL ([AT,STRING ts\<^sub>c]@db\<^sub>c) [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        using lcase parse_run_append by fastforce
      have r: "parse_run (TUPLE (ts\<^sub>c, DB\<^sub>c) p) [SEMICOLON] [(ts\<^sub>c, DB\<^sub>c)] INITIAL"
        by (simp add:parse_run_singleton)
      show ?thesis using G_logentry_sc(1) G_logentry_sc(2)
        by (simp add:parse_run_append[OF l r, simplified])
    next
      assume "\<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain p where l: "parse_run INITIAL ([AT,STRING ts\<^sub>c]@db\<^sub>c) [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        using lcase parse_run_append by fastforce
      have r: "parse_run (TUPLE (ts\<^sub>c, DB\<^sub>c) p) [SEMICOLON] [(ts\<^sub>c, DB\<^sub>c)] INITIAL"
        by (simp add:parse_run_singleton)
      show ?thesis using G_logentry_sc(1) G_logentry_sc(2)
        by (simp add:parse_run_append[OF l r, simplified])
    qed
  next
    case (G_logentry_no_sc db\<^sub>c DB\<^sub>c ts\<^sub>c)
    have "parse_run TIMESTAMP [STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (simp add:parse_run_singleton)
    then have lcase: "parse_run INITIAL [AT,STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (rule parse_run_append[OF linit _,simplified])
    show ?thesis using G_db_parse_run[OF G_logentry_no_sc(3),where ts = ts\<^sub>c]
    proof (elim disjE)
      assume assm:"db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
      then have r: "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
        by blast
      show ?thesis
        using parse_run_append[OF lcase r,simplified] G_logentry_no_sc(2) G_logentry_no_sc(1) assm
        by fastforce
    next
      assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' p where assm: "G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run ParserState.INITIAL (AT # STRING ts\<^sub>c # db\<^sub>c) [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (rule parse_run_append[OF lcase _,simplified])
      then show ?thesis
        using assm G_logentry_no_sc(1) G_logentry_no_sc(2) by fastforce
    next
      assume "\<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' re RE fs FS p where assm:"G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run ParserState.INITIAL (AT # STRING ts\<^sub>c # db\<^sub>c) [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (rule parse_run_append[OF lcase _,simplified])
      then show ?thesis
        using assm G_logentry_no_sc(1) G_logentry_no_sc(2) by fastforce
    qed
  qed
next
  case 2
  have linit: "parse_run (TABLE tdb') [AT] [tdb'] TIMESTAMP"
    by (simp add:parse_run_singleton)
  show ?case using assms
  proof (cases le LE rule:G_logentry.cases)
    case (G_logentry_sc db\<^sub>c DB\<^sub>c ts\<^sub>c)
    have "parse_run TIMESTAMP [STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (simp add:parse_run_singleton)
    then have lcase: "parse_run (TABLE tdb') [AT,STRING ts\<^sub>c] [tdb']
                               (TABLE (ts\<^sub>c,Mapping.empty))"
      by (rule parse_run_append[OF linit _,simplified])
    show ?thesis using G_db_parse_run[OF G_logentry_sc(3),where ts = ts\<^sub>c]
    proof (elim disjE)
      assume assm: "db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
      then have "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
        by blast
      then have l: "parse_run (TABLE tdb') ([AT,STRING ts\<^sub>c]@db\<^sub>c) [tdb']
                   (TABLE (ts\<^sub>c, Mapping.empty))"
        by (simp add: parse_run_append[OF lcase _,simplified])
      have r: "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) [SEMICOLON] [(ts\<^sub>c, Mapping.empty)] INITIAL"
        by (simp add:parse_run_singleton)
      then show ?thesis
        using G_logentry_sc(1) G_logentry_sc(2) assm parse_run_append[OF l r, simplified] by blast
    next
      assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' p where assm: "G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have l: "parse_run (TABLE tdb') ([AT,STRING ts\<^sub>c]@db\<^sub>c) [tdb']
                   (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (auto simp add: parse_run_append[OF lcase _,simplified])
      have r: "parse_run (TUPLE (ts\<^sub>c, DB\<^sub>c) p) [SEMICOLON] [(ts\<^sub>c, DB\<^sub>c)] INITIAL"
        by (simp add:parse_run_singleton)
      show ?thesis
        using G_logentry_sc(1) G_logentry_sc(2) assm parse_run_append[OF l r, simplified] by blast
    next
      assume assm:" \<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' re RE fs FS p where assm:"G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have l: "parse_run (TABLE tdb') ([AT,STRING ts\<^sub>c]@db\<^sub>c) [tdb']
                   (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (auto simp add: parse_run_append[OF lcase _,simplified])
      have r: "parse_run (TUPLE (ts\<^sub>c, DB\<^sub>c) p) [SEMICOLON] [(ts\<^sub>c, DB\<^sub>c)] INITIAL"
        by (simp add:parse_run_singleton)
      show ?thesis
        using G_logentry_sc(1) G_logentry_sc(2) assm parse_run_append[OF l r, simplified] by blast
    qed
  next
    case (G_logentry_no_sc db\<^sub>c DB\<^sub>c ts\<^sub>c)
    have "parse_run TIMESTAMP [STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (simp add:parse_run_singleton)
    then have lcase: "parse_run (TABLE tdb') [AT,STRING ts\<^sub>c] [tdb']
                               (TABLE (ts\<^sub>c,Mapping.empty))"
      by (rule parse_run_append[OF linit _,simplified])
    show ?thesis using G_db_parse_run[OF G_logentry_no_sc(3),where ts = ts\<^sub>c]
    proof (elim disjE)
      assume assm:"db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
      then have r: "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
        by blast
      show ?thesis
        using parse_run_append[OF lcase r,simplified] G_logentry_no_sc(2) G_logentry_no_sc(1) assm
        by fastforce
    next
      assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then show ?thesis
        using G_logentry_no_sc(1) G_logentry_no_sc(2)
        by (auto simp add:parse_run_append[OF lcase _,simplified])
    next
      assume "\<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' re RE fs FS p where assm:"G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run (TABLE tdb') (AT # STRING ts\<^sub>c # db\<^sub>c) [tdb'] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (rule parse_run_append[OF lcase _,simplified])
      then show ?thesis
        using assm G_logentry_no_sc(1) G_logentry_no_sc(2) by fastforce
    qed
  qed
next
  case 3
  have linit: "parse_run (TUPLE tdb' p') [AT] [tdb'] TIMESTAMP"
    by (simp add:parse_run_singleton)
  show ?case using assms
  proof (cases le LE rule:G_logentry.cases)
    case (G_logentry_sc db\<^sub>c DB\<^sub>c ts\<^sub>c)
    have "parse_run TIMESTAMP [STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (simp add:parse_run_singleton)
    then have lcase: "parse_run (TUPLE tdb' p') [AT,STRING ts\<^sub>c] [tdb']
            (TABLE (ts\<^sub>c,Mapping.empty))"
      by (rule parse_run_append[OF linit _,simplified])
    show ?thesis using G_db_parse_run[OF G_logentry_sc(3),where ts = ts\<^sub>c]
    proof (elim disjE)
      assume assm: "db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
     then have "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
        by blast
      then have l: "parse_run (TUPLE tdb' p') ([AT,STRING ts\<^sub>c]@db\<^sub>c) [tdb']
                   (TABLE (ts\<^sub>c, Mapping.empty))"
        by (simp add: parse_run_append[OF lcase _,simplified])
      have r: "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) [SEMICOLON] [(ts\<^sub>c, Mapping.empty)] INITIAL"
        by (simp add:parse_run_singleton)
      then show ?thesis
        using G_logentry_sc(1) G_logentry_sc(2) assm parse_run_append[OF l r, simplified] by blast
    next
      assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' p where "G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have l: "parse_run (TUPLE tdb' p') ([AT,STRING ts\<^sub>c]@db\<^sub>c) [tdb']
                   (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (auto simp add: parse_run_append[OF lcase _,simplified])
      have r: "parse_run (TUPLE (ts\<^sub>c, DB\<^sub>c) p) [SEMICOLON] [(ts\<^sub>c, DB\<^sub>c)] INITIAL"
        by (simp add:parse_run_singleton)
      show ?thesis using G_logentry_sc(1) G_logentry_sc(2)
        by (simp add:parse_run_append[OF l r, simplified])
    next
      assume "\<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' re RE fs FS p where assm:"G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have l: "parse_run (TUPLE tdb' p') ([AT,STRING ts\<^sub>c]@db\<^sub>c) [tdb']
                   (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (auto simp add: parse_run_append[OF lcase _,simplified])
      have r: "parse_run (TUPLE (ts\<^sub>c, DB\<^sub>c) p) [SEMICOLON] [(ts\<^sub>c, DB\<^sub>c)] INITIAL"
        by (simp add:parse_run_singleton)
      show ?thesis
        using G_logentry_sc(1) G_logentry_sc(2) assm parse_run_append[OF l r, simplified] by blast
    qed
  next
    case (G_logentry_no_sc db\<^sub>c DB\<^sub>c ts\<^sub>c)
    have "parse_run TIMESTAMP [STRING ts\<^sub>c] [] (TABLE (ts\<^sub>c,Mapping.empty))"
      by (simp add:parse_run_singleton)
    then have lcase: "parse_run (TUPLE tdb' p') [AT,STRING ts\<^sub>c] [tdb']
                               (TABLE (ts\<^sub>c,Mapping.empty))"
      by (rule parse_run_append[OF linit _,simplified])
    show ?thesis using G_db_parse_run[OF G_logentry_no_sc(3),where ts = ts\<^sub>c]
    proof (elim disjE)
      assume assm:"db\<^sub>c = [] \<and> DB\<^sub>c = Mapping.empty
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
      then have r: "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TABLE (ts\<^sub>c, Mapping.empty))"
        by blast
      show ?thesis
        using parse_run_append[OF lcase r,simplified] G_logentry_no_sc(2) G_logentry_no_sc(1) assm
        by fastforce
    next
      assume "\<exists>db' DB' p. G_db db' DB' \<and> db\<^sub>c = db' @ [STRING p] \<and> DB\<^sub>c = DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then show ?thesis
        using G_logentry_no_sc(1) G_logentry_no_sc(2)
        by (auto simp add:parse_run_append[OF lcase _,simplified])
    next
      assume "\<exists>db' DB' re RE fs FS p. G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
      then obtain db' DB' re RE fs FS p where assm:"G_db db' DB' \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> db\<^sub>c = db' @ [STRING p] @ re @ fs \<and> DB\<^sub>c = UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB'
          \<and> parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run (TABLE (ts\<^sub>c, Mapping.empty)) db\<^sub>c [] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by blast
      then have "parse_run (TUPLE tdb' p') (AT # STRING ts\<^sub>c # db\<^sub>c) [tdb'] (TUPLE (ts\<^sub>c, DB\<^sub>c) p)"
        by (rule parse_run_append[OF lcase _,simplified])
      then show ?thesis
        using assm G_logentry_no_sc(1) G_logentry_no_sc(2) by fastforce
    qed
  qed
qed


(*-PROOF-MAIN-CASE-----------*)
(* The completeness lemma shows that for all token lists and corresponding output accepted by the
   grammar, the parser must be able to produce the same output by the invariant on the INITIAL
   parser state as both start and end state. *)
lemma G_parser_parse_run: "G_parser tos tdb \<Longrightarrow> parse_run INITIAL tos tdb INITIAL
\<or> (\<exists>tos' tdb' ts.
      G_parser tos' tdb' \<and> tos = tos'@[AT,STRING ts] \<and> tdb = tdb'@[(ts,Mapping.empty)]
    \<and> parse_run INITIAL tos tdb' (TABLE (ts,Mapping.empty)))
\<or> (\<exists>tos' tdb' db DB ts p.
      G_parser tos' tdb' \<and> G_db db DB \<and> tos = tos'@[AT,STRING ts]@db@[STRING p]
    \<and> tdb = tdb'@[(ts,DB)] \<and> parse_run INITIAL tos tdb' (TUPLE (ts,DB) p))
\<or> (\<exists>tos' tdb' db DB tps T fs FS ts p.
      G_parser tos' tdb' \<and> G_db db DB \<and> G_relation tps T \<and> G_tuple fs FS
    \<and> tos = tos'@[AT,STRING ts]@db@[STRING p]@tps@fs
    \<and> tdb = tdb'@[(ts,UpdateWith p {} (\<lambda>x. x\<union>T\<union>{FS}) DB)]
    \<and> parse_run INITIAL tos tdb' (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>T\<union>{FS}) DB) p))"
and "G_parser tos tdb \<Longrightarrow> (parse_run (TABLE tdb\<^sub>i) tos tdb (TABLE tdb\<^sub>i) \<and> tos = [] \<and> tdb = [])
\<or> parse_run (TABLE tdb\<^sub>i) tos ([tdb\<^sub>i]@tdb) INITIAL
\<or> (\<exists>tos' tdb' ts.
      G_parser tos' tdb' \<and> tos = tos'@[AT,STRING ts] \<and> tdb = tdb'@[(ts,Mapping.empty)]
    \<and> parse_run (TABLE tdb\<^sub>i) tos ([tdb\<^sub>i]@tdb') (TABLE (ts,Mapping.empty)))
\<or> (\<exists>tos' tdb' db DB ts p.
      G_parser tos' tdb' \<and> G_db db DB \<and> tos = tos'@[AT,STRING ts]@db@[STRING p]
    \<and> tdb = tdb'@[(ts,DB)] \<and> parse_run (TABLE tdb\<^sub>i) tos ([tdb\<^sub>i]@tdb') (TUPLE (ts,DB) p))
\<or> (\<exists>tos' tdb' db DB tps T fs FS ts p.
      G_parser tos' tdb' \<and> G_db db DB \<and> G_relation tps T \<and> G_tuple fs FS
    \<and> tos = tos'@[AT,STRING ts]@db@[STRING p]@tps@fs
    \<and> tdb = tdb'@[(ts,UpdateWith p {} (\<lambda>x. x\<union>T\<union>{FS}) DB)]
    \<and> parse_run (TABLE tdb\<^sub>i) tos ([tdb\<^sub>i]@tdb') (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>T\<union>{FS}) DB) p))"
and "G_parser tos tdb \<Longrightarrow> (parse_run (TUPLE tdb\<^sub>i p\<^sub>i) tos tdb (TUPLE tdb\<^sub>i p\<^sub>i) \<and> tos = [] \<and> tdb = [])
\<or> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) tos ([tdb\<^sub>i]@tdb) INITIAL
\<or> (\<exists>tos' tdb' ts.
      G_parser tos' tdb' \<and> tos = tos'@[AT,STRING ts] \<and> tdb = tdb'@[(ts,Mapping.empty)]
    \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) tos ([tdb\<^sub>i]@tdb') (TABLE (ts,Mapping.empty)))
\<or> (\<exists>tos' tdb' db DB ts p.
      G_parser tos' tdb' \<and> G_db db DB \<and> tos = tos'@[AT,STRING ts]@db@[STRING p]
    \<and> tdb = tdb'@[(ts,DB)] \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) tos ([tdb\<^sub>i]@tdb') (TUPLE (ts,DB) p))
\<or> (\<exists>tos' tdb' db DB tps T fs FS ts p.
      G_parser tos' tdb' \<and> G_db db DB \<and> G_relation tps T \<and> G_tuple fs FS
    \<and> tos = tos'@[AT,STRING ts]@db@[STRING p]@tps@fs
    \<and> tdb = tdb'@[(ts,UpdateWith p {} (\<lambda>x. x\<union>T\<union>{FS}) DB)]
    \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) tos ([tdb\<^sub>i]@tdb') (TUPLE (ts,UpdateWith p {} (\<lambda>x. x\<union>T\<union>{FS}) DB) p))"
proof (induction tos tdb arbitrary:tdb\<^sub>i p\<^sub>i rule: G_parser.induct)
  case G_parser_empty
  {
    case 1
    then show ?case by (simp add:parse_run.intros(1))
  next
    case 2
    then show ?case by (simp add:parse_run.intros(1))
  next
    case 3
    then show ?case by (simp add:parse_run.intros(1))
  }
next
  case (G_parser_log le le' ls ls')
  {
    case 1
    show ?case using G_logentry_parse_run(1)[OF G_parser_log(1)]
    proof (elim disjE)
      assume assm: "parse_run INITIAL le [le'] INITIAL"
      show ?case using G_parser_log.IH(1)
      proof (elim disjE)
        assume "parse_run INITIAL ls ls' INITIAL"
        then show ?case by (simp add:parse_run_append[OF assm _,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run INITIAL ls tdb' (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                          append.left_neutral append_Cons assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run INITIAL ls tdb' (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append.left_neutral append_Cons assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run INITIAL ls tdb' (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x\<union>T'\<union>{FS'}) DB')p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append.left_neutral append_Cons assm parse_run_append)
      qed
    next
      assume assm: "\<exists>ts. le = [AT, STRING ts] \<and> le' = (ts, Mapping.empty)
          \<and> parse_run ParserState.INITIAL le [] (TABLE le')"
      show ?case using G_parser_log.IH(2)[where tdb\<^sub>i = le']
      proof (elim disjE)
        assume "parse_run (TABLE le') ls ls' (TABLE le') \<and> ls = [] \<and> ls' = []"
        then show ?case
          using G_parser_log.hyps(2) assm by auto
      next
        assume r: "parse_run (TABLE le') ls ([le'] @ ls') INITIAL"
        have l: "parse_run INITIAL le [] (TABLE le')"
          using assm by blast
        show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?thesis
          by (smt (verit) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc append_Cons
                          append_Nil assm parse_run_append)
      qed
    next
      assume "\<exists>ts db DB p. G_db db DB \<and> le = [AT, STRING ts] @ db @ [STRING p] \<and> le' = (ts, DB)
          \<and> parse_run ParserState.INITIAL le [] (TUPLE le' p)"
      then obtain ts db DB p where assm: "G_db db DB \<and> le = [AT, STRING ts] @ db @ [STRING p]
          \<and> le' = (ts, DB) \<and> parse_run ParserState.INITIAL le [] (TUPLE le' p)" by blast
      show ?case using G_parser_log.IH(3)[where tdb\<^sub>i = le' and p\<^sub>i = p]
      proof (elim disjE)
        assume "parse_run (TUPLE le' p) ls ls' (TUPLE le' p) \<and> ls = [] \<and> ls' = []"
        then show ?case
          by (metis G_parser_log.hyps(2) append.right_neutral append_self_conv2 assm)
      next
        assume r:"parse_run (TUPLE le' p) ls ([le'] @ ls') INITIAL"
        have l: "parse_run INITIAL le [] (TUPLE le' p)"
          using assm by blast
        then show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc append_Cons
                                append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_SIG) G_parser.G_parser_log G_parser_log.hyps(1) append.left_neutral
                                    append_Cons append_assoc assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      qed
    next
      assume assm: "\<exists>ts db DB re RE fs FS p. G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> le = [AT, STRING ts] @ db @ [STRING p] @ re @ fs
          \<and> le' = (ts, UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB)
          \<and> parse_run ParserState.INITIAL le [] (TUPLE le' p)"
      then obtain ts db DB re RE fs FS p where assm: "G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> le = [AT, STRING ts] @ db @ [STRING p] @ re @ fs
          \<and> le' = (ts, UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB)
          \<and> parse_run ParserState.INITIAL le [] (TUPLE le' p)"
        by blast
      show ?case using G_parser_log.IH(3)[where tdb\<^sub>i = le' and p\<^sub>i = p]
      proof (elim disjE)
        assume "parse_run (TUPLE le' p) ls ls' (TUPLE le' p) \<and> ls = [] \<and> ls' = []"
        then show ?case
          using G_parser_log.hyps(2) assm by fastforce
      next
        assume r:"parse_run (TUPLE le' p) ls ([le'] @ ls') INITIAL"
        have l: "parse_run INITIAL le [] (TUPLE le' p)"
          using assm by blast
        then show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc append_Cons
                                append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      qed
    qed
  next
    case 2
    show ?case using G_logentry_parse_run(2)[OF G_parser_log(1), where tdb' = tdb\<^sub>i]
    proof (elim disjE)
      assume assm: "parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i, le'] INITIAL"
      show ?case using G_parser_log.IH(1)
      proof (elim disjE)
        assume "parse_run INITIAL ls ls' INITIAL"
        then show ?case by (simp add:parse_run_append[OF assm _,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run INITIAL ls tdb' (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                          append.left_neutral append_Cons assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run INITIAL ls tdb' (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append.left_neutral append_Cons assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run INITIAL ls tdb' (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x\<union>T'\<union>{FS'}) DB')p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append.left_neutral append_Cons assm parse_run_append)
      qed
    next
      assume assm: "\<exists>ts. le = [AT, STRING ts] \<and> le' = (ts, Mapping.empty)
          \<and> parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TABLE le')"
      show ?case using G_parser_log.IH(2)[where tdb\<^sub>i = le']
      proof (elim disjE)
        assume "parse_run (TABLE le') ls ls' (TABLE le') \<and> ls = [] \<and> ls' = []"
        then show ?case
          using G_parser_log.hyps(2) assm by auto
      next
        assume r: "parse_run (TABLE le') ls ([le'] @ ls') INITIAL"
        have l: "parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TABLE le')"
          using assm by blast
        show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?thesis
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      qed
    next
      assume "\<exists>ts db DB p. G_db db DB \<and> le = [AT, STRING ts] @ db @ [STRING p]
          \<and> le' = (ts, DB) \<and> parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
      then obtain ts db DB p where assm: "G_db db DB \<and> le = [AT, STRING ts] @ db @ [STRING p]
          \<and> le' = (ts, DB) \<and> parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
        by blast
      show ?case using G_parser_log.IH(3)[where tdb\<^sub>i = le' and p\<^sub>i = p]
      proof (elim disjE)
        assume "parse_run (TUPLE le' p) ls ls' (TUPLE le' p) \<and> ls = [] \<and> ls' = []"
        then show ?case
          by (metis G_parser_log.hyps(2) append.right_neutral append_Nil assm)
      next
        assume r:"parse_run (TUPLE le' p) ls ([le'] @ ls') INITIAL"
        have l: "parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
          using assm by blast
        then show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc append_Cons
                                append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_SIG) G_parser.G_parser_log G_parser_log.hyps(1) append.left_neutral
                                    append_Cons append_assoc assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      qed
    next
      assume "\<exists>ts db DB re RE fs FS p. G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> le = [AT, STRING ts] @ db @ [STRING p] @ re @ fs
          \<and> le' = (ts, UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB)
          \<and> parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
      then obtain ts db DB re RE fs FS p where assm: "G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> le = [AT, STRING ts] @ db @ [STRING p] @ re @ fs
          \<and> le' = (ts, UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB)
          \<and> parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
        by blast
      show ?case using G_parser_log.IH(3)[where tdb\<^sub>i = le' and p\<^sub>i = p]
      proof (elim disjE)
        assume "parse_run (TUPLE le' p) ls ls' (TUPLE le' p) \<and> ls = [] \<and> ls' = []"
        then show ?case
          using G_parser_log.hyps(2) assm by force
      next
        assume r:"parse_run (TUPLE le' p) ls ([le'] @ ls') INITIAL"
        have l: "parse_run (TABLE tdb\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
          using assm by blast
        then show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc append_Cons
                          append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      qed
    qed
  next
    case 3
    show ?case using G_logentry_parse_run(3)[OF G_parser_log(1), where tdb' = tdb\<^sub>i and p' = p\<^sub>i]
    proof (elim disjE)
      assume assm: "parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i, le'] INITIAL"
      show ?case using G_parser_log.IH(1)
      proof (elim disjE)
        assume "parse_run INITIAL ls ls' INITIAL"
        then show ?case by (simp add:parse_run_append[OF assm _,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run INITIAL ls tdb' (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                          append.left_neutral append_Cons assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run INITIAL ls tdb' (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append.left_neutral append_Cons assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run INITIAL ls tdb' (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x\<union>T'\<union>{FS'}) DB')p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append.left_neutral append_Cons assm parse_run_append)
      qed
    next
      assume assm: "\<exists>ts'. le = [AT, STRING ts'] \<and> le' = (ts', Mapping.empty)
          \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TABLE le')"
      show ?case using G_parser_log.IH(2)[where tdb\<^sub>i = le']
      proof (elim disjE)
        assume "parse_run (TABLE le') ls ls' (TABLE le') \<and> ls = [] \<and> ls' = []"
        then show ?case
          using G_parser_log.hyps(2) assm by auto
      next
        assume r: "parse_run (TABLE le') ls ([le'] @ ls') INITIAL"
        have l: "parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TABLE le')"
          using assm by blast
        show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TABLE le') ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?thesis
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append_Cons
                                          append_Nil assm parse_run_append)

      qed
    next
      assume "\<exists>ts db DB p. G_db db DB \<and> le = [AT, STRING ts] @ db @ [STRING p]
          \<and> le' = (ts, DB) \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
      then obtain ts db DB p where assm: "G_db db DB \<and> le = [AT, STRING ts] @ db @ [STRING p]
          \<and> le' = (ts, DB) \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
        by blast
      show ?case using G_parser_log.IH(3)[where tdb\<^sub>i = le' and p\<^sub>i = p]
      proof (elim disjE)
        assume "parse_run (TUPLE le' p) ls ls' (TUPLE le' p) \<and> ls = [] \<and> ls' = []"
        then show ?case
          by (metis G_parser_log.hyps(2) append.right_neutral append_Nil assm)
      next
        assume r:"parse_run (TUPLE le' p) ls ([le'] @ ls') INITIAL"
        have l: "parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
          using assm by blast
        then show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc append_Cons
                                append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_SIG) G_parser.G_parser_log G_parser_log.hyps(1) append.left_neutral
                                    append_Cons append_assoc assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      qed
    next
      assume "\<exists>ts db DB re RE fs FS p. G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> le = [AT, STRING ts] @ db @ [STRING p] @ re @ fs
          \<and> le' = (ts, UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB)
          \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
      then obtain ts db DB re RE fs FS p where assm: "G_db db DB \<and> G_relation re RE \<and> G_tuple fs FS
          \<and> le = [AT, STRING ts] @ db @ [STRING p] @ re @ fs
          \<and> le' = (ts, UpdateWith p {} (\<lambda>x. x \<union> RE \<union> {FS}) DB)
          \<and> parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
        by blast
      show ?case using G_parser_log.IH(3)[where tdb\<^sub>i = le' and p\<^sub>i = p]
      proof (elim disjE)
        assume "parse_run (TUPLE le' p) ls ls' (TUPLE le' p) \<and> ls = [] \<and> ls' = []"
        then show ?case
          using G_parser_log.hyps(2) assm by force
      next
        assume r:"parse_run (TUPLE le' p) ls ([le'] @ ls') INITIAL"
        have l: "parse_run (TUPLE tdb\<^sub>i p\<^sub>i) le [tdb\<^sub>i] (TUPLE le' p)"
          using assm by blast
        then show ?case
          by (simp add:parse_run_append[OF l r,simplified])
      next
        assume "\<exists>tos' tdb' ts'. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts']
                \<and> ls' = tdb' @ [(ts', Mapping.empty)]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TABLE (ts', Mapping.empty))"
        then show ?case
          by (smt (verit, best) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc append_Cons
                                append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] \<and> ls' = tdb' @ [(ts', DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb') (TUPLE (ts', DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      next
        assume "\<exists>tos' tdb' db' DB' tps' T' fs' FS' ts' p'. G_parser tos' tdb' \<and> G_db db' DB'
                \<and> G_relation tps' T' \<and> G_tuple fs' FS'
                \<and> ls = tos' @ [AT, STRING ts'] @ db' @ [STRING p'] @ tps' @ fs'
                \<and> ls' = tdb' @ [(ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB')]
                \<and> parse_run (TUPLE le' p) ls ([le'] @ tdb')
                           (TUPLE (ts', UpdateWith p' {} (\<lambda>x. x \<union> T' \<union> {FS'}) DB') p')"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser.G_parser_log G_parser_log.hyps(1) append.assoc
                                          append_Cons append_Nil assm parse_run_append)
      qed
    qed
  }
next
  case (G_parser_cmd cmd ls ls')
  {
    case 1
      from G_parser_cmd(3) show ?case
      proof (elim disjE)
        assume assumption:"parse_run INITIAL ls ls' INITIAL"
        have l: "parse_run INITIAL cmd [] INITIAL"
          using G_parser_cmd(1) by (auto simp add:G_command_parse_run G_command.simps)
        show ?case by (simp add:parse_run_append[OF l assumption,simplified])
      next
        assume "\<exists>tos' tdb' ts. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts]
          \<and> ls' = tdb' @ [(ts, Mapping.empty)]
          \<and> parse_run INITIAL ls tdb' (TABLE (ts, Mapping.empty))"
        then show ?case
          by (metis G_parser_cmd(1) G_command.cases G_command_parse_run(1) G_parser.intros(3)
              append.assoc append_Nil parse_run_append)
      next 
        assume "\<exists>tos' tdb' db DB ts p. G_parser tos' tdb' \<and> G_db db DB
          \<and> ls = tos' @ [AT, STRING ts] @ db @ [STRING p] \<and> ls' = tdb' @ [(ts, DB)]
          \<and> parse_run INITIAL ls tdb' (TUPLE (ts, DB) p)"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(1)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      next
        assume "\<exists>tos' tdb' db DB tps T fs FS ts p. G_parser tos' tdb' \<and> G_db db DB
          \<and> G_relation tps T \<and> G_tuple fs FS
          \<and> ls = tos' @ [AT, STRING ts] @ db @ [STRING p] @ tps @ fs
          \<and> ls' = tdb' @ [(ts, UpdateWith p {} (\<lambda>x. x \<union> T \<union> {FS}) DB)]
          \<and> parse_run INITIAL ls tdb' (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> T \<union> {FS}) DB) p)"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(1)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      qed
  next
    case 2
      from G_parser_cmd(3) show ?case
      proof (elim disjE)
        assume assumption:"parse_run INITIAL ls ls' INITIAL"
        have l: "parse_run (TABLE tdb\<^sub>i) cmd [tdb\<^sub>i] INITIAL"
          using G_parser_cmd(1) by (auto simp add:G_command_parse_run G_command.simps)
        show ?case by (simp add:parse_run_append[OF l assumption,simplified])
      next
        assume "\<exists>tos' tdb' ts. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts]
          \<and> ls' = tdb' @ [(ts, Mapping.empty)]
          \<and> parse_run INITIAL ls tdb' (TABLE (ts, Mapping.empty))"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(2)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      next 
        assume "\<exists>tos' tdb' db DB ts p. G_parser tos' tdb' \<and> G_db db DB
          \<and> ls = tos' @ [AT, STRING ts] @ db @ [STRING p] \<and> ls' = tdb' @ [(ts, DB)]
          \<and> parse_run INITIAL ls tdb' (TUPLE (ts, DB) p)"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(2)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      next
        assume "\<exists>tos' tdb' db DB tps T fs FS ts p. G_parser tos' tdb' \<and> G_db db DB
          \<and> G_relation tps T \<and> G_tuple fs FS
          \<and> ls = tos' @ [AT, STRING ts] @ db @ [STRING p] @ tps @ fs
          \<and> ls' = tdb' @ [(ts, UpdateWith p {} (\<lambda>x. x \<union> T \<union> {FS}) DB)]
          \<and> parse_run INITIAL ls tdb' (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> T \<union> {FS}) DB) p)"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(2)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      qed
  next
    case 3
      from G_parser_cmd(3) show ?case
      proof (elim disjE)
        assume assumption:"parse_run INITIAL ls ls' INITIAL"
        have l: "parse_run (TUPLE tdb\<^sub>i p\<^sub>i) cmd [tdb\<^sub>i] INITIAL"
          using G_parser_cmd(1) by (auto simp add:G_command_parse_run G_command.simps)
        show ?case by (simp add:parse_run_append[OF l assumption,simplified])
      next
        assume "\<exists>tos' tdb' ts. G_parser tos' tdb' \<and> ls = tos' @ [AT, STRING ts]
          \<and> ls' = tdb' @ [(ts, Mapping.empty)]
          \<and> parse_run INITIAL ls tdb' (TABLE (ts, Mapping.empty))"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(3)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      next 
        assume "\<exists>tos' tdb' db DB ts p. G_parser tos' tdb' \<and> G_db db DB
          \<and> ls = tos' @ [AT, STRING ts] @ db @ [STRING p] \<and> ls' = tdb' @ [(ts, DB)]
          \<and> parse_run INITIAL ls tdb' (TUPLE (ts, DB) p)"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(3)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      next
        assume "\<exists>tos' tdb' db DB tps T fs FS ts p. G_parser tos' tdb' \<and> G_db db DB
          \<and> G_relation tps T \<and> G_tuple fs FS
          \<and> ls = tos' @ [AT, STRING ts] @ db @ [STRING p] @ tps @ fs
          \<and> ls' = tdb' @ [(ts, UpdateWith p {} (\<lambda>x. x \<union> T \<union> {FS}) DB)]
          \<and> parse_run INITIAL ls tdb' (TUPLE (ts, UpdateWith p {} (\<lambda>x. x \<union> T \<union> {FS}) DB) p)"
        then show ?case
          by (smt (verit, ccfv_threshold) G_parser_cmd(1) G_command.cases G_command_parse_run(3)
              G_parser.intros(3) append.assoc append_self_conv2 parse_run_append)
      qed
  }
qed


(*-EXAMPLES--------------------------------------------------------------------------------------*)
value "ParseString ''@1234 p (\"abc\", \"def\") (\"1\", \"2\") q (\"3\") p (\"hello\", \"world\")''"

value "ParseString ''@1307532861 mgr_S (Mallory,Alice)
            mgr_S (Merlin,Bob)
            mgr_S (Merlin,Charlie)
@1307532861 approve (Mallory,152)
@1307955600 approve (Merlin,163)
            publish (Alice,160)
            mgr_F (Merlin,Charlie)
@1308477599 approve (Merlin,187)
            publish (Bob,163) (Alice,163) (Charlie,163) (Charlie,152)
''"


end