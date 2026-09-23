theory MFODL_Parser
  imports MFODL_Lexer MFODL_Post "HOL-Library.Code_Target_Int"
begin

section \<open>The verified parser\<close>

text \<open>
  \<^theory_text>\<open>parser\<close> generates an LALR(1) parser for \<^const>\<open>mfodl\<close> with the
  theorems \<open>mfodl_parse.sound\<close> and \<open>mfodl_parse.complete\<close> relating it to the
  inductive relation \<open>mfodl_Formula\<close> of the start symbol: the parser returns
  \<open>Some \<phi>\<close> on a token word \<open>w\<close> iff \<open>w\<close> derives \<open>\<phi>\<close> in the grammar. That
  there is at most one such \<open>\<phi>\<close> follows, since the parser is a function.
\<close>

parser mfodl_parse for mfodl

thm mfodl_parse.sound mfodl_parse.complete

corollary mfodl_parse_iff: \<open>mfodl_parse w = Some \<phi> \<longleftrightarrow> mfodl_Formula w \<phi>\<close>
  using mfodl_parse.sound mfodl_parse.complete by blast

corollary mfodl_Formula_unique: \<open>mfodl_Formula w \<phi> \<Longrightarrow> mfodl_Formula w \<psi> \<Longrightarrow> \<phi> = \<psi>\<close>
  by (metis mfodl_parse_iff option.inject)

text \<open>The complete pipeline: lexing, parsing and post-processing.\<close>

definition parse_formula :: \<open>string \<Rightarrow> formula option\<close> where
  \<open>parse_formula s = (case lex s of
     None \<Rightarrow> None
   | Some w \<Rightarrow> Option.bind (mfodl_parse w) postprocess)\<close>

lemma parse_formula_Some_iff:
  \<open>parse_formula s = Some \<phi> \<longleftrightarrow>
     (\<exists>w \<psi>. lex s = Some w \<and> mfodl_Formula w \<psi> \<and> postprocess \<psi> = Some \<phi>)\<close>
  by (auto simp: parse_formula_def mfodl_parse_iff split: option.splits)


section \<open>Examples\<close>

text \<open>Binary operators: \<open>AND\<close> binds tighter than \<open>OR\<close>, both tighter than \<open>SINCE\<close>,
  which is right associative.\<close>

lemma \<open>parse_formula ''P(x) OR Q(x) AND R(x) SINCE S(x) SINCE [0,5] T(x)'' = Some
  (FSince dfintv (FOr (FPred (''P'', [TVar ''x''])) (FAnd (FPred (''Q'', [TVar ''x''])) (FPred (''R'', [TVar ''x'']))))
    (FSince (CBnd 0, CBnd 5) (FPred (''S'', [TVar ''x''])) (FPred (''T'', [TVar ''x'']))))\<close>
  by eval

text \<open>A unary temporal operator absorbs the Boolean connectives to its right but not
  a binary temporal operator; \<open>NOT\<close> binds tightest.\<close>

lemma \<open>parse_formula ''PREV P(x) AND NOT Q(x) SINCE R(x)'' = Some
  (FSince dfintv (FPrev dfintv (FAnd (FPred (''P'', [TVar ''x''])) (FNeg (FPred (''Q'', [TVar ''x''])))))
    (FPred (''R'', [TVar ''x''])))\<close>
  by eval

text \<open>\<open>LET\<close> absorbs everything, also as the right operand of \<open>AND\<close>.\<close>

lemma \<open>parse_formula ''A() AND LET P(x) = Q(x) IN P(x) SINCE B()'' = Some
  (FAnd (FPred (''A'', []))
    (FLet (''P'', [TVar ''x'']) (FPred (''Q'', [TVar ''x'']))
      (FSince dfintv (FPred (''P'', [TVar ''x''])) (FPred (''B'', [])))))\<close>
  by eval

text \<open>Terms, intervals in time units, \<open>>\<close> as flipped \<open><\<close>.\<close>

lemma \<open>parse_formula ''ONCE (1m, 2h] x > -y * 2 + 1'' = Some
  (FOnce (OBnd 60, CBnd 7200)
    (FLess (TPlus (TMult (TUMinus (TVar ''y'')) (TCst (CInt 2))) (TCst (CInt 1))) (TVar ''x'')))\<close>
  by eval

text \<open>Anonymous arguments are numbered and existentially quantified.\<close>

lemma \<open>parse_formula ''P(_, x) OR Q(_)'' = Some
  (FOr (FExists [''_1''] (FPred (''P'', [TVar ''_1'', TVar ''x''])))
    (FExists [''_2''] (FPred (''Q'', [TVar ''_2''])))))\<close>
  by eval

text \<open>Aggregations: the aggregated variable must be free in the body.\<close>

lemma \<open>parse_formula ''s <- SUM x; g P(g, x)'' = Some
  (FAggreg ''s'' ASum ''x'' [''g''] (FPred (''P'', [TVar ''g'', TVar ''x''])))\<close>
  by eval

lemma \<open>parse_formula ''s <- SUM x; g P(g)'' = None\<close>
  by eval

text \<open>Regular expressions: a bare atom is a test followed by a step (\<open>MATCHF\<close>).\<close>

lemma \<open>parse_formula ''MATCHF [0,5] P(x) Q(x)? + .*'' = Some
  (FFrex (CBnd 0, CBnd 5)
    (RPlus (RConcat (RConcat (RTest (FPred (''P'', [TVar ''x'']))) wild) (RTest (FPred (''Q'', [TVar ''x'']))))
      (RStar wild)))\<close>
  by eval

text \<open>Comments, synonyms of keywords, and syntax errors.\<close>

lemma \<open>parse_formula ''SOMETIMES (* a comment *) P() # another'' = Some (FEventually dfintv (FPred (''P'', [])))\<close>
  by eval

lemma \<open>parse_formula ''P(x) AND'' = None\<close> and \<open>parse_formula ''P(x) Q(x)'' = None\<close>
  by eval+


section \<open>Code export\<close>

text \<open>Entry points on native strings for \<^verbatim>\<open>src/verified_parser_adapter.ml\<close>.\<close>

definition parse_formula_literal :: \<open>String.literal \<Rightarrow> formula option\<close> where
  \<open>parse_formula_literal s = parse_formula (String.explode s)\<close>

definition lex_literal :: \<open>String.literal \<Rightarrow> (mtok \<times> String.literal) list option\<close> where
  \<open>lex_literal s = map_option (map (\<lambda>t. (tok t, String.implode (lexeme t)))) (lex (String.explode s))\<close>

export_code parse_formula_literal lex_literal String.implode integer_of_int integer_of_nat nat_of_integer
  in OCaml module_name Verified_parser file_prefix "verified_parser"

end
