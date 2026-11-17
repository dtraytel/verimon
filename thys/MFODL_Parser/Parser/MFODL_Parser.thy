theory MFODL_Parser
  imports MFODL_Lexer "MFODL_Syntax.Surface_Postprocessing"
begin

section \<open>Verified parser of formulas\<close>

text \<open>\<^theory_text>\<open>parser\<close> generates an LALR(1) parser for \<^const>\<open>mfodl\<close> restricted by its
  precedence declarations, sound and complete for the parse trees of its start symbol that satisfy
  them.\<close>

text \<open>The lexer package imports \<open>Code_Target_Nat\<close>, where \<open>0\<close> is no constructor, so the
  equations of \<^const>\<open>path_bfs\<close>, which the \<^theory_text>\<open>parser\<close> command evaluates, need the
  form that TIGER gives \<open>lreach\<close> and \<open>rlevel\<close>:\<close>

lemma path_bfs_code [code]:
  \<open>path_bfs succ tgt n seen wk = (if n = 0 then None else case wk of
     [] \<Rightarrow> None
   | (i, p) # wk' \<Rightarrow>
       if i = tgt then Some (rev p)
       else (let succs = fold (\<lambda>(X, j) acc.
               if j \<in> set seen \<or> j \<in> set (map fst wk') \<or> j \<in> set (map fst acc) then acc
               else acc @ [(j, X # p)]) (succ i) []
         in path_bfs succ tgt (n - 1) (i # seen) (wk' @ succs)))\<close>
  by (induction succ tgt n seen wk rule: path_bfs.induct) (simp_all add: Let_def)

text \<open>With evaluated tables, VeriMon's exported code holds the parser's tables as static
  data instead of computing them when it loads. VeriMon reports a rejected formula itself, so the
  parser comes without the diagnostic parser.\<close>

declare [[parser_literal_tables]]
parser (no_diagnostics) mfodl_parse for mfodl
declare [[parser_literal_tables = false]]

thm mfodl_parse.sound mfodl_parse.complete

text \<open>The meaning of the grammar: \<open>w\<close> derives the formula \<open>\<phi>\<close> if a parse tree of the start
  symbol yields \<open>w\<close>, satisfies the precedence declarations and has the value \<open>\<phi>\<close> by the
  semantic actions.\<close>

definition mfodl_Formula :: \<open>mtoken list \<Rightarrow> formula \<Rightarrow> bool\<close> where
  \<open>mfodl_Formula w \<phi> \<longleftrightarrow> (\<exists>pt. wf_ptree mfodl pt \<and>
     proot pt = (Nt (istart mfodl), istart_ind mfodl) \<and> pyield pt = w \<and>
     prec_ok mfodl mfodl_parse_prec pt \<and> mfodl__dec_Formula (erase pt) = Some \<phi>)\<close>

corollary mfodl_parse_iff: \<open>mfodl_parse w = Some \<phi> \<longleftrightarrow> mfodl_Formula w \<phi>\<close>
  unfolding mfodl_Formula_def using mfodl_parse.sound mfodl_parse.complete by blast

corollary mfodl_Formula_unique: \<open>mfodl_Formula w \<phi> \<Longrightarrow> mfodl_Formula w \<psi> \<Longrightarrow> \<phi> = \<psi>\<close>
  by (metis mfodl_parse_iff option.inject)

definition parse_formula :: \<open>string \<Rightarrow> formula option\<close> where
  \<open>parse_formula s = (case lex s of
     None \<Rightarrow> None
   | Some w \<Rightarrow> Option.bind (mfodl_parse w) postprocess)\<close>

lemma parse_formula_Some_iff:
  \<open>parse_formula s = Some \<phi> \<longleftrightarrow>
     (\<exists>w \<psi>. lex s = Some w \<and> mfodl_Formula w \<psi> \<and> postprocess \<psi> = Some \<phi>)\<close>
  unfolding parse_formula_def
  by (auto simp: bind_eq_Some_conv mfodl_parse_iff split: option.splits)


end
