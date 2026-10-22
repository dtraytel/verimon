theory MFODL_Parser
  imports MFODL_Lexer "MFODL_Syntax.Surface_Postprocessing"
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
  unfolding parse_formula_def
  by (auto simp: bind_eq_Some_conv mfodl_parse_iff split: option.splits)


end
