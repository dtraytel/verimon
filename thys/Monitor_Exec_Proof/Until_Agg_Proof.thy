(*<*)
theory Until_Agg_Proof
  imports "Monitor_Exec.Until_Agg" Since_Agg_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>It tracks the plain window\<close>

text \<open>The fused operations differ from @{const uw_extend}, @{const uw_step} and
  @{const uw_shift} only in the extra component and in what is pushed onto the list of finished
  answers.  The first lemmas say so: everything but that list steps identically.\<close>

text \<open>And the aggregate it carries stays valid for the union it is kept against: the scan's
  insertions are exactly @{const cnt_add}'s, so @{thm [source] ag_inv_ins} applies at each of
  them.  This mirrors @{thm [source] sa_move_rep} for the Since window's scan.\<close>

text \<open>The two recursions in step, and the shift that drives them, keep the relation.\<close>

text \<open>What the plain window's validity gives about the tables it holds, in the form
  @{thm [source] ag_inv_ins} and @{thm [source] ag_inv_del} want them.\<close>

text \<open>The step needs only what @{thm [source] valid_uw_tables} extracts, not the whole of
  @{const valid_uw}: the shift below applies it to states whose queue of pending time stamps has
  already had its head taken off.\<close>

text \<open>The two entry points.  Both shift first, and the relation is preserved by everything they
  do afterwards: appending to the queues touches neither the count set, nor the aggregate, nor
  the finished answers, and handing the answers over reverses a list the relation maps
  pointwise.\<close>

lemma uuwm_init_ucc: "uw_init args = uuwm (uuwm_init args)"
  by (simp add: uw_init_def uuwm_init_def uuwm.simps ucc.simps)

lemma rua_init: "rua (uua_init args p) = ua_init args p"
  by (simp add: rua.simps uua_init_def ua_init_def uuwm_init_ucc)

(*<*)
end
(*>*)
