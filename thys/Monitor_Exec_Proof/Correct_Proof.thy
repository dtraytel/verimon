(*<*)
theory Correct_Proof
  imports "Monitor_Exec.Correct" IEval_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



section \<open>The executable monitor inherits the kernel's correctness theorems\<close>

subsection \<open>The concrete monitor is a @{locale verimon}\<close>

sublocale verimon_spec \<subseteq> dmon: verimon \<phi> SIG ENV
  valid_mmasaux "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux
    add_new_table_mmasaux result_mmasaux
  valid_muaux_dq "init_muaux_dq :: _ \<Rightarrow> muaux_dq" add_new_muaux_dq length_muaux_dq eval_muaux_dq
  valid_mmtaux init_mmtaux update_mmtaux result_mmtaux bin_join mmulti_join
  by unfold_locales (simp_all del: bin_join.simps mmulti_join.simps add: bin_join_table mmulti_join_correct)


text \<open>The indices a state keeps do not change what it computes: two states that agree once their
  indices are forgotten (@{text eforget}) give the same verdicts at every step, and agree again
  after it.  So the indices can be chosen when the monitor starts (@{text eindex}).\<close>

definition eforget :: "emstate \<Rightarrow> nat \<times> nat \<times> eformula \<times> nat \<times> cols \<times> ts mbuf_t" where
  "eforget st = (emstate_i st, emstate_j st, eabs (emstate_m st), emstate_n st, emstate_cs st,
     emstate_t st)"

lemma eforget_eindex[simp]: "eforget (eindex ix st) = eforget st"
  by (simp add: eforget_def eindex_def)

lemma eabs_eindex[simp]: "eabs (emstate_m (eindex ix st)) = eabs (emstate_m st)"
  by (simp add: eindex_def)

lemma emstep_eforget:
  assumes "eforget s1 = eforget s2"
  shows "fst (emstep tdb s1) = fst (emstep tdb s2) \<and>
    eforget (snd (emstep tdb s1)) = eforget (snd (emstep tdb s2))"
proof -
  obtain xs1 m1 where e1: "ieval [] (emstate_j s1 + 1) [snd tdb] (demb (fst tdb)) (emstate_m s1) = (xs1, m1)"
    by fastforce
  obtain xs2 m2 where e2: "ieval [] (emstate_j s2 + 1) [snd tdb] (demb (fst tdb)) (emstate_m s2) = (xs2, m2)"
    by fastforce
  have "map iset xs1 = map iset xs2 \<and> eabs m1 = eabs m2"
    using ieval_eeval[OF e1] ieval_eeval[OF e2] assms by (simp add: eforget_def)
  then show ?thesis
    using assms by (simp only: emstep_def e1 e2 prod.case) (auto simp: eforget_def split: prod.splits)
qed

lemma emsteps0_stateless_eforget:
  "eforget s1 = eforget s2 \<Longrightarrow> emsteps0_stateless \<pi> s1 = emsteps0_stateless \<pi> s2"
proof (induct \<pi> arbitrary: s1 s2)
  case (Cons tdb \<pi>)
  note e = emstep_eforget[OF Cons(2), of "apfst mk_db tdb"]
  show ?case
    using e Cons(1)[OF conjunct2[OF e]]
    by (simp add: Let_def split: prod.splits) (metis fst_conv snd_conv)
qed simp

lemma emonitor_eindex[simp]: "emonitor (eindex ix st) \<pi> = emonitor st \<pi>"
  unfolding emonitor_def emsteps_stateless.rep_eq by (rule emsteps0_stateless_eforget) simp


subsection \<open>The state relation\<close>

text \<open>
  Two states are related when their bookkeeping agrees and their formulas are related by
  @{const esim} at the column lists @{term ks} (the kernel's) and @{term cs} (the executable one the
  state records), with the timestamp bound of @{const esim} being the last timestamp the two have
  been fed.
\<close>

subsection \<open>One step\<close>

subsection \<open>The whole prefix\<close>

text \<open>
  The timestamp bound of @{const esim} is the last timestamp of the prefix read so far: each step
  re-establishes it at the timestamp just consumed, and the prefix's own sortedness says the next
  one is no smaller.  That is where the timestamp hypothesis of @{thm [source] esim_deval} is
  discharged, once and for all.  The kernel's invariant @{const kwf_mstate} threads through alongside: it
  makes every step a good call (@{thm [source] kgood_mstep}).
\<close>

subsection \<open>The verdicts are the narrowing of the kernel's\<close>

subsection \<open>The correctness theorems, transferred\<close>

text \<open>
  Nothing about the executable representation is left in these statements: they are the kernel's own
  collected results with @{const emonitor} in place of the kernel's monitor and the verdict
  tables widened back.  The simulation is what carries them across, and the only thing it asks of
  the caller is a related initial state.
\<close>

context verimon_spec
begin

text \<open>Widening the verdicts back recovers the kernel's exactly, because @{const etabc} is a
  bijection on the tables of the frame (@{thm [source] etabw_dtabc}) and the kernel's verdict
  tables live there.\<close>

text \<open>
  Nothing about the executable representation is left in these statements: they are the kernel's own
  collected results with @{const emonitor} in place of the kernel's monitor and the verdict
  tables widened back.  The simulation is what carries them across, and the only thing it asks of
  the caller is a related initial state.
\<close>

theorem emstep_mverdicts:
  assumes r: "emsim_state n (Formula.fv_list \<phi>) cs (last_ts \<pi>) st dst"
    and wf: "dmon.wf_mstate SIG ENV \<phi> \<pi> R st"
    and wtydb: "wty_db SIG (fst tdb)" and fin: "finite (fst tdb)"
    and le: "last_ts \<pi> \<le> snd tdb"
    and restrict: "mem_restr R (Formula.fv_list \<phi>) v"
  shows "(i, t, v) \<in> flatten_verdicts (map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) cs X))
        (fst (emstep (apfst mk_db tdb) dst)))
     \<longleftrightarrow> (i, t, v) \<in> Mt (psnoc \<pi> tdb) - Mt \<pi>"
proof -
  have tle': "last_ts \<pi> \<le> snd (apfst mk_db tdb)" using le by simp
  have mn: "mstate_n st = n" using r by (simp add: emsim_state_def)
  have kg: "kgood n (Formula.fv_list \<phi>) (mstate_j st + 1) [snd (apfst mk_db tdb)] (fst (apfst mk_db tdb))
      (mstate_m st)"
    using kgood_mstep[OF wf wtydb le fin] mn by simp
  have step: "fst (emstep (apfst mk_db tdb) dst)
      = map (\<lambda>(i, t, X). (i, t, etabc (Formula.fv_list \<phi>) cs X)) (fst (mstep (apfst mk_db tdb) st))"
    and tb: "\<forall>(i, t, X) \<in> set (fst (mstep (apfst mk_db tdb) st)). table (Formula.fv_list \<phi>) X"
    using emstep_mstep[OF r tle' kg] by simp_all
  have "map (\<lambda>(i, t, X). (i, t, etabw (Formula.fv_list \<phi>) cs X)) (fst (emstep (apfst mk_db tdb) dst))
      = fst (mstep (apfst mk_db tdb) st)"
    unfolding step by (rule map_etabw_etabc[OF emsim_state_dframe[OF r] tb])
  then show ?thesis
    unfolding Monitor_Impl.mstep_def
    using dmon.mstep_mverdicts[OF wf wtydb le restrict fin] by simp
qed

end

(*<*)
end
(*>*)
