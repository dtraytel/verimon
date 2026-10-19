(*<*)
theory Kernel_Call
  imports "MFODL_Monitor_Devel.Monitor_Impl" "MFODL_Monitor_Devel.Correctness"
begin
(*>*)

section \<open>The kernel's correctness for the concrete instance\<close>

text \<open>
  The interpretation @{text default_maux} precedes the kernel's correctness proof, so it does not
  carry its facts, and a second interpretation with the same parameters would be subsumed by it.
  We instantiate the facts we need with @{thm [source] default_maux.maux_axioms} instead.
\<close>

abbreviation "kwf_mformula \<equiv> maux.wf_mformula valid_mmasaux valid_muaux_dq length_muaux_dq
  (valid_mmtaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmtaux \<Rightarrow> _)"
abbreviation "kwf_mstate \<equiv> maux.wf_mstate valid_mmasaux valid_muaux_dq length_muaux_dq
  (valid_mmtaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmtaux \<Rightarrow> _)"
abbreviation "kletpast_meval_invar \<equiv> maux.letpast_meval_invar valid_mmasaux valid_muaux_dq
  length_muaux_dq (valid_mmtaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmtaux \<Rightarrow> _)"
abbreviation "kletpast_meval_post \<equiv> maux.letpast_meval_post valid_mmasaux valid_muaux_dq
  length_muaux_dq (valid_mmtaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmtaux \<Rightarrow> _)"

lemmas kmaux_meval_correct = maux.meval_correct[OF default_maux.maux_axioms, folded meval_def]
lemmas kmaux_wf_mformula_cases = maux.wf_mformula.cases[OF default_maux.maux_axioms, consumes 1,
  case_names Eq Pred Let Frz LetPast And AndAssign AndRel And_Trigger And_Release Ands Or Neg Exists
    Agg Prev Next Since Until Trigger_0 Release MatchP MatchF MTP MTS]
lemmas kmaux_wf_minit0 = maux.wf_minit0[OF default_maux.maux_axioms, folded minit0_def]
lemmas kmaux_wf_mstate_def = maux.wf_mstate_def[OF default_maux.maux_axioms]
lemmas kmaux_wf_mstate_minit_safe =
  maux.wf_mstate_minit_safe[OF default_maux.maux_axioms, folded minit_safe_def]
lemmas kmaux_wf_mstate_mstep = maux.wf_mstate_mstep[OF default_maux.maux_axioms, folded mstep_def]
lemmas kmaux_letpast_meval_invar_def = maux.letpast_meval_invar_def[OF default_maux.maux_axioms]
lemmas kmaux_letpast_meval_invar_init = maux.letpast_meval_invar_init[OF default_maux.maux_axioms]
lemmas kmaux_letpast_meval_invar_post =
  maux.letpast_meval_invar_post[OF default_maux.maux_axioms, folded meval_def letpast_meval_def]
lemmas kmaux_letpast_meval_post_def = maux.letpast_meval_post_def[OF default_maux.maux_axioms]
lemmas kmaux_invar_recursion_invar =
  maux.invar_recursion_invar[OF default_maux.maux_axioms, folded meval_def]
lemmas kmaux_frz_qtable_def = maux.frz_qtable_def[OF default_maux.maux_axioms]
lemmas kmaux_qtable_frz_alpha = maux.qtable_frz_alpha[OF default_maux.maux_axioms]
lemmas kmaux_wf_envs_update3 = maux.wf_envs_update3[OF default_maux.maux_axioms]
lemmas kmaux_wf_envs_update_frz = maux.wf_envs_update_frz[OF default_maux.maux_axioms]
lemmas kmaux_wf_frz_queue_def = maux.wf_frz_queue_def[OF default_maux.maux_axioms]
lemmas kmaux_wf_frz_queue_append = maux.wf_frz_queue_append[OF default_maux.maux_axioms]
lemmas kmaux_wf_frz_queue_drop = maux.wf_frz_queue_drop[OF default_maux.maux_axioms]
lemmas kmaux_wf_frz_state_def = maux.wf_frz_state_def[OF default_maux.maux_axioms]
lemmas kmaux_wf_frz_win_def = maux.wf_frz_win_def[OF default_maux.maux_axioms]

section \<open>The calls the kernel's invariant covers\<close>

text \<open>
  The executable evaluator's operations need their operand tables to be finite and well formed
  over the node's columns.  The kernel's correctness theorem @{thm [source] kmaux_meval_correct}
  provides exactly that for the tables a well-formed state yields on a database of the trace:
  its tables are @{const qtable}s, which are finite.  A call of @{const meval} is \<^emph>\<open>good\<close> when it
  is one of those -- a well-formed state of a well-typed formula, a database that agrees with the
  trace and the environments, and the trace's time-stamps -- and the column list it is
  simulated at is the formula's own.
\<close>

definition kgood :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  "kgood n ks j ts db \<phi> \<longleftrightarrow> (\<exists>S E \<sigma> j0 P P' V R \<psi>. j0 \<le> j \<and> ts = map (\<tau> \<sigma>) [j0..<j] \<and>
     kwf_mformula \<sigma> j0 P V n R \<phi> \<psi> \<and> wf_envs S \<sigma> j0 (j - j0) P P' V db \<and>
     S, E \<turnstile> \<psi> \<and> ks = Formula.fv_list \<psi>)"

lemma kgoodI:
  "j0 \<le> j \<Longrightarrow> ts = map (\<tau> \<sigma>) [j0..<j] \<Longrightarrow> kwf_mformula \<sigma> j0 P V n R \<phi> \<psi> \<Longrightarrow>
   wf_envs S \<sigma> j0 (j - j0) P P' V db \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> ks = Formula.fv_list \<psi> \<Longrightarrow>
   kgood n ks j ts db \<phi>"
  unfolding kgood_def by blast

lemma kgoodE:
  assumes "kgood n ks j ts db \<phi>"
  obtains S E \<sigma> j0 P P' V R \<psi> where "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    "kwf_mformula \<sigma> j0 P V n R \<phi> \<psi>" "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    "S, E \<turnstile> \<psi>" "ks = Formula.fv_list \<psi>"
  using assms unfolding kgood_def by blast

text \<open>A call on an operand is good when every well-formed, well-typed kernel formula the node can
  stand for gives the operand one, in the same environments and on the same database.\<close>

lemma kgood_sub:
  assumes "kgood n ks j ts db \<phi>"
    and "\<And>\<sigma> j0 P V R \<chi> S E. kwf_mformula \<sigma> j0 P V n R \<phi> \<chi> \<Longrightarrow> S, E \<turnstile> \<chi> \<Longrightarrow>
      ks = Formula.fv_list \<chi> \<Longrightarrow>
      \<exists>R' E' \<psi>. kwf_mformula \<sigma> j0 P V n' R' \<phi>' \<psi> \<and> S, E' \<turnstile> \<psi> \<and> ks' = Formula.fv_list \<psi>"
  shows "kgood n' ks' j ts db \<phi>'"
  using assms(1) by (rule kgoodE) (use assms(2) in \<open>blast intro: kgoodI\<close>)

text \<open>A good call's tables are finite tables over its columns.\<close>

lemma kgood_tables:
  assumes g: "kgood n ks j ts db \<phi>" and e: "meval j n ts db \<phi> = (xs, \<phi>')"
  shows "list_all (\<lambda>X. table ks X \<and> finite X) xs"
proof -
  obtain S E \<sigma> j0 P P' V R \<psi> where j0: "j0 \<le> j" and ts: "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R \<phi> \<psi>" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wty: "S, E \<turnstile> \<psi>" and ks: "ks = Formula.fv_list \<psi>"
    using g by (rule kgoodE)
  have "case meval (j0 + (j - j0)) n (map (\<tau> \<sigma>) [j0..<j0 + (j - j0)]) db \<phi> of (xs, \<phi>\<^sub>n) \<Rightarrow>
      kwf_mformula \<sigma> (j0 + (j - j0)) P' V n R \<phi>\<^sub>n \<psi> \<and>
      list_all2 (\<lambda>i. sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi>)
        [progress \<sigma> P \<psi> j0..<progress \<sigma> P' \<psi> (j0 + (j - j0))] xs"
    by (rule kmaux_meval_correct[OF wf envs wty])
  then have "list_all2 (\<lambda>i. sat_table \<sigma> V n R ks i \<psi>)
      [progress \<sigma> P \<psi> j0..<progress \<sigma> P' \<psi> j] xs"
    using j0 e unfolding ts ks by simp
  then show ?thesis
    by (auto simp: list_all2_conv_all_nth list_all_length dest: qtableD(1,5))
qed

lemma kgood_sorted: "kgood n ks j ts db \<phi> \<Longrightarrow> sorted ts"
  by (erule kgoodE) (auto simp: sorted_map intro: sorted_wrt_mono_rel[OF _ sorted_upt])


subsection \<open>The operands of a good call are good\<close>

text \<open>The operands are evaluated in the same environments and on the same database, except
  under a binder; the column lists the node records for them are their formulas' own.\<close>

lemma kgood_MAndRel:
  assumes "kgood n ks j ts db (MAndRel ks \<phi> conf)"
  shows "kgood n ks j ts db \<phi>"
  using assms by (rule kgood_sub) (erule kmaux_wf_mformula_cases, auto dest: wty_formula_AndD)

lemma kgood_MNeg:
  assumes "kgood n ks j ts db (MNeg \<phi>)"
  shows "kgood n [] j ts db \<phi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MNeg \<phi>) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 where \<chi>: "\<chi> = Formula.Neg \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V n R \<phi> \<phi>1" and fv: "Formula.fv \<phi>1 = {}"
    by (cases rule: kmaux_wf_mformula_cases) auto
  from fv have fvl: "[] = Formula.fv_list \<phi>1"
    using set_fvi_list[of 0 \<phi>1] by (simp del: set_fvi_list)
  from wty have "S, E \<turnstile> \<phi>1"
    unfolding \<chi> by (rule wty_formula_NegD)
  then show ?thesis
    by (rule kgoodI[OF g wf\<phi> envs _ fvl])
qed

lemma kgood_MExists:
  assumes "kgood n ks j ts db (MExists kks \<phi>)"
  shows "kgood (Suc n) kks j ts db \<phi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MExists kks \<phi>) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 t where \<chi>: "\<chi> = Formula.Exists t \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V (Suc n) (lift_envs R) \<phi> \<phi>1"
    and kks: "kks = Formula.fv_list \<phi>1"
    by (cases rule: kmaux_wf_mformula_cases) auto
  from wty obtain t' where "S, case_nat t' E \<turnstile> \<phi>1"
    unfolding \<chi> by (cases rule: wty_formula.cases) auto
  then show ?thesis
    by (rule kgoodI[OF g wf\<phi> envs _ kks])
qed

lemma kgood_MAnd:
  assumes "kgood n ks j ts db (MAnd k1 \<phi> pos k2 \<psi> buf)"
  shows "kgood n k1 j ts db \<phi>" "kgood n k2 j ts db \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MAnd k1 \<phi> pos k2 \<psi> buf) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 \<psi>1 where
    wf\<phi>: "kwf_mformula \<sigma> j0 P V n R \<phi> \<phi>1"
    and wf\<psi>: "kwf_mformula \<sigma> j0 P V n R \<psi> \<psi>1"
    and \<chi>: "\<chi> = Formula.And \<phi>1 (if pos then \<psi>1 else Formula.Neg \<psi>1)"
    and ks: "k1 = Formula.fv_list \<phi>1" "k2 = Formula.fv_list \<psi>1"
    by (cases rule: kmaux_wf_mformula_cases) (auto split: if_splits)
  from wty have "S, E \<turnstile> \<phi>1"
    unfolding \<chi> by (rule wty_formula_AndD(1))
  then show "kgood n k1 j ts db \<phi>"
    by (rule kgoodI[OF g wf\<phi> envs _ ks(1)])
  from wty_formula_AndD(2)[OF wty[unfolded \<chi>]] have "S, E \<turnstile> \<psi>1"
    by (cases pos) (auto dest: wty_formula_NegD)
  then show "kgood n k2 j ts db \<psi>"
    by (rule kgoodI[OF g wf\<psi> envs _ ks(2)])
qed

lemma kgood_MAndAssign:
  assumes "kgood n ks j ts db (MAndAssign k0 \<phi> conf)"
  shows "kgood n k0 j ts db \<phi>"
  using assms by (rule kgood_sub) (erule kmaux_wf_mformula_cases, auto dest: wty_formula_AndD)

lemma kgood_MPrev:
  assumes "kgood n ks j ts db (MPrev I \<phi> first buf nts)"
  shows "kgood n ks j ts db \<phi>"
  using assms by (rule kgood_sub) (erule kmaux_wf_mformula_cases, auto dest: wty_formula_PrevD)

lemma kgood_MNext:
  assumes "kgood n ks j ts db (MNext I \<phi> first nts)"
  shows "kgood n ks j ts db \<phi>"
  using assms by (rule kgood_sub) (erule kmaux_wf_mformula_cases, auto dest: wty_formula_NextD)

lemma kgood_MAgg:
  assumes "kgood n ks j ts db (MAgg args \<phi>)"
  shows "kgood (length (aggargs_tys args) + n) (aggargs_cols args) j ts db \<phi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MAgg args \<phi>) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 where
    \<chi>: "\<chi> = Formula.Agg (aggargs_y args) (aggargs_\<omega> args) (aggargs_tys args) (aggargs_f args) \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V (length (aggargs_tys args) + n)
      (lift_envs' (length (aggargs_tys args)) R) \<phi> \<phi>1"
    and cols: "aggargs_cols args = Formula.fv_list \<phi>1"
    by (cases rule: kmaux_wf_mformula_cases) auto
  from wty have "S, agg_env E (aggargs_tys args) \<turnstile> \<phi>1"
    unfolding \<chi> by (cases rule: wty_formula.cases) auto
  then show ?thesis
    by (rule kgoodI[OF g wf\<phi> envs _ cols])
qed

text \<open>A temporal node with an aggregation on top is typed in the aggregation's environment.\<close>

lemma wty_packagg_body:
  assumes "S, E \<turnstile> packagg args \<chi>"
  obtains E' where "S, E' \<turnstile> \<chi>"
proof (cases "args_agg args")
  case None
  with assms show ?thesis
    by (intro that) (simp add: packagg_def)
next
  case (Some aggargs)
  with assms have "S, E \<turnstile> Formula.Agg (aggargs_y aggargs) (aggargs_\<omega> aggargs)
      (aggargs_tys aggargs) (aggargs_f aggargs) \<chi>"
    by (simp add: packagg_def)
  then have "S, agg_env E (aggargs_tys aggargs) \<turnstile> \<chi>"
    by (cases rule: wty_formula.cases) auto
  then show ?thesis
    by (rule that)
qed

lemma kgood_MSince:
  assumes "kgood n ks j ts db (MSince args \<phi> \<psi> buf aux)"
  shows "kgood (args_n args) (args_L args) j ts db \<phi>" "kgood (args_n args) (args_R args) j ts db \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MSince args \<phi> \<psi> buf aux) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 \<phi>2 \<psi>1 I R' where \<chi>: "\<chi> = packagg args (Formula.Since \<phi>2 I \<psi>1)"
    and pos: "if args_pos args then \<phi>2 = \<phi>1 else \<phi>2 = Formula.Neg \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V (args_n args) R' \<phi> \<phi>1"
    and wf\<psi>: "kwf_mformula \<sigma> j0 P V (args_n args) R' \<psi> \<psi>1"
    and LR: "args_L args = Formula.fv_list \<phi>1" "args_R args = Formula.fv_list \<psi>1"
    by (cases rule: kmaux_wf_mformula_cases) auto
  obtain E' where wty_Since: "S, E' \<turnstile> Formula.Since \<phi>2 I \<psi>1"
    using wty unfolding \<chi> by (rule wty_packagg_body)
  from pos wty_formula_SinceD(1)[OF wty_Since] have "S, E' \<turnstile> \<phi>1"
    by (cases "args_pos args") (auto dest: wty_formula_NegD)
  then show "kgood (args_n args) (args_L args) j ts db \<phi>"
    by (rule kgoodI[OF g wf\<phi> envs _ LR(1)])
  from wty_Since have "S, E' \<turnstile> \<psi>1"
    by (rule wty_formula_SinceD(2))
  then show "kgood (args_n args) (args_R args) j ts db \<psi>"
    by (rule kgoodI[OF g wf\<psi> envs _ LR(2)])
qed

lemma kgood_MUntil:
  assumes "kgood n ks j ts db (MUntil args \<phi> \<psi> buf nts t aux)"
  shows "kgood (args_n args) (args_L args) j ts db \<phi>" "kgood (args_n args) (args_R args) j ts db \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MUntil args \<phi> \<psi> buf nts t aux) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 \<phi>2 \<psi>1 I R' where \<chi>: "\<chi> = packagg args (Formula.Until \<phi>2 I \<psi>1)"
    and pos: "if args_pos args then \<phi>2 = \<phi>1 else \<phi>2 = Formula.Neg \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V (args_n args) R' \<phi> \<phi>1"
    and wf\<psi>: "kwf_mformula \<sigma> j0 P V (args_n args) R' \<psi> \<psi>1"
    and LR: "args_L args = Formula.fv_list \<phi>1" "args_R args = Formula.fv_list \<psi>1"
    by (cases rule: kmaux_wf_mformula_cases) auto
  obtain E' where wty_Until: "S, E' \<turnstile> Formula.Until \<phi>2 I \<psi>1"
    using wty unfolding \<chi> by (rule wty_packagg_body)
  from pos wty_formula_UntilD(1)[OF wty_Until] have "S, E' \<turnstile> \<phi>1"
    by (cases "args_pos args") (auto dest: wty_formula_NegD)
  then show "kgood (args_n args) (args_L args) j ts db \<phi>"
    by (rule kgoodI[OF g wf\<phi> envs _ LR(1)])
  from wty_Until have "S, E' \<turnstile> \<psi>1"
    by (rule wty_formula_UntilD(2))
  then show "kgood (args_n args) (args_R args) j ts db \<psi>"
    by (rule kgoodI[OF g wf\<psi> envs _ LR(2)])
qed

lemma kgood_MTrigger:
  assumes "kgood n ks j ts db (MTrigger args \<phi> \<psi> buf nts aux)"
  shows "kgood n (args_L args) j ts db \<phi>" "kgood n (args_R args) j ts db \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MTrigger args \<phi> \<psi> buf nts aux) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<gamma> I \<alpha> \<beta> where \<chi>: "\<chi> = Formula.Trigger \<alpha> I \<beta>"
    and pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = Formula.Neg \<gamma>"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V n R \<phi> \<gamma>"
    and wf\<psi>: "kwf_mformula \<sigma> j0 P V n R \<psi> \<beta>"
    and LR: "args_L args = Formula.fv_list \<gamma>" "args_R args = Formula.fv_list \<beta>"
    by (cases rule: kmaux_wf_mformula_cases) auto
  have "S, E \<turnstile> \<gamma>" "S, E \<turnstile> \<beta>"
    using wty_formula_TriggerD[OF wty[unfolded \<chi>]] pos wty_formula_NegD[of S E \<gamma>]
    by (auto split: if_splits)
  then show "kgood n (args_L args) j ts db \<phi>" "kgood n (args_R args) j ts db \<psi>"
    by (auto intro: kgoodI[OF g wf\<phi> envs _ LR(1)] kgoodI[OF g wf\<psi> envs _ LR(2)])
qed

lemma kgood_MRelease:
  assumes "kgood n ks j ts db (MRelease args \<phi> \<psi> buf nts t aux)"
  shows "kgood n (args_L args) j ts db \<phi>" "kgood n (args_R args) j ts db \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MRelease args \<phi> \<psi> buf nts t aux) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<alpha> \<gamma> I \<beta> where \<chi>: "\<chi> = Formula.Release \<alpha> I \<beta>"
    and rl: "release_left \<alpha> \<beta> = (\<gamma>, args_pos args)"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V n R \<phi> \<gamma>"
    and wf\<psi>: "kwf_mformula \<sigma> j0 P V n R \<psi> \<beta>"
    and LR: "args_L args = Formula.fv_list \<gamma>" "args_R args = Formula.fv_list \<beta>"
    by (cases rule: kmaux_wf_mformula_cases) auto
  from wty have "S, E \<turnstile> \<alpha>" "S, E \<turnstile> \<beta>"
    unfolding \<chi> by (auto dest: wty_formulaD elim: wty_formula.cases)
  then have "S, E \<turnstile> \<gamma>" "S, E \<turnstile> \<beta>"
    using wty_release_left[OF rl] by auto
  then show "kgood n (args_L args) j ts db \<phi>" "kgood n (args_R args) j ts db \<psi>"
    by (auto intro: kgoodI[OF g wf\<phi> envs _ LR(1)] kgoodI[OF g wf\<psi> envs _ LR(2)])
qed

lemma kgood_MAndTrigger:
  assumes "kgood n ks j ts db (MAndTrigger k\<alpha> \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)"
  shows "kgood n k\<alpha> j ts db \<alpha>" "kgood n (args_L args) j ts db \<phi>" "kgood n (args_R args) j ts db \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MAndTrigger k\<alpha> \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<alpha>1 \<gamma> \<phi>1 I \<beta> where \<chi>: "\<chi> = Formula.And \<alpha>1 (Formula.Trigger \<phi>1 I \<beta>)"
    and pos: "if args_pos args then \<phi>1 = \<gamma> else \<phi>1 = Formula.Neg \<gamma>"
    and wf\<alpha>: "kwf_mformula \<sigma> j0 P V n R \<alpha> \<alpha>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V n R \<phi> \<gamma>"
    and wf\<psi>: "kwf_mformula \<sigma> j0 P V n R \<psi> \<beta>"
    and LR: "k\<alpha> = Formula.fv_list \<alpha>1" "args_L args = Formula.fv_list \<gamma>" "args_R args = Formula.fv_list \<beta>"
    by (cases rule: kmaux_wf_mformula_cases) auto
  have wty\<alpha>: "S, E \<turnstile> \<alpha>1" and wtyT: "S, E \<turnstile> Formula.Trigger \<phi>1 I \<beta>"
    using wty unfolding \<chi> by (auto dest: wty_formula_AndD)
  have "S, E \<turnstile> \<gamma>" "S, E \<turnstile> \<beta>"
    using wty_formula_TriggerD[OF wtyT] pos wty_formula_NegD[of S E \<gamma>] by (auto split: if_splits)
  with wty\<alpha> show "kgood n k\<alpha> j ts db \<alpha>" "kgood n (args_L args) j ts db \<phi>" "kgood n (args_R args) j ts db \<psi>"
    by (auto intro: kgoodI[OF g wf\<alpha> envs _ LR(1)] kgoodI[OF g wf\<phi> envs _ LR(2)]
        kgoodI[OF g wf\<psi> envs _ LR(3)])
qed


text \<open>A disjunction node also evaluates the rewriting of a conjunction with a release; in both
  shapes its operands are those of a disjunction of well-typed formulas.\<close>

lemma kgood_MOr:
  assumes "kgood n ks j ts db (MOr k1 \<phi> k2 \<psi> buf)"
  shows "kgood n k1 j ts db \<phi>" "kgood n k2 j ts db \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MOr k1 \<phi> k2 \<psi> buf) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms by (rule kgoodE)
  have "\<exists>a b. kwf_mformula \<sigma> j0 P V n R (MOr k1 \<phi> k2 \<psi> buf) (Formula.Or a b) \<and>
      S, E \<turnstile> a \<and> S, E \<turnstile> b"
    using wf
  proof (cases rule: kmaux_wf_mformula_cases)
    case Or
    with wf wty show ?thesis
      by (auto elim: wty_formula.cases)
  next
    case (And_Release I \<phi>1 \<psi>1 \<alpha>1)
    then have \<chi>: "\<chi> = formula.And \<alpha>1 (formula.Release \<phi>1 I \<psi>1)"
      and wfR: "kwf_mformula \<sigma> j0 P V n R (MOr k1 \<phi> k2 \<psi> buf) (and_release_safe_bounded \<alpha>1 \<phi>1 I \<psi>1)"
      by simp_all
    from wty have wty\<alpha>: "S, E \<turnstile> \<alpha>1" and wty\<phi>: "S, E \<turnstile> \<phi>1" and wty\<psi>: "S, E \<turnstile> \<psi>1"
      unfolding \<chi> by (auto dest: wty_formulaD)
    have "S, E \<turnstile> formula.And \<alpha>1 (formula.Neg (Formula.eventually I Formula.TT))"
      "S, E \<turnstile> formula.And \<alpha>1 (release_safe_bounded \<phi>1 I \<psi>1)"
      using wty\<alpha> wty\<phi> wty\<psi>
      by (auto simp: Formula.eventually_def release_safe_bounded_def
          always_safe_bounded_def once_def intro!: wty_formula.intros)
    with wfR show ?thesis
      by (auto simp: and_release_safe_bounded_def)
  qed simp_all
  then obtain a b where wfOr: "kwf_mformula \<sigma> j0 P V n R (MOr k1 \<phi> k2 \<psi> buf) (Formula.Or a b)"
    and wtya: "S, E \<turnstile> a" and wtyb: "S, E \<turnstile> b"
    by blast
  from wfOr have "kwf_mformula \<sigma> j0 P V n R \<phi> a \<and> kwf_mformula \<sigma> j0 P V n R \<psi> b \<and>
      k1 = Formula.fv_list a \<and> k2 = Formula.fv_list b"
    by (cases rule: kmaux_wf_mformula_cases) simp_all
  then have wf\<phi>: "kwf_mformula \<sigma> j0 P V n R \<phi> a" and wf\<psi>: "kwf_mformula \<sigma> j0 P V n R \<psi> b"
    and ks: "k1 = Formula.fv_list a" "k2 = Formula.fv_list b"
    by blast+
  show "kgood n k1 j ts db \<phi>" "kgood n k2 j ts db \<psi>"
    by (rule kgoodI[OF g wf\<phi> envs wtya ks(1)], rule kgoodI[OF g wf\<psi> envs wtyb ks(2)])
qed

lemma kgood_MAnds:
  assumes "kgood n ks j ts db (MAnds ks' kps kns L buf)" and i: "i < length L"
  shows "kgood n ((kps @ kns) ! i) j ts db (L ! i)"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MAnds ks' kps kns L buf) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms(1) by (rule kgoodE)
  from wf obtain pos neg l' where \<chi>: "\<chi> = Formula.Ands l'"
    and wfl: "list_all2 (kwf_mformula \<sigma> j0 P V n R) L (pos @ map remove_neg neg)"
    and posneg: "(pos, neg) = partition safe_formula l'"
    and A: "kps = map Formula.fv_list pos" "kns = map Formula.fv_list neg"
    by (cases rule: kmaux_wf_mformula_cases) auto
  let ?l = "pos @ map remove_neg neg"
  have len: "length L = length ?l"
    using wfl by (rule list_all2_lengthD)
  have wfi: "kwf_mformula \<sigma> j0 P V n R (L ! i) (?l ! i)"
    using wfl i by (simp add: list_all2_conv_all_nth)
  have wty_l': "\<forall>\<phi> \<in> set l'. S, E \<turnstile> \<phi>"
    using wty unfolding \<chi> by (cases rule: wty_formula.cases) auto
  have "set ?l \<subseteq> set l' \<union> remove_neg ` set l'"
    using posneg by auto
  moreover have "S, E \<turnstile> remove_neg \<phi>" if "S, E \<turnstile> \<phi>" for \<phi>
    using that by (cases \<phi>) (auto dest: wty_formula_NegD)
  ultimately have "S, E \<turnstile> ?l ! i"
    using wty_l' nth_mem[of i ?l] i len by auto
  moreover have "(kps @ kns) ! i = Formula.fv_list (?l ! i)"
    using i len by (simp add: A nth_append)
  ultimately show ?thesis
    by (intro kgoodI[OF g wfi envs]) simp_all
qed

lemma kgood_MMatchP:
  assumes "kgood n ks j ts db (MMatchP I ks' dss mr mrs L buf nts aux)" and i: "i < length L"
  shows "kgood n (dss ! i) j ts db (L ! i)"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MMatchP I ks' dss mr mrs L buf nts aux) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms(1) by (rule kgoodE)
  from wf obtain r \<psi>s where \<chi>: "\<chi> = Formula.MatchP I r" and mr: "to_mregex r = (mr, \<psi>s)"
    and \<psi>s: "list_all2 (kwf_mformula \<sigma> j0 P V n R) L \<psi>s"
    and dss: "dss = map Formula.fv_list \<psi>s"
    by (cases rule: kmaux_wf_mformula_cases) (auto split: prod.splits)
  have len: "length L = length \<psi>s"
    using \<psi>s by (rule list_all2_lengthD)
  have "S, E \<turnstile> \<psi>s ! i"
  proof -
    from wty have "Regex.pred_regex (wty_formula S E) r"
      unfolding \<chi> by (cases pred: wty_formula) simp_all
    moreover have "\<psi>s ! i \<in> safe_atms r"
      by (rule to_mregex_safe_atms[OF _ mr]) (use i len in simp)
    ultimately show ?thesis
      by (rule pred_regex_wty_formula)
  qed
  moreover have "kwf_mformula \<sigma> j0 P V n R (L ! i) (\<psi>s ! i)"
    using \<psi>s i by (simp add: list_all2_conv_all_nth)
  ultimately show ?thesis
    using i len by (intro kgoodI[OF g _ envs]) (simp_all add: dss)
qed

lemma kgood_MMatchF:
  assumes "kgood n ks j ts db (MMatchF I ks' dss mr mrs L buf nts t aux)" and i: "i < length L"
  shows "kgood n (dss ! i) j ts db (L ! i)"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MMatchF I ks' dss mr mrs L buf nts t aux) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    using assms(1) by (rule kgoodE)
  from wf obtain r \<psi>s where \<chi>: "\<chi> = Formula.MatchF I r" and mr: "to_mregex r = (mr, \<psi>s)"
    and \<psi>s: "list_all2 (kwf_mformula \<sigma> j0 P V n R) L \<psi>s"
    and dss: "dss = map Formula.fv_list \<psi>s"
    by (cases rule: kmaux_wf_mformula_cases) (auto split: prod.splits)
  have len: "length L = length \<psi>s"
    using \<psi>s by (rule list_all2_lengthD)
  have "S, E \<turnstile> \<psi>s ! i"
  proof -
    from wty have "Regex.pred_regex (wty_formula S E) r"
      unfolding \<chi> by (cases pred: wty_formula) simp_all
    moreover have "\<psi>s ! i \<in> safe_atms r"
      by (rule to_mregex_safe_atms[OF _ mr]) (use i len in simp)
    ultimately show ?thesis
      by (rule pred_regex_wty_formula)
  qed
  moreover have "kwf_mformula \<sigma> j0 P V n R (L ! i) (\<psi>s ! i)"
    using \<psi>s i by (simp add: list_all2_conv_all_nth)
  ultimately show ?thesis
    using i len by (intro kgoodI[OF g _ envs]) (simp_all add: dss)
qed

subsection \<open>Under a binder\<close>

text \<open>The body of a let is evaluated on the database the bound formula's tables extend, reordered
  to the positional columns -- which is what the kernel's own evaluation does.\<close>

lemma kgood_MLet:
  assumes g0: "kgood n ks j ts db (MLet p m kks \<phi> \<psi>)"
  shows "kgood m kks j ts db \<phi>"
    and "meval j m ts db \<phi> = (as, \<phi>2) \<Longrightarrow>
      kgood n ks j ts (Mapping.update (p, m) (map (reorder [0..<m] kks) as) db) \<psi>"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MLet p m kks \<phi> \<psi>) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>"
    and ks: "ks = Formula.fv_list \<chi>"
    using g0 by (rule kgoodE)
  from wf obtain \<phi>1 \<psi>1 where \<chi>: "\<chi> = Formula.Let p \<phi>1 \<psi>1"
    and wf1: "kwf_mformula \<sigma> j0 P V m UNIV \<phi> \<phi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> fv \<phi>1"
    and wf2: "kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> progress \<sigma> P \<phi>1 j0))
      (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>1)) n R \<psi> \<psi>1"
    and safe1: "safe_formula \<phi>1" and kks: "kks = Formula.fv_list \<phi>1"
    by (cases rule: kmaux_wf_mformula_cases) auto
  from wty obtain E' where wty1: "S, E' \<turnstile> \<phi>1"
    and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    unfolding \<chi> fv by (cases pred: wty_formula) simp_all
  show "kgood m kks j ts db \<phi>"
    by (rule kgoodI[OF g wf1 envs wty1 kks])
  assume e: "meval j m ts db \<phi> = (as, \<phi>2)"
  have "case meval (j0 + (j - j0)) m (map (\<tau> \<sigma>) [j0..<j0 + (j - j0)]) db \<phi> of (xs, \<phi>\<^sub>n) \<Rightarrow>
      kwf_mformula \<sigma> (j0 + (j - j0)) P' V m UNIV \<phi>\<^sub>n \<phi>1 \<and>
      list_all2 (\<lambda>i. sat_table \<sigma> V m UNIV (Formula.fv_list \<phi>1) i \<phi>1)
        [progress \<sigma> P \<phi>1 j0..<progress \<sigma> P' \<phi>1 (j0 + (j - j0))] xs"
    by (rule kmaux_meval_correct[OF wf1 envs wty1])
  then have res: "list_all2 (\<lambda>i. sat_table \<sigma> V m UNIV (Formula.fv_list \<phi>1) i \<phi>1)
      [progress \<sigma> P \<phi>1 j0..<progress \<sigma> P' \<phi>1 (j0 + (j - j0))] as"
    using g e by simp
  have res': "list_all2 (\<lambda>i. sat_table \<sigma> V m UNIV [0..<m] i \<phi>1)
      [progress \<sigma> P \<phi>1 j0..<progress \<sigma> P' \<phi>1 (j0 + (j - j0))] (map (reorder [0..<m] kks) as)"
    unfolding list.rel_map kks by (rule list.rel_mono_strong[OF res]) (rule sat_table_reorder_upt[OF _ fv(2,1)])
  show "kgood n ks j ts (Mapping.update (p, m) (map (reorder [0..<m] kks) as) db) \<psi>"
    by (rule kgoodI[OF g wf2 wf_envs_update[OF envs fv res' safe1 wty1] wty2]) (simp add: ks \<chi>)
qed


subsection \<open>The freeze's copies\<close>

text \<open>Two runs of the copy loop that evaluate related states on the same tables agree, as long as
  an invariant @{term K} of the first run's state, which the window's moves preserve, is what the
  copies need: unlike @{thm [source] frz_live_loop_rel}, the evaluation is only required to be
  related at the states the loop actually reaches.\<close>

lemma frz_loop_rel_inv:
  assumes adv: "\<And>s s' i. frz_st_rel R g s s' \<Longrightarrow> K s \<Longrightarrow>
      frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s') \<and>
      K (frz_adv_st sz ev pm dbe fl d j i s)"
    and cp: "\<And>\<rho> w pR tq rb \<rho>' X i. R \<rho> \<rho>' \<Longrightarrow> K (\<rho>, w, pR, tq, rb) \<Longrightarrow> X \<in> A \<Longrightarrow>
      fst (ev' [] (Mapping.update pm' (replicate (frz_cut po w i j) (ga X)) dbe') \<rho>') =
        map g (fst (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>))
        (snd (ev' [] (Mapping.update pm' (replicate (frz_cut po w i j) (ga X)) dbe') \<rho>'))"
    and "set \<alpha>s \<subseteq> A" and "frz_st_rel R g s s'" and "K s"
    and "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s1, lv, s1)"
    and "frz_loop sz' ev' pm' dbe' (ga fl) d po j i (map ga \<alpha>s) s' = (ys', \<alpha>s1', lv', s1')"
  shows "ys' = map g ys \<and> \<alpha>s1' = map ga \<alpha>s1 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv lv' \<and>
    frz_st_rel R g s1 s1' \<and> K s1"
  using assms(3-)
proof (induction \<alpha>s arbitrary: i s s' ys \<alpha>s1 lv s1 ys' \<alpha>s1' lv' s1')
  case Nil
  then show ?case
    using adv[OF Nil.prems(2,3), of i] by auto
next
  case (Cons \<alpha> \<alpha>s)
  note prems = Cons.prems and IH = Cons.IH
  obtain \<rho> w pR tq rb where s1: "frz_adv_st sz ev pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  from adv[OF prems(2,3), of i] s1 obtain \<rho>' where
    s1': "frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s' = (\<rho>', w, pR, tq, map g rb)"
    and R: "R \<rho> \<rho>'" and K1: "K (\<rho>, w, pR, tq, rb)"
    by (cases "frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s'") auto
  let ?c = "frz_cut po w i j"
  obtain us \<sigma> where e: "ev [] (Mapping.update pm (replicate ?c \<alpha>) dbe) \<rho> = (us, \<sigma>)"
    by fastforce
  obtain us' \<sigma>' where e': "ev' [] (Mapping.update pm' (replicate ?c (ga \<alpha>)) dbe') \<rho>' = (us', \<sigma>')"
    by fastforce
  have "\<alpha> \<in> A"
    using prems(1) by simp
  from cp[OF R K1 this, of i] e e' have us': "us' = map g us" and R\<sigma>: "R \<sigma> \<sigma>'"
    by simp_all
  have dr: "drop (i - (pR - length (map g rb))) (map g rb @ us') = map g (drop (i - (pR - length rb)) (rb @ us))"
    by (simp add: us' drop_map[symmetric])
  show ?case
  proof (cases "drop (i - (pR - length rb)) (rb @ us)")
    case Nil
    then have dr': "drop (i - (pR - length (map g rb))) (map g rb @ us') = []"
      using dr by simp
    have "ys = []" "\<alpha>s1 = \<alpha> # \<alpha>s" "lv = Some (i - (pR - length rb) - length (rb @ us), \<sigma>)"
      "s1 = (\<rho>, w, pR, tq, rb)"
      using prems(4) s1 e Nil by auto
    moreover have "ys' = []" "\<alpha>s1' = ga \<alpha> # map ga \<alpha>s"
      "lv' = Some (i - (pR - length rb) - length (rb @ us), \<sigma>')" "s1' = (\<rho>', w, pR, tq, map g rb)"
      using prems(5) s1' e' dr' us' by auto
    ultimately show ?thesis
      using R R\<sigma> K1 by simp
  next
    case (Cons y r)
    obtain zs bs lv0 s2 where rec: "frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) = (zs, bs, lv0, s2)"
      by (metis prod_cases4)
    obtain zs' bs' lv0' s2' where rec': "frz_loop sz' ev' pm' dbe' (ga fl) d po j (Suc i) (map ga \<alpha>s)
        (\<rho>', w, pR, tq, map g rb) = (zs', bs', lv0', s2')"
      by (metis prod_cases4)
    have IH': "zs' = map g zs \<and> bs' = map ga bs \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv0 lv0' \<and>
        frz_st_rel R g s2 s2' \<and> K s2"
      by (rule IH[OF _ _ K1 rec rec']) (use prems(1) R in auto)
    have dr': "drop (i - (pR - length (map g rb))) (map g rb @ us') = g y # map g r"
      using dr[unfolded Cons] by simp
    have "ys = y # zs" "\<alpha>s1 = bs" "lv = lv0" "s1 = s2"
      using prems(4) s1 e Cons rec by auto
    moreover have "ys' = g y # zs'" "\<alpha>s1' = bs'" "lv' = lv0'" "s1' = s2'"
      using prems(5) s1' e' dr' rec' by auto
    ultimately show ?thesis
      using IH' by simp
  qed
qed

lemma frz_live_loop_rel_inv:
  assumes adv: "\<And>s s' i. frz_st_rel R g s s' \<Longrightarrow> K s \<Longrightarrow>
      frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s') \<and>
      K (frz_adv_st sz ev pm dbe fl d j i s)"
    and cp: "\<And>\<rho> w pR tq rb \<rho>' X i. R \<rho> \<rho>' \<Longrightarrow> K (\<rho>, w, pR, tq, rb) \<Longrightarrow> X \<in> A \<Longrightarrow>
      fst (ev' [] (Mapping.update pm' (replicate (frz_cut po w i j) (ga X)) dbe') \<rho>') =
        map g (fst (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>))
        (snd (ev' [] (Mapping.update pm' (replicate (frz_cut po w i j) (ga X)) dbe') \<rho>'))"
    and A: "set \<alpha>s \<subseteq> A" and st: "frz_st_rel R g s s'" and K: "K s"
    and L: "rel_option (\<lambda>(k, us, \<sigma>) (k', us', \<sigma>'). k' = k \<and> us' = map g us \<and> R \<sigma> \<sigma>') lr lr'"
    and r: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s1, lv, s1)"
    and r': "frz_live_loop sz' ev' pm' dbe' (ga fl) d po j i (map ga \<alpha>s) lr' s' = (ys', \<alpha>s1', lv', s1')"
  shows "ys' = map g ys \<and> \<alpha>s1' = map ga \<alpha>s1 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv lv' \<and>
    frz_st_rel R g s1 s1' \<and> K s1"
proof (cases lr)
  case None
  then have "lr' = None"
    using L by simp
  with None r r' have r0: "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s1, lv, s1)"
    and r0': "frz_loop sz' ev' pm' dbe' (ga fl) d po j i (map ga \<alpha>s) s' = (ys', \<alpha>s1', lv', s1')"
    by (simp_all add: frz_live_loop_def)
  show ?thesis
    by (rule frz_loop_rel_inv[OF adv cp A st K r0 r0'])
next
  case (Some x)
  then obtain k us \<sigma> where lr: "lr = Some (k, us, \<sigma>)"
    by (cases x) auto
  with L obtain \<sigma>' where lr': "lr' = Some (k, map g us, \<sigma>')" and R: "R \<sigma> \<sigma>'"
    by (cases lr') auto
  show ?thesis
  proof (cases "drop k us")
    case Nil
    have "frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s') \<and>
        K (frz_adv_st sz ev pm dbe fl d j i s)"
      using adv[OF st K] by blast
    then show ?thesis
      using r r' lr lr' R Nil by (auto simp: frz_live_loop_def drop_map)
  next
    case (Cons y r0)
    obtain zs bs lv0 s2 where rec: "frz_loop sz ev pm dbe fl d po j (Suc i) (tl \<alpha>s) s = (zs, bs, lv0, s2)"
      by (metis prod_cases4)
    obtain zs' bs' lv0' s2' where rec': "frz_loop sz' ev' pm' dbe' (ga fl) d po j (Suc i) (map ga (tl \<alpha>s)) s' =
        (zs', bs', lv0', s2')"
      by (metis prod_cases4)
    have A': "set (tl \<alpha>s) \<subseteq> A"
      using A by (cases \<alpha>s) auto
    have IH': "zs' = map g zs \<and> bs' = map ga bs \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv0 lv0' \<and>
        frz_st_rel R g s2 s2' \<and> K s2"
      by (rule frz_loop_rel_inv[OF adv cp A' st K rec rec'])
    have "ys = y # zs" "\<alpha>s1 = bs" "lv = lv0" "s1 = s2"
      using r lr Cons rec by (auto simp: frz_live_loop_def)
    moreover have "ys' = g y # zs'" "\<alpha>s1' = bs'" "lv' = lv0'" "s1' = s2'"
      using r' lr' Cons rec' by (auto simp: frz_live_loop_def drop_map map_tl)
    ultimately show ?thesis
      using IH' by simp
  qed
qed

text \<open>The state of the replay base between the copies, read through the kernel's invariant: the
  window starts at @{term w} and its time-stamps are those of the trace from there, and the base is
  well formed for every valuation of the frozen predicate from @{term w} on.  The tables in
  @{term A} are those of the frozen formula at some time point (or empty), which is what the copies
  and the window's moves feed the base.\<close>

text \<open>The executable tables are read at the frozen predicate's variables through their own
  columns: reading a tuple's restriction there is reading the tuple.\<close>

lemma val_restrict:
  assumes "eframe ks cs"
  shows "val m cs (restrict cs ks x) = val m ks x"
proof -
  have "tup_get cs (restrict cs ks x) i = tup_get ks x i" for i
  proof (cases "i \<in> set cs")
    case True
    then show ?thesis
      by (simp add: tup_get_def restrict_def map_of_zip_map)
  next
    case False
    then have "i \<notin> set ks"
      using eframeD(3)[OF assms] by simp
    then have "map_of (zip ks x) i = None"
      by (auto simp: map_of_eq_None_iff dest: set_zip_leftD)
    with False show ?thesis
      by (simp add: tup_get_def restrict_def map_of_zip_map)
  qed
  then show ?thesis
    by (simp add: val_def)
qed

lemma etabc_frz_cmb:
  assumes "eframe ks cs"
  shows "fo_cmb (frz_kops m cs) (etabc ks cs yS) (etabc ks cs yE) \<alpha> = etabc ks cs (fo_cmb (frz_kops m ks) yS yE \<alpha>)"
  using val_restrict[OF assms] by (auto simp: frz_kops_def etabc_def)

text \<open>The separable mode under the simulation.  The two runs replay the same tables, from related
  states; the copies' verdicts are mapped like all others.  Its tables, the frozen ones and their
  unions, are those of a set @{term B} closed under union, for which the replays are good calls.
  The operations of the two runs agree on the frozen tables, and the combination of two rows
  commutes with the map of the verdicts.\<close>

definition frz_ops_rel :: "('t \<Rightarrow> 't') \<Rightarrow> ('a, 't) frz_ops \<Rightarrow> ('a, 't') frz_ops \<Rightarrow> bool" where
  "frz_ops_rel g ops ops' \<longleftrightarrow> fo_un ops' = fo_un ops \<and> fo_fr ops' = fo_fr ops \<and> fo_cd ops' = fo_cd ops \<and>
    fo_emp ops' = fo_emp ops \<and> (\<forall>yS yE \<alpha>. fo_cmb ops' (g yS) (g yE) \<alpha> = g (fo_cmb ops yS yE \<alpha>))"

lemma frz_ops_relD:
  assumes "frz_ops_rel g ops ops'"
  shows "fo_un ops' = fo_un ops" "fo_fr ops' = fo_fr ops" "fo_cd ops' = fo_cd ops" "fo_emp ops' = fo_emp ops"
    "fo_cmb ops' (g yS) (g yE) \<alpha> = g (fo_cmb ops yS yE \<alpha>)"
  using assms by (simp_all add: frz_ops_rel_def)

lemma frz_unions_rel: "frz_ops_rel g ops ops' \<Longrightarrow> frz_unions ops' xs L = frz_unions ops xs L"
  by (simp add: frz_unions_def frz_ops_rel_def)

lemma frz_absorb_rel: "frz_ops_rel g ops ops' \<Longrightarrow> frz_absorb ops' xs c = frz_absorb ops xs c"
  by (simp add: frz_absorb_def frz_ops_rel_def)

lemma frz_emit_rel:
  "frz_ops_rel g ops ops' \<Longrightarrow>
    frz_emit (fo_cmb ops') \<alpha>s (map (map_prod g g) buf) = map g (frz_emit (fo_cmb ops) \<alpha>s buf)"
  by (induction \<alpha>s arbitrary: buf) (auto simp: frz_emit_def frz_ops_rel_def neq_Nil_conv)

lemma frz_unions_in:
  assumes "\<And>X Y. X \<in> B \<Longrightarrow> Y \<in> B \<Longrightarrow> fo_un ops X Y \<in> B" "L \<in> B" "set xs \<subseteq> B"
  shows "frz_unions ops xs L \<in> B"
  using assms(2,3) unfolding frz_unions_def by (induction xs arbitrary: L) (auto intro: assms(1))

lemma frz_absorb_in:
  assumes "\<And>X Y. X \<in> B \<Longrightarrow> Y \<in> B \<Longrightarrow> fo_un ops X Y \<in> B" "L \<in> B" "set xs \<subseteq> B"
  shows "fst (frz_absorb ops xs (L, n, f)) \<in> B"
  using assms(2,3) unfolding frz_absorb_def
  by (induction xs arbitrary: L n f) (auto intro: assms(1) simp: Let_def)

lemma frz_copies_rel_inv:
  assumes cpc: "\<And>\<rho> w pR tq rb \<rho>' X. R \<rho> \<rho>' \<Longrightarrow> K (\<rho>, w, pR, tq, rb) \<Longrightarrow> X \<in> B \<Longrightarrow>
      fst (ev' [] (Mapping.update pm (replicate (j - w) X) dbe') \<rho>') =
        map g (fst (ev [] (Mapping.update pm (replicate (j - w) X) dbe) \<rho>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate (j - w) X) dbe) \<rho>))
        (snd (ev' [] (Mapping.update pm (replicate (j - w) X) dbe') \<rho>'))"
    and sz: "\<And>\<psi>1 \<psi>1' \<psi>2 \<psi>2'. R \<psi>1 \<psi>1' \<Longrightarrow> Rs \<psi>2 \<psi>2' \<Longrightarrow> sz \<psi>1 = sz \<psi>2 \<longleftrightarrow> sz' \<psi>1' = sz' \<psi>2'"
    and st: "frz_st_rel R g s s'" and K: "K s" and L: "L \<in> B" and E: "emp \<in> B"
    and RS: "Rs \<sigma>S \<sigma>S'" and RE: "Rs \<sigma>E \<sigma>E'"
  shows "rel_option (\<lambda>(\<rho>S, \<rho>E, pX, buf) (\<rho>S', \<rho>E', pX', buf'). R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E' \<and> pX' = pX \<and>
      buf' = map (map_prod g g) buf)
    (frz_copies sz ev emp pm dbe j i L \<sigma>S \<sigma>E s) (frz_copies sz' ev' emp pm dbe' j i L \<sigma>S' \<sigma>E' s')"
proof -
  obtain \<rho> w pR tq rb where s: "s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  with st obtain \<rho>' where s': "s' = (\<rho>', w, pR, tq, map g rb)" and R: "R \<rho> \<rho>'"
    by (cases s') auto
  obtain uS \<rho>S where eS: "ev [] (Mapping.update pm (replicate (j - w) L) dbe) \<rho> = (uS, \<rho>S)"
    by fastforce
  obtain uE \<rho>E where eE: "ev [] (Mapping.update pm (replicate (j - w) emp) dbe) \<rho> = (uE, \<rho>E)"
    by fastforce
  obtain uS' \<rho>S' where eS': "ev' [] (Mapping.update pm (replicate (j - w) L) dbe') \<rho>' = (uS', \<rho>S')"
    by fastforce
  obtain uE' \<rho>E' where eE': "ev' [] (Mapping.update pm (replicate (j - w) emp) dbe') \<rho>' = (uE', \<rho>E')"
    by fastforce
  have K': "K (\<rho>, w, pR, tq, rb)"
    using K s by simp
  have S: "uS' = map g uS" "R \<rho>S \<rho>S'"
    using cpc[OF R K' L] eS eS' by simp_all
  have E': "uE' = map g uE" "R \<rho>E \<rho>E'"
    using cpc[OF R K' E] eE eE' by simp_all
  have g1: "sz \<rho>S = sz \<sigma>S \<longleftrightarrow> sz' \<rho>S' = sz' \<sigma>S'"
    by (rule sz[OF S(2) RS])
  have g2: "sz \<rho>E = sz \<sigma>E \<longleftrightarrow> sz' \<rho>E' = sz' \<sigma>E'"
    by (rule sz[OF E'(2) RE])
  have z: "zip (map g rb @ map g uS) (map g rb @ map g uE) = map (map_prod g g) (zip (rb @ uS) (rb @ uE))"
    by (simp add: zip_map_map flip: map_append)
  show ?thesis
    using S E' g1 g2
    by (auto simp: frz_copies_def s s' eS eE eS' eE' z drop_map)
qed

lemma frz_stock_rel_inv:
  assumes adv: "\<And>s s' i. frz_st_rel R g s s' \<Longrightarrow> K s \<Longrightarrow>
      frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm dbe' fl d j i s') \<and>
      K (frz_adv_st sz ev pm dbe fl d j i s)"
    and cp: "\<And>\<rho> w pR tq rb \<rho>' X i. R \<rho> \<rho>' \<Longrightarrow> K (\<rho>, w, pR, tq, rb) \<Longrightarrow> X \<in> A \<Longrightarrow>
      fst (ev' [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe') \<rho>') =
        map g (fst (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>))
        (snd (ev' [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe') \<rho>'))"
    and cpc: "\<And>\<rho> w pR tq rb \<rho>' X. R \<rho> \<rho>' \<Longrightarrow> K (\<rho>, w, pR, tq, rb) \<Longrightarrow> X \<in> B \<Longrightarrow>
      fst (ev' [] (Mapping.update pm (replicate (j - w) X) dbe') \<rho>') =
        map g (fst (ev [] (Mapping.update pm (replicate (j - w) X) dbe) \<rho>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate (j - w) X) dbe) \<rho>))
        (snd (ev' [] (Mapping.update pm (replicate (j - w) X) dbe') \<rho>'))"
    and sz: "\<And>\<psi>1 \<psi>1' \<psi>2 \<psi>2'. R \<psi>1 \<psi>1' \<Longrightarrow> Rs \<psi>2 \<psi>2' \<Longrightarrow> sz \<psi>1 = sz \<psi>2 \<longleftrightarrow> sz' \<psi>1' = sz' \<psi>2'"
    and RRs: "\<And>\<psi> \<psi>'. R \<psi> \<psi>' \<Longrightarrow> Rs \<psi> \<psi>'"
    and ops: "frz_ops_rel g ops ops'"
    and Bun: "\<And>X Y. X \<in> B \<Longrightarrow> Y \<in> B \<Longrightarrow> fo_un ops X Y \<in> B" and AB: "A \<subseteq> B" and EB: "fo_emp ops \<in> B"
    and A: "set \<alpha>s \<subseteq> A" and xsr: "set xsr \<subseteq> B" and st: "frz_st_rel R g s s'" and K: "K s"
    and c: "c = (rg, bo, tk, Lsh, nsh, Lr)" "Lsh \<in> B" "Lr \<in> B"
    and RS: "Rs \<sigma>S \<sigma>S'" and RE: "Rs \<sigma>E \<sigma>E'"
    and L: "rel_option (\<lambda>(k, us, \<sigma>) (k', us', \<sigma>'). k' = k \<and> us' = map g us \<and> R \<sigma> \<sigma>') lr lr'"
    and r: "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr c \<sigma>S \<sigma>E s = (ys, \<alpha>s1, lv, s1, sx1, \<rho>S, \<rho>E)"
    and r': "frz_stock sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr lr' c \<sigma>S' \<sigma>E' s' = (ys', \<alpha>s1', lv', s1', sx1', \<rho>S', \<rho>E')"
  shows "ys' = map g ys \<and> \<alpha>s1' = \<alpha>s1 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv lv' \<and>
    frz_st_rel R g s1 s1' \<and> K s1 \<and> sx1' = map_frz_sep id g sx1 \<and> Rs \<rho>S \<rho>S' \<and> Rs \<rho>E \<rho>E' \<and>
    (\<forall>L nL pX buf rg bo tk Lr. sx1 = FSSep L nL pX buf rg bo tk Lr \<longrightarrow> R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E')"
proof -
  obtain ys0 bs0 lv0 s0 where l: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys0, bs0, lv0, s0)"
    by (metis prod_cases4)
  obtain ys0' bs0' lv0' s0' where l': "frz_live_loop sz' ev' pm dbe' fl d po j i \<alpha>s lr' s' = (ys0', bs0', lv0', s0')"
    by (metis prod_cases4)
  have l'': "frz_live_loop sz' ev' pm dbe' (id fl) d po j i (map id \<alpha>s) lr' s' = (ys0', bs0', lv0', s0')"
    using l' by simp
  have LR: "ys0' = map g ys0 \<and> bs0' = map id bs0 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv0 lv0' \<and>
      frz_st_rel R g s0 s0'"
    by (rule frz_live_loop_rel_inv[where ga = id, OF _ _ A st K L l l''])
      (use adv cp in \<open>simp_all\<close>)
  obtain Lsh1 nsh1 nf where ab: "frz_absorb ops xsr (Lsh, nsh, 0) = (Lsh1, nsh1, nf)"
    by (metis prod_cases3)
  have ab': "frz_absorb ops' xsr (Lsh, nsh, 0) = (Lsh1, nsh1, nf)"
    using ab frz_absorb_rel[OF ops] by simp
  have K0: "K s0" and st0: "frz_st_rel R g s0 s0'" and ys0': "ys0' = map g ys0" and bs0': "bs0' = bs0"
    and lv0: "rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv0 lv0'"
    using LR by simp_all
  have w0: "fst (snd s0') = fst (snd s0)"
    using st0 by (cases s0; cases s0') auto
  have bs0A: "set bs0 \<subseteq> A"
    using frz_live_loop_inv[where P = "\<lambda>_. True" and T = "\<lambda>_. True", OF _ _ _ l] A by (auto simp: list_all_iff)
  have Lsh1B: "Lsh1 \<in> B"
    using frz_absorb_in[OF Bun c(2) xsr, of nsh 0] ab by simp
  let ?L = "frz_unions ops bs0 Lsh1"
  have LB: "?L \<in> B"
    by (rule frz_unions_in[OF Bun Lsh1B]) (use bs0A AB in blast)
  have cpr: "rel_option (\<lambda>(\<rho>S, \<rho>E, pX, buf) (\<rho>S', \<rho>E', pX', buf'). R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E' \<and> pX' = pX \<and>
      buf' = map (map_prod g g) buf)
    (frz_copies sz ev (fo_emp ops) pm dbe j (i + length ys0) ?L \<sigma>S \<sigma>E s0)
    (frz_copies sz' ev' (fo_emp ops) pm dbe' j (i + length ys0) ?L \<sigma>S' \<sigma>E' s0')"
    by (rule frz_copies_rel_inv[where Rs = Rs, OF cpc sz st0 K0 LB EB RS RE])
  have eq: "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr c \<sigma>S \<sigma>E s = _"
    unfolding c by (rule frz_stock_eq[OF l ab])
  have eq': "frz_stock sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr lr' c \<sigma>S' \<sigma>E' s' = _"
    unfolding c by (rule frz_stock_eq[OF l' ab'])
  note opsr = frz_ops_relD[OF ops] frz_unions_rel[OF ops]
  show ?thesis
    using r r' cpr K0 st0 lv0 RS RE RRs
    unfolding eq eq' opsr ys0' bs0' w0 length_map Let_def
    by (simp only: split: if_split_asm option.split_asm prod.split_asm) (auto simp: option.rel_sel)
qed

lemma frz_step_rel_inv:
  assumes adv: "\<And>s s' i. frz_st_rel R g s s' \<Longrightarrow> K s \<Longrightarrow>
      frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm dbe' fl d j i s') \<and>
      K (frz_adv_st sz ev pm dbe fl d j i s)"
    and cp: "\<And>\<rho> w pR tq rb \<rho>' X i. R \<rho> \<rho>' \<Longrightarrow> K (\<rho>, w, pR, tq, rb) \<Longrightarrow> X \<in> A \<Longrightarrow>
      fst (ev' [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe') \<rho>') =
        map g (fst (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe) \<rho>))
        (snd (ev' [] (Mapping.update pm (replicate (frz_cut po w i j) X) dbe') \<rho>'))"
    and cpc: "\<And>\<rho> w pR tq rb \<rho>' X. R \<rho> \<rho>' \<Longrightarrow> K (\<rho>, w, pR, tq, rb) \<Longrightarrow> X \<in> B \<Longrightarrow>
      fst (ev' [] (Mapping.update pm (replicate (j - w) X) dbe') \<rho>') =
        map g (fst (ev [] (Mapping.update pm (replicate (j - w) X) dbe) \<rho>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate (j - w) X) dbe) \<rho>))
        (snd (ev' [] (Mapping.update pm (replicate (j - w) X) dbe') \<rho>'))"
    and sz: "\<And>\<psi>1 \<psi>1' \<psi>2 \<psi>2'. R \<psi>1 \<psi>1' \<Longrightarrow> Rs \<psi>2 \<psi>2' \<Longrightarrow> sz \<psi>1 = sz \<psi>2 \<longleftrightarrow> sz' \<psi>1' = sz' \<psi>2'"
    and RRs: "\<And>\<psi> \<psi>'. R \<psi> \<psi>' \<Longrightarrow> Rs \<psi> \<psi>'"
    and ops: "frz_ops_rel g ops ops'"
    and Bun: "\<And>X Y. X \<in> B \<Longrightarrow> Y \<in> B \<Longrightarrow> fo_un ops X Y \<in> B" and AB: "A \<subseteq> B" and EB: "fo_emp ops \<in> B"
    and A: "set \<alpha>s \<subseteq> A" and xsr: "set xsr \<subseteq> B" and st: "frz_st_rel R g s s'" and K: "K s"
    and SB: "\<And>rg bo tk Lsh nsh Lr. sx = FSStock rg bo tk Lsh nsh Lr \<Longrightarrow> Lsh \<in> B \<and> Lr \<in> B"
      "\<And>L nL pX buf rg bo tk Lr. sx = FSSep L nL pX buf rg bo tk Lr \<Longrightarrow> L \<in> B \<and> Lr \<in> B"
    and RS: "Rs \<sigma>S \<sigma>S'" and RE: "Rs \<sigma>E \<sigma>E'"
    and L: "rel_option (\<lambda>(k, us, \<sigma>) (k', us', \<sigma>'). k' = k \<and> us' = map g us \<and> R \<sigma> \<sigma>') lr lr'"
    and FD: "rel_option (\<lambda>((uS, \<rho>S), (uE, \<rho>E)) ((uS', \<rho>S'), (uE', \<rho>E')).
      uS' = map g uS \<and> uE' = map g uE \<and> R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E') fd fd'"
    and r: "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s = (ys, \<alpha>s1, lv, s1, sx1, \<rho>S, \<rho>E)"
    and r': "frz_step sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr lr' fd' (map_frz_sep id g sx) \<sigma>S' \<sigma>E' s' =
      (ys', \<alpha>s1', lv', s1', sx1', \<rho>S', \<rho>E')"
  shows "ys' = map g ys \<and> \<alpha>s1' = \<alpha>s1 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv lv' \<and>
    frz_st_rel R g s1 s1' \<and> K s1 \<and> sx1' = map_frz_sep id g sx1 \<and> Rs \<rho>S \<rho>S' \<and> Rs \<rho>E \<rho>E' \<and>
    (\<forall>L nL pX buf rg bo tk Lr. sx1 = FSSep L nL pX buf rg bo tk Lr \<longrightarrow> R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E')"
proof (cases sx)
  case FSOff
  obtain ys0 bs0 lv0 s0 where l: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys0, bs0, lv0, s0)"
    by (metis prod_cases4)
  obtain ys0' bs0' lv0' s0' where l': "frz_live_loop sz' ev' pm dbe' fl d po j i \<alpha>s lr' s' = (ys0', bs0', lv0', s0')"
    by (metis prod_cases4)
  have l'': "frz_live_loop sz' ev' pm dbe' (id fl) d po j i (map id \<alpha>s) lr' s' = (ys0', bs0', lv0', s0')"
    using l' by simp
  have LR: "ys0' = map g ys0 \<and> bs0' = map id bs0 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv0 lv0' \<and>
      frz_st_rel R g s0 s0' \<and> K s0"
    by (rule frz_live_loop_rel_inv[where ga = id, OF _ _ A st K L l l''])
      (use adv cp in \<open>simp_all\<close>)
  show ?thesis
    using r r' LR RS RE FSOff by (simp add: frz_step_def l l')
next
  case (FSStock rg bo tk Lsh nsh Lr)
  have r0: "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr lr (rg, bo, tk, Lsh, nsh, Lr) \<sigma>S \<sigma>E s =
      (ys, \<alpha>s1, lv, s1, sx1, \<rho>S, \<rho>E)"
    using r FSStock by (simp add: frz_step_def)
  have r0': "frz_stock sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr lr' (rg, bo, tk, Lsh, nsh, Lr) \<sigma>S' \<sigma>E' s' =
      (ys', \<alpha>s1', lv', s1', sx1', \<rho>S', \<rho>E')"
    using r' FSStock by (simp add: frz_step_def)
  show ?thesis
    by (rule frz_stock_rel_inv[OF adv cp cpc sz RRs ops Bun AB EB A xsr st K refl _ _ RS RE L r0 r0'])
      (use SB(1)[OF FSStock] in simp_all)
next
  case (FSSep L nL pX buf rg bo tk Lr)
  obtain L1 nL1 nf where ab: "frz_absorb ops xsr (L, nL, 0) = (L1, nL1, nf)"
    by (metis prod_cases3)
  have ab': "frz_absorb ops' xsr (L, nL, 0) = (L1, nL1, nf)"
    using ab frz_absorb_rel[OF ops] by simp
  have LB: "L \<in> B" and LrB: "Lr \<in> B"
    using SB(2)[OF FSSep] by simp_all
  have L1B: "L1 \<in> B"
    using frz_absorb_in[OF Bun LB xsr, of nL 0] ab by simp
  let ?Lr1 = "frz_unions ops xsr Lr"
  have Lr1B: "?Lr1 \<in> B"
    by (rule frz_unions_in[OF Bun LrB xsr])
  have LpB: "frz_unions ops \<alpha>s ?Lr1 \<in> B"
    by (rule frz_unions_in[OF Bun Lr1B]) (use A AB in blast)
  \<comment> \<open>the replay base, moved or not\<close>
  have s2: "frz_st_rel R g (if b then frz_adv_st sz ev pm dbe fl d j i s else s)
      (if b then frz_adv_st sz' ev' pm dbe' fl d j i s' else s') \<and>
    K (if b then frz_adv_st sz ev pm dbe fl d j i s else s)" for b
    using adv[OF st K] st K by simp
  \<comment> \<open>the copies, rebuilt or fed\<close>
  have cpr: "rel_option (\<lambda>(\<rho>S, \<rho>E, pX, buf) (\<rho>S', \<rho>E', pX', buf'). R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E' \<and> pX' = pX \<and>
      buf' = map (map_prod g g) buf)
    (frz_copies sz ev (fo_emp ops) pm dbe j i Ln \<sigma>S \<sigma>E s2)
    (frz_copies sz' ev' (fo_emp ops) pm dbe' j i Ln \<sigma>S' \<sigma>E' s2')"
    if "Ln \<in> B" "frz_st_rel R g s2 s2'" "K s2" for Ln s2 s2'
    by (rule frz_copies_rel_inv[where Rs = Rs, OF cpc sz that(2,3,1) EB RS RE])
  have fdr: "rel_option (\<lambda>(\<rho>S, \<rho>E, pX, buf) (\<rho>S', \<rho>E', pX', buf'). R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E' \<and> pX' = pX \<and>
      buf' = map (map_prod g g) buf)
    (case fd of Some ((uS, \<rho>S), (uE, \<rho>E)) \<Rightarrow> if sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E
        then Some (\<rho>S, \<rho>E, pX + length uS, drop (min i (pX + length uS) - (pX - length buf)) (buf @ zip uS uE))
        else None
      | None \<Rightarrow> None)
    (case fd' of Some ((uS, \<rho>S), (uE, \<rho>E)) \<Rightarrow> if sz' \<rho>S = sz' \<sigma>S' \<and> sz' \<rho>E = sz' \<sigma>E'
        then Some (\<rho>S, \<rho>E, pX + length uS,
          drop (min i (pX + length uS) - (pX - length (map (map_prod g g) buf))) (map (map_prod g g) buf @ zip uS uE))
        else None
      | None \<Rightarrow> None)"
    using FD
  proof (cases fd)
    case (Some x)
    then obtain uS \<rho>S1 uE \<rho>E1 where fd: "fd = Some ((uS, \<rho>S1), (uE, \<rho>E1))"
      by (metis prod_cases4)
    with FD obtain \<rho>S1' \<rho>E1' where fd': "fd' = Some ((map g uS, \<rho>S1'), (map g uE, \<rho>E1'))"
      and R1: "R \<rho>S1 \<rho>S1'" "R \<rho>E1 \<rho>E1'"
      by (cases fd') auto
    have g1: "sz \<rho>S1 = sz \<sigma>S \<longleftrightarrow> sz' \<rho>S1' = sz' \<sigma>S'" and g2: "sz \<rho>E1 = sz \<sigma>E \<longleftrightarrow> sz' \<rho>E1' = sz' \<sigma>E'"
      using sz[OF R1(1) RS] sz[OF R1(2) RE] .
    show ?thesis
      using R1 g1 g2 by (auto simp: fd fd' drop_map zip_map_map simp flip: map_append)
  qed simp
  have eq: "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s = _"
    unfolding FSSep by (rule frz_step_sep_eq[OF ab])
  have eq': "frz_step sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr lr' fd' (map_frz_sep id g sx) \<sigma>S' \<sigma>E' s' = _"
    unfolding FSSep frz_sep.map id_apply by (rule frz_step_sep_eq[OF ab'])
  note opsr = frz_ops_relD(1-4)[OF ops] frz_unions_rel[OF ops]
  define ep where "ep = (frz_epoch \<le> Suc tk)"
  define nP where "nP = (if ep then fo_cd ops (frz_unions ops \<alpha>s ?Lr1) else 0)"
  define pr where "pr = (nf = 0 \<and> ep \<and> 2 * nP + 256 < nL1)"
  define rb where "rb = (0 < nf \<or> pr)"
  define Ln where "Ln = (if pr then frz_unions ops \<alpha>s ?Lr1 else L1)"
  define nLn where "nLn = (if pr then nP else nL1)"
  define tk' where "tk' = (if ep then 0 else Suc tk)"
  define Lr' where "Lr' = (if ep then fo_emp ops else ?Lr1)"
  define sB where "sB = (if rb then frz_adv_st sz ev pm dbe fl d j i s else s)"
  define sB' where "sB' = (if rb then frz_adv_st sz' ev' pm dbe' fl d j i s' else s')"
  define cq where "cq = (if rb then frz_copies sz ev (fo_emp ops) pm dbe j i Ln \<sigma>S \<sigma>E sB
    else (case fd of Some ((uS, \<rho>S), (uE, \<rho>E)) \<Rightarrow> if sz \<rho>S = sz \<sigma>S \<and> sz \<rho>E = sz \<sigma>E
        then Some (\<rho>S, \<rho>E, pX + length uS, drop (min i (pX + length uS) - (pX - length buf)) (buf @ zip uS uE))
        else None
      | None \<Rightarrow> None))"
  define cq' where "cq' = (if rb then frz_copies sz' ev' (fo_emp ops) pm dbe' j i Ln \<sigma>S' \<sigma>E' sB'
    else (case fd' of Some ((uS, \<rho>S), (uE, \<rho>E)) \<Rightarrow> if sz' \<rho>S = sz' \<sigma>S' \<and> sz' \<rho>E = sz' \<sigma>E'
        then Some (\<rho>S, \<rho>E, pX + length uS,
          drop (min i (pX + length uS) - (pX - length (map (map_prod g g) buf))) (map (map_prod g g) buf @ zip uS uE))
        else None
      | None \<Rightarrow> None))"
  have stq: "frz_step sz ev ops pm dbe fl d po j i \<alpha>s xsr lr fd sx \<sigma>S \<sigma>E s = (case cq of
      None \<Rightarrow> frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr None (0, bo, tk', Ln, nLn, Lr') \<sigma>S \<sigma>E sB
    | Some (\<rho>S2, \<rho>E2, pX', buf') \<Rightarrow>
      (let ys = frz_emit (fo_cmb ops) \<alpha>s buf';
           s'' = frz_adv_st sz ev pm dbe fl d j (i + length ys) sB;
           k = j - fst (snd s'');
           rg' = rg + (frz_lambda * nLn + (if rb then k * nLn else 0)) - k * sum_list (map (fo_cd ops) xsr)
       in if k * max 1 nLn + frz_c0 < rg'
         then (ys, drop (length ys) \<alpha>s, None, s'', FSStock 0 (2 * bo) tk' Ln nLn Lr', \<sigma>S, \<sigma>E)
         else (ys, drop (length ys) \<alpha>s, None, s'', FSSep Ln nLn pX' (drop (length ys) buf') rg' bo tk' Lr', \<rho>S2, \<rho>E2)))"
    unfolding eq Let_def
    by (simp only: ep_def nP_def pr_def rb_def Ln_def nLn_def tk'_def Lr'_def sB_def cq_def)
  have stq': "frz_step sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr lr' fd' (map_frz_sep id g sx) \<sigma>S' \<sigma>E' s' = (case cq' of
      None \<Rightarrow> frz_stock sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr None (0, bo, tk', Ln, nLn, Lr') \<sigma>S' \<sigma>E' sB'
    | Some (\<rho>S2, \<rho>E2, pX', buf') \<Rightarrow>
      (let ys = frz_emit (fo_cmb ops') \<alpha>s buf';
           s'' = frz_adv_st sz' ev' pm dbe' fl d j (i + length ys) sB';
           k = j - fst (snd s'');
           rg' = rg + (frz_lambda * nLn + (if rb then k * nLn else 0)) - k * sum_list (map (fo_cd ops) xsr)
       in if k * max 1 nLn + frz_c0 < rg'
         then (ys, drop (length ys) \<alpha>s, None, s'', FSStock 0 (2 * bo) tk' Ln nLn Lr', \<sigma>S', \<sigma>E')
         else (ys, drop (length ys) \<alpha>s, None, s'', FSSep Ln nLn pX' (drop (length ys) buf') rg' bo tk' Lr', \<rho>S2, \<rho>E2)))"
    unfolding eq' Let_def opsr
    by (simp only: ep_def nP_def pr_def rb_def Ln_def nLn_def tk'_def Lr'_def sB'_def cq'_def)
  have LnB: "Ln \<in> B"
    using LpB L1B by (simp add: Ln_def)
  have Lr'B: "Lr' \<in> B"
    using EB Lr1B by (simp add: Lr'_def)
  have sBr: "frz_st_rel R g sB sB'" and KB: "K sB"
    using s2[of rb] by (simp_all add: sB_def sB'_def)
  have cqr: "rel_option (\<lambda>(\<rho>S, \<rho>E, pX, buf) (\<rho>S', \<rho>E', pX', buf'). R \<rho>S \<rho>S' \<and> R \<rho>E \<rho>E' \<and> pX' = pX \<and>
      buf' = map (map_prod g g) buf) cq cq'"
  proof (cases rb)
    case True
    then show ?thesis
      using cpr[OF LnB sBr KB] by (simp add: cq_def cq'_def)
  next
    case False
    then show ?thesis
      using fdr by (simp add: cq_def cq'_def)
  qed
  show ?thesis
  proof (cases cq)
    case None
    then have None': "cq' = None"
      using cqr by (cases cq') auto
    have r0: "frz_stock sz ev ops pm dbe fl d po j i \<alpha>s xsr None (0, bo, tk', Ln, nLn, Lr') \<sigma>S \<sigma>E sB =
        (ys, \<alpha>s1, lv, s1, sx1, \<rho>S, \<rho>E)"
      using r unfolding stq None by simp
    have r0': "frz_stock sz' ev' ops' pm dbe' fl d po j i \<alpha>s xsr None (0, bo, tk', Ln, nLn, Lr') \<sigma>S' \<sigma>E' sB' =
        (ys', \<alpha>s1', lv', s1', sx1', \<rho>S', \<rho>E')"
      using r' unfolding stq' None' by simp
    show ?thesis
      by (rule frz_stock_rel_inv[OF adv cp cpc sz RRs ops Bun AB EB A xsr sBr KB refl LnB Lr'B RS RE _ r0 r0']) simp
  next
    case (Some cc)
    then obtain \<rho>S2 \<rho>E2 pX2 buf2 where cqS: "cq = Some (\<rho>S2, \<rho>E2, pX2, buf2)"
      by (metis prod_cases4)
    with cqr obtain \<rho>S2' \<rho>E2' where cqS': "cq' = Some (\<rho>S2', \<rho>E2', pX2, map (map_prod g g) buf2)"
      and R2: "R \<rho>S2 \<rho>S2'" "R \<rho>E2 \<rho>E2'"
      by (cases cq') auto
    define ys0 where "ys0 = frz_emit (fo_cmb ops) \<alpha>s buf2"
    have ys0': "frz_emit (fo_cmb ops') \<alpha>s (map (map_prod g g) buf2) = map g ys0"
      unfolding ys0_def by (rule frz_emit_rel[OF ops])
    have adv2: "frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j (i + length ys0) sB)
        (frz_adv_st sz' ev' pm dbe' fl d j (i + length ys0) sB') \<and>
      K (frz_adv_st sz ev pm dbe fl d j (i + length ys0) sB)"
      by (rule adv[OF sBr KB])
    have w2: "fst (snd (frz_adv_st sz' ev' pm dbe' fl d j (i + length ys0) sB')) =
        fst (snd (frz_adv_st sz ev pm dbe fl d j (i + length ys0) sB))"
      using conjunct1[OF adv2]
      by (cases "frz_adv_st sz ev pm dbe fl d j (i + length ys0) sB";
          cases "frz_adv_st sz' ev' pm dbe' fl d j (i + length ys0) sB'") auto
    show ?thesis
      using r r' RS RE R2 adv2 RRs[OF R2(1)] RRs[OF R2(2)]
      unfolding stq stq' cqS cqS' option.case prod.case Let_def ys0' length_map w2 ys0_def[symmetric]
      by (auto simp: drop_map split: if_splits)
  qed
qed

text \<open>The tables of the separable evaluation: subsets of the union of the frozen tables and of the
  tables its state holds.\<close>

definition frz_tabs :: "event_data table set \<Rightarrow> (event_data list set, 't) frz_sep \<Rightarrow> event_data table set" where
  "frz_tabs A sx = {X. X \<subseteq> \<Union> A \<union>
    (case sx of FSOff \<Rightarrow> {} | FSStock _ _ _ Lsh _ Lr \<Rightarrow> Lsh \<union> Lr | FSSep L _ _ _ _ _ _ Lr \<Rightarrow> L \<union> Lr)}"

definition frz_kinv :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> Formula.name \<times> nat \<Rightarrow> enat \<Rightarrow> database \<Rightarrow>
    event_data table set \<Rightarrow> event_data table set \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<times> nat \<times> nat \<times> ts list \<times>
    event_data table list \<Rightarrow> bool" where
  "frz_kinv n ks J pm d dbe A B s \<longleftrightarrow> (\<exists>S E E' \<sigma> P' V R \<phi>1 \<psi>1. snd pm = Formula.nfv \<phi>1 \<and>
     wf_envs S \<sigma> J 0 P' P' V dbe \<and> S, E' \<turnstile> \<phi>1 \<and> S(pm \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1 \<and>
     {0..<snd pm} \<subseteq> Formula.fv \<phi>1 \<and> safe_formula \<phi>1 \<and> ks = Formula.fv_list \<psi>1 \<and>
     (\<forall>X \<in> A. finite X \<and> (\<exists>io. X = {v. length v = snd pm \<and>
       (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)})) \<and>
     (\<forall>X \<in> B. frz_tab \<sigma> V (snd pm) \<phi>1 X) \<and>
     (case s of (\<rho>', w', pR', tq', rb') \<Rightarrow> w' \<le> J \<and> (d \<noteq> \<infinity> \<longrightarrow> length tq' = J - w') \<and>
       (\<exists>N'. \<forall>M. frz_sup \<sigma> V \<phi>1 M \<longrightarrow> kwf_mformula \<sigma> J (P'(pm \<mapsto> w'))
         (V(pm \<mapsto> frz_ext \<sigma> V \<phi>1 N' w' M)) n R \<rho>' \<psi>1)))"

lemma frz_kinvE:
  assumes "frz_kinv n ks J (p, m) d dbe A B (\<rho>', w', pR', tq', rb')"
  obtains S E E' \<sigma> P' V R \<phi>1 \<psi>1 N' where "m = Formula.nfv \<phi>1"
    "wf_envs S \<sigma> J 0 P' P' V dbe" "S, E' \<turnstile> \<phi>1"
    "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    "{0..<m} \<subseteq> Formula.fv \<phi>1" "safe_formula \<phi>1" "ks = Formula.fv_list \<psi>1"
    "\<forall>X \<in> A. finite X \<and> (\<exists>io. X = {v. length v = m \<and>
       (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)})"
    "\<forall>X \<in> B. frz_tab \<sigma> V m \<phi>1 X"
    "w' \<le> J" "d \<noteq> \<infinity> \<longrightarrow> length tq' = J - w'"
    "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> J (P'((p, m) \<mapsto> w'))
         (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N' w' M)) n R \<rho>' \<psi>1"
  using assms unfolding frz_kinv_def prod.case snd_conv
  by (elim exE conjE) (rule that, assumption+, erule allE, erule mp, assumption)

lemma frz_kinvI:
  assumes "m = Formula.nfv \<phi>1" "wf_envs S \<sigma> J 0 P' P' V dbe" "S, E' \<turnstile> \<phi>1"
    "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    "{0..<m} \<subseteq> Formula.fv \<phi>1" "safe_formula \<phi>1" "ks = Formula.fv_list \<psi>1"
    "\<forall>X \<in> A. finite X \<and> (\<exists>io. X = {v. length v = m \<and>
       (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)})"
    "\<forall>X \<in> B. frz_tab \<sigma> V m \<phi>1 X"
    "w' \<le> J" "d \<noteq> \<infinity> \<longrightarrow> length tq' = J - w'"
    "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> J (P'((p, m) \<mapsto> w'))
         (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N' w' M)) n R \<rho>' \<psi>1"
  shows "frz_kinv n ks J (p, m) d dbe A B (\<rho>', w', pR', tq', rb')"
  unfolding frz_kinv_def prod.case snd_conv
  by (rule exI[of _ S], rule exI[of _ E], rule exI[of _ E'], rule exI[of _ \<sigma>], rule exI[of _ P'],
      rule exI[of _ V], rule exI[of _ R], rule exI[of _ \<phi>1], rule exI[of _ \<psi>1])
    (use assms in \<open>intro conjI exI[of _ N'] allI impI; assumption?\<close>)

lemma frz_adv_le: "d \<noteq> \<infinity> \<longrightarrow> length tq = J - w \<Longrightarrow> frz_adv d w i J tq \<le> J - w"
  unfolding frz_adv_def by (auto intro: order_trans[OF length_takeWhile_le])

lemma frz_cut_le: "frz_cut po w i J \<le> J - w"
  unfolding frz_cut_def by simp

text \<open>A call the copy loop makes, from such a state and with one of those tables, is good.\<close>

lemma frz_kinv_call:
  assumes inv: "frz_kinv n ks J pm d dbe A B (\<rho>', w', pR', tq', rb')" and X: "X \<in> A"
    and c: "c \<le> J - w'"
  shows "kgood n ks J [] (Mapping.update pm (replicate c X) dbe) \<rho>'"
proof -
  obtain p m where pm: "pm = (p, m)"
    by (cases pm)
  from inv obtain S E E' \<sigma> P' V R \<phi>1 \<psi>1 N' where m: "m = Formula.nfv \<phi>1"
    and envs: "wf_envs S \<sigma> J 0 P' P' V dbe" and wty1: "S, E' \<turnstile> \<phi>1"
    and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1" and ks: "ks = Formula.fv_list \<psi>1"
    and A: "\<forall>X \<in> A. finite X \<and> (\<exists>io. X = {v. length v = m \<and>
       (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)})"
    and w': "w' \<le> J"
    and wf: "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> J (P'((p, m) \<mapsto> w'))
         (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N' w' M)) n R \<rho>' \<psi>1"
    unfolding pm by (elim frz_kinvE) blast
  from A X obtain io where fX: "finite X"
    and Xo: "X = {v. length v = m \<and> (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)}"
    by blast
  let ?L = "\<lambda>k. if k < w' then N' k else io"
  have Ys: "list_all2 (\<lambda>k Y. Y = {v. length v = m \<and> frz_val \<sigma> V \<phi>1 ?L v k}) [w'..<w' + c] (replicate c X)"
    by (auto simp: list_all2_conv_all_nth Xo frz_val_def)
  have envs': "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> J 0 (P'((p, m) \<mapsto> w'))
    (P'((p, m) \<mapsto> w' + c)) (V((p, m) \<mapsto> frz_val \<sigma> V \<phi>1 ?L)) (Mapping.update (p, m) (replicate c X) dbe)"
    by (rule kmaux_wf_envs_update_frz[OF envs m fv safe1 wty1 _ _ _ _ Ys])
      (use w' c fX in \<open>auto dest: frz_val_sat\<close>)
  show ?thesis
    unfolding pm
    by (rule kgoodI[OF order_refl _ wf[OF frz_sup_val[of \<sigma> V \<phi>1 "\<lambda>_. io"], unfolded frz_ext_val] _ wty2 ks])
      (use envs' in simp_all)
qed

text \<open>So is a replay of the window with a table of the separable evaluation.\<close>

lemma frz_kinv_call_B:
  assumes inv: "frz_kinv n ks J pm d dbe A B (\<rho>', w', pR', tq', rb')" and X: "X \<in> B"
    and c: "c \<le> J - w'"
  shows "kgood n ks J [] (Mapping.update pm (replicate c X) dbe) \<rho>'"
proof -
  obtain p m where pm: "pm = (p, m)"
    by (cases pm)
  from inv obtain S E E' \<sigma> P' V R \<phi>1 \<psi>1 N' where m: "m = Formula.nfv \<phi>1"
    and envs: "wf_envs S \<sigma> J 0 P' P' V dbe" and wty1: "S, E' \<turnstile> \<phi>1"
    and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1" and ks: "ks = Formula.fv_list \<psi>1"
    and B: "\<forall>X \<in> B. frz_tab \<sigma> V m \<phi>1 X"
    and w': "w' \<le> J"
    and wf: "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> J (P'((p, m) \<mapsto> w'))
         (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N' w' M)) n R \<rho>' \<psi>1"
    unfolding pm by (elim frz_kinvE) blast
  have tX: "frz_tab \<sigma> V m \<phi>1 X"
    using B X by blast
  let ?Q = "frz_ext \<sigma> V \<phi>1 N' w' (\<lambda>v k. v \<in> X)"
  have Ys: "list_all2 (\<lambda>k Y. Y = {v. length v = m \<and> ?Q v k}) [w'..<w' + c] (replicate c X)"
    using tX by (auto simp: list_all2_conv_all_nth frz_ext_ge frz_tab_def)
  have envs': "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> J 0 (P'((p, m) \<mapsto> w'))
    (P'((p, m) \<mapsto> w' + c)) (V((p, m) \<mapsto> ?Q)) (Mapping.update (p, m) (replicate c X) dbe)"
    by (rule kmaux_wf_envs_update_frz[OF envs m fv safe1 wty1 _ _ _ _ Ys])
      (use w' c tX frz_tab_sup[OF tX] in \<open>auto simp: frz_tab_def dest: frz_ext_sat\<close>)
  show ?thesis
    unfolding pm
    by (rule kgoodI[OF order_refl _ wf[OF frz_tab_sup[OF tX]] _ wty2 ks]) (use envs' in simp_all)
qed

text \<open>The window's move preserves the invariant: the base, fed the filling table for the time
  points that leave the window, is well formed for every valuation from the window's new start on.\<close>

lemma frz_kinv_adv:
  assumes inv: "frz_kinv n ks J pm d dbe A B s" and fl: "fl \<in> A"
  shows "frz_kinv n ks J pm d dbe A B (frz_adv_st size (meval J n) pm dbe fl d J i s)"
proof -
  obtain p m where pm: "pm = (p, m)"
    by (cases pm)
  obtain \<rho>' w' pR' tq' rb' where s: "s = (\<rho>', w', pR', tq', rb')"
    by (metis prod_cases5)
  from inv obtain S E E' \<sigma> P' V R \<phi>1 \<psi>1 N' where m: "m = Formula.nfv \<phi>1"
    and envs: "wf_envs S \<sigma> J 0 P' P' V dbe" and wty1: "S, E' \<turnstile> \<phi>1"
    and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1" and ks: "ks = Formula.fv_list \<psi>1"
    and A: "\<forall>X \<in> A. finite X \<and> (\<exists>io. X = {v. length v = m \<and>
       (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)})"
    and B: "\<forall>X \<in> B. frz_tab \<sigma> V m \<phi>1 X"
    and w': "w' \<le> J" and tq': "d \<noteq> \<infinity> \<longrightarrow> length tq' = J - w'"
    and wf: "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> J (P'((p, m) \<mapsto> w'))
         (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N' w' M)) n R \<rho>' \<psi>1"
    unfolding pm s by (elim frz_kinvE) blast
  from A fl obtain io where ffl: "finite fl"
    and flo: "fl = {v. length v = m \<and> (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)}"
    by blast
  define a where "a = frz_adv d w' i J tq'"
  have a: "a \<le> J - w'"
    unfolding a_def by (rule frz_adv_le[OF tq'])
  obtain rs \<rho>2 where e: "meval J n [] (Mapping.update (p, m) (replicate a fl) dbe) \<rho>' = (rs, \<rho>2)"
    by fastforce
  define N'' where "N'' = (\<lambda>k. if k < w' then N' k else io)"
  have wf2: "kwf_mformula \<sigma> J (P'((p, m) \<mapsto> w' + a))
      (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N'' (w' + a) M)) n R \<rho>2 \<psi>1" if supM: "frz_sup \<sigma> V \<phi>1 M" for M
  proof -
    let ?Q = "frz_ext \<sigma> V \<phi>1 N'' (w' + a) M"
    define M' where "M' = (\<lambda>v k. if k < w' + a then frz_val \<sigma> V \<phi>1 (\<lambda>_. io) v k else M v k)"
    have supM': "frz_sup \<sigma> V \<phi>1 M'"
      using supM by (auto simp: M'_def frz_sup_def dest: frz_val_sat)
    have eq: "frz_ext \<sigma> V \<phi>1 N' w' M' = ?Q"
      by (auto simp: N''_def M'_def frz_ext_def frz_val_def fun_eq_iff)
    have Ys: "list_all2 (\<lambda>k Y. Y = {v. length v = m \<and> ?Q v k}) [w'..<w' + a] (replicate a fl)"
      by (auto simp: list_all2_conv_all_nth flo N''_def frz_val_def frz_ext_def)
    have envs': "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> J 0 (P'((p, m) \<mapsto> w'))
      (P'((p, m) \<mapsto> w' + a)) (V((p, m) \<mapsto> ?Q)) (Mapping.update (p, m) (replicate a fl) dbe)"
      by (rule kmaux_wf_envs_update_frz[OF envs m fv safe1 wty1 _ _ _ _ Ys])
        (use w' a ffl supM in \<open>auto dest: frz_ext_sat\<close>)
    have "case meval (J + 0) n (map (\<tau> \<sigma>) [J..<J + 0]) (Mapping.update (p, m) (replicate a fl) dbe) \<rho>' of
        (xs, \<phi>\<^sub>n) \<Rightarrow> kwf_mformula \<sigma> (J + 0) (P'((p, m) \<mapsto> w' + a)) (V((p, m) \<mapsto> ?Q)) n R \<phi>\<^sub>n \<psi>1 \<and>
        list_all2 (\<lambda>i. sat_table \<sigma> (V((p, m) \<mapsto> ?Q)) n R (Formula.fv_list \<psi>1) i \<psi>1)
          [progress \<sigma> (P'((p, m) \<mapsto> w')) \<psi>1 J..<progress \<sigma> (P'((p, m) \<mapsto> w' + a)) \<psi>1 (J + 0)] xs"
      by (rule kmaux_meval_correct[OF wf[OF supM', unfolded eq] envs' wty2])
    then show ?thesis
      using e by simp
  qed
  show ?thesis
  proof (cases "size \<rho>2 = size \<rho>'")
    case True
    have st: "frz_adv_st size (meval J n) pm dbe fl d J i s =
      (\<rho>2, w' + a, pR' + length rs, drop a tq', drop (min i (pR' + length rs) - (pR' - length rb')) (rb' @ rs))"
      using e True unfolding s pm a_def by (simp add: frz_adv_st_def Let_def)
    show ?thesis
      unfolding st unfolding pm
      by (rule frz_kinvI[OF m envs wty1 wty2 fv safe1 ks A B _ _ wf2]) (use w' a tq' in auto)
  next
    case False
    then have "frz_adv_st size (meval J n) pm dbe fl d J i s = s"
      using e unfolding s pm a_def by (simp add: frz_adv_st_def Let_def)
    with inv show ?thesis
      by simp
  qed
qed


text \<open>What a good call of a freeze node provides: the facts of the kernel's invariant the four
  kinds of calls below need.\<close>

lemma kgood_MFrzE:
  assumes "kgood n ks j ts db (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)"
  obtains S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1 N where "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    "S, E' \<turnstile> \<phi>1" "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" "safe_formula \<phi>1"
    "ks = Formula.fv_list \<psi>1" "kks = Formula.fv_list \<phi>1"
    "kwf_mformula \<sigma> j0 P V m UNIV \<phi> \<phi>1"
    "\<And>i. kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> 0)) (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>1)) n R \<psi> \<psi>1"
    "maux.wf_frz_state \<sigma> j0 P V p m \<phi>1 \<psi>1 jphi \<alpha>s"
    "jfrz = progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j0"
    "jpsi0 = progress \<sigma> (P((p, m) \<mapsto> 0)) \<psi>1 j0"
    "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> w))
      (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N w M)) n R \<rho> \<psi>1"
    "maux.wf_frz_win \<sigma> j0 P V n R p m \<phi>1 \<psi>1 jfrz w pR tq rb d"
    "\<And>g. lv = Some g \<Longrightarrow> \<exists>wL NL. (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
      kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz)) n R \<rho>L \<psi>1"
    "cS = Formula.fv_list \<psi>1"
    "sx \<noteq> FSOff \<Longrightarrow> key_sep (p, m) \<psi>1 \<and> Formula.contains_pred (p, m) \<psi>1"
    "\<And>rg bo tk Lsh nsh Lr. sx = FSStock rg bo tk Lsh nsh Lr \<Longrightarrow>
      frz_tab \<sigma> V m \<phi>1 Lsh \<and> frz_tab \<sigma> V m \<phi>1 Lr"
    "\<And>L nL pX buf rg bo tk Lr. sx = FSSep L nL pX buf rg bo tk Lr \<Longrightarrow>
      lv = None \<and> frz_tab \<sigma> V m \<phi>1 L \<and> frz_tab \<sigma> V m \<phi>1 Lr \<and> (\<forall>\<alpha> \<in> set \<alpha>s. \<alpha> \<subseteq> L) \<and>
      (\<exists>wS NS wE NE. (\<forall>k<wS. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        (\<forall>k<wE. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NS wS (\<lambda>v k. v \<in> L))) n R \<rho>S \<psi>1 \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NE wE (\<lambda>_ _. False))) n R \<rho>E \<psi>1)"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R
      (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>" and ks: "ks = Formula.fv_list \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 \<psi>1 N where \<chi>: "\<chi> = Formula.Frz p \<phi>1 \<psi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V m UNIV \<phi> \<phi>1"
    and wf\<psi>: "\<And>i. kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> 0)) (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>1)) n R \<psi> \<psi>1"
    and st: "maux.wf_frz_state \<sigma> j0 P V p m \<phi>1 \<psi>1 jphi \<alpha>s"
    and jfrz: "jfrz = progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j0"
    and jpsi0: "jpsi0 = progress \<sigma> (P((p, m) \<mapsto> 0)) \<psi>1 j0"
    and wf\<rho>: "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> w))
      (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N w M)) n R \<rho> \<psi>1"
    and win: "maux.wf_frz_win \<sigma> j0 P V n R p m \<phi>1 \<psi>1 jfrz w pR tq rb d"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1"
    and live: "\<And>g. lv = Some g \<Longrightarrow> \<exists>wL NL. (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
      kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz)) n R \<rho>L \<psi>1"
    and kks: "kks = Formula.fv_list \<phi>1" and cS: "cS = Formula.fv_list \<psi>1"
    and sep_ok: "sx \<noteq> FSOff \<Longrightarrow> key_sep (p, m) \<psi>1 \<and> Formula.contains_pred (p, m) \<psi>1"
    and stock: "\<And>rg bo tk Lsh nsh Lr. sx = FSStock rg bo tk Lsh nsh Lr \<Longrightarrow>
      frz_tab \<sigma> V m \<phi>1 Lsh \<and> frz_tab \<sigma> V m \<phi>1 Lr"
    and sep: "\<And>L nL pX buf rg bo tk Lr. sx = FSSep L nL pX buf rg bo tk Lr \<Longrightarrow>
      lv = None \<and> frz_tab \<sigma> V m \<phi>1 L \<and> frz_tab \<sigma> V m \<phi>1 Lr \<and> (\<forall>\<alpha> \<in> set \<alpha>s. \<alpha> \<subseteq> L) \<and>
      (\<exists>wS NS wE NE. (\<forall>k<wS. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        (\<forall>k<wE. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NS wS (\<lambda>v k. v \<in> L))) n R \<rho>S \<psi>1 \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NE wE (\<lambda>_ _. False))) n R \<rho>E \<psi>1)"
    by (cases rule: kmaux_wf_mformula_cases) (simp_all, blast)
  from wty obtain E' where wty1: "S, E' \<turnstile> \<phi>1"
    and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    unfolding \<chi> fv by (cases pred: wty_formula) simp_all
  show ?thesis
    by (rule that[OF g envs wty1 wty2 fv safe1 _ kks wf\<phi> wf\<psi> st jfrz jpsi0 wf\<rho> win live cS sep_ok stock sep])
      (simp add: ks \<chi>)
qed

lemma kgood_MFrz_phi:
  "kgood n ks j ts db (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) \<Longrightarrow>
   kgood m kks j ts db \<phi>"
  by (erule kgood_MFrzE) (rule kgoodI, assumption+)

lemma kgood_MFrz_psi:
  "kgood n ks j ts db (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) \<Longrightarrow>
   kgood n ks j ts (Mapping.update (p, m) [] db) \<psi>"
proof (erule kgood_MFrzE)
  fix S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1
  assume g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wty1: "S, E' \<turnstile> \<phi>1" and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1"
    and ks: "ks = Formula.fv_list \<psi>1"
    and wf\<psi>: "\<And>i. kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> 0)) (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>1)) n R \<psi> \<psi>1"
  show "kgood n ks j ts (Mapping.update (p, m) [] db) \<psi>"
    by (rule kgoodI[OF g wf\<psi>[of 0] kmaux_wf_envs_update3[OF envs fv safe1 wty1] wty2 ks])
qed

lemma kgood_MFrz_rho:
  "kgood n ks j ts db (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) \<Longrightarrow>
   kgood n ks j ts (Mapping.update (p, m) [] db) \<rho>"
proof (erule kgood_MFrzE)
  fix S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1 N
  assume g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wty1: "S, E' \<turnstile> \<phi>1" and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1"
    and ks: "ks = Formula.fv_list \<psi>1"
    and wf\<rho>: "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> w))
      (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N w M)) n R \<rho> \<psi>1"
    and win: "maux.wf_frz_win \<sigma> j0 P V n R p m \<phi>1 \<psi>1 jfrz w pR tq rb d"
  have w: "w \<le> j0"
    using win by (simp add: kmaux_wf_frz_win_def)
  have envs': "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> j0 (j - j0) (P((p, m) \<mapsto> w))
    (P'((p, m) \<mapsto> w)) (V((p, m) \<mapsto> frz_val \<sigma> V \<phi>1 (\<lambda>k. if k < w then N k else None))) (Mapping.update (p, m) [] db)"
    by (rule kmaux_wf_envs_update_frz[OF envs fv safe1 wty1]) (use w in \<open>auto dest: frz_val_sat\<close>)
  show "kgood n ks j ts (Mapping.update (p, m) [] db) \<rho>"
    by (rule kgoodI[OF g wf\<rho>[OF frz_sup_False, unfolded frz_ext_False] envs' wty2 ks])
qed

text \<open>The frozen tables a step replays: the queue of the kernel's state and the frozen formula's
  new tables, each the frozen formula's value at its time point, from the first pending one on.\<close>

lemma frz_queue_tables:
  assumes "maux.wf_frz_queue \<sigma> V m \<phi>1 ks Xs" and "X \<in> set Xs" and "{0..<m} \<subseteq> Formula.fv \<phi>1"
  shows "finite X \<and> (\<exists>i. X = {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>1})"
proof -
  from assms(1,2) obtain i where "sat_table \<sigma> V m UNIV [0..<m] i \<phi>1 X"
    by (auto simp: kmaux_wf_frz_queue_def kmaux_frz_qtable_def list_all2_conv_all_nth
        in_set_conv_nth)
  then show ?thesis
    using kmaux_qtable_frz_alpha[OF _ assms(3)] by (blast dest: qtableD(5))
qed

lemma frz_queues:
  assumes envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and j0: "j0 \<le> j"
    and wty1: "S, E' \<turnstile> \<phi>1" and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1"
    and kks: "kks = Formula.fv_list \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V m UNIV \<phi> \<phi>1"
    and st: "maux.wf_frz_state \<sigma> j0 P V p m \<phi>1 \<psi>1 jphi \<alpha>s"
    and e1: "meval j m (map (\<tau> \<sigma>) [j0..<j]) db \<phi> = (as0, \<phi>2)"
  shows "maux.wf_frz_queue \<sigma> V m \<phi>1 [progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j0..<jphi] \<alpha>s"
    and "maux.wf_frz_queue \<sigma> V m \<phi>1 [jphi..<progress \<sigma> P' \<phi>1 j] (map (reorder [0..<m] kks) as0)"
proof -
  have jphi: "jphi = progress \<sigma> P \<phi>1 j0"
    using st by (simp add: kmaux_wf_frz_state_def Let_def)
  show "maux.wf_frz_queue \<sigma> V m \<phi>1 [progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j0..<jphi] \<alpha>s"
    using st by (simp add: kmaux_wf_frz_state_def Let_def jphi)
  have "case meval (j0 + (j - j0)) m (map (\<tau> \<sigma>) [j0..<j0 + (j - j0)]) db \<phi> of (xs, \<phi>\<^sub>n) \<Rightarrow>
      kwf_mformula \<sigma> (j0 + (j - j0)) P' V m UNIV \<phi>\<^sub>n \<phi>1 \<and>
      list_all2 (\<lambda>i. sat_table \<sigma> V m UNIV (Formula.fv_list \<phi>1) i \<phi>1)
        [progress \<sigma> P \<phi>1 j0..<progress \<sigma> P' \<phi>1 (j0 + (j - j0))] xs"
    by (rule kmaux_meval_correct[OF wf\<phi> envs wty1])
  then have raw: "list_all2 (\<lambda>i. sat_table \<sigma> V m UNIV (Formula.fv_list \<phi>1) i \<phi>1)
      [jphi..<progress \<sigma> P' \<phi>1 j] as0"
    using j0 e1 by (simp add: jphi)
  show "maux.wf_frz_queue \<sigma> V m \<phi>1 [jphi..<progress \<sigma> P' \<phi>1 j] (map (reorder [0..<m] kks) as0)"
    unfolding kmaux_wf_frz_queue_def kmaux_frz_qtable_def list.rel_map kks
    by (rule list.rel_mono_strong[OF raw]) (rule sat_table_reorder_upt[OF _ fv(2,1)])
qed

lemma kgood_MFrz_kinv:
  assumes g0: "kgood n ks j ts db (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)"
    and e1: "meval j m ts db \<phi> = (as0, \<phi>2)"
    and e4: "meval j n ts (Mapping.update (p, m) [] db) \<rho> = (rs, \<rho>2)"
  shows "frz_kinv n ks j (p, m) d (Mapping.map_values (\<lambda>_ _. []) db)
      (Set.insert (frz_fill ng (\<alpha>s @ map (reorder [0..<m] kks) as0)) (set (\<alpha>s @ map (reorder [0..<m] kks) as0)))
      (frz_tabs (Set.insert (frz_fill ng (\<alpha>s @ map (reorder [0..<m] kks) as0)) (set (\<alpha>s @ map (reorder [0..<m] kks) as0))) sx)
      (\<rho>2, w, pR', if d = \<infinity> then [] else tq @ ts, rb')"
  using g0
proof (rule kgood_MFrzE)
  fix S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1 N
  assume g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wty1: "S, E' \<turnstile> \<phi>1" and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1"
    and ks: "ks = Formula.fv_list \<psi>1" and kks: "kks = Formula.fv_list \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V m UNIV \<phi> \<phi>1"
    and st: "maux.wf_frz_state \<sigma> j0 P V p m \<phi>1 \<psi>1 jphi \<alpha>s"
    and wf\<rho>: "\<And>M. frz_sup \<sigma> V \<phi>1 M \<Longrightarrow> kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> w))
      (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N w M)) n R \<rho> \<psi>1"
    and win: "maux.wf_frz_win \<sigma> j0 P V n R p m \<phi>1 \<psi>1 jfrz w pR tq rb d"
    and stock: "\<And>rg bo tk Lsh nsh Lr. sx = FSStock rg bo tk Lsh nsh Lr \<Longrightarrow>
      frz_tab \<sigma> V m \<phi>1 Lsh \<and> frz_tab \<sigma> V m \<phi>1 Lr"
    and sep: "\<And>L nL pX buf rg bo tk Lr. sx = FSSep L nL pX buf rg bo tk Lr \<Longrightarrow>
      lv = None \<and> frz_tab \<sigma> V m \<phi>1 L \<and> frz_tab \<sigma> V m \<phi>1 Lr \<and> (\<forall>\<alpha> \<in> set \<alpha>s. \<alpha> \<subseteq> L) \<and>
      (\<exists>wS NS wE NE. (\<forall>k<wS. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        (\<forall>k<wE. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NS wS (\<lambda>v k. v \<in> L))) n R \<rho>S \<psi>1 \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NE wE (\<lambda>_ _. False))) n R \<rho>E \<psi>1)"
  let ?xsr = "map (reorder [0..<m] kks) as0"
  have w: "w \<le> j0" and tq: "tq = (if d = \<infinity> then [] else map (\<tau> \<sigma>) [w..<j0])"
    using win by (simp_all add: kmaux_wf_frz_win_def)
  note qs = frz_queues[OF envs g(1) wty1 fv kks wf\<phi> st e1[unfolded g(2)]]
  have tabs: "finite X \<and> (\<exists>i. X = {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>1})"
    if "X \<in> set (\<alpha>s @ ?xsr)" for X
    using that frz_queue_tables[OF qs(1) _ fv(2)] frz_queue_tables[OF qs(2) _ fv(2)] by auto
  have A: "\<forall>X \<in> Set.insert (frz_fill ng (\<alpha>s @ ?xsr)) (set (\<alpha>s @ ?xsr)). finite X \<and>
      (\<exists>io. X = {v. length v = m \<and> (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)})"
  proof
    fix X
    assume X: "X \<in> Set.insert (frz_fill ng (\<alpha>s @ ?xsr)) (set (\<alpha>s @ ?xsr))"
    have "X = {} \<or> X \<in> set (\<alpha>s @ ?xsr)"
      using X frz_fill_cases[of ng "\<alpha>s @ ?xsr"] by auto
    then show "finite X \<and>
      (\<exists>io. X = {v. length v = m \<and> (case io of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>1)})"
    proof
      assume "X = {}"
      then show ?thesis
        by (intro conjI exI[of _ None]) simp_all
    next
      assume "X \<in> set (\<alpha>s @ ?xsr)"
      with tabs obtain i where "finite X" "X = {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>1}"
        by blast
      then show ?thesis
        by (intro conjI exI[of _ "Some i"]) simp_all
    qed
  qed
  have base: "wf_envs S \<sigma> j 0 P' P' V (Mapping.map_values (\<lambda>_ _. []) db)"
    using wf_envs_empty[OF envs] g(1) by simp
  have wf\<rho>2: "kwf_mformula \<sigma> j (P'((p, m) \<mapsto> w))
      (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 N w M)) n R \<rho>2 \<psi>1" if supM: "frz_sup \<sigma> V \<phi>1 M" for M
  proof -
    let ?Q = "frz_ext \<sigma> V \<phi>1 N w M"
    have envs': "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> j0 (j - j0) (P((p, m) \<mapsto> w))
      (P'((p, m) \<mapsto> w)) (V((p, m) \<mapsto> ?Q)) (Mapping.update (p, m) [] db)"
      by (rule kmaux_wf_envs_update_frz[OF envs fv safe1 wty1]) (use w supM in \<open>auto dest: frz_ext_sat\<close>)
    have "case meval (j0 + (j - j0)) n (map (\<tau> \<sigma>) [j0..<j0 + (j - j0)]) (Mapping.update (p, m) [] db) \<rho> of
        (xs, \<phi>\<^sub>n) \<Rightarrow> kwf_mformula \<sigma> (j0 + (j - j0)) (P'((p, m) \<mapsto> w)) (V((p, m) \<mapsto> ?Q)) n R \<phi>\<^sub>n \<psi>1 \<and>
        list_all2 (\<lambda>i. sat_table \<sigma> (V((p, m) \<mapsto> ?Q)) n R (Formula.fv_list \<psi>1) i \<psi>1)
          [progress \<sigma> (P((p, m) \<mapsto> w)) \<psi>1 j0..<progress \<sigma> (P'((p, m) \<mapsto> w)) \<psi>1 (j0 + (j - j0))] xs"
      by (rule kmaux_meval_correct[OF wf\<rho>[OF supM] envs' wty2])
    then show ?thesis
      using e4 g by simp
  qed
  have B: "\<forall>X \<in> frz_tabs (Set.insert (frz_fill ng (\<alpha>s @ ?xsr)) (set (\<alpha>s @ ?xsr))) sx. frz_tab \<sigma> V m \<phi>1 X"
  proof
    fix X
    assume X: "X \<in> frz_tabs (Set.insert (frz_fill ng (\<alpha>s @ ?xsr)) (set (\<alpha>s @ ?xsr))) sx"
    have tabA: "length v = m \<and> (\<exists>i. Formula.sat \<sigma> V v i \<phi>1)"
      if "v \<in> Y" "Y \<in> Set.insert (frz_fill ng (\<alpha>s @ ?xsr)) (set (\<alpha>s @ ?xsr))" for v Y
      using A that by auto
    have tabS: "length v = m \<and> (\<exists>i. Formula.sat \<sigma> V v i \<phi>1)"
      if "v \<in> (case sx of FSOff \<Rightarrow> {} | FSStock _ _ _ Lsh _ Lr \<Rightarrow> Lsh \<union> Lr | FSSep L _ _ _ _ _ _ Lr \<Rightarrow> L \<union> Lr)" for v
      using that stock sep by (auto simp: frz_tab_def split: frz_sep.splits)
    have finA: "finite (\<Union> (Set.insert (frz_fill ng (\<alpha>s @ ?xsr)) (set (\<alpha>s @ ?xsr))))"
      using A by auto
    have finS: "finite (case sx of FSOff \<Rightarrow> {} | FSStock _ _ _ Lsh _ Lr \<Rightarrow> Lsh \<union> Lr | FSSep L _ _ _ _ _ _ Lr \<Rightarrow> L \<union> Lr)"
      using stock sep by (auto simp: frz_tab_def split: frz_sep.splits)
    have "finite X"
      using X finA finS by (auto simp: frz_tabs_def intro: finite_subset)
    then show "frz_tab \<sigma> V m \<phi>1 X"
      using X tabA tabS by (auto simp: frz_tab_def frz_tabs_def)
  qed
  have tqs: "d \<noteq> \<infinity> \<longrightarrow> length (tq @ ts) = j - w"
    using tq g w by simp
  show ?thesis
    by (rule frz_kinvI[OF fv(1) base wty1 wty2 fv(2) safe1 ks A B _ _ wf\<rho>2]) (use w g(1) tqs in auto)
qed

text \<open>The live copy, fed the new time points with the frozen table of the first pending one.\<close>

lemma kgood_MFrz_live:
  assumes g0: "kgood n ks j ts db (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)"
    and e1: "meval j m ts db \<phi> = (as0, \<phi>2)" and lv: "lv = Some g"
    and ne: "drop (jfrz - jphi) (\<alpha>s @ map (reorder [0..<m] kks) as0) \<noteq> []"
  shows "kgood n ks j ts (Mapping.update (p, m)
      (replicate (length ts) (hd (drop (jfrz - jphi) (\<alpha>s @ map (reorder [0..<m] kks) as0)))) db) \<rho>L"
  using g0
proof (rule kgood_MFrzE)
  fix S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1
  assume g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wty1: "S, E' \<turnstile> \<phi>1" and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1"
    and ks: "ks = Formula.fv_list \<psi>1" and kks: "kks = Formula.fv_list \<phi>1"
    and wf\<phi>: "kwf_mformula \<sigma> j0 P V m UNIV \<phi> \<phi>1"
    and st: "maux.wf_frz_state \<sigma> j0 P V p m \<phi>1 \<psi>1 jphi \<alpha>s"
    and jfrz: "jfrz = progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j0"
    and live: "\<And>g. lv = Some g \<Longrightarrow> \<exists>wL NL. (\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
      kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz)) n R \<rho>L \<psi>1"
  let ?xsr = "map (reorder [0..<m] kks) as0"
  let ?a1 = "drop (jfrz - jphi) (\<alpha>s @ ?xsr)"
  from live[OF lv] obtain wL NL where winL: "\<forall>k<wL. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)"
    and wfL: "kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz)) n R \<rho>L \<psi>1"
    by blast
  have wL: "wL \<le> jfrz"
    by (rule frz_win_le[OF winL])
  have pm: "pred_mapping (\<lambda>x. x \<le> j0) P"
    by (rule wf_envs_P_simps(1)[OF envs])
  have jfrz_j0: "jfrz \<le> j0"
    unfolding jfrz by (rule progress_le_gen[OF pm])
  note qs = frz_queues[OF envs g(1) wty1 fv kks wf\<phi> st e1[unfolded g(2)]]
  have jphi: "jphi = progress \<sigma> P \<phi>1 j0"
    using st by (simp add: kmaux_wf_frz_state_def Let_def)
  have jphi_le: "jphi \<le> progress \<sigma> P' \<phi>1 j"
    unfolding jphi using wf_envs_progress_mono[OF envs, of \<phi>1] g(1) by simp
  have q1: "maux.wf_frz_queue \<sigma> V m \<phi>1 [jfrz..<progress \<sigma> P' \<phi>1 j] ?a1"
  proof (cases "jfrz \<le> jphi")
    case True
    have "maux.wf_frz_queue \<sigma> V m \<phi>1 ([jfrz..<jphi] @ [jphi..<progress \<sigma> P' \<phi>1 j]) (\<alpha>s @ ?xsr)"
      by (rule kmaux_wf_frz_queue_append[OF qs[folded jfrz]])
    then show ?thesis
      using True jphi_le by (simp add: upt_add_eq_append'[symmetric])
  next
    case False
    then have "\<alpha>s = []"
      using qs(1)[folded jfrz] by (auto simp: kmaux_wf_frz_queue_def)
    with kmaux_wf_frz_queue_drop[OF qs(2), of "jfrz - jphi"] False show ?thesis
      by simp
  qed
  have hd: "sat_table \<sigma> V m UNIV [0..<m] jfrz \<phi>1 (hd ?a1)"
    using q1 ne by (cases ?a1) (auto simp: kmaux_wf_frz_queue_def kmaux_frz_qtable_def
        list_all2_Cons2 upt_eq_Cons_conv)
  have envs': "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> j0 (j - j0) (P((p, m) \<mapsto> j0))
    (P'((p, m) \<mapsto> j0 + (j - j0))) (V((p, m) \<mapsto> frz_cv \<sigma> V \<phi>1 NL wL jfrz))
    (Mapping.update (p, m) (replicate (length ts) (hd ?a1)) db)"
  proof (rule kmaux_wf_envs_update_frz[OF envs fv safe1 wty1])
    show "list_all2 (\<lambda>k Y. Y = {v. length v = m \<and> frz_cv \<sigma> V \<phi>1 NL wL jfrz v k})
      [j0..<j0 + (j - j0)] (replicate (length ts) (hd ?a1))"
      using kmaux_qtable_frz_alpha[OF hd fv(2)] wL jfrz_j0 g
      by (auto simp: list_all2_conv_all_nth frz_cv_ge)
  qed (use qtableD(5)[OF hd] in \<open>auto dest: frz_val_sat\<close>)
  show "kgood n ks j ts (Mapping.update (p, m) (replicate (length ts) (hd ?a1)) db) \<rho>L"
    by (rule kgoodI[OF g wfL _ wty2 ks]) (use envs' g(1) in simp)
qed


text \<open>The two live copies of the separable evaluation, fed the new time points with the table
  @{term L} and with the empty table.\<close>

lemma kgood_MFrz_sep:
  assumes g0: "kgood n ks j ts db (MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)"
    and sx: "sx = FSSep L nL pX buf rg bo tk Lr"
  shows "kgood n ks j ts (Mapping.update (p, m) (replicate (length ts) L) db) \<rho>S \<and>
    kgood n ks j ts (Mapping.update (p, m) (replicate (length ts) {}) db) \<rho>E"
  using g0
proof (rule kgood_MFrzE)
  fix S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1
  assume g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wty1: "S, E' \<turnstile> \<phi>1" and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe1: "safe_formula \<phi>1"
    and ks: "ks = Formula.fv_list \<psi>1"
    and jfrz: "jfrz = progress \<sigma> P (Formula.Frz p \<phi>1 \<psi>1) j0"
    and sep: "\<And>L nL pX buf rg bo tk Lr. sx = FSSep L nL pX buf rg bo tk Lr \<Longrightarrow>
      lv = None \<and> frz_tab \<sigma> V m \<phi>1 L \<and> frz_tab \<sigma> V m \<phi>1 Lr \<and> (\<forall>\<alpha> \<in> set \<alpha>s. \<alpha> \<subseteq> L) \<and>
      (\<exists>wS NS wE NE. (\<forall>k<wS. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        (\<forall>k<wE. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)) \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NS wS (\<lambda>v k. v \<in> L))) n R \<rho>S \<psi>1 \<and>
        kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NE wE (\<lambda>_ _. False))) n R \<rho>E \<psi>1)"
  from sep[OF sx] obtain wS NS wE NE where tL: "frz_tab \<sigma> V m \<phi>1 L"
    and winS: "\<forall>k<wS. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)"
    and winE: "\<forall>k<wE. enat (\<tau> \<sigma> k) + past_reach \<psi>1 < enat (\<tau> \<sigma> jfrz)"
    and wfS: "kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NS wS (\<lambda>v k. v \<in> L))) n R \<rho>S \<psi>1"
    and wfE: "kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> j0)) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NE wE (\<lambda>_ _. False))) n R \<rho>E \<psi>1"
    by blast
  have pm: "pred_mapping (\<lambda>x. x \<le> j0) P"
    by (rule wf_envs_P_simps(1)[OF envs])
  have jfrz_j0: "jfrz \<le> j0"
    unfolding jfrz by (rule progress_le_gen[OF pm])
  have wS: "wS \<le> j0" and wE: "wE \<le> j0"
    using frz_win_le[OF winS] frz_win_le[OF winE] jfrz_j0 by simp_all
  have lts: "length ts = j - j0"
    using g by simp
  have envsS: "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> j0 (j - j0) (P((p, m) \<mapsto> j0))
    (P'((p, m) \<mapsto> j0 + (j - j0))) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NS wS (\<lambda>v k. v \<in> L)))
    (Mapping.update (p, m) (replicate (length ts) L) db)"
  proof (rule kmaux_wf_envs_update_frz[OF envs fv safe1 wty1])
    show "list_all2 (\<lambda>k Y. Y = {v. length v = m \<and> frz_ext \<sigma> V \<phi>1 NS wS (\<lambda>v k. v \<in> L) v k})
      [j0..<j0 + (j - j0)] (replicate (length ts) L)"
      using tL wS lts by (auto simp: list_all2_conv_all_nth frz_ext_ge frz_tab_def)
  qed (use tL frz_tab_sup[OF tL] in \<open>auto simp: frz_tab_def dest: frz_ext_sat\<close>)
  have envsE: "wf_envs (S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))) \<sigma> j0 (j - j0) (P((p, m) \<mapsto> j0))
    (P'((p, m) \<mapsto> j0 + (j - j0))) (V((p, m) \<mapsto> frz_ext \<sigma> V \<phi>1 NE wE (\<lambda>_ _. False)))
    (Mapping.update (p, m) (replicate (length ts) {}) db)"
  proof (rule kmaux_wf_envs_update_frz[OF envs fv safe1 wty1])
    show "list_all2 (\<lambda>k Y. Y = {v. length v = m \<and> frz_ext \<sigma> V \<phi>1 NE wE (\<lambda>_ _. False) v k})
      [j0..<j0 + (j - j0)] (replicate (length ts) {})"
      using wE lts by (auto simp: list_all2_conv_all_nth frz_ext_ge)
  qed (use frz_sup_False in \<open>auto dest: frz_ext_sat\<close>)
  show ?thesis
  proof
    show "kgood n ks j ts (Mapping.update (p, m) (replicate (length ts) L) db) \<rho>S"
      by (rule kgoodI[OF g wfS _ wty2 ks]) (use envsS g(1) in simp)
    show "kgood n ks j ts (Mapping.update (p, m) (replicate (length ts) {}) db) \<rho>E"
      by (rule kgoodI[OF g wfE _ wty2 ks]) (use envsE g(1) in simp)
  qed
qed


subsection \<open>The rounds of a recursive let\<close>

text \<open>The state of the rounds of @{const letpast_meval0}, read through the kernel's invariant
  @{const kletpast_meval_invar}.\<close>

definition lpgood :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data table list \<Rightarrow> event_data table list \<Rightarrow>
    Formula.name \<times> nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  "lpgood m kks j i ys xs pm ts db \<phi> \<longleftrightarrow> (\<exists>S E' \<sigma> P P' V \<phi>1 (n :: nat) k. snd pm = m \<and> length ts \<le> j \<and>
     ts = map (\<tau> \<sigma>) [j - length ts..<j] \<and>
     kletpast_meval_invar n V \<sigma> P \<phi>1 m j i ys xs (fst pm) ts db \<phi> k \<and>
     wf_envs S \<sigma> (j - length ts) (length ts) P P' V db \<and>
     safe_letpast pm \<phi>1 \<le> PastRec \<and> m = Formula.nfv \<phi>1 \<and> {0..<m} \<subseteq> Formula.fv \<phi>1 \<and> safe_formula \<phi>1 \<and>
     kks = Formula.fv_list \<phi>1 \<and> S(pm \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1)"

lemma lpgoodE:
  assumes "lpgood m kks j i ys xs (p, m) ts db \<phi>"
  obtains S E' \<sigma> P P' V \<phi>1 and n :: nat and k where "length ts \<le> j" "ts = map (\<tau> \<sigma>) [j - length ts..<j]"
    "kletpast_meval_invar n V \<sigma> P \<phi>1 m j i ys xs p ts db \<phi> k"
    "wf_envs S \<sigma> (j - length ts) (length ts) P P' V db"
    "safe_letpast (p, m) \<phi>1 \<le> PastRec" "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1"
    "safe_formula \<phi>1" "kks = Formula.fv_list \<phi>1" "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
  using assms unfolding lpgood_def by fastforce

text \<open>A round's call: the bound formula, on the database in which the bound predicate holds the
  previous round's tables, is a good call, and its tables are those of the recursion.\<close>

lemma lpgood_correct:
  assumes "lpgood m kks j i ys xs (p, m) ts db \<phi>"
  obtains S E' \<sigma> P P' V \<phi>1 and n :: nat and k where
    "kgood m kks j ts (Mapping.update (p, m) xs db) \<phi>"
    "kletpast_meval_invar n V \<sigma> P \<phi>1 m j i ys xs p ts db \<phi> k"
    "wf_envs S \<sigma> (j - length ts) (length ts) P P' V db"
    "length ts \<le> j" "ts = map (\<tau> \<sigma>) [j - length ts..<j]" "safe_letpast (p, m) \<phi>1 \<le> PastRec"
    "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" "safe_formula \<phi>1" "kks = Formula.fv_list \<phi>1"
    "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
    "case apfst (map (reorder [0..<m] kks)) (meval j m ts (Mapping.update (p, m) xs db) \<phi>) of (xs', \<phi>\<^sub>n) \<Rightarrow>
      kwf_mformula \<sigma> j (P'((p, m) \<mapsto> i + length xs))
        (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1))) m UNIV \<phi>\<^sub>n \<phi>1 \<and>
      list_all2 (\<lambda>i. qtable [0..<m] (mem_restr UNIV [0..<m])
        (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1) (val m [0..<m] v) i))
        [progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>1 (j - length ts)..<progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>1 j] xs'"
proof -
  obtain S E' \<sigma> P P' V \<phi>1 and n :: nat and k where len: "length ts \<le> j" and ts: "ts = map (\<tau> \<sigma>) [j - length ts..<j]"
    and invar: "kletpast_meval_invar n V \<sigma> P \<phi>1 m j i ys xs p ts db \<phi> k"
    and envs: "wf_envs S \<sigma> (j - length ts) (length ts) P P' V db"
    and safe: "safe_letpast (p, m) \<phi>1 \<le> PastRec" and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1"
    and safe1: "safe_formula \<phi>1" and kks: "kks = Formula.fv_list \<phi>1"
    and wty: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
    using assms by (rule lpgoodE)
  let ?P = "P((p, m) \<mapsto> i)"
  let ?V = "V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1))"
  let ?S = "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1))"
  let ?P' = "P'((p, m) \<mapsto> i + length xs)"
  let ?Q = "\<lambda>i. qtable [0..<m] (mem_restr UNIV [0..<m])
    (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>1) (val m [0..<m] v) i)"
  have pm: "pred_mapping (\<lambda>x. x \<le> j - length ts) P" and rel: "rel_mapping (\<le>) P P'"
    using wf_envs_P_simps[OF envs] by simp_all
  from invar have wf: "kwf_mformula \<sigma> (j - length ts) ?P ?V m UNIV \<phi> \<phi>1"
    and le_a: "i + length xs \<le> progress \<sigma> ?P \<phi>1 (j - length ts)"
    and le_lp: "i + length xs \<le> letpast_progress \<sigma> P (p, m) \<phi>1 (j - length ts)"
    and xs_a: "list_all2 ?Q [i..<progress \<sigma> ?P \<phi>1 (j - length ts)] xs"
    unfolding kmaux_letpast_meval_invar_def Let_def by simp_all
  have i_j: "i + length xs \<le> j - length ts"
    using le_lp letpast_progress_le[OF pm, of \<sigma> "(p, m)" \<phi>1] by linarith
  have "length xs = progress \<sigma> ?P \<phi>1 (j - length ts) - i"
    using list_all2_lengthD[OF xs_a] by simp
  then have xs: "list_all2 ?Q [i..<i + length xs] xs"
    using xs_a by (cases "i \<le> progress \<sigma> ?P \<phi>1 (j - length ts)") simp_all
  have envs': "wf_envs ?S \<sigma> (j - length ts) (length ts) ?P ?P' ?V (Mapping.update (p, m) xs db)"
    by (rule wf_envs_update2[OF envs fv rel _ _ _ xs safe1 wty]) (use i_j in simp_all)
  have kg: "kgood m kks j ts (Mapping.update (p, m) xs db) \<phi>"
    by (rule kgoodI[OF _ _ wf _ wty kks]) (use len ts envs' in simp_all)
  have sat_letpast: "Formula.sat \<sigma> ?V w k \<phi>1 =
    letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1) w k" for w k
    by (subst letpast_sat.simps) (rule V_subst_letpast[OF safe], simp)
  have "case meval (j - length ts + length ts) m (map (\<tau> \<sigma>) [j - length ts..<j - length ts + length ts])
      (Mapping.update (p, m) xs db) \<phi> of (xs', \<phi>\<^sub>n) \<Rightarrow>
      kwf_mformula \<sigma> (j - length ts + length ts) ?P' ?V m UNIV \<phi>\<^sub>n \<phi>1 \<and>
      list_all2 (\<lambda>i. sat_table \<sigma> ?V m UNIV (Formula.fv_list \<phi>1) i \<phi>1)
        [progress \<sigma> ?P \<phi>1 (j - length ts)..<progress \<sigma> ?P' \<phi>1 (j - length ts + length ts)] xs'"
    by (rule kmaux_meval_correct[OF wf envs' wty])
  then have raw: "case meval j m ts (Mapping.update (p, m) xs db) \<phi> of (xs', \<phi>\<^sub>n) \<Rightarrow>
      kwf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>1 \<and>
      list_all2 (\<lambda>i. sat_table \<sigma> ?V m UNIV (Formula.fv_list \<phi>1) i \<phi>1)
        [progress \<sigma> ?P \<phi>1 (j - length ts)..<progress \<sigma> ?P' \<phi>1 j] xs'"
    using len ts by simp
  obtain ys0 \<phi>n where ev: "meval j m ts (Mapping.update (p, m) xs db) \<phi> = (ys0, \<phi>n)"
    by fastforce
  from raw ev have wf_n: "kwf_mformula \<sigma> j ?P' ?V m UNIV \<phi>n \<phi>1"
    and ys0: "list_all2 (\<lambda>i. sat_table \<sigma> ?V m UNIV (Formula.fv_list \<phi>1) i \<phi>1)
      [progress \<sigma> ?P \<phi>1 (j - length ts)..<progress \<sigma> ?P' \<phi>1 j] ys0"
    by simp_all
  have "list_all2 (\<lambda>i. sat_table \<sigma> ?V m UNIV [0..<m] i \<phi>1)
    [progress \<sigma> ?P \<phi>1 (j - length ts)..<progress \<sigma> ?P' \<phi>1 j] (map (reorder [0..<m] kks) ys0)"
    unfolding list.rel_map kks by (rule list.rel_mono_strong[OF ys0]) (rule sat_table_reorder_upt[OF _ fv(2,1)])
  with wf_n have res: "case apfst (map (reorder [0..<m] kks)) (meval j m ts (Mapping.update (p, m) xs db) \<phi>) of
      (xs', \<phi>\<^sub>n) \<Rightarrow> kwf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>1 \<and>
      list_all2 ?Q [progress \<sigma> ?P \<phi>1 (j - length ts)..<progress \<sigma> ?P' \<phi>1 j] xs'"
    unfolding ev sat_letpast by simp
  show ?thesis
    by (rule that[OF kg invar envs len ts safe fv safe1 kks wty res])
qed

lemma lpgood_call: "lpgood m kks j i ys xs (p, m) ts db \<phi> \<Longrightarrow> kgood m kks j ts (Mapping.update (p, m) xs db) \<phi>"
  by (erule lpgood_correct)

lemma lpgood_step:
  assumes lp: "lpgood m kks j i ys xs (p, m) ts db \<phi>"
    and e: "apfst (map (reorder [0..<m] kks)) (meval j m ts (Mapping.update (p, m) xs db) \<phi>) = (ys', \<phi>n)"
    and ne: "ys' \<noteq> []" and lt: "Suc (i + length xs) < j"
  shows "lpgood m kks j (i + length xs) (ys @ ys') ys' (p, m) [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>n"
proof -
  from lp obtain S E' \<sigma> P P' V \<phi>1 and n :: nat and k where
    invar: "kletpast_meval_invar n V \<sigma> P \<phi>1 m j i ys xs p ts db \<phi> k"
    and envs: "wf_envs S \<sigma> (j - length ts) (length ts) P P' V db" and len: "length ts \<le> j"
    and safe: "safe_letpast (p, m) \<phi>1 \<le> PastRec" and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1"
    and safe1: "safe_formula \<phi>1" and kks: "kks = Formula.fv_list \<phi>1"
    and wty: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
    and res: "case apfst (map (reorder [0..<m] kks)) (meval j m ts (Mapping.update (p, m) xs db) \<phi>) of (xs', \<phi>\<^sub>n) \<Rightarrow>
      kwf_mformula \<sigma> j (P'((p, m) \<mapsto> i + length xs))
        (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1))) m UNIV \<phi>\<^sub>n \<phi>1 \<and>
      list_all2 (\<lambda>i. qtable [0..<m] (mem_restr UNIV [0..<m])
        (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1) (val m [0..<m] v) i))
        [progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>1 (j - length ts)..<progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>1 j] xs'"
    by (rule lpgood_correct)
  have pm: "pred_mapping (\<lambda>x. x \<le> j - length ts) P" "pred_mapping (\<lambda>x. x \<le> j) P'"
    and rel: "rel_mapping (\<le>) P P'"
    using wf_envs_P_simps[OF envs] len by simp_all
  have invar': "kletpast_meval_invar n V \<sigma> P' \<phi>1 m j (i + length xs) (ys @ ys') ys' p []
      (Mapping.map_values (\<lambda>_ _. []) db) \<phi>n k"
    by (rule kmaux_invar_recursion_invar[OF pm rel res invar e[symmetric] ne]) (use lt in simp)
  have envs': "wf_envs S \<sigma> (j - length []) (length []) P' P' V (Mapping.map_values (\<lambda>_ _. []) db)"
    using wf_envs_empty[OF envs] len by simp
  show ?thesis
    unfolding lpgood_def
    by (intro exI[of _ S] exI[of _ E'] exI[of _ \<sigma>] exI[of _ P'] exI[of _ P'] exI[of _ V] exI[of _ \<phi>1]
        exI[of _ n] exI[of _ k]) (use invar' envs' safe fv safe1 kks wty in simp)
qed

text \<open>The rounds start from the node's state, and the body is evaluated on the database in which
  the bound predicate holds the rounds' tables.\<close>

lemma kgood_MLetPastE:
  assumes "kgood n ks j ts db (MLetPast p m kks \<phi> \<psi> i buf)"
  obtains S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1 where "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    "kwf_mformula \<sigma> j0 P V n R (MLetPast p m kks \<phi> \<psi> i buf) (Formula.LetPast p \<phi>1 \<psi>1)"
    "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
    "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" "safe_letpast (p, m) \<phi>1 \<le> PastRec"
    "safe_formula \<phi>1" "ks = Formula.fv_list \<psi>1" "kks = Formula.fv_list \<phi>1"
    "kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> letpast_progress \<sigma> P (p, m) \<phi>1 j0))
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1))) n R \<psi> \<psi>1"
proof -
  obtain S E \<sigma> j0 P P' V R \<chi> where g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MLetPast p m kks \<phi> \<psi> i buf) \<chi>"
    and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db" and wty: "S, E \<turnstile> \<chi>" and ks: "ks = Formula.fv_list \<chi>"
    using assms by (rule kgoodE)
  from wf obtain \<phi>1 \<psi>1 where \<chi>: "\<chi> = Formula.LetPast p \<phi>1 \<psi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1"
    and wf2: "kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> letpast_progress \<sigma> P (p, m) \<phi>1 j0))
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1))) n R \<psi> \<psi>1"
    and safe: "safe_letpast (p, m) \<phi>1 \<le> PastRec" and safe1: "safe_formula \<phi>1"
    and kks: "kks = Formula.fv_list \<phi>1"
    by (cases rule: kmaux_wf_mformula_cases) auto
  from wty obtain E' where wty1: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
    and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    unfolding \<chi> fv by (cases pred: wty_formula) simp_all
  show ?thesis
    by (rule that[OF g envs wf[unfolded \<chi>] wty1 wty2 fv safe safe1 _ kks wf2]) (simp add: ks \<chi>)
qed

lemma kgood_MLetPast_init:
  assumes "kgood n ks j ts db (MLetPast p m kks \<phi> \<psi> i buf)"
  shows "lpgood m kks j i [] (list_of_option buf) (p, m) ts db \<phi>"
  using assms
proof (rule kgood_MLetPastE)
  fix S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1
  assume g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MLetPast p m kks \<phi> \<psi> i buf) (Formula.LetPast p \<phi>1 \<psi>1)"
    and wty1: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe: "safe_letpast (p, m) \<phi>1 \<le> PastRec"
    and safe1: "safe_formula \<phi>1" and kks: "kks = Formula.fv_list \<phi>1"
  have len: "length ts = j - j0" and j0: "j - length ts = j0"
    using g by simp_all
  have pm: "pred_mapping (\<lambda>x. x \<le> j - length ts) P"
    using wf_envs_P_simps[OF envs] j0 by simp
  have invar: "kletpast_meval_invar n V \<sigma> P \<phi>1 m j i [] (list_of_option buf) p ts db \<phi>
      (letpast_progress \<sigma> P (p, m) \<phi>1 (j - length ts))"
    by (rule kmaux_letpast_meval_invar_init[OF pm]) (use wf j0 in simp)
  show "lpgood m kks j i [] (list_of_option buf) (p, m) ts db \<phi>"
    unfolding lpgood_def
    by (intro exI[of _ S] exI[of _ E'] exI[of _ \<sigma>] exI[of _ P] exI[of _ P'] exI[of _ V] exI[of _ \<phi>1]
        exI[of _ n] exI[of _ "letpast_progress \<sigma> P (p, m) \<phi>1 (j - length ts)"])
      (use g len j0 invar envs safe fv safe1 kks wty1 in simp)
qed

lemma kgood_MLetPast_body:
  assumes g0: "kgood n ks j ts db (MLetPast p m kks \<phi> \<psi> i buf)"
    and e: "letpast_meval m kks j i [] (list_of_option buf) (p, m) ts db \<phi> = (as, i2, buf2, \<phi>2)"
  shows "kgood n ks j ts (Mapping.update (p, m) as db) \<psi>"
  using g0
proof (rule kgood_MLetPastE)
  fix S E E' \<sigma> j0 P P' V R \<phi>1 \<psi>1
  assume g: "j0 \<le> j" "ts = map (\<tau> \<sigma>) [j0..<j]" and envs: "wf_envs S \<sigma> j0 (j - j0) P P' V db"
    and wf: "kwf_mformula \<sigma> j0 P V n R (MLetPast p m kks \<phi> \<psi> i buf) (Formula.LetPast p \<phi>1 \<psi>1)"
    and wty1: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E' \<turnstile> \<phi>1"
    and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1)), E \<turnstile> \<psi>1"
    and fv: "m = Formula.nfv \<phi>1" "{0..<m} \<subseteq> Formula.fv \<phi>1" and safe: "safe_letpast (p, m) \<phi>1 \<le> PastRec"
    and safe1: "safe_formula \<phi>1" and ks: "ks = Formula.fv_list \<psi>1" and kks: "kks = Formula.fv_list \<phi>1"
    and wf2: "kwf_mformula \<sigma> j0 (P((p, m) \<mapsto> letpast_progress \<sigma> P (p, m) \<phi>1 j0))
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1))) n R \<psi> \<psi>1"
  have len: "length ts = j - j0" and j0: "j - length ts = j0"
    using g by simp_all
  have pm: "pred_mapping (\<lambda>x. x \<le> j - length ts) P" and pm': "pred_mapping (\<lambda>x. x \<le> j) P'"
    and rel: "rel_mapping (\<le>) P P'"
    using wf_envs_P_simps[OF envs] j0 g(1) by simp_all
  from wf have wf1: "kwf_mformula \<sigma> (j - length ts) (P((p, m) \<mapsto> i))
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1))) m UNIV \<phi> \<phi>1"
    unfolding j0 by (cases rule: kmaux_wf_mformula_cases) auto
  have invar: "kletpast_meval_invar n V \<sigma> P \<phi>1 m j i [] (list_of_option buf) p ts db \<phi>
      (letpast_progress \<sigma> P (p, m) \<phi>1 (j - length ts))"
    by (rule kmaux_letpast_meval_invar_init[OF pm]) (use wf j0 in simp)
  have envs0: "wf_envs S \<sigma> (j - length ts) (length ts) P P' V db"
    using envs j0 len by simp
  have post: "kletpast_meval_post n V \<sigma> P' \<phi>1 m j i2 as buf2 p \<phi>2
      (letpast_progress \<sigma> P (p, m) \<phi>1 (j - length ts))"
  proof (rule kmaux_letpast_meval_invar_post[OF safe pm pm' rel fv wf1 envs0 _ _ wty1 safe1 kks
        invar e[symmetric]], goal_cases)
    case (1 xs db \<phi>_m us P P' V S E)
    from 1(5) len g have eq1: "j - length us + length us = j"
      and eq2: "map (\<tau> \<sigma>) [j - length us..<j] = us"
      by auto
    from kmaux_meval_correct[OF 1(2) 1(3) 1(4)] show ?case
      unfolding eq1 eq2 .
  qed (use len g(1) in simp)
  then have full: "list_all2 (\<lambda>i. qtable [0..<m] (mem_restr UNIV [0..<m])
        (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1) (val m [0..<m] v) i))
      [letpast_progress \<sigma> P (p, m) \<phi>1 j0..<letpast_progress \<sigma> P' (p, m) \<phi>1 (j0 + (j - j0))] as"
    using j0 g(1) by (simp add: kmaux_letpast_meval_post_def)
  show "kgood n ks j ts (Mapping.update (p, m) as db) \<psi>"
    by (rule kgoodI[OF g wf2 wf_envs_update_sup[OF envs fv full safe1 wty1] wty2 ks])
qed


subsection \<open>The monitor's steps\<close>

text \<open>A step of the kernel's monitor from a well-formed state is a good call of its formula.\<close>

lemma kgood_mstep:
  assumes wf: "kwf_mstate S E \<phi> \<pi> R st" and wty: "wty_db S (fst tdb)"
    and le: "last_ts \<pi> \<le> snd tdb" and fin: "finite (fst tdb)"
  shows "kgood (mstate_n st) (Formula.fv_list \<phi>) (mstate_j st + 1) [snd tdb] (mk_db (fst tdb)) (mstate_m st)"
proof -
  from wf have wtyp: "wty_prefix S \<pi>" and wty\<phi>: "S, E \<turnstile> \<phi>" and j: "mstate_j st = plen \<pi>"
    unfolding kmaux_wf_mstate_def by auto
  obtain \<sigma> where p: "prefix_of (psnoc \<pi> tdb) \<sigma>" and wtys: "wty_trace S \<sigma>"
    using ex_prefix_of_wty[OF wty_psnoc[OF wtyp wty le]] by blast
  from prefix_of_psnocE[OF p le] have p\<pi>: "prefix_of \<pi> \<sigma>"
    and G: "\<Gamma> \<sigma> (plen \<pi>) = fst tdb" and T: "\<tau> \<sigma> (plen \<pi>) = snd tdb"
    by auto
  from wf p\<pi> wtys have wfm: "kwf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (mstate_n st) R (mstate_m st) \<phi>"
    unfolding kmaux_wf_mstate_def by auto
  have envs: "wf_envs S \<sigma> (plen \<pi>) 1 Map.empty Map.empty Map.empty (mk_db (fst tdb))"
    using wf_envs_mk_db[OF wtys, of "plen \<pi>"] fin G by simp
  show ?thesis
    by (rule kgoodI[OF _ _ wfm _ wty\<phi> refl]) (use envs T j in simp_all)
qed

(*<*)
end
(*>*)
