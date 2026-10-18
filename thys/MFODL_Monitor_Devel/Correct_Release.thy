(*<*)
theory Correct_Release
  imports
    Correct_Trigger
begin
(*>*)


subsection \<open> Release \<close>

text \<open>The release with 0 in its interval is evaluated natively (@{const update_release}). The
  auxiliary list holds, for each time point @{term i} whose verdict is pending, the tuples that
  are still waiting to be released and the tuples that are still alive, both over the columns of
  the right operand. The left operand is the formula the monitor evaluates; with @{term pos}
  false, the release is by the points where it does not hold.\<close>

definition "Releasep pos \<phi> I \<psi> \<equiv> Formula.Release (if pos then \<phi> else Formula.Neg \<phi>) I \<psi>"

definition wf_release_auxlist :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> bool \<Rightarrow>
    ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula \<Rightarrow> event_data muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne \<longleftrightarrow>
    list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      qtable (Formula.fv_list \<psi>) (mem_restr R (Formula.fv_list \<psi>)) (\<lambda>v.
        \<forall>j\<in>{i..<ne+length auxlist}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
          Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) j \<psi> \<and>
          (if pos then \<not> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) j \<phi>
           else Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) j \<phi>)) r1 \<and>
      qtable (Formula.fv_list \<psi>) (mem_restr R (Formula.fv_list \<psi>)) (\<lambda>v.
        \<forall>j\<in>{i..<ne+length auxlist}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
          Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) j \<psi> \<or>
          (\<exists>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>
            else \<not> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>)) r2)
      auxlist [ne..<ne+length auxlist]"

text \<open>The left operand the monitor evaluates (@{const release_left}) gives the release the
  same verdicts and the same progress.\<close>

lemma release_left_cases: "release_left \<alpha> \<psi> = (\<phi>, pos) \<Longrightarrow>
  pos \<and> \<phi> = \<alpha> \<and> safe_formula \<alpha> \<or> \<not> pos \<and> \<alpha> = Formula.Neg \<phi> \<and> safe_formula \<phi> \<or>
  pos \<and> \<phi> = Formula.And \<psi> \<alpha>"
  by (auto simp: release_left_def split: if_splits formula.splits)

lemma sat_release_left:
  assumes "release_left \<alpha> \<psi> = (\<phi>, pos)" "mem I 0"
  shows "Formula.sat \<sigma> V v i (Releasep pos \<phi> I \<psi>) \<longleftrightarrow> Formula.sat \<sigma> V v i (Formula.Release \<alpha> I \<psi>)"
  using release_left_cases[OF assms(1)] sat_release_conj_0[OF assms(2), where \<psi>=\<psi> and \<phi>=\<alpha>]
  by (elim disjE conjE) (simp_all add: Releasep_def del: sat.simps)

lemma progress_release_left_min: "release_left \<alpha> \<psi> = (\<phi>, pos) \<Longrightarrow>
  min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) = min (progress \<sigma> P \<alpha> j) (progress \<sigma> P \<psi> j)"
  by (auto simp: min.commute min.left_commute dest!: release_left_cases)

lemma progress_release_left:
  assumes "release_left \<alpha> \<psi> = (\<phi>, pos)" "mem I 0"
  shows "progress \<sigma> P (Releasep pos \<phi> I \<psi>) j = progress \<sigma> P (Formula.Release \<alpha> I \<psi>) j"
proof -
  have "min (progress \<sigma> P (if pos then \<phi> else Formula.Neg \<phi>) j) (progress \<sigma> P \<psi> j) =
    min (progress \<sigma> P \<alpha> j) (progress \<sigma> P \<psi> j)"
    using progress_release_left_min[OF assms(1)] by (cases pos) simp_all
  then show ?thesis
    by (simp only: Releasep_def progress.simps assms(2) simp_thms if_True)
qed

lemma fv_release_left: "release_left \<alpha> \<psi> = (\<phi>, pos) \<Longrightarrow> Formula.fv \<alpha> \<subseteq> Formula.fv \<psi> \<Longrightarrow>
  Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
  by (auto dest!: release_left_cases)

lemma safe_release_left: "release_left \<alpha> \<psi> = (\<phi>, pos) \<Longrightarrow> safe_formula (Formula.And \<psi> \<alpha>) \<Longrightarrow>
  safe_formula \<phi>"
  by (auto dest!: release_left_cases)

lemma wty_release_left: "release_left \<alpha> \<psi> = (\<phi>, pos) \<Longrightarrow> S, E \<turnstile> \<alpha> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow>
  S, E \<turnstile> \<phi>"
  by (auto dest!: release_left_cases dest: wty_formula_NegD intro: wty_formula.intros)

lemma wf_release_auxlist_Nil: "wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> [] ne"
  unfolding wf_release_auxlist_def by simp

lemma qtable_diff: "qtable cs P Q1 X \<Longrightarrow> qtable cs P Q2 Y \<Longrightarrow>
  (\<And>x. wf_tuple cs x \<Longrightarrow> P x \<Longrightarrow> Q x = (Q1 x \<and> \<not> Q2 x)) \<Longrightarrow> qtable cs P Q (X - Y)"
  unfolding qtable_def table_def by blast

lemma length_update_release: "length (update_release args rel1 rel2 nt aux) = Suc (length aux)"
  unfolding update_release_def by simp

text \<open>A tuple stays alive at a new point of the window if it satisfies the right operand there,
  or if it is no longer waiting to be released.\<close>

lemma release_alive_step:
  assumes win: "\<And>k. i \<le> k \<Longrightarrow> k \<le> m \<Longrightarrow> mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" and "i \<le> m"
  shows "(\<forall>j\<in>{i..<Suc m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<or> (\<exists>k\<in>{i..<j}. L k)) \<longleftrightarrow>
    (\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<or> (\<exists>k\<in>{i..<j}. L k)) \<and>
    \<not> ((\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<and> \<not> L j) \<and> \<not> S m)"
proof
  assume A: "\<forall>j\<in>{i..<Suc m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<or> (\<exists>k\<in>{i..<j}. L k)"
  then have m: "S m \<or> (\<exists>k\<in>{i..<m}. L k)"
    using win[of m] \<open>i \<le> m\<close> by auto
  show "(\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<or> (\<exists>k\<in>{i..<j}. L k)) \<and>
    \<not> ((\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<and> \<not> L j) \<and> \<not> S m)"
  proof (intro conjI notI)
    show "\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<or> (\<exists>k\<in>{i..<j}. L k)"
      using A by auto
  next
    assume P: "(\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<and> \<not> L j) \<and> \<not> S m"
    with m obtain k where "k \<in> {i..<m}" "L k"
      by blast
    with P win[of k] show False
      by auto
  qed
next
  assume B: "(\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<or> (\<exists>k\<in>{i..<j}. L k)) \<and>
    \<not> ((\<forall>j\<in>{i..<m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<and> \<not> L j) \<and> \<not> S m)"
  show "\<forall>j\<in>{i..<Suc m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> S j \<or> (\<exists>k\<in>{i..<j}. L k)"
  proof (intro ballI impI)
    fix j
    assume j: "j \<in> {i..<Suc m}" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    show "S j \<or> (\<exists>k\<in>{i..<j}. L k)"
    proof (cases "j < m")
      case True
      then show ?thesis
        using B j by auto
    next
      case False
      with j have "j = m"
        by auto
      show ?thesis
      proof (cases "S m")
        case False
        with B obtain j' where j': "j' \<in> {i..<m}" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "\<not> S j' \<or> L j'"
          by blast
        then show ?thesis
          using B \<open>j = m\<close> by fastforce
      qed (simp add: \<open>j = m\<close>)
    qed
  qed
qed

lemma wf_update_release_auxlist:
  assumes pre: "wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne"
    and qtable1: "sat_table \<sigma> V n R (Formula.fv_list \<phi>) (ne + length auxlist) \<phi> rel1"
    and qtable2: "sat_table \<sigma> V n R (Formula.fv_list \<psi>) (ne + length auxlist) \<psi> rel2"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and mem: "mem I 0"
    and args_ivl: "args_ivl args = I"
    and args_pos: "args_pos args = pos"
    and args_L: "args_L args = Formula.fv_list \<phi>"
    and args_R: "args_R args = Formula.fv_list \<psi>"
  shows "wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> (update_release args rel1 rel2 (\<tau> \<sigma> (ne + length auxlist)) auxlist) ne"
  unfolding wf_release_auxlist_def length_update_release
  unfolding update_release_def list.rel_map add_Suc_right upt.simps eqTrueI[OF le_add1] if_True
proof (rule list_all2_appendI, unfold list.rel_map, goal_cases old new)
  case old
  let ?m = "ne + length auxlist"
  let ?\<phi>s = "Formula.fv_list \<phi>" and ?\<psi>s = "Formula.fv_list \<psi>"
  let ?sat = "\<lambda>v k \<alpha>. Formula.sat \<sigma> V (val n ?\<psi>s v) k \<alpha>"
  let ?L = "\<lambda>v k. if pos then ?sat v k \<phi> else \<not> ?sat v k \<phi>"
  have sat_\<phi>: "Formula.sat \<sigma> V (val n ?\<phi>s (restrict ?\<phi>s ?\<psi>s x)) k \<phi> \<longleftrightarrow> ?sat x k \<phi>" for x k
    by (rule sat_restrict) simp
  show ?case
  proof (rule list.rel_mono_strong[OF pre[unfolded wf_release_auxlist_def]], goal_cases mono)
    case (mono x i)
    obtain t a1 a2 where x: "x = (t, a1, a2)"
      by (cases x)
    from mono(2) have "i < ?m"
      by simp
    from mono(3)[unfolded x] have t: "t = \<tau> \<sigma> i"
      and A1: "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. \<forall>j\<in>{i..<?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
        ?sat v j \<psi> \<and> (if pos then \<not> ?sat v j \<phi> else ?sat v j \<phi>)) a1"
      and A2: "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. \<forall>j\<in>{i..<?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
        ?sat v j \<psi> \<or> (\<exists>k\<in>{i..<j}. ?L v k)) a2"
      by auto
    show ?case
    proof (cases "memR I (\<tau> \<sigma> ?m - \<tau> \<sigma> i)")
      case True
      have win: "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" if "i \<le> k" "k \<le> ?m" for k
        using mem True that memR_antimono[of I "\<tau> \<sigma> ?m - \<tau> \<sigma> i" "\<tau> \<sigma> k - \<tau> \<sigma> i"]
          diff_le_mono[OF \<tau>_mono[of k ?m \<sigma>], of "\<tau> \<sigma> i"]
        by auto
      have A1': "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. (\<forall>j\<in>{i..<?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
        ?sat v j \<psi> \<and> (if pos then \<not> ?sat v j \<phi> else ?sat v j \<phi>)) \<and> ?sat v ?m \<psi>) (a1 \<inter> rel2)"
        by (rule qtable_inter[OF A1 qtable2]) simp
      have B1: "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. \<forall>j\<in>{i..<Suc ?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
        ?sat v j \<psi> \<and> (if pos then \<not> ?sat v j \<phi> else ?sat v j \<phi>)) (join ?\<psi>s (a1 \<inter> rel2) (\<not> pos) ?\<phi>s rel1)"
        by (rule qtable_join_sub[OF A1' qtable1 distinct_fvi_list distinct_fvi_list])
          (use fvi_subset win[of ?m] \<open>i < ?m\<close> in \<open>auto simp: sat_\<phi> less_Suc_eq\<close>)
      have D: "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. (\<forall>j\<in>{i..<?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
        ?sat v j \<psi> \<and> \<not> ?L v j) \<and> \<not> ?sat v ?m \<psi>) (a1 - rel2)"
        by (rule qtable_diff[OF A1 qtable2]) (cases pos; simp)
      have B2: "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. \<forall>j\<in>{i..<Suc ?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
        ?sat v j \<psi> \<or> (\<exists>k\<in>{i..<j}. ?L v k)) (a2 - (a1 - rel2))"
        by (rule qtable_diff[OF A2 D])
          (rule release_alive_step[OF win], simp_all add: \<open>i < ?m\<close> less_imp_le)
      show ?thesis
        unfolding x prod.case args_ivl args_pos args_L args_R if_P[OF True[folded t]]
        using t B1 B2 by simp
    next
      case False
      have nm: "\<not> mem I (\<tau> \<sigma> ?m - \<tau> \<sigma> i)"
        using False by auto
      have eq: "(\<forall>j\<in>{i..<Suc ?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Q j) \<longleftrightarrow>
        (\<forall>j\<in>{i..<?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Q j)" for Q
        using nm by (auto simp: less_Suc_eq)
      show ?thesis
        unfolding x prod.case args_ivl if_not_P[OF False[folded t]]
        by (simp only: eq t A1 A2 simp_thms)
    qed
  qed
next
  case new
  let ?m = "ne + length auxlist"
  let ?\<phi>s = "Formula.fv_list \<phi>" and ?\<psi>s = "Formula.fv_list \<psi>"
  have sat_\<phi>: "Formula.sat \<sigma> V (val n ?\<phi>s (restrict ?\<phi>s ?\<psi>s x)) k \<phi> \<longleftrightarrow>
    Formula.sat \<sigma> V (val n ?\<psi>s x) k \<phi>" for x k
    by (rule sat_restrict) simp
  have B1: "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. \<forall>j\<in>{?m..<Suc ?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> ?m) \<longrightarrow>
    Formula.sat \<sigma> V (val n ?\<psi>s v) j \<psi> \<and> (if pos then \<not> Formula.sat \<sigma> V (val n ?\<psi>s v) j \<phi>
      else Formula.sat \<sigma> V (val n ?\<psi>s v) j \<phi>)) (join ?\<psi>s rel2 (\<not> pos) ?\<phi>s rel1)"
    by (rule qtable_join_sub[OF qtable2 qtable1 distinct_fvi_list distinct_fvi_list])
      (use fvi_subset mem in \<open>auto simp: sat_\<phi>\<close>)
  have B2: "qtable ?\<psi>s (mem_restr R ?\<psi>s) (\<lambda>v. \<forall>j\<in>{?m..<Suc ?m}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> ?m) \<longrightarrow>
    Formula.sat \<sigma> V (val n ?\<psi>s v) j \<psi> \<or> (\<exists>k\<in>{?m..<j}. if pos then Formula.sat \<sigma> V (val n ?\<psi>s v) k \<phi>
      else \<not> Formula.sat \<sigma> V (val n ?\<psi>s v) k \<phi>)) rel2"
    by (rule qtable_cong[OF qtable2 refl]) (use mem in auto)
  show ?case
    using B1 B2 by (simp add: args_pos args_L args_R)
qed

lemma wf_release_aux_Cons: "wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> (a # aux) ne \<Longrightarrow>
  wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> aux (Suc ne)"
  unfolding wf_release_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong)

lemma wf_release_aux_Cons1: "wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_release_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_release_aux_Cons3: "wf_release_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow>
  qtable (Formula.fv_list \<psi>) (mem_restr R (Formula.fv_list \<psi>)) (\<lambda>v.
    \<forall>j\<in>{ne..<Suc (ne + length aux)}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> ne) \<longrightarrow>
      Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) j \<psi> \<or>
      (\<exists>k\<in>{ne..<j}. if pos then Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>
        else \<not> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>) v) k \<phi>)) a2"
  unfolding wf_release_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma progress_Releasep[simp]: "mem I 0 \<Longrightarrow> progress \<sigma> P (Releasep pos \<phi> I \<psi>) j =
  Inf {i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  by (cases pos) (simp_all add: Releasep_def)

lemma progress_Releasep_le: "mem I 0 \<Longrightarrow>
  progress \<sigma> P (Releasep pos \<phi> I \<psi>) j \<le> min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
  by (auto simp: trans_le_add1 intro!: cInf_lower)

lemma update_release':
  "wf_release_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux'' (progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>)) \<and>
  progress \<sigma> P (Releasep pos \<phi>'' I \<psi>'') j + length zs = progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>) \<and>
  progress \<sigma> P (Releasep pos \<phi>'' I \<psi>'') j + length zs + length aux'' =
    min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
  list_all2 (\<lambda>i. sat_table \<sigma> V n R (Formula.fv_list \<psi>'') i (Releasep pos \<phi>'' I \<psi>''))
    [progress \<sigma> P (Releasep pos \<phi>'' I \<psi>'') j..<progress \<sigma> P (Releasep pos \<phi>'' I \<psi>'') j + length zs] zs \<and>
  nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
  if q1: "list_all2 (\<lambda>i. sat_table \<sigma> V n R (Formula.fv_list \<phi>'') i \<phi>'')
    [progress \<sigma> P \<phi>'' j..<progress \<sigma> P' \<phi>'' (j + \<delta>)] xs"
  and q2: "list_all2 (\<lambda>i. sat_table \<sigma> V n R (Formula.fv_list \<psi>'') i \<psi>'')
    [progress \<sigma> P \<psi>'' j..<progress \<sigma> P' \<psi>'' (j + \<delta>)] ys"
  and eq1: "mbuf2t_take (update_release args) aux (mbuf2_add xs ys buf) t (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = (aux', buf', nt, nts')"
  and eq2: "eval_until I nt aux' = (zs, aux'')"
  and wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
  and fvi_sub: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
  and mem: "mem I 0"
  and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
  and nts: "wf_ts \<sigma> P j \<phi>'' \<psi>'' nts"
  and aux: "wf_release_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux (progress \<sigma> P (Releasep pos \<phi>'' I \<psi>'') j)"
  and args_ivl: "args_ivl args = I"
  and args_L: "args_L args = Formula.fv_list \<phi>''"
  and args_R: "args_R args = Formula.fv_list \<psi>''"
  and args_pos: "args_pos args = pos"
  and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))))"
  and length_aux: "progress \<sigma> P (Releasep pos \<phi>'' I \<psi>'') j + length aux = min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
  and nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
proof -
  note sat.simps[simp del] progress_simps[simp del] progress_Releasep[simp del]
  define ne where "ne \<equiv> progress \<sigma> P (Releasep pos \<phi>'' I \<psi>'') j"
  have update1: "wf_release_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux' ne \<and>
      ne + length aux' = min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    using q1 q2 nts_snoc length_aux aux fvi_sub
    by (elim mbuf2t_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF wf_envs] buf])
      (auto simp: args_ivl args_pos args_L args_R ne_def length_update_release mem
        intro!: wf_update_release_auxlist)
  then have wf_auxlist': "wf_release_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux' ne"
    by blast
  have nts': "wf_ts \<sigma> P' (j + \<delta>) \<phi>'' \<psi>'' nts'"
    using q1 q2 wf_envs nts_snoc
    unfolding wf_ts_def
    by (intro mbuf2t_take_eqD(2)[OF eq1]) (auto intro: wf_mbuf2_add buf[unfolded wf_mbuf2'_def])
  have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
  proof -
    let ?m = "min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
    let ?m' = "min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    from nts have nts_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m..<j] nts"
      unfolding wf_ts_def .
    from nts' have nts'_rel: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?m'..<j + \<delta>] nts'"
      unfolding wf_ts_def .
    show ?thesis
    proof (cases "nts' = []")
      case False
      with nts'_rel have "hd nts' = \<tau> \<sigma> ?m'" "?m' < j + \<delta>"
        by (rule list_all2_hdD)+
      then have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = ?m'"
        by linarith+
      with \<open>hd nts' = \<tau> \<sigma> ?m'\<close> False show ?thesis
        unfolding mbuf2t_take_nt[OF eq1] by (simp only: hd_append if_False if_not_P)
    next
      case True
      with nts'_rel have "j + \<delta> \<le> ?m'"
        by auto
      show ?thesis
      proof (cases "\<delta> = 0")
        case False
        with \<open>j + \<delta> \<le> ?m'\<close> have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = j + \<delta> - 1"
          by linarith+
        with False show ?thesis
          unfolding mbuf2t_take_nt[OF eq1] \<open>nts' = []\<close>
          by (simp only: if_not_P) (simp add: hd_append hd_rev last_map)
      next
        case True
        show ?thesis
        proof (cases "nts = []")
          case False
          with nts_rel have "last nts = \<tau> \<sigma> (j - 1)" "?m < j"
            by (rule list_all2_lastD list_all2_hdD(2))+
          with \<open>j + \<delta> \<le> ?m'\<close> \<open>\<delta> = 0\<close> have "j + \<delta> \<noteq> 0" "min (j + \<delta> - 1) ?m' = j - 1"
            by linarith+
          with False \<open>last nts = \<tau> \<sigma> (j - 1)\<close> \<open>\<delta> = 0\<close> show ?thesis
            unfolding mbuf2t_take_nt[OF eq1] \<open>nts' = []\<close>
            by (simp only: if_not_P) (simp add: hd_append hd_rev)
        next
          case True
          with nts_rel have "j \<le> ?m"
            by auto
          with \<open>j + \<delta> \<le> ?m'\<close> \<open>\<delta> = 0\<close> have "min (j - 1) ?m = j - 1" "min (j + \<delta> - 1) ?m' = j - 1"
            by linarith+
          with True \<open>\<delta> = 0\<close> show ?thesis
            unfolding mbuf2t_take_nt[OF eq1] \<open>nts' = []\<close> t
            by (simp only: add_0_right upt_conv_Nil[OF order.refl] list.map(1) rev.simps(1)
                append_Nil list.sel(1))
        qed
      qed
    qed
  qed
  have "i \<le> progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>) \<Longrightarrow>
      wf_release_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' i \<Longrightarrow>
      i + length auxlist' = min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<Longrightarrow>
      eval_until I nt auxlist' = (zs, aux'') \<Longrightarrow>
      wf_release_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux'' (progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>)) \<and>
        i + length zs = progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>) \<and>
        i + length zs + length aux'' = min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
        list_all2 (\<lambda>i. sat_table \<sigma> V n R (Formula.fv_list \<psi>'') i (Releasep pos \<phi>'' I \<psi>''))
          [i..<i + length zs] zs" for i auxlist'
  proof (induction auxlist' arbitrary: zs aux'' i)
    case Nil
    then show ?case
      by (auto dest!: antisym[OF progress_Releasep_le[OF mem]])
  next
    case (Cons a aux')
    obtain t a1 a2 where "a = (t, a1, a2)" by (cases a)
    from Cons.prems(2) have aux': "wf_release_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux' (Suc i)"
      by (rule wf_release_aux_Cons)
    from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
      unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_release_aux_Cons1)
    from Cons.prems(2) have 3: "qtable (Formula.fv_list \<psi>'') (mem_restr R (Formula.fv_list \<psi>'')) (\<lambda>v.
        \<forall>j\<in>{i..<Suc (i + length aux')}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow>
          Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) j \<psi>'' \<or>
          (\<exists>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) k \<phi>''
            else \<not> Formula.sat \<sigma> V (val n (Formula.fv_list \<psi>'') v) k \<phi>'')) a2"
      unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_release_aux_Cons3)
    from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' =
          min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
      by simp
    have prog_le: "i \<ge> progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>)"
      if "memR I (nt - t)"
      using that nts' mem unfolding wf_ts_def progress_Releasep[OF mem] nt
      by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
    have prog_Suc: "Suc i \<le> progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>)"
      if "\<not> memR I (nt - t)"
    proof -
      let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
      let ?min = "min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))"
      from that have "?X \<noteq> {}"
        by (auto intro!: exI[of _ "progress \<sigma> P' \<phi>'' (j + \<delta>)"])
      have "j + \<delta> \<noteq> 0"
        using Suc_i_aux' wf_envs_progress_le(2)[OF wf_envs, of \<psi>''] by linarith
      show ?thesis
        unfolding progress_Releasep[OF mem]
      proof (rule cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
        fix x
        assume "x \<in> ?X"
        show "Suc i \<le> x"
        proof (rule ccontr)
          assume "\<not> Suc i \<le> x"
          then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> i"
            by (intro \<tau>_mono) simp
          have "?min < j + \<delta>" "?min \<le> min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
            using \<open>j + \<delta> \<noteq> 0\<close> by linarith+
          with \<open>x \<in> ?X\<close> have "memR I (\<tau> \<sigma> ?min - \<tau> \<sigma> x)"
            by blast
          then have "memR I (nt - t)"
            unfolding nt 1 if_not_P[OF \<open>j + \<delta> \<noteq> 0\<close>]
            by (rule memR_antimono) (rule diff_le_mono2[OF \<open>\<tau> \<sigma> x \<le> \<tau> \<sigma> i\<close>])
          with that show False
            by contradiction
        qed
      qed
    qed
    have *: "k < progress \<sigma> P' \<psi> (j + \<delta>)" if
      "\<not> memR I (nt - \<tau> \<sigma> i)"
      "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "\<psi> = \<psi>'' \<or> \<psi> = \<phi>''" for k \<psi>
      using that nts' unfolding wf_ts_def nt
      by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
    show ?case
    proof (cases "memR I (nt - t)")
      case True
      with Cons.prems(4) have "zs = []" "aux'' = a # aux'"
        by (simp_all add: \<open>a = (t, a1, a2)\<close>)
      moreover from Cons.prems(1) prog_le[OF True]
      have "i = progress \<sigma> P' (Releasep pos \<phi>'' I \<psi>'') (j + \<delta>)"
        by (rule antisym)
      ultimately show ?thesis
        using Cons.prems(2,3) by simp
    next
      case False
      obtain xs aux''' where eq: "eval_until I nt aux' = (xs, aux''')"
        by (cases "eval_until I nt aux'")
      with False Cons.prems(4) have zs: "zs = a2 # xs" and aux'': "aux'' = aux'''"
        by (simp_all add: \<open>a = (t, a1, a2)\<close>)
      have j_lt: "k < Suc (i + length aux')" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
        using *[OF False[unfolded 1] that, of \<psi>''] *[OF False[unfolded 1] that, of \<phi>''] Suc_i_aux'
        by simp
      have "sat_table \<sigma> V n R (Formula.fv_list \<psi>'') i (Releasep pos \<phi>'' I \<psi>'') a2"
        by (rule qtable_cong[OF 3 refl]) (cases pos; auto simp: Releasep_def sat.simps j_lt)
      with Cons.IH[OF prog_Suc[OF False] aux' Suc_i_aux' eq] show ?thesis
        unfolding zs aux'' by (clarsimp simp: upt_conv_Cons simp del: upt_Suc)
    qed
  qed
  note wf_aux'' = this[OF wf_envs_progress_mono[OF wf_envs]
      wf_auxlist'[unfolded ne_def] conjunct2[OF update1, unfolded ne_def] eq2]
  then show ?thesis
    using nt by auto
qed

(*<*)
end
(*>*)
