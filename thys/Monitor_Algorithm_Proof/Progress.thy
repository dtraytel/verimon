(*<*)
theory Progress
  imports "MFODL_Logic.Safety" "MFODL_Logic.Specification"
begin
(*>*)


section \<open> Progress \<close>


subsection \<open> Fixpoints and infima \<close>

lemma image_eqD: "f ` A = B \<Longrightarrow> \<forall>x\<in>A. f x \<in> B"
  by blast

lemma bounded_fixpoint_ex:
  fixes f :: "nat \<Rightarrow> nat"
  shows "mono_on {..j} f \<Longrightarrow> (\<forall>x \<le> j. f x \<le> j) \<Longrightarrow> \<exists>y \<le> j. y = f y"
proof (induction j)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  show ?case
  proof (cases "f (Suc j) = Suc j")
    case True
    then show ?thesis
      by (intro exI[of _ "Suc j"]) simp
  next
    case False
    with Suc.prems(2) have fSuc: "f (Suc j) \<le> j"
      by (simp add: le_Suc_eq)
    have "f x \<le> j" if "x \<le> j" for x
    proof -
      have "f x \<le> f (Suc j)"
        by (rule mono_onD[OF Suc.prems(1)]) (use that in auto)
      with fSuc show ?thesis
        by simp
    qed
    moreover have "mono_on {..j} f"
      using Suc.prems(1) by (rule mono_on_subset) auto
    ultimately obtain y where "y \<le> j" "y = f y"
      using Suc.IH by blast
    then show ?thesis
      by (intro exI[of _ y]) simp
  qed
qed

lemma bounded_fixpoint_ex_above:
  fixes f :: "nat \<Rightarrow> nat"
  shows "mono_on {i..j} f \<Longrightarrow> (\<forall>x \<in> {i .. j}. f x \<in> {i .. j}) \<Longrightarrow> i \<le> j \<Longrightarrow> \<exists>y \<in> {i .. j}. y = f y"
proof (induction j)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  show ?case
  proof (cases "f (Suc j) = Suc j")
    case True
    with Suc.prems(3) show ?thesis
      by (intro bexI[of _ "Suc j"]) simp_all
  next
    case False
    have "f (Suc j) \<in> {i..Suc j}"
      using Suc.prems(2,3) by simp
    with False have fSuc: "i \<le> f (Suc j)" "f (Suc j) \<le> j"
      by (auto simp: le_Suc_eq)
    then have "i \<le> j"
      by simp
    have "f x \<in> {i..j}" if "x \<in> {i..j}" for x
    proof -
      have "i \<le> f x"
        using Suc.prems(2) that by auto
      moreover have "f x \<le> f (Suc j)"
        by (rule mono_onD[OF Suc.prems(1)]) (use that \<open>i \<le> j\<close> in auto)
      ultimately show ?thesis
        using fSuc by simp
    qed
    moreover have "mono_on {i..j} f"
      using Suc.prems(1) by (rule mono_on_subset) auto
    ultimately obtain y where "y \<in> {i..j}" "y = f y"
      using Suc.IH \<open>i \<le> j\<close> by blast
    then show ?thesis
      by (intro bexI[of _ y]) auto
  qed
qed

lemma min_Inf:
  fixes X :: "nat set"
  assumes "X \<noteq> {}" "Y \<noteq> {}"
  shows "min (Inf X) (Inf Y) = Inf (X \<union> Y)"
proof -
  obtain x where x_def: "x = Inf X" "x \<in> X" "\<And>z. z \<in> X \<Longrightarrow> x \<le> z"
    using assms(1) cInf_lower
    by (auto simp add: Inf_nat_def1)
  obtain y where y_def: "y = Inf Y" "y \<in> Y" "\<And>z. z \<in> Y \<Longrightarrow> y \<le> z"
    using assms(2) cInf_lower
    by (auto simp add: Inf_nat_def1)
  have "min x y \<in> X \<union> Y" "\<And>z. z \<in> X \<union> Y \<Longrightarrow> min x y \<le> z"
    using x_def(2,3) y_def(2,3)
    by (fastforce simp: min_def)+
  then have "Inf (X \<union> Y) = min x y"
    unfolding Inf_nat_def
    by (rule Least_equality)
  then show ?thesis
    by (auto simp: x_def(1) y_def(1))
qed

lemma cInf_restrict_nat:
  fixes x :: nat
  assumes "x \<in> A"
  shows "Inf A = Inf {y \<in> A. y \<le> x}"
  using assms by (auto intro!: antisym intro: cInf_greatest cInf_lower Inf_nat_def1)

lemma Inf_UNIV_nat: "(Inf UNIV :: nat) = 0"
  by (simp add: cInf_eq_minimum)

lemma Inf_memR_conv: 
  "\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> n \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} =
  (case j of 0 \<Rightarrow> 0 | Suc x \<Rightarrow> Inf {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)})"
  using memR_antimono[OF _ diff_le_mono[OF \<tau>_mono]]
  by (fastforce simp: cInf_eq_minimum less_Suc_eq_le 
      split: nat.splits intro!: arg_cong[where ?f=Inf])

lemma min_x_Inf: 
  "min x (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}) 
  = \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
proof -
  {
    assume assm: "x < \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
    then have "x \<in> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
      by auto
    then have "x \<ge> \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
      by (simp add: cInf_lower)
    then have "False" using assm by auto
  }
  then show ?thesis
    by (meson min.absorb2 not_le_imp_less)
qed

lemma memR_flip_int_double_upper: "memR I t \<Longrightarrow> memR (flip_int_double_upper I) t"
  by transfer auto


subsection \<open> Progress function \<close>

context fixes \<sigma> :: "'a trace" begin

function (sequential) progress :: "(Formula.name \<times> nat \<rightharpoonup> nat) \<Rightarrow> 't Formula.formula \<Rightarrow> nat \<Rightarrow> nat" where
  "progress P (Formula.Pred e ts) j = (case P (e, length ts) of None \<Rightarrow> j | Some k \<Rightarrow> k)"
| "progress P (Formula.Let p \<phi> \<psi>) j = progress (P((p, Formula.nfv \<phi>) \<mapsto> progress P \<phi> j)) \<psi> j"
| "progress P (Formula.Frz p \<phi> \<psi>) j =
    (let pn = (p, Formula.nfv \<phi>) in
     (LEAST i. i \<le> j \<and> progress (P(pn \<mapsto> (if i < progress P \<phi> j then j else 0))) \<psi> j \<le> i))"
| "progress P (Formula.LetPast p \<phi> \<psi>) j =
    (let pn = (p, Formula.nfv \<phi>) in
    progress (P(pn \<mapsto> \<Sqinter>{i. i \<le> j \<and> i = progress (P(pn \<mapsto> i)) \<phi> j})) \<psi> j)"
| "progress P (Formula.Eq t1 t2) j = j"
| "progress P (Formula.Less t1 t2) j = j"
| "progress P (Formula.LessEq t1 t2) j = j"
| "progress P (Formula.Neg \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Or \<phi> \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.And \<phi> \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.Ands l) j = (if l = [] then j else Min (set (map (\<lambda>\<phi>. progress P \<phi> j) l)))"
| "progress P (Formula.Exists t \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Agg y \<omega> b f \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress P \<phi> j)) j)"
| "progress P (Formula.Next I \<phi>) j = progress P \<phi> j - 1"
| "progress P (Formula.Since \<phi> I \<psi>) j = min (progress P \<phi> j)
    (if memL I 0 then progress P \<psi> j else Suc (progress P \<psi> j))"
| "progress P (Formula.Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress P \<phi> j) (progress P \<psi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
| "progress P (Formula.Trigger \<phi> I \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.Release \<phi> I \<psi>) j = (
    \<comment> \<open>without 0 in the interval: progress of the rewriting\<close>
    if mem I 0 \<or> \<not> bounded I then
      Inf {i. \<forall>k. k < j \<and> k \<le> min (progress P \<phi> j) (progress P \<psi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}
    else
      (progress P (release_safe_bounded \<phi> I \<psi>) j)
    )"| "progress P (Formula.MatchP I r) j = min_regex_default (progress P) r j"
| "progress P (Formula.MatchF I r) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min_regex_default (progress P) r j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
| "progress P (Formula.TP t) j = j"
| "progress P (Formula.TS t) j = j"
  by pat_completeness auto
termination
  using size'_Or
  by (relation "measure (\<lambda>(_, \<phi>, _). size' \<phi>)")
    (simp_all add: less_Suc_eq_le sum_list_mem_leq size'_release_aux(3)
      less_imp_le[OF regex_atms_size'])

lemma progress_FF [simp]: "progress P Formula.FF j = j"
  unfolding Formula.FF_def
  by auto

lemma progress_TT [simp]: "progress P Formula.TT j = j"
  unfolding Formula.TT_def
  by auto

lemma progress_first [simp]: "progress P Formula.first j = j"
  unfolding Formula.first_def
  by auto

lemma progress_Until_le: "progress P (Formula.Until \<phi> I \<psi>) j \<le> min (progress P \<phi> j) (progress P \<psi> j)"
  by (auto simp: trans_le_add1 intro!: cInf_lower)

lemma progress_once [simp]: "progress P (once I \<phi>) j
  = (if memL I 0 then min j (progress P \<phi> j) else min j (Suc (progress P \<phi> j)))"
  unfolding once_def
  by auto

lemma progress_eventually: "progress P (eventually I \<phi>) j
  = Inf {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  unfolding eventually_def
  by (auto intro: arg_cong[where f = Inf])

lemma progress_always_safe_0 [simp]: "progress P (always_safe_0 I \<phi>) j =
  Inf {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
proof -
  have set_eq: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> Suc (local.progress P \<phi> j) \<and> k \<le> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)} =
        {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  have subset: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<subseteq>
  {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    using memR_flip_int_double_upper
    by auto
  have "(local.progress P \<phi> j + 1) \<in> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  then have non_empty: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<noteq> {}"
    by blast

  have "min (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)})
     (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}) =
    \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    using cInf_superset_mono[OF non_empty bdd_below_bot subset]
    by auto
  
  then show ?thesis
    using set_eq
    unfolding always_safe_0_def
    by auto
qed

lemma progress_eventually_nempty: 
  "{i. \<forall>k. k < j \<and> k \<le> n \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<noteq> {}"
  by (auto intro!: exI[of _ n])

lemma progress_eventually_or[simp]: "progress P (eventually I (Formula.Or \<phi> \<psi>)) j =
  min (progress P (eventually I \<phi>) j) (progress P (eventually I \<psi>) j)"
  unfolding progress_eventually min_Inf[OF progress_eventually_nempty progress_eventually_nempty]
  by (cases "progress P \<phi> j \<le> progress P \<psi> j") (auto intro: arg_cong[where ?f=Inf])

lemma progress_release_safe_bounded_evtl: 
  "min (progress P (Formula.eventually I Formula.TT) j) (progress P (release_safe_bounded \<phi> I \<psi>) j)
  = progress P (release_safe_bounded \<phi> I \<psi>) j"
  unfolding release_safe_bounded_def
  by (auto simp: progress_eventually)

lemma progress_eventually_monos:
  assumes "progress P \<phi> j \<le> progress P' \<psi> j'" and "j \<le> j'"
  shows "(progress P (Formula.eventually I \<phi>) j) \<le> (progress P' (Formula.eventually I \<psi>) j')"
    and "(progress P (Formula.eventually (int_remove_lower_bound I) \<phi>) j) 
        \<le> (progress P' (Formula.eventually (int_remove_lower_bound I) \<psi>) j')"
    and "(progress P (Formula.eventually (flip_int_less_lower I) \<phi>) j) 
        \<le> (progress P' (Formula.eventually (flip_int_less_lower I) \<psi>) j')"
  using assms 
  by (auto simp: progress_eventually intro!: cInf_superset_mono
          elim!: allE[of "\<lambda>x. \<exists>k<j'. k \<le> _ \<and> \<not> memR _ (\<tau> \<sigma> k - \<tau> \<sigma> x)" j'])

lemma progress_and_release_rewrite_bounded:
  assumes "\<not> mem I 0" "bounded I"
  shows "Progress.progress \<sigma> P (and_release_safe_bounded \<phi> \<phi>' I \<psi>') j 
  = progress P (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) j"
proof -
  have "progress P (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) j 
  = min (progress P \<phi> j) 
      (min (progress P (Formula.eventually I Formula.TT) j) 
          (progress P (release_safe_bounded \<phi>' I \<psi>') j))"
    using assms
    by (auto simp only: progress_release_safe_bounded_evtl[of P I j \<phi>' \<psi>'] 
        progress.simps split: if_splits)
  then show ?thesis
    using assms
    unfolding and_release_safe_bounded_def
    by (auto simp: progress_eventually)
qed

definition "progress_regex P = min_regex_default (progress P)"
definition "letpast_progress P p \<phi> j = \<Sqinter>{i. i \<le> j \<and> i = progress (P(p \<mapsto> i)) \<phi> j}"
definition "frz_progress P p \<phi> \<psi> j =
  (let pn = (p, Formula.nfv \<phi>) in
   (LEAST i. i \<le> j \<and> progress (P(pn \<mapsto> (if i < progress P \<phi> j then j else 0))) \<psi> j \<le> i))"

declare progress.simps[simp del]
lemmas progress_simps[simp] 
  = progress.simps[folded progress_regex_def[THEN fun_cong, THEN fun_cong] letpast_progress_def frz_progress_def]

end


subsection \<open> Bounds and monotonicity \<close>

lemma progress_fixpoint_ex':
  assumes "(\<And>P. pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> Progress.progress \<sigma> P \<phi> j \<le> j)"
  and "(\<And>P P'. pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P' \<Longrightarrow> rel_mapping (\<le>) P P' 
    \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j)"
  shows "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> \<exists>i \<le> j. i = Progress.progress \<sigma> (P(p \<mapsto> i)) \<phi> j"
  by (rule bounded_fixpoint_ex)
    (auto simp: reflp_def intro!: mono_onI assms rel_mapping_map_upd rel_mapping_reflp)

lemma progress_le_gen: "\<And>j P. pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P \<phi> j \<le> j" 
  and progress_mono_gen: "\<And>j j' P P'. j \<le> j' \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P 
    \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j') P' \<Longrightarrow> rel_mapping (\<le>) P P' 
    \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j'"
proof (induction \<phi>)
  case (Pred e ts) case 1
  then show ?case
    by (force simp: pred_mapping_alt dom_def split: option.splits)
next
  case (Pred e ts) case 2
  then show ?case
    by (force simp: rel_mapping_alt dom_def split: option.splits)
next
  case (Ands l) case 1
  with Ands show ?case
    by (auto simp: image_iff 
        intro!: Min.coboundedI[where a="progress \<sigma> P (hd l) j", THEN order_trans])
next
  case (Ands l) case 2
  with Ands show ?case
    by (auto simp: image_iff 
        intro!: Min.coboundedI[THEN order_trans])
next
  case (Since \<phi> I \<psi>)
  {
    case 1
    from Since.IH(1)[OF 1] show ?case by simp
  next
    case 2
    then have
      "progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j'"
      "progress \<sigma> P \<psi> j \<le> progress \<sigma> P' \<psi> j'"
      using Since.IH(2,4) by auto
    then show ?case by auto
  }
next
  case (Until \<phi> I \<psi>) case 1
  then show ?case
    by (auto intro!: cInf_lower)
next
  case (Until \<phi> I \<psi>) case 2
  with Until(2,4)[of j j' P P'] show ?case
    by (auto 0 3 dest: memR_nonzeroD less_\<tau>D spec[of _ j'] 
        intro!: cInf_superset_mono)
next
  case (Release \<phi> I \<psi>) case 1
  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    then show ?thesis 
      using Release 
      by (auto intro!: cInf_lower)
  next
    case False
    have fact1: "progress \<sigma> P (Formula.eventually I Formula.TT) j \<le> j"
      by (simp add: progress_eventually) (rule cInf_lower; clarsimp)
    have fact2: "(progress \<sigma> P (Formula.eventually I \<psi>') j) \<le> progress \<sigma> P \<psi>' j" 
      for \<psi>' :: "'b Formula.formula"
      by (simp add: progress_eventually) (rule cInf_lower; clarsimp)
    hence "(progress \<sigma> P (always_safe_bounded I \<psi>) j) \<le> progress \<sigma> P \<psi> j"
      by (clarsimp simp: always_safe_bounded_def)
        (meson min_le_iff_disj)
    thus ?thesis
      using Release(1,3)[OF 1] 1 False fact1 fact2 min.coboundedI1
      by (auto simp add: release_safe_bounded_def)
  qed
next
  case (Release \<phi> I \<psi>) case 2
  show ?case 
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    let ?A = "\<lambda>P j. {i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)
      \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    have \<phi>: "progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j'"
      and \<psi>: "progress \<sigma> P \<psi> j \<le> progress \<sigma> P' \<psi> j'"
      using Release(2,4)[OF 2] by auto
    have "?A P' j' \<subseteq> ?A P j"
      using \<phi> \<psi> 2(1) by auto
    moreover have "?A P' j' \<noteq> {}"
      by (auto intro!: exI[of _ j'])
    ultimately have "Inf (?A P j) \<le> Inf (?A P' j')"
      by (intro cInf_superset_mono) auto
    with True show ?thesis
      by simp  next
    case False
    have fact1: "progress \<sigma> P (Formula.eventually I Formula.TT) j 
      \<le> progress \<sigma> P' (Formula.eventually I Formula.TT) j'"
      and fact2: "progress \<sigma> P (Formula.eventually (flip_int_less_lower I) \<phi>) j
      \<le> progress \<sigma> P' (Formula.eventually (flip_int_less_lower I) \<phi>) j'"
      using 2(1) False Release(2,4)[OF 2]
      by (auto simp: progress_eventually intro!: cInf_superset_mono exI[of _ j'] 
          elim!: allE[of "\<lambda>x. \<exists>k<j'. k \<le> _ \<and> \<not> memR _ (\<tau> \<sigma> k - \<tau> \<sigma> x)" j'])
    have fact3: "(progress \<sigma> P (Formula.eventually I \<psi>') j) 
        \<le> (progress \<sigma> P' (Formula.eventually I \<psi>') j')" 
      and fact4: "(progress \<sigma> P (Formula.eventually (int_remove_lower_bound I) \<psi>') j) 
        \<le> (progress \<sigma> P' (Formula.eventually (int_remove_lower_bound I) \<psi>') j')"
      and fact5: "(progress \<sigma> P (Formula.eventually (flip_int_less_lower I) \<psi>') j) 
        \<le> (progress \<sigma> P' (Formula.eventually (flip_int_less_lower I) \<psi>') j')"
      if "progress \<sigma> P \<psi>' j \<le> progress \<sigma> P' \<psi>' j'"
      for \<psi>' :: "'b Formula.formula"
      using progress_eventually_monos[OF that 2(1)] 
      by blast+
    hence "(progress \<sigma> P (always_safe_bounded I \<psi>) j) 
        \<le> (progress \<sigma> P' (always_safe_bounded I \<psi>) j')" 
      using Release(2,4)[OF 2] 2(1) 
      by (clarsimp simp: always_safe_bounded_def min_le_iff_disj)
    moreover have "progress \<sigma> P (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I) (Formula.And \<psi> \<phi>))) j
      \<le> progress \<sigma> P' (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I) (Formula.And \<psi> \<phi>))) j'"
    proof -
      let ?S = "\<lambda>P j. {i. \<forall>k. k < j \<and> k \<le> progress \<sigma> P \<psi> j \<and> k \<le> progress \<sigma> P \<phi> j
        \<longrightarrow> memR (int_remove_lower_bound I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
      have "?S P' j' \<subseteq> ?S P j"
        using Release(2,4)[OF 2] 2(1) by auto
      moreover have "?S P' j' \<noteq> {}"
        by (auto intro!: exI[of _ j'])
      ultimately have "Inf (?S P j) \<le> Inf (?S P' j')"
        by (intro cInf_superset_mono) auto
      then show ?thesis
        by (simp add: diff_le_mono)
    qed
    then have "progress \<sigma> P (Formula.eventually (flip_int_less_lower I)
        (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I) (Formula.And \<psi> \<phi>)))) j
      \<le> progress \<sigma> P' (Formula.eventually (flip_int_less_lower I)
        (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I) (Formula.And \<psi> \<phi>)))) j'"
      by (rule fact5)
    ultimately show ?thesis
      using False fact1 fact2
      by (simp add: release_safe_bounded_def del: min.bounded_iff) (intro min.mono; assumption)
  qed
next
  case (MatchF I r) case 1
  then show ?case
    by (auto intro!: cInf_lower)
next
  case (MatchF I r) case 2
  with MatchF(2)[of _ j j' P P'] show ?case
    by (auto 0 3 simp: Min_le_iff progress_regex_def dest: memR_nonzeroD less_\<tau>D spec[of _ j']
      elim!: order_trans less_le_trans intro!: cInf_superset_mono)
next
  case (LetPast p \<phi>1 \<phi>2) case 1
  obtain i where fp: "i = progress \<sigma> (P((p, Formula.nfv \<phi>1) \<mapsto> i)) \<phi>1 j" "i \<le> j"
    using progress_fixpoint_ex'[OF LetPast(1,2) 1] by blast
  have "\<Sqinter>{i. i \<le> j \<and> i = progress \<sigma> (P((p, Formula.nfv \<phi>1) \<mapsto> i)) \<phi>1 j} \<le> j"
    using fp by (auto intro!: cInf_lower2[of i])
  then show ?case
    unfolding progress.simps Let_def
    by (intro LetPast(3) pred_mapping_map_upd[OF _ 1])
next
  case (Frz p \<phi> \<psi>) case 1
  let ?pn = "(p, Formula.nfv \<phi>)"
  show ?case
    unfolding progress.simps Let_def
  proof (rule Least_le)
    have pm: "pred_mapping (\<lambda>x. x \<le> j)
      (P(?pn \<mapsto> (if j < progress \<sigma> P \<phi> j then j else 0)))"
      using 1 by auto
    moreover have "progress \<sigma> (P(?pn \<mapsto> (if j < progress \<sigma> P \<phi> j then j else 0))) \<psi> j \<le> j"
      by (rule Frz(3)[OF pm])
    ultimately show "j \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if j < progress \<sigma> P \<phi> j then j else 0))) \<psi> j \<le> j"
      by simp
  qed
next
  case (Frz p \<phi> \<psi>) case 2
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?r = "progress \<sigma> P' (Formula.Frz p \<phi> \<psi>) j'"
  let ?a = "\<lambda>i. if i < progress \<sigma> P \<phi> j then j else 0"
  let ?a' = "\<lambda>i. if i < progress \<sigma> P' \<phi> j' then j' else 0"
  have r_ex: "\<exists>i. i \<le> j' \<and> progress \<sigma> (P'(?pn \<mapsto> ?a' i)) \<psi> j' \<le> i"
  proof
    have pm: "pred_mapping (\<lambda>x. x \<le> j') (P'(?pn \<mapsto> ?a' j'))"
      using 2 by auto
    moreover have "progress \<sigma> (P'(?pn \<mapsto> ?a' j')) \<psi> j' \<le> j'"
      by (rule Frz(3)[OF pm])
    ultimately show "j' \<le> j' \<and> progress \<sigma> (P'(?pn \<mapsto> ?a' j')) \<psi> j' \<le> j'"
      by simp
  qed
  have r_prop: "?r \<le> j' \<and> progress \<sigma> (P'(?pn \<mapsto> ?a' ?r)) \<psi> j' \<le> ?r"
    unfolding progress.simps Let_def by (rule LeastI_ex[OF r_ex])
  show ?case
  proof (cases "?r \<le> j")
    case True
    have \<phi>_mono: "progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j'"
      by (rule Frz(2)[OF 2])
    have aa': "?a ?r \<le> ?a' ?r"
    proof (cases "?r < progress \<sigma> P \<phi> j")
      case True
      with \<phi>_mono have "?r < progress \<sigma> P' \<phi> j'"
        by simp
      with True 2(1) show ?thesis
        by simp
    next
      case False
      then show ?thesis
        by simp
    qed
    have pm_l: "pred_mapping (\<lambda>x. x \<le> j) (P(?pn \<mapsto> ?a ?r))"
      using 2 True by auto
    have pm_r: "pred_mapping (\<lambda>x. x \<le> j') (P'(?pn \<mapsto> ?a' ?r))"
      using 2 r_prop by auto
    have rm: "rel_mapping (\<le>) (P(?pn \<mapsto> ?a ?r)) (P'(?pn \<mapsto> ?a' ?r))"
      by (rule rel_mapping_map_upd[OF aa' 2(4)])
    have "progress \<sigma> (P(?pn \<mapsto> ?a ?r)) \<psi> j \<le> progress \<sigma> (P'(?pn \<mapsto> ?a' ?r)) \<psi> j'"
      by (rule Frz(4)[OF 2(1) pm_l pm_r rm])
    also have "... \<le> ?r"
      using r_prop by simp
    finally have "?r \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> ?a ?r)) \<psi> j \<le> ?r"
      using True by simp
    then show ?thesis
      unfolding progress.simps Let_def by (rule Least_le)
  next
    case False
    have "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j \<le> j"
      unfolding progress.simps Let_def
    proof (rule Least_le)
      have pm: "pred_mapping (\<lambda>x. x \<le> j) (P(?pn \<mapsto> ?a j))"
        using 2 by auto
      moreover have "progress \<sigma> (P(?pn \<mapsto> ?a j)) \<psi> j \<le> j"
        by (rule Frz(3)[OF pm])
      ultimately show "j \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> ?a j)) \<psi> j \<le> j"
        by simp
    qed
    with False show ?thesis
      by simp
  qed
next
  case (LetPast p \<phi>1 \<phi>2) case 2
  obtain i where fp: "i = progress \<sigma> (P((p, Formula.nfv \<phi>1) \<mapsto> i)) \<phi>1 j" "i \<le> j"
    using progress_fixpoint_ex'[OF LetPast(1,2)] 2 by blast
  obtain i' where fp': "i' = progress \<sigma> (P'((p, Formula.nfv \<phi>1) \<mapsto> i')) \<phi>1 j'" "i' \<le> j'"
    using progress_fixpoint_ex'[OF LetPast(1,2)] 2 by blast
  let ?pn = "(p, Formula.nfv \<phi>1)"
  let ?F = "\<lambda>i. progress \<sigma> (P(?pn \<mapsto> i)) \<phi>1 j"
  let ?F' = "\<lambda>i. progress \<sigma> (P'(?pn \<mapsto> i)) \<phi>1 j'"
  have le_j: "\<Sqinter>{i. i \<le> j \<and> i = ?F i} \<le> j"
    using fp by (auto intro!: cInf_lower2[of i])
  have le_j': "\<Sqinter>{i. i \<le> j' \<and> i = ?F' i} \<le> j'"
    using fp' by (auto intro!: cInf_lower2[of i'])
  have le: "\<Sqinter>{i. i \<le> j \<and> i = ?F i} \<le> \<Sqinter>{i. i \<le> j' \<and> i = ?F' i}"
  proof (rule cInf_mono)
    show "{i. i \<le> j' \<and> i = ?F' i} \<noteq> {}"
      using fp' by auto
    show "bdd_below {i. i \<le> j \<and> i = ?F i}"
      by simp
    fix k
    assume "k \<in> {i. i \<le> j' \<and> i = ?F' i}"
    then have k: "k \<le> j'" "k = ?F' k"
      by simp_all
    have "\<exists>i \<le> min k j. i = ?F i"
    proof (rule bounded_fixpoint_ex)
      show "mono_on {..min k j} ?F"
        using 2 by (intro mono_onI LetPast(2)) (simp_all del: fun_upd_apply)
      show "\<forall>x \<le> min k j. ?F x \<le> min k j"
      proof (intro allI impI)
        fix x
        assume x: "x \<le> min k j"
        have "?F x \<le> ?F' k"
          using 2 x k(1) by (intro LetPast(2)) (simp_all del: fun_upd_apply)
        moreover have "?F x \<le> j"
          using 2 x by (intro LetPast(1)) (simp del: fun_upd_apply)
        ultimately show "?F x \<le> min k j"
          using k(2) by simp
      qed
    qed
    then show "\<exists>a \<in> {i. i \<le> j \<and> i = ?F i}. a \<le> k"
      by auto
  qed
  show ?case
    unfolding progress.simps Let_def
    using le_j le_j' le 2
    by (intro LetPast(4)[OF 2(1)] pred_mapping_map_upd rel_mapping_map_upd) simp_all
qed (simp_all add: Min_le_iff progress_regex_def min_le_iff_disj le_imp_diff_le diff_le_mono
  ex_in_conv split: option.splits, fastforce)

lemma progress_mono:
  "j \<le> j' \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow>
  Progress.progress \<sigma> P \<phi> j \<le> Progress.progress \<sigma> P \<phi> j'"
  by (rule progress_mono_gen) (auto elim: pred_mapping_mono simp: rel_mapping_reflp reflp_def)

lemma progress_le: "progress \<sigma> Map.empty \<phi> j \<le> j"
  using progress_le_gen[of _ Map.empty] by auto

lemma progress_Frz_eq:
  assumes pm: "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j =
    (let pn = (p, Formula.nfv \<phi>); jphi = progress \<sigma> P \<phi> j;
         a = progress \<sigma> (P(pn \<mapsto> 0)) \<psi> j; b = progress \<sigma> (P(pn \<mapsto> j)) \<psi> j
     in if b < jphi then b else if a \<le> jphi then jphi else a)"
proof -
  define pn where "pn = (p, Formula.nfv \<phi>)"
  define jphi where "jphi = progress \<sigma> P \<phi> j"
  define a where "a = progress \<sigma> (P(pn \<mapsto> 0)) \<psi> j"
  define b where "b = progress \<sigma> (P(pn \<mapsto> j)) \<psi> j"
  have F: "progress \<sigma> (P(pn \<mapsto> (if i < jphi then j else 0))) \<psi> j = (if i < jphi then b else a)" for i
    by (simp add: a_def b_def)
  have ab: "a \<le> b"
    unfolding a_def b_def using pm
    by (intro progress_mono_gen[OF order_refl])
      (auto intro!: rel_mapping_map_upd simp: rel_mapping_reflp reflp_def)
  have bj: "b \<le> j"
    unfolding b_def using pm by (intro progress_le_gen) auto
  have jphi_j: "jphi \<le> j"
    unfolding jphi_def by (rule progress_le_gen[OF pm])
  have "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) j =
    (LEAST i. i \<le> j \<and> progress \<sigma> (P(pn \<mapsto> (if i < jphi then j else 0))) \<psi> j \<le> i)"
    by (simp add: frz_progress_def pn_def jphi_def)
  also have "\<dots> = (if b < jphi then b else if a \<le> jphi then jphi else a)"
    unfolding F by (rule Least_equality) (use ab bj jphi_j in \<open>auto split: if_splits\<close>)
  finally show ?thesis
    by (simp add: Let_def pn_def jphi_def a_def b_def)
qed

lemma progress_Frz_eq_le:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P"
    and le1: "progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j \<le> progress \<sigma> P \<alpha> j"
    and le0: "progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> 0)) \<psi> j \<le> progress \<sigma> P \<alpha> j"
  shows "progress \<sigma> P (Formula.Frz q \<alpha> \<psi>) j = progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j"
proof -
  let ?pn = "(q, Formula.nfv \<alpha>)"
  let ?a = "progress \<sigma> P \<alpha> j" and ?m = "progress \<sigma> (P(?pn \<mapsto> j)) \<psi> j"
  have a_le: "?a \<le> j"
    by (rule progress_le_gen[OF P])
  have "(LEAST i. i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < ?a then j else 0))) \<psi> j \<le> i) = ?m"
  proof (rule Least_equality)
    show "?m \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> if ?m < ?a then j else 0)) \<psi> j \<le> ?m"
      using le1 le0 a_le by auto
  next
    fix y
    assume "y \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> if y < ?a then j else 0)) \<psi> j \<le> y"
    then show "?m \<le> y"
      using le1 by (cases "y < ?a") auto
  qed
  then show ?thesis
    by (simp add: frz_progress_def)
qed

lemma progress_0_gen[simp]:
  "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> progress \<sigma> P \<phi> 0 = 0"
  using progress_le_gen[of 0 P] by auto

lemma progress_0[simp]:
  "progress \<sigma> Map.empty \<phi> 0 = 0"
  by (auto simp: pred_mapping_alt)

lemma progress_fixpoint_ex: 
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> \<exists>i \<le> j. i = Progress.progress \<sigma> (P(p \<mapsto> i)) \<phi> j"
  by (blast intro!: progress_fixpoint_ex' progress_le_gen progress_mono_gen)

lemma not_contains_pred_progress[simp]: "\<not> contains_pred p \<phi> 
  \<Longrightarrow> progress \<sigma> (P(p \<mapsto> x)) \<phi> j = progress \<sigma> P \<phi> j"
proof (induction p \<phi> arbitrary: P x rule: contains_pred.induct)
  case (5 p e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  show ?case
  proof (cases "contains_pred p \<phi>")
    case True
    with "5.prems" have "\<not> contains_pred ?en \<psi>" "\<not> contains_pred p \<psi>"
      by auto
    then show ?thesis
      by (simp add: "5.IH"(2,3) del: fun_upd_apply)
  next
    case False
    then have \<phi>: "progress \<sigma> (P(p \<mapsto> x)) \<phi> j = progress \<sigma> P \<phi> j"
      by (rule "5.IH"(1))
    show ?thesis
    proof (cases "p = ?en")
      case True
      then show ?thesis
        using \<phi> by (simp del: fun_upd_apply)
    next
      case neq: False
      with "5.prems" have "\<not> contains_pred p \<psi>"
        by simp
      with neq \<phi> show ?thesis
        by (simp add: fun_upd_twist[of p] "5.IH"(3) del: fun_upd_apply)
    qed
  qed
next
  case (6 p e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  show ?case
  proof (cases "contains_pred p \<phi>")
    case True
    with "6.prems" have "\<not> contains_pred ?en \<psi>" "\<not> contains_pred p \<psi>"
      by auto
    then show ?thesis
      unfolding progress.simps Let_def
      by (simp add: "6.IH"(2,3) del: fun_upd_apply)
  next
    case False
    then have \<phi>: "progress \<sigma> (P(p \<mapsto> x)) \<phi> j = progress \<sigma> P \<phi> j"
      by (rule "6.IH"(1))
    have "progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> y)) \<psi> j = progress \<sigma> (P(?en \<mapsto> y)) \<psi> j" for y
    proof (cases "p = ?en")
      case True
      then show ?thesis
        by (simp del: fun_upd_apply)
    next
      case neq: False
      with "6.prems" have "\<not> contains_pred p \<psi>"
        by simp
      with neq show ?thesis
        by (simp add: fun_upd_twist[of p] "6.IH"(3) del: fun_upd_apply)
    qed
    then show ?thesis
      unfolding progress.simps Let_def \<phi>
      by (simp del: fun_upd_apply)
  qed
next
  case (7 p e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  show ?case
  proof (cases "p = ?en")
    case True
    then show ?thesis
      by (simp add: letpast_progress_def Let_def del: fun_upd_apply)
  next
    case neq: False
    with "7.prems" have \<psi>: "\<not> contains_pred p \<psi>"
      by simp
    show ?thesis
    proof (cases "contains_pred p \<phi>")
      case True
      with neq "7.prems" have "\<not> contains_pred ?en \<psi>"
        by simp
      with \<psi> show ?thesis
        by (simp add: Let_def "7.IH"(2,3) del: fun_upd_apply)
    next
      case False
      have "progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> i)) \<phi> j = progress \<sigma> (P(?en \<mapsto> i)) \<phi> j" for i
        using neq False by (simp add: fun_upd_twist[of p] "7.IH"(1) del: fun_upd_apply)
      then have "letpast_progress \<sigma> (P(p \<mapsto> x)) ?en \<phi> j = letpast_progress \<sigma> P ?en \<phi> j"
        by (simp add: letpast_progress_def del: fun_upd_apply)
      with neq \<psi> show ?thesis
        by (simp add: Let_def fun_upd_twist[of p] "7.IH"(3) del: fun_upd_apply)
    qed
  qed
next
  case (19 p \<phi> I \<psi>)
  then show ?case
    by (auto simp: release_safe_bounded_def Formula.eventually_def
        intro!: arg_cong2[where f=min])
      (clarsimp simp: always_safe_bounded_def progress_eventually)
qed (simp_all add: progress_regex_def)

lemma progress_regex_le: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
  by (auto intro!: progress_le_gen simp: Min_le_iff progress_regex_def)

lemma progress_MatchF_le: "progress \<sigma> P (Formula.MatchF I r) j \<le> progress_regex \<sigma> P r j"
  by (auto simp: trans_le_add1 progress_regex_def intro!: cInf_lower)

lemma progress_Release_cong:
  assumes "progress \<sigma> P \<phi> j = progress \<sigma> P' \<phi>' j" "progress \<sigma> P \<psi> j = progress \<sigma> P' \<psi>' j"
  shows "progress \<sigma> P (Formula.Release \<phi> I \<psi>) j = progress \<sigma> P' (Formula.Release \<phi>' I \<psi>') j"
  using assms
  by (simp only: progress.simps release_safe_bounded_def always_safe_bounded_def Formula.eventually_def once_def Formula.TT_def)


subsection \<open> Progress of LetPast \<close>

lemma not_contains_letpast_progress[simp]: 
  "\<not> contains_pred p \<phi> \<Longrightarrow> letpast_progress \<sigma> (P(p \<mapsto> x)) q \<phi> j = letpast_progress \<sigma> P q \<phi> j"
  by (cases "p = q") (simp_all add: letpast_progress_def fun_upd_twist[of p q])

lemma letpast_progress0: 
  "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> letpast_progress \<sigma> P p \<phi> 0 = 0"
  by (simp add: letpast_progress_def cInf_eq_minimum)

lemma letpast_progress_le:
  assumes "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "letpast_progress \<sigma> P p \<phi> j \<le> j"
proof -
  obtain i where "i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j" "i \<le> j"
    using progress_fixpoint_ex[OF assms] by blast
  then show ?thesis
    by (auto simp add: letpast_progress_def intro!: cInf_lower2[of i])
qed

lemma letpast_progress_fixpoint:
  assumes "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "progress \<sigma> (P(p \<mapsto> letpast_progress \<sigma> P p \<phi> j)) \<phi> j = letpast_progress \<sigma> P p \<phi> j"
proof -
  let ?A = "{i. i \<le> j \<and> i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j}"
  have nonempty: "?A \<noteq> {}" using progress_fixpoint_ex[OF assms] by simp
  then have "letpast_progress \<sigma> P p \<phi> j = Min ?A"
    by (simp add: letpast_progress_def cInf_eq_Min)
  moreover have "Min ?A \<in> ?A"
    using nonempty by (intro Min_in) auto
  ultimately show ?thesis by simp
qed

lemma letpast_progress_mono:
  assumes "pred_mapping (\<lambda>x. x \<le> j1) P1" and "pred_mapping (\<lambda>x. x \<le> j2) P2" and "j1 \<le> j2"
    and "rel_mapping (\<le>) P1 P2"
  shows "letpast_progress \<sigma> P1 p \<phi> j1 \<le> letpast_progress \<sigma> P2 p \<phi> j2"
  unfolding letpast_progress_def
proof (rule cInf_mono)
  let ?F1 = "\<lambda>i. progress \<sigma> (P1(p \<mapsto> i)) \<phi> j1"
  let ?F2 = "\<lambda>i. progress \<sigma> (P2(p \<mapsto> i)) \<phi> j2"
  show "{i. i \<le> j2 \<and> i = ?F2 i} \<noteq> {}"
    using progress_fixpoint_ex[OF assms(2)] by simp
  show "bdd_below {i. i \<le> j1 \<and> i = ?F1 i}"
    by simp
  fix k
  assume "k \<in> {i. i \<le> j2 \<and> i = ?F2 i}"
  then have k: "k \<le> j2" "k = ?F2 k"
    by simp_all
  have "\<exists>i \<le> min k j1. i = ?F1 i"
  proof (rule bounded_fixpoint_ex)
    show "mono_on {..min k j1} ?F1"
      using assms(1) by (intro mono_onI progress_mono_gen) (simp_all del: fun_upd_apply)
    show "\<forall>x \<le> min k j1. ?F1 x \<le> min k j1"
    proof (intro allI impI)
      fix x
      assume x: "x \<le> min k j1"
      have "?F1 x \<le> ?F2 k"
        using assms x k(1) by (intro progress_mono_gen) (simp_all del: fun_upd_apply)
      moreover have "?F1 x \<le> j1"
        using assms(1) x by (intro progress_le_gen) (simp del: fun_upd_apply)
      ultimately show "?F1 x \<le> min k j1"
        using k(2) by simp
    qed
  qed
  then show "\<exists>a \<in> {i. i \<le> j1 \<and> i = ?F1 i}. a \<le> k"
    by auto
qed

lemma le_letpast_progress_preservation:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P"
    and P': "pred_mapping (\<lambda>x. x \<le> j') P'"
    and PP': "rel_mapping (\<le>) P P'"
    and i: "i \<le> letpast_progress \<sigma> P p \<phi> j"
    and jj': "j \<le> j'"
  shows "progress \<sigma> (P(p \<mapsto> i)) \<phi> j \<le> letpast_progress \<sigma> P' p \<phi> j'"
  unfolding letpast_progress_def
proof (rule cInf_greatest)
  show "{k. k \<le> j' \<and> k = progress \<sigma> (P'(p \<mapsto> k)) \<phi> j'} \<noteq> {}"
    using progress_fixpoint_ex[OF P'] by simp
  fix k
  assume "k \<in> {k. k \<le> j' \<and> k = progress \<sigma> (P'(p \<mapsto> k)) \<phi> j'}"
  then have k: "k \<le> j'" "k = progress \<sigma> (P'(p \<mapsto> k)) \<phi> j'"
    by simp_all
  have "i \<le> letpast_progress \<sigma> P' p \<phi> j'"
    using i letpast_progress_mono[OF P P' jj' PP'] by (rule order_trans)
  also have "\<dots> \<le> k"
    unfolding letpast_progress_def using k by (intro cInf_lower) simp_all
  finally have ik: "i \<le> k" .
  have "i \<le> j"
    using i letpast_progress_le[OF P] by (rule order_trans)
  then have "progress \<sigma> (P(p \<mapsto> i)) \<phi> j \<le> progress \<sigma> (P'(p \<mapsto> k)) \<phi> j'"
    using P P' PP' jj' k(1) ik by (intro progress_mono_gen) simp_all
  then show "progress \<sigma> (P(p \<mapsto> i)) \<phi> j \<le> k"
    using k(2)[symmetric] by (rule ord_le_eq_trans)
qed


subsection \<open> Progress under safe recursion \<close>

lemma safe_letpast_progress_upd':
  fixes \<phi> :: "'t Formula.formula"
  shows "safe_letpast p \<phi> \<le> NonFutuRec \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P 
  \<Longrightarrow> x \<le> j \<Longrightarrow> y = (if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j) 
  \<Longrightarrow> min y (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
proof (induction \<phi> arbitrary: P p x y)
  case (Let e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  let ?p\<phi> = "\<lambda>P. progress \<sigma> P \<phi> j"
  let ?p\<psi> = "\<lambda>P. progress \<sigma> P \<psi> j"
  define y\<psi> where "y\<psi> = (if safe_letpast p \<psi> = NonFutuRec \<and> p \<noteq> ?en then x else min (Suc x) j)"
  define y\<phi> where "y\<phi> = (if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j)"
  define y\<phi>\<psi> where "y\<phi>\<psi> = (if safe_letpast ?en \<psi> = NonFutuRec then y\<phi> else min (Suc y\<phi>) j)"

  have P\<phi>_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> P))"
    using Let.prems(2) by (simp add: progress_le_gen)
  have Pmin_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
    using Let.prems(2,3) by (simp add: min.coboundedI1 y\<phi>_def)
  have P\<phi>x_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x))))"
    using Let.prems(2,3) by (simp add: progress_le_gen)

  have "?p\<psi> (P(p \<mapsto> x, ?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> min y\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))))"
  proof (cases "?en = p")
    case True
    then show ?thesis by simp
  next
    case False
    then have "?p\<psi> (P(p \<mapsto> x, ?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) = ?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)), p \<mapsto> x))"
      by (simp add: fun_upd_twist[of p])
    also have "\<dots> \<ge> min y\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))))"
    proof (rule Let.IH(2)[of p _ x y\<psi>, OF _ P\<phi>x_le Let.prems(3)])
      show "safe_letpast p \<psi> \<le> NonFutuRec"
        using Let.prems(1) False by simp
      show "y\<psi> = (if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j)"
        using False by (simp add: y\<psi>_def)
    qed
    finally show ?thesis .
  qed
  moreover have "safe_letpast ?en \<psi> * safe_letpast p \<phi> \<le> NonFutuRec"
    using Let.prems(1) by simp
  then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> min y (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
  proof (cases rule: mult_le_NonFutuRec_cases)
    case unused1
    then show ?thesis by (simp add: safe_letpast_Unused)
  next
    case unused2
    then show ?thesis by (simp add: safe_letpast_Unused)
  next
    case NonFutuRec
    have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> ?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
    proof (rule progress_mono_gen[OF order_refl Pmin_le P\<phi>x_le rel_mapping_le_map_upd])
      show "min y\<phi> (?p\<phi> P) \<le> ?p\<phi> (P(p \<mapsto> x))"
        using NonFutuRec(2) Let.prems(2,3) y\<phi>_def by (rule Let.IH(1))
    qed
    moreover have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
    proof (cases "y\<phi> \<le> ?p\<phi> P")
      case True
      then have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) = ?p\<psi> (P(?en \<mapsto> y\<phi>))" by simp
      also have "\<dots> = ?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>))" by simp
      also have "y\<phi> \<le> j" using Let.prems(3) by (simp add: y\<phi>_def)
      then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>)) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
        using NonFutuRec(1) P\<phi>_le Let.prems(3) y\<phi>\<psi>_def by (intro Let.IH(2))
      finally show ?thesis .
    next
      case False
      then show ?thesis by simp
    qed
    moreover have "y \<le> y\<phi>\<psi>"
      using Let.prems(1,3,4)
      by (auto simp add: y\<phi>\<psi>_def y\<phi>_def mult_eq_NonFutuRec_iff sup.absorb1)
    ultimately show ?thesis by simp
  qed
  moreover have "y \<le> y\<psi>"
    using Let.prems(1,3,4)
    by (auto simp add: y\<psi>_def mult_eq_NonFutuRec_iff sup.absorb2)
  ultimately show ?case by (simp del: fun_upd_apply)
next
  case (Frz e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
  let ?y\<psi> = "if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j"
  let ?p\<phi> = "progress \<sigma> P \<phi> j"
  let ?px\<phi> = "progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
  let ?a = "\<lambda>i. if i < ?p\<phi> then j else 0"
  let ?a' = "\<lambda>i. if i < ?px\<phi> then j else 0"
  let ?r = "progress \<sigma> P (Formula.Frz e \<phi> \<psi>) j"
  let ?r' = "progress \<sigma> (P(p \<mapsto> x)) (Formula.Frz e \<phi> \<psi>) j"
  have Px_le: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> x))"
    using Frz.prems(2,3) by simp
  have r_le: "?r \<le> j"
    by (rule progress_le_gen[OF Frz.prems(2)])
  have r'_le: "?r' \<le> j"
    by (rule progress_le_gen[OF Px_le])
  show ?case
  proof (cases "?en = p")
    case True
    show ?thesis
    proof (cases "safe_letpast ?en \<psi> = Unused")
      case psi_unused: True
      have not_contains: "\<not> contains_pred ?en \<psi>"
        using safe_letpast_Unused[OF psi_unused] .
      have p\<psi>_le: "progress \<sigma> P \<psi> j \<le> j"
        by (rule progress_le_gen[OF Frz.prems(2)])
      have px\<psi>_le: "progress \<sigma> (P(p \<mapsto> x)) \<psi> j \<le> j"
        by (rule progress_le_gen[OF Px_le])
      have r_eq: "?r = progress \<sigma> P \<psi> j"
        unfolding progress.simps Let_def
        using not_contains p\<psi>_le
        by (intro Least_equality) simp_all
      have r'_eq: "?r' = progress \<sigma> P \<psi> j"
        unfolding progress.simps Let_def
        using not_contains True px\<psi>_le
        by (intro Least_equality) simp_all
      show ?thesis
        using r'_eq r_eq by linarith
    next
      case psi_used: False
      have safe_\<phi>: "safe_letpast p \<phi> \<le> NonFutuRec"
        using Frz.prems(1) True psi_used by simp
      have y_eq: "y = ?y\<phi>"
        using Frz.prems(1,4) True psi_used
        by (simp add: frz_dep_def)
      have ge_\<phi>: "min ?y\<phi> ?p\<phi> \<le> ?px\<phi>"
        using Frz.IH(1)[OF safe_\<phi> Frz.prems(2,3)]
        by blast
      have r'_ex: "\<exists>i. i \<le> j \<and> progress \<sigma> (P(p \<mapsto> ?a' i)) \<psi> j \<le> i"
      proof
        have pm: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> ?a' j))"
          using Frz.prems(2) by auto
        moreover have "progress \<sigma> (P(p \<mapsto> ?a' j)) \<psi> j \<le> j"
          by (rule progress_le_gen[OF pm])
        ultimately show "j \<le> j \<and> progress \<sigma> (P(p \<mapsto> ?a' j)) \<psi> j \<le> j"
          by simp
      qed
      have r'_prop: "?r' \<le> j \<and> progress \<sigma> (P(p \<mapsto> ?a' ?r')) \<psi> j \<le> ?r'"
        unfolding progress.simps Let_def True fun_upd_upd
        by (rule LeastI_ex[OF r'_ex])
      show ?thesis
      proof (cases "?r' < min y ?r")
        case less_min: True
        have r'_lt_y: "?r' < y" and r'_lt_r: "?r' < ?r"
          using less_min by simp_all
        have a_le: "?a ?r' \<le> ?a' ?r'"
        proof (cases "?r' < ?p\<phi>")
          case True': True
          have "?r' < min ?y\<phi> ?p\<phi>"
            using r'_lt_y y_eq True' by simp
          also have "... \<le> ?px\<phi>"
            using ge_\<phi> by simp
          finally have "?r' < ?px\<phi>" .
          with True' show ?thesis by simp
        next
          case False
          then show ?thesis by simp
        qed
        have pm_l: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> ?a ?r'))"
          using Frz.prems(2) by auto
        have pm_r: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> ?a' ?r'))"
          using Frz.prems(2) by auto
        have rm: "rel_mapping (\<le>) (P(p \<mapsto> ?a ?r')) (P(p \<mapsto> ?a' ?r'))"
          by (rule rel_mapping_le_map_upd[OF a_le])
        have old_le: "progress \<sigma> (P(p \<mapsto> ?a ?r')) \<psi> j \<le> ?r'"
        proof -
          have "progress \<sigma> (P(p \<mapsto> ?a ?r')) \<psi> j \<le> progress \<sigma> (P(p \<mapsto> ?a' ?r')) \<psi> j"
            by (rule progress_mono_gen[OF order_refl pm_l pm_r rm])
          also have "... \<le> ?r'"
            using r'_prop by simp
          finally show ?thesis .
        qed
        have "?r' \<le> j \<and> progress \<sigma> (P(?en \<mapsto> ?a ?r')) \<psi> j \<le> ?r'"
          using r'_le old_le True by simp
        then have "?r \<le> ?r'"
          unfolding progress.simps(3)[of \<sigma> P] Let_def by (rule Least_le)
        with r'_lt_r show ?thesis by simp
      next
        case False
        then show ?thesis
          by linarith
      qed
    qed
  next
    case False
    show ?thesis
    proof (cases "safe_letpast ?en \<psi> = Unused")
      case psi_unused: True
      have not_contains: "\<not> contains_pred ?en \<psi>"
        using safe_letpast_Unused[OF psi_unused] .
      have safe_\<psi>: "safe_letpast p \<psi> \<le> NonFutuRec"
        using Frz.prems(1) False psi_unused by simp
      have y_eq: "y = ?y\<psi>"
        using Frz.prems(1,4) False psi_unused
        by (simp add: frz_dep_def)
      have p\<psi>_le: "progress \<sigma> P \<psi> j \<le> j"
        by (rule progress_le_gen[OF Frz.prems(2)])
      have px\<psi>_le: "progress \<sigma> (P(p \<mapsto> x)) \<psi> j \<le> j"
        by (rule progress_le_gen[OF Px_le])
      have r_eq: "?r = progress \<sigma> P \<psi> j"
        unfolding progress.simps Let_def
        using not_contains p\<psi>_le
        by (intro Least_equality) simp_all
      have r'_eq: "?r' = progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
        unfolding progress.simps Let_def
        using not_contains False px\<psi>_le
        by (intro Least_equality) (simp_all add: fun_upd_twist)
      show ?thesis
        using Frz.IH(2)[OF safe_\<psi> Frz.prems(2,3) y_eq]
        r_eq r'_eq by linarith
    next
      case psi_used: False
      have safe_\<phi>: "safe_letpast p \<phi> \<le> NonFutuRec"
        using Frz.prems(1) False psi_used by simp
      have safe_\<psi>: "safe_letpast p \<psi> \<le> NonFutuRec"
        using Frz.prems(1) False by simp
      have y_le_\<phi>: "y \<le> ?y\<phi>"
        using Frz.prems(1,4) False psi_used
        by (simp add: Frz.prems(3) frz_dep_def sup_eq_NonFutuRec_iff)
      have y_le_\<psi>: "y \<le> ?y\<psi>"
        using Frz.prems(1,4) False psi_used
        by (simp add: Frz.prems(3) frz_dep_def sup_eq_NonFutuRec_iff)
      have ge_\<phi>: "min ?y\<phi> ?p\<phi> \<le> ?px\<phi>"
        using Frz.IH(1)[OF safe_\<phi> Frz.prems(2,3)]
        by blast
      have r'_ex:
        "\<exists>i. i \<le> j \<and> progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a' i)) \<psi> j \<le> i"
      proof
        have pm: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> x, ?en \<mapsto> ?a' j))"
          using Frz.prems(2,3) False by (auto simp: fun_upd_twist)
        moreover have "progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a' j)) \<psi> j \<le> j"
          by (rule progress_le_gen[OF pm])
        ultimately show "j \<le> j \<and> progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a' j)) \<psi> j \<le> j"
          by simp
      qed
      have r'_prop:
        "?r' \<le> j \<and> progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a' ?r')) \<psi> j \<le> ?r'"
        unfolding progress.simps Let_def
        by (rule LeastI_ex[OF r'_ex])
      show ?thesis
      proof (cases "?r' < min y ?r")
        case True
        have r'_lt_y: "?r' < y" and r'_lt_r: "?r' < ?r"
          using True by simp_all
        have r'_lt_y\<phi>: "?r' < ?y\<phi>"
          using r'_lt_y y_le_\<phi> by linarith
        have r'_lt_y\<psi>: "?r' < ?y\<psi>"
          using r'_lt_y y_le_\<psi> by linarith
        have a_le: "?a ?r' \<le> ?a' ?r'"
        proof (cases "?r' < ?p\<phi>")
          case True': True
          have "?r' < min ?y\<phi> ?p\<phi>"
            using r'_lt_y\<phi> True' by simp
          also have "... \<le> ?px\<phi>"
            using ge_\<phi> by simp
          finally have "?r' < ?px\<phi>" .
          with True' show ?thesis by simp
        next
          case False
          then show ?thesis by simp
        qed
        have pm_mid: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> x, ?en \<mapsto> ?a ?r'))"
          using Frz.prems(2,3) False by (auto simp: fun_upd_twist)
        have pm_r: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> x, ?en \<mapsto> ?a' ?r'))"
          using Frz.prems(2,3) False by (auto simp: fun_upd_twist)
        have rm: "rel_mapping (\<le>) (P(p \<mapsto> x, ?en \<mapsto> ?a ?r')) (P(p \<mapsto> x, ?en \<mapsto> ?a' ?r'))"
          by (intro rel_mapping_map_upd a_le rel_mapping_order_refl)
        have mid_le: "progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a ?r')) \<psi> j \<le> ?r'"
        proof -
          have "progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a ?r')) \<psi> j
            \<le> progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a' ?r')) \<psi> j"
            by (rule progress_mono_gen[OF order_refl pm_mid pm_r rm])
          also have "... \<le> ?r'"
            using r'_prop by simp
          finally show ?thesis .
        qed
        have base_step:
          "min ?y\<psi> (progress \<sigma> (P(?en \<mapsto> ?a ?r')) \<psi> j)
            \<le> progress \<sigma> (P(?en \<mapsto> ?a ?r', p \<mapsto> x)) \<psi> j"
        proof (rule Frz.IH(2)[of p "P(?en \<mapsto> ?a ?r')" x ?y\<psi>])
          show "safe_letpast p \<psi> \<le> NonFutuRec"
            by (rule safe_\<psi>)
          show "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?a ?r'))"
            using Frz.prems(2) by auto
          show "x \<le> j"
            by (rule Frz.prems(3))
          show "?y\<psi> = (if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j)"
            by simp
        qed
        have base_le: "progress \<sigma> (P(?en \<mapsto> ?a ?r')) \<psi> j \<le> ?r'"
        proof -
          have "progress \<sigma> (P(?en \<mapsto> ?a ?r', p \<mapsto> x)) \<psi> j =
            progress \<sigma> (P(p \<mapsto> x, ?en \<mapsto> ?a ?r')) \<psi> j"
            using False by (simp add: fun_upd_twist)
          with base_step mid_le show ?thesis
            using r'_lt_y\<psi> by linarith
        qed
        have "?r \<le> ?r'"
          unfolding progress.simps Let_def
          using r'_le base_le False
          by (metis (lifting) not_less_Least progress.simps(3) r'_lt_r)
        with r'_lt_r show ?thesis by simp
      next
        case False
        then show ?thesis
          by linarith
      qed
    qed
  qed
next
  case (LetPast e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  let ?p\<phi> = "\<lambda>P. letpast_progress \<sigma> P ?en \<phi> j"
  let ?p\<phi>1 = "\<lambda>P. progress \<sigma> P \<phi> j"
  let ?p\<psi> = "\<lambda>P. progress \<sigma> P \<psi> j"
  define y\<psi> where "y\<psi> = (if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j)"
  define y\<phi> where "y\<phi> = (if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j)"
  define y\<phi>\<psi> where "y\<phi>\<psi> = (if safe_letpast ?en \<psi> = NonFutuRec then y\<phi> else min (Suc y\<phi>) j)"

  have P\<phi>_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> P))"
    using LetPast.prems(2) by (simp add: letpast_progress_le)
  have Pmin_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
    using LetPast.prems(2,3) by (simp add: min.coboundedI1 y\<phi>_def)
  have P\<phi>x_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x))))"
    using LetPast.prems(2,3) by (simp add: letpast_progress_le)

  show ?case
  proof (cases "?en = p")
    case True
    then show ?thesis by (simp add: letpast_progress_def del: fun_upd_apply)
  next
    case False
    have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)), p \<mapsto> x)) \<ge> min y\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))))"
    proof (rule LetPast.IH(2)[OF _ P\<phi>x_le LetPast.prems(3) y\<psi>_def])
      show "safe_letpast p \<psi> \<le> NonFutuRec"
        using LetPast.prems(1) False by simp
    qed
    moreover have "safe_letpast ?en \<psi> * safe_letpast p \<phi> \<le> NonFutuRec"
      using LetPast.prems(1) False by simp
    then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
    proof (cases rule: mult_le_NonFutuRec_cases)
      case unused1
      then show ?thesis by (simp add: safe_letpast_Unused)
    next
      case unused2
      then show ?thesis by (simp add: safe_letpast_Unused)
    next
      case NonFutuRec
      have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> ?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
      proof (rule progress_mono_gen[OF order_refl Pmin_le P\<phi>x_le rel_mapping_le_map_upd])
        have "min y\<phi> (?p\<phi> P) \<le> \<Sqinter> {i. i \<le> j \<and> i = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> i))}"
        proof (rule cInf_greatest)
          show "{i. i \<le> j \<and> i = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> i))} \<noteq> {}"
            using LetPast.prems(2,3) by (simp add: progress_fixpoint_ex)
        next
          fix fp
          assume fp: "fp \<in> {i. i \<le> j \<and> i = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> i))}"
          then have fp_unfold: "fp = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> fp))" by simp
          then have fp_twist: "fp = ?p\<phi>1 (P(?en \<mapsto> fp, p \<mapsto> x))"
            using False by (simp add: fun_upd_twist[of p])
          moreover have IH_fp: "\<dots> \<ge> min y\<phi> (?p\<phi>1 (P(?en \<mapsto> fp)))"
            using NonFutuRec(2) LetPast.prems(2,3) fp
            by (intro LetPast.IH(1)) (simp_all add: y\<phi>_def del: fun_upd_apply)
          moreover have "?p\<phi>1 (P(?en \<mapsto> fp)) \<ge> ?p\<phi> P" if *: "?p\<phi>1 (P(?en \<mapsto> fp)) \<le> y\<phi>"
          proof -
            have "?p\<phi>1 (P(?en \<mapsto> fp)) = min y\<phi> (?p\<phi>1 (P(?en \<mapsto> fp)))"
              using * by simp
            also have "\<dots> \<le> ?p\<phi>1 (P(?en \<mapsto> fp, p \<mapsto> x))"
              by (rule IH_fp)
            also have "\<dots> = fp"
              by (rule fp_twist[symmetric])
            finally have fp_ge: "?p\<phi>1 (P(?en \<mapsto> fp)) \<le> fp" .
            have "\<exists>fp'\<le>fp. fp' = ?p\<phi>1 (P(?en \<mapsto> fp'))"
            proof (rule bounded_fixpoint_ex)
              show "mono_on {..fp} (\<lambda>i. ?p\<phi>1 (P(?en \<mapsto> i)))"
                using LetPast.prems(2) fp by (intro mono_onI progress_mono_gen) simp_all
              show "\<forall>i \<le> fp. ?p\<phi>1 (P(?en \<mapsto> i)) \<le> fp"
              proof (intro allI impI)
                fix i
                assume "i \<le> fp"
                then have "?p\<phi>1 (P(?en \<mapsto> i)) \<le> ?p\<phi>1 (P(?en \<mapsto> fp))"
                  using LetPast.prems(2) fp by (intro progress_mono_gen) simp_all
                then show "?p\<phi>1 (P(?en \<mapsto> i)) \<le> fp"
                  using fp_ge by (rule order_trans)
              qed
            qed
            then obtain fp' where fp': "fp' \<le> fp" "fp' = ?p\<phi>1 (P(?en \<mapsto> fp'))"
              by blast
            then have "?p\<phi>1 (P(?en \<mapsto> fp')) \<le> ?p\<phi>1 (P(?en \<mapsto> fp))"
              using LetPast.prems(2) fp by (intro progress_mono_gen) simp_all
            then show ?thesis
              unfolding letpast_progress_def using fp fp'
              by (auto intro!: cInf_lower2[of fp'])
          qed
          ultimately show "min y\<phi> (?p\<phi> P) \<le> fp" by linarith
        qed
        then show "min y\<phi> (?p\<phi> P) \<le> ?p\<phi> (P(p \<mapsto> x))"
          by (subst (2) letpast_progress_def)
      qed
      moreover have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
      proof (cases "y\<phi> \<le> ?p\<phi> P")
        case True
        then have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) = ?p\<psi> (P(?en \<mapsto> y\<phi>))" by simp
        also have "\<dots> = ?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>))" by simp
        also have "y\<phi> \<le> j" using LetPast.prems(3) by (simp add: y\<phi>_def)
        then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>)) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
          using NonFutuRec(1) P\<phi>_le LetPast.prems(3) y\<phi>\<psi>_def by (intro LetPast.IH(2))
        finally show ?thesis .
      next
        case False
        then show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
    moreover have "y \<le> y\<psi>"
      using LetPast.prems(1,3,4) False
      by (simp add: y\<psi>_def sup.absorb2)
    moreover have "y \<le> y\<phi>\<psi>"
      using LetPast.prems(1,3,4) False
      by (auto simp add: y\<phi>\<psi>_def y\<phi>_def sup.absorb1 sup.absorb2)
    ultimately show ?thesis
      using False by (simp add: Let_def fun_upd_twist[of p] del: fun_upd_apply)
  qed
next
  case (Or \<phi> \<psi>)
  let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
  let ?y\<psi> = "if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j"
  have "min ?y\<phi> (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
    using Or.IH(1)[of p P x] Or.prems by (simp del: fun_upd_apply)
  moreover have "min ?y\<psi> (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
    using Or.IH(2)[of p P x] Or.prems by (simp del: fun_upd_apply)
  moreover have "y \<le> ?y\<phi>" and "y \<le> ?y\<psi>"
    using Or.prems(1,3,4) by (simp_all add: sup_eq_NonFutuRec_iff)
  ultimately show ?case
    unfolding progress.simps by linarith
next
  case (And \<phi> \<psi>)
  let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
  let ?y\<psi> = "if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j"
  have "min ?y\<phi> (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
    using And.IH(1)[of p P x] And.prems by (simp del: fun_upd_apply)
  moreover have "min ?y\<psi> (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
    using And.IH(2)[of p P x] And.prems by (simp del: fun_upd_apply)
  moreover have "y \<le> ?y\<phi>" and "y \<le> ?y\<psi>"
    using And.prems(1,3,4) by (simp_all add: sup_eq_NonFutuRec_iff)
  ultimately show ?case
    unfolding progress.simps by linarith
next
  case (Ands l)
  {
    fix \<phi> :: "'t Formula.formula"
    let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
    assume "\<phi> \<in> set l"
    then have "min ?y\<phi> (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Ands.IH[of \<phi> p P x] Ands.prems
      by (simp add: Sup_rec_safety_le_iff del: fun_upd_apply)
    moreover have "y \<le> ?y\<phi>"
    proof (cases "safe_letpast p (Formula.Ands l) = NonFutuRec")
      case True
      then show ?thesis
        using Ands.prems(3,4) by simp
    next
      case False
      have "safe_letpast p \<phi> \<le> safe_letpast p (Formula.Ands l)"
        using \<open>\<phi> \<in> set l\<close>
          Sup_rec_safety_le_iff[of "safe_letpast p ` set l" "safe_letpast p (Formula.Ands l)"]
        by simp
      with False Ands.prems(1) have "safe_letpast p \<phi> \<noteq> NonFutuRec"
        by (metis order.antisym)
      with False Ands.prems(4) show ?thesis
        by simp
    qed
    moreover have "(MIN \<phi>'\<in>set l. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> P \<phi> j"
      using \<open>\<phi> \<in> set l\<close> by (simp add: Min_le_iff)
    ultimately have "min y (MIN \<phi>'\<in>set l. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      by simp
  }
  then show ?case by (simp del: fun_upd_apply)
next
  case (Prev I \<phi>)
  let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
  have progress_Prev:
    "progress \<sigma> P' (Formula.Prev I \<phi>) j = min (Suc (progress \<sigma> P' \<phi> j)) j" for P'
    by simp
  have "safe_letpast p \<phi> \<le> NonFutuRec"
    using Prev.prems(1) by (cases "safe_letpast p \<phi>") simp_all
  then have "min ?y\<phi> (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
    using Prev.IH[of p P x] Prev.prems(2,3) by (simp del: fun_upd_apply)
  moreover have "x \<le> ?y\<phi>"
    using Prev.prems(3) by simp
  moreover have "y = min (Suc x) j"
    using Prev.prems(4) by (simp add: mult_eq_NonFutuRec_iff)
  ultimately show ?case
    unfolding progress_Prev by linarith
next
  case (Next I \<phi>)
  then show ?case
    by (simp add: mult_le_NonFutuRec_iff safe_letpast_Unused del: fun_upd_apply)
next
  case (Since \<phi> I \<psi>)
  show ?case 
  proof (cases "safe_letpast p (Formula.Since \<phi> I \<psi>) = NonFutuRec")
    case True
    then have "y = x"
      using Since.prems by simp
    moreover have "min x (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Since.prems
      by (auto intro!: order.trans[rotated, OF Since.IH(1)])
    moreover have "min x (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Since.prems
      by (auto simp add: mult_le_NonFutuRec_iff split: if_splits
          intro!: order.trans[rotated, OF Since.IH(2)])
    ultimately show ?thesis
      by (force simp del: fun_upd_apply)
  next
    case False
    then have y: "y = min (Suc x) j"
      using Since.prems by simp
    have "safe_letpast p \<phi> \<noteq> NonFutuRec"
      using False Since.prems by (auto simp add: sup_eq_NonFutuRec_iff)
    then have \<phi>_le: "min (min (Suc x) j) (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Since.prems
      by (auto intro!: order.trans[rotated, OF Since.IH(1)])
    have "memL I 0 \<Longrightarrow> safe_letpast p \<psi> \<noteq> NonFutuRec"
      using False Since.prems(1)
      by (auto simp add: sup_eq_NonFutuRec_iff)
    then have \<psi>_le: "if memL I 0
        then min (min (Suc x) j) (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j
        else min x (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Since.prems
      by (auto simp add: mult_le_NonFutuRec_iff split: if_splits
          intro!: order.trans[rotated, OF Since.IH(2)])
    let ?p\<phi> = "progress \<sigma> P \<phi> j" and ?p\<phi>' = "progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
    let ?p\<psi> = "progress \<sigma> P \<psi> j" and ?p\<psi>' = "progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
    from \<phi>_le y have \<phi>': "min y ?p\<phi> \<le> ?p\<phi>'"
      by simp
    show ?thesis
    proof (cases "memL I 0")
      case True
      with \<psi>_le y have \<psi>': "min y ?p\<psi> \<le> ?p\<psi>'"
        by simp
      have "min y (min ?p\<phi> ?p\<psi>) = min (min y ?p\<phi>) (min y ?p\<psi>)"
        by (simp add: ac_simps)
      also have "\<dots> \<le> min ?p\<phi>' ?p\<psi>'"
        using \<phi>' \<psi>' by (rule min.mono)
      finally show ?thesis
        using True by (simp del: fun_upd_apply)
    next
      case False
      with \<psi>_le have "min x ?p\<psi> \<le> ?p\<psi>'"
        by simp
      have "min y (Suc ?p\<psi>) \<le> min (Suc x) (Suc ?p\<psi>)"
        unfolding y by (intro min.mono min.cobounded1 order_refl)
      also have "\<dots> = Suc (min x ?p\<psi>)"
        by simp
      also have "\<dots> \<le> Suc ?p\<psi>'"
        using \<open>min x ?p\<psi> \<le> ?p\<psi>'\<close> by simp
      finally have \<psi>': "min y (Suc ?p\<psi>) \<le> Suc ?p\<psi>'" .
      have "min y (min ?p\<phi> (Suc ?p\<psi>)) = min (min y ?p\<phi>) (min y (Suc ?p\<psi>))"
        by (simp add: ac_simps)
      also have "\<dots> \<le> min ?p\<phi>' (Suc ?p\<psi>')"
        using \<phi>' \<psi>' by (rule min.mono)
      finally show ?thesis
        using False by (simp del: fun_upd_apply)
    qed
  qed
next
  case (Until \<phi> I \<psi>)
  then show ?case
    by (simp add: mult_le_NonFutuRec_iff sup_eq_Unused_iff 
        safe_letpast_Unused del: fun_upd_apply)
next
  case (Trigger \<phi> I \<psi>)
  then show ?case
  proof (cases "safe_letpast p (Formula.Trigger \<phi> I \<psi>) = NonFutuRec")
    case True
    then have "y = x"
      using Trigger.prems by simp
    moreover have "min x (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      thm Trigger.IH(1,2)[of p P x x]
      using Trigger.prems
      by (auto intro!: order.trans[rotated, OF Trigger.IH(1)])
    moreover have "min x (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Trigger.prems
      by (auto simp add: mult_le_NonFutuRec_iff split: if_splits
          intro!: order.trans[rotated, OF Trigger.IH(2)])
    ultimately show ?thesis
      by (force simp del: fun_upd_apply)
  next
    case False
    then have "y = min (Suc x) j"
      using Trigger.prems by simp
    moreover have "safe_letpast p \<phi> \<noteq> NonFutuRec"
      using False Trigger.prems by (auto simp add: sup_eq_NonFutuRec_iff)
    then have "min (min (Suc x) j) (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Trigger.prems
      by (auto intro!: order.trans[rotated, OF Trigger.IH(1)])
    moreover have "safe_letpast p \<psi> \<noteq> NonFutuRec"
      using False Trigger.prems by (auto simp add: sup_eq_NonFutuRec_iff)
    then have "min (min (Suc x) j) (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Trigger.prems
      by (auto intro!: order.trans[rotated, OF Trigger.IH(2)] split: if_splits)
    ultimately show ?thesis
      unfolding progress.simps by linarith
  qed
next
  case (Release \<phi> I \<psi>)
  then show ?case
    by (simp add: mult_le_NonFutuRec_iff sup_eq_Unused_iff 
        safe_letpast_Unused del: fun_upd_apply)
next
  case (MatchF I r)
  then show ?case
    by (auto simp add: mult_le_NonFutuRec_iff Sup_eq_Unused_iff 
        safe_letpast_Unused progress_regex_def
        simp del: fun_upd_apply dest!: subset_singletonD image_eqD)
next
  case (MatchP I r)
  {
    fix \<phi> :: "'t Formula.formula"
    let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
    assume "\<phi> \<in> regex.atms r"
    then have "min ?y\<phi> (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using MatchP.IH[of \<phi> p P x] MatchP.prems
      by (simp add: Sup_rec_safety_le_iff del: fun_upd_apply)
    moreover have "y \<le> ?y\<phi>"
    proof (cases "safe_letpast p (Formula.MatchP I r) = NonFutuRec")
      case True
      then show ?thesis
        using MatchP.prems(3,4) by simp
    next
      case False
      have "safe_letpast p \<phi> \<le> safe_letpast p (Formula.MatchP I r)"
        using \<open>\<phi> \<in> regex.atms r\<close>
          Sup_rec_safety_le_iff[of "safe_letpast p ` regex.atms r" "safe_letpast p (Formula.MatchP I r)"]
        by simp
      with False MatchP.prems(1) have "safe_letpast p \<phi> \<noteq> NonFutuRec"
        by (metis order.antisym)
      with False MatchP.prems(4) show ?thesis
        by simp
    qed
    moreover have "(MIN \<phi>'\<in>regex.atms r. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> P \<phi> j"
      using \<open>\<phi> \<in> regex.atms r\<close> by (simp add: Min_le_iff)
    ultimately have "min y (MIN \<phi>'\<in>regex.atms r. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      by simp
  }
  then show ?case by (simp add: progress_regex_def del: fun_upd_apply)
qed simp_all


lemma safe_letpast_progress_upd:
  "safe_letpast p \<phi> \<le> PastRec \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> x \<le> j \<Longrightarrow>
  progress \<sigma> (P(p \<mapsto> x)) \<phi> j \<ge> min (Suc x) (progress \<sigma> P \<phi> j)"
proof -
  assume past: "safe_letpast p \<phi> \<le> PastRec"
    and Pj: "pred_mapping (\<lambda>x. x \<le> j) P" and "x \<le> j"
  have "safe_letpast p \<phi> \<le> NonFutuRec" "safe_letpast p \<phi> \<noteq> NonFutuRec"
    using past by (cases "safe_letpast p \<phi>"; simp)+
  then have "min (min (Suc x) j) (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
    by (intro safe_letpast_progress_upd'[OF _ Pj \<open>x \<le> j\<close>]) simp_all
  moreover have "progress \<sigma> P \<phi> j \<le> j"
    by (rule progress_le_gen[OF Pj])
  ultimately show ?thesis
    by linarith
qed

lemma letpast_progress_PastRec:
  assumes past: "safe_letpast p \<phi> \<le> PastRec"
    and Pj: "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "letpast_progress \<sigma> P p \<phi> j \<ge> min (progress \<sigma> P \<phi> j) j"
  unfolding letpast_progress_def
proof (rule cInf_greatest)
  show "{i. i \<le> j \<and> i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j} \<noteq> {}"
    using progress_fixpoint_ex[OF Pj] by simp
  fix i
  assume "i \<in> {i. i \<le> j \<and> i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j}"
  then have i: "i \<le> j" and fp: "i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j"
    by simp_all
  have "min (Suc i) (progress \<sigma> P \<phi> j) \<le> i"
    using safe_letpast_progress_upd[OF past Pj i] fp[symmetric] by (rule ord_le_eq_trans)
  then show "min (progress \<sigma> P \<phi> j) j \<le> i"
    by (simp add: min_le_iff_disj)
qed

lemma letpast_progress_upd_idem: "letpast_progress \<sigma> (P(p \<mapsto> x)) p \<phi> j = letpast_progress \<sigma> P p \<phi> j"
  by (simp add: letpast_progress_def)

lemma progress_Suc_letpast_progress_eq:
  assumes past: "safe_letpast p \<phi> \<le> PastRec"
    and Pj: "pred_mapping (\<lambda>x. x \<le> j) P"
    and Suc_i: "Suc i = letpast_progress \<sigma> P p \<phi> j"
  shows "progress \<sigma> (P(p \<mapsto> i)) \<phi> j = letpast_progress \<sigma> P p \<phi> j"
proof -
  let ?lp = "letpast_progress \<sigma> P p \<phi> j"
  have lp_le: "?lp \<le> j"
    by (rule letpast_progress_le[OF Pj])
  have "i < ?lp"
    using Suc_i by simp
  with lp_le have i: "i \<le> j"
    by simp
  have Pij: "pred_mapping (\<lambda>x. x \<le> j) (P(p \<mapsto> i))"
    using Pj i by simp
  have "progress \<sigma> (P(p \<mapsto> i)) \<phi> j \<le> j"
    by (rule progress_le_gen[OF Pij])
  then have "progress \<sigma> (P(p \<mapsto> i)) \<phi> j = min (progress \<sigma> (P(p \<mapsto> i)) \<phi> j) j"
    by simp
  also have "\<dots> \<le> letpast_progress \<sigma> (P(p \<mapsto> i)) p \<phi> j"
    by (rule letpast_progress_PastRec[OF past Pij])
  also have "\<dots> = ?lp"
    by (rule letpast_progress_upd_idem)
  finally have le: "progress \<sigma> (P(p \<mapsto> i)) \<phi> j \<le> ?lp" .
  have "progress \<sigma> (P(p \<mapsto> ?lp)) \<phi> j = ?lp"
    by (rule letpast_progress_fixpoint[OF Pj])
  then have "?lp = min (Suc i) (progress \<sigma> (P(p \<mapsto> ?lp)) \<phi> j)"
    using Suc_i by simp
  also have "\<dots> \<le> progress \<sigma> (P(p \<mapsto> ?lp, p \<mapsto> i)) \<phi> j"
    using Pj lp_le i by (intro safe_letpast_progress_upd[OF past]) simp_all
  also have "\<dots> = progress \<sigma> (P(p \<mapsto> i)) \<phi> j"
    by simp
  finally show ?thesis
    using le by (rule antisym[rotated])
qed

lemma letpast_progress_ge:
  assumes safe: "safe_letpast p \<phi> \<le> PastRec"
    and ge_\<phi>: "\<exists>P j. dom P = S \<and> range_mapping x j P \<and> x \<le> progress \<sigma> P \<phi> j"
  shows "\<exists>P j. dom P = S \<and> range_mapping x j P \<and> x \<le> letpast_progress \<sigma> P p \<phi> j"
proof -
  from ge_\<phi> obtain P j where P: "dom P = S" "range_mapping x j P"
    and x: "x \<le> progress \<sigma> P \<phi> j"
    by blast
  from P(2) have Pj: "pred_mapping (\<lambda>x. x \<le> j) P"
    by (simp add: pred_mapping_alt)
  from x have "x \<le> min (progress \<sigma> P \<phi> j) j"
    by (simp add: min_absorb1 progress_le_gen[OF Pj])
  also have "\<dots> \<le> letpast_progress \<sigma> P p \<phi> j"
    by (rule letpast_progress_PastRec[OF safe Pj])
  finally show ?thesis
    using P by blast
qed

lemma letpast_progress_ignore_upd: 
  "letpast_progress \<sigma> (P(p := x)) p \<phi> j = letpast_progress \<sigma> P p \<phi> j"
  by (simp add: letpast_progress_def)


subsection \<open> Eventual progress \<close>

lemma progress_ge_gen:
  fixes \<phi> :: "'t Formula.formula"
  shows "Safety.future_bounded \<phi> \<Longrightarrow>
   \<exists>P j. dom P = S \<and> range_mapping i j P \<and> i \<le> progress \<sigma> P \<phi> j"
proof (induction \<phi> arbitrary: i S rule: formula_release_safe_bounded_induct)
  case (Pred e ts)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"])
      (auto split: option.splits if_splits simp: rel_mapping_alt pred_mapping_alt dom_def)
next
  case (Let p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  from Let.prems obtain P2 j2 where P2: "dom P2 = insert ?pn S" "range_mapping i j2 P2"
    "i \<le> progress \<sigma> P2 \<psi> j2"
    by (atomize_elim, intro Let(2)) auto
  from Let.prems obtain P1 j1 where P1: "dom P1 = S" "range_mapping (the (P2 ?pn)) j1 P1"
    "the (P2 ?pn) \<le> progress \<sigma> P1 \<phi> j1"
    by (atomize_elim, intro Let(1)) auto
  let ?P12 = "max_mapping P1 P2"
  have P1j: "pred_mapping (\<lambda>x. x \<le> j1) P1"
    using P1(2) by (rule range_mapping_to_pred_mapping)
  have P2j: "pred_mapping (\<lambda>x. x \<le> j2) P2"
    using P2(2) by (rule range_mapping_to_pred_mapping)
  have P12_bound: "pred_mapping (\<lambda>x. x \<le> max j1 j2) ?P12"
    using P1j P2j by (rule pred_mapping_max_mapping)
  have P12'_bound: "pred_mapping (\<lambda>x. x \<le> max j1 j2) (?P12(?pn := P1 ?pn))"
  proof -
    have "pred_mapping (\<lambda>x. x \<le> max j1 j2) P1"
      using P1j by (rule pred_mapping_mono) auto
    with P12_bound show ?thesis
      by (auto simp: pred_mapping_def)
  qed
  have le1: "progress \<sigma> P1 \<phi> j1 \<le> progress \<sigma> (?P12(?pn := P1 ?pn)) \<phi> (max j1 j2)"
  proof (rule progress_mono_gen[OF max.cobounded1 P1j P12'_bound])
    have "rel_mapping (\<le>) P1 ?P12"
      using P1(1) P2(1) by (intro max_mapping_cobounded1) auto
    then show "rel_mapping (\<le>) P1 (?P12(?pn := P1 ?pn))"
      by (auto simp: rel_mapping_def rel_fun_def intro: option.rel_refl)
  qed
  have le2: "progress \<sigma> P2 \<psi> j2 \<le> progress \<sigma> (?P12(?pn \<mapsto> progress \<sigma> P1 \<phi> j1)) \<psi> (max j1 j2)"
    using P1 P2 P12_bound 
    by (intro progress_mono_gen) (auto simp: rel_mapping_alt max_mapping_def split: option.splits
      intro!: max.coboundedI1 progress_le_gen
      elim: pred_mapping_mono intro!: pred_mapping_map_upd)
  show ?case
    unfolding progress.simps
  proof (intro exI[of _ "?P12(?pn := P1 ?pn)"] exI[of _ "max j1 j2"] conjI)
    show "dom (?P12(?pn := P1 ?pn)) = S"
      using P1(1) P2(1) by auto
  next
    have "i \<le> the (P2 ?pn)"
      using P2(1,2) by (simp add: pred_mapping_alt)
    with P1(2) have P1i: "range_mapping i j1 P1"
      by (rule range_mapping_relax) simp
    have "range_mapping i (max j1 j2) P1"
      using P1i by (rule range_mapping_relax) simp_all
    with range_mapping_max_mapping[OF P1i P2(2)]
    show "range_mapping i (max j1 j2) (?P12(?pn := P1 ?pn))"
      by (auto simp: pred_mapping_def)
  next
    have "i \<le> progress \<sigma> P2 \<psi> j2" by fact
    also have "... \<le> progress \<sigma> (?P12(?pn \<mapsto> progress \<sigma> P1 \<phi> j1)) \<psi> (max j1 j2)"
      using le2 by blast
    also have "... \<le> progress \<sigma> 
      ((?P12(?pn := P1 ?pn))(?pn\<mapsto>progress \<sigma> (?P12(?pn := P1 ?pn)) \<phi> (max j1 j2))) \<psi> (max j1 j2)"
    proof (rule progress_mono_gen[OF order_refl])
      have "progress \<sigma> P1 \<phi> j1 \<le> max j1 j2"
        by (rule max.coboundedI1[OF progress_le_gen[OF P1j]])
      with P12_bound show "pred_mapping (\<lambda>x. x \<le> max j1 j2) (?P12(?pn \<mapsto> progress \<sigma> P1 \<phi> j1))"
        by simp
      show "pred_mapping (\<lambda>x. x \<le> max j1 j2)
        ((?P12(?pn := P1 ?pn))(?pn \<mapsto> progress \<sigma> (?P12(?pn := P1 ?pn)) \<phi> (max j1 j2)))"
        unfolding fun_upd_upd
        by (intro pred_mapping_map_upd progress_le_gen P12'_bound P12_bound)
      show "rel_mapping (\<le>) (?P12(?pn \<mapsto> progress \<sigma> P1 \<phi> j1))
        ((?P12(?pn := P1 ?pn))(?pn \<mapsto> progress \<sigma> (?P12(?pn := P1 ?pn)) \<phi> (max j1 j2)))"
        using le1 by simp
    qed
    finally show "i \<le> ..." .
  qed
next
  case (Frz p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  obtain P1 j1 where P1: "dom P1 = S" "range_mapping (Suc i) j1 P1"
    "Suc i \<le> progress \<sigma> P1 \<phi> j1"
    using Frz(1)[of S "Suc i"] Frz.prems by auto
  obtain P2 j2 where P2: "dom P2 = insert ?pn S" "range_mapping i j2 P2"
    "i \<le> progress \<sigma> P2 \<psi> j2"
    using Frz(2)[of "insert ?pn S" i] Frz.prems by auto
  let ?j = "max j1 j2"
  let ?P12 = "max_mapping P1 P2"
  have P1i: "range_mapping i j1 P1"
    using P1(2) by (rule range_mapping_relax) auto
  have P12_rng: "range_mapping i ?j ?P12"
    using P1i P2(2) by simp
  have P12_phi: "Suc i \<le> progress \<sigma> ?P12 \<phi> ?j"
    using P1(1,2) P2(1,2,3)
    by (intro order.trans[OF P1(3) progress_mono_gen[OF max.coboundedI1]])
      (auto intro: max_mapping_cobounded1 simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
  have j_ge_i: "i \<le> ?j"
    using P2(1,2)
    by (auto simp: pred_mapping_alt)
  have P2_le: "progress \<sigma> P2 \<psi> j2 \<le> progress \<sigma> (?P12(?pn \<mapsto> ?j)) \<psi> ?j"
  proof (rule progress_mono_gen[OF max.coboundedI2])
    show "pred_mapping (\<lambda>x. x \<le> j2) P2"
      using P2(2) by (rule range_mapping_to_pred_mapping)
    show "pred_mapping (\<lambda>x. x \<le> ?j) (?P12(?pn \<mapsto> ?j))"
      using P12_rng by (simp add: pred_mapping_alt)
    show "rel_mapping (\<le>) P2 (?P12(?pn \<mapsto> ?j))"
      using P1(1) P2(1,2)
      by (auto simp: rel_mapping_alt max_mapping_def pred_mapping_alt split: option.splits)
  qed simp
  show ?case
  proof (intro exI[of _ ?P12] exI[of _ ?j] conjI)
    show "dom ?P12 = S"
      using P1(1) P2(1) by auto
    show "range_mapping i ?j ?P12"
      by (rule P12_rng)
    show "i \<le> progress \<sigma> ?P12 (Formula.Frz p \<phi> \<psi>) ?j"
    proof (rule ccontr)
      assume ni: "\<not> i \<le> progress \<sigma> ?P12 (Formula.Frz p \<phi> \<psi>) ?j"
      let ?r = "progress \<sigma> ?P12 (Formula.Frz p \<phi> \<psi>) ?j"
      have r_lt_i: "?r < i"
        using ni by simp
      have ex_r: "\<exists>k. k \<le> ?j \<and> progress \<sigma> (?P12(?pn \<mapsto> (if k < progress \<sigma> ?P12 \<phi> ?j then ?j else 0))) \<psi> ?j \<le> k"
      proof
        have "pred_mapping (\<lambda>x. x \<le> ?j) (?P12(?pn \<mapsto> (if ?j < progress \<sigma> ?P12 \<phi> ?j then ?j else 0)))"
          using P12_rng by (simp add: pred_mapping_alt)
        then have "progress \<sigma> (?P12(?pn \<mapsto> (if ?j < progress \<sigma> ?P12 \<phi> ?j then ?j else 0))) \<psi> ?j \<le> ?j"
          by (rule progress_le_gen)
        then show "?j \<le> ?j \<and> progress \<sigma> (?P12(?pn \<mapsto> (if ?j < progress \<sigma> ?P12 \<phi> ?j then ?j else 0))) \<psi> ?j \<le> ?j"
          by simp
      qed
      have r_prop: "?r \<le> ?j \<and> progress \<sigma> (?P12(?pn \<mapsto> (if ?r < progress \<sigma> ?P12 \<phi> ?j then ?j else 0))) \<psi> ?j \<le> ?r"
        unfolding progress.simps Let_def by (rule LeastI_ex[OF ex_r])
      have r_lt_phi: "?r < progress \<sigma> ?P12 \<phi> ?j"
        using r_lt_i P12_phi by linarith
      hence r_psi_le: "progress \<sigma> (?P12(?pn \<mapsto> ?j)) \<psi> ?j \<le> ?r"
        using r_prop by simp
      have "i \<le> progress \<sigma> (?P12(?pn \<mapsto> ?j)) \<psi> ?j"
        using P2(3) P2_le by linarith
      with r_psi_le r_lt_i show False
        by linarith
    qed
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  from LetPast.prems obtain P2 j2 
    where P2: "dom P2 = insert ?pn S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<psi> j2"
    by (atomize_elim, intro LetPast(2)) auto
  from LetPast.prems have safe: "safe_letpast ?pn \<phi> \<le> PastRec" and fb_\<phi>: "Safety.future_bounded \<phi>"
    by simp_all
  obtain P1 j1 
    where P1: "dom P1 = insert ?pn S" "range_mapping (the (P2 ?pn)) j1 P1"
    "the (P2 ?pn) \<le>letpast_progress \<sigma> P1 ?pn \<phi> j1"
    using letpast_progress_ge[OF safe LetPast(1)[OF fb_\<phi>]] by blast
  let ?P12 = "max_mapping P1 P2"
  have P1j: "pred_mapping (\<lambda>x. x \<le> j1) P1"
    using P1(2) by (rule range_mapping_to_pred_mapping)
  have P2j: "pred_mapping (\<lambda>x. x \<le> j2) P2"
    using P2(2) by (rule range_mapping_to_pred_mapping)
  have P12_bound: "pred_mapping (\<lambda>x. x \<le> max j1 j2) ?P12"
    using P1j P2j by (rule pred_mapping_max_mapping)
  have P12_upd_bound: "pred_mapping (\<lambda>x. x \<le> max j1 j2) (?P12(?pn \<mapsto> letpast_progress \<sigma> P1 ?pn \<phi> j1))"
  proof -
    have "letpast_progress \<sigma> P1 ?pn \<phi> j1 \<le> max j1 j2"
      by (rule max.coboundedI1[OF letpast_progress_le[OF P1j]])
    with P12_bound show ?thesis
      by simp
  qed
  have le2: "progress \<sigma> P2 \<psi> j2 
    \<le> progress \<sigma> (?P12(?pn \<mapsto> letpast_progress \<sigma> P1 ?pn \<phi> j1)) \<psi> (max j1 j2)"
  proof (rule progress_mono_gen[OF max.cobounded2 P2j P12_upd_bound])
    show "rel_mapping (\<le>) P2 (?P12(?pn \<mapsto> letpast_progress \<sigma> P1 ?pn \<phi> j1))"
      using P1(1,3) P2(1) by (intro rel_mapping_max_mapping_fun_upd) simp_all
  qed
  let ?P12' = "?P12(?pn := if ?pn \<in> S then P1 ?pn else None)"
  show ?case
    unfolding progress.simps Let_def
  proof (intro exI[of _ "?P12'"] exI[of _ "max j1 j2"] conjI)
    have "P1 ?pn \<noteq> None"
      using P1(1) by auto
    then show "dom ?P12' = S"
      using P1(1) P2(1) by auto
  next
    have "i \<le> the (P2 ?pn)"
      using P2(1,2) by (simp add: pred_mapping_alt)
    with P1(2) have P1i: "range_mapping i j1 P1"
      by (rule range_mapping_relax) simp
    have "range_mapping i (max j1 j2) P1"
      using P1i by (rule range_mapping_relax) simp_all
    with range_mapping_max_mapping[OF P1i P2(2)]
    show "range_mapping i (max j1 j2) ?P12'"
      by (auto simp: pred_mapping_def)
  next
    have "i \<le> progress \<sigma> P2 \<psi> j2" by fact
    also have "... \<le> progress \<sigma> (?P12(?pn \<mapsto> letpast_progress \<sigma> P1 ?pn \<phi> j1)) \<psi> (max j1 j2)"
      using le2 by blast
    also have "... \<le> progress \<sigma> (?P12'(?pn \<mapsto> letpast_progress \<sigma> ?P12' ?pn \<phi> (max j1 j2))) \<psi> (max j1 j2)"
      unfolding fun_upd_upd letpast_progress_ignore_upd
    proof (rule progress_mono_gen[OF order_refl P12_upd_bound])
      show "pred_mapping (\<lambda>x. x \<le> max j1 j2) (?P12(?pn \<mapsto> letpast_progress \<sigma> ?P12 ?pn \<phi> (max j1 j2)))"
        by (intro pred_mapping_map_upd letpast_progress_le P12_bound)
      have "rel_mapping (\<le>) P1 ?P12"
        using P1(1) P2(1) by (intro max_mapping_cobounded1) simp
      then have "letpast_progress \<sigma> P1 ?pn \<phi> j1 \<le> letpast_progress \<sigma> ?P12 ?pn \<phi> (max j1 j2)"
        by (rule letpast_progress_mono[OF P1j P12_bound max.cobounded1])
      then show "rel_mapping (\<le>) (?P12(?pn \<mapsto> letpast_progress \<sigma> P1 ?pn \<phi> j1))
        (?P12(?pn \<mapsto> letpast_progress \<sigma> ?P12 ?pn \<phi> (max j1 j2)))"
        by (rule rel_mapping_le_map_upd)
    qed
    also have "... \<le> progress \<sigma> (?P12'(?pn \<mapsto>(Inf {i. i \<le> max j1 j2 \<and> i = progress \<sigma> (?P12'(?pn \<mapsto> i)) \<phi> (max j1 j2)}))) \<psi> (max j1 j2)"
      unfolding letpast_progress_def by(auto)
    finally show "i \<le> ..." .
  qed
next
  case (Eq _ _)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (Less _ _)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (LessEq _ _)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (Or \<phi>1 \<phi>2)
  from Or(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using Or(1)[of S i] by auto
  moreover
  from Or(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using Or(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Or \<phi>1 \<phi>2) (max j1 j2)"
    by (auto 0 3 elim!: order.trans[OF _ progress_mono_gen] 
        intro: max_mapping_cobounded1 max_mapping_cobounded2 simp:range_mapping_to_pred_mapping)
        (auto simp: pred_mapping_max_mapping range_mapping_to_pred_mapping)
  with P1 P2 show ?case 
    by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) 
      auto
next
  case (And \<phi>1 \<phi>2)
  from And(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using And(1)[of S i] by auto
  moreover
  from And(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using And(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.And \<phi>1 \<phi>2) (max j1 j2)"
    by (auto 0 3 elim!: order.trans[OF _ progress_mono_gen] 
        intro: max_mapping_cobounded1 max_mapping_cobounded2 simp:range_mapping_to_pred_mapping)
        (auto simp: pred_mapping_max_mapping range_mapping_to_pred_mapping)
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) auto
next
  case (Ands l)
  show ?case proof (cases "l = []")
    case True
    then show ?thesis
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"])
        (auto split: if_splits simp: pred_mapping_alt)
  next
    case False
    then obtain \<phi> where "\<phi> \<in> set l" by (cases l) auto
    from Ands.prems have "\<forall>\<phi>\<in>set l. Safety.future_bounded \<phi>"
      by (simp add: list.pred_set)
    { fix \<phi>
      assume "\<phi> \<in> set l"
      with Ands.prems obtain P j where "dom P = S" "range_mapping i j P" "i \<le> progress \<sigma> P \<phi> j"
        by (atomize_elim, intro Ands(1)[of \<phi> S i]) (auto simp: list.pred_set)
      hence "\<exists>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) 
        \<and> i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)" (is "\<exists>Pj. ?P Pj")
        by (intro exI[of _ "(P, j)"]) auto
    }
    hence "\<forall>\<phi>\<in>set l. \<exists>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) 
        \<and> i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)" (is "\<forall>\<phi>\<in>set l. \<exists>Pj. ?P Pj \<phi>")
      by blast
    with Ands(1) Ands.prems False have "\<exists>Pjf. \<forall>\<phi>\<in>set l. ?P (Pjf \<phi>) \<phi>"
      by (auto simp: Ball_def intro: choice)
    then obtain Pjf where Pjf: "\<forall>\<phi>\<in>set l. ?P (Pjf \<phi>) \<phi>" ..
    define Pf where "Pf = fst o Pjf"
    define jf where "jf = snd o Pjf"
    have *: "dom (Pf \<phi>) = S" "range_mapping i (jf \<phi>) (Pf \<phi>)" "i \<le> progress \<sigma> (Pf \<phi>) \<phi> (jf \<phi>)"
      if "\<phi> \<in> set l" for \<phi>
      using Pjf[THEN bspec, OF that] 
      unfolding Pf_def jf_def by auto
    let ?P = "Max_mapping (Pf ` set l)" and ?j = "MAX \<phi>\<in>set l. jf \<phi>"
    have dom: "dom ?P = S"
      using False *(1) by auto
    have rng: "range_mapping i ?j ?P"
      using False *(2) by (intro range_mapping_Max_mapping[of "set l" i jf Pf]) auto
    have "i \<le> progress \<sigma> ?P \<phi> ?j" if "\<phi> \<in> set l" for \<phi>
    proof -
      have "i \<le> progress \<sigma> (Pf \<phi>) \<phi> (jf \<phi>)"
        using that by (rule *(3))
      also have "\<dots> \<le> progress \<sigma> ?P \<phi> ?j"
      proof (rule progress_mono_gen)
        show "jf \<phi> \<le> ?j"
          using that by simp
        show "pred_mapping (\<lambda>x. x \<le> jf \<phi>) (Pf \<phi>)"
          using *(2)[OF that] by (rule range_mapping_to_pred_mapping)
        show "pred_mapping (\<lambda>x. x \<le> ?j) ?P"
          using rng by (rule range_mapping_to_pred_mapping)
        show "rel_mapping (\<le>) (Pf \<phi>) ?P"
          using that *(1) by (intro Max_mapping_coboundedI) auto
      qed
      finally show ?thesis .
    qed
    with False have "i \<le> progress \<sigma> ?P (formula.Ands l) ?j"
      by simp
    with dom rng show ?thesis
      by blast
  qed
next
  case (Prev I \<phi>)
  then obtain P j where "dom P = S" "range_mapping i j P" "i \<le> progress \<sigma> P \<phi> j"
    by (atomize_elim, intro Prev(1)) (auto simp: pred_mapping_alt dom_def)
  with Prev(2) have "dom P = S \<and> range_mapping i (max i j) P 
    \<and> i \<le> progress \<sigma> P (formula.Prev I \<phi>) (max i j)"
    by (auto simp: le_Suc_eq max_def pred_mapping_alt split: if_splits
        elim: order.trans[OF _ progress_mono])
  then show ?case by blast
next
  case (Next I \<phi>)
  then obtain P j where "dom P = S" "range_mapping (Suc i) j P" "Suc i \<le> progress \<sigma> P \<phi> j"
    by (atomize_elim, intro Next(1)) (auto simp: pred_mapping_alt dom_def)
  then show ?case
    by (intro exI[of _ P] exI[of _ j]) (auto 0 4 simp: pred_mapping_alt dom_def)
next
  case (Since \<phi>1 I \<phi>2)
  from Since(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using Since(1)[of S i] by auto
  moreover
  from Since(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using Since(2)[of S i] by auto
  ultimately have
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>1 (max j1 j2)"
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>2 (max j1 j2)"
    by (auto elim!: order.trans[OF _ progress_mono_gen] simp: max_mapping_cobounded1 max_mapping_cobounded2)
      (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
  then have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Since \<phi>1 I \<phi>2) (max j1 j2)"
    by simp
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"])
      (auto elim!: pred_mapping_le intro: max_mapping_cobounded1)
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then obtain i' where "i < i'" and 1: "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  from Until.prems obtain P1 j1 where P1: "dom P1 = S" "range_mapping (Suc i') j1 P1" "Suc i' \<le> progress \<sigma> P1 \<phi>1 j1"
    by (atomize_elim, intro Until(1)) (auto simp: pred_mapping_alt dom_def)
  from Until.prems obtain P2 j2 where P2: "dom P2 = S" "range_mapping (Suc i') j2 P2" "Suc i' \<le> progress \<sigma> P2 \<phi>2 j2"
    by (atomize_elim, intro Until(2)) (auto simp: pred_mapping_alt dom_def)
  let ?P12 = "max_mapping P1 P2"
  have "i \<le> progress \<sigma> ?P12 (Formula.Until \<phi>1 I \<phi>2) (max j1 j2)"
    unfolding progress.simps
  proof (intro cInf_greatest, goal_cases nonempty greatest)
    case nonempty
    then show ?case
      by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
  next
    case (greatest x)
    from P1(2,3) have "i' < j1"
      by (auto simp: less_eq_Suc_le intro!: progress_le_gen elim!: order.trans pred_mapping_mono_strong)
    then have "i' < max j1 j2" by simp
    have "progress \<sigma> P1 \<phi>1 j1 \<le> progress \<sigma> ?P12 \<phi>1 (max j1 j2)"
      using P1 P2
      by (auto intro!: progress_mono_gen max_mapping_cobounded1)
         (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
    moreover have "progress \<sigma> P2 \<phi>2 j2 \<le> progress \<sigma> ?P12 \<phi>2 (max j1 j2)"
      using P1 P2
      by (auto intro!: progress_mono_gen max_mapping_cobounded2)
         (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
    ultimately have "i' \<le> min (progress \<sigma> ?P12 \<phi>1 (max j1 j2)) (progress \<sigma> ?P12 \<phi>2 (max j1 j2))"
      using P1(3) P2(3) by simp
    with greatest \<open>i' < max j1 j2\<close> have "memR I (\<tau> \<sigma> i' - \<tau> \<sigma> x)"
      by simp
    with 1 have "\<tau> \<sigma> i < \<tau> \<sigma> x"
      by (auto 0 3 elim: contrapos_np)
    then show ?case by (auto dest!: less_\<tau>D)
  qed
  with P1 P2 \<open>i < i'\<close> show ?case
    by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) (auto simp: range_mapping_relax)
next
  case (Trigger \<phi>1 I \<phi>2)
  hence f_bdd1: "Safety.future_bounded \<phi>1" 
    and f_bdd2: "Safety.future_bounded \<phi>2"
    by clarsimp+
  have size':
    "size' \<phi>1 \<le> size' \<phi>1 + size' \<phi>2"
    "size' \<phi>2 \<le> size' \<phi>1 + size' \<phi>2"
    by auto
  obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using Trigger(1)[OF f_bdd1, of S i] by auto
  moreover
  obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using Trigger(2)[OF f_bdd2, of S i] by auto
  ultimately have
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>1 (max j1 j2)"
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>2 (max j1 j2)"
    by (auto elim!: order.trans[OF _ progress_mono_gen] simp: max_mapping_cobounded1 max_mapping_cobounded2)
      (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
  then have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Trigger \<phi>1 I \<phi>2) (max j1 j2)"
    by simp
  with P1 P2 show ?case 
    by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"])
      (auto elim!: pred_mapping_le intro: max_mapping_cobounded1 split: if_splits)
next
  case (Release \<phi>1 I \<phi>2)
  from Release(4) have "bounded (flip_int_double_upper I)"
    by (transfer) auto
  then obtain m where "\<not> memR (flip_int_double_upper I) m"
    by (auto simp: bounded_memR)

  then obtain i' where "i < i'" and 1: "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  then have not_mem_I: "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using memR_flip_int_double_upper
    by auto

  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    obtain P1 j1 
      where P1: "dom P1 = S" "range_mapping (Suc i') j1 P1" "Suc i' \<le> progress \<sigma> P1 \<phi>1 j1"
      using Release(4) True
      by (atomize_elim, intro Release(1)) 
        (auto simp: pred_mapping_alt dom_def)
    obtain P2 j2 
      where P2: "dom P2 = S" "range_mapping (Suc i') j2 P2" "Suc i' \<le> progress \<sigma> P2 \<phi>2 j2"
      using Release(4) True
      by (atomize_elim, intro Release(2)) 
        (auto simp: pred_mapping_alt dom_def)
    let ?P12 = "max_mapping P1 P2"

    have "i \<le> progress \<sigma> ?P12 (Formula.Release \<phi>1 I \<phi>2) (max j1 j2)"
      unfolding progress.simps if_P[OF True]
    proof (intro cInf_greatest, goal_cases nonempty greatest)
      case nonempty
      then show ?case
        by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
    next
      case (greatest x)
      from P1(2,3) have "i' < j1"
        by (auto simp: less_eq_Suc_le intro!: progress_le_gen elim!: order.trans pred_mapping_mono_strong)
      then have "i' < max j1 j2" by simp
      have "progress \<sigma> P1 \<phi>1 j1 \<le> progress \<sigma> ?P12 \<phi>1 (max j1 j2)"
        using P1(1) P2(1) pred_mapping_max_mapping[of j1 P1 j2 P2] 
          range_mapping_to_pred_mapping[OF P1(2)]
          range_mapping_to_pred_mapping[OF P2(2)]
        by (auto intro!: progress_mono_gen max_mapping_cobounded1)
      moreover have "progress \<sigma> P2 \<phi>2 j2 \<le> progress \<sigma> ?P12 \<phi>2 (max j1 j2)"
        using P1(1) P2(1) pred_mapping_max_mapping[of j1 P1 j2 P2] 
          range_mapping_to_pred_mapping[OF P1(2)]
          range_mapping_to_pred_mapping[OF P2(2)]
        by (auto intro!: progress_mono_gen max_mapping_cobounded2)
      ultimately have "i' \<le> min (progress \<sigma> ?P12 \<phi>1 (max j1 j2)) (progress \<sigma> ?P12 \<phi>2 (max j1 j2))"
        using P1(3) P2(3) by simp
      with greatest \<open>i' < max j1 j2\<close> have
        "memR (flip_int_double_upper I) (\<tau> \<sigma> i' - \<tau> \<sigma> x) \<or> memR (I) (\<tau> \<sigma> i' - \<tau> \<sigma> x)"
        by auto
      with 1 not_mem_I have "\<tau> \<sigma> i < \<tau> \<sigma> x"
        by (auto 0 3 elim: contrapos_np)
      then show ?case by (auto dest!: less_\<tau>D)
    qed
    then show ?thesis
      using P1 P2 \<open>i < i'\<close>
      by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) (auto simp: range_mapping_relax)
  next
    case False
    have "\<not> memL I 0"
      using False memR_zero by blast
    then have "bounded (flip_int_less_lower I)"
      using flip_int_less_lower_props by blast
    with Release(4) False have future_bounded: "Safety.future_bounded (release_safe_bounded \<phi>1 I \<phi>2)"
      by (simp add: release_safe_bounded_def)
    show ?thesis 
      using Release(3)[OF False future_bounded] False by auto
  qed
next
  case (MatchP I r)
  then show ?case
  proof (cases "regex.atms r = {}")
    case True
    with MatchP.prems show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"] exI[of _ i])
        (auto split: if_splits simp: pred_mapping_alt regex.pred_set)
  next
    case False
    define pick where "pick = (\<lambda>\<phi> :: 't Formula.formula. SOME Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and>
       i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj))"
    let ?pickP = "fst o pick" let ?pickj = "snd o pick"
    from MatchP have pick: "\<phi> \<in> regex.atms r \<Longrightarrow> dom (?pickP \<phi>) = S \<and>
      range_mapping i (?pickj \<phi>) (?pickP \<phi>) \<and> i \<le> progress \<sigma> (?pickP \<phi>) \<phi> (?pickj \<phi>)" for \<phi>
      unfolding pick_def o_def future_bounded.simps regex.pred_set
      by (intro someI_ex[where P = "\<lambda>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and>
         i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"]) auto
    from pick have pred_pick: "\<phi> \<in> regex.atms r \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> ?pickj \<phi>) (?pickP \<phi>)" for \<phi>
      by (force elim: pred_mapping_mono)
    with pick False show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "Max_mapping (?pickP ` regex.atms r)"] exI[of _ "Max (?pickj ` regex.atms r)"])
        (auto simp: Max_mapping_coboundedI range_mapping_Max_mapping[of _ 0, simplified]
          order_trans[OF pick[THEN conjunct2, THEN conjunct2] progress_mono_gen])
  qed
next
  case (MatchF I r)
  from MatchF.prems obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then obtain i' where "i < i'" and i': "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  have ix: "i \<le> x" if "memR I (\<tau> \<sigma> i' - \<tau> \<sigma> x)" for x
    using i' less_\<tau>D[of \<sigma> i x] that by (auto 0 3 simp: diff_le_mono2 elim: contrapos_np)
  show ?case
  proof (cases "regex.atms r = {}")
    case True
    with MatchF.prems ix show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some (Suc i') else None"] exI[of _ "Suc i'"])
        (auto split: if_splits simp: pred_mapping_alt regex.pred_set add.commute less_Suc_eq
          intro!: cInf_greatest dest!: spec[of _ i'] less_imp_le[THEN \<tau>_mono, of _ i' \<sigma>])
  next
    case False
    then obtain \<phi> where \<phi>: "\<phi> \<in> regex.atms r" by auto
    define pick where "pick = (\<lambda>\<phi> :: 't Formula.formula. SOME Pj. dom (fst Pj) = S \<and> range_mapping (Suc i') (snd Pj) (fst Pj) \<and>
      Suc i' \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj))"
    define pickP where "pickP = fst o pick" define pickj where "pickj = snd o pick"
    from MatchF have pick: "\<phi> \<in> regex.atms r \<Longrightarrow> dom (pickP \<phi>) = S \<and>
    range_mapping (Suc i') (pickj \<phi>) (pickP \<phi>) \<and> Suc i' \<le> progress \<sigma> (pickP \<phi>) \<phi> (pickj \<phi>)" for \<phi>
      unfolding pick_def o_def future_bounded.simps regex.pred_set pickj_def pickP_def
      by (intro someI_ex[where P = "\<lambda>Pj. dom (fst Pj) = S \<and> range_mapping (Suc i') (snd Pj) (fst Pj) \<and>
       Suc i' \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"]) auto
    from pick have pred_pick: "\<phi> \<in> regex.atms r \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> pickj \<phi>) (pickP \<phi>)" for \<phi>
      by (force elim: pred_mapping_mono)
    let ?P = "Max_mapping (pickP ` regex.atms r)" let ?j = "Max (pickj ` regex.atms r)"
    from pick[OF \<phi>] False \<phi> have "Suc i' \<le> ?j"
      by (intro order_trans[OF pick[THEN conjunct2, THEN conjunct2], OF \<phi>] order_trans[OF progress_le_gen])
        (auto simp: Max_ge_iff dest: range_mapping_relax[of _ _ _ 0, OF _ _ order_refl, simplified])
    moreover
    note i' ix
    moreover
    from MatchF.prems have "Regex.pred_regex Safety.future_bounded r"
      by auto
    ultimately show ?thesis using \<tau>_mono[of _ ?j \<sigma>] less_\<tau>D[of \<sigma> i] pick pred_pick False
      by (intro exI[of _ "?j"]  exI[of _ "?P"])
        (auto 0 3 intro!: cInf_greatest range_mapping_Max_mapping[of _ 0, simplified]
          order_trans[OF le_SucI[OF order_refl] order_trans[OF pick[THEN conjunct2, THEN conjunct2] progress_mono_gen]]
          range_mapping_Max_mapping[OF _ _ ballI[OF range_mapping_relax[of "Suc i'" _ _ i, OF _ _ order_refl]]]
          simp: ac_simps Suc_le_eq trans_le_add2 Max_mapping_coboundedI progress_regex_def
          dest: spec[of _ "i'"] spec[of _ ?j])
  qed
next
  case (TP t)
  show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (TS t)
  show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
qed auto

lemma progress_ge: "Safety.future_bounded \<phi> \<Longrightarrow> \<exists>j. i \<le> progress \<sigma> Map.empty \<phi> j"
  using progress_ge_gen[of \<phi> "{}" i \<sigma>]
  by auto


subsection \<open> Traces with a common prefix \<close>

lemma progress_time_conv:
  assumes "\<forall>i<j. \<tau> \<sigma> i = \<tau> \<sigma>' i"
  shows "progress \<sigma> P \<phi> j = progress \<sigma>' P \<phi> j"
  using assms
proof (induction \<phi> arbitrary: P j)
next
  case (Frz p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  show ?case
    unfolding progress.simps Let_def
  proof (rule arg_cong[where f=Least])
    show "(\<lambda>i. i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < progress \<sigma> P \<phi> j then j else 0))) \<psi> j \<le> i) =
      (\<lambda>i. i \<le> j \<and> progress \<sigma>' (P(?pn \<mapsto> (if i < progress \<sigma>' P \<phi> j then j else 0))) \<psi> j \<le> i)"
      using Frz by (intro ext) (auto simp del: fun_upd_apply)
  qed
next
  case(LetPast p \<phi> \<psi>)
  with LetPast show ?case
    by (auto simp: letpast_progress_def 
        simp del: fun_upd_apply)
next 
  case (Until \<phi>1 I \<phi>2)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with Until show ?case
  proof (cases "bounded I")
    case True
    then show ?thesis
    proof (cases "j")
      case (Suc n)
      with * Until show ?thesis
        using \<tau>_mono[THEN trans_le_add1]
        by (auto 6 0
            intro!: box_equals[OF arg_cong[where f=Inf]
              cInf_restrict_nat[symmetric, where x=n] 
              cInf_restrict_nat[symmetric, where x=n]])
    qed simp
  qed (simp add: bounded_memR)
next
  case (Release \<phi> I \<psi> P j)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with Release show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case mem: True
    show ?thesis
      using mem Release
    proof (cases "bounded I")
      case True
      then show ?thesis
        using mem
      proof (cases "j")
        case (Suc n)
        with * Release show ?thesis
          using \<tau>_mono[THEN trans_le_add1] mem
          by (auto 6 0
              intro!: box_equals[OF arg_cong[where f=Inf]
                cInf_restrict_nat[symmetric, where x=n] 
                cInf_restrict_nat[symmetric, where x=n]])
      qed (simp add: Release)
    qed (auto simp add: bounded_memR)
  next
    case False
    have obs: "progress \<sigma> P \<psi>' j = progress \<sigma>' P \<psi>' j 
    \<Longrightarrow> progress \<sigma> P (Formula.eventually J \<psi>') j = progress \<sigma>' P (Formula.eventually J \<psi>') j"
      for \<psi>':: "'c Formula.formula" and J
      using Release.prems
      by (auto simp: fun_eq_iff progress_eventually 
          intro!: arg_cong[where f="(\<lambda>X. \<Sqinter> X)"] 
          arg_cong[where f=Collect] iff_allI)
        (metis memR_nonzeroD less_\<tau>D  order.strict_trans zero_less_diff)+
    have "progress \<sigma> P Formula.TT j = progress \<sigma>' P Formula.TT j"
      by auto
    moreover have "progress \<sigma> P (formula.Until \<psi> (int_remove_lower_bound I) (formula.And \<psi> \<phi>)) j 
      = progress \<sigma>' P (formula.Until \<psi> (int_remove_lower_bound I) (formula.And \<psi> \<phi>)) j"
      using Release.prems
      by (auto simp: fun_eq_iff intro!: arg_cong[where f="(\<lambda>X. \<Sqinter> X)"] 
          arg_cong[where f=Collect])
        (metis Release.IH less_\<tau>D less_or_eq_imp_le memR_nonzeroD 
          order_less_le_trans zero_less_diff)+
    ultimately show ?thesis 
      using Release False obs
      by (auto simp: release_safe_bounded_def always_safe_bounded_def
          simp del: progress.simps(16)
          intro!: arg_cong2[where f=min] arg_cong[where f="\<lambda>x. x - Suc 0"])
  qed
next
  case (MatchP I r P j)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with MatchP show ?case using \<tau>_mono[THEN trans_le_add1]
    by (cases "bounded I"; cases j)
      ((auto 6 0 simp: progress_le_gen progress_regex_def intro!: box_equals[OF arg_cong[where f=Inf]
            cInf_restrict_nat[symmetric, where x="j-1"] cInf_restrict_nat[symmetric, where x="j-1"]]) [])+
next
  case (MatchF I r)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with MatchF show ?case using \<tau>_mono[THEN trans_le_add1]
    by (cases "bounded I"; cases j)
      ((auto 6 0 simp: progress_le_gen progress_regex_def intro!: box_equals[OF arg_cong[where f=Inf]
            cInf_restrict_nat[symmetric, where x="j-1"] cInf_restrict_nat[symmetric, where x="j-1"]]) [])+
qed (auto simp: progress_regex_def)

lemma progress_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "progress \<sigma> P \<phi> (plen \<pi>) = progress \<sigma>' P \<phi> (plen \<pi>)"
  using assms by (auto intro: progress_time_conv \<tau>_prefix_conv)

lemma sat_prefix_conv_gen:
  fixes \<phi> :: "ty Formula.formula"
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "i < progress \<sigma> P \<phi> (plen \<pi>) \<Longrightarrow> dom V = dom V' \<Longrightarrow> dom P = dom V \<Longrightarrow>
    pred_mapping (\<lambda>x. x \<le> plen \<pi>) P \<Longrightarrow>
    (\<And>p n v i \<phi>. (p, n) \<in> dom V \<Longrightarrow> i < the (P (p, n)) \<Longrightarrow> n = length v \<Longrightarrow>
      the (V (p, n)) v i = the (V' (p, n)) v i) \<Longrightarrow>
    Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat \<sigma>' V' v i \<phi>"
proof (induction \<phi> arbitrary: P V V' v i rule: formula_release_safe_bounded_induct)
  case (Pred e ts)
  let ?en = "(e, length ts)"
  from Pred.prems(1,4) have "i < plen \<pi>"
    by (blast intro!: order.strict_trans2 progress_le_gen)
  show ?case proof (cases "V ?en")
    case None
    then have "V' ?en = None" using \<open>dom V = dom V'\<close> by auto
    with None \<Gamma>_prefix_conv[OF assms(1,2) \<open>i < plen \<pi>\<close>] show ?thesis by simp
  next
    case (Some a)
    obtain a' where "V' ?en = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    then have "i < the (P ?en)"
      using Pred.prems(1-3) by (auto split: option.splits)
    then have "the (V ?en) (map (Formula.eval_trm v) ts) i = the (V' ?en) (map (Formula.eval_trm v) ts) i"
      using Some by (intro Pred.prems(5)) (simp_all add: domI)
    with Some \<open>V' ?en = Some a'\<close> show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>))"
  show ?case 
    unfolding sat.simps 
  proof (rule Let.IH(2))
    from Let.prems show "i < progress \<sigma> (P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) \<psi> (plen \<pi>)"
      by simp
    from Let.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by simp
    from Let.prems show "dom (P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) = dom (?V V \<sigma>)"
      by simp
    from Let.prems show "pred_mapping (\<lambda>x. x \<le> plen \<pi>) (P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>)))"
      by (auto intro!: pred_mapping_map_upd elim!: progress_le_gen)
  next
    fix p' n v i \<phi>'
    assume 1: "(p', n) \<in> dom (?V V \<sigma>)" and 2: "i < the ((P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) (p', n))"
      and 3: "n = length (v :: event_data list)"
    show "the (?V V \<sigma> (p', n)) v i = the (?V V' \<sigma>' (p', n)) v i"
    proof (cases "(p', n) = ?pn")
      case True
      with Let 2 show ?thesis by auto
    next
      case False
      from 1 False have "(p', n) \<in> dom V"
        by auto
      moreover from 2 False have "i < the (P (p', n))"
        by auto
      ultimately have "the (V (p', n)) v i = the (V' (p', n)) v i"
        using 3 by (rule Let.prems(5))
      with False show ?thesis
        by auto
    qed
  qed
next
  case (Frz p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?q = "if i < progress \<sigma> P \<phi> (plen \<pi>) then plen \<pi> else 0"
  let ?P = "P(?pn \<mapsto> ?q)"
  let ?V = "\<lambda>V \<sigma>. V(?pn \<mapsto> (\<lambda>w j. Formula.sat \<sigma> V w i \<phi>))"
  have i_lt_plen: "i < plen \<pi>"
    using Frz.prems(1,4) by (blast intro!: order.strict_trans2 progress_le_gen)
  have i_lt_psi: "i < progress \<sigma> ?P \<psi> (plen \<pi>)"
  proof (rule ccontr)
    assume "\<not> i < progress \<sigma> ?P \<psi> (plen \<pi>)"
    then have "progress \<sigma> ?P \<psi> (plen \<pi>) \<le> i"
      by simp
    then have "progress \<sigma> P (Formula.Frz p \<phi> \<psi>) (plen \<pi>) \<le> i"
      unfolding progress.simps Let_def
      by (intro Least_le) (use i_lt_plen in auto)
    with Frz.prems(1) show False by simp
  qed
  show ?case
    unfolding sat.simps Let_def
  proof (rule Frz.IH(2))
    show "i < progress \<sigma> ?P \<psi> (plen \<pi>)"
      by (rule i_lt_psi)
    from Frz.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by simp
    from Frz.prems show "dom ?P = dom (?V V \<sigma>)"
      by simp
    from Frz.prems show "pred_mapping (\<lambda>x. x \<le> plen \<pi>) ?P"
      by auto
  next
    fix p' n w k \<phi>'
    assume 1: "(p', n) \<in> dom (?V V \<sigma>)"
      and 2: "k < the (?P (p', n))"
      and 3: "n = length (w :: event_data list)"
    show "the (?V V \<sigma> (p', n)) w k = the (?V V' \<sigma>' (p', n)) w k"
    proof (cases "(p', n) = ?pn")
      case True
      then have i_lt_phi: "i < progress \<sigma> P \<phi> (plen \<pi>)"
        using 2 option.sel by fastforce
      have "Formula.sat \<sigma> V w i \<phi> = Formula.sat \<sigma>' V' w i \<phi>"
        by (rule Frz.IH(1)[OF i_lt_phi Frz.prems(2-5)])
      with True show ?thesis by simp
    next
      case False
      from 1 False have "(p', n) \<in> dom V"
        by auto
      moreover from 2 False have "k < the (P (p', n))"
        by auto
      ultimately have "the (V (p', n)) w k = the (V' (p', n)) w k"
        using 3 by (rule Frz.prems(5))
      with False show ?thesis
        by auto
    qed
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. (V(?pn \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>)))"
  show ?case unfolding sat.simps Let_def proof (rule LetPast.IH(2))
    from LetPast.prems show "i < progress \<sigma> (P(?pn \<mapsto> (Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)}))) \<psi> (plen \<pi>)"
      by (simp add: letpast_progress_def Let_def)
    from LetPast.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by simp
    from LetPast.prems show "dom (P(?pn \<mapsto>(Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)}))) = dom (?V V \<sigma>)"
      by simp
    from LetPast.prems show "pred_mapping (\<lambda>x. x \<le> plen \<pi>) (P(?pn \<mapsto>(Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)})))"
      by(auto simp add: pred_mapping_alt intro: letpast_progress_le[unfolded letpast_progress_def])
  next
    fix p' n v i \<phi>'
    assume 1: "(p', n) \<in> dom (?V V \<sigma>)" and 2: "i < the ((P(?pn \<mapsto>(Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)}))) (p', n))"
      and 3: "n = length (v :: event_data list)"
    show "the (?V V \<sigma> (p', n)) v i = the (?V V' \<sigma>' (p', n)) v i"
    proof (cases "(p', n) = ?pn")
      case True
      with 2 have "i < letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>)"
        unfolding letpast_progress_def by simp
      then have i_less: "i < progress \<sigma> (P(?pn \<mapsto>letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>))) \<phi> (plen \<pi>)"
        using letpast_progress_fixpoint[OF LetPast(6)] by metis
      have P': "pred_mapping (\<lambda>x. x \<le> plen \<pi>) (P(?pn \<mapsto> letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>)))"
        using LetPast.prems(4) by (auto simp: letpast_progress_le)

      have "letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j =
            letpast_sat (\<lambda>X u k. Formula.sat \<sigma>' (V'(?pn \<mapsto> X)) u k \<phi>) w j"
        if "j \<le> i" for w j
        using that
      proof (induct "\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>" w j rule: letpast_sat.induct)
        case (1 w j)
        then have j_less: "j < progress \<sigma> (P(?pn \<mapsto>letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>))) \<phi> (plen \<pi>)"
          using i_less by simp
        let ?X = "\<lambda>w j'. j' < j \<and> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j'"
        let ?X' = "\<lambda>w j'. j' < j \<and> letpast_sat (\<lambda>X u k. Formula.sat \<sigma>' (V'(?pn \<mapsto> X)) u k \<phi>) w j'"
        show ?case
        proof (subst (1 2) letpast_sat.simps, rule LetPast.IH(1)[OF j_less _ _ P'])
          show "dom (V(?pn \<mapsto> ?X)) = dom (V'(?pn \<mapsto> ?X'))"
            using LetPast.prems(2) by simp
          show "dom (P(?pn \<mapsto> letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>))) = dom (V(?pn \<mapsto> ?X))"
            using LetPast.prems(3) by simp
        next
          fix p'' n' v' i' \<phi>'
          assume dom: "(p'', n') \<in> dom (V(?pn \<mapsto> ?X))"
            and lt: "i' < the ((P(?pn \<mapsto> letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>))) (p'', n'))"
            and len: "n' = length (v' :: event_data list)"
          show "the ((V(?pn \<mapsto> ?X)) (p'', n')) v' i' = the ((V'(?pn \<mapsto> ?X')) (p'', n')) v' i'"
          proof (cases "(p'', n') = ?pn")
            case True
            have "letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) v' i' =
              letpast_sat (\<lambda>X u k. Formula.sat \<sigma>' (V'(?pn \<mapsto> X)) u k \<phi>) v' i'" if "i' < j"
              using that "1"(2) by (intro "1"(1)) simp_all
            with True show ?thesis
              by auto
          next
            case False
            from dom False have "(p'', n') \<in> dom V"
              by auto
            moreover from lt False have "i' < the (P (p'', n'))"
              by auto
            ultimately have "the (V (p'', n')) v' i' = the (V' (p'', n')) v' i'"
              using len by (rule LetPast.prems(5))
            with False show ?thesis
              by auto
          qed
        qed
      qed
      with True show ?thesis by simp
    next
      case False
      with 1 2 3 LetPast.prems(5) show ?thesis by fastforce
    qed
  qed
next
  case (Eq t1 t2)
  show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by auto
next
  case (Ands l)
  from Ands.prems have "\<forall>\<phi>\<in>set l. i < progress \<sigma> P \<phi> (plen \<pi>)"
    by (cases l) simp_all
  with Ands show ?case 
    unfolding Formula.sat.simps(11) by (auto 0 4)
next
  case (Exists \<phi>)
  then show ?case by simp
next
  case (Prev I \<phi>)
  with \<tau>_prefix_conv[OF assms(1,2)] show ?case
    by (cases i) (auto split: if_splits)
next
  case (Next I \<phi>)
  then have "Suc i < plen \<pi>"
    by (auto intro: order.strict_trans2[OF _ progress_le_gen[of _ P \<sigma> \<phi>]])
  with Next.prems \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro conj_cong Next) auto
next
  case (Since \<phi>1 I \<phi>2)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le_gen])
  with Since.prems \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro conj_cong ex_cong ball_cong Since.IH[where P=P])
      (auto split: if_splits, metis diff_self_eq_0 less_antisym order.strict_trans1)
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems have [simp]: "bounded I"
    by (cases "bounded I") (auto simp: bounded_memR Inf_UNIV_nat)
  from Until.prems obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    "j \<le> progress \<sigma> P \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma> P \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 1: "k < progress \<sigma> P \<phi>1 (plen \<pi>)" and 2: "k < progress \<sigma> P \<phi>2 (plen \<pi>)"
    if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    using that
    by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
  have 3: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    using 1[OF that] progress_le_gen[OF Until.prems(4)] by (rule order.strict_trans2)

  from Until.prems have "i < progress \<sigma>' P (Formula.Until \<phi>1 I \<phi>2) (plen \<pi>)"
    unfolding progress_prefix_conv[OF assms(1,2)] by simp
  then obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
    "j \<le> progress \<sigma>' P \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma>' P \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 11: "k < progress \<sigma> P \<phi>1 (plen \<pi>)" and 21: "k < progress \<sigma> P \<phi>2 (plen \<pi>)"
    if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    unfolding progress_prefix_conv[OF assms(1,2)]
    using that
    by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
  have 31: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    using 11[OF that] progress_le_gen[OF Until.prems(4)] by (rule order.strict_trans2)

  show ?case unfolding sat.simps
  proof ((intro ex_cong iffI; elim conjE), goal_cases LR RL)
    case (LR j)
    have memR_le: "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" if "k \<le> j" for k
      using LR(3) diff_le_mono[OF \<tau>_mono[OF that]] by (rule memR_antimono)
    have \<tau>_eq: "\<tau> \<sigma> k = \<tau> \<sigma>' k" if "k \<le> j" for k
      using memR_le[OF that] by (rule \<tau>_prefix_conv[OF assms(1,2) 3])
    have sat1: "Formula.sat \<sigma> V v k \<phi>1 \<longleftrightarrow> Formula.sat \<sigma>' V' v k \<phi>1" if "k \<le> j" for k
      using memR_le[OF that] by (rule Until.IH(1)[OF 1 Until.prems(2-5)])
    have sat2: "Formula.sat \<sigma> V v j \<phi>2 \<longleftrightarrow> Formula.sat \<sigma>' V' v j \<phi>2"
      using LR(3) by (rule Until.IH(2)[OF 2 Until.prems(2-5)])
    show ?case
      using LR(1-5) by (simp add: \<tau>_eq sat1 sat2)
  next
    case (RL j)
    have memR_le: "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" if "k \<le> j" for k
      using RL(3) diff_le_mono[OF \<tau>_mono[OF that]] by (rule memR_antimono)
    have \<tau>_eq: "\<tau> \<sigma> k = \<tau> \<sigma>' k" if "k \<le> j" for k
      using memR_le[OF that] by (rule \<tau>_prefix_conv[OF assms(1,2) 31])
    have sat1: "Formula.sat \<sigma> V v k \<phi>1 \<longleftrightarrow> Formula.sat \<sigma>' V' v k \<phi>1" if "k \<le> j" for k
      using memR_le[OF that] by (rule Until.IH(1)[OF 11 Until.prems(2-5)])
    have sat2: "Formula.sat \<sigma> V v j \<phi>2 \<longleftrightarrow> Formula.sat \<sigma>' V' v j \<phi>2"
      using RL(3) by (rule Until.IH(2)[OF 21 Until.prems(2-5)])
    show ?case
      using RL(1-5) by (simp add: \<tau>_eq sat1 sat2)
  qed
next
  case (Trigger \<phi> I \<psi>)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le_gen])
  have \<tau>_eq: "\<tau> \<sigma> k = \<tau> \<sigma>' k" if "k \<le> i" for k
    using that \<open>i < plen \<pi>\<close> by (simp add: \<tau>_prefix_conv[OF assms(1,2)])
  from Trigger.prems(1)
  have i_less: "i < progress \<sigma> P \<phi> (plen \<pi>)" "i < progress \<sigma> P \<psi> (plen \<pi>)"
    by simp_all
  have sat_\<phi>: "Formula.sat \<sigma> V v k \<phi> \<longleftrightarrow> Formula.sat \<sigma>' V' v k \<phi>" if "k \<le> i" for k
    using le_less_trans[OF that i_less(1)] by (rule Trigger.IH(1)[OF _ Trigger.prems(2-5)])
  have sat_\<psi>: "Formula.sat \<sigma> V v k \<psi> \<longleftrightarrow> Formula.sat \<sigma>' V' v k \<psi>" if "k \<le> i" for k
    using le_less_trans[OF that i_less(2)] by (rule Trigger.IH(2)[OF _ Trigger.prems(2-5)])
  show ?case
    unfolding sat.simps by (simp add: \<tau>_eq sat_\<phi> sat_\<psi>)
next
  case (Release \<phi> I \<psi>)

 have \<tau>_prefix_diff_conv: "\<And>k i. k < plen \<pi> \<Longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
  proof -
    fix k i
    assume assm: "k < plen \<pi>"
    {
      assume "i \<le> k"
      then have "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
        using assm \<tau>_prefix_conv[OF assms(1,2)]
        by auto
    }
    moreover {
      assume "i > k"
      then have
        "\<tau> \<sigma> k - \<tau> \<sigma> i = 0"
        "\<tau> \<sigma>' k - \<tau> \<sigma>' i = 0"
        by auto
      then have "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
        by auto
    }
    ultimately show "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" 
      using not_le_imp_less by blast
  qed

  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    from Release.prems True have [simp]: "bounded I"
      by (cases "bounded I") (auto simp: bounded_memR Inf_UNIV_nat)
    from Release.prems True obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
      "j \<le> progress \<sigma> P \<phi> (plen \<pi>)" "j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
      by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 1: "k < progress \<sigma> P \<phi> (plen \<pi>)" and 2: "k < progress \<sigma> P \<psi> (plen \<pi>)"
      if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using that
      by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
    have 3: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using 1[OF that] progress_le_gen[OF Release.prems(4)] by (rule order.strict_trans2)

    from Release.prems have "i < progress \<sigma>' P (Formula.Release \<phi> I \<psi>) (plen \<pi>)"
      unfolding progress_prefix_conv[OF assms(1,2)] by simp
    with True obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
      "j \<le> progress \<sigma>' P \<phi> (plen \<pi>)" "j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
      by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 11: "k < progress \<sigma> P \<phi> (plen \<pi>)" and 21: "k < progress \<sigma> P \<psi> (plen \<pi>)"
      if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      unfolding progress_prefix_conv[OF assms(1,2)]
      using that
      by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
    have 31: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using 11[OF that] progress_le_gen[OF Release.prems(4)] by (rule order.strict_trans2)

    have \<tau>_eq: "\<tau> \<sigma> k = \<tau> \<sigma>' k" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using that by (rule \<tau>_prefix_conv[OF assms(1,2) 3])
    have \<tau>_eq': "\<tau> \<sigma> k = \<tau> \<sigma>' k" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using that by (rule \<tau>_prefix_conv[OF assms(1,2) 31])
    have i_in: "memR I (\<tau> \<sigma> i - \<tau> \<sigma> i)" "memR I (\<tau> \<sigma>' i - \<tau> \<sigma>' i)"
      using True by auto
    have memR_iff: "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<longleftrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    proof
      assume a: "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then show "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
        unfolding \<tau>_eq[OF a] \<tau>_eq[OF i_in(1)] .
    next
      assume a: "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
      then show "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        unfolding \<tau>_eq'[OF a, symmetric] \<tau>_eq'[OF i_in(2), symmetric] .
    qed
    have memR_le: "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" if "memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "k \<le> j" for j k
      using that(1) diff_le_mono[OF \<tau>_mono[OF that(2)]] by (rule memR_antimono)
    have sat1: "Formula.sat \<sigma> V v k \<phi> \<longleftrightarrow> Formula.sat \<sigma>' V' v k \<phi>"
      if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using that by (rule Release.IH(1)[OF True 1 Release.prems(2-5)])
    have sat2: "Formula.sat \<sigma> V v k \<psi> \<longleftrightarrow> Formula.sat \<sigma>' V' v k \<psi>"
      if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using that by (rule Release.IH(2)[OF True 2 Release.prems(2-5)])
    have "(mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>)) \<longleftrightarrow>
      (mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<longrightarrow> Formula.sat \<sigma>' V' v j \<psi> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma>' V' v k \<phi>))"
      if "i \<le> j" for j
    proof (cases "memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
      case True
      have "Formula.sat \<sigma> V v k \<phi> \<longleftrightarrow> Formula.sat \<sigma>' V' v k \<phi>" if "k < j" for k
        using sat1[OF memR_le[OF True]] that by simp
      then show ?thesis
        using \<tau>_eq[OF i_in(1)] \<tau>_eq[OF True] sat2[OF True]
        by (auto simp: Bex_def)
    next
      case False
      then show ?thesis
        using memR_iff[of j] by auto
    qed
    then show ?thesis
      unfolding sat.simps by (auto 0 4)
  next    case False
    then have i_le: "i < progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) (plen \<pi>)"
      using Release(4)
      by auto

    have rewrite_conds: "bounded I" "\<not> mem I 0"
      using False
      by auto
    
    have sat_safe_bounded_eq: "\<And>v. Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I \<psi>) 
      = Formula.sat \<sigma>' V' v i (release_safe_bounded \<phi> I \<psi>)"
      using Release(3)[OF False i_le] Release(4-)
      by auto

    show ?thesis
    proof (cases "\<exists>j\<in>{i..<plen \<pi>}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
      case True
      then have "\<exists>j\<in>{i..<plen \<pi>}. mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using \<tau>_prefix_diff_conv
        by auto
      then have
        "Formula.sat \<sigma> V v i (Formula.eventually I Formula.TT)"
        "Formula.sat \<sigma>' V' v i (Formula.eventually I Formula.TT)"
        using True
        by auto
      then have r:
        "Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I \<psi>)"
        "Formula.sat \<sigma>' V' v i (formula.Release \<phi> I \<psi>) = Formula.sat \<sigma>' V' v i (release_safe_bounded \<phi> I \<psi>)"
        using sat_release_rewrite[OF rewrite_conds, of _ _ v i \<phi> \<psi>]
        by auto
      
      show ?thesis
        using sat_safe_bounded_eq[of v]
        unfolding r
        by blast
    next
      case int_props: False
      then have int_props:
        "\<forall>j\<in>{i..<plen \<pi>}. \<not>mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        "\<forall>j\<in>{i..<plen \<pi>}. \<not>mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using \<tau>_prefix_diff_conv
        by auto
      define event_TT where "event_TT = ((Formula.eventually I Formula.TT):: ty Formula.formula)"
      have "i < progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) (plen \<pi>)"
        using False Release(4)
        by auto
      then have i_le: "i < progress \<sigma> P event_TT (plen \<pi>)"
        unfolding release_safe_bounded_def event_TT_def
        by auto
      moreover have "progress \<sigma> P event_TT (plen \<pi>) = progress \<sigma>' P event_TT (plen \<pi>)"
        by (meson assms(1) assms(2) progress_prefix_conv)
      ultimately have i_le': "i < progress \<sigma>' P event_TT (plen \<pi>)"
        by auto

      have "\<And>j. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> j < plen \<pi>"
      proof -
        fix j
        assume mem: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        {
          assume assm: "j \<ge> plen \<pi>"
          have "{i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} 
            = {i. \<forall>k. k < plen \<pi> \<and> k \<le> plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
            by auto
          have "\<And>k. k < plen \<pi> \<Longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          proof -
            fix k
            assume "k < plen \<pi>"
            then have "k < j"
              using assm
              by auto
            then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j"
              by auto
            then show "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
              using mem
              by auto
          qed
          then have "i \<in> {i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
            by auto
          then have "i \<ge> progress \<sigma> P event_TT (plen \<pi>)"
            unfolding progress_eventually progress_TT event_TT_def
            by (auto simp add: cInf_lower)
          then have "False"
            using i_le leD 
            by blast
        }
        then show "j < plen \<pi>"
          using not_le
          by blast
      qed
      then have "\<forall>j\<ge>plen \<pi>. \<not>mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        using leD
        by blast
      then have not_mem_\<sigma>: "\<forall>j\<ge>i. \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        using int_props
        by auto

      have "\<And>j. mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<Longrightarrow> j < plen \<pi>"
      proof -
        fix j
        assume mem: "mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        {
          assume assm: "j \<ge> plen \<pi>"
          have "{i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)} 
            = {i. \<forall>k. k < plen \<pi> \<and> k \<le> plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
            by auto
          have "\<And>k. k < plen \<pi> \<Longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
          proof -
            fix k
            assume "k < plen \<pi>"
            then have "k < j"
              using assm
              by auto
            then have "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' j"
              by auto
            then show "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
              using mem
              by auto
          qed
          then have "i \<in> {i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
            by auto
          then have "i \<ge> progress \<sigma>' P event_TT (plen \<pi>)"
            unfolding progress_eventually progress_TT event_TT_def
            by (auto simp add: cInf_lower)
          then have "False"
            using i_le' leD
            by blast
        }
        then show "j < plen \<pi>"
          using not_le
          by blast
      qed
      then have "\<forall>j\<ge>plen \<pi>. \<not>mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using leD
        by blast
      then have not_mem_\<sigma>': "\<forall>j\<ge>i. \<not> mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using int_props
        by auto

      show ?thesis
        using not_mem_\<sigma> not_mem_\<sigma>'
        by auto
    qed
  qed
next
  case (MatchP I r)
  then have "i < plen \<pi>"
    by (force simp: pred_mapping_alt elim!: order.strict_trans2[OF _ progress_le_gen])
  with MatchP.prems \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro ex_cong conj_cong match_cong_strong MatchP) 
      (auto simp: progress_regex_def split: if_splits)
next
  case (MatchF I r)
  from MatchF.prems have [simp]: "bounded I"
    by (cases "bounded I") 
      (auto simp: bounded_memR Inf_UNIV_nat)
  show ?case
  proof (cases "regex.atms r = {}")
    case True
    from MatchF.prems(1) obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "j \<le> plen \<pi>"
      by atomize_elim 
        (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 1: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      by (meson \<tau>_mono diff_le_mono memR_antimono not_le_imp_less that)
    from MatchF.prems have "i < progress \<sigma>' P (Formula.MatchF I r) (plen \<pi>)"
      unfolding progress_prefix_conv[OF assms(1,2)] by blast
    then obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "j \<le> plen \<pi>"
      by atomize_elim 
        (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 2: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      by (meson \<tau>_mono diff_le_mono memR_antimono not_le_imp_less that)
    from MatchF.prems(1,4) True show ?thesis
      unfolding sat.simps conj_commute[of "memL _ _"]
    proof (intro ex_cong conj_cong match_cong_strong, goal_cases memL memR sat)
      case (memL j)
      then show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 1, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (memR j)
      then show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    qed auto
  next
    case False
    from MatchF.prems(1) False obtain j 
      where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "(\<forall>x\<in>regex.atms r. j \<le> progress \<sigma> P x (plen \<pi>))"
      by atomize_elim (auto 0 6 simp add: less_eq_Suc_le not_le progress_regex_def
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 1: "\<phi> \<in> regex.atms r \<Longrightarrow> k < progress \<sigma> P \<phi> (plen \<pi>)" 
      if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k \<phi>
      using that
      by (auto 0 3 elim!: contrapos_np[of _ "_ < _"] simp: diff_le_mono)
    then have 2: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "regex.atms r \<noteq> {}" for k
      using that
      by (fastforce intro: order.strict_trans2[OF _ progress_le_gen[OF MatchF(5), of \<sigma>], of k])

    from MatchF.prems have "i < progress \<sigma>' P (Formula.MatchF I r) (plen \<pi>)"
      unfolding progress_prefix_conv[OF assms(1,2)] by blast
    with False obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "(\<forall>x\<in>regex.atms r. j \<le> progress \<sigma>' P x (plen \<pi>))"
      by atomize_elim (auto 0 6 simp add: less_eq_Suc_le not_le progress_regex_def
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 11:  "\<phi> \<in> regex.atms r \<Longrightarrow> k < progress \<sigma> P \<phi> (plen \<pi>)" 
      if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k \<phi>
      using that unfolding progress_prefix_conv[OF assms(1,2)]
      by (auto 0 3 elim!: contrapos_np[of _ "_ < _"] simp: diff_le_mono) 
    have 21: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using 11[OF that(1)] False 
      by (fastforce intro: order.strict_trans2[OF _ progress_le_gen[OF MatchF(5), of \<sigma>], of k])
    show ?thesis unfolding sat.simps conj_commute[of "memL _ _"]
    proof ((intro ex_cong conj_cong match_cong_strong MatchF(1)[OF _ _ MatchF(3-6)]; assumption?), 
        goal_cases memR memL progress)
      case (memR j)
      with False show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (memL j)
      with False show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (progress j k z)
      with False show ?case
        by (elim 1[rotated])
          (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; 
            auto simp: diff_le_mono memR_antimono elim!: contrapos_np[of _ False])
    qed
  qed
next
  case (TS t)
  with \<tau>_prefix_conv[OF assms] show ?case
    by simp
qed (auto)

lemma sat_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "i < progress \<sigma> Map.empty \<phi> (plen \<pi>) \<Longrightarrow>
    Formula.sat \<sigma> Map.empty v i \<phi> \<longleftrightarrow> Formula.sat \<sigma>' Map.empty v i \<phi>"
  by (erule sat_prefix_conv_gen[OF assms]) auto

lemma progress_remove_neg[simp]: "progress \<sigma> P (remove_neg \<phi>) j = progress \<sigma> P \<phi> j"
  by (cases \<phi>) simp_all


subsection \<open> Prefix progress and specification \<close>

text \<open>The progress on a prefix does not depend on the trace that extends it; with it, every
  future-bounded formula meets the abstract specification of a sliceable monitor.\<close>

definition pprogress :: "'t Formula.formula \<Rightarrow> Formula.prefix \<Rightarrow> nat" where
  "pprogress \<phi> \<pi> = (THE n. \<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> progress \<sigma> Map.empty \<phi> (plen \<pi>) = n)"

lemma pprogress_eq: "prefix_of \<pi> \<sigma> \<Longrightarrow> pprogress \<phi> \<pi> = progress \<sigma> Map.empty \<phi> (plen \<pi>)"
  unfolding pprogress_def using progress_prefix_conv
  by blast

sublocale future_bounded_mfodl \<subseteq> sliceable_timed_progress "Formula.nfv \<phi>" "Formula.fv_list \<phi>" traces "relevant_events \<phi>"
  "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" "pprogress \<phi>"
proof (unfold_locales, goal_cases)
  case (1 \<pi>' \<pi>)
  moreover obtain \<sigma> where "prefix_of \<pi>' \<sigma>"
    using ex_prefix_of ..
  moreover have "prefix_of \<pi> \<sigma>"
    using prefix_of_antimono[OF \<open>\<pi> \<le> \<pi>'\<close> \<open>prefix_of \<pi>' \<sigma>\<close>] .
  ultimately show ?case
    by (simp add: pprogress_eq plen_mono progress_mono)
next
  case (2 \<sigma> x)
  obtain j where "x \<le> progress \<sigma> Map.empty \<phi> j"
    using future_bounded progress_ge by blast
  then have "x \<le> pprogress \<phi> (take_prefix j \<sigma>)"
    by (simp add: pprogress_eq[of _ \<sigma>])
  then show ?case by force
next
  case (3 \<sigma> \<pi> \<sigma>' i v)
  then have "i < progress \<sigma> Map.empty \<phi> (plen \<pi>)"
    by (simp add: pprogress_eq)
  with 3 show ?case
    using sat_prefix_conv by blast
next
  case (4 \<pi> \<pi>')
  then have "plen \<pi> = plen \<pi>'"
    unfolding length_pts_eq_plen[symmetric] by auto
  moreover obtain \<sigma> \<sigma>' where "prefix_of \<pi> \<sigma>" "prefix_of \<pi>' \<sigma>'"
    using ex_prefix_of by blast+
  moreover have "\<forall>i < plen \<pi>. \<tau> \<sigma> i = \<tau> \<sigma>' i"
    using 4 calculation nth_pts_eq_\<tau>[OF calculation(3)] nth_pts_eq_\<tau>[OF calculation(2)]
    by auto
  ultimately show ?case
    by (simp add: pprogress_eq progress_time_conv)
qed

lemma (in future_bounded_mfodl) Mt_pnil: "Mt pnil = {}"
  by (simp add: Mt_def M_def pprogress_eq)

lemma (in future_bounded_mfodl) fst_M_less_plen: 
  assumes "(i, v) \<in> M \<pi>" 
  shows "i < plen \<pi>"
proof -
  obtain \<sigma> where "prefix_of \<pi> \<sigma>"
    using ex_prefix_of by blast
  then have "pprogress \<phi> \<pi> \<le> plen \<pi>"
    by (simp add: pprogress_eq progress_le_gen)
  with assms show ?thesis
    unfolding M_def by simp
qed

lemma (in future_bounded_mfodl) mono_monitor': "\<pi>' \<in> formula_slicer.prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> Mt \<pi> \<subseteq> Mt \<pi>'"
  unfolding Mt_def using mono_monitor[of \<pi>' \<pi>] fst_M_less_plen[of _ _ \<pi>]
  by (auto simp add: nth_pts_prefix_cong dest!: subsetD)

(*<*)
end
(*>*)
