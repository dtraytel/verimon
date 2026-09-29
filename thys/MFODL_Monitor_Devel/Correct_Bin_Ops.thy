(*<*)
theory Correct_Bin_Ops
  imports
    Monitor 
    Progress
begin
(*>*)


section \<open> Correctness \<close>


subsection \<open> Monitor's binary buffers \<close>

definition wf_mbuf2 where
  "wf_mbuf2 i ja jb P Q buf \<longleftrightarrow> i \<le> ja \<and> i \<le> jb \<and> (case buf of (xs, ys) \<Rightarrow>
    list_all2 P [i..<ja] xs \<and> list_all2 Q [i..<jb] ys)"

lemma wf_mbuf2_add:
  assumes "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 P [ja..<ja'] xs"
    and "list_all2 Q [jb..<jb'] ys"
    and "ja \<le> ja'" "jb \<le> jb'"
  shows "wf_mbuf2 i ja' jb' P Q (mbuf2_add xs ys buf)"
  using assms unfolding wf_mbuf2_def
  by (auto 0 3 simp: list_all2_append2 upt_append dest: list_all2_lengthD
      intro: exI[where x="[i..<ja]"] exI[where x="[ja..<ja']"]
      exI[where x="[i..<jb]"] exI[where x="[jb..<jb']"] split: prod.splits)

lemma mbuf2_take_eqD:
  assumes "mbuf2_take f buf = (xs, buf')"
    and "wf_mbuf2 i ja jb P Q buf"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 (\<lambda>i z. \<exists>x y. P i x \<and> Q i y \<and> z = f x y) [i..<min ja jb] xs"
  using assms unfolding wf_mbuf2_def
  by (induction f buf arbitrary: i xs buf' rule: mbuf2_take.induct)
    (fastforce simp add: list_all2_Cons2 upt_eq_Cons_conv min_absorb1 min_absorb2 split: prod.splits)+

definition wf_mbuf2' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
  ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> event_data mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j))
    (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)
    (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r)
    (\<lambda>i (r). sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> r) buf"

lemma wf_mbuf2'_0: "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> wf_mbuf2' \<sigma> P V 0 n R \<phi> \<psi> ([], [])"
  unfolding wf_mbuf2'_def wf_mbuf2_def by simp

lemma mbuf2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and rm: "rel_mapping (\<le>) P P'"
    and xs: "list_all2 (\<lambda>i r. sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i r. sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "list_all2 (\<lambda>i Z. \<exists>X Y.
      sat_table \<sigma> V n R (Formula.fv_list \<phi>) i \<phi> X \<and>
      sat_table \<sigma> V n R (Formula.fv_list \<psi>) i \<psi> Y \<and>
      Z = f X Y)
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')] zs"
  using pre rm unfolding wf_mbuf2'_def
  by (force intro!: mbuf2_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm])+


subsection \<open> Binary operators' qtable \<close>

lemma qtable_bin_join:
  assumes "qtable A P1 Q1 X" "qtable B P2 Q2 Y" "distinct A" "distinct B"
    "\<not> b \<Longrightarrow> set B \<subseteq> set A" "C = cols_union A B"
    "\<And>x. wf_tuple C x \<Longrightarrow> P x \<Longrightarrow> P1 (restrict A C x) \<and> P2 (restrict B C x)"
    "\<And>x. b \<Longrightarrow> wf_tuple C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> Q2 (restrict B C x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> \<not> Q2 (restrict B C x)"
  shows "qtable C P Q (bin_join A X b B Y)"
  using qtable_join[OF assms] bin_join_table[OF assms(3,4) qtableD(1)[OF assms(1)] qtableD(1)[OF assms(2)]]
  by simp

text \<open>The join of two tables restricted to a slice, in the slice.\<close>

lemma qtable_bin_join_mem_restr:
  assumes "qtable A (mem_restr R A) Q1 X" "qtable B (mem_restr R B) Q2 Y" "distinct A" "distinct B"
    "\<not> b \<Longrightarrow> set B \<subseteq> set A" "C = cols_union A B"
    "\<And>x. b \<Longrightarrow> wf_tuple C x \<Longrightarrow> mem_restr R C x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> Q2 (restrict B C x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple C x \<Longrightarrow> mem_restr R C x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A C x) \<and> \<not> Q2 (restrict B C x)"
  shows "qtable C (mem_restr R C) Q (bin_join A X b B Y)"
  using assms(6) by (intro qtable_bin_join[OF assms(1-6)] assms(7,8))
    (auto intro!: restrict_mem_restr simp: assms(3,4))

lemma qtable_reorder_table:
  assumes "qtable ds P Q X" "distinct cs" "distinct ds" "set cs = set ds"
    "\<And>v. wf_tuple cs v \<Longrightarrow> P' v \<Longrightarrow> P (restrict ds cs v)"
    "\<And>v. wf_tuple cs v \<Longrightarrow> P' v \<Longrightarrow> Q' v \<longleftrightarrow> Q (restrict ds cs v)"
  shows "qtable cs P' Q' (reorder cs ds X)"
proof -
  have q: "qtable cs P' Q' (restrict cs ds ` X)"
    by (rule qtable_reorder[OF assms(1,3,2,4) assms(5,6)])
  show ?thesis
  proof (cases "cs = ds")
    case True
    have "restrict ds ds x = x" if "x \<in> X" for x
      using restrict_idle[OF assms(3) qtableD(1)[OF assms(1), THEN tableD, OF that]] .
    then have "restrict cs ds ` X = X"
      using True by (auto simp: image_iff)
    with q True show ?thesis
      by (simp add: reorder_def)
  next
    case False
    with q show ?thesis
      by (simp add: reorder_def)
  qed
qed
lemma qtable_reorder_mem_restr:
  assumes "qtable ds (mem_restr R ds) Q X" "distinct cs" "distinct ds" "set cs = set ds"
    "\<And>v. wf_tuple cs v \<Longrightarrow> mem_restr R cs v \<Longrightarrow> Q' v \<longleftrightarrow> Q (restrict ds cs v)"
  shows "qtable cs (mem_restr R cs) Q' (reorder cs ds X)"
  using assms by (intro qtable_reorder_table[OF assms(1-4)] restrict_mem_restr) auto

lemma qtable_mmulti_join:
  assumes pos: "list_all3 (\<lambda>A Qi X. qtable A (mem_restr R A) Qi X \<and> distinct A) A_pos Q_pos L_pos"
    and neg: "list_all3 (\<lambda>A Qi X. qtable A (mem_restr R A) Qi X \<and> distinct A) A_neg Q_neg L_neg"
    and C: "distinct C" "set C = (\<Union>A\<in>set A_pos. set A)" and L_eq: "L = L_pos @ L_neg"
    and "A_pos \<noteq> []" and fv_subset: "(\<Union>A\<in>set A_neg. set A) \<subseteq> (\<Union>A\<in>set A_pos. set A)"
    and Qs: "\<And>x. wf_tuple C x \<Longrightarrow> mem_restr R C x \<Longrightarrow> Q x \<longleftrightarrow>
      list_all2 (\<lambda>A Qi. Qi (restrict A C x)) A_pos Q_pos \<and>
      list_all2 (\<lambda>A Qi. \<not> Qi (restrict A C x)) A_neg Q_neg"
  shows "qtable C (mem_restr R C) Q (mmulti_join C A_pos A_neg L)"
proof (rule qtableI)
  from pos have 1: "list_all2 (\<lambda>A X. distinct A \<and> table A X) A_pos L_pos"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  moreover from neg have "list_all2 (\<lambda>A X. distinct A \<and> table A X) A_neg L_neg"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  ultimately have L: "list_all2 (\<lambda>A X. distinct A \<and> table A X) (A_pos @ A_neg) (L_pos @ L_neg)"
    by (rule list_all2_appendI)
  note in_join_iff = mmulti_join_correct[OF \<open>A_pos \<noteq> []\<close> L fv_subset C]
  from 1 have take_eq: "take (length A_pos) (L_pos @ L_neg) = L_pos"
    by (auto dest!: list_all2_lengthD)
  from 1 have drop_eq: "drop (length A_pos) (L_pos @ L_neg) = L_neg"
    by (auto dest!: list_all2_lengthD)
  have len: "length Q_pos = length A_pos" "length L_pos = length A_pos"
    "length Q_neg = length A_neg" "length L_neg = length A_neg"
    using pos neg by (auto simp: list_all3_conv_all_nth)
  have qpos: "restrict (A_pos ! i) C x \<in> L_pos ! i \<longleftrightarrow> (Q_pos ! i) (restrict (A_pos ! i) C x)"
    if "i < length A_pos" "mem_restr R C x" for i x
  proof -
    have q: "qtable (A_pos ! i) (mem_restr R (A_pos ! i)) (Q_pos ! i) (L_pos ! i)" "distinct (A_pos ! i)"
      using pos that(1) by (auto simp: list_all3_conv_all_nth)
    have "set (A_pos ! i) \<subseteq> set C"
      using that(1) C(2) nth_mem[OF that(1)] by blast
    then have "mem_restr R (A_pos ! i) (restrict (A_pos ! i) C x)"
      using restrict_mem_restr[OF that(2) C(1) q(2)] by simp
    with q(1) show ?thesis
      by (simp add: qtable_iff)
  qed
  have qneg: "restrict (A_neg ! i) C x \<in> L_neg ! i \<longleftrightarrow> (Q_neg ! i) (restrict (A_neg ! i) C x)"
    if "i < length A_neg" "mem_restr R C x" for i x
  proof -
    have q: "qtable (A_neg ! i) (mem_restr R (A_neg ! i)) (Q_neg ! i) (L_neg ! i)" "distinct (A_neg ! i)"
      using neg that(1) by (auto simp: list_all3_conv_all_nth)
    have "set (A_neg ! i) \<subseteq> set C"
      using that(1) C(2) fv_subset nth_mem[OF that(1)] by blast
    then have "mem_restr R (A_neg ! i) (restrict (A_neg ! i) C x)"
      using restrict_mem_restr[OF that(2) C(1) q(2)] by simp
    with q(1) show ?thesis
      by (simp add: qtable_iff)
  qed
  note mmulti_join.simps[simp del]
  show "table C (mmulti_join C A_pos A_neg L)"
    unfolding L_eq table_def by (simp add: in_join_iff)
  show "Q x" if "x \<in> mmulti_join C A_pos A_neg L" "wf_tuple C x" "mem_restr R C x" for x
    using that(2,3)
  proof (rule Qs[THEN iffD2, OF _ _ conjI])
    have pos': "list_all2 (\<lambda>A. (\<in>) (restrict A C x)) A_pos L_pos"
      and neg': "list_all2 (\<lambda>A. (\<notin>) (restrict A C x)) A_neg L_neg"
      using that(1) unfolding L_eq in_join_iff take_eq drop_eq by simp_all
    show "list_all2 (\<lambda>A Qi. Qi (restrict A C x)) A_pos Q_pos"
      using pos' qpos[OF _ that(3)] len by (auto simp: list_all2_conv_all_nth)
    show "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A C x)) A_neg Q_neg"
      using neg' qneg[OF _ that(3)] len by (auto simp: list_all2_conv_all_nth)
  qed
  show "x \<in> mmulti_join C A_pos A_neg L" if "wf_tuple C x" "mem_restr R C x" "Q x" for x
    unfolding L_eq in_join_iff take_eq drop_eq
  proof (intro conjI)
    from that have pos': "list_all2 (\<lambda>A Qi. Qi (restrict A C x)) A_pos Q_pos"
      and neg': "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A C x)) A_neg Q_neg"
      using Qs[THEN iffD1] by auto
    show "wf_tuple C x"
      by (rule that(1))
    show "list_all2 (\<lambda>A. (\<in>) (restrict A C x)) A_pos L_pos"
      using pos' qpos[OF _ that(2)] len by (auto simp: list_all2_conv_all_nth)
    show "list_all2 (\<lambda>A. (\<notin>) (restrict A C x)) A_neg L_neg"
      using neg' qneg[OF _ that(2)] len by (auto simp: list_all2_conv_all_nth)
  qed
qed(*<*)
end
(*>*)