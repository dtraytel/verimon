(*<*)
theory Table_Join
  imports "MFOTL_Monitor_Devel.Table"
begin
(*>*)

section \<open>Joins of tables\<close>

text \<open>Facts about the join of two tables (@{const join}) and the reordering of a table's columns
  that any evaluation of conjunctions relies on, whichever join algorithm implements them.\<close>

abbreviation "join_cond pos t \<equiv> (\<lambda>as. if pos then as \<in> t else as \<notin> t)"

abbreviation "join_filter_cond pos t \<equiv> (\<lambda>as _. join_cond pos t as)"

lemma join_sub:
  assumes "distinct cs" "distinct ds" "table cs t" "table ds t'" "set ds \<subseteq> set cs"
  shows "join cs t pos ds t' = {as \<in> t. join_cond pos t' (restrict ds cs as)}"
proof (rule set_eqI)
  fix v
  have "cols_union cs ds = cs"
    by (rule cols_union_subset[OF assms(5)])
  then show "v \<in> join cs t pos ds t' \<longleftrightarrow> v \<in> {as \<in> t. join_cond pos t' (restrict ds cs as)}"
    using join_restrict[OF assms(1-4), of pos v] assms(5) tableD[OF assms(3), of v]
      restrict_idle[OF assms(1), of v]
    by auto
qed

text \<open>The join of two tables over the same columns is their intersection or difference.\<close>

lemma join_eq:
  assumes "table cs t1" "table cs t2" "distinct cs"
  shows "join cs t2 pos cs t1 = (if pos then t2 \<inter> t1 else t2 - t1)"
proof -
  have idle: "restrict cs cs x = x" if "x \<in> t2" for x
    using restrict_idle[OF assms(3) tableD[OF assms(2) that]] .
  show ?thesis
    using join_sub[OF assms(3,3,2,1) subset_refl, of pos] by (auto simp: idle)
qed

lemma join_True_iff:
  assumes "distinct cs" "distinct ds" "table cs X" "table ds Y"
  shows "v \<in> join cs X True ds Y \<longleftrightarrow> wf_tuple (cols_union cs ds) v \<and>
    restrict cs (cols_union cs ds) v \<in> X \<and> restrict ds (cols_union cs ds) v \<in> Y"
  using join_restrict[OF assms, of True v] by simp

lemma join_False_iff:
  assumes "distinct cs" "distinct ds" "table cs X" "table ds Y" "set ds \<subseteq> set cs"
  shows "v \<in> join cs X False ds Y \<longleftrightarrow> v \<in> X \<and> restrict ds cs v \<notin> Y"
  using join_restrict[OF assms(1-4), of False v] assms(5) tableD[OF assms(3), of v]
    restrict_idle[OF assms(1), of v]
  by (auto simp: cols_union_subset)

lemma join_sub':
  assumes "distinct cs" "distinct ds" "table cs t" "table ds t'" "set cs \<subseteq> set ds"
  shows "join cs t True ds t' = restrict (cols_union cs ds) ds ` {as \<in> t'. restrict cs ds as \<in> t}"
    (is "_ = ?R")
proof (rule set_eqI)
  fix v
  let ?U = "cols_union cs ds"
  have U: "set ?U = set ds" "distinct ?U"
    using assms(1,2,5) by auto
  show "v \<in> join cs t True ds t' \<longleftrightarrow> v \<in> ?R"
  proof
    assume "v \<in> join cs t True ds t'"
    then have v: "wf_tuple ?U v" "restrict cs ?U v \<in> t" "restrict ds ?U v \<in> t'"
      using join_restrict[OF assms(1-4), of True v] by simp_all
    have "restrict cs ds (restrict ds ?U v) = restrict cs ?U v"
      using assms(5) by (simp add: restrict_restrict)
    moreover have "restrict ?U ds (restrict ds ?U v) = v"
      using U v(1) by (simp add: restrict_restrict restrict_idle)
    ultimately show "v \<in> ?R"
      using v(2,3) by (auto intro!: image_eqI[where x = "restrict ds ?U v"])
  next
    assume "v \<in> ?R"
    then obtain y where y: "y \<in> t'" "restrict cs ds y \<in> t" and v: "v = restrict ?U ds y"
      by blast
    have "restrict cs ?U v = restrict cs ds y"
      using U assms(5) by (simp add: v restrict_restrict)
    moreover have "restrict ds ?U v = y"
      using U y(1) tableD[OF assms(4)] by (simp add: v restrict_restrict restrict_idle assms(2))
    ultimately show "v \<in> join cs t True ds t'"
      using join_restrict[OF assms(1-4), of True v] y by (simp add: v)
  qed
qed


definition reorder :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "reorder cs ds t = (if cs = ds then t else restrict cs ds ` t)"

lemma mem_reorder:
  assumes "distinct cs" "distinct ds" "set cs = set ds" "table ds t"
  shows "z \<in> reorder cs ds t \<longleftrightarrow> wf_tuple cs z \<and> restrict ds cs z \<in> t"
proof (cases "cs = ds")
  case True
  then show ?thesis
    using assms(1,4) by (auto simp: reorder_def restrict_idle dest: tableD)
next
  case False
  show ?thesis
  proof
    assume "z \<in> reorder cs ds t"
    then obtain y where "y \<in> t" "z = restrict cs ds y"
      using False by (auto simp: reorder_def)
    moreover have "restrict ds cs (restrict cs ds y) = y" if "y \<in> t" for y
      using assms that by (simp add: restrict_restrict restrict_idle tableD)
    ultimately show "wf_tuple cs z \<and> restrict ds cs z \<in> t"
      by simp
  next
    assume z: "wf_tuple cs z \<and> restrict ds cs z \<in> t"
    then have "restrict cs ds (restrict ds cs z) = z"
      using assms(1,3) by (simp add: restrict_restrict restrict_idle)
    with z False show "z \<in> reorder cs ds t"
      by (auto simp: reorder_def intro: rev_image_eqI)
  qed
qed

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

lemma join_cond_restrict_perm:
  assumes "set L = set R" "distinct L" "distinct R" "table L l" "wf_tuple R x"
  shows "join_cond pos (restrict R L ` l) x \<longleftrightarrow> join_cond pos l (restrict L R x)"
proof -
  have "x \<in> restrict R L ` l \<longleftrightarrow> restrict L R x \<in> l"
  proof
    assume "x \<in> restrict R L ` l"
    then obtain y where y: "y \<in> l" "x = restrict R L y"
      by auto
    then show "restrict L R x \<in> l"
      using restrict_restrict[of L R L y] restrict_idle[OF assms(2) tableD[OF assms(4) y(1)]] assms(1)
      by auto
  next
    assume "restrict L R x \<in> l"
    moreover have "restrict R L (restrict L R x) = x"
      using restrict_restrict[of R L R x] restrict_idle[OF assms(3,5)] assms(1)
      by auto
    ultimately show "x \<in> restrict R L ` l"
      by (metis image_eqI)
  qed
  then show ?thesis
    by auto
qed


(*<*)
end
(*>*)
