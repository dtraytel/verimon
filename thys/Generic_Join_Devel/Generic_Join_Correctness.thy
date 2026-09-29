section \<open>Correctness\<close>

theory Generic_Join_Correctness
  imports Generic_Join
begin

subsection \<open>Well-formed queries\<close>

definition wf_atable :: "'a atable \<Rightarrow> bool" where
  "wf_atable X \<longleftrightarrow> distinct (fst X) \<and> table (fst X) (snd X)"

definition included :: "vertices \<Rightarrow> 'a query \<Rightarrow> bool" where
  "included V Q \<longleftrightarrow> (\<forall>X\<in>Q. set (fst X) \<subseteq> V)"

definition covering :: "vertices \<Rightarrow> 'a query \<Rightarrow> bool" where
  "covering V Q \<longleftrightarrow> V \<subseteq> (\<Union>X\<in>Q. set (fst X))"

definition non_empty_query :: "'a query \<Rightarrow> bool" where
  "non_empty_query Q \<longleftrightarrow> (\<forall>X\<in>Q. fst X \<noteq> [])"

definition rwf_query :: "vertices \<Rightarrow> 'a query \<Rightarrow> 'a query \<Rightarrow> bool" where
  "rwf_query V Qp Qn \<longleftrightarrow> finite V \<and> card Qp \<ge> 1 \<and> (\<forall>X\<in>Qp \<union> Qn. wf_atable X) \<and>
    covering V Qp \<and> included V Qp \<and> included V Qn \<and> non_empty_query Qp \<and> non_empty_query Qn"


subsection \<open>Tuples over the variables of a join\<close>

lemma set_cols[simp]: "finite V \<Longrightarrow> set (cols V) = V"
  by simp

lemma restrict_append2:
  "wf_tuple cs x \<Longrightarrow> set ds \<inter> set cs = {} \<Longrightarrow> restrict ds (cs @ cs') (x @ y) = restrict ds cs' y"
  by (rule restrict_cong) (auto simp: tup_get_append)

context
  fixes I J :: vertices
  assumes fin: "finite I" "finite J" and disj: "I \<inter> J = {}"
begin

lemma wf_tuple_merge: "wf_tuple (cols (I \<union> J)) (merge I J t1 t2)"
  by (simp add: merge_def)

lemma restrict_merge1:
  assumes "wf_tuple (cols I) t1"
  shows "restrict (cols I) (cols (I \<union> J)) (merge I J t1 t2) = t1"
proof -
  have "restrict (cols I) (cols (I \<union> J)) (merge I J t1 t2) = restrict (cols I) (cols I @ cols J) (t1 @ t2)"
    unfolding merge_def using fin by (intro restrict_restrict) auto
  also have "\<dots> = t1"
    using assms by (simp add: restrict_append restrict_idle)
  finally show ?thesis .
qed

lemma restrict_merge2:
  assumes "wf_tuple (cols I) t1" "wf_tuple (cols J) t2"
  shows "restrict (cols J) (cols (I \<union> J)) (merge I J t1 t2) = t2"
proof -
  have "restrict (cols J) (cols (I \<union> J)) (merge I J t1 t2) = restrict (cols J) (cols I @ cols J) (t1 @ t2)"
    unfolding merge_def using fin by (intro restrict_restrict) auto
  also have "\<dots> = t2"
    using assms fin disj by (subst restrict_append2) (auto simp: restrict_idle)
  finally show ?thesis .
qed

lemma merge_restrict:
  assumes "wf_tuple (cols (I \<union> J)) z"
  shows "merge I J (restrict (cols I) (cols (I \<union> J)) z) (restrict (cols J) (cols (I \<union> J)) z) = z"
proof (rule wf_tuple_cong[OF _ wf_tuple_merge assms], safe)
  fix c
  assume "c \<in> set (cols (I \<union> J))"
  then show "tup_get (cols (I \<union> J)) (merge I J (restrict (cols I) (cols (I \<union> J)) z)
      (restrict (cols J) (cols (I \<union> J)) z)) c = tup_get (cols (I \<union> J)) z c"
    using fin by (auto simp: merge_def tup_get_restrict tup_get_append)
qed simp

end

text \<open>A row of a table is determined by its values at the table's columns among @{term I} and
  among @{term J}.\<close>

lemma restrict_parts_eq:
  assumes "distinct cs" "wf_tuple cs y" "wf_tuple cs y'" "set cs \<subseteq> I \<union> J"
    "restrict (cols_in I cs) cs y = restrict (cols_in I cs) cs y'"
    "restrict (cols_in J cs) cs y = restrict (cols_in J cs) cs y'"
  shows "y = y'"
proof (rule wf_tuple_cong[OF assms(1-3)], safe)
  fix c
  assume c: "c \<in> set cs"
  show "tup_get cs y c = tup_get cs y' c"
  proof (cases "c \<in> I")
    case True
    then show ?thesis
      using c arg_cong[OF assms(5), of "\<lambda>x. tup_get (cols_in I cs) x c"] by (simp add: tup_get_restrict)
  next
    case False
    then show ?thesis
      using c assms(4) arg_cong[OF assms(6), of "\<lambda>x. tup_get (cols_in J cs) x c"]
      by (auto simp: tup_get_restrict)
  qed
qed

text \<open>A tuple over @{term V} read at a table's columns among @{term "K \<subseteq> V"}: through its part
  over @{term K} or through the table's columns.\<close>

lemma restrict_cols_in:
  assumes "finite V" "K \<subseteq> V" "set cs \<subseteq> V"
  shows "restrict (cols_in K cs) (cols K) (restrict (cols K) (cols V) z) =
    restrict (cols_in K cs) cs (restrict cs (cols V) z)"
proof -
  have "finite K"
    using assms(1,2) by (rule finite_subset[rotated])
  with assms have "restrict (cols_in K cs) (cols K) (restrict (cols K) (cols V) z) =
      restrict (cols_in K cs) (cols V) z"
    by (intro restrict_restrict) auto
  moreover have "restrict (cols_in K cs) cs (restrict cs (cols V) z) = restrict (cols_in K cs) (cols V) z"
    by (intro restrict_restrict) auto
  ultimately show ?thesis
    by simp
qed

lemma restrict_sub:
  assumes "finite V" "K \<subseteq> V" "set cs \<subseteq> K"
  shows "restrict cs (cols V) z = restrict cs (cols K) (restrict (cols K) (cols V) z)"
proof -
  have "finite K"
    using assms(1,2) by (rule finite_subset[rotated])
  with assms show ?thesis
    by (auto simp: restrict_restrict)
qed

text \<open>A tuple over @{term "I \<union> J"} is in a table if and only if its part over @{term J} is
  among the parts over @{term J} of the table's rows that agree with its part over @{term I}.\<close>

lemma mem_table_split:
  assumes "finite I" "finite J" "wf_atable (cs, X)" "set cs \<subseteq> I \<union> J"
  shows "restrict cs (cols (I \<union> J)) z \<in> X \<longleftrightarrow>
    restrict (cols_in J cs) (cols J) (restrict (cols J) (cols (I \<union> J)) z) \<in>
      restrict (cols_in J cs) cs ` {y \<in> X. restrict (cols_in I cs) cs y =
        restrict (cols_in I cs) (cols I) (restrict (cols I) (cols (I \<union> J)) z)}"
    (is "?y \<in> X \<longleftrightarrow> _")
proof -
  have fin: "finite (I \<union> J)"
    using assms(1,2) by simp
  note I = restrict_cols_in[OF fin Un_upper1 assms(4), of z]
  note J = restrict_cols_in[OF fin Un_upper2 assms(4), of z]
  have wf: "distinct cs" "table cs X"
    using assms(3) by (simp_all add: wf_atable_def)
  show ?thesis
  proof
    assume "?y \<in> X"
    then show "restrict (cols_in J cs) (cols J) (restrict (cols J) (cols (I \<union> J)) z) \<in>
      restrict (cols_in J cs) cs ` {y \<in> X. restrict (cols_in I cs) cs y =
        restrict (cols_in I cs) (cols I) (restrict (cols I) (cols (I \<union> J)) z)}"
      unfolding I J by blast
  next
    assume "restrict (cols_in J cs) (cols J) (restrict (cols J) (cols (I \<union> J)) z) \<in>
      restrict (cols_in J cs) cs ` {y \<in> X. restrict (cols_in I cs) cs y =
        restrict (cols_in I cs) (cols I) (restrict (cols I) (cols (I \<union> J)) z)}"
    then obtain y where y: "y \<in> X" "restrict (cols_in I cs) cs y = restrict (cols_in I cs) cs ?y"
      "restrict (cols_in J cs) cs y = restrict (cols_in J cs) cs ?y"
      unfolding I J by auto
    have "y = ?y"
      by (rule restrict_parts_eq[OF wf(1) tableD[OF wf(2) y(1)] wf_tuple_restrict assms(4) y(2,3)])
    with y(1) show "?y \<in> X"
      by simp
  qed
qed


subsection \<open>The base case\<close>

lemma rwf_queryD:
  assumes "rwf_query V Qp Qn"
  shows "finite V" "Qp \<noteq> {}" "finite Qp"
    "\<And>cs X. (cs, X) \<in> Qp \<union> Qn \<Longrightarrow> distinct cs \<and> table cs X \<and> set cs \<subseteq> V \<and> cs \<noteq> []"
    "\<And>x. x \<in> V \<Longrightarrow> \<exists>X\<in>Qp. x \<in> set (fst X)"
proof -
  note * = assms[unfolded rwf_query_def wf_atable_def included_def covering_def non_empty_query_def]
  show "finite V" "\<And>x. x \<in> V \<Longrightarrow> \<exists>X\<in>Qp. x \<in> set (fst X)"
    using * by blast+
  show "Qp \<noteq> {}" "finite Qp"
    using * by (auto intro: card_ge_0_finite)
  fix cs X
  assume "(cs, X) \<in> Qp \<union> Qn"
  moreover from * have "\<forall>X\<in>Qp \<union> Qn. distinct (fst X) \<and> table (fst X) (snd X) \<and> set (fst X) \<subseteq> V \<and> fst X \<noteq> []"
    by blast
  ultimately have "distinct (fst (cs, X)) \<and> table (fst (cs, X)) (snd (cs, X)) \<and>
    set (fst (cs, X)) \<subseteq> V \<and> fst (cs, X) \<noteq> []"
    by (rule bspec[rotated])
  then show "distinct cs \<and> table cs X \<and> set cs \<subseteq> V \<and> cs \<noteq> []"
    by simp
qed

lemma distinct_singleton_set: "distinct cs \<Longrightarrow> cs \<noteq> [] \<Longrightarrow> set cs \<subseteq> {v} \<Longrightarrow> cs = [v]"
  by (cases cs) (auto simp: subset_singleton_iff)

lemma base_correctness:
  assumes "rwf_query V Q Qn" "card V = 1"
  shows "z \<in> (\<Inter>(_, x)\<in>Q. x) - (\<Union>(_, x)\<in>Qn. x) \<longleftrightarrow> wf_tuple (cols V) z \<and>
    (\<forall>(cs, X)\<in>Q. restrict cs (cols V) z \<in> X) \<and> (\<forall>(cs, X)\<in>Qn. restrict cs (cols V) z \<notin> X)"
proof -
  obtain v where V: "V = {v}"
    using assms(2) card_1_singletonE by blast
  note Q = rwf_queryD[OF assms(1)]
  have tab: "cs = [v] \<and> table [v] X" if "(cs, X) \<in> Q \<union> Qn" for cs X
  proof -
    have "cs = [v]"
      using Q(4)[OF that] by (intro distinct_singleton_set) (auto simp: V)
    with Q(4)[OF that] show ?thesis
      by simp
  qed
  have restr: "restrict [v] [v] z = z" if "wf_tuple [v] z"
    using that by (simp add: restrict_idle)
  obtain cs0 X0 where X0: "(cs0, X0) \<in> Q"
    using Q(2) by auto
  show ?thesis
  proof
    assume z: "z \<in> (\<Inter>(_, x)\<in>Q. x) - (\<Union>(_, x)\<in>Qn. x)"
    then have "z \<in> X0"
      using X0 by fastforce
    then have "wf_tuple [v] z"
      using tab[OF UnI1[OF X0]] by (blast intro: tableD)
    with z tab show "wf_tuple (cols V) z \<and>
      (\<forall>(cs, X)\<in>Q. restrict cs (cols V) z \<in> X) \<and> (\<forall>(cs, X)\<in>Qn. restrict cs (cols V) z \<notin> X)"
      by (fastforce simp: V restr)
  next
    assume "wf_tuple (cols V) z \<and>
      (\<forall>(cs, X)\<in>Q. restrict cs (cols V) z \<in> X) \<and> (\<forall>(cs, X)\<in>Qn. restrict cs (cols V) z \<notin> X)"
    with tab show "z \<in> (\<Inter>(_, x)\<in>Q. x) - (\<Union>(_, x)\<in>Qn. x)"
      by (fastforce simp: V restr)
  qed
qed


subsection \<open>The recursive calls\<close>

lemma mem_filterQuery[simp]: "X \<in> filterQuery I Q \<longleftrightarrow> X \<in> Q \<and> set (fst X) \<inter> I \<noteq> {}"
  by auto

lemma mem_filterQueryNeg[simp]: "X \<in> filterQueryNeg I Q \<longleftrightarrow> X \<in> Q \<and> set (fst X) \<subseteq> I"
  by auto

declare filterQuery.simps[simp del] filterQueryNeg.simps[simp del]

lemma wf_atable_projectTable: "wf_atable X \<Longrightarrow> wf_atable (projectTable I X)"
  by (cases X) (auto simp: wf_atable_def table_def)

lemma wf_atable_semiJoin: "wf_atable X \<Longrightarrow> wf_atable (semiJoin X (I, t))"
  by (cases X) (auto simp: wf_atable_def table_def)

lemma fst_projectTable[simp]: "fst (projectTable I X) = cols_in I (fst X)"
  by (cases X) simp

lemma fst_semiJoin[simp]: "fst (semiJoin X (I, t)) = fst X"
  by (cases X) simp

lemma mem_projectQuery: "X \<in> projectQuery I Q \<longleftrightarrow> (\<exists>Y\<in>Q. X = projectTable I Y)"
  by auto

lemma mem_newQuery: "X \<in> newQuery J Q (I, t) \<longleftrightarrow> (\<exists>Y\<in>Q. X = projectTable J (semiJoin Y (I, t)))"
  by auto

lemma snd_projectTable_semiJoin: "snd (projectTable J (semiJoin X (I, t))) =
  restrict (cols_in J (fst X)) (fst X) ` {x \<in> snd X. restrict (cols_in I (fst X)) (fst X) x =
    restrict (cols_in I (fst X)) (cols I) t}"
  by (cases X) simp

lemma snd_projectTable: "snd (projectTable I X) = restrict (cols_in I (fst X)) (fst X) ` snd X"
  by (cases X) simp

declare projectTable.simps[simp del] semiJoin.simps[simp del] projectQuery.simps[simp del]
  newQuery.simps[simp del]

lemma ball_image_iff: "(\<forall>x\<in>f ` A. P x) \<longleftrightarrow> (\<forall>y\<in>A. P (f y))"
  by auto

lemma ball_filter_iff: "(\<forall>x\<in>Set.filter Q A. P x) \<longleftrightarrow> (\<forall>y\<in>A. Q y \<longrightarrow> P y)"
  by auto

lemma ball_Diff_iff: "(\<forall>x\<in>A - B. P x) \<longleftrightarrow> (\<forall>y\<in>A. y \<notin> B \<longrightarrow> P y)"
  by auto

text \<open>The conditions the recursive calls impose, table by table of the original query.\<close>

lemma all_projectQuery: "(\<forall>(A, X)\<in>projectQuery I (filterQuery I Q). restrict A (cols I) t \<in> X) \<longleftrightarrow>
  (\<forall>(cs, X)\<in>Q. set cs \<inter> I \<noteq> {} \<longrightarrow> restrict (cols_in I cs) (cols I) t \<in> restrict (cols_in I cs) cs ` X)"
  unfolding projectQuery.simps filterQuery.simps ball_image_iff ball_filter_iff
  by (intro ball_cong[OF refl]) (auto simp: split_beta snd_projectTable)

lemma all_filterQueryNeg: "(\<forall>(A, X)\<in>filterQueryNeg I Qn. restrict A (cols I) t \<notin> X) \<longleftrightarrow>
  (\<forall>(cs, X)\<in>Qn. set cs \<subseteq> I \<longrightarrow> restrict cs (cols I) t \<notin> X)"
  unfolding filterQueryNeg.simps ball_filter_iff
  by (intro ball_cong[OF refl]) (auto simp: split_beta)

lemma all_newQuery: "(\<forall>(A, X)\<in>newQuery J (filterQuery J Q) (I, t). restrict A (cols J) y \<in> X) \<longleftrightarrow>
  (\<forall>(cs, X)\<in>Q. set cs \<inter> J \<noteq> {} \<longrightarrow> restrict (cols_in J cs) (cols J) y \<in> restrict (cols_in J cs) cs `
    {x \<in> X. restrict (cols_in I cs) cs x = restrict (cols_in I cs) (cols I) t})"
  unfolding newQuery.simps filterQuery.simps ball_image_iff ball_filter_iff
  by (intro ball_cong[OF refl]) (auto simp: split_beta snd_projectTable_semiJoin)

lemma all_newQuery_neg: "(\<forall>(A, X)\<in>newQuery J (Qn - filterQueryNeg I Qn) (I, t). restrict A (cols J) y \<notin> X) \<longleftrightarrow>
  (\<forall>(cs, X)\<in>Qn. \<not> set cs \<subseteq> I \<longrightarrow> restrict (cols_in J cs) (cols J) y \<notin> restrict (cols_in J cs) cs `
    {x \<in> X. restrict (cols_in I cs) cs x = restrict (cols_in I cs) (cols I) t})"
  unfolding newQuery.simps ball_image_iff ball_Diff_iff
  by (intro ball_cong[OF refl]) (auto simp: split_beta snd_projectTable_semiJoin)

context getIJ
begin

lemma rwf_query_I:
  assumes rwf: "rwf_query V Q Qn" and card: "card V \<ge> 2" and IJ: "(I, J) = getIJ Q Qn V"
  shows "rwf_query I (projectQuery I (filterQuery I Q)) (filterQueryNeg I Qn)"
proof -
  note Q = rwf_queryD[OF rwf]
  note IJ' = getIJProperties[OF card IJ]
  have wf: "wf_atable X" if "X \<in> Q \<union> Qn" for X
    using rwf that by (auto simp: rwf_query_def)
  have "finite I"
    using Q(1) IJ'(5) by auto
  obtain i where "i \<in> I"
    using IJ'(1) by (metis card.empty ex_in_conv not_one_le_zero)
  then obtain X0 where "X0 \<in> Q" "i \<in> set (fst X0)"
    using Q(5) IJ'(5) by blast
  with \<open>i \<in> I\<close> have "projectTable I X0 \<in> projectQuery I (filterQuery I Q)"
    unfolding mem_projectQuery mem_filterQuery by (intro bexI[of _ X0]) auto
  then have ne: "projectQuery I (filterQuery I Q) \<noteq> {}"
    by blast
  have fin: "finite (projectQuery I (filterQuery I Q))"
    using Q(3) by (simp add: projectQuery.simps filterQuery.simps)
  show ?thesis
    unfolding rwf_query_def
  proof (intro conjI)
    show "finite I" by fact
    show "card (projectQuery I (filterQuery I Q)) \<ge> 1"
      using ne fin by (simp add: Suc_le_eq card_gt_0_iff)
    show "\<forall>X\<in>projectQuery I (filterQuery I Q) \<union> filterQueryNeg I Qn. wf_atable X"
    proof
      fix X
      assume "X \<in> projectQuery I (filterQuery I Q) \<union> filterQueryNeg I Qn"
      then show "wf_atable X"
        unfolding Un_iff mem_projectQuery mem_filterQuery mem_filterQueryNeg
        using wf wf_atable_projectTable mem_filterQuery[THEN iffD1] by blast
    qed
    show "covering I (projectQuery I (filterQuery I Q))"
      using Q(5) IJ'(5) by (fastforce simp: covering_def mem_projectQuery projectTable.simps)
    show "included I (projectQuery I (filterQuery I Q))" "included I (filterQueryNeg I Qn)"
      by (auto simp: included_def mem_projectQuery projectTable.simps)
    show "non_empty_query (projectQuery I (filterQuery I Q))"
      by (auto simp: non_empty_query_def mem_projectQuery projectTable.simps filter_empty_conv
        empty_filter_conv)
    show "non_empty_query (filterQueryNeg I Qn)"
      using rwf by (auto simp: rwf_query_def non_empty_query_def)
  qed
qed

lemma rwf_query_J:
  assumes rwf: "rwf_query V Q Qn" and card: "card V \<ge> 2" and IJ: "(I, J) = getIJ Q Qn V"
  shows "rwf_query J (newQuery J (filterQuery J Q) (I, t)) (newQuery J (Qn - filterQueryNeg I Qn) (I, t))"
proof -
  note Q = rwf_queryD[OF rwf]
  note IJ' = getIJProperties[OF card IJ]
  have wf: "wf_atable X" if "X \<in> Q \<union> Qn" for X
    using rwf that by (auto simp: rwf_query_def)
  have "finite J"
    using Q(1) IJ'(5) by auto
  obtain j where "j \<in> J"
    using IJ'(2) by (metis card.empty ex_in_conv not_one_le_zero)
  then obtain X0 where "X0 \<in> Q" "j \<in> set (fst X0)"
    using Q(5) IJ'(5) by blast
  with \<open>j \<in> J\<close> have "projectTable J (semiJoin X0 (I, t)) \<in> newQuery J (filterQuery J Q) (I, t)"
    unfolding mem_newQuery mem_filterQuery by (intro bexI[of _ X0]) auto
  then have ne: "newQuery J (filterQuery J Q) (I, t) \<noteq> {}"
    by blast
  have fin: "finite (newQuery J (filterQuery J Q) (I, t))"
    using Q(3) by (simp add: newQuery.simps filterQuery.simps)
  have neg: "set (fst X) \<inter> J \<noteq> {}" if "X \<in> Qn" "\<not> set (fst X) \<subseteq> I" for X
    using that Q(4)[of "fst X" "snd X"] IJ'(5) by auto
  show ?thesis
    unfolding rwf_query_def
  proof (intro conjI)
    show "finite J" by fact
    show "card (newQuery J (filterQuery J Q) (I, t)) \<ge> 1"
      using ne fin by (simp add: Suc_le_eq card_gt_0_iff)
    show "\<forall>X\<in>newQuery J (filterQuery J Q) (I, t) \<union> newQuery J (Qn - filterQueryNeg I Qn) (I, t). wf_atable X"
    proof
      fix X
      assume "X \<in> newQuery J (filterQuery J Q) (I, t) \<union> newQuery J (Qn - filterQueryNeg I Qn) (I, t)"
      then show "wf_atable X"
        unfolding Un_iff mem_newQuery mem_filterQuery Diff_iff
        using wf wf_atable_projectTable wf_atable_semiJoin mem_filterQuery[THEN iffD1] by blast
    qed
    show "covering J (newQuery J (filterQuery J Q) (I, t))"
      using Q(5) IJ'(5)
      by (fastforce simp: covering_def mem_newQuery projectTable.simps semiJoin.simps)
    show "included J (newQuery J (filterQuery J Q) (I, t))"
      "included J (newQuery J (Qn - filterQueryNeg I Qn) (I, t))"
      by (auto simp: included_def mem_newQuery projectTable.simps semiJoin.simps)
    show "non_empty_query (newQuery J (filterQuery J Q) (I, t))"
      by (auto simp: non_empty_query_def mem_newQuery projectTable.simps semiJoin.simps
        filter_empty_conv empty_filter_conv)
    show "non_empty_query (newQuery J (Qn - filterQueryNeg I Qn) (I, t))"
      using neg by (fastforce simp: non_empty_query_def mem_newQuery projectTable.simps
        semiJoin.simps filter_empty_conv empty_filter_conv)
  qed
qed

end

end
