(*<*)
theory Wf_Table_Proof
  imports "Monitor_Impl.Wf_Table"
begin
(*>*)


lemma distinct_wf_table_sig[simp]: "distinct (wf_table_sig t)"
  by transfer auto

lemma wf_table_set_table: "wf_table_sig t = cs \<Longrightarrow> table cs (wf_table_set t)"
  by transfer auto

lemma wf_table_set_wf: "wf_table_sig t = cs \<Longrightarrow> x \<in> wf_table_set t \<Longrightarrow> wf_tuple cs x"
  by transfer (auto simp: table_def)

lemma wf_table_eqI:
  assumes "wf_table_sig t = wf_table_sig t'" "wf_table_set t = wf_table_set t'"
  shows "t = t'"
  using assms
  by transfer auto

lemma wf_table_sig_of_set: "distinct cs \<Longrightarrow> wf_table_sig (wf_table_of_set cs T) = cs"
  by transfer auto

lemma wf_table_set_of_set: "distinct cs \<Longrightarrow> wf_table_set (wf_table_of_set cs T) = Set.filter (wf_tuple cs) T"
  by transfer auto

lemma wf_table_sig_union: "wf_table_sig (wf_table_union t1 t2) = wf_table_sig t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_union: "wf_table_sig t1 = wf_table_sig t2 \<Longrightarrow>
  wf_table_set (wf_table_union t1 t2) = wf_table_set t1 \<union> wf_table_set t2"
  by transfer auto

lemma wf_table_set_union_deg: "wf_table_sig t1 \<noteq> wf_table_sig t2 \<Longrightarrow>
  wf_table_set (wf_table_union t1 t2) = wf_table_set t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_union': "wf_table_set (wf_table_union t1 t2) =
  (if wf_table_sig t1 = wf_table_sig t2 then wf_table_set t1 \<union> wf_table_set t2 else wf_table_set t1)"
  using wf_table_set_union wf_table_set_union_deg
  by (fastforce split: if_splits)

lemma wf_table_sig_join: "wf_table_sig (wf_table_join t1 t2) = cols_union (wf_table_sig t1) (wf_table_sig t2)"
  by transfer auto

lemma wf_table_set_join: "wf_table_set (wf_table_join t1 t2) =
  join (wf_table_sig t1) (wf_table_set t1) True (wf_table_sig t2) (wf_table_set t2)"
  by transfer (auto simp del: bin_join.simps simp: bin_join_table)

lemma wf_table_sig_antijoin: "wf_table_sig (wf_table_antijoin t1 t2) = wf_table_sig t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_antijoin: "set (wf_table_sig t2) \<subseteq> set (wf_table_sig t1) \<Longrightarrow>
  wf_table_set (wf_table_antijoin t1 t2) =
  join (wf_table_sig t1) (wf_table_set t1) False (wf_table_sig t2) (wf_table_set t2)"
  by transfer (auto simp del: bin_join.simps simp: bin_join_table)

lemma wf_table_set_antijoin_deg: "\<not> set (wf_table_sig t2) \<subseteq> set (wf_table_sig t1) \<Longrightarrow>
  wf_table_set (wf_table_antijoin t1 t2) = wf_table_set t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_antijoin': "wf_table_set (wf_table_antijoin t1 t2) =
  (if set (wf_table_sig t2) \<subseteq> set (wf_table_sig t1)
   then join (wf_table_sig t1) (wf_table_set t1) False (wf_table_sig t2) (wf_table_set t2)
   else wf_table_set t1)"
  by (simp add: wf_table_set_antijoin wf_table_set_antijoin_deg)

lemma idx_wfD:
  assumes "idx_wf cs I T" "Mapping.lookup T x = Some Y"
  shows "table cs Y" "Y \<noteq> {}" "z \<in> Y \<Longrightarrow> x = restrict I cs z"
  using assms by (auto simp: idx_wf_def)

lemma idx_wfI:
  "(\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table cs Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I cs z)) \<Longrightarrow>
  idx_wf cs I T"
  by (auto simp: idx_wf_def)

lemma mem_set_of_idx: "z \<in> set_of_idx T \<longleftrightarrow> (\<exists>x Y. Mapping.lookup T x = Some Y \<and> z \<in> Y)"
  by transfer (auto simp: ran_def Map_To_Mapping.map_apply_def)

text \<open>A tuple of the index is in the cluster of its key.\<close>

lemma idx_wf_lookup:
  assumes "idx_wf cs I T" "z \<in> set_of_idx T"
  obtains Y where "Mapping.lookup T (restrict I cs z) = Some Y" "z \<in> Y"
  using assms by (auto simp: mem_set_of_idx dest: idx_wfD(3))

lemma lookup_cluster: "Mapping.lookup (cluster f Y) x =
  (if Some x \<in> f ` Y then Some {y \<in> Y. f y = Some x} else None)"
  by transfer (simp add: Map_To_Mapping.map_apply_def)

lemma lookup_mapping_join: "Mapping.lookup (mapping_join f m m') x =
  (case Mapping.lookup m x of None \<Rightarrow> None
   | Some y \<Rightarrow> (case Mapping.lookup m' x of None \<Rightarrow> None | Some y' \<Rightarrow> Some (f y y')))"
  by (simp add: Mapping.lookup_def mapping_join.rep_eq split: option.splits)

lemma lookup_mapping_antijoin: "Mapping.lookup (mapping_antijoin m m') x =
  (case Mapping.lookup m x of None \<Rightarrow> None
   | Some y \<Rightarrow> (case Mapping.lookup m' x of None \<Rightarrow> Some y | Some y' \<Rightarrow> None))"
  by (simp add: Mapping.lookup_def mapping_antijoin.rep_eq split: option.splits)

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

text \<open>When the second index is keyed by all its columns, it is a set of keys.\<close>

lemma idx_wf_all_cols:
  assumes "distinct ds" "idx_wf ds ds T'"
  shows "w \<in> set_of_idx T' \<longleftrightarrow> Mapping.lookup T' w \<noteq> None"
proof
  assume "w \<in> set_of_idx T'"
  then obtain Y where "Mapping.lookup T' (restrict ds ds w) = Some Y"
    using idx_wf_lookup[OF assms(2)] by blast
  moreover have "restrict ds ds w = w"
    using idx_wf_table[OF assms(2)] \<open>w \<in> set_of_idx T'\<close> restrict_idle[OF assms(1)] by (auto simp: table_def)
  ultimately show "Mapping.lookup T' w \<noteq> None"
    by simp
next
  assume "Mapping.lookup T' w \<noteq> None"
  then obtain Y where Y: "Mapping.lookup T' w = Some Y"
    by blast
  then obtain y where "y \<in> Y"
    using idx_wfD(2)[OF assms(2)] by blast
  moreover have "w = y"
    using idx_wfD(3)[OF assms(2) Y \<open>y \<in> Y\<close>] idx_wfD(1)[OF assms(2) Y] \<open>y \<in> Y\<close> restrict_idle[OF assms(1)]
    by (auto simp: table_def)  ultimately show "w \<in> set_of_idx T'"
    using Y by (auto simp: mem_set_of_idx)
qed

lemma mapping_antijoin_idx:
  fixes T T' :: "('a tuple, 'a table) mapping"
  assumes "distinct cs" "distinct ds" "set ds \<subseteq> set cs" "idx_wf cs ds T" "idx_wf ds ds T'"
  shows "set_of_idx (mapping_antijoin T T') = join cs (set_of_idx T) False ds (set_of_idx T')"
    "idx_wf cs ds (mapping_antijoin T T')"
proof -
  note antijoin = join_False_iff[OF assms(1,2) idx_wf_table[OF assms(4)] idx_wf_table[OF assms(5)] assms(3)]
  show "set_of_idx (mapping_antijoin T T') = join cs (set_of_idx T) False ds (set_of_idx T')"
  proof (rule set_eqI, rule iffI)
    fix z
    assume "z \<in> set_of_idx (mapping_antijoin T T')"
    then obtain x Y where Y: "Mapping.lookup T x = Some Y" "Mapping.lookup T' x = None" "z \<in> Y"
      by (auto simp: mem_set_of_idx lookup_mapping_antijoin split: option.splits)
    have "x = restrict ds cs z"
      using idx_wfD(3)[OF assms(4) Y(1,3)] .
    then have "restrict ds cs z \<notin> set_of_idx T'"
      using Y(2) by (simp add: idx_wf_all_cols[OF assms(2,5)])
    moreover have "z \<in> set_of_idx T"
      using Y(1,3) by (auto simp: mem_set_of_idx intro!: exI[of _ x])
    ultimately show "z \<in> join cs (set_of_idx T) False ds (set_of_idx T')"
      by (simp add: antijoin)
  next
    fix z
    assume "z \<in> join cs (set_of_idx T) False ds (set_of_idx T')"
    then have z: "z \<in> set_of_idx T" "Mapping.lookup T' (restrict ds cs z) = None"
      by (simp_all add: antijoin idx_wf_all_cols[OF assms(2,5)])
    obtain Y where Y: "Mapping.lookup T (restrict ds cs z) = Some Y" "z \<in> Y"
      using idx_wf_lookup[OF assms(4) z(1)] .
    then show "z \<in> set_of_idx (mapping_antijoin T T')"
      using z(2) by (auto simp: mem_set_of_idx lookup_mapping_antijoin intro!: exI[of _ "restrict ds cs z"])
  qed  show "idx_wf cs ds (mapping_antijoin T T')"
    using assms(4) by (auto simp: idx_wf_def lookup_mapping_antijoin split: option.splits)
qed

lemma distinct_wf_idx_sig[simp]: "distinct (wf_idx_sig t)"
  by transfer auto

lemma wf_idx_set_table: "wf_idx_sig t = cs \<Longrightarrow> table cs (wf_idx_set t)"
  by transfer (auto intro: idx_wf_table)

lemma wf_idx_set_wf: "wf_idx_sig t = cs \<Longrightarrow> x \<in> wf_idx_set t \<Longrightarrow> wf_tuple cs x"
  using wf_idx_set_table by (auto simp: table_def)

lemma wf_idx_sig_of_table[simp]: "wf_idx_sig (wf_idx_of_table I t) = wf_table_sig t"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_of_table[simp]: "wf_idx_set (wf_idx_of_table I t) = wf_table_set t"
  by transfer (auto simp: Let_def idx_create(1))

lemma table_filter: "table cs {a \<in> T. wf_tuple cs a}"
  by (auto simp: table_def)

lemma idx_wf_empty[simp]: "idx_wf cs I Mapping.empty"
  by (simp add: idx_wf_def)

lemma wf_idx_sig_of_set: "distinct cs \<Longrightarrow> wf_idx_sig (wf_idx_of_set cs I T) = cs"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_of_set: "distinct cs \<Longrightarrow> wf_idx_set (wf_idx_of_set cs I T) = Set.filter (wf_tuple cs) T"
  by transfer (auto simp: Let_def idx_create(1)[OF table_filter])
lemma wf_idx_sig_reindex: "wf_idx_sig (wf_idx_reindex I t) = wf_idx_sig t"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_reindex: "wf_idx_set (wf_idx_reindex I t) = wf_idx_set t"
  by transfer (auto simp: Let_def idx_reindex(1))

lemma wf_idx_rep:
  obtains cs I T where "Rep_wf_idx t = (cs, I, T)" "distinct cs" "set I \<subseteq> set cs" "idx_wf cs I T"
  using Rep_wf_idx[of t] by auto

lemma wf_idx_sig_union: "wf_idx_sig (wf_idx_union t1 t2) = wf_idx_sig t1"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_union: "wf_idx_sig t1 = wf_idx_sig t2 \<Longrightarrow>
  wf_idx_set (wf_idx_union t1 t2) = wf_idx_set t1 \<union> wf_idx_set t2"
proof -
  assume sig: "wf_idx_sig t1 = wf_idx_sig t2"
  obtain cs I T where t1: "Rep_wf_idx t1 = (cs, I, T)" "distinct cs" "set I \<subseteq> set cs" "idx_wf cs I T"
    by (rule wf_idx_rep)
  obtain I' T' where t2: "Rep_wf_idx t2 = (cs, I', T')" "idx_wf cs I' T'"
    using wf_idx_rep[of t2] sig by (metis prod.inject t1(1) wf_idx_sig.rep_eq case_prod_conv)
  define I'' where "I'' = filter (\<lambda>c. c \<in> set I') I"
  note R = idx_reindex[OF t1(4), of I''] idx_reindex[OF t2(2), of I'']
  show ?thesis
    using idx_union(1)[OF R(2) R(4)]
    by (simp add: wf_idx_set.rep_eq wf_idx_union.rep_eq t1(1) t2(1) Let_def I''_def[symmetric] R(1,3))
qed

lemma wf_idx_set_union_deg: "wf_idx_sig t1 \<noteq> wf_idx_sig t2 \<Longrightarrow> wf_idx_set (wf_idx_union t1 t2) = wf_idx_set t1"
  by (simp add: wf_idx_set.rep_eq wf_idx_sig.rep_eq wf_idx_union.rep_eq split: prod.splits)
lemma wf_idx_set_union': "wf_idx_set (wf_idx_union t1 t2) =
  (if wf_idx_sig t1 = wf_idx_sig t2 then wf_idx_set t1 \<union> wf_idx_set t2 else wf_idx_set t1)"
  by (simp add: wf_idx_set_union wf_idx_set_union_deg)

lemma wf_idx_sig_join: "wf_idx_sig (wf_idx_join t1 t2) = cols_union (wf_idx_sig t1) (wf_idx_sig t2)"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_join: "wf_idx_set (wf_idx_join t1 t2) =
  join (wf_idx_sig t1) (wf_idx_set t1) True (wf_idx_sig t2) (wf_idx_set t2)"
proof -
  obtain cs I T where t1: "Rep_wf_idx t1 = (cs, I, T)" "distinct cs" "set I \<subseteq> set cs" "idx_wf cs I T"
    by (rule wf_idx_rep)
  obtain ds I' T' where t2: "Rep_wf_idx t2 = (ds, I', T')" "distinct ds" "set I' \<subseteq> set ds" "idx_wf ds I' T'"
    by (rule wf_idx_rep)
  define I'' where "I'' = filter (\<lambda>c. c \<in> set I') I"
  have I'': "set I'' \<subseteq> set cs" "set I'' \<subseteq> set ds"
    using t1(3) t2(3) by (auto simp: I''_def)
  note R = idx_reindex[OF t1(4), of I''] idx_reindex[OF t2(4), of I'']
  show ?thesis
    using idx_join(1)[OF t1(2) t2(2) I'' R(2) R(4)]
    by (simp add: wf_idx_set.rep_eq wf_idx_sig.rep_eq wf_idx_join.rep_eq t1(1) t2(1) Let_def
      I''_def[symmetric] R(1,3))
qed

lemma wf_idx_sig_antijoin: "wf_idx_sig (wf_idx_antijoin t1 t2) = wf_idx_sig t1"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_antijoin: "set (wf_idx_sig t2) \<subseteq> set (wf_idx_sig t1) \<Longrightarrow>
  wf_idx_set (wf_idx_antijoin t1 t2) = join (wf_idx_sig t1) (wf_idx_set t1) False (wf_idx_sig t2) (wf_idx_set t2)"
proof -
  assume sub: "set (wf_idx_sig t2) \<subseteq> set (wf_idx_sig t1)"
  obtain cs I T where t1: "Rep_wf_idx t1 = (cs, I, T)" "distinct cs" "set I \<subseteq> set cs" "idx_wf cs I T"
    by (rule wf_idx_rep)
  obtain ds I' T' where t2: "Rep_wf_idx t2 = (ds, I', T')" "distinct ds" "set I' \<subseteq> set ds" "idx_wf ds I' T'"
    by (rule wf_idx_rep)
  define I'' where "I'' = filter (\<lambda>c. c \<in> set I') I"
  have ds: "set ds \<subseteq> set cs"
    using sub by (simp add: wf_idx_sig.rep_eq t1 t2)
  have I'': "set I'' \<subseteq> set cs" "set I'' \<subseteq> set ds"
    using t1(3) t2(3) by (auto simp: I''_def)
  note R = idx_reindex[OF t1(4), of I''] idx_reindex[OF t2(4), of I'']
  show ?thesis
  proof (cases "I'' = ds")
    case True
    show ?thesis
      using mapping_antijoin_idx(1)[OF t1(2) t2(2) ds R(2)[unfolded True] R(4)[unfolded True]] True ds
      by (simp add: wf_idx_set.rep_eq wf_idx_sig.rep_eq wf_idx_antijoin.rep_eq t1(1) t2(1) Let_def
        I''_def[symmetric] R(1,3)[unfolded True])
  next
    case False
    show ?thesis
      using idx_antijoin(1)[OF t1(2) t2(2) I''(2) ds R(2) R(4)] False ds
      by (simp add: wf_idx_set.rep_eq wf_idx_sig.rep_eq wf_idx_antijoin.rep_eq t1(1) t2(1) Let_def
        I''_def[symmetric] R(1,3))
  qed
qed

lemma wf_idx_set_antijoin_deg: "\<not> set (wf_idx_sig t2) \<subseteq> set (wf_idx_sig t1) \<Longrightarrow>
  wf_idx_set (wf_idx_antijoin t1 t2) = wf_idx_set t1"
proof -
  assume sub: "\<not> set (wf_idx_sig t2) \<subseteq> set (wf_idx_sig t1)"
  obtain cs I T where t1: "Rep_wf_idx t1 = (cs, I, T)"
    by (rule wf_idx_rep)
  obtain ds I' T' where t2: "Rep_wf_idx t2 = (ds, I', T')"
    by (rule wf_idx_rep)
  show ?thesis
    using sub by (simp add: wf_idx_set.rep_eq wf_idx_sig.rep_eq wf_idx_antijoin.rep_eq t1 t2)
qed
lemma wf_table_of_idx_of_wf_set[simp]: "wf_table_of_idx (wf_idx_of_wf_set I t) = wf_table_of_wf_set t"
  by (rule wf_table_eqI; transfer) (auto simp: Let_def idx_create(1))

lemma wf_table_of_wf_set_of_idx[simp]: "wf_table_of_wf_set (wf_set_of_idx t) = wf_table_of_idx t"
  by (rule wf_table_eqI; transfer) auto

text \<open>The operations on the two representations.\<close>

lemma wf_table_union_wf_set: "wf_table_union (wf_table_of_wf_set t) (wf_table_of_wf_set t') =
  wf_table_of_wf_set (wf_set_union t t')"
  by transfer auto

lemma wf_table_join_wf_set: "wf_table_join (wf_table_of_wf_set t) (wf_table_of_wf_set t') =
  wf_table_of_wf_set (wf_set_join t t')"
  by transfer auto

lemma wf_table_antijoin_wf_set: "wf_table_antijoin (wf_table_of_wf_set t) (wf_table_of_wf_set t') =
  wf_table_of_wf_set (wf_set_antijoin t t')"
  by transfer auto

end
