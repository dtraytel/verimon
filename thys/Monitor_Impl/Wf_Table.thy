theory Wf_Table
  imports "Containers.Containers" "HOL-Library.Code_Target_Nat" Optimized_Join "Monitor_DS.Cluster" "Monitor_DS.Mapping_Code"
begin

section \<open>Tables that carry their columns\<close>

text \<open>A @{text wf_table} is a table together with the list of its columns.  The generated code
  represents it either as a plain set (@{text wf_set}) or as an index (@{text wf_idx}) that
  clusters the tuples by their values at some of the columns; joins of two indexes on the same
  key columns join cluster by cluster.\<close>

subsection \<open>Tables\<close>

typedef 'a wf_table = "{(cs :: nat list, T :: 'a table) | cs T. distinct cs \<and> table cs T}"
  by (rule exI[of _ "([], {})"]) auto

setup_lifting type_definition_wf_table

lift_definition wf_table_sig :: "'a wf_table \<Rightarrow> nat list" is fst .

lift_definition wf_table_set :: "'a wf_table \<Rightarrow> 'a table" is snd .

lemma wf_table_eqI:
  assumes "wf_table_sig t = wf_table_sig t'" "wf_table_set t = wf_table_set t'"
  shows "t = t'"
  using assms
  by transfer auto

lift_definition wf_table_of_set :: "nat list \<Rightarrow> 'a table \<Rightarrow> 'a wf_table" is
  "\<lambda>cs T. if distinct cs then (cs, Set.filter (wf_tuple cs) T) else ([], {})"
  by (auto simp: table_def)

lemma wf_table_sig_of_set: "distinct cs \<Longrightarrow> wf_table_sig (wf_table_of_set cs T) = cs"
  by transfer auto

lemma wf_table_set_of_set: "distinct cs \<Longrightarrow> wf_table_set (wf_table_of_set cs T) = Set.filter (wf_tuple cs) T"
  by transfer auto

lift_definition wf_table_union :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, T) (ds, T'). if cs = ds then (cs, T \<union> T') else (cs, T)"
  by auto

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

lift_definition wf_table_join :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, T) (ds, T'). (cols_union cs ds, bin_join cs T True ds T')"
  by (fastforce simp del: bin_join.simps simp: bin_join_table intro: join_table)

lemma wf_table_sig_join: "wf_table_sig (wf_table_join t1 t2) = cols_union (wf_table_sig t1) (wf_table_sig t2)"
  by transfer auto

lemma wf_table_set_join: "wf_table_set (wf_table_join t1 t2) =
  join (wf_table_sig t1) (wf_table_set t1) True (wf_table_sig t2) (wf_table_set t2)"
  by transfer (auto simp del: bin_join.simps simp: bin_join_table)

text \<open>The antijoin requires the second table's columns to be among the first's.\<close>

lift_definition wf_table_antijoin :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, T) (ds, T'). if set ds \<subseteq> set cs then (cs, bin_join cs T False ds T') else (cs, T)"
  by (fastforce simp del: bin_join.simps simp: bin_join_table cols_union_subset intro: join_table)

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

subsection \<open>Indexes\<close>

text \<open>An index over the columns @{term cs} with the key columns @{term I} maps each key to the
  nonempty cluster of the tuples with that key.\<close>

definition idx_wf :: "nat list \<Rightarrow> nat list \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> bool" where
  "idx_wf cs I T \<longleftrightarrow> (\<forall>x Y. Mapping.lookup T x = Some Y \<longrightarrow>
    table cs Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I cs z))"

lemma idx_wfD:
  assumes "idx_wf cs I T" "Mapping.lookup T x = Some Y"
  shows "table cs Y" "Y \<noteq> {}" "z \<in> Y \<Longrightarrow> x = restrict I cs z"
  using assms by (auto simp: idx_wf_def)

lemma idx_wfI:
  "(\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table cs Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I cs z)) \<Longrightarrow>
  idx_wf cs I T"
  by (auto simp: idx_wf_def)

lemma idx_wf_table: "idx_wf cs I T \<Longrightarrow> table cs (set_of_idx T)"
  by (auto simp: table_def mem_set_of_idx idx_wf_def)

text \<open>A tuple of the index is in the cluster of its key.\<close>

lemma idx_wf_lookup:
  assumes "idx_wf cs I T" "z \<in> set_of_idx T"
  obtains Y where "Mapping.lookup T (restrict I cs z) = Some Y" "z \<in> Y"
  using assms by (auto simp: mem_set_of_idx dest: idx_wfD(3))

definition idx_create :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> ('a tuple, 'a table) mapping" where
  "idx_create cs I T = cluster (Some \<circ> restrict I cs) T"

lemma idx_create:
  assumes "table cs T"
  shows "set_of_idx (idx_create cs I T) = T" "idx_wf cs I (idx_create cs I T)"
proof -
  show "set_of_idx (idx_create cs I T) = T"
    by (auto simp: mem_set_of_idx idx_create_def lookup_cluster image_iff split: if_splits) blast
  show "idx_wf cs I (idx_create cs I T)"
    using assms by (auto simp: idx_wf_def idx_create_def lookup_cluster table_def split: if_splits)
qed

definition idx_reindex :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow>
  ('a tuple, 'a table) mapping" where
  "idx_reindex cs I' I T = (if I = I' then T else idx_create cs I' (set_of_idx T))"

lemma idx_reindex:
  assumes "idx_wf cs I T"
  shows "set_of_idx (idx_reindex cs I' I T) = set_of_idx T" "idx_wf cs I' (idx_reindex cs I' I T)"
  using assms idx_create[OF idx_wf_table[OF assms]]
  by (auto simp: idx_reindex_def)

definition "idx_union = Mapping.combine (\<union>)"

lemma idx_union:
  assumes "idx_wf cs I T" "idx_wf cs I T'"
  shows "set_of_idx (idx_union T T') = set_of_idx T \<union> set_of_idx T'" "idx_wf cs I (idx_union T T')"
proof -
  show "set_of_idx (idx_union T T') = set_of_idx T \<union> set_of_idx T'"
  proof (rule set_eqI, rule iffI)
    fix z
    assume "z \<in> set_of_idx (idx_union T T')"
    then obtain x Y where "combine_options (\<union>) (Mapping.lookup T x) (Mapping.lookup T' x) = Some Y" "z \<in> Y"
      by (auto simp: mem_set_of_idx idx_union_def Mapping.lookup_combine)
    then show "z \<in> set_of_idx T \<union> set_of_idx T'"
      by (cases "Mapping.lookup T x"; cases "Mapping.lookup T' x") (auto simp: mem_set_of_idx)
  next
    fix z
    assume "z \<in> set_of_idx T \<union> set_of_idx T'"
    then obtain x Y where "Mapping.lookup T x = Some Y \<or> Mapping.lookup T' x = Some Y" "z \<in> Y"
      by (auto simp: mem_set_of_idx)
    then show "z \<in> set_of_idx (idx_union T T')"
      by (cases "Mapping.lookup T x"; cases "Mapping.lookup T' x")
        (auto simp: mem_set_of_idx idx_union_def Mapping.lookup_combine intro!: exI[of _ x])
  qed
  show "idx_wf cs I (idx_union T T')"
    using assms by (auto simp: idx_wf_def idx_union_def Mapping.lookup_combine combine_options_def
      split: option.splits)
qed

text \<open>Two indexes on the same key columns are joined cluster by cluster: the tuples of a join
  have the same key in both operands.\<close>

definition "idx_join cs T ds T' =
  Mapping.filter (\<lambda>_ Y. Y \<noteq> {}) (mapping_join (\<lambda>Y Y'. bin_join cs Y True ds Y') T T')"

lemma idx_join:
  fixes T T' :: "('a tuple, 'a table) mapping"
  assumes "distinct cs" "distinct ds" "set I \<subseteq> set cs" "set I \<subseteq> set ds" "idx_wf cs I T" "idx_wf ds I T'"
  shows "set_of_idx (idx_join cs T ds T') = join cs (set_of_idx T) True ds (set_of_idx T')"
    "idx_wf (cols_union cs ds) I (idx_join cs T ds T')"
proof -
  let ?es = "cols_union cs ds"
  have lookup: "Mapping.lookup (idx_join cs T ds T') x =
    (case Mapping.lookup T x of None \<Rightarrow> None | Some Y \<Rightarrow> (case Mapping.lookup T' x of None \<Rightarrow> None
     | Some Y' \<Rightarrow> if join cs Y True ds Y' \<noteq> {} then Some (join cs Y True ds Y') else None))" for x
    using idx_wfD(1)[OF assms(5)] idx_wfD(1)[OF assms(6)]
    by (auto simp: idx_join_def Mapping.lookup_filter lookup_mapping_join bin_join_table[OF assms(1,2)]
      simp del: bin_join.simps split: option.splits)
  have key: "restrict I cs (restrict cs ?es z) = restrict I ?es z"
    "restrict I ds (restrict ds ?es z) = restrict I ?es z" for z :: "'a tuple"
    using assms(3,4) by (simp_all add: restrict_restrict)
  show "set_of_idx (idx_join cs T ds T') = join cs (set_of_idx T) True ds (set_of_idx T')"
  proof (rule set_eqI, rule iffI)
    fix z
    assume "z \<in> set_of_idx (idx_join cs T ds T')"
    then obtain x Z where xZ: "Mapping.lookup (idx_join cs T ds T') x = Some Z" "z \<in> Z"
      by (auto simp: mem_set_of_idx)
    then obtain Y Y' where Y: "Mapping.lookup T x = Some Y" "Mapping.lookup T' x = Some Y'"
      and "Z = join cs Y True ds Y'"
      by (cases "Mapping.lookup T x"; cases "Mapping.lookup T' x") (auto simp: lookup split: if_splits)
    with xZ(2) have z: "z \<in> join cs Y True ds Y'"
      by simp
    have "Y \<subseteq> set_of_idx T" "Y' \<subseteq> set_of_idx T'"
      using Y by (auto simp: mem_set_of_idx intro!: exI[of _ x])
    with z show "z \<in> join cs (set_of_idx T) True ds (set_of_idx T')"
      by (auto simp: join_True_iff[OF assms(1,2) idx_wfD(1)[OF assms(5) Y(1)] idx_wfD(1)[OF assms(6) Y(2)]]
        join_True_iff[OF assms(1,2) idx_wf_table[OF assms(5)] idx_wf_table[OF assms(6)]])
  next
    fix z
    assume "z \<in> join cs (set_of_idx T) True ds (set_of_idx T')"
    then have z: "wf_tuple ?es z" "restrict cs ?es z \<in> set_of_idx T" "restrict ds ?es z \<in> set_of_idx T'"
      by (simp_all add: join_True_iff[OF assms(1,2) idx_wf_table[OF assms(5)] idx_wf_table[OF assms(6)]])
    obtain Y where Y: "Mapping.lookup T (restrict I ?es z) = Some Y" "restrict cs ?es z \<in> Y"
      using idx_wf_lookup[OF assms(5) z(2)] by (auto simp: key)
    obtain Y' where Y': "Mapping.lookup T' (restrict I ?es z) = Some Y'" "restrict ds ?es z \<in> Y'"
      using idx_wf_lookup[OF assms(6) z(3)] by (auto simp: key)
    have "z \<in> join cs Y True ds Y'"
      using z(1) Y(2) Y'(2)
      by (simp add: join_True_iff[OF assms(1,2) idx_wfD(1)[OF assms(5) Y(1)] idx_wfD(1)[OF assms(6) Y'(1)]])
    then show "z \<in> set_of_idx (idx_join cs T ds T')"
      using Y(1) Y'(1) by (auto simp: mem_set_of_idx lookup intro!: exI[of _ "restrict I ?es z"])
  qed
  show "idx_wf ?es I (idx_join cs T ds T')"
  proof (rule idx_wfI)
    fix x Z
    assume "Mapping.lookup (idx_join cs T ds T') x = Some Z"
    then obtain Y Y' where Y: "Mapping.lookup T x = Some Y" "Mapping.lookup T' x = Some Y'"
      and Z: "Z = join cs Y True ds Y'" "Z \<noteq> {}"
      by (auto simp: lookup split: option.splits if_splits)
    have tabs: "table cs Y" "table ds Y'"
      using idx_wfD(1) assms(5,6) Y by blast+
    have "table ?es Z"
      unfolding Z(1) by (rule join_table[OF tabs]) auto
    moreover have "x = restrict I ?es z" if "z \<in> Z" for z
    proof -
      have "restrict cs ?es z \<in> Y"
        using that by (simp add: Z(1) join_True_iff[OF assms(1,2) tabs])
      then show ?thesis
        using idx_wfD(3)[OF assms(5) Y(1)] key(1) by metis
    qed
    ultimately show "table ?es Z \<and> Z \<noteq> {} \<and> (\<forall>z \<in> Z. x = restrict I ?es z)"
      using Z(2) by blast
  qed
qed
text \<open>The antijoin keeps the clusters of the first index that the second does not have, and
  antijoins the others.\<close>

definition "idx_antijoin cs T ds T' = Mapping.combine (\<union>) (mapping_antijoin T T')
  (Mapping.filter (\<lambda>_ Y. Y \<noteq> {}) (mapping_join (\<lambda>Y Y'. bin_join cs Y False ds Y') T T'))"

lemma idx_antijoin:
  fixes T T' :: "('a tuple, 'a table) mapping"
  assumes "distinct cs" "distinct ds" "set I \<subseteq> set ds" "set ds \<subseteq> set cs" "idx_wf cs I T" "idx_wf ds I T'"
  shows "set_of_idx (idx_antijoin cs T ds T') = join cs (set_of_idx T) False ds (set_of_idx T')"
    "idx_wf cs I (idx_antijoin cs T ds T')"
proof -
  have lookup: "Mapping.lookup (idx_antijoin cs T ds T') x =
    (case Mapping.lookup T x of None \<Rightarrow> None | Some Y \<Rightarrow> (case Mapping.lookup T' x of None \<Rightarrow> Some Y
     | Some Y' \<Rightarrow> if join cs Y False ds Y' \<noteq> {} then Some (join cs Y False ds Y') else None))" for x
    using idx_wfD(1)[OF assms(5)] idx_wfD(1)[OF assms(6)]
    by (auto simp: idx_antijoin_def Mapping.lookup_combine Mapping.lookup_filter lookup_mapping_join
      lookup_mapping_antijoin bin_join_table[OF assms(1,2)] simp del: bin_join.simps split: option.splits)
  have key: "restrict I ds (restrict ds cs z) = restrict I cs z" for z :: "'a tuple"
    using assms(3) by (simp add: restrict_restrict)
  note antijoin = join_False_iff[OF assms(1,2) _ _ assms(4)]
  \<comment> \<open>the tuples of @{term T'} that match a tuple are in the cluster of its key\<close>
  have T'_mem: "restrict ds cs z \<in> set_of_idx T' \<longleftrightarrow>
    (\<exists>Y'. Mapping.lookup T' (restrict I cs z) = Some Y' \<and> restrict ds cs z \<in> Y')" for z
    using idx_wf_lookup[OF assms(6), of "restrict ds cs z"] by (auto simp: key mem_set_of_idx)
  show "set_of_idx (idx_antijoin cs T ds T') = join cs (set_of_idx T) False ds (set_of_idx T')"
  proof (rule set_eqI, rule iffI)
    fix z
    assume "z \<in> set_of_idx (idx_antijoin cs T ds T')"
    then obtain x Z where xZ: "Mapping.lookup (idx_antijoin cs T ds T') x = Some Z" "z \<in> Z"
      by (auto simp: mem_set_of_idx)
    then obtain Y where Y: "Mapping.lookup T x = Some Y" "z \<in> Y"
      and Y': "\<And>Y'. Mapping.lookup T' x = Some Y' \<Longrightarrow> restrict ds cs z \<notin> Y'"
      using idx_wfD(1)[OF assms(5)] idx_wfD(1)[OF assms(6)]
      by (cases "Mapping.lookup T x"; cases "Mapping.lookup T' x") (auto simp: lookup antijoin split: if_splits)
    have "x = restrict I cs z"
      using idx_wfD(3)[OF assms(5) Y] .
    then have "restrict ds cs z \<notin> set_of_idx T'"
      using Y' by (auto simp: T'_mem)
    moreover have "z \<in> set_of_idx T"
      using Y by (auto simp: mem_set_of_idx intro!: exI[of _ x])
    ultimately show "z \<in> join cs (set_of_idx T) False ds (set_of_idx T')"
      by (simp add: antijoin[OF idx_wf_table[OF assms(5)] idx_wf_table[OF assms(6)]])
  next
    fix z
    assume "z \<in> join cs (set_of_idx T) False ds (set_of_idx T')"
    then have z: "z \<in> set_of_idx T" "restrict ds cs z \<notin> set_of_idx T'"
      by (simp_all add: antijoin[OF idx_wf_table[OF assms(5)] idx_wf_table[OF assms(6)]])
    obtain Y where Y: "Mapping.lookup T (restrict I cs z) = Some Y" "z \<in> Y"
      using idx_wf_lookup[OF assms(5) z(1)] .
    show "z \<in> set_of_idx (idx_antijoin cs T ds T')"
    proof (cases "Mapping.lookup T' (restrict I cs z)")
      case None
      then show ?thesis
        using Y by (auto simp: mem_set_of_idx lookup intro!: exI[of _ "restrict I cs z"])
    next
      case (Some Y')
      then have "z \<in> join cs Y False ds Y'"
        using Y(2) z(2) idx_wfD(1)[OF assms(5) Y(1)] idx_wfD(1)[OF assms(6) Some]
        by (auto simp: antijoin T'_mem)
      then show ?thesis
        using Y(1) Some by (auto simp: mem_set_of_idx lookup intro!: exI[of _ "restrict I cs z"])
    qed
  qed
  show "idx_wf cs I (idx_antijoin cs T ds T')"
  proof (rule idx_wfI)
    fix x Z
    assume "Mapping.lookup (idx_antijoin cs T ds T') x = Some Z"
    then obtain Y where Y: "Mapping.lookup T x = Some Y" and Z: "Z \<subseteq> Y" "Z \<noteq> {}"
      using idx_wfD(2)[OF assms(5)]
      by (cases "Mapping.lookup T x"; cases "Mapping.lookup T' x")
        (auto simp: lookup join_False_code split: if_splits)
    then show "table cs Z \<and> Z \<noteq> {} \<and> (\<forall>z \<in> Z. x = restrict I cs z)"
      using idx_wfD(1,3)[OF assms(5) Y] by (auto intro: table_subset)
  qed
qed

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

subsection \<open>Indexed tables\<close>

typedef 'a wf_idx = "{(cs :: nat list, I :: nat list, T :: ('a tuple, 'a table) mapping) | cs I T.
  distinct cs \<and> set I \<subseteq> set cs \<and> idx_wf cs I T}"
  by (rule exI[of _ "([], [], Mapping.empty)"]) (auto simp: idx_wf_def)

setup_lifting type_definition_wf_idx

lift_definition wf_idx_sig :: "'a wf_idx \<Rightarrow> nat list" is "\<lambda>(cs, I, T). cs" .

lift_definition wf_idx_cols :: "'a wf_idx \<Rightarrow> nat list" is "\<lambda>(cs, I, T). I" .

lift_definition wf_idx_set :: "'a wf_idx \<Rightarrow> 'a table" is "\<lambda>(cs, I, T). set_of_idx T" .

lift_definition wf_table_of_idx :: "'a wf_idx \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, I, T). (cs, set_of_idx T)"
  by (auto intro: idx_wf_table)

lemma wf_table_sig_of_idx[simp]: "wf_table_sig (wf_table_of_idx t) = wf_idx_sig t"
  by transfer auto

lemma wf_table_set_of_idx[simp]: "wf_table_set (wf_table_of_idx t) = wf_idx_set t"
  by transfer auto

lemma idx_wf_empty[simp]: "idx_wf cs I Mapping.empty"
  by (simp add: idx_wf_def)

lift_definition wf_idx_of_set :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> 'a wf_idx" is
  "\<lambda>cs I T. if distinct cs then let I' = filter (\<lambda>c. c \<in> set cs) I in
    (cs, I', idx_create cs I' (Set.filter (wf_tuple cs) T)) else ([], [], Mapping.empty)"
  by (auto simp: Let_def idx_create(2)[OF table_filter])

lemma wf_idx_sig_of_set: "distinct cs \<Longrightarrow> wf_idx_sig (wf_idx_of_set cs I T) = cs"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_of_set: "distinct cs \<Longrightarrow> wf_idx_set (wf_idx_of_set cs I T) = Set.filter (wf_tuple cs) T"
  by transfer (auto simp: Let_def idx_create(1)[OF table_filter])

text \<open>The binary operations bring both indexes to the key columns they share, in the order of
  the first index.\<close>

lift_definition wf_idx_union :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) (ds, I', T'). if cs = ds then
    (let I'' = filter (\<lambda>c. c \<in> set I') I in
      (cs, I'', idx_union (idx_reindex cs I'' I T) (idx_reindex cs I'' I' T')))
  else (cs, I, T)"
  by (auto simp: Let_def idx_union(2) idx_reindex(2))

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

lift_definition wf_idx_join :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) (ds, I', T'). let I'' = filter (\<lambda>c. c \<in> set I') I in
    (cols_union cs ds, I'', idx_join cs (idx_reindex cs I'' I T) ds (idx_reindex ds I'' I' T'))"
  by (auto 0 3 simp: Let_def intro!: idx_join(2) idx_reindex(2))

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

lift_definition wf_idx_antijoin :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) (ds, I', T'). if set ds \<subseteq> set cs then
    (let I'' = filter (\<lambda>c. c \<in> set I') I in
      if I'' = ds then (cs, I'', mapping_antijoin (idx_reindex cs I'' I T) (idx_reindex ds I'' I' T'))
      else (cs, I'', idx_antijoin cs (idx_reindex cs I'' I T) ds (idx_reindex ds I'' I' T')))
  else (cs, I, T)"
  by (auto 0 3 simp: Let_def intro!: idx_antijoin(2) mapping_antijoin_idx(2) idx_reindex(2))

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
subsection \<open>Plain tables\<close>

typedef 'a wf_set = "{(cs :: nat list, T :: 'a table) | cs T. distinct cs \<and> table cs T}"
  by (rule exI[of _ "([], {})"]) auto

setup_lifting type_definition_wf_set

lift_definition wf_set_sig :: "'a wf_set \<Rightarrow> nat list" is fst .

lift_definition wf_set_set :: "'a wf_set \<Rightarrow> 'a table" is snd .

lift_definition wf_table_of_wf_set :: "'a wf_set \<Rightarrow> 'a wf_table" is "\<lambda>t. t" .

lemma wf_set_sig[simp]: "wf_table_sig (wf_table_of_wf_set t) = wf_set_sig t"
  by transfer auto

lemma wf_set_set[simp]: "wf_table_set (wf_table_of_wf_set t) = wf_set_set t"
  by transfer auto

lift_definition wf_set_of_set :: "nat list \<Rightarrow> 'a table \<Rightarrow> 'a wf_set" is
  "\<lambda>cs T. if distinct cs then (cs, Set.filter (wf_tuple cs) T) else ([], {})"
  by (auto simp: table_def)

lift_definition wf_set_union :: "'a wf_set \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_set" is
  "\<lambda>(cs, T) (ds, T'). if cs = ds then (cs, T \<union> T') else (cs, T)"
  by auto

lift_definition wf_set_join :: "'a wf_set \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_set" is
  "\<lambda>(cs, T) (ds, T'). (cols_union cs ds, bin_join cs T True ds T')"
  by (fastforce simp del: bin_join.simps simp: bin_join_table intro: join_table)

lift_definition wf_set_antijoin :: "'a wf_set \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_set" is
  "\<lambda>(cs, T) (ds, T'). if set ds \<subseteq> set cs then (cs, bin_join cs T False ds T') else (cs, T)"
  by (fastforce simp del: bin_join.simps simp: bin_join_table cols_union_subset intro: join_table)

lift_definition wf_idx_of_wf_set :: "nat list \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_idx" is
  "\<lambda>I (cs, T). let I' = filter (\<lambda>c. c \<in> set cs) I in (cs, I', idx_create cs I' T)"
  by (auto simp: Let_def idx_create)

lemma wf_table_of_idx_of_wf_set[simp]: "wf_table_of_idx (wf_idx_of_wf_set I t) = wf_table_of_wf_set t"
  by (rule wf_table_eqI; transfer) (auto simp: Let_def idx_create(1))

text \<open>The operations on the two representations.\<close>

lemma wf_table_of_wf_set_of_set: "wf_table_of_set cs T = wf_table_of_wf_set (wf_set_of_set cs T)"
  by transfer auto

lemma wf_table_union_wf_set: "wf_table_union (wf_table_of_wf_set t) (wf_table_of_wf_set t') =
  wf_table_of_wf_set (wf_set_union t t')"
  by transfer auto

lemma wf_table_join_wf_set: "wf_table_join (wf_table_of_wf_set t) (wf_table_of_wf_set t') =
  wf_table_of_wf_set (wf_set_join t t')"
  by transfer auto

lemma wf_table_antijoin_wf_set: "wf_table_antijoin (wf_table_of_wf_set t) (wf_table_of_wf_set t') =
  wf_table_of_wf_set (wf_set_antijoin t t')"
  by transfer auto

lemma wf_table_union_idx: "wf_table_union (wf_table_of_idx i) (wf_table_of_idx i') =
  wf_table_of_idx (wf_idx_union i i')"
  by (rule wf_table_eqI)
    (simp_all add: wf_table_sig_union wf_idx_sig_union wf_table_set_union' wf_idx_set_union')

lemma wf_table_join_idx: "wf_table_join (wf_table_of_idx i) (wf_table_of_idx i') =
  wf_table_of_idx (wf_idx_join i i')"
  by (rule wf_table_eqI) (simp_all add: wf_table_sig_join wf_idx_sig_join wf_table_set_join wf_idx_set_join)

lemma wf_table_antijoin_idx: "wf_table_antijoin (wf_table_of_idx i) (wf_table_of_idx i') =
  wf_table_of_idx (wf_idx_antijoin i i')"
  by (rule wf_table_eqI)
    (simp_all add: wf_table_sig_antijoin wf_idx_sig_antijoin wf_table_set_antijoin' wf_idx_set_antijoin
      wf_idx_set_antijoin_deg)

subsection \<open>Code setup\<close>

code_datatype wf_table_of_wf_set wf_table_of_idx

lemmas wf_table_sig_code[code] = wf_table_sig_of_idx wf_set_sig
lemmas wf_table_set_code[code] = wf_table_set_of_idx wf_set_set
lemmas wf_table_of_set_code[code] = wf_table_of_wf_set_of_set

lemma wf_table_union_code[code]:
  "wf_table_union (wf_table_of_idx i) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_union i i')"
  "wf_table_union (wf_table_of_idx i) (wf_table_of_wf_set t') =
    wf_table_of_idx (wf_idx_union i (wf_idx_of_wf_set (wf_idx_cols i) t'))"
  "wf_table_union (wf_table_of_wf_set t) (wf_table_of_wf_set t') = wf_table_of_wf_set (wf_set_union t t')"
  "wf_table_union (wf_table_of_wf_set t) (wf_table_of_idx i') =
    wf_table_of_idx (wf_idx_union (wf_idx_of_wf_set (wf_idx_cols i') t) i')"
  by (simp_all flip: wf_table_union_idx add: wf_table_union_wf_set)

lemma wf_table_join_code[code]:
  "wf_table_join (wf_table_of_idx i) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_join i i')"
  "wf_table_join (wf_table_of_idx i) (wf_table_of_wf_set t') =
    wf_table_of_idx (wf_idx_join i (wf_idx_of_wf_set (wf_idx_cols i) t'))"
  "wf_table_join (wf_table_of_wf_set t) (wf_table_of_wf_set t') = wf_table_of_wf_set (wf_set_join t t')"
  "wf_table_join (wf_table_of_wf_set t) (wf_table_of_idx i') =
    wf_table_of_idx (wf_idx_join (wf_idx_of_wf_set (wf_idx_cols i') t) i')"
  by (simp_all flip: wf_table_join_idx add: wf_table_join_wf_set)

lemma wf_table_antijoin_code[code]:
  "wf_table_antijoin (wf_table_of_idx i) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_antijoin i i')"
  "wf_table_antijoin (wf_table_of_idx i) (wf_table_of_wf_set t') =
    wf_table_of_idx (wf_idx_antijoin i (wf_idx_of_wf_set (wf_idx_cols i) t'))"
  "wf_table_antijoin (wf_table_of_wf_set t) (wf_table_of_wf_set t') =
    wf_table_of_wf_set (wf_set_antijoin t t')"
  "wf_table_antijoin (wf_table_of_wf_set t) (wf_table_of_idx i') =
    wf_table_of_idx (wf_idx_antijoin (wf_idx_of_wf_set (wf_idx_cols i') t) i')"
  by (simp_all flip: wf_table_antijoin_idx add: wf_table_antijoin_wf_set)

end
