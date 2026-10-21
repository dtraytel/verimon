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

lift_definition wf_table_of_set :: "nat list \<Rightarrow> 'a table \<Rightarrow> 'a wf_table" is
  "\<lambda>cs T. if distinct cs then (cs, Set.filter (wf_tuple cs) T) else ([], {})"
  by (auto simp: table_def)

lift_definition wf_table_union :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, T) (ds, T'). if cs = ds then (cs, T \<union> T') else (cs, T)"
  by auto

lift_definition wf_table_join :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, T) (ds, T'). (cols_union cs ds, bin_join cs T True ds T')"
  by (fastforce simp del: bin_join.simps simp: bin_join_table intro: join_table)

text \<open>The antijoin requires the second table's columns to be among the first's.\<close>

lift_definition wf_table_antijoin :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, T) (ds, T'). if set ds \<subseteq> set cs then (cs, bin_join cs T False ds T') else (cs, T)"
  by (fastforce simp del: bin_join.simps simp: bin_join_table cols_union_subset intro: join_table)

subsection \<open>Indexes\<close>

text \<open>An index over the columns @{term cs} with the key columns @{term I} maps each key to the
  nonempty cluster of the tuples with that key.\<close>

definition idx_wf :: "nat list \<Rightarrow> nat list \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> bool" where
  "idx_wf cs I T \<longleftrightarrow> (\<forall>x Y. Mapping.lookup T x = Some Y \<longrightarrow>
    table cs Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I cs z))"

definition idx_create :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> ('a tuple, 'a table) mapping" where
  "idx_create cs I T = cluster (Some \<circ> restrict I cs) T"

definition idx_reindex :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow>
  ('a tuple, 'a table) mapping" where
  "idx_reindex cs I' I T = (if I = I' then T else idx_create cs I' (set_of_idx T))"

definition "idx_union = Mapping.combine (\<union>)"

text \<open>Two indexes on the same key columns are joined cluster by cluster: the tuples of a join
  have the same key in both operands.\<close>

definition "idx_join cs T ds T' =
  Mapping.filter (\<lambda>_ Y. Y \<noteq> {}) (mapping_join (\<lambda>Y Y'. bin_join cs Y True ds Y') T T')"

text \<open>The antijoin keeps the clusters of the first index that the second does not have, and
  antijoins the others.\<close>

definition "idx_antijoin cs T ds T' = Mapping.combine (\<union>) (mapping_antijoin T T')
  (Mapping.filter (\<lambda>_ Y. Y \<noteq> {}) (mapping_join (\<lambda>Y Y'. bin_join cs Y False ds Y') T T'))"

subsection \<open>Indexed tables\<close>

typedef 'a wf_idx = "{(cs :: nat list, I :: nat list, T :: ('a tuple, 'a table) mapping) | cs I T.
  distinct cs \<and> set I \<subseteq> set cs \<and> idx_wf cs I T}"
  by (rule exI[of _ "([], [], Mapping.empty)"]) (auto simp: idx_wf_def)

setup_lifting type_definition_wf_idx

lift_definition wf_idx_sig :: "'a wf_idx \<Rightarrow> nat list" is "\<lambda>(cs, I, T). cs" .

lift_definition wf_idx_cols :: "'a wf_idx \<Rightarrow> nat list" is "\<lambda>(cs, I, T). I" .

lift_definition wf_idx_set :: "'a wf_idx \<Rightarrow> 'a table" is "\<lambda>(cs, I, T). set_of_idx T" .

lift_definition wf_idx_of_table :: "nat list \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_idx" is
  "\<lambda>I (cs, T). let I' = filter (\<lambda>c. c \<in> set cs) I in (cs, I', idx_create cs I' T)"
  by (auto simp: Let_def idx_create)

lift_definition wf_table_of_idx :: "'a wf_idx \<Rightarrow> 'a wf_table" is
  "\<lambda>(cs, I, T). (cs, set_of_idx T)"
  by (auto intro: idx_wf_table)

lift_definition wf_idx_of_set :: "nat list \<Rightarrow> nat list \<Rightarrow> 'a table \<Rightarrow> 'a wf_idx" is
  "\<lambda>cs I T. if distinct cs then let I' = filter (\<lambda>c. c \<in> set cs) I in
    (cs, I', idx_create cs I' (Set.filter (wf_tuple cs) T)) else ([], [], Mapping.empty)"
  by (auto simp: Let_def idx_create(2)[OF table_filter])

lift_definition wf_idx_reindex :: "nat list \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>I' (cs, I, T). let I'' = filter (\<lambda>c. c \<in> set I') I in (cs, I'', idx_reindex cs I'' I T)"
  by (auto simp: Let_def idx_reindex(2))

text \<open>The binary operations bring both indexes to the key columns they share, in the order of
  the first index.\<close>

lift_definition wf_idx_union :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) (ds, I', T'). if cs = ds then
    (let I'' = filter (\<lambda>c. c \<in> set I') I in
      (cs, I'', idx_union (idx_reindex cs I'' I T) (idx_reindex cs I'' I' T')))
  else (cs, I, T)"
  by (auto simp: Let_def idx_union(2) idx_reindex(2))

lift_definition wf_idx_join :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) (ds, I', T'). let I'' = filter (\<lambda>c. c \<in> set I') I in
    (cols_union cs ds, I'', idx_join cs (idx_reindex cs I'' I T) ds (idx_reindex ds I'' I' T'))"
  by (auto 0 3 simp: Let_def intro!: idx_join(2) idx_reindex(2))

lift_definition wf_idx_antijoin :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(cs, I, T) (ds, I', T'). if set ds \<subseteq> set cs then
    (let I'' = filter (\<lambda>c. c \<in> set I') I in
      if I'' = ds then (cs, I'', mapping_antijoin (idx_reindex cs I'' I T) (idx_reindex ds I'' I' T'))
      else (cs, I'', idx_antijoin cs (idx_reindex cs I'' I T) ds (idx_reindex ds I'' I' T')))
  else (cs, I, T)"
  by (auto 0 3 simp: Let_def intro!: idx_antijoin(2) mapping_antijoin_idx(2) idx_reindex(2))

subsection \<open>Plain tables\<close>

typedef 'a wf_set = "{(cs :: nat list, T :: 'a table) | cs T. distinct cs \<and> table cs T}"
  by (rule exI[of _ "([], {})"]) auto

setup_lifting type_definition_wf_set

lift_definition wf_set_sig :: "'a wf_set \<Rightarrow> nat list" is fst .

lift_definition wf_set_set :: "'a wf_set \<Rightarrow> 'a table" is snd .

lift_definition wf_table_of_wf_set :: "'a wf_set \<Rightarrow> 'a wf_table" is "\<lambda>t. t" .

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

lift_definition wf_set_of_idx :: "'a wf_idx \<Rightarrow> 'a wf_set" is
  "\<lambda>(cs, I, T). (cs, set_of_idx T)"
  by (auto intro: idx_wf_table)

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
