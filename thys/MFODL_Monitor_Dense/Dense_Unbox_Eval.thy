(*<*)
theory Dense_Unbox_Eval
  imports Dense_Exec Dense_Unbox
begin
(*>*)

section \<open>The verified dense evaluator, without the option\<close>

text \<open>
  @{const edeval} of @{theory MFODL_Monitor_Dense.Dense_Exec} is the verified dense evaluator with
  its buffers in queues; its tables are the kernel's, @{typ "event_data option list set"}, and a
  dense tuple never has a hole.  This theory states the evaluator once more over
  @{typ "event_data list set"} and proves that on a formula whose tables are the short ones with
  the option put back, @{const edeval} computes what the short evaluator computes with the option
  put back.  The proof is a naturality argument, node by node: every operation the evaluator
  runs commutes with @{const reopt_table}.  The operations that read a field are
  @{theory MFODL_Monitor_Dense.Dense_Utuple}'s twins read through @{const deopt}, so for them the
  commutation is by definition; the ones that move fields are the generic ones of
  @{theory MFODL_Monitor_Dense.Dense_Unbox} and @{theory MFODL_Monitor_Dense.Dense_Until_Gen}, whose
  commutation is proved here from that of the containers they are built from.  No invariant is
  needed: the operations were stated in @{theory MFODL_Monitor_Dense.Dense_Utuple} and
  @{theory MFODL_Monitor_Dense.Dense_Until_Gen} precisely so that the commutation holds on every
  input.
\<close>

subsection \<open>Short tuples and tables\<close>

text \<open>The queue scans are unfolded by hand where a proof needs it; left to the simplifier they
  would unfold before their commutation lemmas could apply.\<close>

declare dropWhile_queue.simps[simp del] takeWhile_queue.simps[simp del]
  takedropWhile_queue.simps[simp del]

lemma dproj_reopt[simp]: "dproj msk (reopt x) = reopt (dproj msk x)"
  by (induct msk x rule: dproj.induct) auto

lemma dmerge_reopt[simp]: "dmerge p (reopt x) (reopt y) = reopt (dmerge p x y)"
  by (induct p x y rule: dmerge.induct) auto

lemma dtabc_reopt_table[simp]: "dtabc n cs (reopt_table X) = reopt_table (dtabc n cs X)"
  by (simp add: dtabc_def reopt_table_def image_image)

lemma dsemi_reopt_table[simp]:
  "dsemi msk pos (reopt_table A) (reopt_table B) = reopt_table (dsemi msk pos A B)"
  by (auto simp: dsemi_def reopt_table_def image_iff)

lemma reopt_table_image_dproj[simp]:
  "dproj msk ` reopt_table X = reopt_table (dproj msk ` X)"
  by (simp add: reopt_table_def image_image)

lemma reopt_table_tl[simp]: "tl ` reopt_table X = reopt_table (tl ` X)"
  by (simp add: reopt_table_def image_image)

lemma reopt_table_UN[simp]: "\<Union> (reopt_table ` S) = reopt_table (\<Union> S)"
  by (auto simp: reopt_table_def)

text \<open>The sorted list of a table: the option is compared field by field, so the two orders agree
  and the sorted list of the table with the option put back is the sorted list with the option
  put back.\<close>

lemma comparator_list_option_reopt:
  "comparator_list (comparator_option c) (reopt x) (reopt y) = comparator_list c x y"
  by (induct x arbitrary: y) (case_tac y; simp add: reopt_def split: order.splits)+

lemma le_of_comp_list_option_reopt:
  "le_of_comp (comparator_list (comparator_option c)) (reopt x) (reopt y)
   = le_of_comp (comparator_list c) x y"
  by (simp add: le_of_comp_def comparator_list_option_reopt)

lemma ID_ccompare_ed_Some: "\<exists>c. ID CCOMPARE(event_data) = Some c"
  using ID_ccompare_ed by (auto simp: ccompare_list_def ID_def split: option.splits)

lemma csl_reopt_table: "csl (reopt_table (X :: event_data list set)) = map reopt (csl X)"
proof (cases "finite X")
  case False
  then show ?thesis by (simp add: csl_infinite)
next
  case True
  obtain c where c: "ID CCOMPARE(event_data) = Some c" using ID_ccompare_ed_Some by blast
  have c': "CCOMPARE(event_data) = Some c" using c by (simp add: ID_def)
  have cl: "ID CCOMPARE(event_data list) = Some (comparator_list c)"
    and co: "ID CCOMPARE(event_data tuple) = Some (comparator_list (comparator_option c))"
    by (simp_all add: ccompare_list_def ccompare_option_def ID_def c')
  let ?xs = "csorted_list_of_set X"
  have xs1: "set ?xs = X" using True cl by (subst csorted_list_of_set_split) (auto simp: ID_def)
  have xs2: "distinct ?xs" using True cl by (subst csorted_list_of_set_split) (auto simp: ID_def)
  have xs3: "linorder.sorted (le_of_comp (comparator_list c)) ?xs"
    using True cl by (subst csorted_list_of_set_split) (auto simp: ID_def, metis option.sel)
  note xs = xs1 xs2 xs3
  have s: "linorder.sorted (le_of_comp (comparator_list (comparator_option c))) (map reopt ?xs)"
    using xs by (simp add: sorted_wrt_map le_of_comp_list_option_reopt)
  have "csorted_list_of_set (reopt_table X)
      = linorder.sorted_list_of_set (le_of_comp (comparator_list (comparator_option c)))
          (set (map reopt ?xs))"
    using True xs by (simp add: csorted_list_of_set_def co reopt_table_def)
  also have "\<dots> = map reopt ?xs"
    using xs s by (intro csorted_list_of_set_set[OF co]) (simp_all add: distinct_map inj_on_def)
  finally show ?thesis using True by (simp add: csl_finite)
qed

subsection \<open>The containers\<close>

text \<open>Every container the structures hold tuples in gets a map over its elements; the
  operations on it commute with the map, which is what the naturality of the structures'
  operations is assembled from.\<close>

subsubsection \<open>Queue buffers\<close>

lift_definition map_mbuf :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mbuf_t \<Rightarrow> 'b mbuf_t" is map .

lemma Rep_map_mbuf[simp]: "Rep_mbuf_t (map_mbuf f b) = map f (Rep_mbuf_t b)"
  by (simp add: map_mbuf.rep_eq)

lemma map_mbuf_empty[simp]: "map_mbuf f mbuf_t_empty = mbuf_t_empty"
  by transfer simp

lemma map_mbuf_Cons[simp]: "map_mbuf f (x ## b) = f x ## map_mbuf f b"
  by transfer simp

lemma map_mbuf_append[simp]: "map_mbuf f (b @@ xs) = map_mbuf f b @@ map f xs"
  by transfer simp

lemma map_mbuf_is_empty[simp]: "mbuf_t_is_empty (map_mbuf f b) = mbuf_t_is_empty b"
  by transfer simp

lemma mbuf_t_cases_map_mbuf[simp]:
  "mbuf_t_cases (map_mbuf f b) = map_prod (map_option f) (map_mbuf f) (mbuf_t_cases b)"
  by transfer (simp split: list.splits)

lemma map_mbuf_inj: "map_mbuf reopt b = map_mbuf reopt b' \<longleftrightarrow> b = b'"
  by transfer (simp add: inj_map_eq_map inj_reopt)


subsubsection \<open>Deques\<close>

definition map_dq :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dq \<Rightarrow> 'b dq" where
  "map_dq f d = Dq (map f (dq_f d)) (map f (dq_b d)) (dq_nf d) (dq_nb d)"

lemma map_dq_simps[simp]:
  "dq_f (map_dq f d) = map f (dq_f d)" "dq_b (map_dq f d) = map f (dq_b d)"
  "dq_nf (map_dq f d) = dq_nf d" "dq_nb (map_dq f d) = dq_nb d"
  "dq_len (map_dq f d) = dq_len d"
  by (simp_all add: map_dq_def dq_len_def)

lemma map_dq_empty[simp]: "map_dq f dq_empty = dq_empty"
  by (simp add: map_dq_def dq_empty_def)

lemma map_dq_push[simp]: "dq_push (f x) (map_dq f d) = map_dq f (dq_push x d)"
  by (simp add: map_dq_def dq_push_def rev_map)

lemma map_dq_norm[simp]: "dq_norm (map_dq f d) = map_dq f (dq_norm d)"
  by (simp add: map_dq_def dq_norm_def Let_def rev_map drop_map take_map)

lemma map_dq_Dq[simp]: "map_dq f (Dq fs bs nf nb) = Dq (map f fs) (map f bs) nf nb"
  by (simp add: map_dq_def)

lemma map_dq_tl[simp]: "dq_tl (map_dq f d) = map_dq f (dq_tl d)"
proof -
  have "Dq (tl (dq_f (map_dq f d'))) (dq_b (map_dq f d')) (dq_nf (map_dq f d') - 1)
      (dq_nb (map_dq f d')) = map_dq f (Dq (tl (dq_f d')) (dq_b d') (dq_nf d' - 1) (dq_nb d'))"
    for d' by (simp add: map_dq_def map_tl)
  then show ?thesis
    unfolding dq_tl_def Let_def map_dq_norm
    by (simp only: map_dq_simps map_tl map_dq_Dq[symmetric] map_dq_norm)
qed

lemma map_dq_upd[simp]: "dq_upd (map_dq f d) k (f x) = map_dq f (dq_upd d k x)"
  by (simp add: map_dq_def dq_upd_def map_update)

lemma map_dq_nth_s[simp]:
  "dq_inv d \<Longrightarrow> dq_nth_s (map_dq f d) k (f z) = f (dq_nth_s d k z)"
  by (simp add: dq_nth_s_def dq_nth_def dq_len_def dq_inv_def)

lemma map_dq_inj: "map_dq reopt d = map_dq reopt d' \<longleftrightarrow> d = d'"
  by (cases d; cases d') (simp add: map_dq_def inj_map_eq_map inj_reopt)

subsubsection \<open>Mappings keyed by tuples\<close>

text \<open>A mapping keyed by short tuples becomes one keyed by the kernel's tuples: a key with the
  option put back finds its value, and a key with a hole finds nothing.  The values are mapped
  too, since the index mappings hold tables.\<close>

lemma those_reopt[simp]: "those (reopt k) = Some k"
  by (induct k) (auto simp: reopt_def)

lemma those_eq_Some_iff: "those w = Some k \<longleftrightarrow> w = reopt k"
  by (induct w arbitrary: k) (auto simp: reopt_def split: option.splits)

lift_definition rmk :: "('v \<Rightarrow> 'w) \<Rightarrow> (event_data list, 'v) mapping \<Rightarrow>
    (event_data tuple, 'w) mapping" is
  "\<lambda>f m w. case those w of None \<Rightarrow> None | Some k \<Rightarrow> map_option f (m k)" .

lemma lookup_rmk: "Mapping.lookup (rmk f m) w =
    (case those w of None \<Rightarrow> None | Some k \<Rightarrow> map_option f (Mapping.lookup m k))"
  by (simp only: Mapping.lookup.rep_eq rmk.rep_eq)

lemma lookup_rmk_reopt[simp]: "Mapping.lookup (rmk f m) (reopt k) = map_option f (Mapping.lookup m k)"
  by (simp add: lookup_rmk)

lemma rmk_eqI:
  assumes "\<And>k. Mapping.lookup m1 k = Mapping.lookup m2 k"
  shows "rmk f m1 = rmk f m2"
  using assms by (intro mapping_eqI) (simp add: lookup_rmk split: option.splits)

lemma rmk_empty[simp]: "rmk f Mapping.empty = Mapping.empty"
  by transfer (simp add: fun_eq_iff split: option.splits)

lemma rmk_update[simp]: "Mapping.update (reopt k) (f v) (rmk f m) = rmk f (Mapping.update k v m)"
  by (intro mapping_eqI) (auto simp: lookup_rmk Mapping.lookup_update' those_eq_Some_iff split: option.splits)

lemma rmk_update_id[simp]:
  "Mapping.update (reopt k) v (rmk (\<lambda>v. v) m) = rmk (\<lambda>v. v) (Mapping.update k v m)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk Mapping.lookup_update' split: option.splits dest!: those_eq_Some_iff[THEN iffD1])

lemma rmk_update_rt[simp]:
  "Mapping.update (reopt k) (reopt_table v) (rmk reopt_table m)
   = rmk reopt_table (Mapping.update k v m)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk Mapping.lookup_update' split: option.splits dest!: those_eq_Some_iff[THEN iffD1])

lemma rmk_delete[simp]: "Mapping.delete (reopt k) (rmk f m) = rmk f (Mapping.delete k m)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk lookup_delete_if split: option.splits dest!: those_eq_Some_iff[THEN iffD1])

lemma keys_rmk[simp]: "Mapping.keys (rmk f m) = reopt_table (Mapping.keys m)"
  by (auto simp: Mapping.keys_dom_lookup lookup_rmk reopt_table_def those_eq_Some_iff dom_def
      split: option.splits)

lemma rmk_filter[simp]:
  "Mapping.filter P (rmk f m) = rmk f (Mapping.filter (\<lambda>k v. P (reopt k) (f v)) m)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk Mapping.lookup_filter split: option.splits dest!: those_eq_Some_iff[THEN iffD1])

lemma rmk_map_values:
  "(\<And>k v. G (reopt k) (f v) = f' (G' k v)) \<Longrightarrow>
     Mapping.map_values G (rmk f m) = rmk f' (Mapping.map_values G' m)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk Mapping.lookup_map_values option.map_comp comp_def split: option.splits
      dest!: those_eq_Some_iff[THEN iffD1])

lemma rmk_combine:
  "(\<And>a b. g (f a) (f b) = f (g' a b)) \<Longrightarrow>
     Mapping.combine g (rmk f m1) (rmk f m2) = rmk f (Mapping.combine g' m1 m2)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk Mapping.lookup_combine combine_options_def split: option.splits)

lemma rmk_upd_set[simp]:
  "upd_set (rmk f m) (\<lambda>_. f v) (reopt_table X) = rmk f (upd_set m (\<lambda>_. v) X)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk Mapping_lookup_upd_set reopt_table_def split: option.splits
      dest!: those_eq_Some_iff[THEN iffD1])

lemma rmk_mapping_delete_set[simp]:
  "mapping_delete_set (rmk f m) (reopt_table X) = rmk f (mapping_delete_set m X)"
  by (intro mapping_eqI)
    (auto simp: lookup_rmk delete_set_lookup reopt_table_def split: option.splits
      dest!: those_eq_Some_iff[THEN iffD1])

lemma minus_keys_rmk[simp]: "minus_keys (reopt_table X) (rmk f m) = reopt_table (minus_keys X m)"
  by (simp add: minus_keys_def)

lemma rmk_id_inj: "rmk (\<lambda>v. v) m = rmk (\<lambda>v. v) m' \<longleftrightarrow> m = m'"
proof
  assume "rmk (\<lambda>v. v) m = rmk (\<lambda>v. v) m'"
  then have "Mapping.lookup (rmk (\<lambda>v. v) m) (reopt k) = Mapping.lookup (rmk (\<lambda>v. v) m') (reopt k)" for k
    by simp
  then show "m = m'" by (intro mapping_eqI) (simp add: option.map_ident)
qed simp

lemma rmk_reopt_table_inj: "rmk reopt_table m = rmk reopt_table m' \<longleftrightarrow> m = m'"
proof
  assume "rmk reopt_table m = rmk reopt_table m'"
  then have e: "map_option reopt_table (Mapping.lookup m k) = map_option reopt_table (Mapping.lookup m' k)"
    for k by (simp add: lookup_rmk_reopt[symmetric] del: lookup_rmk_reopt)
  show "m = m'"
  proof (intro mapping_eqI)
    fix k show "Mapping.lookup m k = Mapping.lookup m' k"
      using e[of k] by (cases "Mapping.lookup m k"; cases "Mapping.lookup m' k") auto
  qed
qed simp

text \<open>The index algebra of @{theory MFODL_Monitor_Dense.Dense_Aux}.\<close>

lemma cluster_reopt_table:
  "cluster (Some \<circ> dproj msk) (reopt_table X) = rmk reopt_table (cluster (Some \<circ> dproj msk) X)"
proof (intro mapping_eqI)
  fix w
  show "Mapping.lookup (cluster (Some \<circ> dproj msk) (reopt_table X)) w
      = Mapping.lookup (rmk reopt_table (cluster (Some \<circ> dproj msk) X)) w"
  proof (cases "those w")
    case None
    then have "w \<noteq> reopt k" for k using those_eq_Some_iff by (metis option.distinct(1))
    then show ?thesis using None by (auto simp: lookup_cluster lookup_rmk reopt_table_def image_iff)
  next
    case (Some k)
    then have w: "w = reopt k" by (simp add: those_eq_Some_iff)
    show ?thesis unfolding w
      by (auto simp: lookup_cluster reopt_table_def image_iff)
  qed
qed

lemma didx_reopt_table[simp]: "didx msk (reopt_table X) = rmk reopt_table (didx msk X)"
  by (simp add: didx_def cluster_reopt_table)

lemma set_of_idx_rmk[simp]: "set_of_idx (rmk reopt_table i) = reopt_table (set_of_idx i)"
proof (rule set_eqI)
  fix y
  show "y \<in> set_of_idx (rmk reopt_table i) \<longleftrightarrow> y \<in> reopt_table (set_of_idx i)"
  proof
    assume "y \<in> set_of_idx (rmk reopt_table i)"
    then obtain w Y where "Mapping.lookup (rmk reopt_table i) w = Some Y" "y \<in> Y"
      unfolding in_set_of_idx by blast
    then obtain k Z where "Mapping.lookup i k = Some Z" "Y = reopt_table Z"
      by (auto simp: lookup_rmk split: option.splits)
    then have "y \<in> reopt_table {x. x \<in> set_of_idx i}"
      using \<open>y \<in> Y\<close> unfolding in_set_of_idx by (auto simp: reopt_table_def)
    then show "y \<in> reopt_table (set_of_idx i)" by simp
  next
    assume "y \<in> reopt_table (set_of_idx i)"
    then obtain x k Z where "y = reopt x" "Mapping.lookup i k = Some Z" "x \<in> Z"
      by (auto simp: in_set_of_idx reopt_table_def)
    then show "y \<in> set_of_idx (rmk reopt_table i)"
      unfolding in_set_of_idx
      by (intro exI[of _ "reopt k"] exI[of _ "reopt_table Z"]) (simp add: reopt_table_def)
  qed
qed

lemma dsemi_idx_rmk[simp]:
  "dsemi_idx msk pos (rmk reopt_table i) (reopt_table X) = reopt_table (dsemi_idx msk pos i X)"
  by (simp add: dsemi_idx_def)

lemma didx_union_rmk[simp]:
  "didx_union (rmk reopt_table i1) (rmk reopt_table i2) = rmk reopt_table (didx_union i1 i2)"
  by (simp add: didx_union_def rmk_combine)

lemma dbucket_rmk[simp]: "dbucket (rmk reopt_table d) (reopt k) = reopt_table (dbucket d k)"
  by (simp add: dbucket_def split: option.splits)

lemma didx_minus_rmk[simp]:
  "didx_minus (rmk reopt_table i) (rmk reopt_table d) = rmk reopt_table (didx_minus i d)"
  unfolding didx_minus_def
  by (subst rmk_map_values[where f' = reopt_table and G' = "\<lambda>k Y. Y - dbucket d k"]) simp_all

lemma gvalid_tuple_rmk[simp]: "gvalid_tuple (rmk (\<lambda>v. v) m) (t, reopt as) = gvalid_tuple m (t, as)"
  by (simp add: gvalid_tuple_def split: option.splits)

lemma gidx_upd_rmk[simp]:
  "gidx_upd args (\<lambda>u. rmk reopt_table (w u)) = rmk reopt_table (gidx_upd args w)"
  by (simp add: gidx_upd_def)

subsubsection \<open>The folds\<close>

text \<open>The shapes the structures hold: a time stamp with a table, and a queue of them.\<close>

abbreviation rtq :: "ts \<times> event_data list set \<Rightarrow> ts \<times> event_data table" where
  "rtq \<equiv> map_prod (\<lambda>t. t) reopt_table"

abbreviation rq :: "(ts \<times> event_data list set) queue \<Rightarrow> (ts \<times> event_data table) queue" where
  "rq \<equiv> map_queue rtq"


lemma fold_append_queue_map_queue[simp]:
  "fold append_queue (map f xs) (map_queue f q) = map_queue f (fold append_queue xs q)"
  by (induct xs arbitrary: q) auto

lemma fold_append_queue_rq:
  "fold (\<lambda>(t, X) q. append_queue (t, X) q) (map (rtq) xs) (rq q)
   = rq (fold (\<lambda>(t, X) q. append_queue (t, X) q) xs q)"
  by (induct xs arbitrary: q) (auto simp: map_prod_def split: prod.splits)

lemma filter_set_rmk:
  "filter_set (t, reopt_table X) (rmk (\<lambda>v. v) m, reopt_table Y)
   = map_prod (rmk (\<lambda>v. v)) reopt_table (filter_set (t, X) (m, Y))"
proof -
  have f: "Mapping.filter (filter_cond (reopt_table X) (rmk (\<lambda>v. v) m) t) (rmk (\<lambda>v. v) m)
      = rmk (\<lambda>v. v) (Mapping.filter (filter_cond X m t) m)"
    unfolding rmk_filter
    by (rule arg_cong[where f = "rmk (\<lambda>v. v)"], rule mapping_eqI)
      (simp add: Mapping.lookup_filter option.map_ident split: option.splits)
  show ?thesis unfolding filter_set.simps Let_def f by simp
qed

lemma fold_filter_set_rmk:
  "fold filter_set (map (rtq) xs) (rmk (\<lambda>v. v) m, reopt_table Y)
   = map_prod (rmk (\<lambda>v. v)) reopt_table (fold filter_set xs (m, Y))"
proof (induct xs arbitrary: m Y)
  case (Cons x xs)
  obtain t X where x: "x = (t, X)" by (cases x)
  obtain m' Y' where s: "filter_set (t, X) (m, Y) = (m', Y')" by (cases "filter_set (t, X) (m, Y)")
  show ?case unfolding x by (simp add: filter_set_rmk s Cons)
qed simp

lemma upd_set_keys_rmk:
  "upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple (rmk (\<lambda>v. v) ts) (t, as)}) (t, reopt_table X)
      (rmk (\<lambda>v. v) m, reopt_table Y)
   = map_prod (rmk (\<lambda>v. v)) reopt_table
       (upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple ts (t, as)}) (t, X) (m, Y))"
proof -
  have "{as \<in> reopt_table X. gvalid_tuple (rmk (\<lambda>v. v) ts) (t, as)}
      = reopt_table {as \<in> X. gvalid_tuple ts (t, as)}"
    by (auto simp: reopt_table_def)
  then show ?thesis unfolding upd_set_keys.simps
    by (simp add: rmk_upd_set[of "\<lambda>v. v", simplified])
qed

lemma fold_upd_set_keys_rmk:
  "fold (upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple (rmk (\<lambda>v. v) ts) (t, as)}))
      (map (rtq) xs) (rmk (\<lambda>v. v) m, reopt_table Y)
   = map_prod (rmk (\<lambda>v. v)) reopt_table
       (fold (upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple ts (t, as)})) xs (m, Y))"
proof (induct xs arbitrary: m Y)
  case (Cons x xs)
  obtain t X where x: "x = (t, X)" by (cases x)
  obtain m' Y' where s: "upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple ts (t, as)}) (t, X) (m, Y) = (m', Y')"
    by (cases "upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple ts (t, as)}) (t, X) (m, Y)")
  show ?case unfolding x by (simp add: upd_set_keys_rmk s Cons)
qed simp



lemmas fold_filter_set_rmk0 = fold_filter_set_rmk[where Y = "{}", simplified]
lemmas fold_upd_set_keys_rmk0 = fold_upd_set_keys_rmk[where Y = "{}", simplified]

text \<open>The queue scans, with the predicates the structures use: on the time stamp of an entry.\<close>


lemma rtq_pred: "(\<lambda>x. (\<lambda>(t, X). P t) (rtq x)) = (\<lambda>(t, X). P t)"
  by (auto simp: fun_eq_iff)

lemma dropWhile_queue_rq[simp]:
  "dropWhile_queue (\<lambda>(t, X). P t) (rq q) = rq (dropWhile_queue (\<lambda>(t, X). P t) q)"
  unfolding dropWhile_queue_map_queue rtq_pred ..

lemma takedropWhile_queue_rq[simp]:
  "takedropWhile_queue (\<lambda>(t, X). P t) (rq q)
   = map_prod rq (map rtq) (takedropWhile_queue (\<lambda>(t, X). P t) q)"
  unfolding takedropWhile_queue_map_queue rtq_pred ..

lemma append_queue_rq[simp]: "append_queue (t, reopt_table X) (rq q) = rq (append_queue (t, X) q)"
  using append_queue_map_queue[of rtq "(t, X)" q] by simp

lemmas rmk_upd_set_id[simp] = rmk_upd_set[of "\<lambda>v. v", simplified]

subsection \<open>The Since structure\<close>

fun rmsaux :: "event_data gmsaux \<Rightarrow> event_data option gmsaux" where
  "rmsaux (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in, idx_since, tuple_since)
   = (t, gc, msk, rq data_prev, rq data_in, reopt_table table_in, rmk reopt_table idx_in,
      rmk (\<lambda>v. v) tuple_in, rmk reopt_table idx_since, rmk (\<lambda>v. v) tuple_since)"

lemma ginit_msaux_rmsaux: "ginit_msaux args msk = rmsaux (ginit_msaux args msk)"
  by (simp add: ginit_msaux_def)

lemma gshift_end_rmsaux: "gshift_end args nt (rmsaux s) = rmsaux (gshift_end args nt s)"
  by (cases s rule: gmsaux_cases) (simp add: Let_def fold_filter_set_rmk0 split: prod.splits)

lemma gadd_new_ts_msaux'_rmsaux:
  "gadd_new_ts_msaux' args nt (rmsaux s) = rmsaux (gadd_new_ts_msaux' args nt s)"
  by (cases s rule: gmsaux_cases)
    (simp add: Let_def fold_append_queue_rq fold_upd_set_keys_rmk0 split: prod.splits)

lemma gadd_new_ts_msaux_rmsaux:
  "gadd_new_ts_msaux args nt (rmsaux s) = rmsaux (gadd_new_ts_msaux args nt s)"
  by (simp add: gadd_new_ts_msaux_def gshift_end_rmsaux gadd_new_ts_msaux'_rmsaux)

lemma ggc_msaux_rmsaux: "ggc_msaux args (rmsaux s) = rmsaux (ggc_msaux args s)"
proof (cases s rule: gmsaux_cases)
  case (1 t gc msk data_prev data_in table_in idx_in tuple_in idx_since tuple_since)
  have "\<Union> (snd ` (set (linearize (rq data_prev)) \<union> set (linearize (rq data_in))))
      = reopt_table (\<Union> (snd ` (set (linearize data_prev) \<union> set (linearize data_in))))"
    by (auto simp: reopt_table_def)
  then show ?thesis unfolding 1 by (simp add: Let_def)
qed

lemma gadd_new_table_msaux_rmsaux:
  "gadd_new_table_msaux args (reopt_table X) (rmsaux s) = rmsaux (gadd_new_table_msaux args X s)"
  by (cases s rule: gmsaux_cases) (simp add: Let_def)

lemma gresult_msaux_rmsaux: "gresult_msaux args (rmsaux s) = reopt_table (gresult_msaux args s)"
  by (cases s rule: gmsaux_cases) simp

lemma gjoin_msaux_rmsaux:
  "gjoin_msaux args (reopt_table Y) (rmsaux s) = rmsaux (gjoin_msaux args Y s)"
  by (cases s rule: gmsaux_cases) (auto simp: Let_def)

lemma ggc_join_msaux_rmsaux:
  "ggc_join_msaux args (reopt_table Y) (rmsaux s) = rmsaux (ggc_join_msaux args Y s)"
  by (cases s rule: gmsaux_cases)
    (simp only: ggc_join_msaux.simps rmsaux.simps gjoin_msaux_rmsaux[symmetric]
      ggc_msaux_rmsaux[symmetric] if_distrib[where f = "gjoin_msaux args (reopt_table Y)"]
      if_distrib[where f = rmsaux] refl)

subsection \<open>The Since window\<close>

text \<open>The window of @{theory MFODL_Monitor_Dense.Dense_Evt}, over a bare element type.  It is the
  verified one clause for clause; at the option instance it \<^emph>\<open>is\<close> the verified one.\<close>

type_synonym 'b gcntset = "('b list, nat) mapping \<times> 'b list set"

definition gcnt_add1 :: "'b list \<Rightarrow> 'b gcntset \<Rightarrow> 'b gcntset" where
  "gcnt_add1 t cc = (case cc of (c, s) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, Set.insert t s)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, s)))"

definition gcnt_del1 :: "'b list \<Rightarrow> 'b gcntset \<Rightarrow> 'b gcntset" where
  "gcnt_del1 t cc = (case cc of (c, s) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (c, s)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, Set.remove t s)
                  else (Mapping.update t (k - 1) c, s))))"

definition gcnt_add :: "'b :: ccompare list set \<Rightarrow> 'b gcntset \<Rightarrow> 'b gcntset" where
  "gcnt_add T cc = fold gcnt_add1 (csl T) cc"

definition gcnt_del :: "'b :: ccompare list set \<Rightarrow> 'b gcntset \<Rightarrow> 'b gcntset" where
  "gcnt_del T cc = fold gcnt_del1 (csl T) cc"

type_synonym 'b gswaux = "ts \<times> (ts \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times> 'b gcntset"

function gsw_move :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'b :: ccompare list set) queue \<Rightarrow>
    (ts \<times> 'b list set) queue \<Rightarrow> 'b gcntset \<Rightarrow>
    (ts \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times> 'b gcntset" where
  "gsw_move args nt pend win cc =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cc)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then gsw_move args nt (tl_queue pend') (append_queue e win) (gcnt_add (snd e) cc)
               else gsw_move args nt (tl_queue pend') win cc)
         else (pend', win, cc)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, pend, win, cc). length (linearize pend))")
     (fastforce split: prod.splits)+

declare gsw_move.simps[simp del]

function gsw_expire :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'b :: ccompare list set) queue \<Rightarrow> 'b gcntset \<Rightarrow>
    (ts \<times> 'b list set) queue \<times> 'b gcntset" where
  "gsw_expire args nt win cc =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cc)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cc)
         else gsw_expire args nt (tl_queue win') (gcnt_del (snd e) cc)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, win, cc). length (linearize win))")
     (fastforce split: prod.splits)+

declare gsw_expire.simps[simp del]

definition gsw_init :: "args \<Rightarrow> 'b gswaux" where
  "gsw_init args = (0, empty_queue, empty_queue, Mapping.empty, {})"

definition gsw_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> 'b :: ccompare gswaux \<Rightarrow> 'b gswaux" where
  "gsw_add_new_ts args nt aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (case gsw_move args nt pend win cc of (pend', win', cc') \<Rightarrow>
      (case gsw_expire args nt win' cc' of (win'', cc'') \<Rightarrow> (nt, pend', win'', cc''))))"

definition gsw_join :: "args \<Rightarrow> 'b list set \<Rightarrow> 'b gswaux \<Rightarrow> 'b gswaux" where
  "gsw_join args X aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, Mapping.empty, {})))"

definition gsw_add_new_table :: "args \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b gswaux \<Rightarrow> 'b gswaux" where
  "gsw_add_new_table args X aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (t, pend, append_queue (t, X) win, gcnt_add X cc)
      else (t, append_queue (t, X) pend, win, cc)))"

definition gsw_result :: "args \<Rightarrow> 'b gswaux \<Rightarrow> 'b list set" where
  "gsw_result args aux = (case aux of (t, pend, win, cc) \<Rightarrow> snd cc)"

lemma gcnt_add1_eq: "gcnt_add1 = (cnt_add1 :: event_data tuple \<Rightarrow> _)"
  by (intro ext) (simp add: gcnt_add1_def cnt_add1_def)

lemma gcnt_del1_eq: "gcnt_del1 = (cnt_del1 :: event_data tuple \<Rightarrow> _)"
  by (intro ext) (simp add: gcnt_del1_def cnt_del1_def)

lemma gcnt_add_eq: "gcnt_add (T :: event_data table) = cnt_add T"
  by (intro ext) (simp add: gcnt_add_def cnt_add_def gcnt_add1_eq)

lemma gcnt_del_eq: "gcnt_del (T :: event_data table) = cnt_del T"
  by (intro ext) (simp add: gcnt_del_def cnt_del_def gcnt_del1_eq)

lemma gsw_move_eq:
  "gsw_move args nt (pend :: (ts \<times> event_data table) queue) win cc = sw_move args nt pend win cc"
proof (induct args nt pend win cc rule: gsw_move.induct)
  case (1 args nt pend win cc)
  obtain h pend' where sh: "safe_hd pend = (h, pend')" by (cases "safe_hd pend")
  show ?case
    using 1[OF sh[symmetric]]
    by (subst gsw_move.simps, subst sw_move.simps)
      (auto simp: sh gcnt_add_eq split: option.splits)
qed

lemma gsw_expire_eq:
  "gsw_expire args nt (win :: (ts \<times> event_data table) queue) cc = sw_expire args nt win cc"
proof (induct args nt win cc rule: gsw_expire.induct)
  case (1 args nt win cc)
  obtain h win' where sh: "safe_hd win = (h, win')" by (cases "safe_hd win")
  show ?case
    using 1[OF sh[symmetric]]
    by (subst gsw_expire.simps, subst sw_expire.simps)
      (auto simp: sh gcnt_del_eq split: option.splits)
qed

lemma gsw_init_eq: "gsw_init args = (sw_init args :: swaux)"
  by (simp add: gsw_init_def sw_init_def)

lemma gsw_add_new_ts_eq: "gsw_add_new_ts args nt (aux :: swaux) = sw_add_new_ts args nt aux"
  by (simp add: gsw_add_new_ts_def sw_add_new_ts_def gsw_move_eq gsw_expire_eq split: prod.splits)

lemma gsw_join_eq: "gsw_join args X (aux :: swaux) = sw_join args X aux"
  by (simp add: gsw_join_def sw_join_def split: prod.splits)

lemma gsw_add_new_table_eq:
  "gsw_add_new_table args X (aux :: swaux) = sw_add_new_table args X aux"
  by (simp add: gsw_add_new_table_def sw_add_new_table_def gcnt_add_eq split: prod.splits)

lemma gsw_result_eq: "gsw_result args (aux :: swaux) = sw_result args aux"
  by (simp add: gsw_result_def sw_result_def split: prod.splits)

text \<open>Its naturality.\<close>

fun rcc :: "event_data gcntset \<Rightarrow> event_data option gcntset" where
  "rcc (c, s) = (rmk (\<lambda>v. v) c, reopt_table s)"

fun rsw :: "event_data gswaux \<Rightarrow> event_data option gswaux" where
  "rsw (t, pend, win, cc) = (t, rq pend, rq win, rcc cc)"

text \<open>The two maps are unfolded only on demand: the naturality lemmas below are stated on an
  abstract count set, which the simplifier would otherwise split.\<close>

declare rcc.simps[simp del] rsw.simps[simp del]

lemma gcnt_add1_rcc: "gcnt_add1 (reopt t) (rcc cc) = rcc (gcnt_add1 t cc)"
  by (cases cc) (simp add: gcnt_add1_def rcc.simps split: option.splits)

lemma gcnt_del1_rcc: "gcnt_del1 (reopt t) (rcc cc) = rcc (gcnt_del1 t cc)"
  by (cases cc) (simp add: gcnt_del1_def rcc.simps split: option.splits)

lemma fold_gcnt_add1_rcc: "fold gcnt_add1 (map reopt xs) (rcc cc) = rcc (fold gcnt_add1 xs cc)"
  by (induct xs arbitrary: cc) (simp_all add: gcnt_add1_rcc)

lemma fold_gcnt_del1_rcc: "fold gcnt_del1 (map reopt xs) (rcc cc) = rcc (fold gcnt_del1 xs cc)"
  by (induct xs arbitrary: cc) (simp_all add: gcnt_del1_rcc)

lemma gcnt_add_rcc[simp]: "gcnt_add (reopt_table T) (rcc cc) = rcc (gcnt_add T cc)"
  by (simp add: gcnt_add_def csl_reopt_table fold_gcnt_add1_rcc)

lemma gcnt_del_rcc[simp]: "gcnt_del (reopt_table T) (rcc cc) = rcc (gcnt_del T cc)"
  by (simp add: gcnt_del_def csl_reopt_table fold_gcnt_del1_rcc)

lemma gsw_move_rsw:
  "gsw_move args nt (rq pend) (rq win) (rcc cc)
   = (case gsw_move args nt pend win cc of (pend', win', cc') \<Rightarrow> (rq pend', rq win', rcc cc'))"
proof (induct args nt pend win cc rule: gsw_move.induct)
  case (1 args nt pend win cc)
  obtain h pend' where sh: "safe_hd pend = (h, pend')" by (cases "safe_hd pend")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst gsw_move.simps, subst (2) gsw_move.simps) (simp add: sh)
  next
    case (Some e)
    obtain te Xe where e: "e = (te, Xe)" by (cases e)
    note IH = 1[OF sh[symmetric] Some, unfolded e, simplified]
    show ?thesis
      by (subst gsw_move.simps, subst (2) gsw_move.simps)
        (auto simp: sh Some e IH split: prod.splits)
  qed
qed

lemma gsw_expire_rsw:
  "gsw_expire args nt (rq win) (rcc cc)
   = (case gsw_expire args nt win cc of (win', cc') \<Rightarrow> (rq win', rcc cc'))"
proof (induct args nt win cc rule: gsw_expire.induct)
  case (1 args nt win cc)
  obtain h win' where sh: "safe_hd win = (h, win')" by (cases "safe_hd win")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst gsw_expire.simps, subst (2) gsw_expire.simps) (simp add: sh)
  next
    case (Some e)
    obtain te Xe where e: "e = (te, Xe)" by (cases e)
    note IH = 1[OF sh[symmetric] Some, unfolded e, simplified]
    show ?thesis
      by (subst gsw_expire.simps, subst (2) gsw_expire.simps)
        (auto simp: sh Some e IH split: prod.splits)
  qed
qed

lemma gsw_init_rsw: "gsw_init args = rsw (gsw_init args)"
  by (simp add: gsw_init_def rsw.simps rcc.simps)

lemma gsw_add_new_ts_rsw: "gsw_add_new_ts args nt (rsw w) = rsw (gsw_add_new_ts args nt w)"
proof -
  obtain t pend win cc where w: "w = (t, pend, win, cc)" by (cases w)
  obtain pend' win' cc' where m: "gsw_move args nt pend win cc = (pend', win', cc')"
    by (metis prod_cases3)
  obtain win'' cc'' where e: "gsw_expire args nt win' cc' = (win'', cc'')"
    by (cases "gsw_expire args nt win' cc'")
  show ?thesis unfolding w
    by (simp add: gsw_add_new_ts_def rsw.simps gsw_move_rsw gsw_expire_rsw m e)
qed

lemma gsw_join_rsw: "gsw_join args (reopt_table X) (rsw w) = rsw (gsw_join args X w)"
  by (cases w) (simp add: gsw_join_def rsw.simps rcc.simps)

lemma gsw_add_new_table_rsw:
  "gsw_add_new_table args (reopt_table X) (rsw w) = rsw (gsw_add_new_table args X w)"
  by (cases w) (simp add: gsw_add_new_table_def rsw.simps)

lemma gsw_result_rsw: "gsw_result args (rsw w) = reopt_table (gsw_result args w)"
  by (cases w) (auto simp: gsw_result_def rsw.simps rcc.simps split: prod.splits)

subsection \<open>The fused aggregation window\<close>

text \<open>The kernel's incremental aggregation structure reads widened boxed tuples.  The unboxed
  window produces them from its short tuples in one pass, and reads the structure's result back
  as short tuples.  Both directions are exact: the widening of an embedded table is the widening
  of the short one, and the sanitised result of the kernel is the embedding of its short reading.\<close>

fun udwiden :: "bool list \<Rightarrow> 'a list \<Rightarrow> 'a tuple" where
  "udwiden [] xs = []"
| "udwiden (False # bs) xs = None # udwiden bs xs"
| "udwiden (True # bs) (x # xs) = Some x # udwiden bs xs"
| "udwiden (True # bs) [] = []"

lemma udwiden_eq: "udwiden bs xs = dwiden bs (reopt xs)"
  by (induct bs xs rule: udwiden.induct) (auto simp: reopt_def)

definition udtabw :: "nat \<Rightarrow> cols \<Rightarrow> 'a list set \<Rightarrow> 'a table" where
  "udtabw n cs D = udwiden (wide_mask n cs) ` D"

lemma udtabw_eq: "udtabw n cs D = dtabw n cs (reopt_table D)"
  by (simp add: udtabw_def dtabw_def reopt_table_def image_image udwiden_eq)

definition udagg_wide :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> event_data table" where
  "udagg_wide p w D = udtabw (Suc w) (dagg_ccols p w) D"

lemma udagg_wide_eq: "udagg_wide p w D = dagg_wide p w (reopt_table D)"
  by (simp add: udagg_wide_def dagg_wide_def udtabw_eq)

fun udagg_p :: "daggp \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "udagg_p (g0, \<omega>, f, k, pos) = uagg g0 \<omega> f k pos"

lemma udagg_p_eq: "reopt_table (udagg_p p X) = dagg_p p (reopt_table X)"
  by (cases p) (simp add: dagg_def)

text \<open>
  The count structure of @{theory MFODL_Monitor_Dense.Dense_Evt} keeps the tuples' counts in a
  mapping and their keys in a set beside it, so that the plain window can hand out its union in
  one step.  The fused window never hands out that union -- it hands out the aggregate, and reads
  the count structure only to learn which tuples enter the window and which leave it.  The
  mapping answers both, so the fused window keeps the mapping alone and pays one tree operation
  per tuple where the plain window pays two.  @{text ucc} reads the count structure off it: the
  key set is the mapping's domain, which is what the plain window's second half always was.
\<close>

type_synonym ucnt = "(event_data list, nat) mapping"

definition ucnt_add1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> Mapping.update t 1 c
   | Some k \<Rightarrow> Mapping.update t (k + 1) c)"

definition ucnt_del1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> c
   | Some k \<Rightarrow> (if k \<le> 1 then Mapping.delete t c else Mapping.update t (k - 1) c))"

definition ucnt_add :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add T c = fold ucnt_add1 (csl T) c"

definition ucnt_del :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del T c = fold ucnt_del1 (csl T) c"

fun ucc :: "ucnt \<Rightarrow> event_data gcntset" where
  "ucc c = (c, Mapping.keys c)"

declare ucc.simps[simp del]

lemma lookup_None_keys: "(Mapping.lookup c t = None) = (t \<notin> Mapping.keys c)"
  by (simp add: Mapping.keys_dom_lookup domIff)

lemma gcnt_add1_ucc: "gcnt_add1 t (ucc c) = ucc (ucnt_add1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: gcnt_add1_def ucnt_add1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis by (simp add: gcnt_add1_def ucnt_add1_def ucc.simps insert_absorb)
qed

lemma gcnt_del1_ucc: "gcnt_del1 t (ucc c) = ucc (ucnt_del1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: gcnt_del1_def ucnt_del1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis
    by (simp add: gcnt_del1_def ucnt_del1_def ucc.simps insert_absorb)
qed

lemma fold_gcnt_add1_ucc: "fold gcnt_add1 xs (ucc c) = ucc (fold ucnt_add1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: gcnt_add1_ucc)

lemma fold_gcnt_del1_ucc: "fold gcnt_del1 xs (ucc c) = ucc (fold ucnt_del1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: gcnt_del1_ucc)

lemma gcnt_add_ucc[simp]: "gcnt_add T (ucc c) = ucc (ucnt_add T c)"
  by (simp add: gcnt_add_def ucnt_add_def fold_gcnt_add1_ucc)

lemma gcnt_del_ucc[simp]: "gcnt_del T (ucc c) = ucc (ucnt_del T c)"
  by (simp add: gcnt_del_def ucnt_del_def fold_gcnt_del1_ucc)

text \<open>What enters the window is what the mapping does not hold yet, and what leaves it is what
  it holds exactly once: both are read off the mapping, one lookup per tuple.\<close>

definition ucnt_enter :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> event_data list set" where
  "ucnt_enter T c = Set.filter (\<lambda>x. Mapping.lookup c x = None) T"

definition ucnt_leave :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> event_data list set" where
  "ucnt_leave T c = Set.filter (\<lambda>x. Mapping.lookup c x = Some 1) T"

lemma ucnt_enter_ucc: "ucnt_enter T c = T - snd (ucc c)"
  by (auto simp: ucnt_enter_def ucc.simps lookup_None_keys)

text \<open>
  The aggregate is kept over the short tuples, in @{typ "event_data gagg"}: the dense window's
  structure with the option taken off the keys.  @{text rgagg} puts it back on, and every
  operation commutes with it -- the keys are renamed by the injective @{const reopt}, which the
  mapping operations commute with, and the value a tuple contributes is the one the dense side
  reads through @{const deopt}.
\<close>

type_synonym ugagg = "event_data gagg"

fun rgagg :: "ugagg \<Rightarrow> dgagg" where
  "rgagg (GCnt m) = GCnt (rmk (\<lambda>v. v) m)"
| "rgagg (GSum m) = GSum (rmk (\<lambda>v. v) m)"
| "rgagg (GRank m ty) = GRank (rmk (\<lambda>v. v) m) ty"

definition uag_ins :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_ins p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gins k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = None) (csl T)) ax)"

definition uag_del :: "daggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_del p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gdel k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl T)) ax)"

text \<open>
  A node whose result is an aggregate is often read through a constraint on the aggregate's own
  value: \<^verbatim>\<open>(r <- CNT y; x ONCE[0,60] A(x,y)) AND 40 < r\<close> is the shape of a whole family of
  policies.  Compiled as a filter over the node, that builds the table of all groups and then
  drops most of it again -- every group that fails the constraint is inserted into a tree only
  to be removed from the next one.  The constraint is carried by the node instead, as the guard
  below, and the read inserts only the groups that pass.  The guard is @{const None} at a node
  that carries no constraint, and then it admits everything.
\<close>

type_synonym uconstr = "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"

definition uqok :: "uconstr option \<Rightarrow> event_data list \<Rightarrow> bool" where
  "uqok q = (case q of None \<Rightarrow> (\<lambda>_. True) | Some c \<Rightarrow> ueval_constraint c)"

definition dqok :: "uconstr option \<Rightarrow> event_data tuple \<Rightarrow> bool" where
  "dqok q = (case q of None \<Rightarrow> (\<lambda>_. True) | Some c \<Rightarrow> deval_constraint c)"

definition ufilt :: "uconstr option \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "ufilt q X = Set.filter (uqok q) X"

definition dfilt :: "uconstr option \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dfilt q X = Set.filter (dqok q) X"

lemma uqok_None[simp]: "uqok None = (\<lambda>_. True)"
  by (simp add: uqok_def)

lemma dqok_None[simp]: "dqok None = (\<lambda>_. True)"
  by (simp add: dqok_def)

lemma ufilt_None[simp]: "ufilt None = id"
  by (simp add: ufilt_def fun_eq_iff)

lemma dfilt_None[simp]: "dfilt None = id"
  by (simp add: dfilt_def fun_eq_iff)

lemma ufilt_Some: "ufilt (Some c) X = Set.filter (ueval_constraint c) X"
  by (simp add: ufilt_def uqok_def)

lemma dfilt_Some: "dfilt (Some c) X = Set.filter (deval_constraint c) X"
  by (simp add: dfilt_def dqok_def)

lemma dfilt_reopt_table: "dfilt q (reopt_table X) = reopt_table (ufilt q X)"
  by (auto simp: dfilt_def ufilt_def dqok_def uqok_def reopt_table_def split: option.splits)

lemma dfilt_idem[simp]: "dfilt q (dfilt q X) = dfilt q X"
  by (auto simp: dfilt_def)

lemma dfilt_Un: "dfilt q (A \<union> B) = dfilt q A \<union> dfilt q B"
  by (auto simp: dfilt_def)

text \<open>The result writes the aggregate into each group and keeps what passes the node's guard.
  The fused form walks the mapping's entries -- the key and its value together, so no lookup --
  and inserts the node's own tuple straight into the answer.\<close>

definition ugmr :: "(event_data list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> event_data) \<Rightarrow>
    (event_data list, 'b) mapping \<Rightarrow> event_data list set" where
  "ugmr q p f m = Set.filter q (gmr p (\<lambda>x. x) f m)"

lemma fold_insert_image:
  "fold (\<lambda>x A. let v = g x in if q v then Set.insert v A else A) xs A
   = Set.filter q (g ` set xs) \<union> A"
  by (induct xs arbitrary: A) (auto simp: Let_def)

lemma ugmr_code[code]:
  fixes t :: "(event_data list, 'b) mapping_rbt"
  shows "ugmr q p f (RBT_Mapping t) =
    (case ID CCOMPARE(event_data list) of
       None \<Rightarrow> Code.abort (STR ''ugmr RBT_Mapping: ccompare = None'')
                (\<lambda>_. ugmr q p f (RBT_Mapping t))
     | Some _ \<Rightarrow> fold (\<lambda>e A. let v = take p (fst e) @ f (snd e) # drop p (fst e)
                    in if q v then Set.insert v A else A)
                  (RBT_Mapping2.entries t) {})"
proof (cases "ID CCOMPARE(event_data list)")
  case (Some c)
  note comp = ID_ccompare'[OF Some]
  have dist: "distinct (map fst (RBT_Mapping2.entries t))"
    using Some by (transfer fixing: c)
      (simp add: ord.is_rbt_def linorder.distinct_entries[OF comparator.linorder[OF comp]])
  have mo: "map_of (RBT_Mapping2.entries t) (fst e) = Some (snd e)"
    if "e \<in> set (RBT_Mapping2.entries t)" for e
    using dist that by (cases e) (simp add: map_of_is_SomeI)
  have lk: "Mapping.lookup (RBT_Mapping t) = map_of (RBT_Mapping2.entries t)"
    by (simp add: lookup_Mapping_code(1) map_of_entries Some del: RBT_Mapping_def)
  have ky: "Mapping.keys (RBT_Mapping t) = fst ` set (RBT_Mapping2.entries t)"
    unfolding Mapping.keys_dom_lookup lk by (rule dom_map_of_conv_image_fst)
  have "ugmr q p f (RBT_Mapping t)
      = Set.filter q ((\<lambda>e. take p (fst e) @ f (snd e) # drop p (fst e))
          ` set (RBT_Mapping2.entries t))"
    unfolding ugmr_def gmr_def ky lk image_image
    by (intro arg_cong[of _ _ "Set.filter q"] image_cong[OF refl]) (simp add: mo)
  then show ?thesis using Some by (simp add: fold_insert_image)
qed simp

definition ugres :: "(event_data list \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> ugagg \<Rightarrow>
    event_data list set" where
  "ugres q g0 \<omega> p a = Set.filter q (gres g0 \<omega> p (\<lambda>x. x) a)"

lemma ugres_code[code]:
  "ugres q g0 \<omega> p a = (case a of
     GCnt m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else ugmr q p (\<lambda>k. EInt (integer_of_int k)) m)
   | GSum m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Sum \<Rightarrow> ugmr q p (\<lambda>k. EInt (snd k)) m
       | Formula.Agg_Avg \<Rightarrow> ugmr q p
           (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) / double_of_int (fst k))) m
       | _ \<Rightarrow> {}))
   | GRank m ty \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Min \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k 0) m
       | Formula.Agg_Max \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k (get_length k - 1)) m
       | Formula.Agg_Med \<Rightarrow> ugmr q p (\<lambda>k. let u = get_length k; u' = u div 2;
           aggval = (if even u
             then (double_of_event_data_agg (get_edata_list k (u' - 1))
                   + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
             else double_of_event_data_agg (get_edata_list k u'))
           in EFloat aggval) m
       | _ \<Rightarrow> {})))"
  by (cases a) (simp_all add: ugres_def ugmr_def Mapping.is_empty_def
      split: Formula.agg_type.splits)

definition uag_res :: "uconstr option \<Rightarrow> daggp \<Rightarrow> nat \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> event_data list set" where
  "uag_res q p w c ax = ufilt q (case ax of
     None \<Rightarrow> udagg_p p (Mapping.keys c)
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gres g0 \<omega> pos (\<lambda>x. x) a))"

lemma uag_res_code[code]:
  "uag_res q p w c ax = (case ax of
     None \<Rightarrow> ufilt q (udagg_p p (Mapping.keys c))
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) g0 \<omega> pos a))"
  by (simp add: uag_res_def ugres_def ufilt_def split: option.splits prod.splits)

text \<open>The naturality of the three operations and of the read.\<close>

lemma drop_reopt: "drop k (reopt t) = reopt (drop k t)"
  by (simp add: reopt_def drop_map)

lemma gstep_ins_rgagg:
  "gstep_ins k (\<lambda>t. ev (deopt t)) (reopt t) (map_option rgagg ax)
   = map_option rgagg (gstep_ins k ev t ax)"
proof (cases ax)
  case (Some a)
  then show ?thesis
    by (cases a) (simp_all add: gstep_ins_def drop_reopt Let_def del: reopt_simps(5)
        split: option.split prod.split event_data.split type.split list_aux.split)
qed (simp add: gstep_ins_def)

lemma gstep_del_rgagg:
  "gstep_del k (\<lambda>t. ev (deopt t)) (reopt t) (map_option rgagg ax)
   = map_option rgagg (gstep_del k ev t ax)"
proof (cases ax)
  case (Some a)
  then show ?thesis
    by (cases a) (simp_all add: gstep_del_def drop_reopt Let_def del: reopt_simps(5)
        split: option.split prod.split event_data.split type.split list_aux.split)
qed (simp add: gstep_del_def)

lemma gins_rgagg:
  "gins k (\<lambda>t. ev (deopt t)) (map reopt xs) (map_option rgagg ax) = map_option rgagg (gins k ev xs ax)"
  by (induct xs arbitrary: ax) (simp_all add: gins_def gstep_ins_rgagg)

lemma gdel_rgagg:
  "gdel k (\<lambda>t. ev (deopt t)) (map reopt xs) (map_option rgagg ax) = map_option rgagg (gdel k ev xs ax)"
  by (induct xs arbitrary: ax) (simp_all add: gdel_def gstep_del_rgagg)

lemma ginit_rgagg[simp]: "map_option rgagg (ginit \<omega>) = ginit \<omega>"
  by (simp add: ginit_def split: Formula.agg_type.splits ty.splits prod.splits)

lemma ag_init_rgagg[simp]: "map_option rgagg (ag_init p w) = ag_init p w"
  by (cases p) (simp add: ag_init_def)

lemma reopt_in_rcc: "reopt t \<in> snd (rcc (ucc c)) \<longleftrightarrow> Mapping.lookup c t \<noteq> None"
  by (auto simp: rcc.simps ucc.simps reopt_table_def lookup_None_keys reopt_def inj_on_def)

lemma lookup_rcc_reopt: "Mapping.lookup (fst (rcc (ucc c))) (reopt t) = Mapping.lookup c t"
  by (simp add: rcc.simps ucc.simps option.map_ident)

lemma ag_ins_rcc[simp]:
  "ag_ins p w (reopt_table T) (rcc (ucc c)) (map_option rgagg ax) = map_option rgagg (uag_ins p w T c ax)"
  by (cases p) (simp add: ag_ins_def uag_ins_def csl_reopt_table filter_map o_def reopt_in_rcc
      gins_rgagg)

lemma ag_del_rcc[simp]:
  "ag_del p w (reopt_table T) (rcc (ucc c)) (map_option rgagg ax) = map_option rgagg (uag_del p w T c ax)"
  by (cases p) (simp add: ag_del_def uag_del_def csl_reopt_table filter_map o_def lookup_rcc_reopt
      gdel_rgagg)

lemma gmr_rmk: "gmr p Some f (rmk (\<lambda>v. v) m) = reopt_table (gmr p (\<lambda>x. x) f m)"
  unfolding gmr_def keys_rmk reopt_table_def image_image
  by (intro image_cong refl) (simp split: option.split)

lemma gres_rgagg: "gres g0 \<omega> p Some (rgagg a) = reopt_table (gres g0 \<omega> p (\<lambda>x. x) a)"
proof -
  have e: "Mapping.keys (rmk (\<lambda>v. v) m) = {} \<longleftrightarrow> Mapping.keys m = {}" for m :: "(event_data list, 'v) mapping"
    by (simp add: reopt_table_def)
  have s: "reopt_table {[x]} = {[Some x]}" for x :: event_data
    by (simp add: reopt_table_def reopt_def)
  have r0: "reopt_table {} = {}" by (simp add: reopt_table_def)
  show ?thesis
    by (cases a; simp only: rgagg.simps gres.simps e s gmr_rmk r0 split: if_split
        Formula.agg_type.split; auto)
qed

lemma ag_res_rcc:
  "dfilt q (ag_res p w (rcc (ucc c)) (map_option rgagg ax)) = reopt_table (uag_res q p w c ax)"
proof (cases ax)
  case None
  show ?thesis unfolding None
    by (simp add: uag_res_def ag_res_def rcc.simps ucc.simps udagg_p_eq[symmetric]
        dfilt_reopt_table)
next
  case (Some a)
  show ?thesis unfolding Some
    by (cases p) (simp add: uag_res_def ag_res_def gres_rgagg dfilt_reopt_table)
qed

lemma ag_res_rcc_None[simp]:
  "ag_res p w (rcc (ucc c)) (map_option rgagg ax) = reopt_table (uag_res None p w c ax)"
  using ag_res_rcc[of None] by simp


lemma cnt_add_rcc[simp]: "cnt_add (reopt_table T) (rcc cc) = rcc (gcnt_add T cc)"
  by (simp add: gcnt_add_eq[symmetric])

lemma cnt_del_rcc[simp]: "cnt_del (reopt_table T) (rcc cc) = rcc (gcnt_del T cc)"
  by (simp add: gcnt_del_eq[symmetric])

type_synonym uswaux =
  "ts \<times> (ts \<times> event_data list set) queue \<times> (ts \<times> event_data list set) queue \<times> ucnt"

type_synonym uswagg = "uswaux \<times> ugagg option"

function usa_move :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
    (ts \<times> event_data list set) queue \<Rightarrow> ucnt \<Rightarrow> ugagg option \<Rightarrow>
    (ts \<times> event_data list set) queue \<times> (ts \<times> event_data list set) queue \<times>
    ucnt \<times> ugagg option" where
  "usa_move args p nt pend win cc ax =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cc, ax)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then usa_move args p nt (tl_queue pend') (append_queue e win) (ucnt_add (snd e) cc)
                      (uag_ins p (args_n args) (snd e) cc ax)
               else usa_move args p nt (tl_queue pend') win cc ax)
         else (pend', win, cc, ax)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, nt, pend, win, cc, ax). length (linearize pend))")
     (fastforce split: prod.splits)+

declare usa_move.simps[simp del]

function usa_expire :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data list set) queue \<Rightarrow>
    ucnt \<Rightarrow> ugagg option \<Rightarrow>
    (ts \<times> event_data list set) queue \<times> ucnt \<times> ugagg option" where
  "usa_expire args p nt win cc ax =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cc, ax)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cc, ax)
         else usa_expire args p nt (tl_queue win') (ucnt_del (snd e) cc)
                (uag_del p (args_n args) (snd e) cc ax)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, nt, win, cc, ax). length (linearize win))")
     (fastforce split: prod.splits)+

declare usa_expire.simps[simp del]

definition usw_init :: "args \<Rightarrow> uswaux" where
  "usw_init args = (0, empty_queue, empty_queue, Mapping.empty)"

definition usw_join :: "args \<Rightarrow> event_data list set \<Rightarrow> uswaux \<Rightarrow> uswaux" where
  "usw_join args X aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, Mapping.empty)))"

definition usa_init :: "args \<Rightarrow> daggp \<Rightarrow> uswagg" where
  "usa_init args p = (usw_init args, ag_init p (args_n args))"

definition usa_add_new_ts :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> uswagg \<Rightarrow> uswagg" where
  "usa_add_new_ts args p nt aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (case usa_move args p nt pend win cc ax of (pend', win', cc', ax') \<Rightarrow>
      (case usa_expire args p nt win' cc' ax' of (win'', cc'', ax'') \<Rightarrow>
        ((nt, pend', win'', cc''), ax''))))"

definition usa_join :: "args \<Rightarrow> daggp \<Rightarrow> event_data list set \<Rightarrow> uswagg \<Rightarrow> uswagg" where
  "usa_join args p X aux = (case aux of (w, ax) \<Rightarrow>
     (usw_join args X w,
      if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then ax
      else ag_init p (args_n args)))"

definition usa_add_new_table :: "args \<Rightarrow> daggp \<Rightarrow> event_data list set \<Rightarrow> uswagg \<Rightarrow> uswagg" where
  "usa_add_new_table args p X aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (if memL (args_ivl args) 0
      then ((t, pend, append_queue (t, X) win, ucnt_add X cc), uag_ins p (args_n args) X cc ax)
      else ((t, append_queue (t, X) pend, win, cc), ax)))"

definition usa_result :: "uconstr option \<Rightarrow> args \<Rightarrow> daggp \<Rightarrow> uswagg \<Rightarrow> event_data list set" where
  "usa_result q args p aux =
     (case aux of ((t, pend, win, cc), ax) \<Rightarrow> uag_res q p (args_n args) cc ax)"

text \<open>Its naturality, against the boxed window of the verified evaluator.\<close>

fun usw :: "uswaux \<Rightarrow> event_data gswaux" where
  "usw (t, pend, win, cc) = (t, pend, win, ucc cc)"

fun rsa :: "uswagg \<Rightarrow> swagg" where
  "rsa (w, ax) = (rsw (usw w), map_option rgagg ax)"

declare usw.simps[simp del] rsa.simps[simp del]

lemma usw_init_ucc: "gsw_init args = usw (usw_init args)"
  by (simp add: gsw_init_def usw_init_def usw.simps ucc.simps)

lemma usw_join_ucc: "gsw_join args X (usw w) = usw (usw_join args X w)"
  by (cases w) (simp add: gsw_join_def usw_join_def usw.simps ucc.simps)

lemma sa_move_rsa:
  "sa_move args p nt (rq pend) (rq win) (rcc (ucc cc)) (map_option rgagg ax)
   = (case usa_move args p nt pend win cc ax of
        (pend', win', cc', ax') \<Rightarrow> (rq pend', rq win', rcc (ucc cc'), map_option rgagg ax'))"
proof (induct args p nt pend win cc ax rule: usa_move.induct)
  case (1 args p nt pend win cc ax)
  obtain h pend' where sh: "safe_hd pend = (h, pend')" by (cases "safe_hd pend")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst sa_move.simps, subst usa_move.simps) (simp add: sh)
  next
    case (Some e)
    obtain te Xe where e: "e = (te, Xe)" by (cases e)
    note IH = 1[OF sh[symmetric] Some, unfolded e, simplified]
    show ?thesis
      by (subst sa_move.simps, subst usa_move.simps)
        (auto simp: sh Some e IH split: prod.splits)
  qed
qed

lemma sa_expire_rsa:
  "sa_expire args p nt (rq win) (rcc (ucc cc)) (map_option rgagg ax)
   = (case usa_expire args p nt win cc ax of
        (win', cc', ax') \<Rightarrow> (rq win', rcc (ucc cc'), map_option rgagg ax'))"
proof (induct args p nt win cc ax rule: usa_expire.induct)
  case (1 args p nt win cc ax)
  obtain h win' where sh: "safe_hd win = (h, win')" by (cases "safe_hd win")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst sa_expire.simps, subst usa_expire.simps) (simp add: sh)
  next
    case (Some e)
    obtain te Xe where e: "e = (te, Xe)" by (cases e)
    note IH = 1[OF sh[symmetric] Some, unfolded e, simplified]
    show ?thesis
      by (subst sa_expire.simps, subst usa_expire.simps)
        (auto simp: sh Some e IH split: prod.splits)
  qed
qed

lemma sa_init_rsa: "sa_init args p = rsa (usa_init args p)"
  by (simp add: sa_init_def usa_init_def rsa.simps usw_init_ucc[symmetric]
      gsw_init_rsw[symmetric] gsw_init_eq)

lemma sa_add_new_ts_rsa: "sa_add_new_ts args p nt (rsa aux) = rsa (usa_add_new_ts args p nt aux)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  obtain pend' win' cc' ax' where m: "usa_move args p nt pend win cc ax = (pend', win', cc', ax')"
    by (metis prod_cases4)
  obtain win'' cc'' ax'' where e: "usa_expire args p nt win' cc' ax' = (win'', cc'', ax'')"
    by (metis prod_cases3)
  show ?thesis unfolding aux
    by (simp add: sa_add_new_ts_def usa_add_new_ts_def rsa.simps rsw.simps usw.simps
        sa_move_rsa sa_expire_rsa m e)
qed

lemma sa_join_rsa: "sa_join args p (reopt_table X) (rsa aux) = rsa (usa_join args p X aux)"
  by (cases aux) (simp add: sa_join_def usa_join_def rsa.simps usw_join_ucc[symmetric]
      gsw_join_rsw[symmetric] gsw_join_eq)

lemma sa_add_new_table_rsa:
  "sa_add_new_table args p (reopt_table X) (rsa aux) = rsa (usa_add_new_table args p X aux)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  show ?thesis unfolding aux
    by (simp add: sa_add_new_table_def usa_add_new_table_def rsa.simps rsw.simps usw.simps)
qed

lemma sa_result_rsa:
  "dfilt q (sa_result args p (rsa aux)) = reopt_table (usa_result q args p aux)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  show ?thesis unfolding aux
    by (simp add: sa_result_def usa_result_def rsa.simps rsw.simps usw.simps ag_res_rcc
        del: ag_res_rcc_None)
qed

subsection \<open>The Until structure\<close>

text \<open>The generic Until deque of @{theory MFODL_Monitor_Dense.Dense_Until_Gen} reads its deques
  off their lists, so that every operation commutes with the embedding on every state.  The one
  reading that cannot is the head of the time stamp queue in @{const geval_step_dq}, which is
  undefined on an empty queue: the step is natural on the states it is ever applied to, those
  with a pending time stamp, and the shift applies it once per time stamp it takes.\<close>

lemma gmuaux_cases:
  fixes d :: "'b gmuaux"
  obtains tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
  where "d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
  by (metis prod.collapse)

abbreviation rtt :: "event_data list set \<times> (ts + tp) \<Rightarrow> event_data table \<times> (ts + tp)" where
  "rtt \<equiv> map_prod reopt_table (\<lambda>a. a)"

abbreviation rtbl :: "(event_data list set \<times> (ts + tp)) queue \<Rightarrow>
    (event_data table \<times> (ts + tp)) queue" where
  "rtbl \<equiv> map_queue rtt"

abbreviation ra2 :: "(event_data list, ts + tp) mapping dq \<Rightarrow>
    (event_data tuple, ts + tp) mapping dq" where
  "ra2 \<equiv> map_dq (rmk (\<lambda>v. v))"

fun rmuaux :: "event_data gmuaux \<Rightarrow> event_data option gmuaux" where
  "rmuaux (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn)
   = (tp, tss, rtbl tables, len, maskL, maskR, reopt_table result, rmk (\<lambda>v. v) a1_map,
      ra2 a2_dq, tstp_dq, map reopt_table dn)"

fun utss :: "'b gmuaux \<Rightarrow> ts queue" where
  "utss (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) = tss"

lemma dq_hd_s_map_dq: "dq_hd_s (map_dq f d) (f z) = f (dq_hd_s d z)"
  by (simp add: dq_hd_s_def last_map split: list.splits)

lemma dq_hd_s_ra2[simp]:
  "dq_hd_s (ra2 d) Mapping.empty = rmk (\<lambda>v. v) (dq_hd_s d Mapping.empty)"
  using dq_hd_s_map_dq[of "rmk (\<lambda>v. v)" d Mapping.empty] by simp

lemma dq_nth_l_map_dq: "dq_nth_l (map_dq f d) k (f z) = f (dq_nth_l d k z)"
  by (simp add: dq_nth_l_def Let_def)

lemma dq_nth_l_ra2[simp]:
  "dq_nth_l (ra2 d) k Mapping.empty = rmk (\<lambda>v. v) (dq_nth_l d k Mapping.empty)"
  using dq_nth_l_map_dq[of "rmk (\<lambda>v. v)" d k Mapping.empty] by simp

lemma dq_push_empty_ra2[simp]: "dq_push Mapping.empty (ra2 d) = ra2 (dq_push Mapping.empty d)"
  using map_dq_push[of "rmk (\<lambda>v. v)" Mapping.empty d] by simp

lemma dq_upd_empty_ra2[simp]: "dq_upd (ra2 d) k Mapping.empty = ra2 (dq_upd d k Mapping.empty)"
  using map_dq_upd[of "rmk (\<lambda>v. v)" d k Mapping.empty] by simp

lemma rmk_combine_id[simp]:
  "Mapping.combine g (rmk (\<lambda>v. v) m1) (rmk (\<lambda>v. v) m2) = rmk (\<lambda>v. v) (Mapping.combine g m1 m2)"
  by (rule rmk_combine) simp

lemma if_rmk[simp]: "(if b then rmk f X else rmk f Y) = rmk f (if b then X else Y)"
  by simp

lemma if_empty_rmk[simp]:
  "(if b then Mapping.empty else rmk f m) = rmk f (if b then Mapping.empty else m)"
  by simp

lemma filter_lookup_rmk[simp]:
  "Set.filter (\<lambda>x. case Mapping.lookup (rmk (\<lambda>v. v) m) x of Some v \<Rightarrow> Q v | None \<Rightarrow> False)
     (reopt_table Y)
   = reopt_table (Set.filter (\<lambda>x. case Mapping.lookup m x of Some v \<Rightarrow> Q v | None \<Rightarrow> False) Y)"
  by (auto simp: reopt_table_def split: option.splits)

text \<open>The same, in the shape the simplifier gives the expired tuples of a step.\<close>

lemma Collect_lookup_rmk[simp]:
  "{a. (\<exists>x \<in> set xs. a \<in> reopt_table (f x)) \<and>
      (case Mapping.lookup (rmk (\<lambda>v. v) m) a of None \<Rightarrow> False | Some v \<Rightarrow> Q v)}
   = reopt_table {a. (\<exists>x \<in> set xs. a \<in> f x) \<and>
      (case Mapping.lookup m a of None \<Rightarrow> False | Some v \<Rightarrow> Q v)}"
  by (auto simp: reopt_table_def split: option.splits intro!: imageI)

lemma rtt_pred: "(\<lambda>x. (\<lambda>(X, s). P s) (rtt x)) = (\<lambda>(X, s). P s)"
  by (auto simp: fun_eq_iff)

lemma takedropWhile_queue_rtbl[simp]:
  "takedropWhile_queue (\<lambda>(X, s). P s) (rtbl q)
   = map_prod rtbl (map rtt) (takedropWhile_queue (\<lambda>(X, s). P s) q)"
  unfolding takedropWhile_queue_map_queue rtt_pred ..

lemma append_queue_rtbl[simp]:
  "append_queue (reopt_table X, s) (rtbl q) = rtbl (append_queue (X, s) q)"
  using append_queue_map_queue[of rtt "(X, s)" q] by simp

lemma UN_fst_rtt[simp]:
  "\<Union> (set (map fst (map rtt xs))) = reopt_table (\<Union> (set (map fst xs)))"
  "\<Union> ((reopt_table \<circ> f) ` S) = reopt_table (\<Union> (f ` S))"
  "\<Union> ((\<lambda>x. reopt_table (f x)) ` S) = reopt_table (\<Union> (f ` S))"
  by (auto simp: reopt_table_def)

lemma gupd_nested_step_dq_ra2[simp]:
  "gupd_nested_step_dq base d g (t, reopt k) (ra2 dq)
   = ra2 (gupd_nested_step_dq base d g (t, k) dq)"
  by (auto simp: gupd_nested_step_dq_def Let_def split: option.splits)

lemma guntil_step_dq_racc:
  "guntil_step_dq P d t0 (t, reopt as) (reopt_table tbl, ra2 a2)
   = (case guntil_step_dq P d t0 (t, as) (tbl, a2) of
        (tbl', a2') \<Rightarrow> (reopt_table tbl', ra2 a2'))"
  by (simp add: guntil_step_dq_def)

lemma guntil_elem_step_dq_racc:
  "guntil_elem_step_dq (rmk (\<lambda>v. v) a1) msk pos tp len inz P d (reopt as)
     (reopt_table tbl, ra2 a2)
   = (case guntil_elem_step_dq a1 msk pos tp len inz P d as (tbl, a2) of
        (tbl', a2') \<Rightarrow> (reopt_table tbl', ra2 a2'))"
  by (auto simp: guntil_elem_step_dq_def Let_def guntil_step_dq_racc
      split: option.splits prod.splits)

lemma fold_guntil_elem_step_dq_racc:
  "fold (guntil_elem_step_dq (rmk (\<lambda>v. v) a1) msk pos tp len inz P d) (map reopt xs)
     (reopt_table tbl, ra2 a2)
   = (case fold (guntil_elem_step_dq a1 msk pos tp len inz P d) xs (tbl, a2) of
        (tbl', a2') \<Rightarrow> (reopt_table tbl', ra2 a2'))"
proof (induct xs arbitrary: tbl a2)
  case (Cons x xs)
  obtain tbl' a2'
    where s: "guntil_elem_step_dq a1 msk pos tp len inz P d x (tbl, a2) = (tbl', a2')"
    by (metis prod.exhaust)
  show ?case by (simp add: guntil_elem_step_dq_racc s Cons)
qed simp

lemma fold_guntil_elem_step_dq_racc0:
  "fold (guntil_elem_step_dq (rmk (\<lambda>v. v) a1) msk pos tp len inz P d) (map reopt xs)
     ({}, ra2 a2)
   = (case fold (guntil_elem_step_dq a1 msk pos tp len inz P d) xs ({}, a2) of
        (tbl', a2') \<Rightarrow> (reopt_table tbl', ra2 a2'))"
  using fold_guntil_elem_step_dq_racc[where tbl = "{}"] by simp

lemma geval_step_dq_rmuaux:
  assumes ne: "linearize (utss d) \<noteq> []"
  shows "geval_step_dq args (rmuaux d) = rmuaux (geval_step_dq args d)"
    and "linearize (utss (geval_step_dq args d)) = tl (linearize (utss d))"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: gmuaux_cases)
  obtain h tss' where sh: "safe_hd tss = (h, tss')" by (cases "safe_hd tss")
  obtain ts where h: "h = Some ts"
    using safe_hd_rep[OF sh] ne unfolding d by (cases h) auto
  obtain h2 tss'' where sh2: "safe_hd (tl_queue tss') = (h2, tss'')" by (cases "safe_hd (tl_queue tss')")
  have l: "linearize tss'' = tl (linearize tss)"
    using safe_hd_rep[OF sh] safe_hd_rep[OF sh2] by (simp add: tl_queue_rep)
  show "geval_step_dq args (rmuaux d) = rmuaux (geval_step_dq args d)"
    unfolding d rmuaux.simps geval_step_dq.simps sh h
    by (cases h2) (simp_all add: Let_def sh2 split: prod.splits)
  show "linearize (utss (geval_step_dq args d)) = tl (linearize (utss d))"
    unfolding d geval_step_dq.simps sh h
    by (auto simp: Let_def sh2 l split: prod.splits option.splits)
qed

lemma foldl_geval_step_dq_rmuaux:
  "length xs \<le> length (linearize (utss d)) \<Longrightarrow>
   foldl (\<lambda>aux _. geval_step_dq args aux) (rmuaux d) xs
   = rmuaux (foldl (\<lambda>aux _. geval_step_dq args aux) d xs)"
proof (induct xs arbitrary: d)
  case (Cons x xs)
  have ne: "linearize (utss d) \<noteq> []" using Cons.prems by auto
  have l: "length xs \<le> length (linearize (utss (geval_step_dq args d)))"
    using Cons.prems geval_step_dq_rmuaux(2)[OF ne] by simp
  show ?case by (simp add: geval_step_dq_rmuaux(1)[OF ne] Cons.hyps[OF l])
qed simp

lemma gshift_dq_rmuaux: "gshift_dq args nt (rmuaux d) = rmuaux (gshift_dq args nt d)"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where d: "d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases d rule: gmuaux_cases)
  obtain tq tss' where tw: "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss = (tq, tss')"
    by (cases "takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss")
  have l: "length (linearize tq) \<le> length (linearize tss')"
    using takeWhile_queue_rep_fst[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
      takeWhile_queue_rep_snd[of "\<lambda>t. \<not> memR (args_ivl args) (nt - t)" tss]
    unfolding tw by (simp add: length_takeWhile_le)
  let ?s = "(tp, tss', tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
  have "length (linearize tq) \<le> length (linearize (utss ?s))" using l by simp
  note f = foldl_geval_step_dq_rmuaux[OF this, unfolded rmuaux.simps]
  show ?thesis unfolding d gshift_dq.simps rmuaux.simps tw by (simp add: Let_def f)
qed

lemma geval_dq_rmuaux:
  "geval_dq args nt (rmuaux d)
   = (case geval_dq args nt d of (zs, d') \<Rightarrow> (map reopt_table zs, rmuaux d'))"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where s: "gshift_dq args nt d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases "gshift_dq args nt d" rule: gmuaux_cases)
  show ?thesis unfolding geval_dq.simps gshift_dq_rmuaux s by (simp add: Let_def rev_map)
qed

lemma glength_dq_rmuaux: "glength_dq args (rmuaux d) = glength_dq args d"
  by (cases d rule: gmuaux_cases) simp

lemma ginit_dq_rmuaux: "ginit_dq args = rmuaux (ginit_dq args)"
  by (simp add: ginit_dq_def dq_push_def map_dq_def dq_empty_def)

lemma gadd_new_dq_rmuaux:
  "gadd_new_dq args msk (reopt_table rel1) (reopt_table rel2) nt (rmuaux d)
   = rmuaux (gadd_new_dq args msk rel1 rel2 nt d)"
proof -
  obtain tp tss tables len mL mR result a1_map a2_dq tstp_dq dn
    where s: "gshift_dq args nt d = (tp, tss, tables, len, mL, mR, result, a1_map, a2_dq, tstp_dq, dn)"
    by (cases "gshift_dq args nt d" rule: gmuaux_cases)
  show ?thesis
    unfolding gadd_new_dq_def gshift_dq_rmuaux s
    by (auto simp: Let_def csl_reopt_table fold_guntil_elem_step_dq_racc0 split: prod.splits)
qed

subsection \<open>The Until window\<close>

text \<open>The window for a closed left operand, on short tuples, with the generic count set.\<close>

type_synonym uuw_entry = "ts \<times> event_data list set \<times> bool"

type_synonym uuwaux = "ts queue \<times> uuw_entry queue \<times> uuw_entry queue \<times> nat \<times> bool \<times>
  event_data gcntset \<times> event_data list set list"

function uuw_extend :: "args \<Rightarrow> ts \<Rightarrow> uuw_entry queue \<Rightarrow> uuw_entry queue \<Rightarrow> bool \<Rightarrow>
    event_data gcntset \<Rightarrow> uuw_entry queue \<times> uuw_entry queue \<times> bool \<times> event_data gcntset" where
  "uuw_extend args ts0 win rest bend cc =
     (if \<not> bend then (win, rest, bend, cc)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cc)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then uuw_extend args ts0 (append_queue e win) (tl_queue rest')
                        (snd (snd e)) (gcnt_add (fst (snd e)) cc)
                 else (win, rest', bend, cc))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, ts0, win, rest, bend, cc). length (linearize rest))")
     (fastforce split: prod.splits)+

declare uuw_extend.simps[simp del]

definition uuw_init :: "args \<Rightarrow> uuwaux" where
  "uuw_init args = (empty_queue, empty_queue, empty_queue, 0, True, (Mapping.empty, {}), [])"

definition uuw_length :: "args \<Rightarrow> uuwaux \<Rightarrow> nat" where
  "uuw_length args aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow> length dn + len)"

definition uuw_step :: "args \<Rightarrow> ts \<Rightarrow> uuwaux \<Rightarrow> uuwaux" where
  "uuw_step args ts0 aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (case uuw_extend args ts0 win rest bend cc of (win, rest, bend, cc) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow> (tl_queue nts, win', rest, len - 1, bend, cc, {} # dn)
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                cc' = gcnt_del (fst (snd e)) cc;
                bend' = (if Queue.is_empty win'' then True else bend)
            in (tl_queue nts, win'', rest, len - 1, bend', cc', snd cc # dn)))))"

function uuw_shift :: "args \<Rightarrow> ts \<Rightarrow> uuwaux \<Rightarrow> uuwaux" where
  "uuw_shift args nt aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> (nts', win, rest, len, bend, cc, dn)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then (nts', win, rest, len, bend, cc, dn)
         else uuw_shift args nt (uuw_step args ts0 (nts', win, rest, len, bend, cc, dn)))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(args, nt, (nts, win, rest, len, bend, cc, dn)). len)")
     (auto simp: uuw_step_def Let_def split: prod.splits option.splits)

declare uuw_shift.simps[simp del]

definition uuw_add_new :: "args \<Rightarrow> event_data list set \<Rightarrow> event_data list set \<Rightarrow> ts \<Rightarrow>
    uuwaux \<Rightarrow> uuwaux" where
  "uuw_add_new args rel1 rel2 nt aux =
     (case uuw_shift args nt aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in (append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn)))"

definition uuw_eval :: "args \<Rightarrow> ts \<Rightarrow> uuwaux \<Rightarrow> event_data list set list \<times> uuwaux" where
  "uuw_eval args nt aux =
     (case uuw_shift args nt aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
       (rev dn, (nts, win, rest, len, bend, cc, [])))"

text \<open>Its naturality.\<close>

abbreviation rte :: "uuw_entry \<Rightarrow> uw_entry" where
  "rte \<equiv> map_prod (\<lambda>t. t) (map_prod reopt_table (\<lambda>b. b))"

abbreviation rqe :: "uuw_entry queue \<Rightarrow> uw_entry queue" where
  "rqe \<equiv> map_queue rte"

fun ruw :: "uuwaux \<Rightarrow> uwaux" where
  "ruw (nts, win, rest, len, bend, cc, dn)
   = (nts, rqe win, rqe rest, len, bend, rcc cc, map reopt_table dn)"

declare ruw.simps[simp del]

lemma snd_rcc[simp]: "snd (rcc cc) = reopt_table (snd cc)"
  by (cases cc) (simp add: rcc.simps)

lemma append_queue_rqe[simp]:
  "append_queue (t, reopt_table X, b) (rqe q) = rqe (append_queue (t, X, b) q)"
  using append_queue_map_queue[of rte "(t, X, b)" q] by simp

lemma uw_extend_ruw:
  "uw_extend args ts0 (rqe win) (rqe rest) bend (rcc cc)
   = (case uuw_extend args ts0 win rest bend cc of
        (win', rest', bend', cc') \<Rightarrow> (rqe win', rqe rest', bend', rcc cc'))"
proof (induct args ts0 win rest bend cc rule: uuw_extend.induct)
  case (1 args ts0 win rest bend cc)
  obtain h rest' where sh: "safe_hd rest = (h, rest')" by (cases "safe_hd rest")
  show ?case
  proof (cases h)
    case None
    then show ?thesis by (subst uw_extend.simps, subst uuw_extend.simps) (simp add: sh)
  next
    case (Some e)
    obtain te Xe be where e: "e = (te, Xe, be)" by (metis prod_cases3)
    note IH = 1[OF _ sh[symmetric] Some, unfolded e, simplified]
    show ?thesis
      by (subst uw_extend.simps, subst uuw_extend.simps)
        (auto simp: sh Some e IH split: prod.splits)
  qed
qed

lemma uw_step_ruw: "uw_step args ts0 (ruw w) = ruw (uuw_step args ts0 w)"
proof -
  obtain nts win rest len bend cc dn where w: "w = (nts, win, rest, len, bend, cc, dn)"
    by (cases w) auto
  obtain win' rest' bend' cc' where e: "uuw_extend args ts0 win rest bend cc = (win', rest', bend', cc')"
    by (metis prod_cases4)
  obtain h win'' where sh: "safe_hd win' = (h, win'')" by (cases "safe_hd win'")
  show ?thesis
  proof (cases h)
    case None
    then show ?thesis
      unfolding w by (simp add: uw_step_def uuw_step_def ruw.simps uw_extend_ruw e sh)
  next
    case (Some x)
    obtain tx Xx bx where x: "x = (tx, Xx, bx)" by (metis prod_cases3)
    show ?thesis
      unfolding w by (simp add: uw_step_def uuw_step_def ruw.simps uw_extend_ruw e sh Some x Let_def)
  qed
qed

lemma uw_shift_ruw: "uw_shift args nt (ruw w) = ruw (uuw_shift args nt w)"
proof (induct args nt w rule: uuw_shift.induct)
  case (1 args nt w)
  obtain nts win rest len bend cc dn where w: "w = (nts, win, rest, len, bend, cc, dn)"
    by (cases w) auto
  obtain h nts' where sh: "safe_hd nts = (h, nts')" by (cases "safe_hd nts")
  show ?case
  proof (cases h)
    case None
    then show ?thesis
      unfolding w by (subst uw_shift.simps, subst uuw_shift.simps) (simp add: ruw.simps sh)
  next
    case (Some ts0)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - ts0) \<or> len = 0")
      case True
      then show ?thesis
        unfolding w by (subst uw_shift.simps, subst uuw_shift.simps) (simp add: ruw.simps sh Some)
    next
      case False
      note IH = 1[OF w[symmetric] refl refl refl refl refl sh[symmetric] Some False]
      have "uw_shift args nt (ruw w)
          = uw_shift args nt (uw_step args ts0 (ruw (nts', win, rest, len, bend, cc, dn)))"
        unfolding w by (subst uw_shift.simps) (simp add: ruw.simps sh Some False)
      also have "\<dots> = uw_shift args nt (ruw (uuw_step args ts0 (nts', win, rest, len, bend, cc, dn)))"
        by (simp only: uw_step_ruw)
      also have "\<dots> = ruw (uuw_shift args nt (uuw_step args ts0 (nts', win, rest, len, bend, cc, dn)))"
        by (rule IH)
      also have "\<dots> = ruw (uuw_shift args nt w)"
        unfolding w by (subst (2) uuw_shift.simps) (simp add: sh Some False)
      finally show ?thesis .
    qed
  qed
qed

lemma uw_init_ruw: "uw_init args = ruw (uuw_init args)"
  by (simp add: uw_init_def uuw_init_def ruw.simps rcc.simps)

lemma uw_length_ruw: "uw_length args (ruw w) = uuw_length args w"
  by (cases w) (simp add: uw_length_def uuw_length_def ruw.simps)

lemma uw_add_new_ruw:
  "uw_add_new args (reopt_table rel1) (reopt_table rel2) nt (ruw w)
   = ruw (uuw_add_new args rel1 rel2 nt w)"
proof -
  obtain nts win rest len bend cc dn
    where s: "uuw_shift args nt w = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uuw_shift args nt w") auto
  show ?thesis
    unfolding uw_add_new_def uuw_add_new_def uw_shift_ruw s by (simp add: ruw.simps Let_def)
qed

lemma uw_eval_ruw:
  "uw_eval args nt (ruw w) = (case uuw_eval args nt w of (zs, w') \<Rightarrow> (map reopt_table zs, ruw w'))"
proof -
  obtain nts win rest len bend cc dn
    where s: "uuw_shift args nt w = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uuw_shift args nt w") auto
  show ?thesis
    unfolding uw_eval_def uuw_eval_def uw_shift_ruw s by (simp add: ruw.simps rev_map)
qed

section \<open>The kernel's trigger structure over short tuples\<close>

subsection \<open>The trigger structure at the short element type\<close>

text \<open>
  The second half of the trigger's naturality, and the one the evaluator's own state needs.
  @{const tmm} widens the left operand's frame, and is a statement about a state that is narrow;
  this map only puts the option back on every tuple the structure holds.  It is a relabelling,
  so it commutes with the operations on every input, with no invariant at all -- as the other
  structures of this theory do, and as @{text udeval_Rep} needs, being unconditional itself.
\<close>

abbreviation rtq3 :: "ts \<times> event_data list set \<times> event_data list set \<Rightarrow>
    ts \<times> event_data table \<times> event_data table" where
  "rtq3 \<equiv> (\<lambda>(t, l, r). (t, reopt_table l, reopt_table r))"

abbreviation rq3 :: "(ts \<times> event_data list set \<times> event_data list set) queue \<Rightarrow>
    (ts \<times> event_data table \<times> event_data table) queue" where
  "rq3 \<equiv> map_queue rtq3"

fun bmm :: "event_data gmmtaux \<Rightarrow> event_data option gmmtaux" where
  "bmm (cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tuple_in_once,
        tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)
   = (cur, idx_next, idx_mid, idx_oldest, msk, rq3 data_prev, rq data_in,
      rmk (\<lambda>v. v) tuple_in_once, reopt_table tuple_in_once_keys,
      rmk (\<lambda>v. v) tuple_since_hist, reopt_table hist_sat, reopt_table since_sat)"

declare bmm.simps[simp del]

lemma rtq3_pred: "(\<lambda>x. (\<lambda>(t, _). P t) (rtq3 x)) = (\<lambda>(t, _). P t)"
  by (auto simp: fun_eq_iff)

lemma takedropWhile_queue_rq3[simp]:
  "takedropWhile_queue (\<lambda>(t, _). P t) (rq3 q)
   = map_prod rq3 (map rtq3) (takedropWhile_queue (\<lambda>(t, _). P t) q)"
  unfolding takedropWhile_queue_map_queue rtq3_pred ..

lemma append_queue_rq3[simp]:
  "append_queue (t, reopt_table l, reopt_table r) (rq3 q) = rq3 (append_queue (t, l, r) q)"
  using append_queue_map_queue[of rtq3 "(t, l, r)" q] by simp

lemma filter_rtq3: "filter (\<lambda>(t, _). P t) (map rtq3 xs) = map rtq3 (filter (\<lambda>(t, _). P t) xs)"
  by (induct xs) (auto split: prod.splits)

lemma fold_append_r_rtq3:
  "fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) (map rtq3 xs) (rq q)
   = rq (fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) xs q)"
  by (induct xs arbitrary: q) (auto split: prod.splits)

text \<open>The semi-join is a filter on a projection, and both commute with the relabelling.\<close>

lemma gsemi_join_reopt[simp]:
  "gsemi_join msk pos (reopt_table r) (reopt_table l) = reopt_table (gsemi_join msk pos r l)"
proof (cases "\<forall>i \<in> set msk. i")
  case True
  show ?thesis unfolding gsemi_join_def if_P[OF True] by simp
next
  case f1: False
  show ?thesis
  proof (cases "\<forall>i \<in> set msk. \<not> i")
    case True
    show ?thesis unfolding gsemi_join_def if_not_P[OF f1] if_P[OF True] by simp
  next
    case f2: False
    have ds: "dsemi msk pos (reopt_table r) (reopt_table l) = reopt_table (dsemi msk pos r l)"
      by (auto simp: dsemi_def reopt_table_def image_iff)
    show ?thesis
      unfolding gsemi_join_def if_not_P[OF f1] if_not_P[OF f2] ds ..
  qed
qed

text \<open>The fold that expires the left operand's records, relabelled.\<close>

lemma fold_filter_once_bmm:
  "fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in,
       {as \<in> tuple_in_keys. filter_cond' (fst X) tuple_in t as}))
      (map rtq3 ds) (rmk (\<lambda>v. v) tio, reopt_table keys)
    = map_prod (rmk (\<lambda>v. v)) reopt_table (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in,
       {as \<in> tuple_in_keys. filter_cond' (fst X) tuple_in t as})) ds (tio, keys))"
proof (induction ds arbitrary: tio keys)
  case (Cons d ds)
  obtain t l r where d: "d = (t, l, r)" by (cases d) auto
  have pc: "filter_cond (reopt_table l) (rmk (\<lambda>v. v) tio) t (reopt k) v = filter_cond l tio t k v"
    for k v by (simp add: option.map_ident)
  have f1: "Mapping.filter (filter_cond (reopt_table l) (rmk (\<lambda>v. v) tio) t) (rmk (\<lambda>v. v) tio)
      = rmk (\<lambda>v. v) (Mapping.filter (filter_cond l tio t) tio)"
    by (simp only: rmk_filter) (simp add: pc)
  have f2: "{as \<in> reopt_table keys. filter_cond' (reopt_table l) (rmk (\<lambda>v. v) tio) t as}
      = reopt_table {as \<in> keys. filter_cond' l tio t as}"
    by (auto simp: reopt_table_def image_iff option.map_ident)
  show ?case
    unfolding d list.map fold.simps comp_apply prod.case fst_conv f1 f2
    by (rule Cons.IH)
qed simp

lemma shift_end'_bmm:
  "(case shift_end' I nt fst (empty_queue :: (ts \<times> event_data table \<times> event_data table) queue,
        rq3 data_prev, rmk (\<lambda>v. v) tio, reopt_table keys) of
      (q0, dp', move, tio', keys') \<Rightarrow> (dp', move, tio', keys'))
   = (case shift_end' I nt fst
        (empty_queue :: (ts \<times> event_data list set \<times> event_data list set) queue,
         data_prev, tio, keys) of
      (q0, dp', move, tio', keys') \<Rightarrow>
        (rq3 dp', map rtq3 move, rmk (\<lambda>v. v) tio', reopt_table keys'))"
proof -
  obtain dp' move where tdq: "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_prev
      = (dp', move)"
    by (cases "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_prev")
  have td: "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) (rq3 data_prev)
      = (rq3 dp', map rtq3 move)"
    by (simp only: takedropWhile_queue_rq3 tdq map_prod_simp)
  show ?thesis
    by (auto simp only: shift_end'.simps Let_def td tdq fold_filter_once_bmm
        map_prod_simp prod.case split: prod.splits)
qed

text \<open>The fold over the time points that enter the interval, relabelled.\<close>

lemma fold_hist_bmm:
  "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat = hist_sat \<inter> r;
          since_sat = since_sat \<inter> r
      in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
          hist_sat, idx_move + 1, since_sat \<union> gsemi_join msk pos r l))
      (map rtq3 move) (rmk (\<lambda>v. v) tsh, reopt_table hs, idx, reopt_table ss)
   = (case fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat = hist_sat \<inter> r;
          since_sat = since_sat \<inter> r
      in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
          hist_sat, idx_move + 1, since_sat \<union> gsemi_join msk pos r l))
      move (tsh, hs, idx, ss) of
        (tsh', hs', i', ss') \<Rightarrow> (rmk (\<lambda>v. v) tsh', reopt_table hs', i', reopt_table ss'))"
proof (induction move arbitrary: tsh hs idx ss)
  case (Cons m move)
  then show ?case
    by (cases m) (simp add: Cons.IH rmk_filter Let_def split: prod.splits)
qed simp

text \<open>The read that closes the update: the new @{text hist_sat} is read off the head of the
  in-window queue, whose tuples the relabelling has already put the option back on.\<close>

lemma hist_sat_bmm:
  "(case fst (safe_hd (rq q)) of None \<Rightarrow> {}
      | Some db \<Rightarrow> reopt_table hs \<union> {tuple \<in> snd db.
          case Mapping.lookup (rmk (\<lambda>v. v) m) tuple of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> i})
   = reopt_table (case fst (safe_hd q) of None \<Rightarrow> {}
      | Some db \<Rightarrow> hs \<union> {tuple \<in> snd db.
          case Mapping.lookup m tuple of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> i})"
proof (cases "fst (safe_hd q)")
  case None
  then show ?thesis by simp
next
  case (Some db)
  have "{tuple \<in> reopt_table (snd db). case Mapping.lookup (rmk (\<lambda>v. v) m) tuple of
        None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> i}
      = reopt_table {tuple \<in> snd db.
        case Mapping.lookup m tuple of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> i}"
    by (auto simp: reopt_table_def image_iff option.map_ident)
  with Some show ?thesis by simp
qed

lemma gupdate_mmtaux'_bmm:
  "gupdate_mmtaux' args nt idx_mid idx_oldest msk (rq3 data_prev) (rq data_in)
      (rmk (\<lambda>v. v) tio) (reopt_table keys) (rmk (\<lambda>v. v) tsh) (reopt_table hs) (reopt_table ss)
   = (case gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss of
       (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss') \<Rightarrow>
         (idx_mid', idx_oldest', rq3 data_prev', rq data_in', rmk (\<lambda>v. v) tio',
          reopt_table keys', rmk (\<lambda>v. v) tsh', reopt_table hs', reopt_table ss'))"
proof -
  obtain q0 dp' move tio' keys' where se:
    "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> event_data list set \<times> event_data list set) queue,
         data_prev, tio, keys) = (q0, dp', move, tio', keys')"
    by (metis surj_pair)
  obtain q0b where seb:
    "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> event_data table \<times> event_data table) queue,
         rq3 data_prev, rmk (\<lambda>v. v) tio, reopt_table keys)
      = (q0b, rq3 dp', map rtq3 move, rmk (\<lambda>v. v) tio', reopt_table keys')"
  proof -
    obtain q0b dpb moveb tiob keysb where b:
      "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
          (empty_queue :: (ts \<times> event_data table \<times> event_data table) queue,
           rq3 data_prev, rmk (\<lambda>v. v) tio, reopt_table keys)
        = (q0b, dpb, moveb, tiob, keysb)"
      by (metis surj_pair)
    have "(dpb, moveb, tiob, keysb)
        = (rq3 dp', map rtq3 move, rmk (\<lambda>v. v) tio', reopt_table keys')"
      using shift_end'_bmm[of "flip_int_less_lower (args_ivl args)" nt data_prev tio keys]
      by (simp only: se b prod.case)
    with b show thesis by (auto intro: that)
  qed
  obtain di' drop where td:
    "takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in = (di', drop)"
    by (cases "takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in")
  have tdb: "takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (rq data_in)
      = (rq di', map rtq drop)"
    by (simp only: takedropWhile_queue_rq td map_prod_simp)
  obtain tsh2 hs2 idx2 ss2 where fh:
    "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
       (upd_set (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist) (\<lambda>_. idx_move)
          (r - Mapping.keys (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist)),
        hist_sat \<inter> r, idx_move + 1, since_sat \<inter> r \<union> gsemi_join msk (args_pos args) r l))
       move (tsh, hs, idx_mid, ss) = (tsh2, hs2, idx2, ss2)"
    by (cases "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
       (upd_set (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist) (\<lambda>_. idx_move)
          (r - Mapping.keys (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist)),
        hist_sat \<inter> r, idx_move + 1, since_sat \<inter> r \<union> gsemi_join msk (args_pos args) r l))
       move (tsh, hs, idx_mid, ss)") auto
  show ?thesis
    by (simp only: gupdate_mmtaux'_def Let_def se seb td tdb prod.case
        filter_rtq3 length_map fold_append_r_rtq3 fold_hist_bmm[unfolded Let_def] fh
        reopt_table_simps if_empty_rmk hist_sat_bmm)
      simp
qed

lemma gupdate_mmtaux_bmm:
  "gupdate_mmtaux args nt (reopt_table l) (reopt_table r) (bmm ax)
   = bmm (gupdate_mmtaux args nt l r ax)"
proof -
  obtain cur idx_next idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (metis surj_pair)
  obtain idx_mid' idx_oldest' dp' di' tio' keys' tsh' hs' ss' where g:
    "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
      = (idx_mid', idx_oldest', dp', di', tio', keys', tsh', hs', ss')"
    by (metis surj_pair)
  show ?thesis
    unfolding ax bmm.simps gupdate_mmtaux_def prod.case
    by (simp only: gupdate_mmtaux'_bmm g prod.case Let_def
        append_queue_rq append_queue_rq3 rmk_filter keys_rmk rmk_upd_set_id
        reopt_table_simps gsemi_join_reopt is_empty_map_queue)
      (simp add: bmm.simps)
qed

lemma gresult_mmtaux_bmm: "gresult_mmtaux args (bmm ax) = reopt_table (gresult_mmtaux args ax)"
  by (cases ax rule: bmm.cases) (simp add: gresult_mmtaux_def bmm.simps)

lemma gmmtaux_empty_bmm: "gmmtaux_empty (bmm ax) = gmmtaux_empty ax"
  by (cases ax rule: bmm.cases) (simp add: gmmtaux_empty_def bmm.simps)

lemma ginit_mmtaux_bmm: "ginit_mmtaux args msk = bmm (ginit_mmtaux args msk)"
  by (simp add: ginit_mmtaux_def bmm.simps)

(*<*)
end
(*>*)
