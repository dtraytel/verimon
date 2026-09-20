(*<*)
theory Dense_Unbox_Eval
  imports Dense_Exec Dense_Unbox
begin
(*>*)

section \<open>The verified dense evaluator, without the option\<close>

text \<open>
  @{const edeval} of @{theory MFODL_Monitor_Imp.Dense_Exec} is the verified dense evaluator with
  its buffers in queues; its tables are the kernel's, @{typ "event_data option list set"}, and a
  dense tuple never has a hole.  This theory states the evaluator once more over
  @{typ "event_data list set"} and proves that on a formula whose tables are the short ones with
  the option put back, @{const edeval} computes what the short evaluator computes with the option
  put back.  The proof is a naturality argument, node by node: every operation the evaluator
  runs commutes with @{const reopt_table}.  The operations that read a field are
  @{theory MFODL_Monitor_Imp.Dense_Utuple}'s twins read through @{const deopt}, so for them the
  commutation is by definition; the ones that move fields are the generic ones of
  @{theory MFODL_Monitor_Imp.Dense_Unbox} and @{theory MFODL_Monitor_Imp.Dense_Until_Gen}, whose
  commutation is proved here from that of the containers they are built from.  No invariant is
  needed: the operations were stated in @{theory MFODL_Monitor_Imp.Dense_Utuple} and
  @{theory MFODL_Monitor_Imp.Dense_Until_Gen} precisely so that the commutation holds on every
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

subsubsection \<open>Queues\<close>

lift_definition map_queue :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a queue \<Rightarrow> 'b queue" is
  "\<lambda>f (fs, ls). (map f fs, map f ls)"
  by (auto simp: queue_invariant_def split: list.splits)

lemma linearize_map_queue[simp]: "linearize (map_queue f q) = map f (linearize q)"
  by transfer (auto simp: rev_map split: prod.splits)

lemma map_queue_empty[simp]: "map_queue f empty_queue = empty_queue"
  by transfer simp

lemma is_empty_map_queue[simp]: "Queue.is_empty (map_queue f q) = Queue.is_empty q"
  by transfer (auto split: prod.splits list.splits)

lemma append_queue_map_queue[simp]:
  "append_queue (f x) (map_queue f q) = map_queue f (append_queue x q)"
  by transfer (auto split: prod.splits)

lemma prepend_queue_map_queue[simp]:
  "prepend_queue (f x) (map_queue f q) = map_queue f (prepend_queue x q)"
  by transfer (auto simp: queue_invariant_def split: prod.splits list.splits)

lemma safe_hd_map_queue[simp]:
  "safe_hd (map_queue f q) = map_prod (map_option f) (map_queue f) (safe_hd q)"
proof (transfer, goal_cases)
  case (1 f q)
  then show ?case
    by (cases q rule: safe_hd_t.cases)
      (simp_all add: Let_def rev_map hd_map queue_invariant_def hd_append)
qed

lemma tl_queue_map_queue[simp]: "tl_queue (map_queue f q) = map_queue f (tl_queue q)"
proof (transfer, goal_cases)
  case (1 f q)
  then show ?case
    by (cases q rule: tl_queue_t.cases) (simp_all add: rev_map map_tl queue_invariant_def)
qed

lemma dropWhile_queue_map_queue:
  "dropWhile_queue P (map_queue f q) = map_queue f (dropWhile_queue (\<lambda>x. P (f x)) q)"
proof (induct "\<lambda>x. P (f x)" q rule: dropWhile_queue.induct)
  case (1 q)
  then show ?case
    by (subst dropWhile_queue.simps, subst (2) dropWhile_queue.simps)
      (auto split: prod.splits option.splits)
qed

lemma takeWhile_queue_map_queue:
  "takeWhile_queue P (map_queue f q)
   = map_prod (map_queue f) (map_queue f) (takeWhile_queue (\<lambda>x. P (f x)) q)"
proof (induct "\<lambda>x. P (f x)" q rule: takeWhile_queue.induct)
  case (1 q)
  then show ?case
    by (subst takeWhile_queue.simps, subst (2) takeWhile_queue.simps)
      (auto simp: Let_def split: prod.splits option.splits)
qed

lemma map_queue_inj: "map_queue reopt q = map_queue reopt q' \<longleftrightarrow> q = q'"
  by transfer (auto simp: inj_map_eq_map inj_reopt split: prod.splits)

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
  by transfer simp

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

text \<open>The index algebra of @{theory MFODL_Monitor_Imp.Dense_Aux}.\<close>

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

lemma takedropWhile_queue_map_queue:
  "takedropWhile_queue P (map_queue f q)
   = map_prod (map_queue f) (map f) (takedropWhile_queue (\<lambda>x. P (f x)) q)"
proof (induct "\<lambda>x. P (f x)" q rule: takedropWhile_queue.induct)
  case (1 q)
  then show ?case
    by (subst takedropWhile_queue.simps, subst (2) takedropWhile_queue.simps)
      (auto split: prod.splits option.splits)
qed

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

text \<open>The window of @{theory MFODL_Monitor_Imp.Dense_Evt}, over a bare element type.  It is the
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

(*<*)
end
(*>*)
