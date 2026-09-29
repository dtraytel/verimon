(*<*)
theory Dense_Mono
  imports Dense_Tree_Code
begin
(*>*)

section \<open>The generic operations left on the monitor's inner loops\<close>

text \<open>
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} gives the kernel's operations at the tuples of
  @{typ event_data} monomorphic copies, in which the comparator of the tuples is
  @{const ed_comparator} rather than the generic comparator on lists, reached through a closure
  for every element compared.  What is left generic comes in three kinds.
  \<^item> Operations at other closed types -- time points, event data, the states of the match
    automata, the values of the rank aggregations -- and the operations at the tuples that the
    kernel's list did not reach.  Each gets a copy, as in the dense evaluator's sweep
    (\<^verbatim>\<open>Dense_Mono_Sweep\<close>, \<^verbatim>\<open>Dense_Mono_Hot\<close>).
  \<^item> The copy @{text ed_join} of the plain join was derived from the join's code equations of
    the time; @{theory MFODL_Monitor_Dense.Kernel_Code} has since replaced those.
  \<^item> Boxes: a box builds the dictionary once and passes it, so the comparator is still the
    generic one.  The hot ones become copies.
\<close>

subsection \<open>The plain join\<close>

declare [[code drop: ed_join]]

lemmas ed_join_code[code] = join_key_code[where 'a = event_data, folded ed_join_def]

subsection \<open>The dictionaries of the remaining closed types\<close>

text \<open>Each family needs its class operations as an explicit equation, so that instantiating a
  code equation at the type can rewrite the dictionary lookups away.  These mirror
  @{thm [source] etuple_dict_simps}.\<close>

lemma ID_ccompare_nat: "ID CCOMPARE(nat) = Some (compare :: nat comparator)"
  by (simp add: ccompare_nat_def ID_Some)
lemma ccompare_nat_Some: "CCOMPARE(nat) = Some (compare :: nat comparator)"
  by (simp add: ccompare_nat_def)
lemma ID_ceq_nat: "ID CEQ(nat) = Some ((=) :: nat \<Rightarrow> _)"
  by (simp add: ceq_nat_def ID_Some)
lemma ceq_nat_Some: "CEQ(nat) = Some ((=) :: nat \<Rightarrow> _)"
  by (simp add: ceq_nat_def)

lemmas nat_dict_simps = ID_ccompare_nat ccompare_nat_Some ID_ceq_nat ceq_nat_Some

lemma ID_ccompare_ed: "ID CCOMPARE(event_data) = Some comparator_event_data"
  by (simp add: ccompare_event_data_def ID_Some)
lemma ccompare_ed_Some: "CCOMPARE(event_data) = Some comparator_event_data"
  by (simp add: ccompare_event_data_def)
lemma ID_ceq_ed: "ID CEQ(event_data) = Some ((=) :: event_data \<Rightarrow> _)"
  by (simp add: ceq_event_data_def ID_Some)
lemma ceq_ed_Some: "CEQ(event_data) = Some ((=) :: event_data \<Rightarrow> _)"
  by (simp add: ceq_event_data_def)

lemmas ed_dict_simps = ID_ccompare_ed ccompare_ed_Some ID_ceq_ed ceq_ed_Some

lemma ID_ccompare_mregex: "ID CCOMPARE(mregex) = Some comparator_mregex"
  by (simp add: ccompare_mregex_def ID_Some)
lemma ccompare_mregex_Some: "CCOMPARE(mregex) = Some comparator_mregex"
  by (simp add: ccompare_mregex_def)
lemma ID_ceq_mregex: "ID CEQ(mregex) = Some ((=) :: mregex \<Rightarrow> _)"
  by (simp add: ceq_mregex_def ID_Some)
lemma ceq_mregex_Some: "CEQ(mregex) = Some ((=) :: mregex \<Rightarrow> _)"
  by (simp add: ceq_mregex_def)

lemmas mregex_dict_simps = ID_ccompare_mregex ccompare_mregex_Some ID_ceq_mregex ceq_mregex_Some

lemma ID_ccompare_s8: "ID CCOMPARE(string8) = Some (compare :: string8 comparator)"
  by (simp add: ccompare_string8_def ID_Some)
lemma ccompare_s8_Some: "CCOMPARE(string8) = Some (compare :: string8 comparator)"
  by (simp add: ccompare_string8_def)
lemma ID_ceq_s8: "ID CEQ(string8) = Some ((=) :: string8 \<Rightarrow> _)"
  by (simp add: ceq_string8_def ID_Some)

lemmas s8_dict_simps = ID_ccompare_s8 ccompare_s8_Some ID_ceq_s8

ML \<open>
val mono = Monomorphize.monomorphize_cmd
val dicts = ["nat_dict_simps", "ed_dict_simps", "mregex_dict_simps", "s8_dict_simps",
             "etuple_dict_simps"]
\<close>

subsection \<open>Time points, event data and the match automata's states\<close>

setup \<open>mono
  [("Set.member", "nat_member", ["nat"]),
   ("Set.remove", "nat_remove", ["nat"]),
   ("List.member", "nat_list_member", ["nat"]),
   ("List.superset", "nat_superset", ["nat"]),
   ("comparator_of", "nat_comparator_of", ["nat"]),
   ("sum_list", "nat_sum_list", ["nat"]),
   ("Max", "nat_Max", ["nat"]),
   ("Rings.dvd_class.dvd", "nat_dvd", ["nat"]),
   ("less_eq :: _ set \<Rightarrow> _", "nat_subset", ["nat"])]
  dicts\<close>

setup \<open>Monomorphize.box_cmd
  [("atLeastLessThan", "nat_atLeastLessThan_v", ["nat"])]\<close>

setup \<open>mono
  [("min", "ed_min", ["event_data"]),
   ("max", "ed_max", ["event_data"])]
  dicts\<close>

setup \<open>mono
  [("Set.bind", "mregex_bind", ["mregex", "mregex"]),
   ("sorted_list_of_set", "mregex_sorted_list_of_set", ["mregex"]),
   ("less_eq :: _ set \<Rightarrow> _", "mregex_subset", ["mregex"]),
   ("Mapping.lookup_default", "mregex_lookup_default", ["mregex", "event_data table"]),
   ("RBT_Mapping2.bulkload", "mregex_rbt_bulkload", ["mregex", "event_data table"]),
   ("Mapping.map_values", "pn_map_values",
      ["string8 \<times> nat", "event_data table", "event_data table"])]
  dicts\<close>

setup \<open>mono
  [("Set.member", "mregex_member", ["mregex"]),
   ("sort_key", "mregex_sort_key", ["mregex", "mregex"])]
  dicts\<close>

subsection \<open>The rank trees of the aggregations\<close>

text \<open>
  The aggregations MIN, MAX and MED keep one order-statistic tree per group
  (@{typ list_aux}, over @{typ "'a treelist"}, over @{typ "'a wf_wbt"}).  Its operations are
  refined here at the level of code equations, with the refinements proved against the
  equations they replace.

  @{const Order_Statistic_Tree.combine} decides which side to take the new root from by
  comparing @{const size}, which walks both subtrees, although every node carries its size;
  and @{const Order_Statistic_Tree.split_min} and @{const del_max} test @{term "l = Leaf"}, an equality on trees,
  which is the only reason the tree operations need an @{class equal} dictionary besides the
  @{class linorder} one.  The copies below read the stored size and match on @{const Leaf}
  instead.  On a tree satisfying @{const wbt}, which every tree inside @{typ "'a wf_wbt"}
  does, they compute the same result.  The subtrees are inspected with a @{text case} rather
  than by nested patterns, which would make the generated code rebuild the inner node.
\<close>

fun split_min_p :: "'a wbt \<Rightarrow> 'a \<times> 'a wbt" where
  "split_min_p (Node l (a, _) r) = (case l of
     Leaf \<Rightarrow> (a, r)
   | Node _ _ _ \<Rightarrow> let (x, l') = split_min_p l in (x, balanceL l' a r))"

fun del_max_p :: "'a wbt \<Rightarrow> 'a \<times> 'a wbt" where
  "del_max_p (Node l (a, _) r) = (case r of
     Leaf \<Rightarrow> (a, l)
   | Node _ _ _ \<Rightarrow> let (x, r') = del_max_p r in (x, balanceR l a r'))"

lemma split_min_p_eq: "t \<noteq> Leaf \<Longrightarrow> split_min_p t = Order_Statistic_Tree.split_min t"
  by (induction t rule: split_min_p.induct) (auto split: tree.split)

lemma del_max_p_eq: "t \<noteq> Leaf \<Longrightarrow> del_max_p t = del_max t"
  by (induction t rule: del_max_p.induct) (auto split: tree.split)

definition combine_p :: "'a wbt \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
  "combine_p l r = (case l of
     Leaf \<Rightarrow> r
   | Node _ _ _ \<Rightarrow> (case r of
       Leaf \<Rightarrow> l
     | Node _ _ _ \<Rightarrow>
         if size_wbt l > size_wbt r then
           let (lMax, l') = del_max_p l in balanceL l' lMax r
         else
           let (rMin, r') = split_min_p r in balanceR l rMin r'))"

lemma combine_p_eq: "wbt l \<Longrightarrow> wbt r \<Longrightarrow> combine_p l r = Order_Statistic_Tree.combine l r"
  by (cases l; cases r) (simp_all add: combine_p_def split_min_p_eq del_max_p_eq)

fun delete_p :: "'a::linorder \<Rightarrow> 'a wbt \<Rightarrow> 'a wbt" where
  "delete_p _ Leaf = Leaf"
| "delete_p x (Node l (a, _) r) =
    (case cmp x a of
       LT \<Rightarrow> balanceL (delete_p x l) a r
     | GT \<Rightarrow> balanceR l a (delete_p x r)
     | EQ \<Rightarrow> combine_p l r)"

lemma delete_p_eq: "wbt t \<Longrightarrow> delete_p x t = delete x t"
  by (induction x t rule: delete_p.induct) (simp_all add: combine_p_eq)

lemma tree_remove_code[code]: "Rep_wf_wbt (tree_remove x t) = delete_p x (Rep_wf_wbt t)"
  using Rep_wf_wbt[of t] by (simp add: tree_remove.rep_eq delete_p_eq)

text \<open>MIN and MAX ask for the element of rank 0 and of rank \<open>n - 1\<close>.  @{const select} finds
  them by comparing the rank with the stored size at every node on the way down; the leftmost
  and the rightmost node are reached without any arithmetic.\<close>

fun wbt_min :: "'a wbt \<Rightarrow> 'a" where
  "wbt_min Leaf = [] ! 0"
| "wbt_min (Node l (a, _) _) = (case l of Leaf \<Rightarrow> a | Node _ _ _ \<Rightarrow> wbt_min l)"

fun wbt_max :: "'a wbt \<Rightarrow> 'a" where
  "wbt_max Leaf = [] ! 0"
| "wbt_max (Node _ (a, _) r) = (case r of Leaf \<Rightarrow> a | Node _ _ _ \<Rightarrow> wbt_max r)"

lemma select_0: "wbt t \<Longrightarrow> select t 0 = wbt_min t"
proof (induction t)
  case (Node l x r)
  then show ?case by (cases x; cases l) auto
qed simp

lemma select_last: "wbt t \<Longrightarrow> select t (size_wbt t - 1) = wbt_max t"
proof (induction t)
  case (Node l x r)
  then show ?case by (cases x; cases r) auto
qed simp

lift_definition tree_min :: "'a::linorder wf_wbt \<Rightarrow> 'a" is wbt_min .
lift_definition tree_max :: "'a::linorder wf_wbt \<Rightarrow> 'a" is wbt_max .

lemma tree_select_0: "tree_select t 0 = tree_min t"
  by transfer (simp add: select_0)

lemma tree_select_last: "tree_select t (tree_size t - 1) = tree_max t"
  by transfer (metis select_last)

definition get_edata_min :: "list_aux \<Rightarrow> event_data" where
  "get_edata_min k = get_edata_list k 0"

definition get_edata_max :: "list_aux \<Rightarrow> event_data" where
  "get_edata_max k = get_edata_list k (get_length k - 1)"

lemma get_edata_min_code[code]:
  "get_edata_min (LInt (Collapse t)) = EInt (tree_min t)"
  "get_edata_min (LString (Collapse s)) = EString (tree_min s)"
  by (simp_all add: get_edata_min_def get_treelist_code tree_select_0)

lemma get_edata_max_code[code]:
  "get_edata_max (LInt (Collapse t)) = EInt (tree_max t)"
  "get_edata_max (LString (Collapse s)) = EString (tree_max s)"
  by (simp_all add: get_edata_max_def get_length_def get_treelist_code length_treelist_code
      tree_select_last[unfolded One_nat_def])

lemma get_edata_min_max_unfold[code_unfold]:
  "get_edata_list k 0 = get_edata_min k"
  "get_edata_list k (get_length k - 1) = get_edata_max k"
  by (simp_all add: get_edata_min_def get_edata_max_def)

text \<open>The treelists and the tree operations at the two closed types they are used at: the
  integer values of MIN, MAX and MED and the string values of the first two.\<close>

setup \<open>mono
  [("insert_treelist", "int_insert_treelist", ["integer"]),
   ("remove_treelist", "int_remove_treelist", ["integer"]),
   ("empty_treelist", "int_empty_treelist", ["integer"]),
   ("get_treelist", "int_get_treelist", ["integer"]),
   ("length_treelist", "int_length_treelist", ["integer"]),
   ("insert_treelist", "s8_insert_treelist", ["string8"]),
   ("remove_treelist", "s8_remove_treelist", ["string8"]),
   ("empty_treelist", "s8_empty_treelist", ["string8"])]
  dicts\<close>

setup \<open>mono
  [("cmp", "nat_cmp", ["nat"]),
   ("cmp", "int_cmp", ["integer"]),
   ("Order_Statistic_Tree.insert", "int_wbt_insert", ["integer"]),
   ("delete_p", "int_wbt_delete", ["integer"]),
   ("tree_insert", "int_tree_insert", ["integer"]),
   ("tree_remove", "int_tree_remove", ["integer"]),
   ("cmp", "s8_cmp", ["string8"]),
   ("Order_Statistic_Tree.insert", "s8_wbt_insert", ["string8"]),
   ("delete_p", "s8_wbt_delete", ["string8"]),
   ("tree_insert", "s8_tree_insert", ["string8"]),
   ("tree_remove", "s8_tree_remove", ["string8"])]
  dicts\<close>

subsection \<open>The tuples' key list, fold, sorted list and filter\<close>

text \<open>The membership test on a table compared the lookup with @{term "Some ()"} by the generic
  equality on options.  The tree's key list and the sorted list of a table, and the filter of a
  count map, are boxed in @{theory MFODL_Monitor_Devel.Monomorphic_Code}; the boxes are taken out
  of the preprocessor (here, and again in \<^verbatim>\<open>Monitor_Code_Dense\<close>, whose merge of the imports
  brings them back) in favour of copies.\<close>

lemma ed_rbt_member_lookup[code]:
  "ed_rbt_member t x = (case RBT_Mapping2.lookup t x of None \<Rightarrow> False | Some _ \<Rightarrow> True)"
  by (simp add: ed_rbt_member_code equal split: option.splits)

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps
  @{thms ed_csorted_list_of_set_v_unfold ed_mfilter_nat_v_unfold})\<close>

setup \<open>mono
  [("csorted_list_of_set", "ed_csorted_list_of_set", [etuple]),
   ("RBT_Mapping2.filter", "ed_rbt_filter_nat", [etuple, "nat"]),
   ("Mapping.filter", "ed_mfilter_nat", [etuple, "nat"])]
  dicts\<close>

subsection \<open>The copies\<close>

text \<open>The box of @{const cluster} would shadow its copy.\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps @{thms ed_cluster_v_unfold})\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("cluster", "ed_cluster", [etuple, etuple]),
   ("reorder", "ed_reorder", ["event_data"]),
   ("\<epsilon>_lax", "ed_eps_lax", ["event_data"]),
   ("r\<epsilon>_strict", "ed_reps_strict", ["event_data"]),
   ("l\<epsilon>_strict", "ed_leps_strict", ["event_data"]),
   ("r\<delta>", "ed_rdelta", ["event_data"]),
   ("l\<delta>", "ed_ldelta", ["event_data"]),
   ("wf_set_of_set", "ed_wf_set_of_set", ["event_data"]),
   ("wf_table_set", "ed_wf_table_set", ["event_data"]),
   ("wf_table_union", "ed_wf_table_union", ["event_data"]),
   ("wf_table_join", "ed_wf_table_join", ["event_data"]),
   ("wf_table_antijoin", "ed_wf_table_antijoin", ["event_data"]),
   ("wf_idx_of_set", "ed_wf_idx_of_set", ["event_data"]),
   ("wf_idx_union", "ed_wf_idx_union", ["event_data"]),
   ("wf_idx_antijoin", "ed_wf_idx_antijoin", ["event_data"]),
   ("move_insert", "ed_move_insert", ["event_data"]),
   ("move_tbl", "ed_move_tbl", ["event_data"]),
   ("tmp_elem", "ed_tmp_elem", ["event_data"]),
   ("until_step", "ed_until_step", ["event_data"])]
  ["etuple_dict_simps"]\<close>

text \<open>The copies made in @{theory MFODL_Monitor_Devel.Monomorphic_Code} were derived through the
  box, and call it: the box is the copy.\<close>

declare [[code drop: ed_cluster_v]]

lemma ed_cluster_v_code[code]: "ed_cluster_v = Box ed_cluster"
  by (simp add: ed_cluster_v_def ed_cluster_def)

text \<open>The Since structure's index is built through @{const wf_table_of_set_args}, which has no
  copy either; nor has the tree's key list, which the count sets of
  \<^verbatim>\<open>Dense_Win\<close> fold over.  And the boxes of the Since structure's
  mapping operations pass the generic comparator down: they become copies too.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("wf_table_of_set_args", "ed_wf_table_of_set_args", ["event_data"]),
   ("wf_idx_of_wf_set", "ed_wf_idx_of_wf_set", ["event_data"]),
   ("wf_set_union", "ed_wf_set_union", ["event_data"]),
   ("RBT_Set2.keys", "ed_rbt_keys", [etuple]),
   ("upd_set", "ed_upd_set_nat_m", [etuple, "nat"]),
   ("minus_keys", "ed_minus_keys_m", [etuple, "nat"]),
   ("mapping_delete_set", "ed_mapping_delete_set_tstp_m", [etuple, "nat + nat"]),
   ("filter_set", "ed_filter_set_m", ["nat", etuple]),
   ("set_of_idx", "ed_set_of_idx_m", [etuple, etuple]),
   ("mapping_of_cluster", "ed_mapping_of_cluster", [etuple, etuple]),
   ("cluster_rbt_comp", "ed_cluster_rbt_comp", [etuple, etuple]),
   ("add_to_rbt_comp", "ed_add_to_rbt_comp", [etuple, etuple]),
   ("idx_bucket", "ed_idx_bucket", ["event_data"]),
   ("idx_add1", "ed_idx_add1", ["event_data"]),
   ("idx_del1", "ed_idx_del1", ["event_data"]),
   ("idx_ins", "ed_idx_ins", ["event_data"]),
   ("idx_dels", "ed_idx_dels", ["event_data"]),
   ("wf_idx_ins", "ed_wf_idx_ins", ["event_data"]),
   ("wf_idx_rem", "ed_wf_idx_rem", ["event_data"]),
   ("wf_table_union0", "ed_wf_table_union0", ["event_data"]),
   ("wf_table_antijoin0", "ed_wf_table_antijoin0", ["event_data"]),
   ("wf_table_add", "ed_wf_table_add", ["event_data"]),
   ("wf_table_del", "ed_wf_table_del", ["event_data"])]
  ["etuple_dict_simps"]\<close>

text \<open>The preprocessor rewrites bottom-up, so the index's argument is redirected to its copy
  before the key-driven forms of \<^verbatim>\<open>Dense_Idx\<close> get to match; they are restated in terms of the
  copies.\<close>

lemma ed_wf_table_add_compat[code_unfold]:
  "ed_wf_table_union t (ed_wf_table_of_set_args args X) = ed_wf_table_add args t X"
  "ed_wf_table_antijoin t (ed_wf_table_of_set_args args X) = ed_wf_table_del args t X"
  by (simp_all add: ed_wf_table_union_def ed_wf_table_antijoin_def ed_wf_table_of_set_args_def
      ed_wf_table_add_def ed_wf_table_del_def wf_table_add_def wf_table_del_def)

text \<open>The Since structure's join (@{thm [source] join_mmsaux_probe}), with the operations it
  calls.  Its copy from \<^verbatim>\<open>Monomorphic_Code\<close> keeps the kernel's equation; it is re-derived.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("mrestrict1", "ed_mrestrict1", [etuple, "event_data table"]),
   ("mfilter_keys", "ed_mfilter_keys", [etuple, "event_data table"]),
   ("wf_idx_keep", "ed_wf_idx_keep", ["event_data"]),
   ("wf_idx_drop", "ed_wf_idx_drop", ["event_data"]),
   ("wf_table_probe0", "ed_wf_table_probe0", ["event_data"]),
   ("wf_table_probe", "ed_wf_table_probe", ["event_data"]),
   ("mapping_delete_set", "ed_mapping_delete_set_nat_m", [etuple, "nat"]),
   ("filter_join", "ed_filter_join_nat", [etuple, "nat"]),
   ("wf_table_upd", "ed_wf_table_upd", ["event_data"]),
   ("join_mmsaux0", "ed_join_mmsaux0", ["event_data"])]
  ["etuple_dict_simps"]\<close>

declare [[code drop: ed_join_mmsaux]]

lemmas ed_join_mmsaux_code[code] =
  join_mmsaux_probe[where 'a = event_data, folded ed_join_mmsaux_def]

declare [[code drop: ed_upd_set_nat_v ed_minus_keys_v ed_mapping_delete_set_tstp_v ed_filter_set_v
  ed_set_of_idx_v]]

lemma ed_box_copies[code]:
  "ed_upd_set_nat_v = Box ed_upd_set_nat_m"
  "ed_minus_keys_v = Box ed_minus_keys_m"
  "ed_mapping_delete_set_tstp_v = Box ed_mapping_delete_set_tstp_m"
  "ed_filter_set_v = Box ed_filter_set_m"
  "ed_set_of_idx_v = Box ed_set_of_idx_m"
  by (simp_all add: ed_upd_set_nat_v_def ed_upd_set_nat_m_def ed_minus_keys_v_def ed_minus_keys_m_def
    ed_mapping_delete_set_tstp_v_def ed_mapping_delete_set_tstp_m_def ed_filter_set_v_def
    ed_filter_set_m_def ed_set_of_idx_v_def ed_set_of_idx_m_def)

(*<*)
end
(*>*)
