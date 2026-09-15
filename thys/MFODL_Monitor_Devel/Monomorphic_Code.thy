(*<*)
theory Monomorphic_Code
  imports Imperative_Join
begin
(*>*)

section \<open>Monomorphisation of the hot code as a refinement\<close>

text \<open>
  The generated code passes type class dictionaries (@{class ceq}, @{class ccompare}, \dots) at
  run time. For the tuple type @{typ "event_data tuple"} these dictionaries are composite
  (@{text "ccompare_list (ccompare_option ccompare_event_data)"}) and are rebuilt at every
  call of a polymorphic function that constructs them from its own dictionary parameters, in
  particular in the per-tuple inner loops of the joins and of the auxiliary structures.

  This theory removes that overhead by a refinement at the level of code equations, without
  changing any definition or correctness proof of the monitor:
  \<^item> for each polymorphic function @{text f} of the implementation that is hot at type
    @{typ event_data}, a monomorphic copy @{text "ed_f = f"} is introduced whose code equations
    are the code equations of @{text f} instantiated to @{typ event_data} (derived by the
    kernel from the definition @{text "ed_f = f"}), and all applied occurrences of @{text f} at
    that type are redirected to @{text ed_f} by a @{text code_unfold} rule;
  \<^item> for each generic container operation @{text c} used at a closed type involving tuples of
    event data, a nullary constant @{text "c_v = Box c"} is introduced. The generated code for a
    nullary constant of a non-function type is a value, so the dictionaries of @{text c} at that
    type are built once, when the program starts; @{text "c x = unbox c_v x"} redirects the calls.
  Both constructions are automated in \<^file>\<open>monomorphize.ML\<close>.
\<close>

subsection \<open>A direct comparator on tuples of event data\<close>

fun ed_comparator :: "event_data tuple comparator" where
  "ed_comparator [] [] = Eq"
| "ed_comparator [] (y # ys) = Lt"
| "ed_comparator (x # xs) [] = Gt"
| "ed_comparator (None # xs) (None # ys) = ed_comparator xs ys"
| "ed_comparator (None # xs) (Some b # ys) = Lt"
| "ed_comparator (Some a # xs) (None # ys) = Gt"
| "ed_comparator (Some a # xs) (Some b # ys) =
    (case comparator_event_data a b of Eq \<Rightarrow> ed_comparator xs ys | r \<Rightarrow> r)"

lemma ed_comparator_eq: "ed_comparator xs ys = comparator_list (comparator_option comparator_event_data) xs ys"
  by (induction xs ys rule: ed_comparator.induct) (auto split: order.splits)

lemma ccompare_etuple: "CCOMPARE(event_data tuple) = Some ed_comparator"
  by (simp add: ccompare_list_def ccompare_option_def ccompare_event_data_def ID_def ed_comparator_eq[abs_def])

lemma ID_ccompare_etuple: "ID CCOMPARE(event_data tuple) = Some ed_comparator"
  by (simp add: ccompare_etuple ID_def)

lemma ccomp_etuple: "(ccomp :: event_data tuple comparator) = ed_comparator"
  by (simp add: ID_ccompare_etuple)

lemma ceq_etuple: "CEQ(event_data tuple) = Some (equality_list (equality_option (=)))"
  by (simp add: ceq_list_def ceq_option_def ceq_event_data_def ID_def)

lemma ID_ceq_etuple: "ID CEQ(event_data tuple) = Some (equality_list (equality_option (=)))"
  by (simp add: ceq_etuple ID_def)

lemmas etuple_dict_simps = ccompare_etuple ID_ccompare_etuple ccomp_etuple ceq_etuple ID_ceq_etuple
  option.case option.sel ID_def id_apply

subsection \<open>Folds over red-black trees without the @{type comp_fun_idem} wrapper\<close>

lemma set_fold_cfi_RBT:
  fixes rbt :: "'a :: ccompare set_rbt"
  assumes "comp_fun_idem_apply g = f"
  shows "set_fold_cfi g b (RBT_set rbt) = (case ID CCOMPARE('a) of
      None \<Rightarrow> Code.abort s (\<lambda>_. set_fold_cfi g b (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold f rbt b)"
proof (cases "ID CCOMPARE('a)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then show ?thesis by (subst set_fold_cfi_code(1)) (simp add: assms)
qed

declare [[code drop: join_row probe_step probe_join tmp_set]]

lemma join_row_RBT_code[code]:
  fixes rbt :: "('a :: {ccompare, ceq}) tuple set_rbt"
  shows "join_row (RBT_set rbt) a acc = (case ID CCOMPARE('a tuple) of
      None \<Rightarrow> Code.abort (STR ''join_row: ccompare = None'') (\<lambda>_. join_row (RBT_set rbt) a acc)
    | Some _ \<Rightarrow> RBT_Set2.fold (join1_insert a) rbt acc)"
  unfolding join_row_def by (rule set_fold_cfi_RBT[OF join1_insert_cfi.rep_eq])

lemmas join_row_fallback_code[code] =
  join_row_def[where B = "DList_set _"] join_row_def[where B = "Set_Monad _"]
  join_row_def[where B = "Collect_set _"] join_row_def[where B = "Complement _"]

definition probe_fold :: "'a tuple \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "probe_fold b acc T = set_fold_cfi (join1_insert_cfi' b) acc T"

lemma probe_fold_RBT_code[code]:
  fixes rbt :: "('a :: {ccompare, ceq}) tuple set_rbt"
  shows "probe_fold b acc (RBT_set rbt) = (case ID CCOMPARE('a tuple) of
      None \<Rightarrow> Code.abort (STR ''probe_fold: ccompare = None'') (\<lambda>_. probe_fold b acc (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold (join1_insert' b) rbt acc)"
  unfolding probe_fold_def by (rule set_fold_cfi_RBT[OF join1_insert_cfi'.rep_eq])

lemmas probe_fold_fallback_code[code] =
  probe_fold_def[where T = "DList_set _"] probe_fold_def[where T = "Set_Monad _"]
  probe_fold_def[where T = "Collect_set _"] probe_fold_def[where T = "Complement _"]

lemma probe_step_code[code]:
  "probe_step I m b acc = (case Mapping.lookup m (restrict I b) of None \<Rightarrow> acc | Some T \<Rightarrow> probe_fold b acc T)"
  unfolding probe_step_def probe_fold_def ..

lemma probe_join_RBT_code[code]:
  fixes rbt :: "('a :: {ccompare, ceq}) tuple set_rbt"
  shows "probe_join I t (RBT_set rbt) = (case ID CCOMPARE('a tuple) of
      None \<Rightarrow> Code.abort (STR ''probe_join: ccompare = None'') (\<lambda>_. probe_join I t (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold (probe_step I (cluster (Some \<circ> restrict I) t)) rbt {})"
  unfolding probe_join_def by (rule set_fold_cfi_RBT[OF probe_step_cfi.rep_eq])

lemmas probe_join_fallback_code[code] =
  probe_join_def[where t' = "DList_set _"] probe_join_def[where t' = "Set_Monad _"]
  probe_join_def[where t' = "Collect_set _"] probe_join_def[where t' = "Complement _"]

text \<open>The probe join with a precomputed projection mask (@{const probe_join_n}, Code_Opt).\<close>

definition probe_step_key :: "('a tuple \<Rightarrow> 'a tuple) \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "probe_step_key key m b acc = (case Mapping.lookup m (key b) of None \<Rightarrow> acc | Some T \<Rightarrow> probe_fold b acc T)"

lemma probe_step_key_restrict: "probe_step_key (restrict I) = probe_step I"
  by (simp add: fun_eq_iff probe_step_key_def probe_step_code)

declare [[code drop: probe_join_n]]

lemma probe_join_n_RBT_code[code]:
  fixes rbt :: "('a :: {ccompare, ceq}) tuple set_rbt"
  shows "probe_join_n n I t (RBT_set rbt) = (case ID CCOMPARE('a tuple) of
      None \<Rightarrow> Code.abort (STR ''probe_join: ccompare = None'') (\<lambda>_. probe_join_n n I t (RBT_set rbt))
    | Some _ \<Rightarrow> (let key = restrict_with I n in
        RBT_Set2.fold (probe_step_key key (cluster (Some \<circ> key) t)) rbt {}))"
  unfolding probe_join_n_def
  by (subst probe_join_RBT_code) (simp only: Let_def restrict_with probe_step_key_restrict)

lemmas probe_join_n_fallback_code[code] =
  probe_join_n_def[where t' = "DList_set _"] probe_join_n_def[where t' = "Set_Monad _"]
  probe_join_n_def[where t' = "Collect_set _"] probe_join_n_def[where t' = "Complement _"]

lemma tmp_set_RBT_code[code]:
  fixes rbt :: "('a :: {ccompare, ceq}) tuple set_rbt"
  shows "tmp_set a1_map maskL pos tp len B (RBT_set rbt) = (case ID CCOMPARE('a tuple) of
      None \<Rightarrow> Code.abort (STR ''tmp_set: ccompare = None'') (\<lambda>_. tmp_set a1_map maskL pos tp len B (RBT_set rbt))
    | Some _ \<Rightarrow> RBT_Set2.fold (tmp_step a1_map maskL pos tp len) rbt B)"
proof (cases "ID CCOMPARE('a tuple)")
  case None
  then show ?thesis by simp
next
  case (Some c)
  then have "finite (RBT_set rbt)"
    by (subst RBT_set_conv_keys) auto
  with Some show ?thesis
    by (subst tmp_set_code) (simp add: set_fold_cfi_RBT[OF tmp_step_cfi.rep_eq, where s = "STR ''x''"])
qed

lemmas tmp_set_fallback_code[code] =
  tmp_set_code[of _ _ _ _ _ _ "DList_set _"] tmp_set_code[of _ _ _ _ _ _ "Set_Monad _"]
  tmp_set_code[of _ _ _ _ _ _ "Collect_set _"] tmp_set_code[of _ _ _ _ _ _ "Complement _"]

datatype 'a boxed = Box (unbox: 'a)

ML_file \<open>monomorphize.ML\<close>

subsection \<open>Empty tables and mappings as values\<close>

lemma RBT_Mapping_empty: "RBT_Mapping RBT_Mapping2.empty = Mapping.empty"
  by (simp add: Mapping.empty_def)

definition ed_bot :: "event_data table" where "ed_bot = {}"
definition ed_bot_pair :: "(nat \<times> event_data tuple) set" where "ed_bot_pair = {}"

lemma ed_bot_code[code]: "ed_bot = RBT_set RBT_Set2.empty"
  by (simp add: ed_bot_def)
lemma ed_bot_pair_code[code]: "ed_bot_pair = RBT_set RBT_Set2.empty"
  by (simp add: ed_bot_pair_def)

lemma ed_bot_unfold[code_unfold]:
  "(bot :: event_data table) = ed_bot"
  "set_empty (of_phantom SET_IMPL(event_data tuple)) = ed_bot"
  "(empty_table :: event_data table) = ed_bot"
  "(bot :: (nat \<times> event_data tuple) set) = ed_bot_pair"
  "set_empty (of_phantom SET_IMPL(nat \<times> event_data tuple)) = ed_bot_pair"
  by (simp_all add: ed_bot_def ed_bot_pair_def empty_table_def)


definition ed_mempty_nat :: "(event_data tuple, nat) mapping" where "ed_mempty_nat = Mapping.empty"
lemma ed_mempty_nat_code[code]: "ed_mempty_nat = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_nat_def RBT_Mapping_empty)
lemma ed_mempty_nat_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, nat) mapping) = ed_mempty_nat"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, nat) mapping) = ed_mempty_nat"
  by (simp_all add: ed_mempty_nat_def)

definition ed_mempty_tstp :: "(event_data tuple, nat + nat) mapping" where "ed_mempty_tstp = Mapping.empty"
lemma ed_mempty_tstp_code[code]: "ed_mempty_tstp = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_tstp_def RBT_Mapping_empty)
lemma ed_mempty_tstp_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, nat + nat) mapping) = ed_mempty_tstp"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, nat + nat) mapping) = ed_mempty_tstp"
  by (simp_all add: ed_mempty_tstp_def)

definition ed_mempty_table :: "(event_data tuple, event_data table) mapping" where "ed_mempty_table = Mapping.empty"
lemma ed_mempty_table_code[code]: "ed_mempty_table = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_table_def RBT_Mapping_empty)
lemma ed_mempty_table_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, event_data table) mapping) = ed_mempty_table"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, event_data table) mapping) = ed_mempty_table"
  by (simp_all add: ed_mempty_table_def)

definition ed_mempty_sum :: "(event_data tuple, nat \<times> integer) mapping" where "ed_mempty_sum = Mapping.empty"
lemma ed_mempty_sum_code[code]: "ed_mempty_sum = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_sum_def RBT_Mapping_empty)
lemma ed_mempty_sum_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, nat \<times> integer) mapping) = ed_mempty_sum"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, nat \<times> integer) mapping) = ed_mempty_sum"
  by (simp_all add: ed_mempty_sum_def)

definition ed_mempty_rank :: "(event_data tuple, list_aux) mapping" where "ed_mempty_rank = Mapping.empty"
lemma ed_mempty_rank_code[code]: "ed_mempty_rank = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: ed_mempty_rank_def RBT_Mapping_empty)
lemma ed_mempty_rank_unfold[code_unfold]:
  "(Mapping.empty :: (event_data tuple, list_aux) mapping) = ed_mempty_rank"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data tuple)) :: (event_data tuple, list_aux) mapping) = ed_mempty_rank"
  by (simp_all add: ed_mempty_rank_def)


ML \<open>
val etuple = "event_data tuple"
val ed_value_types =
  [("nat", "nat"), ("tstp", "nat + nat"), ("table", "event_data table"),
   ("sum", "nat \<times> integer"), ("rank", "list_aux")]
val ed_mapping_ops =
  [("Mapping.lookup", "lookup"), ("Mapping.update", "update"), ("Mapping.delete", "delete"),
   ("Mapping.filter", "mfilter"), ("Mapping.keys", "keys"), ("Mapping.is_empty", "mis_empty")]
val ed_agg_maps =
  ["nat agg_map", "(nat \<times> integer) agg_map", "list_aux agg_map",
   "bool \<times> nat agg_map", "bool \<times> (nat \<times> integer) agg_map", "bool \<times> list_aux agg_map"]
val ed_box_specs =
  [("Set.insert", "ed_insert_v", [etuple]),
   ("Set.member", "ed_member_v", [etuple]),
   ("Set.remove", "ed_remove_v", [etuple]),
   ("sup :: _ set \<Rightarrow> _", "ed_union_v", [etuple]),
   ("inf :: _ set \<Rightarrow> _", "ed_inter_v", [etuple]),
   ("minus :: _ set \<Rightarrow> _", "ed_minus_v", [etuple]),
   ("Set.filter", "ed_filter_v", [etuple]),
   ("image", "ed_image_v", [etuple, etuple]),
   ("Ball", "ed_Ball_v", [etuple]),
   ("Bex", "ed_Bex_v", [etuple]),
   ("finite", "ed_finite_v", [etuple]),
   ("card", "ed_card_v", [etuple]),
   ("set_eq", "ed_set_eq_v", [etuple]),
   ("Set.is_empty", "ed_is_empty_v", [etuple]),
   ("less_eq :: _ set \<Rightarrow> _", "ed_subset_v", [etuple]),
   ("csorted_list_of_set", "ed_csorted_list_of_set_v", [etuple]),
   ("RBT_Set2.fold", "ed_rbt_fold_table_v", [etuple, "event_data table"]),
   ("RBT_Set2.fold", "ed_rbt_fold_pair_v", [etuple, "(nat \<times> event_data tuple) set"]),
   ("set_fold_cfi", "ed_fold_cfi_table_v", [etuple, "event_data table"]),
   ("set_fold_cfi", "ed_fold_cfi_pair_v", [etuple, "(nat \<times> event_data tuple) set"]),
   ("cluster", "ed_cluster_v", [etuple, etuple]),
   ("cluster", "ed_cluster_ed_v", [etuple, "event_data"]),
   ("Mapping.keys", "ed_keys_ed_table_v", ["event_data", "event_data table"]),
   ("Mapping.lookup", "ed_lookup_ed_table_v", ["event_data", "event_data table"]),
   ("set_of_idx", "ed_set_of_idx_v", [etuple, etuple]),
   ("mapping_join", "ed_mapping_join_v", [etuple, "event_data table"]),
   ("mapping_antijoin", "ed_mapping_antijoin_v", [etuple, "event_data table"]),
   ("mapping_delete_set", "ed_mapping_delete_set_tstp_v", [etuple, "nat + nat"]),
   ("upd_set", "ed_upd_set_nat_v", [etuple, "nat"]),
   ("upd_set_keys", "ed_upd_set_keys_v", ["event_data table", "nat", etuple]),
   ("upd_nested_max_tstp", "ed_upd_nested_max_tstp_v", ["nat", etuple]),
   ("filter_set", "ed_filter_set_v", ["nat", etuple]),
   ("minus_keys", "ed_minus_keys_v", [etuple, "nat"]),
   (* sets of (time point, tuple) pairs of the Until structure *)
   ("Set.insert", "ed_insert_pair_v", ["nat \<times> event_data tuple"]),
   ("Set.filter", "ed_filter_pair_v", ["nat \<times> event_data tuple"]),
   ("sup :: _ set \<Rightarrow> _", "ed_union_pair_v", ["nat \<times> event_data tuple"]),
   ("image", "ed_image_pair_snd_v", ["nat \<times> event_data tuple", etuple]),
   ("image", "ed_image_pair_v", [etuple, "nat \<times> event_data tuple"]),
   ("finite", "ed_finite_pair_v", ["nat \<times> event_data tuple"])]
  @ maps (fn (c, nm) => map (fn (tn, ty) => (c, "ed_" ^ nm ^ "_" ^ tn ^ "_v", [etuple, ty])) ed_value_types)
      ed_mapping_ops
  @ map (fn (tn, ty) => ("Mapping.combine", "ed_combine_" ^ tn ^ "_v", [ty, etuple])) ed_value_types
  @ map_index (fn (i, ty) => ("set_fold_cfc", "ed_fold_cfc_agg" ^ string_of_int i ^ "_v", [etuple, ty])) ed_agg_maps
\<close>

setup \<open>Monomorphize.box_cmd ed_box_specs\<close>

subsection \<open>Compatibility with the other preprocessor rules\<close>

text \<open>
  The code preprocessor rewrites bottom-up. The redirections above therefore fire inside the
  left-hand sides of other @{text code_unfold} rules before those get a chance to apply (e.g.
  @{term "{a \<in> A. P a}"} is normally folded into @{term "Set.filter P A"}, and membership in
  @{term "Mapping.keys m"} is normally turned into a lookup). We restate the affected rules in
  terms of the redirected constants.
\<close>

lemma ed_member_compat[code_unfold]:
  "Collect (\<lambda>a. unbox ed_member_v a A \<and> P a) = Set.filter P A"
  "Collect (\<lambda>a. unbox ed_member_v a A) = A"
  "unbox ed_member_v a (Collect Q) = Q a"
  "unbox ed_member_v x (set xs) = List.member xs x"
  "unbox ed_Ball_v (set xs) P = list_all P xs"
  "unbox ed_Bex_v (set xs) P = list_ex P xs"
  "unbox ed_union_v (set xs) (set ys) = set (xs @ ys)"
  unfolding ed_member_v_unfold[symmetric] ed_Ball_v_unfold[symmetric] ed_Bex_v_unfold[symmetric]
    ed_union_v_unfold[symmetric]
  by (auto simp: list_all_iff list_ex_iff)

lemma ed_bot_compat[code_unfold]:
  "(A = ed_bot) = Set.is_empty A"
  "(ed_bot = A) = Set.is_empty A"
  "set_eq A ed_bot = Set.is_empty A"
  "set_eq ed_bot A = Set.is_empty A"
  "(B = ed_bot_pair) = Set.is_empty B"
  "(ed_bot_pair = B) = Set.is_empty B"
  "set_eq B ed_bot_pair = Set.is_empty B"
  "set_eq ed_bot_pair B = Set.is_empty B"
  by (auto simp: ed_bot_def ed_bot_pair_def)

lemma ed_keys_compat[code_unfold]:
  "unbox ed_member_v k (unbox ed_keys_nat_v m1) = (\<not> Option.is_none (unbox ed_lookup_nat_v m1 k))"
  "unbox ed_member_v k (unbox ed_keys_tstp_v m2) = (\<not> Option.is_none (unbox ed_lookup_tstp_v m2 k))"
  "unbox ed_member_v k (unbox ed_keys_table_v m3) = (\<not> Option.is_none (unbox ed_lookup_table_v m3 k))"
  "unbox ed_member_v k (unbox ed_keys_sum_v m4) = (\<not> Option.is_none (unbox ed_lookup_sum_v m4 k))"
  "unbox ed_member_v k (unbox ed_keys_rank_v m5) = (\<not> Option.is_none (unbox ed_lookup_rank_v m5 k))"
  unfolding ed_member_v_unfold[symmetric] ed_keys_nat_v_unfold[symmetric] ed_lookup_nat_v_unfold[symmetric] ed_keys_tstp_v_unfold[symmetric] ed_lookup_tstp_v_unfold[symmetric] ed_keys_table_v_unfold[symmetric] ed_lookup_table_v_unfold[symmetric] ed_keys_sum_v_unfold[symmetric] ed_lookup_sum_v_unfold[symmetric] ed_keys_rank_v_unfold[symmetric] ed_lookup_rank_v_unfold[symmetric]
  by (simp_all add: Mapping.keys_is_none_rep)

lemma ed_minus_keys_compat[code_unfold]:
  "unbox ed_minus_v X (unbox ed_keys_nat_v m1) = Set.filter (\<lambda>k. unbox ed_lookup_nat_v m1 k = None) X"
  "unbox ed_minus_v X (unbox ed_keys_tstp_v m2) = Set.filter (\<lambda>k. unbox ed_lookup_tstp_v m2 k = None) X"
  "unbox ed_minus_v X (unbox ed_keys_table_v m3) = Set.filter (\<lambda>k. unbox ed_lookup_table_v m3 k = None) X"
  "unbox ed_minus_v X (unbox ed_keys_sum_v m4) = Set.filter (\<lambda>k. unbox ed_lookup_sum_v m4 k = None) X"
  "unbox ed_minus_v X (unbox ed_keys_rank_v m5) = Set.filter (\<lambda>k. unbox ed_lookup_rank_v m5 k = None) X"
  unfolding ed_minus_v_unfold[symmetric] ed_keys_nat_v_unfold[symmetric] ed_lookup_nat_v_unfold[symmetric] ed_keys_tstp_v_unfold[symmetric] ed_lookup_tstp_v_unfold[symmetric] ed_keys_table_v_unfold[symmetric] ed_lookup_table_v_unfold[symmetric] ed_keys_sum_v_unfold[symmetric] ed_lookup_sum_v_unfold[symmetric] ed_keys_rank_v_unfold[symmetric] ed_lookup_rank_v_unfold[symmetric]
  by (auto simp: Mapping.keys_dom_lookup)

section \<open>Bulk construction of tables\<close>

text \<open>
  The front end builds the database of a time point by inserting tuples one at a time
  (@{const insert_into_db}). @{text table_of_list} builds a table from a list in one step: if
  the list is strictly sorted with respect to the comparator (checked in linear time; the
  front end sorts with an unverified comparator), the red-black tree is built in linear time
  by @{const rbtreeify}, otherwise by the usual repeated insertion. Either way the result is
  @{term "set xs"}.
\<close>

fun strict_sorted_by :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> bool" where
  "strict_sorted_by c (x # y # zs) \<longleftrightarrow> c x y = Lt \<and> strict_sorted_by c (y # zs)"
| "strict_sorted_by c _ \<longleftrightarrow> True"

lemma lt_of_comp_Lt: "lt_of_comp c x y \<longleftrightarrow> c x y = Lt"
  by (simp add: lt_of_comp_def split: order.splits)

lemma strict_sorted_by_sorted_wrt:
  assumes "comparator c"
  shows "strict_sorted_by c xs \<longleftrightarrow> sorted_wrt (lt_of_comp c) xs"
proof -
  have transp: "transp (lt_of_comp c)"
    using comparator.comp_trans[OF assms]
    by (auto intro!: transpI simp: lt_of_comp_def split: order.splits)
  show ?thesis
  proof (induction xs rule: induct_list012)
    case (3 x y zs)
    then show ?case
      by (subst sorted_wrt2[OF transp]) (simp add: lt_of_comp_Lt[abs_def])
  qed auto
qed

lift_definition rbt_of_sorted_list :: "'a :: ccompare list \<Rightarrow> 'a set_rbt" is
  "\<lambda>xs. if strict_sorted_by ccomp xs then rbtreeify (map (\<lambda>x. (x, ())) xs)
    else rbt_comp_bulkload ccomp (map (\<lambda>x. (x, ())) xs)"
proof goal_cases
  case (1 xs)
  show ?case
  proof (cases "ID CCOMPARE('a)")
    case None
    then show ?thesis by simp
  next
    case (Some c)
    note lin = ID_ccompare[OF Some] and comp = ID_ccompare'[OF Some]
    show ?thesis
      using Some
      by (auto simp: rbt_comp_bulkload[OF comp] strict_sorted_by_sorted_wrt[OF comp]
          linorder.strict_sorted_iff[OF lin] comp_def
          intro!: linorder.is_rbt_rbtreeify[OF lin] linorder.rbt_bulkload_is_rbt[OF lin])
  qed
qed

lemma RBT_set_rbt_of_sorted_list:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "RBT_set (rbt_of_sorted_list (xs :: 'a list)) = set xs"
proof -
  from assms obtain c where Some: "ID CCOMPARE('a) = Some c" by auto
  note lin = ID_ccompare[OF Some] and comp = ID_ccompare'[OF Some]
  show ?thesis
    using Some
    by (auto simp: RBT_set_def RBT_Set2.member.rep_eq rbt_of_sorted_list.rep_eq rbt_comp_lookup[OF comp]
        rbt_comp_bulkload[OF comp] strict_sorted_by_sorted_wrt[OF comp] linorder.strict_sorted_iff[OF lin] comp_def
        linorder.rbt_lookup_rbtreeify[OF lin] linorder.rbt_lookup_rbt_bulkload[OF lin] dom_map_of_conv_image_fst)
qed

definition table_of_list :: "event_data tuple list \<Rightarrow> event_data table" where
  "table_of_list xs = set xs"

lemma table_of_list_code[code]: "table_of_list xs = RBT_set (rbt_of_sorted_list xs)"
  by (simp add: table_of_list_def RBT_set_rbt_of_sorted_list ID_ccompare_etuple)


section \<open>Tables built in one pass\<close>

text \<open>
  An operator that builds its result table by inserting its tuples one at a time into a
  persistent red-black tree copies the root-to-leaf path it descends for every tuple, so a
  table of \<open>n\<close> tuples costs about \<open>n log n\<close> nodes of six words where one pass costs \<open>n\<close>.
  @{const rbt_of_sorted_list} above builds the tree in one pass, but it wants a list that is
  strictly sorted with respect to the comparator, and the tuples an operator produces are not.
  They are therefore collected in a list and sorted here, by a bottom-up merge sort that drops
  duplicates as it merges -- which is exactly the form @{const rbt_of_sorted_list} checks for,
  so nothing is sorted twice and nothing falls back to the bulkload.

  Only the set of the sorted list matters for correctness: @{const rbt_of_sorted_list} checks
  the sortedness itself and falls back if it does not hold, so the equation relating it to
  @{const set} holds unconditionally and the merge sort needs no sortedness proof -- only that
  it preserves the set of its argument.

  The probe join is the first user. Its fold over the probing table inserts each joined tuple
  into the result, and it is the case of @{const bin_join} the pure code has no better
  algorithm for.
\<close>

section \<open>A comparator merge sort\<close>

fun merge_c :: "('a :: ccompare) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_c [] ys = ys"
| "merge_c (x # xs) [] = x # xs"
| "merge_c (x # xs) (y # ys) = (case ccomp x y of
     Lt \<Rightarrow> x # merge_c xs (y # ys)
   | Gt \<Rightarrow> y # merge_c (x # xs) ys
   | Eq \<Rightarrow> x # merge_c xs ys)"

fun merge_pairs_c :: "('a :: ccompare) list list \<Rightarrow> 'a list list" where
  "merge_pairs_c (a # b # r) = merge_c a b # merge_pairs_c r"
| "merge_pairs_c r = r"

fun merge_all_c :: "nat \<Rightarrow> ('a :: ccompare) list list \<Rightarrow> 'a list" where
  "merge_all_c 0 xss = concat xss"
| "merge_all_c (Suc k) xss = (case xss of [] \<Rightarrow> [] | [a] \<Rightarrow> a
     | _ \<Rightarrow> merge_all_c k (merge_pairs_c xss))"

definition sort_c :: "('a :: ccompare) list \<Rightarrow> 'a list" where
  "sort_c xs = merge_all_c (length xs) (map (\<lambda>x. [x]) xs)"

lemma set_merge_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set (merge_c (xs :: 'a list) ys) = set xs \<union> set ys"
proof -
  from assms obtain c where Some: "ID CCOMPARE('a) = Some c" by auto
  have ccomp_eq: "(ccomp :: 'a comparator) = c" using Some by simp
  have eq: "\<And>x y. ccomp x y = Eq \<Longrightarrow> (x :: 'a) = y"
    using comparator.eq[OF ID_ccompare'[OF Some]] by (simp add: ccomp_eq)
  show ?thesis
    by (induction xs ys rule: merge_c.induct) (auto split: order.splits dest: eq)
qed

lemma set_concat_merge_pairs_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "\<Union> (set ` set (merge_pairs_c (xss :: 'a list list))) = \<Union> (set ` set xss)"
proof (induction xss rule: merge_pairs_c.induct)
  case (1 a b r)
  then show ?case by (simp add: set_merge_c[OF assms] Un_assoc)
qed simp_all

lemma set_merge_all_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set (merge_all_c n (xss :: 'a list list)) = \<Union> (set ` set xss)"
proof (induction n arbitrary: xss)
  case (Suc k)
  show ?case
  proof (cases xss)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a r)
    show ?thesis
    proof (cases r)
      case Nil
      then show ?thesis using Cons by simp
    next
      case (Cons b r')
      then show ?thesis using \<open>xss = a # r\<close>
        by (simp add: Suc.IH set_concat_merge_pairs_c[OF assms] set_merge_c[OF assms] Un_assoc)
    qed
  qed
qed simp

lemma set_sort_c:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set (sort_c (xs :: 'a list)) = set xs"
  by (simp add: sort_c_def set_merge_all_c[OF assms])

definition set_of_list :: "('a :: ccompare) list \<Rightarrow> 'a set" where
  "set_of_list xs = RBT_set (rbt_of_sorted_list (sort_c xs))"

lemma set_of_list_eq:
  assumes "ID CCOMPARE('a :: ccompare) \<noteq> None"
  shows "set_of_list (xs :: 'a list) = set xs"
  by (simp add: set_of_list_def RBT_set_rbt_of_sorted_list[OF assms] set_sort_c[OF assms])

section \<open>The probe join in one pass\<close>

definition probe_cluster :: "nat set \<Rightarrow> (('a :: {ccompare, ceq}) tuple, 'a table) mapping \<Rightarrow>
    'a tuple \<Rightarrow> 'a table" where
  "probe_cluster I m b = (case Mapping.lookup m (restrict I b) of None \<Rightarrow> {} | Some T \<Rightarrow> T)"

lemma probe_cluster_cluster:
  "probe_cluster I (cluster (Some \<circ> restrict I) t) b = {a \<in> t. restrict I a = restrict I b}"
  unfolding probe_cluster_def lookup_cluster by (auto split: if_splits simp: image_iff)

definition probe_list :: "nat set \<Rightarrow> ('a :: {ccompare, ceq}) table \<Rightarrow> 'a table \<Rightarrow> 'a tuple list" where
  "probe_list I t t' = (let m = cluster (Some \<circ> restrict I) t in
     fold (\<lambda>b acc. fold (\<lambda>a acc. case join1 (a, b) of None \<Rightarrow> acc | Some z \<Rightarrow> z # acc)
                        (csorted_list_of_set (probe_cluster I m b)) acc)
       (csorted_list_of_set t') [])"

lemma set_fold_join1_cons:
  "set (fold (\<lambda>a acc. case join1 (a, b) of None \<Rightarrow> acc | Some z \<Rightarrow> z # acc) as acc)
     = set acc \<union> (\<Union>a \<in> set as. set_option (join1 (a, b)))"
  by (induction as arbitrary: acc) (auto split: option.splits)

lemma set_fold_probe:
  "set (fold (\<lambda>b acc. fold (\<lambda>a acc. case join1 (a, b) of None \<Rightarrow> acc | Some z \<Rightarrow> z # acc)
                (g b) acc) bs acc)
     = set acc \<union> (\<Union>b \<in> set bs. \<Union>a \<in> set (g b). set_option (join1 (a, b)))"
  by (induction bs arbitrary: acc) (auto simp: set_fold_join1_cons)

lemma set_probe_list:
  fixes t t' :: "('a :: {ccompare, ceq}) table"
  assumes "finite t" "finite t'" "ID CCOMPARE('a tuple) \<noteq> None"
  shows "set (probe_list I t t') =
    (\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
proof -
  have t': "set (csorted_list_of_set t') = t'"
    using assms(2,3) by (subst csorted_list_of_set_split) auto
  have cl: "set (csorted_list_of_set (probe_cluster I (cluster (Some \<circ> restrict I) t) b)) =
    {a \<in> t. restrict I a = restrict I b}" for b
    using assms(1,3) unfolding probe_cluster_cluster
    by (subst csorted_list_of_set_split) auto
  show ?thesis
    unfolding probe_list_def Let_def set_fold_probe t' cl by simp
qed

declare [[code drop: probe_join]]

lemma probe_join_code[code]:
  fixes t t' :: "('a :: {ccompare, ceq}) table"
  shows "probe_join I t t' =
    (if finite t \<and> finite t' \<and> ID CCOMPARE('a tuple) \<noteq> None
     then set_of_list (probe_list I t t')
     else set_fold_cfi (probe_step_cfi I (cluster (Some \<circ> restrict I) t)) {} t')"
proof (cases "finite t \<and> finite t' \<and> ID CCOMPARE('a tuple) \<noteq> None")
  case True
  then have fin: "finite t" "finite t'" and cc: "ID CCOMPARE('a tuple) \<noteq> None" by auto
  have "probe_join I t t' =
    (\<Union>b \<in> t'. \<Union>a \<in> {a \<in> t. restrict I a = restrict I b}. set_option (join1 (a, b)))"
    unfolding probe_join_def set_fold_cfi.rep_eq probe_step_cfi.rep_eq
    by (rule fold_probe_step[OF fin])
  also have "\<dots> = set (probe_list I t t')"
    by (rule set_probe_list[OF fin cc, symmetric])
  also have "\<dots> = set_of_list (probe_list I t t')"
    by (rule set_of_list_eq[OF cc, symmetric])
  finally show ?thesis using True by simp
qed (auto simp: probe_join_def)

setup \<open>Monomorphize.monomorphize_cmd
  [("join1_insert", "ed_join1_insert", ["event_data"]),
   ("join1_insert'", "ed_join1_insert'", ["event_data"]),
   ("join_row", "ed_join_row", ["event_data"]),
   ("join", "ed_join", ["event_data"]),
   ("probe_fold", "ed_probe_fold", ["event_data"]),
   ("probe_step", "ed_probe_step", ["event_data"]),
   ("probe_join", "ed_probe_join", ["event_data"]),
   ("probe_step_key", "ed_probe_step_key", ["event_data"]),
   ("probe_join_n", "ed_probe_join_n", ["event_data"]),
   ("bin_join", "ed_bin_join", ["event_data"]),
   ("tmp_step", "ed_tmp_step", ["event_data"]),
   ("tmp_set", "ed_tmp_set", ["event_data"]),
   ("proj_tuple_in_join", "ed_proj_tuple_in_join", ["event_data"]),
   ("proj_tuple_in_join_optim", "ed_proj_tuple_in_join_optim", ["event_data"]),
   ("singleton_table", "ed_singleton_table", ["event_data"]),
   ("unit_table", "ed_unit_table", ["event_data"]),
   ("valid_tuple", "ed_valid_tuple", ["event_data"]),
   ("mmulti_join", "ed_mmulti_join", ["event_data"]),
   ("mmulti_join_pw", "ed_mmulti_join_pw", ["event_data"]),
   ("mmulti_join_pos", "ed_mmulti_join_pos", ["event_data"]),
   ("mmulti_join_neg", "ed_mmulti_join_neg", ["event_data"]),
   ("mmulti_join_gen", "ed_mmulti_join_gen", ["event_data"]),
   ("hprobe_join", "ed_hprobe_join", ["event_data"]),
   ("probe_join_imp", "ed_probe_join_imp", ["event_data"]),
   ("idx_create", "ed_idx_create", ["event_data"]),
   ("idx_reindex", "ed_idx_reindex", ["event_data"]),
   ("idx_join", "ed_idx_join", ["event_data tuple", "event_data"]),
   ("idx_antijoin", "ed_idx_antijoin", ["event_data tuple", "event_data"]),
   ("idx_union", "ed_idx_union", ["event_data tuple", "event_data tuple"]),
   ("wf_idx_set", "ed_wf_idx_set", ["event_data"]),
   ("join_mmsaux", "ed_join_mmsaux", ["event_data"]),
   ("add_new_table_mmsaux", "ed_add_new_table_mmsaux", ["event_data"]),
   ("add_new_ts_mmsaux", "ed_add_new_ts_mmsaux", ["event_data"]),
   ("shift_end", "ed_shift_end", ["event_data"]),
   ("gc_mmsaux", "ed_gc_mmsaux", ["event_data"]),
   ("init_mmsaux", "ed_init_mmsaux", ["event_data"]),
   ("update_mmtaux", "ed_update_mmtaux", ["event_data"]),
   ("init_mmtaux", "ed_init_mmtaux", ["event_data"]),
   ("update_matchF_step", "ed_update_matchF_step", ["event_data"]),
   ("update_matchF_base", "ed_update_matchF_base", ["event_data"]),
   ("mrtabulate", "ed_mrtabulate", ["event_data"]),
   ("get_map_result", "ed_get_map_result", ["event_data"])]
  ["etuple_dict_simps"]\<close>


definition insert_table_into_db :: "string8 \<times> nat \<Rightarrow> event_data table \<Rightarrow> database \<Rightarrow> database" where
  "insert_table_into_db p X db = update_mapping_with (\<lambda>_ tbl _. map ((\<union>) X) tbl) p [X] db"

lemma lookup_update_mapping_with:
  "Mapping.lookup (update_mapping_with f k v m) k' =
    (if k' = k then (case Mapping.lookup m k of None \<Rightarrow> Some v | Some v' \<Rightarrow> Some (f k v' v)) else Mapping.lookup m k')"
  by transfer (auto split: option.splits)

lemma insert_table_into_db_insert:
  "insert_table_into_db p Y (insert_into_db p x db) = insert_table_into_db p (Set.insert x Y) db"
  by (rule mapping_eqI)
    (auto simp: insert_table_into_db_def insert_into_db_def lookup_update_mapping_with split: option.splits)

lemma insert_table_into_db_fold:
  "fold (insert_into_db p) (x # xs) db = insert_table_into_db p (set (x # xs)) db"
proof (induction xs arbitrary: x db)
  case Nil
  show ?case
    by (auto simp: insert_table_into_db_def insert_into_db_def lookup_update_mapping_with
        intro!: mapping_eqI split: option.splits)
next
  case (Cons y ys)
  show ?case
    using Cons.IH[of y "insert_into_db p x db"] by (simp add: insert_table_into_db_insert)
qed

(*<*)
end
(*>*)
