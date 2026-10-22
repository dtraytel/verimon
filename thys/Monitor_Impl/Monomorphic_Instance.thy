(*<*)
theory Monomorphic_Instance
  imports Efficient_Instance
begin
(*>*)

section \<open>Monomorphisation of the generated code\<close>

subsection \<open>Two code adaptations\<close>

text \<open>@{const literal_string8} is the identity on the common string representation and is printed
  as such; the union of the sets of two lists becomes the set of their concatenation.\<close>

code_printing
  constant "literal_string8 :: string8 \<Rightarrow> String.literal" \<rightharpoonup> (OCaml) "(fun x -> x)"

lemmas [code_unfold] = set_append[symmetric]

subsection \<open>Monomorphisation as a refinement\<close>

text \<open>Hot polymorphic functions get monomorphic copies @{text "ed_f = f"} and container
  operations boxed values @{text "c_v = Box c"}, so dictionaries at @{typ "event_data tuple"} are
  built once.\<close>

subsubsection \<open>Direct comparator on tuples\<close>

fun ed_comparator :: "event_data tuple comparator" where
  "ed_comparator [] [] = Eq"
| "ed_comparator [] (y # ys) = Lt"
| "ed_comparator (x # xs) [] = Gt"
| "ed_comparator (a # xs) (b # ys) =
    (case comparator_event_data a b of Eq \<Rightarrow> ed_comparator xs ys | r \<Rightarrow> r)"

lemma ed_comparator_eq: "ed_comparator xs ys = comparator_list comparator_event_data xs ys"
  by (induction xs ys rule: ed_comparator.induct) (auto split: order.splits)

lemma ccompare_etuple: "CCOMPARE(event_data tuple) = Some ed_comparator"
  by (simp add: ccompare_list_def ccompare_event_data_def ID_def ed_comparator_eq[abs_def])

lemma ID_ccompare_etuple: "ID CCOMPARE(event_data tuple) = Some ed_comparator"
  by (simp add: ccompare_etuple ID_def)

lemma ccomp_etuple: "(ccomp :: event_data tuple comparator) = ed_comparator"
  by (simp add: ID_ccompare_etuple)

lemma ceq_etuple: "CEQ(event_data tuple) = Some (equality_list (=))"
  by (simp add: ceq_list_def ceq_event_data_def ID_def)

lemma ID_ceq_etuple: "ID CEQ(event_data tuple) = Some (equality_list (=))"
  by (simp add: ceq_etuple ID_def)

lemmas etuple_dict_simps = ccompare_etuple ID_ccompare_etuple ccomp_etuple ceq_etuple ID_ceq_etuple
  option.case option.sel ID_def id_apply

subsubsection \<open>Folds over red-black trees\<close>

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

datatype 'a boxed = Box (unbox: 'a)

ML_file \<open>monomorphize.ML\<close>

subsubsection \<open>Empty containers as values\<close>

lemma RBT_Mapping_empty: "RBT_Mapping RBT_Mapping2.empty = Mapping.empty"
  by (simp add: Mapping.empty_def)

definition ed_bot :: "event_data table" where "ed_bot = {}"

lemma ed_bot_code[code]: "ed_bot = RBT_set RBT_Set2.empty"
  by (simp add: ed_bot_def)

lemma ed_bot_unfold[code_unfold]:
  "(bot :: event_data table) = ed_bot"
  "set_empty (of_phantom SET_IMPL(event_data tuple)) = ed_bot"
  "(empty_table :: event_data table) = ed_bot"
  by (simp_all add: ed_bot_def empty_table_def)

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

subsubsection \<open>Boxed and monomorphic operations\<close>

ML \<open>
val etuple = "event_data tuple"
val ed_value_types =
  [("nat", "nat"), ("tstp", "nat + nat"), ("table", "event_data table"),
   ("sum", "nat \<times> integer"), ("rank", "list_aux")]
val ed_mapping_ops =
  [("Mapping.keys", "keys"), ("Mapping.is_empty", "mis_empty")]
val ed_box_specs =
  [
   ("finite", "ed_finite_v", [etuple]),
   ("set_eq", "ed_set_eq_v", [etuple]),
   ("Set.is_empty", "ed_is_empty_v", [etuple]),
   ("RBT_Set2.fold", "ed_rbt_fold_table_v", [etuple, "event_data table"]),
   ("cluster", "ed_cluster_ed_v", [etuple, "event_data"]),
   ("Mapping.keys", "ed_keys_ed_table_v", ["event_data", "event_data table"]),
   ("Mapping.lookup", "ed_lookup_ed_table_v", ["event_data", "event_data table"])]
  @ maps (fn (c, nm) => map (fn (tn, ty) => (c, "ed_" ^ nm ^ "_" ^ tn ^ "_v", [etuple, ty])) ed_value_types)
      ed_mapping_ops
\<close>

setup \<open>Monomorphize.box_cmd ed_box_specs\<close>

text \<open>Membership, lookup and updates are monomorphised down to the tree primitives, so that
  @{thm [source] ccomp_etuple} replaces the composite comparator by @{const ed_comparator}.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  ([("Set.member", "ed_member", [etuple]),
    ("RBT_Mapping2.lookup", "ed_rbt_lookup_unit", [etuple, "unit"]),
    ("RBT_Mapping2.delete", "ed_rbt_delete_unit", [etuple, "unit"])]
   @ maps (fn (tn, ty) =>
       [("Mapping.lookup", "ed_lookup_" ^ tn, [etuple, ty]),
        ("Mapping.update", "ed_update_" ^ tn, [etuple, ty]),
        ("Mapping.delete", "ed_delete_" ^ tn, [etuple, ty]),
        ("Mapping.combine", "ed_combine_" ^ tn, [ty, etuple]),
        ("RBT_Mapping2.lookup", "ed_rbt_lookup_" ^ tn, [etuple, ty]),
        ("RBT_Mapping2.insert", "ed_rbt_insert_" ^ tn, [etuple, ty]),
        ("RBT_Mapping2.delete", "ed_rbt_delete_" ^ tn, [etuple, ty]),
        ("RBT_Mapping2.join", "ed_rbt_join_" ^ tn, [etuple, ty])]) ed_value_types)
  ["etuple_dict_simps"]\<close>

subsubsection \<open>Compatibility with preprocessor rules\<close>

text \<open>The preprocessor rewrites bottom-up, so the redirections fire inside the left-hand sides
  of other @{text code_unfold} rules; these are restated for the redirected constants.\<close>

lemma ed_member_compat[code_unfold]:
  "Collect (\<lambda>a. ed_member a A \<and> P a) = Set.filter P A"
  "Collect (\<lambda>a. ed_member a A) = A"
  "ed_member a (Collect Q) = Q a"
  "ed_member x (set xs) = List.member xs x"
  unfolding ed_member_unfold[symmetric]
  by auto

lemma ed_bot_compat[code_unfold]:
  "(A = ed_bot) = Set.is_empty A"
  "(ed_bot = A) = Set.is_empty A"
  "set_eq A ed_bot = Set.is_empty A"
  "set_eq ed_bot A = Set.is_empty A"
  by (auto simp: ed_bot_def)

lemma ed_keys_compat[code_unfold]:
  "ed_member k (unbox ed_keys_nat_v m1) = (\<not> Option.is_none (ed_lookup_nat m1 k))"
  "ed_member k (unbox ed_keys_tstp_v m2) = (\<not> Option.is_none (ed_lookup_tstp m2 k))"
  "ed_member k (unbox ed_keys_table_v m3) = (\<not> Option.is_none (ed_lookup_table m3 k))"
  "ed_member k (unbox ed_keys_sum_v m4) = (\<not> Option.is_none (ed_lookup_sum m4 k))"
  "ed_member k (unbox ed_keys_rank_v m5) = (\<not> Option.is_none (ed_lookup_rank m5 k))"
  unfolding ed_member_unfold[symmetric] ed_keys_nat_v_unfold[symmetric] ed_lookup_nat_unfold[symmetric] ed_keys_tstp_v_unfold[symmetric] ed_lookup_tstp_unfold[symmetric] ed_keys_table_v_unfold[symmetric] ed_lookup_table_unfold[symmetric] ed_keys_sum_v_unfold[symmetric] ed_lookup_sum_unfold[symmetric] ed_keys_rank_v_unfold[symmetric] ed_lookup_rank_unfold[symmetric]
  by (simp_all add: Mapping.keys_is_none_rep)

subsection \<open>Bulk construction of tables\<close>

text \<open>@{text rbt_of_sorted_list} builds a table in linear time by @{const rbtreeify} if the list
  is strictly sorted, which is checked as the front end sorts with an unverified comparator.\<close>

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
        linorder.rbt_lookup_rbtreeify[OF lin] linorder.rbt_lookup_rbt_bulkload[OF lin] dom_map_of_conv_image_fst
        image_image)
qed

subsection \<open>Second round of monomorphisation\<close>

text \<open>Boxes for the tree projection and the database operations, and monomorphic copies of
  insertion, tree membership, @{const max} and @{const min}, which otherwise pass dictionaries.\<close>

setup \<open>Monomorphize.box_cmd
  (map (fn (tn, ty) => ("RBT_Mapping2.impl_of", "ed_impl_of_" ^ tn ^ "_v", [etuple, ty])) ed_value_types
   @ [("RBT_Mapping2.impl_of", "ed_impl_of_v", [etuple, "unit"]),
   ("Mapping.lookup", "db_lookup_v", ["string8 \<times> nat", "event_data table list"]),
   ("update_mapping_with", "db_update_with_v", ["string8 \<times> nat", "event_data table list"])])\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("Set.insert", "ed_insert", [etuple]),
   ("RBT_Mapping2.insert", "ed_rbt_insert", [etuple, "unit"]),
   ("RBT_Set2.member", "ed_rbt_member", [etuple]),
   ("max", "ed_max_integer", ["integer"]),
   ("max", "ed_max_nat", ["nat"]),
   ("min", "ed_min_nat", ["nat"]),
   ("singleton_table", "ed_singleton_table", ["event_data"]),
   ("unit_table", "ed_unit_table", ["event_data"]),
   ("valid_tuple", "ed_valid_tuple", ["event_data"]),
   ("init_mmsaux", "ed_init_mmsaux", ["event_data"]),
   ("init_mmtaux", "ed_init_mmtaux", ["event_data"])]
  ["etuple_dict_simps"]\<close>

(*<*)
end
(*>*)
