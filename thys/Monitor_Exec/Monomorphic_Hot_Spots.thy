(*<*)
theory Monomorphic_Hot_Spots
  imports Efficient_RBT
begin
(*>*)



section \<open>Monomorphisation of hot spots\<close>

subsection \<open>Copies at the tuples\<close>

text \<open>Without copies, the tree's key list and fold pass the dictionary down.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (let val cnt_set = "(event_data list, nat) mapping \<times> event_data list set" in
    [("RBT_Set2.keys", "edl_rbt_keys", [edl]),
     ("RBT_Set2.fold", "edl_rbt_fold_filter", [edl, cnt_set]),
     ("set_fold_cfi", "edl_fold_cfi_filter", [edl, cnt_set]),
     ("csorted_list_of_set", "edl_csorted_list_of_set", [edl]),
     ("RBT_Mapping2.filter", "edl_rbt_filter_nat", [edl, "nat"]),
     ("Mapping.filter", "edl_mfilter_nat", [edl, "nat"])] end)
  ["etuple_dict_simps"]\<close>

text \<open>Copies of the grouped aggregation's folds, initial state and results call the specialised
  steps.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  [("gins", "edl_gins", ["event_data"]),
   ("gdel", "edl_gdel", ["event_data"]),
   ("ginit", "edl_ginit", ["event_data"]),
   ("gmr", "edl_gmr_cnt", ["event_data", "nat"]),
   ("gmr", "edl_gmr_sum", ["event_data", "nat \<times> integer"]),
   ("gmr", "edl_gmr_rank", ["event_data", "list_aux"]),
   ("gres", "edl_gres", ["event_data"])]
  ["etuple_dict_simps"]\<close>

text \<open>The isomorphisms that @{text code_dt} introduces for the updates take an unused
  dictionary; their projections are boxed, so that it is built once.\<close>

ML \<open>
val upd_iso = "Efficient_Map_Updates.x'b.x_.ccompare.x_.x'a.mapping_rbt.x'b.option.prod.x_x.x'b.x_.ccompare.x_.x'a.rbt.x'b.option.prod.Rep_isom"
val upd2_iso = "Efficient_Map_Updates.x'b.x_.ccompare.x_.x'a.mapping_rbt.x'b.prod.x'b.option.prod.x_x.x'b.x_.ccompare.x_.x'a.rbt.x'b.prod.x'b.option.prod.Rep_isom"
val gagg_value_types =
  [("laux", "list_aux"), ("gcnt", "nat \<times> (event_data list, nat) mapping"),
   ("gsum", "(nat \<times> integer) \<times> (event_data list, nat) mapping")]
\<close>

setup \<open>Monomorphize.box_cmd
  (map (fn (tn, ty) => (upd_iso, "edl_upd_iso_" ^ tn ^ "_v", [edl, ty]))
     ([("nat", "nat"), ("nsum", "nat \<times> integer")] @ gagg_value_types)
   @ map (fn (tn, ty) => (upd2_iso, "edl_upd2_iso_" ^ tn ^ "_v", [edl, ty])) gagg_value_types)\<close>

subsection \<open>Intersection at the tuples' comparator\<close>

text \<open>Copies of the tree intersection call @{const ed_comparator} directly.\<close>

definition edl_map_filter_comp_inter :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list \<times> 'v) list" where
  "edl_map_filter_comp_inter = map_filter_comp_inter ed_comparator"

lemma edl_map_filter_comp_inter_code[code]: "edl_map_filter_comp_inter f t1 t2 =
    List.map_filter (\<lambda>(k, v). case ed_rbtc_lookup t1 k of None \<Rightarrow> None
      | Some v' \<Rightarrow> Some (k, f k v' v)) (RBT_Impl.entries t2)"
  by (simp add: edl_map_filter_comp_inter_def map_filter_comp_inter_def ed_rbtc_lookup_def)

lemma edl_map_filter_comp_inter_unfold[code_unfold]:
  "map_filter_comp_inter ed_comparator = edl_map_filter_comp_inter"
  by (simp add: edl_map_filter_comp_inter_def)

definition edl_rbtc_inter_swap_rec :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_inter_swap_rec = rbt_comp_inter_swap_rec ed_comparator"

lemma edl_rbtc_inter_swap_rec_code[code]: "edl_rbtc_inter_swap_rec f \<gamma> t1 t2 = (let (\<gamma>, t2, t1) =
    if flip_rbt t2 t1 then (\<not>\<gamma>, t1, t2) else (\<gamma>, t2, t1);
    f' = if \<gamma> then (\<lambda>k v v'. f k v' v) else f in
    if small_rbt t2 then rbtreeify (edl_map_filter_comp_inter f' t1 t2)
    else case t1 of rbt.Empty \<Rightarrow> rbt.Empty
    | Branch x l1 a b r1 \<Rightarrow>
      (case edl_rbtc_split t2 a of (l2, \<beta>, r2) \<Rightarrow>
        let l' = edl_rbtc_inter_swap_rec f \<gamma> l1 l2; r' = edl_rbtc_inter_swap_rec f \<gamma> r1 r2 in
        (case \<beta> of None \<Rightarrow> rbt_join2 l' r' | Some b' \<Rightarrow> rbt_join l' a (f' a b b') r')))"
  unfolding edl_rbtc_inter_swap_rec_def edl_map_filter_comp_inter_def edl_rbtc_split_def
  by (rule rbt_comp_inter_swap_rec.simps)

definition edl_rbtc_inter_with_key :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_inter_with_key = rbt_comp_inter_with_key ed_comparator"

lemma edl_rbtc_inter_with_key_code[code]:
  "edl_rbtc_inter_with_key f t1 t2 = RBT_Impl.paint RBT_Impl.B (edl_rbtc_inter_swap_rec f False t1 t2)"
  by (simp add: edl_rbtc_inter_with_key_def edl_rbtc_inter_swap_rec_def rbt_comp_inter_with_key_def)

lemma edl_rbtc_inter_with_key_unfold[code_unfold]:
  "rbt_comp_inter_with_key ed_comparator = edl_rbtc_inter_with_key"
  by (simp add: edl_rbtc_inter_with_key_def)

text \<open>Membership matches on the lookup instead of comparing it with @{term "Some ()"}.\<close>

lemma ed_rbt_member_lookup[code]:
  "ed_rbt_member t x = (case RBT_Mapping2.lookup t x of None \<Rightarrow> False | Some _ \<Rightarrow> True)"
  by (simp add: ed_rbt_member_code equal split: option.splits)

(*<*)
end
(*>*)
