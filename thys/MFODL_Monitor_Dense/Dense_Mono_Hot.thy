(*<*)
theory Dense_Mono_Hot
  imports Dense_RBT_Code
begin
(*>*)

section \<open>The generic operations left on the dense monitor's inner loops\<close>

text \<open>
  @{theory MFODL_Monitor_Dense.Dense_Mono_Sweep} ends with the claim that what is left generic
  is cold.  A profile of the export says otherwise for a handful of operations, all of them at
  the short tuples, and all for one of three reasons.

  \<^item> \<^emph>\<open>A box shadows a monomorphic copy.\<close>  @{theory MFODL_Monitor_Dense.Dense_Code_Opt}
    monomorphises @{const Set.remove} at @{typ "event_data list"} and later, in its list of
    operations whose dictionaries are built once, boxes it at the same type.  Both redirect the
    same term, the box's rule is the one the preprocessor applies, and the monomorphic copy is
    never called: the deletion from a table goes through the generic tree deletion and the
    composite comparator @{text "comparator_list comparator_event_data"}, reached through a
    closure.  That is 4 to 9\% of the run, inclusive, on the ONCE and FRZ benchmarks.  The
    same holds, less expensively, for the sorted list of a table and for the filter of a count
    map, which are boxed but have no copy at all.
  \<^item> \<^emph>\<open>A fold is generic while its step is not.\<close>  @{theory MFODL_Monitor_Dense.Dense_Map_Upd}
    specialises the grouped aggregation's steps @{const gstep_ins} and @{const gstep_del} at
    @{typ event_data}, but not the folds @{const gins} and @{const gdel} over them, nor the
    result @{const gres}, @{const gmr} and the initial state @{const ginit}; the window
    aggregate over a group calls all of these at @{typ event_data}, so it runs the generic
    steps, and their generic one-descent updates and lookups, after all.  On the aggregation
    benchmark that is about a tenth of the run inclusive.
  \<^item> \<^emph>\<open>A dictionary is built per call.\<close>  The one-descent updates of
    @{theory MFODL_Monitor_Dense.Dense_Map_Upd} return a pair containing a tree, and
    @{command lift_definition}'s option @{text code_dt} puts the pair behind an isomorphism whose projection
    takes the key type's @{class ccompare} dictionary without using it.  The monomorphic
    updates call that projection with the dictionary built on the spot, once per update.
\<close>

subsection \<open>The copies\<close>

text \<open>The tree's key list and fold, which the sorted list of a table and the Since
  structure's filter reach, need copies of their own, or the dictionary moves one frame down.\<close>

setup \<open>Monomorphize.monomorphize_cmd
  (let val cnt_set = "(event_data list, nat) mapping \<times> event_data list set" in
    [("RBT_Set2.keys", "edl_rbt_keys", [edl]),
     ("RBT_Set2.fold", "edl_rbt_fold_filter", [edl, cnt_set]),
     ("set_fold_cfi", "edl_fold_cfi_filter", [edl, cnt_set]),
     ("csorted_list_of_set", "edl_csorted_list_of_set", [edl]),
     ("RBT_Mapping2.filter", "edl_rbt_filter_nat", [edl, "nat"]),
     ("Mapping.filter", "edl_mfilter_nat", [edl, "nat"])] end)
  ["edl_dict_simps"]\<close>

text \<open>The grouped aggregation's empty maps at the two value types
  @{theory MFODL_Monitor_Dense.Dense_Code_Opt} has none for, which @{const ginit} starts from.\<close>

definition edl_mempty_nsum :: "(event_data list, nat \<times> integer) mapping" where
  "edl_mempty_nsum = Mapping.empty"
lemma edl_mempty_nsum_code[code]: "edl_mempty_nsum = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: edl_mempty_nsum_def RBT_Mapping_empty)
lemma edl_mempty_nsum_unfold[code_unfold]:
  "(Mapping.empty :: (event_data list, nat \<times> integer) mapping) = edl_mempty_nsum"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data list))
      :: (event_data list, nat \<times> integer) mapping) = edl_mempty_nsum"
  by (simp_all add: edl_mempty_nsum_def)

definition edl_mempty_laux :: "(event_data list, list_aux) mapping" where
  "edl_mempty_laux = Mapping.empty"
lemma edl_mempty_laux_code[code]: "edl_mempty_laux = RBT_Mapping RBT_Mapping2.empty"
  by (simp only: edl_mempty_laux_def RBT_Mapping_empty)
lemma edl_mempty_laux_unfold[code_unfold]:
  "(Mapping.empty :: (event_data list, list_aux) mapping) = edl_mempty_laux"
  "(mapping_empty (of_phantom MAPPING_IMPL(event_data list))
      :: (event_data list, list_aux) mapping) = edl_mempty_laux"
  by (simp_all add: edl_mempty_laux_def)

setup \<open>Monomorphize.monomorphize_cmd
  [("gins", "edl_gins", ["event_data"]),
   ("gdel", "edl_gdel", ["event_data"]),
   ("ginit", "edl_ginit", ["event_data"]),
   ("gmr", "edl_gmr_cnt", ["event_data", "nat"]),
   ("gmr", "edl_gmr_sum", ["event_data", "nat \<times> integer"]),
   ("gmr", "edl_gmr_rank", ["event_data", "list_aux"]),
   ("gres", "edl_gres", ["event_data"])]
  ["edl_dict_simps"]\<close>

text \<open>The projections of the two isomorphisms, boxed at the value types the updates are
  used at, so that their dictionary is built once.\<close>

ML \<open>
val upd_iso = "Dense_Map_Upd.x'b.x_.ccompare.x_.x'a.mapping_rbt.x'b.option.prod.x_x.x'b.x_.ccompare.x_.x'a.rbt.x'b.option.prod.Rep_isom"
val upd2_iso = "Dense_Map_Upd.x'b.x_.ccompare.x_.x'a.mapping_rbt.x'b.prod.x'b.option.prod.x_x.x'b.x_.ccompare.x_.x'a.rbt.x'b.prod.x'b.option.prod.Rep_isom"
val gagg_value_types =
  [("laux", "list_aux"), ("gcnt", "nat \<times> (event_data list, nat) mapping"),
   ("gsum", "(nat \<times> integer) \<times> (event_data list, nat) mapping")]
\<close>

setup \<open>Monomorphize.box_cmd
  (map (fn (tn, ty) => (upd_iso, "edl_upd_iso_" ^ tn ^ "_v", [edl, ty]))
     ([("nat", "nat"), ("nsum", "nat \<times> integer")] @ gagg_value_types)
   @ map (fn (tn, ty) => (upd2_iso, "edl_upd2_iso_" ^ tn ^ "_v", [edl, ty])) gagg_value_types)\<close>

subsection \<open>The intersection at the short tuples' comparator\<close>

text \<open>The intersection of two short tables is the tree intersection of
  @{theory Deriving.RBT_Comparator_Impl} with @{const edl_comparator} passed as its argument, so
  its lookups (the small operand's keys looked up in the other tree) and its splits call the
  comparator through a closure.  These are its copies at that comparator, as
  @{theory MFODL_Monitor_Dense.Dense_Map_Upd} has them for the union and the difference.\<close>

definition edl_map_filter_comp_inter :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list \<times> 'v) list" where
  "edl_map_filter_comp_inter = map_filter_comp_inter edl_comparator"

lemma edl_map_filter_comp_inter_code[code]: "edl_map_filter_comp_inter f t1 t2 =
    List.map_filter (\<lambda>(k, v). case edl_rbtc_lookup t1 k of None \<Rightarrow> None
      | Some v' \<Rightarrow> Some (k, f k v' v)) (RBT_Impl.entries t2)"
  by (simp add: edl_map_filter_comp_inter_def map_filter_comp_inter_def edl_rbtc_lookup_def)

lemma edl_map_filter_comp_inter_unfold[code_unfold]:
  "map_filter_comp_inter edl_comparator = edl_map_filter_comp_inter"
  by (simp add: edl_map_filter_comp_inter_def)

definition edl_rbtc_inter_swap_rec :: "(event_data list \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool \<Rightarrow>
    (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt \<Rightarrow> (event_data list, 'v) rbt" where
  "edl_rbtc_inter_swap_rec = rbt_comp_inter_swap_rec edl_comparator"

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
  "edl_rbtc_inter_with_key = rbt_comp_inter_with_key edl_comparator"

lemma edl_rbtc_inter_with_key_code[code]:
  "edl_rbtc_inter_with_key f t1 t2 = paint RBT_Impl.B (edl_rbtc_inter_swap_rec f False t1 t2)"
  by (simp add: edl_rbtc_inter_with_key_def edl_rbtc_inter_swap_rec_def rbt_comp_inter_with_key_def)

lemma edl_rbtc_inter_with_key_unfold[code_unfold]:
  "rbt_comp_inter_with_key edl_comparator = edl_rbtc_inter_with_key"
  by (simp add: edl_rbtc_inter_with_key_def)

text \<open>And the membership test on a short table, whose code equation compared the lookup with
  @{term "Some ()"} by the generic equality on options.\<close>

lemma edl_rbt_member_lookup[code]:
  "edl_rbt_member t x = (case RBT_Mapping2.lookup t x of None \<Rightarrow> False | Some _ \<Rightarrow> True)"
  by (simp add: edl_rbt_member_code equal split: option.splits)

subsection \<open>The boxes that shadow them\<close>

text \<open>Taken out of the preprocessor here, and again in
  \<^verbatim>\<open>Monitor_Code_Dense\<close>, whose merge of the imports brings them back.\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps
  @{thms edl_remove_v_unfold edl_csorted_list_of_set_v_unfold edl_mfilter_nat_v_unfold})\<close>

(*<*)
end
(*>*)
