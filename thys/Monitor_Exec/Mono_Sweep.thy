(*<*)
theory Mono_Sweep
  imports Tuple_Code
begin
(*>*)



ML \<open>
val mono = Monomorphize.monomorphize_cmd
val dicts = ["nat_dict_simps", "ed_dict_simps", "mregex_dict_simps", "s8_dict_simps",
             "etuple_dict_simps"]
\<close>

subsection \<open>The operations over time points\<close>

text \<open>The time points are @{typ nat}: the buffers, the interval arithmetic of the time-stamp
  bookkeeping and the free-variable sets of the compiler all work at that type.  The order on
  @{typ event_data}, which the extremum aggregations fold with, is monomorphised in
  @{theory Monitor_Impl.Monomorphic_Code} already.\<close>

setup \<open>mono
  [("Set.member", "nat_member", ["nat"]),
   ("comparator_of", "nat_comparator_of", ["nat"]),
   ("sum_list", "nat_sum_list", ["nat"]),
   ("Max", "nat_Max", ["nat"]),
   ("Rings.dvd_class.dvd", "nat_dvd", ["nat"]),
   ("less_eq :: _ set \<Rightarrow> _", "nat_subset", ["nat"])]
  dicts\<close>

setup \<open>Monomorphize.box_cmd
  [("atLeastLessThan", "nat_atLeastLessThan_v", ["nat"])]\<close>

subsection \<open>The operations over the tuples that the two earlier passes left\<close>

setup \<open>mono
  [("wf_table_of_set_args", "ed_wf_table_of_set_args", ["event_data"])]
  dicts\<close>

subsection \<open>The regular expressions and the predicate table of the compiler\<close>

text \<open>Cold -- entered once per formula rather than once per time point -- but generic all the
  same.  @{typ mregex} is the state type of the match automata and @{typ "string8 \<times> nat"}
  the key of the predicate table.  The set
  operations of the recursion check itself stay generic: @{typ rec_safety} is a lattice without
  the container sorts, so instantiating them there makes the code generator ask for arities it
  does not have.\<close>

setup \<open>mono
  [("Set.bind", "mregex_bind", ["mregex", "mregex"]),
   ("sorted_list_of_set", "mregex_sorted_list_of_set", ["mregex"]),
   ("less_eq :: _ set \<Rightarrow> _", "mregex_subset", ["mregex"]),
   ("RBT_Mapping2.bulkload", "mregex_rbt_bulkload", ["mregex", "event_data list set"])]
  dicts\<close>

subsection \<open>The treelists of the rank aggregations\<close>

text \<open>@{const insert_treelist} and its neighbours are the only place the exported code still
  passed an @{class equal} and a @{class linorder} dictionary down a tree descent.  They are
  reached at two closed types -- the integer values of @{const Formula.Agg_Min},
  @{const Formula.Agg_Max} and @{const Formula.Agg_Med}, and the string values of the first two
  -- so each gets a copy.  They are cold: on \<^verbatim>\<open>aggonce-min50\<close> the whole rank path is under
  a percent of the run, and this is for the sake of the export, not of the clock.\<close>

setup \<open>mono
  [("insert_treelist", "int_insert_treelist", ["integer"]),
   ("remove_treelist", "int_remove_treelist", ["integer"]),
   ("empty_treelist", "int_empty_treelist", ["integer"]),
   ("get_treelist", "int_get_treelist", ["integer"]),
   ("insert_treelist", "s8_insert_treelist", ["string8"]),
   ("remove_treelist", "s8_remove_treelist", ["string8"]),
   ("empty_treelist", "s8_empty_treelist", ["string8"])]
  dicts\<close>

subsection \<open>A second pass\<close>

text \<open>Removing the dominant instantiation of a generic operation does not remove the operation
  while another instantiation still reaches it, and it promotes the next instantiation into
  view: @{const Set.member} left the list at @{typ nat} and re-entered it at @{typ mregex}.
  The sweep is therefore iterative.  This is the next layer.\<close>

setup \<open>mono
  [("Set.member", "mregex_member", ["mregex"]),
   ("sort_key", "mregex_sort_key", ["mregex", "mregex"])]
  dicts\<close>

text \<open>The structures over the short tuples that the first pass left: the index of the join and
  of the Since, and the window operations that report what entered and what left.\<close>

setup \<open>mono
  [("csl", "edl_csl", ["event_data list"]),
   ("ecard", "edl_ecard", ["event_data list"]),
   ("card", "edl_card", ["event_data list"]),
   ("cluster", "edl_cluster", ["event_data list", "event_data list"]),
   ("rbt_of_sorted_list", "edl_rbt_of_sorted_list", ["event_data list"]),
   ("mapping_delete_set", "edl_mapping_delete_set", ["event_data list", "nat"]),
   ("mrestrict1_cfi", "edl_mrestrict1_cfi", ["event_data list", "event_data list set"]),
   ("etabc", "eo_etabc", ["event_data"]),
   ("eidx_add1_cfi", "ed_eidx_add1_cfi", ["event_data"]),
   ("eidx_del1_cfi", "ed_eidx_del1_cfi", ["event_data"])]  dicts\<close>

text \<open>Three more are recorded as not done for the same reason as @{text all_interval}:
  @{text these}, @{text gadd_new_ts_msaux_add} and @{text safe_regex} are resolved to constants
  whose type variable is fixed rather than schematic, so @{text monomorphize} has nothing to
  instantiate.  Lifting that restriction is a change to \<^file>\<open>../Monitor_Impl/monomorphize.ML\<close>
  rather than a new spec.\<close>

(*<*)
end
(*>*)
