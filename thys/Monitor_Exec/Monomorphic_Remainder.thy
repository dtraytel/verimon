(*<*)
theory Monomorphic_Remainder
  imports Monomorphic_Exec
begin
(*>*)



section \<open>Monomorphisation of the remaining operations\<close>

text \<open>Monomorphic copies of the operations that the generated code still reaches with a
  dictionary at a closed type.\<close>

subsection \<open>Dictionaries of closed types\<close>

text \<open>Class operations as equations, by which instantiated code equations lose their dictionary
  lookups.\<close>

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

subsection \<open>Operations on numbers and tuples\<close>

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

setup \<open>mono
  [("wf_table_of_set_args", "ed_wf_table_of_set_args", ["event_data"])]
  dicts\<close>

subsection \<open>Regular expressions and predicate tables\<close>

text \<open>The recursion check's set operations stay generic: @{typ rec_safety} lacks the container
  sorts.\<close>

setup \<open>mono
  [("Set.bind", "mregex_bind", ["mregex", "mregex"]),
   ("sorted_list_of_set", "mregex_sorted_list_of_set", ["mregex"]),
   ("less_eq :: _ set \<Rightarrow> _", "mregex_subset", ["mregex"]),
   ("RBT_Mapping2.bulkload", "mregex_rbt_bulkload", ["mregex", "event_data list set"])]
  dicts\<close>

subsection \<open>Treelists of rank aggregations\<close>

setup \<open>mono
  [("insert_treelist", "int_insert_treelist", ["integer"]),
   ("remove_treelist", "int_remove_treelist", ["integer"]),
   ("empty_treelist", "int_empty_treelist", ["integer"]),
   ("get_treelist", "int_get_treelist", ["integer"]),
   ("insert_treelist", "s8_insert_treelist", ["string8"]),
   ("remove_treelist", "s8_remove_treelist", ["string8"]),
   ("empty_treelist", "s8_empty_treelist", ["string8"])]
  dicts\<close>

subsection \<open>Second pass\<close>

text \<open>Removing one instantiation of an operation exposes the next, so the sweep is iterated.\<close>

setup \<open>mono
  [("Set.member", "mregex_member", ["mregex"]),
   ("sort_key", "mregex_sort_key", ["mregex", "mregex"])]
  dicts\<close>

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

text \<open>@{text these}, @{text gadd_new_ts_msaux_add} and @{text safe_regex} stay generic: their
  type variable is fixed, so @{text monomorphize} cannot instantiate them.\<close>

(*<*)
end
(*>*)
