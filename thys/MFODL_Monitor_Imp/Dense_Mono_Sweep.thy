(*<*)
theory Dense_Mono_Sweep
  imports Dense_Code_Opt
begin
(*>*)

section \<open>The remaining generic operations of the generated code\<close>

text \<open>
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} and @{theory MFODL_Monitor_Imp.Dense_Code_Opt}
  monomorphise the operations of the inner loops -- the containers at @{typ "event_data tuple"}
  and at @{typ "event_data list"} -- because those were what the profiles charged for.  What is
  left over is everything else: operations the generated code still reaches with a type class
  dictionary in hand, at types that are closed and known.  None of them is hot, so this section
  buys no measurable time; it is here because the exported code is meant to be monomorphic
  throughout, and a dictionary that survives is a dictionary someone has to reason about when
  reading the export.

  The remaining genericity divides into three kinds, and only the first is work:
  \<^item> \<^emph>\<open>Operations\<close> reached at one closed type -- the ones below.  Each gets a monomorphic copy
    whose code equations are the originals instantiated at that type, and a @{text code_unfold}
    rule that redirects the applied occurrences, exactly as in the two theories above.
  \<^item> \<^emph>\<open>Operations reached at several closed types\<close> -- one copy per type; the subset test and the
    treelists of the rank aggregations are the cases that occur.
  \<^item> \<^emph>\<open>Dictionary constructors\<close> (@{text ccompare_list}, @{text ceq_option}, @{text equal_prod},
    \<dots>).  These are not targets at all: they exist only to feed a generic consumer, and they
    disappear as the consumers above are specialised.  They are the majority of what a count of
    the dictionary-taking definitions in the export reports.
\<close>

subsection \<open>The dictionaries of the remaining closed types\<close>

text \<open>Each family needs its class operations as an explicit equation, so that instantiating a
  code equation at the type can rewrite the dictionary lookups away.  These mirror
  @{thm [source] etuple_dict_simps} and @{thm [source] edl_dict_simps}.\<close>

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
             "etuple_dict_simps", "edl_dict_simps"]
\<close>

subsection \<open>The operations over time points and over event data\<close>

text \<open>The time points are @{typ nat}: the buffers, the interval arithmetic of the time-stamp
  bookkeeping and the free-variable sets of the compiler all work at that type.\<close>

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

text \<open>The order on @{typ event_data} itself, which the extremum aggregations fold with.\<close>

setup \<open>mono
  [("min", "ed_min", ["event_data"]),
   ("max", "ed_max", ["event_data"])]
  dicts\<close>

subsection \<open>The operations over the wide tuples that the two earlier passes left\<close>

setup \<open>mono
  [("filter_set", "ed_filter_set_m", ["nat", "event_data option list"]),
   ("wf_table_of_set_args", "ed_wf_table_of_set_args", ["event_data"]),
   ("set_of_idx", "etuple_set_of_idx", ["event_data option list", "event_data option list"]),
   ("Set.equal_set_inst.equal_set", "etuple_equal_set", ["event_data option list"]),
   ("RBT_Mapping2.entries", "etuple_rbt_entries", ["event_data option list", "unit"])]
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
   ("Mapping.lookup_default", "mregex_lookup_default", ["mregex", "event_data option list set"]),
   ("RBT_Mapping2.bulkload", "mregex_rbt_bulkload", ["mregex", "event_data option list set"]),
   ("Mapping.map_values", "pn_map_values",
      ["string8 \<times> nat", "event_data option list set", "event_data option list set"])]
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
   ("length_treelist", "int_length_treelist", ["integer"]),
   ("insert_treelist", "s8_insert_treelist", ["string8"]),
   ("remove_treelist", "s8_remove_treelist", ["string8"]),
   ("empty_treelist", "s8_empty_treelist", ["string8"])]
  dicts\<close>

(*<*)
end
(*>*)
