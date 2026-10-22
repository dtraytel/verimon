(*<*)
theory Mono_Sweep_Proof
  imports "Monitor_Exec.Mono_Sweep" Tuple_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



section \<open>The remaining generic operations of the generated code\<close>

text \<open>
  @{theory Monitor_Impl.Monomorphic_Code} and @{theory MFODL_Monitor_Exec.Tuple_Code}
  monomorphise the operations of the inner loops -- the containers at @{typ "event_data list"}
  -- because those were what the profiles charged for.  What is left over is everything else:
  operations the generated code still reaches with a type class dictionary in hand, at types
  that are closed and known.  None of them is hot, so this section buys no measurable time; it
  is here because the exported code is meant to be monomorphic throughout, and a dictionary that
  survives is a dictionary someone has to reason about when reading the export.

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

end
(*>*)
