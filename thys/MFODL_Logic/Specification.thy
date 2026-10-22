(*<*)
theory Specification
  imports
    Typing
    Monitorable
    "MFOTL_Monitor_Devel.Abstract_Monitor"
begin
(*>*)

section \<open>MFODL formulas as specifications\<close>

locale traces_downward_closed =
  fixes traces :: "Formula.trace set"
  assumes closed: "\<sigma> \<in> traces \<Longrightarrow> (\<And>i. \<Gamma> \<sigma>' i \<subseteq> \<Gamma> \<sigma> i) \<Longrightarrow> \<sigma>' \<in> traces"
begin

lemma map_\<Gamma>_subset_traces: "\<sigma> \<in> traces \<Longrightarrow> (\<And>D. f D \<subseteq> D) \<Longrightarrow> map_\<Gamma> f \<sigma> \<in> traces"
  by (simp add: closed)

sublocale formula_slicer: sliceable_fo_spec "Formula.nfv \<phi>" "Formula.fv_list \<phi>" traces
  "relevant_events \<phi>" "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" for \<phi>
  by unfold_locales
    (auto simp add: fvi_less_nfv closed iff: sat_slice_strong intro!: sat_fv_cong)

end

locale wty_mfodl =
  fixes \<phi> :: "ty Formula.formula" and SIG :: sig and ENV :: tyenv
  assumes well_typed: "SIG, ENV \<turnstile> \<phi>"
begin

definition "traces = {\<sigma>. wty_trace SIG \<sigma>}"

sublocale traces_downward_closed traces
  by unfold_locales (auto simp add: traces_def wty_envs_def)

end

locale future_bounded_mfodl = wty_mfodl +
   assumes future_bounded: "Safety.future_bounded \<phi>"

lemma (in future_bounded_mfodl) prefixes_alt: "formula_slicer.prefixes = {\<pi>. wty_prefix SIG \<pi>}"
  unfolding formula_slicer.prefixes_def
  using ex_prefix_of_wty prefix_of_wty_trace
  by (fastforce simp: traces_def)

locale verimon_spec = wty_mfodl +
   assumes monitorable: "mmonitorable \<phi>"

sublocale verimon_spec \<subseteq> future_bounded_mfodl
  using monitorable by unfold_locales (simp add: mmonitorable_def)

(*<*)
end
(*>*)
