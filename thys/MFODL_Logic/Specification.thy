(*<*)
theory Specification
  imports
    Typing
    Monitorable
    "MFOTL_Monitor_Devel.Abstract_Monitor"
begin
(*>*)

section \<open>Specification\<close>

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
