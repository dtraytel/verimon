(*<*)
theory Specification
  imports
    Typing
    Monitorable
begin
(*>*)

section \<open>Specification\<close>

lemma wty_db_empty: "wty_db S {}"
  by (simp add: wty_db_def)

lemma prefix_of_wty_trace:
  assumes "wty_trace S \<sigma>" and "prefix_of \<pi> \<sigma>"
  shows "wty_prefix S \<pi>"
proof -
  from assms(1) have "\<forall>i. wty_db S (\<Gamma> \<sigma> i)"
    by (simp add: wty_envs_def wty_db_def)
  with assms(2) show ?thesis
    by (transfer fixing: S) (metis in_set_conv_nth stake_nth)
qed

lemma ex_prefix_of_wty:
  assumes "wty_prefix S p"
  shows "\<exists>s. prefix_of p s \<and> wty_trace S s"
proof -
  from assms have "\<exists>s. prefix_of p s \<and> (\<forall>i. wty_db S (\<Gamma> s i))"
    proof (transfer fixing: S, intro bexI CollectI conjI)
    fix p :: "((string8 \<times> event_data list) set \<times> nat) list"
    assume *: "sorted (map snd p)"
    let ?\<sigma> = "p @- smap (Pair {}) (fromN (snd (last p)))"
    show "stake (length p) ?\<sigma> = p" by (simp add: stake_shift)
    assume "\<forall>x\<in>set p. wty_db S (fst x)"
    then show "\<forall>i. wty_db S (fst (snth ?\<sigma> i))"
      by (simp add: shift_snth wty_db_empty)
    have le_last: "snd (p ! i) \<le> snd (last p)" if "i < length p" for i
      using sorted_nth_mono[OF *, of i "length p - 1"] that
      by (cases p) (auto simp: last_conv_nth nth_Cons')
    with * show "ssorted (smap snd ?\<sigma>)"
      by (force simp: ssorted_iff_mono sorted_iff_nth_mono shift_snth)
    show "sincreasing (smap snd ?\<sigma>)"
    proof (rule sincreasingI)
      fix x
      have "x < snth (smap snd ?\<sigma>) (Suc (length p + x))"
        by simp (metis Suc_pred add.commute diff_Suc_Suc length_greater_0_conv less_add_Suc1 less_diff_conv)
      then show "\<exists>i. x < snth (smap snd ?\<sigma>) i" ..
    qed
  qed
  then show ?thesis by (auto simp: wty_envs_def wty_db_def)
qed

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
