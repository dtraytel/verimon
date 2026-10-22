(*<*)
theory Correct_Envs
  imports
    "Monitor_Algorithm.Monitor"
    Progress
begin
(*>*)


subsection \<open> Well-formed envs \<close>

declare progress_le_gen[simp]

definition "wf_envs S \<sigma> j \<delta> P P' V db =
  (dom V = dom P \<and>
   Mapping.keys db \<supseteq> dom P \<union> (\<Union>k \<in> {j ..< j + \<delta>}. {(p, n). \<exists>x. (p, x) \<in> \<Gamma> \<sigma> k \<and> n = length x}) \<and>
   rel_mapping (\<le>) P P' \<and>
   pred_mapping (\<lambda>i. i \<le> j) P \<and>
   pred_mapping (\<lambda>i. i \<le> j + \<delta>) P' \<and>
   (\<forall>p \<in> Mapping.keys db - dom P. the (Mapping.lookup db p) = map (\<lambda>k. {ts. (fst p, ts) \<in> \<Gamma> \<sigma> k \<and> length ts = snd p}) [j ..< j + \<delta>]) \<and>
   (\<forall>p \<in> dom P. list_all2 (\<lambda>i X. X = {v. length v = snd p \<and> the (V p) v i}) [the (P p)..<the (P' p)] (the (Mapping.lookup db p))) \<and>
   wty_envs S \<sigma> V \<and>
   (\<forall>p \<in> Mapping.keys db. \<forall>X \<in> set (the (Mapping.lookup db p)). finite X))"

lemma wf_envs_mk_db:
  assumes "wty_trace S \<sigma>" "finite (\<Gamma> \<sigma> j)"
  shows "wf_envs S \<sigma> j 1 Map.empty Map.empty Map.empty (mk_db (\<Gamma> \<sigma> j))"
proof -
  have fin: "finite {ts. (p, ts) \<in> \<Gamma> \<sigma> j \<and> n = length ts}" for p n
    by (rule finite_subset[OF _ finite_imageI[OF assms(2), of snd]]) force
  have F: "\<forall>p \<in> Mapping.keys (mk_db (\<Gamma> \<sigma> j)). \<forall>X \<in> set (the (Mapping.lookup (mk_db (\<Gamma> \<sigma> j)) p)). finite X"
    using fin by (auto simp: keys_dom_lookup Mapping.lookup.rep_eq mk_db.rep_eq split: if_splits)
  show ?thesis
    unfolding wf_envs_def
  proof (intro conjI)
    show "\<forall>p \<in> Mapping.keys (mk_db (\<Gamma> \<sigma> j)). \<forall>X \<in> set (the (Mapping.lookup (mk_db (\<Gamma> \<sigma> j)) p)). finite X"
      by (rule F)
  qed (use assms(1) in \<open>auto simp: keys_dom_lookup Mapping.lookup.rep_eq mk_db.rep_eq rel_mapping_alt
    domIff split: if_splits\<close>)
qed

lemma wf_envs_empty: "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow>
  wf_envs S \<sigma> (j + \<delta>) 0 P' P' V (Mapping.map_values (\<lambda>_ _. []) db)"
  by (auto 0 4 simp: wf_envs_def rel_mapping_alt set_eq_iff domIff lookup_map_values
      map_option_case keys_dom_lookup subset_iff split: option.splits)

lemma wf_envs_update:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
    and m_eq: "m = Formula.nfv \<phi>"
    and in_fv: "{0 ..< m} \<subseteq> fv \<phi>"
    and xs: "list_all2 (\<lambda>i. sat_table \<sigma> V m UNIV [0..<m] i \<phi>)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    and safe: "safe_formula \<phi>"
    and wty: "S, E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> progress \<sigma> P \<phi> j)) (P'((p, m) \<mapsto> progress \<sigma> P' \<phi> (j + \<delta>)))
    (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>))
    (Mapping.update (p, m) xs db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 3
  from assms show ?case
    by (auto simp: wf_envs_def pred_mapping_alt progress_le progress_mono_gen
        intro!: rel_mapping_map_upd)
next
  case (6 p')
  with assms show ?case by (cases "p' \<in> dom P") (auto simp: wf_envs_def lookup_update')
next
  case (7 p')
  have "list_all2 (\<lambda>x y. y = {v. length v = m \<and> Formula.sat \<sigma> V v x \<phi>})
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    using xs by (rule list.rel_mono_strong) (rule qtable_upt_eq)
  moreover have "list_all2 (\<lambda>i X. X = {v. length v = snd p' \<and> the (V p') v i}) [the (P p')..<the (P' p')] (the (Mapping.lookup db p'))"
    if "(p, m) \<noteq> p'"
  proof -
    from that 7 have "p' \<in> dom P" by simp
    with wf_envs show ?thesis by (simp add: wf_envs_def)
  qed
  ultimately show ?case
    by (auto simp add: list.rel_map image_iff lookup_update')
next
  case 8
  from wf_envs have "wty_envs S \<sigma> V" by (simp add: wf_envs_def)
  then show ?case unfolding wty_envs_def
    using ty_of_sat_safe[OF safe wty] in_fv 
    by (auto simp: wty_envs_def wty_event_def wty_tuple_def list_all2_conv_all_nth m_eq domIff)
next
  case (9 p' X)
  show ?case
  proof (cases "p' = (p, m)")
    case True
    with 9 have "X \<in> set xs"
      by (simp add: lookup_update')
    then obtain k where "k < length xs" "X = xs ! k"
      by (auto simp: in_set_conv_nth)
    with xs show ?thesis
      by (auto simp: list_all2_conv_all_nth dest: qtableD(5))
  next
    case False
    with 9 have "p' \<in> Mapping.keys db" "X \<in> set (the (Mapping.lookup db p'))"
      by (simp_all add: lookup_update' keys_dom_lookup domIff)
    with wf_envs show ?thesis
      by (simp add: wf_envs_def)
  qed
qed (use assms in \<open>auto simp: wf_envs_def subset_iff\<close>)

lemma wf_envs_update_sup:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
    and m_eq: "m = Formula.nfv \<phi>"
    and in_fv: "{0 ..< m} \<subseteq> fv \<phi>"
    and xs': "list_all2 (\<lambda>i. qtable [0..<m] (mem_restr UNIV [0..<m])
      (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto>  X)) v i \<phi>) (val m [0..<m] v) i))
      [letpast_progress \<sigma> P (p, m) \<phi> j..<letpast_progress \<sigma> P' (p, m) \<phi> (j+\<delta>)] xs'"
    and safe: "safe_formula \<phi>"
    and wty: "S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> (letpast_progress \<sigma> P (p, m) \<phi> j))) (P'((p, m) \<mapsto> (letpast_progress \<sigma> P' (p, m) \<phi> (j+\<delta>))))
    (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>)))
    (Mapping.update (p, m) xs' db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 4
  with assms show ?case
    by(auto simp add: letpast_progress_le wf_envs_def)
next
  case 5
  with assms show ?case
    by(auto simp add: letpast_progress_le wf_envs_def)
next
  case 3
  from assms show ?case
    by (auto simp: wf_envs_def pred_mapping_alt progress_le progress_mono_gen
        intro!: rel_mapping_map_upd letpast_progress_mono)
next
  case (6 p')
  with assms show ?case by (cases "p' \<in> dom P") (auto simp: wf_envs_def lookup_update')
next
  case (7 p')
  let ?S = "\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>"
  have "list_all2 (\<lambda>x y. y = {v. length v = m \<and> letpast_sat ?S v x})
      [letpast_progress \<sigma> P (p, m) \<phi> j..<letpast_progress \<sigma> P' (p, m) \<phi> (j+\<delta>)] xs'"
    using xs' by (rule list.rel_mono_strong) (rule qtable_upt_eq)
  moreover have "list_all2 (\<lambda>i X. X = {v. length v = snd p' \<and> the (V p') v i}) [the (P p')..<the (P' p')] (the (Mapping.lookup db p'))"
    if "(p, m) \<noteq> p'"
  proof -
    from that 7 have "p' \<in> dom P" by simp
    with wf_envs show ?thesis by (simp add: wf_envs_def)
  qed
  ultimately show ?case
    by (auto simp add: list.rel_map lookup_update')
next
  case 8
  have wty_envs: "wty_envs S \<sigma> V" using wf_envs by (auto simp:wf_envs_def)
  show ?case using wty_envs_letpast_update[OF in_fv[unfolded m_eq] safe wty[unfolded m_eq] wty_envs] m_eq by auto
next
  case (9 p' X)
  show ?case
  proof (cases "p' = (p, m)")
    case True
    with 9 have "X \<in> set xs'"
      by (simp add: lookup_update')
    then obtain k where "k < length xs'" "X = xs' ! k"
      by (auto simp: in_set_conv_nth)
    with xs' show ?thesis
      by (auto simp: list_all2_conv_all_nth dest: qtableD(5))
  next
    case False
    with 9 have "p' \<in> Mapping.keys db" "X \<in> set (the (Mapping.lookup db p'))"
      by (simp_all add: lookup_update' keys_dom_lookup domIff)
    with wf_envs show ?thesis
      by (simp add: wf_envs_def)
  qed
qed (use assms in \<open>auto simp: wf_envs_def subset_iff\<close>)

lemma wf_envs_update2:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
    and m_eq: "m = Formula.nfv \<phi>"
    and in_fv: "{0 ..< m} \<subseteq> fv \<phi>"
    and rel: "rel_mapping (\<le>) P P'"
    and "i\<le>i'"
    and "i\<le>j"
    and "i'\<le>j+\<delta>"
    and xs: "list_all2 (\<lambda>i. qtable [0..<m] (mem_restr UNIV [0..<m])
      (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>) (val m [0..<m] v) i))
      [i..<i'] xs"
    and safe: "safe_formula \<phi>"
    and wty: "S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> i)) (P'((p, m) \<mapsto> i'))
    (V((p, m) \<mapsto> \<lambda>w j. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>) w j))
    (Mapping.update (p, m) xs db)"
  unfolding wf_envs_def 
proof (intro conjI ballI, goal_cases)
  case 3
  from assms show ?case
    by (auto)
next
  case (6 p')
  with assms show ?case by (cases "p' \<in> dom P") (auto simp: wf_envs_def lookup_update')
next
  case (7 p')
  have "list_all2 (\<lambda>x y. y = {v. length v = m \<and> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(p' \<mapsto> X)) v i \<phi>) v x})
      [i..<i'] xs" if "(p, m) = p'"
    unfolding that[symmetric] using xs by (rule list.rel_mono_strong) (rule qtable_upt_eq)
  moreover have "list_all2 (\<lambda>i X. X = {v. length v = snd p' \<and> the (V p') v i}) [the (P p')..<the (P' p')] (the (Mapping.lookup db p'))"
    if "(p, m) \<noteq> p'"
  proof -
    from that 7 have "p' \<in> dom P" by simp
    with wf_envs show ?thesis by (simp add: wf_envs_def)
  qed
  ultimately show ?case
    by (auto simp add: list.rel_map image_iff lookup_update')
next
  case (8)
  have wty_envs: "wty_envs S \<sigma> V" using wf_envs by (auto simp:wf_envs_def)
  show ?case using wty_envs_letpast_update in_fv wty safe m_eq wty_envs by auto 
next
  case (9 p' X)
  show ?case
  proof (cases "p' = (p, m)")
    case True
    with 9 have "X \<in> set xs"
      by (simp add: lookup_update')
    then obtain k where "k < length xs" "X = xs ! k"
      by (auto simp: in_set_conv_nth)
    with xs show ?thesis
      by (auto simp: list_all2_conv_all_nth dest: qtableD(5))
  next
    case False
    with 9 have "p' \<in> Mapping.keys db" "X \<in> set (the (Mapping.lookup db p'))"
      by (simp_all add: lookup_update' keys_dom_lookup domIff)
    with wf_envs show ?thesis
      by (simp add: wf_envs_def)
  qed
qed (use assms in \<open>auto simp: wf_envs_def subset_iff\<close>)
lemma wf_envs_finite:
  assumes "wf_envs S \<sigma> j \<delta> P P' V db" "Mapping.lookup db p = Some Rs" "X \<in> set Rs"
  shows "finite X"
proof -
  have "p \<in> Mapping.keys db"
    using assms(2) by (simp add: keys_dom_lookup domI)
  moreover have "\<forall>p \<in> Mapping.keys db. \<forall>X \<in> set (the (Mapping.lookup db p)). finite X"
    using assms(1) by (simp add: wf_envs_def)
  ultimately show ?thesis
    using assms(2,3) by auto
qed

lemma wf_envs_P_simps[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> pred_mapping (\<lambda>i. i \<le> j) P"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> rel_mapping (\<le>) P P'"
  unfolding wf_envs_def by auto

lemma wf_envs_progress_le[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P \<phi> j \<le> j"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) \<le> j + \<delta>"
  unfolding wf_envs_def by auto

lemma wf_envs_progress_regex_le[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P' r (j + \<delta>) \<le> j + \<delta>"
  unfolding wf_envs_def by (auto simp: progress_regex_le)

lemma wf_envs_progress_mono[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> (j+\<delta>)"
  unfolding wf_envs_def
  by (auto simp: progress_mono_gen)

(*<*)
end
(*>*)