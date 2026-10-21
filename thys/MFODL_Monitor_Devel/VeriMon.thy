theory VeriMon
imports Correctness Safety_Proofs "MFODL_Logic.Preparation"
begin

lemma progress_map_formula[simp]: "progress \<sigma> P (Formula.formula.map_formula f \<phi>) j = progress \<sigma> P \<phi> j"
  by (induct \<phi> arbitrary: P j rule: progress_custom_induct)
    (auto simp: letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)
lemma progress_neg_dual[simp]: "progress \<sigma> P (neg_dual \<phi>) j = progress \<sigma> P \<phi> j"
  by (cases \<phi>) (auto simp: neg_dual_def)

lemma progress_dual_since: "progress \<sigma> P (dual_since \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: dual_since.induct)
    (auto simp: dual_since_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

context maux begin

definition "minit_verimon rw sig \<phi> = map_sum id minit (prepare_verimon rw sig \<phi>)"

end
(* Proofs that normalize does not change the progress of the monitor *)

lemma progress_simplify_terms[simp]: "progress \<sigma> P (simplify_terms \<phi>) j = progress \<sigma> P \<phi> j"
  using [[linarith_split_limit = 17]]
  by (induction \<phi> arbitrary: P j rule: simplify_terms.induct)
    (auto simp: simplify_terms_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image
     release_safe_bounded_def Formula.eventually_def always_safe_bounded_def)

lemma progress_push_negation[simp]: "progress \<sigma> P (push_negation \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: push_negation.induct)
    (auto simp: push_negation_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

lemma progress_elim_double_negation[simp]: "progress \<sigma> P (elim_double_negation \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: elim_double_negation.induct)
    (auto simp: elim_double_negation_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

lemma progress_and_app[simp]:
  "progress \<sigma> P (and_app \<phi> \<psi>) j = min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
  using and_app_cong[where P = "\<lambda>\<phi>. progress \<sigma> P \<phi> j" and f = min] by (simp add: min.assoc)

lemma progress_assoc_and[simp]: "progress \<sigma> P (assoc_and \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: assoc_and.induct)
    (auto simp: assoc_and_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

lemma progress_normalize: "progress \<sigma> P (normalize \<phi>) j = progress \<sigma> P \<phi> j"
  unfolding normalize_def by auto

(* Proofs that rewrite does not change the progress of the monitor.
   The rules that propagate a range restriction \<alpha> into the scope of a temporal operator bind
   \<alpha>'s current satisfactions to a fresh predicate with the freeze operator (Frz q \<alpha> (\<alpha> \<and> OP (q \<and> \<beta>))).
   Since \<alpha> is conjoined at the outer level, the frozen predicate q is available whenever the outer
   conjunction can make progress (lemma progress_Frz_And); hence the progress of the rewritten formula
   coincides with the original one (lemma progress_rewrite). *)
lemma progress_shift[simp]: "progress \<sigma> P (project (shiftI_r i \<phi>)) j = progress \<sigma> P (project \<phi>) j"
proof (induction \<phi> arbitrary: i P j rule: Rewriting.formula.induct)
  case (Ands \<phi>s)
  then show ?case
    by (simp add: image_image cong: image_cong)
next
  case (Release \<phi> I \<psi>)
  then show ?case
    by (simp only: project.simps shiftI_r.simps progress.simps release_safe_bounded_def
      always_safe_bounded_def Formula.eventually_def once_def Formula.TT_def)
next
  case (MatchF I r)
  then show ?case
    by (simp add: progress_regex_def regex.set_map image_image cong: image_cong)
next
  case (MatchP I r)
  then show ?case
    by (simp add: progress_regex_def regex.set_map image_image cong: image_cong)
qed (simp_all add: eventually_def historically_def always_def frz_progress_def)

text \<open> The progress of a freeze operator whose body is not ahead of the frozen formula. \<close>

lemma progress_Frz_eq:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P"
    and le1: "progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j \<le> progress \<sigma> P \<alpha> j"
    and le0: "progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> 0)) \<psi> j \<le> progress \<sigma> P \<alpha> j"
  shows "progress \<sigma> P (Formula.Frz q \<alpha> \<psi>) j = progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j"
proof -
  let ?pn = "(q, Formula.nfv \<alpha>)"
  let ?a = "progress \<sigma> P \<alpha> j" and ?m = "progress \<sigma> (P(?pn \<mapsto> j)) \<psi> j"
  have a_le: "?a \<le> j"
    by (rule progress_le_gen[OF P])
  have "(LEAST i. i \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> (if i < ?a then j else 0))) \<psi> j \<le> i) = ?m"
  proof (rule Least_equality)
    show "?m \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> if ?m < ?a then j else 0)) \<psi> j \<le> ?m"
      using le1 le0 a_le by auto
  next
    fix y
    assume "y \<le> j \<and> progress \<sigma> (P(?pn \<mapsto> if y < ?a then j else 0)) \<psi> j \<le> y"
    then show "?m \<le> y"
      using le1 by (cases "y < ?a") auto
  qed
  then show ?thesis
    by (simp add: frz_progress_def)
qed

lemma progress_fresh[simp]: "p \<notin> preds \<phi> \<Longrightarrow> progress \<sigma> (P(p \<mapsto> x)) \<phi> j = progress \<sigma> P \<phi> j"
  by (rule not_contains_pred_progress) (auto dest: contains_pred_preds)

lemma progress_Frz_And:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, Formula.nfv \<alpha>) \<notin> preds \<alpha>"
  shows "progress \<sigma> P (Formula.Frz q \<alpha> (Formula.And \<alpha> \<psi>)) j =
    min (progress \<sigma> P \<alpha> j) (progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j)"
  using fresh by (subst progress_Frz_eq[OF P]) auto

lemma progress_frz_and_rw:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, nfv \<alpha>) \<notin> preds (project \<alpha>)"
  shows "progress \<sigma> P (project (Frz q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same) X))) j =
    min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> (P((q, nfv \<alpha>) \<mapsto> j)) (project X) j)"
  using progress_Frz_And[OF P, where q=q and \<alpha>="project (rewrite \<alpha> Same)" and \<psi>="project X" and \<sigma>=\<sigma>] fresh
  by (simp add: nfv_project)

lemma progress_frz_atom_and:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, n) \<notin> preds (project \<beta>)"
  shows "progress \<sigma> (P((q, n) \<mapsto> j)) (project (And (frz_atom q n) \<beta>)) j = progress \<sigma> P (project \<beta>) j"
  using fresh progress_le_gen[OF P, of \<sigma> "project \<beta>"] by (simp add: frz_atom_def)

lemma progress_frz_ih:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, n) \<notin> preds (project \<beta>)"
    and IH: "pred_mapping (\<lambda>x. x \<le> j) (P((q, n) \<mapsto> j)) \<Longrightarrow>
      progress \<sigma> (P((q, n) \<mapsto> j)) (project (rewrite (And (frz_atom q n) \<beta>) Same)) j =
      progress \<sigma> (P((q, n) \<mapsto> j)) (project (fix_r (And (frz_atom q n) \<beta>) Same)) j"
  shows "progress \<sigma> (P((q, n) \<mapsto> j)) (project (rewrite (And (frz_atom q n) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
  using IH P progress_frz_atom_and[OF P fresh] by simp

lemma progress_release_safe_bounded_cong:
  assumes "progress \<sigma> P \<phi> j = progress \<sigma> P' \<phi>' j" "progress \<sigma> P \<psi> j = progress \<sigma> P' \<psi>' j"
  shows "progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) j = progress \<sigma> P' (release_safe_bounded \<phi>' I \<psi>') j"
  using assms
  by (simp only: progress.simps release_safe_bounded_def always_safe_bounded_def Formula.eventually_def once_def Formula.TT_def)

lemma progress_Release_cong:
  assumes "progress \<sigma> P \<phi> j = progress \<sigma> P' \<phi>' j" "progress \<sigma> P \<psi> j = progress \<sigma> P' \<psi>' j"
  shows "progress \<sigma> P (Formula.Release \<phi> I \<psi>) j = progress \<sigma> P' (Formula.Release \<phi>' I \<psi>') j"
  using assms
  by (simp only: progress.simps release_safe_bounded_def always_safe_bounded_def Formula.eventually_def once_def Formula.TT_def)

lemma progress_Until_cong:
  assumes "min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) = min (progress \<sigma> P' \<phi>' j) (progress \<sigma> P' \<psi>' j)"
  shows "progress \<sigma> P (Formula.Until \<phi> I \<psi>) j = progress \<sigma> P' (Formula.Until \<phi>' I \<psi>') j"
  using assms by (simp only: progress.simps)

lemma progress_rewrite:
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow>
   progress \<sigma> P (project (rewrite \<phi> t)) j = progress \<sigma> P (project (fix_r \<phi> t)) j"
proof (induction \<phi> t arbitrary: P rule: rewrite.induct)
  case (2 \<alpha> \<beta> I \<gamma> t)
  note P = "2.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "2.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "2.IH"(3)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Release (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Release
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Release \<beta> I \<gamma>)) t)) j"
      using progress_Release_cong[OF h1 h2, of I] "2.IH"(1)[OF True P] by simp
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Release (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "2.IH"(4)[OF False P] "2.IH"(5)[OF False refl P] "2.IH"(6)[OF False refl refl P]
        progress_release_safe_bounded_cong[OF "2.IH"(5)[OF False refl P] "2.IH"(6)[OF False refl refl P], of I]
      by simp
  qed
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  note P = "3.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "3.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "3.IH"(3)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Trigger (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Trigger
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Trigger \<beta> I \<gamma>)) t)) j"
      using h1 h2 "3.IH"(1)[OF True P] by simp
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Trigger (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "3.IH"(4)[OF False P] "3.IH"(5)[OF False refl P] "3.IH"(6)[OF False refl refl P]
      by simp
  qed
next
  case (4 \<alpha> k \<beta> t)
  then show ?case
    by (cases "prop_cond \<alpha> \<beta>") (auto simp: project_shift[symmetric])
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  note P = "6.prems"
  let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
  let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
  consider (a) "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>"
    | (c) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "\<not> (prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>)"
    by blast
  then show ?case
  proof cases
    case a
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "6.IH"(2)[OF a refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite \<gamma> Same)) j = progress \<sigma> P (project \<gamma>) j"
      using "6.IH"(3)[OF a refl refl refl P] by (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Since (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same)))"
      using a by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Since
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite \<gamma> Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Since \<beta> I \<gamma>)) t)) j"
      using h1 h2 "6.IH"(1)[OF a P] by simp
    finally show ?thesis .
  next
    case b
    have h1: "progress \<sigma> ?P (project (rewrite \<beta> Same)) j = progress \<sigma> P (project \<beta>) j"
      using "6.IH"(5)[OF b refl refl refl P] by (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "6.IH"(6)[OF b refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Since (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using b by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Since
        (project (rewrite \<beta> Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Since \<beta> I \<gamma>)) t)) j"
      using h1 h2 "6.IH"(4)[OF b P] by simp
    finally show ?thesis .
  next
    case c
    then have eq: "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Since (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "6.IH"(7)[OF c P] "6.IH"(8)[OF c refl P] "6.IH"(9)[OF c refl refl P]
      by simp
  qed
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  note P = "7.prems"
  let ?q = "frz_name [\<alpha>, \<beta>, \<gamma>]"
  let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
  consider (a) "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>"
    | (c) "\<not> (prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)" "\<not> (prop_cond \<alpha> \<gamma> \<and> frz_ok \<alpha>)"
    by blast
  then show ?case
  proof cases
    case a
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "7.IH"(2)[OF a refl refl refl]]) (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite \<gamma> Same)) j = progress \<sigma> P (project \<gamma>) j"
      using "7.IH"(3)[OF a refl refl refl P] by (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Until (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same) I (rewrite \<gamma> Same)))"
      using a by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Until
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) I (project (rewrite \<gamma> Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Until \<beta> I \<gamma>)) t)) j"
      using h1 h2 "7.IH"(1)[OF a P] by simp
    finally show ?thesis .
  next
    case b
    have h1: "progress \<sigma> ?P (project (rewrite \<beta> Same)) j = progress \<sigma> P (project \<beta>) j"
      using "7.IH"(5)[OF b refl refl refl P] by (simp add: frz_name_fresh)
    have h2: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)) j = progress \<sigma> P (project \<gamma>) j"
      by (rule progress_frz_ih[OF P _ "7.IH"(6)[OF b refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Until (rewrite \<beta> Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same)))"
      using b by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.Until
        (project (rewrite \<beta> Same)) I (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<gamma>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Until \<beta> I \<gamma>)) t)) j"
      using h1 h2 "7.IH"(4)[OF b P] by simp
    finally show ?thesis .
  next
    case c
    then have eq: "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t =
      And (rewrite \<alpha> Same) (Until (rewrite \<beta> Same) I (rewrite \<gamma> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "7.IH"(7)[OF c P] "7.IH"(8)[OF c refl P] "7.IH"(9)[OF c refl refl P]
      by simp
  qed
next
  case (8 \<alpha> I \<beta> t)
  note P = "8.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "8.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Once I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Once I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Once I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (once I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Once I \<beta>)) t)) j"
      using h1 "8.IH"(1)[OF True P] by (simp add: once_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Once I \<beta>)) t = And (rewrite \<alpha> Same) (Once I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "8.IH"(3)[OF False P] "8.IH"(4)[OF False refl P]
      by (simp add: once_def)
  qed
next
  case (9 \<alpha> I \<beta> t)
  note P = "9.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "9.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Eventually I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Eventually I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Eventually I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (Formula.eventually I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Eventually I \<beta>)) t)) j"
      using h1 "9.IH"(1)[OF True P] by (simp add: eventually_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Eventually I \<beta>)) t = And (rewrite \<alpha> Same) (Eventually I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "9.IH"(3)[OF False P] "9.IH"(4)[OF False refl P]
      by (simp add: eventually_def)
  qed
next
  case (10 \<alpha> I \<beta> t)
  note P = "10.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "10.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Historically I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Historically I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Historically I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (historically I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Historically I \<beta>)) t)) j"
      using h1 "10.IH"(1)[OF True P] by (simp add: historically_def once_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Historically I \<beta>)) t = And (rewrite \<alpha> Same) (Historically I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "10.IH"(3)[OF False P] "10.IH"(4)[OF False refl P]
      by (simp add: historically_def once_def)
  qed
next
  case (11 \<alpha> I \<beta> t)
  note P = "11.prems"
  show ?case
  proof (cases "prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>")
    case True
    let ?q = "frz_name [\<alpha>, \<beta>]"
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "11.IH"(2)[OF True refl refl refl]]) (simp add: frz_name_fresh)
    have eq: "rewrite (And \<alpha> (Always I \<beta>)) t = Frz ?q (rewrite \<alpha> Same) (And (rewrite \<alpha> Same)
      (Always I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)))"
      using True by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (And \<alpha> (Always I \<beta>)) t)) j =
      min (progress \<sigma> P (project (rewrite \<alpha> Same)) j) (progress \<sigma> ?P (always I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j)"
      unfolding eq by (subst progress_frz_and_rw[OF P]) (simp_all add: frz_name_fresh)
    also have "\<dots> = progress \<sigma> P (project (fix_r (And \<alpha> (Always I \<beta>)) t)) j"
      using h1 "11.IH"(1)[OF True P] by (simp add: always_def eventually_def)
    finally show ?thesis .
  next
    case False
    then have eq: "rewrite (And \<alpha> (Always I \<beta>)) t = And (rewrite \<alpha> Same) (Always I (rewrite \<beta> Same))"
      by (simp add: Let_def)
    show ?thesis
      unfolding eq using "11.IH"(3)[OF False P] "11.IH"(4)[OF False refl P]
      by (simp add: always_def eventually_def)
  qed
next
  case (12 \<alpha> I \<beta> t)
  from "12.IH"(1-4)[OF _ "12.prems"] "12.IH"(5)[OF _ refl "12.prems"] show ?case
    by (cases "prop_cond \<alpha> \<beta>") auto
next
  case (13 \<alpha> I \<beta> t)
  from "13.IH"(1-4)[OF _ "13.prems"] "13.IH"(5)[OF _ refl "13.prems"] show ?case
    using progress_le_gen[OF "13.prems", of \<sigma> "project \<alpha>"] progress_le_gen[OF "13.prems", of \<sigma> "project \<beta>"]
    by (cases "prop_cond \<alpha> \<beta>") (auto simp: min_def not_le less_Suc_eq)
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  note P = "14.prems"
  let ?q = "frz_name [\<alpha>, \<gamma>, \<beta>]"
  have L: "progress \<sigma> (P((?q, n) \<mapsto> x)) (project (rewrite (And \<alpha> \<gamma>) Same)) j =
    min (progress \<sigma> P (project \<alpha>) j) (progress \<sigma> P (project \<gamma>) j)" for n x
    using "14.IH"(1)[OF P] by (simp add: frz_name_fresh)
  consider (a) "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>"
    | (b) "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)"
      "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> \<and> frz_ok \<gamma>"
    | (c) "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> \<and> frz_ok \<alpha>)"
      "\<not> (t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> \<and> frz_ok \<gamma>)"
    by blast
  then show ?case
  proof cases
    case a
    let ?P = "P((?q, nfv \<alpha>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "14.IH"(3)[OF refl a refl refl]]) (simp add: frz_name_fresh)
    have h\<alpha>: "progress \<sigma> P (project (rewrite \<alpha> Same)) j = progress \<sigma> P (project \<alpha>) j"
      using "14.IH"(2)[OF refl a refl refl P] by simp
    have eq: "rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t = Frz ?q (rewrite \<alpha> Same)
      (Since (rewrite (And \<alpha> \<gamma>) Same) I (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))"
      using a by (simp add: Let_def)
    have "progress \<sigma> P (project (rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t)) j =
      progress \<sigma> ?P (Formula.Since (project (rewrite (And \<alpha> \<gamma>) Same)) I
        (project (rewrite (And (frz_atom ?q (nfv \<alpha>)) \<beta>) Same))) j"
      unfolding eq project.simps
      by (rule progress_Frz_eq[OF P, where \<alpha>="project (rewrite \<alpha> Same)", unfolded nfv_project nfv_rewrite]) (simp_all add: L h\<alpha>)
    also have "\<dots> = progress \<sigma> P (project (fix_r (Since (And \<alpha> \<gamma>) I \<beta>) t)) j"
      using a L h1 by simp
    finally show ?thesis .
  next
    case b
    let ?P = "P((?q, nfv \<gamma>) \<mapsto> j)"
    have h1: "progress \<sigma> ?P (project (rewrite (And (frz_atom ?q (nfv \<gamma>)) \<beta>) Same)) j = progress \<sigma> P (project \<beta>) j"
      by (rule progress_frz_ih[OF P _ "14.IH"(5)[OF refl b refl refl]]) (simp add: frz_name_fresh)
    have h\<gamma>: "progress \<sigma> P (project (rewrite \<gamma> Same)) j = progress \<sigma> P (project \<gamma>) j"
      using "14.IH"(4)[OF refl b refl refl P] by simp
    have eq: "rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t = Frz ?q (rewrite \<gamma> Same)
      (Since (rewrite (And \<alpha> \<gamma>) Same) I (rewrite (And (frz_atom ?q (nfv \<gamma>)) \<beta>) Same))"
      using b by (auto simp: Let_def)
    have "progress \<sigma> P (project (rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t)) j =
      progress \<sigma> ?P (Formula.Since (project (rewrite (And \<alpha> \<gamma>) Same)) I
        (project (rewrite (And (frz_atom ?q (nfv \<gamma>)) \<beta>) Same))) j"
      unfolding eq project.simps
      by (rule progress_Frz_eq[OF P, where \<alpha>="project (rewrite \<gamma> Same)", unfolded nfv_project nfv_rewrite]) (simp_all add: L h\<gamma>)
    also have "\<dots> = progress \<sigma> P (project (fix_r (Since (And \<alpha> \<gamma>) I \<beta>) t)) j"
      using b L h1 by simp
    finally show ?thesis .
  next
    case c
    have le: "progress \<sigma> P (project \<alpha>) j \<le> j" "progress \<sigma> P (project \<gamma>) j \<le> j"
      by (rule progress_le_gen[OF P])+
    show ?thesis
      using c "14.IH"(1)[OF P] "14.IH"(6)[OF refl c _ P] "14.IH"(7)[OF refl c _ _ P] "14.IH"(8)[OF refl c _ _ P] le
      by (cases t) (auto simp: Let_def once_def min_def split: if_splits)
  qed
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  note P = "15.prems"
  have le: "progress \<sigma> P (project \<alpha>) j \<le> j" "progress \<sigma> P (project \<gamma>) j \<le> j"
    by (rule progress_le_gen[OF P])+
  let ?a = "progress \<sigma> P (project \<alpha>) j" and ?b = "progress \<sigma> P (project \<beta>) j"
    and ?c = "progress \<sigma> P (project \<gamma>) j"
  define r where "r = (if t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> then rewrite (And (Once I \<alpha>) \<beta>) Same
    else if t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> then rewrite (And (Once I \<gamma>) \<beta>) Same
    else rewrite \<beta> Same)"
  have eq: "rewrite (Until (And \<alpha> \<gamma>) I \<beta>) t = fix_r (Until (rewrite (And \<alpha> \<gamma>) Same) I r) t"
    by (simp add: r_def Let_def)
  have L: "progress \<sigma> P (project (rewrite (And \<alpha> \<gamma>) Same)) j = min ?a ?c"
    using "15.IH"(1)[OF P] by simp
  have R: "min (min ?a ?c) (progress \<sigma> P (project r) j) = min (min ?a ?c) ?b"
  proof (cases "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta>")
    case True
    then show ?thesis
      using "15.IH"(2)[OF refl True P] le by (simp add: r_def once_def min_def)
  next
    case False
    show ?thesis
    proof (cases "t = Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta>")
      case True
      then show ?thesis
        using "15.IH"(3)[OF refl False True P] False le by (simp add: r_def once_def min_def)
    next
      case False': False
      have "r = rewrite \<beta> Same"
        by (simp only: r_def if_not_P[OF False] if_not_P[OF False'])
      then show ?thesis
        using "15.IH"(4)[OF refl False False' P] by simp
    qed
  qed
  show ?case
  proof (cases t)
    case Same
    show ?thesis
      unfolding eq unfolding Same fix_r.simps project.simps
      by (rule progress_Until_cong) (simp add: L R)
  next
    case Swapped
    show ?thesis
      unfolding eq unfolding Swapped fix_r.simps project.simps
      by (rule progress_Until_cong) (use R in \<open>simp add: L min.commute min.left_commute min.assoc\<close>)
  qed
next
  case (28 \<phi> I \<psi> t)
  then show ?case
    using "28.IH"(1)[OF "28.prems"] "28.IH"(2)[OF "28.prems"]
      progress_release_safe_bounded_cong[OF "28.IH"(1)[OF "28.prems"] "28.IH"(2)[OF "28.prems"], of I]
    by simp
qed (auto simp: once_def always_def eventually_def historically_def
    progress_regex_def regex.set_map image_image min.commute)

lemma progress_rrewrite: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P (rrewrite \<phi>) j = progress \<sigma> P \<phi> j"
  by (simp add: rrewrite_def progress_rewrite project_embed)

(* Proofs that the conversion into multi-way joins preserves well-typedness and the specification *)


text \<open>The correctness of the preparation: whatever monitor evaluates the prepared formula
  @{text \<psi>}, it satisfies the specification of @{text \<psi>}, which coincides with that of the
  input formula. The locale does not depend on the auxiliary data structures of any monitor.\<close>

locale verimon_prepare =
  fixes rw sig \<phi>
  assumes wf: "wf_formula \<phi>" 
  and prepare_Inr: "\<not> sum.isl (prepare_verimon rw sig \<phi>)"
begin

definition "\<psi> = (THE \<psi>. prepare_verimon rw sig \<phi> = Inr \<psi>)"
definition "check_subst = (THE f. check sig TAny \<phi> = Inr f)"

lemma check_Inr: "\<exists>f. check sig TAny \<phi> = Inr f"
  using prepare_Inr unfolding prepare_verimon_def type_check_def
  by (simp add: bind_def split: sum.splits if_splits)

lemma check_check_subst: "check sig TAny \<phi> = Inr check_subst"
  unfolding check_subst_def using check_Inr
  by auto

lemma prepare_\<psi>: "prepare_verimon rw sig \<phi> = Inr \<psi>"
  unfolding \<psi>_def using prepare_Inr
  by (cases "prepare_verimon rw sig \<phi>") auto

lemma safe_\<psi>: "safe_formula \<psi>"
  using prepare_\<psi> unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def mmonitorable_def
    simp flip: monitorable_formula_code)

lemma wf_f_TCst_convert_tysym[simp]: "wf_f (TCst o convert_tysym)"
  unfolding wf_f_def                                      
  by (auto simp: numeric_ty_def)

lemma wf_f_check_subst[simp]: "wf_f (TCst \<circ> (convert_tysym o check_subst))"
  using wf_f_comp[OF wf_f_TCst_convert_tysym check_sound_proven[OF check_check_subst wf, unfolded wty_result_fX_def, THEN conjunct1]]
  by (auto simp: comp_assoc)

lemma verimon_spec_\<psi>:
  "verimon_spec \<psi> (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny)"
proof -
  let ?f = "convert_tysym o check_subst"
  let ?\<phi> = "Formula.formula.map_formula ?f \<phi>"
  have type_check: "type_check sig \<phi> = Inr ?\<phi>"
    using prepare_Inr check_check_subst
    by (auto simp: prepare_verimon_def type_check_def bind_def split: if_splits)
  have wty: "map_sig ?f sig, ?f o TAny \<turnstile> ?\<phi>"
    using check_sound_proven[OF check_check_subst wf] wf_f_check_subst wf_f_TCst_convert_tysym
    unfolding wty_result_fX_def by blast
  have \<psi>_cases: "\<psi> = ?\<phi> \<or> \<psi> = normalize ?\<phi> \<or> \<psi> = dual_since (normalize ?\<phi>) \<or> \<psi> = rrewrite (normalize ?\<phi>)"
    using prepare_\<psi> by (auto simp: prepare_verimon_def type_check Let_def split: if_splits)
  have "mmonitorable \<psi>"
    using prepare_\<psi> by (auto simp: prepare_verimon_def type_check Let_def monitorable_formula_code
      split: if_splits)
  moreover have "map_sig ?f sig, ?f o TAny \<turnstile> \<psi>"
    using \<psi>_cases by (elim disjE) (simp_all add: wty wty_normalize wty_dual_since wty_rrewrite)
  ultimately show ?thesis
    by (intro verimon_spec.intro wty_mfodl.intro verimon_spec_axioms.intro)
qed

lemma future_bounded_\<phi>:
  "future_bounded_mfodl (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)
    (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny)"
proof -
  let ?f = "convert_tysym o check_subst"
  let ?\<phi> = "Formula.formula.map_formula ?f \<phi>"
  have type_check: "type_check sig \<phi> = Inr ?\<phi>"
    using prepare_Inr check_check_subst
    by (auto simp: prepare_verimon_def type_check_def bind_def split: if_splits)
  have "map_sig ?f sig, ?f o TAny \<turnstile> ?\<phi>"
    using check_sound_proven[OF check_check_subst wf] wf_f_check_subst wf_f_TCst_convert_tysym
    unfolding wty_result_fX_def by blast
  moreover have "Safety.future_bounded ?\<phi>"
  proof -
    have \<psi>_cases: "\<psi> = ?\<phi> \<or> \<psi> = normalize ?\<phi> \<or> \<psi> = dual_since (normalize ?\<phi>) \<or> \<psi> = rrewrite (normalize ?\<phi>)"
      using prepare_\<psi> by (auto simp: prepare_verimon_def type_check Let_def split: if_splits)
    have "mmonitorable \<psi>"
      using verimon_spec_\<psi> by (rule verimon_spec.monitorable)
    then have "Safety.future_bounded \<psi>"
      by (simp add: mmonitorable_def)
    with \<psi>_cases show ?thesis
      using future_bounded_normalize[OF future_bounded_rrewrite] future_bounded_normalize[OF future_bounded_dual_since]
        future_bounded_normalize
      by auto
  qed
  ultimately show ?thesis
    by (intro future_bounded_mfodl.intro wty_mfodl.intro future_bounded_mfodl_axioms.intro)
qed

interpretation verimon_\<psi>: verimon_spec \<psi> "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using verimon_spec_\<psi> by (auto simp: verimon_spec_def verimon_spec_axioms_def wty_mfodl_def)

interpretation monitor_\<phi>: future_bounded_mfodl "Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>"
  "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  using future_bounded_\<phi> by (auto simp: future_bounded_mfodl_def future_bounded_mfodl_axioms_def wty_mfodl_def)

lemma fvi_\<psi>: "Formula.fvi b \<psi> = Formula.fvi b \<phi>"
  using prepare_\<psi>[symmetric] unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def normalize_fvi dual_since_fvi rrewrite_fvi type_check_def check_check_subst)

lemma nfv_\<psi>: "Formula.nfv \<psi> = Formula.nfv \<phi>"
  using prepare_\<psi>[symmetric] unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def normalize_nfv dual_since_nfv rrewrite_nfv type_check_def check_check_subst)

lemma sat_\<psi>:
  "Formula.sat \<sigma> V v i \<psi> = Formula.sat \<sigma> V v i (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)"
  using prepare_\<psi>[symmetric] safe_\<psi> unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: Let_def final_sat dual_since_sat normalize_sat type_check_def check_check_subst)

lemma pprogress_\<psi>: "pprogress \<psi> \<pi> = pprogress (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>) \<pi>"
  using prepare_\<psi>[symmetric] unfolding pprogress_def unfolding prepare_verimon_def
  by (auto split: sum.splits if_splits simp: progress_normalize progress_dual_since progress_rrewrite Let_def type_check_def check_check_subst)

text \<open>The rewriting preserves the free variables, but not necessarily the order in which
  @{const Formula.fv_list} lists them: the kernel's verdicts on @{term \<psi>} are those of the
  specification of the input formula, with their columns reordered.\<close>

lemma M_exchange: "verimon_\<psi>.M \<pi> = (\<lambda>(i, v). (i, restrict (Formula.fv_list \<psi>)
  (Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)) v)) ` monitor_\<phi>.M \<pi>"
proof -
  let ?ds = "Formula.fv_list \<psi>"
  let ?cs = "Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)"
  have set_cs: "set ?ds = set ?cs" "set ?cs = set ?ds"
    by (simp_all add: fvi_\<psi>)
  have restrict_back: "restrict ?ds ?cs (restrict ?cs ?ds v) = v"
    if "wf_tuple ?ds v" for v :: "event_data list"
    using that by (subst restrict_restrict) (simp_all add: fvi_\<psi> restrict_idle)
  have val_ds: "val (Formula.nfv \<phi>) ?ds (restrict ?ds ?cs v) = val (Formula.nfv \<phi>) ?cs v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have val_cs: "val (Formula.nfv \<phi>) ?cs (restrict ?cs ?ds v) = val (Formula.nfv \<phi>) ?ds v"
    for v :: "event_data list"
    by (rule val_restrict_perm) (rule set_cs)
  have to_\<phi>: "wf_tuple ?ds v \<and> (i, restrict ?cs ?ds v) \<in> monitor_\<phi>.M \<pi>"
    if "(i, v) \<in> verimon_\<psi>.M \<pi>" for i v
    using that unfolding verimon_\<psi>.M_def monitor_\<phi>.M_def
    by (simp add: sat_\<psi> nfv_\<psi> pprogress_\<psi> val_cs)
  have to_\<psi>: "(i, restrict ?ds ?cs v) \<in> verimon_\<psi>.M \<pi>" if "(i, v) \<in> monitor_\<phi>.M \<pi>" for i v
    using that unfolding verimon_\<psi>.M_def monitor_\<phi>.M_def
    by (simp add: sat_\<psi> nfv_\<psi> pprogress_\<psi> val_ds)
  show ?thesis
  proof (rule set_eqI, safe)
    fix i v
    assume "(i, v) \<in> verimon_\<psi>.M \<pi>"
    with to_\<phi>[OF this] show "(i, v) \<in> (\<lambda>(i, v). (i, restrict ?ds ?cs v)) ` monitor_\<phi>.M \<pi>"
      by (auto simp: restrict_back intro!: image_eqI[where x = "(i, restrict ?cs ?ds v)"])
  qed (rule to_\<psi>)
qed

lemma Mt_exchange: "verimon_\<psi>.Mt \<pi> = (\<lambda>(i, t, v). (i, t, restrict (Formula.fv_list \<psi>)
  (Formula.fv_list (Formula.formula.map_formula (convert_tysym \<circ> check_subst) \<phi>)) v)) ` monitor_\<phi>.Mt \<pi>"
  unfolding verimon_\<psi>.Mt_def monitor_\<phi>.Mt_def M_exchange image_image
  by (simp add: split_beta)

(* Correctness of specification of the monitor *)
lemmas mono_monitor = monitor_\<phi>.mono_monitor
lemmas sound_monitor = monitor_\<phi>.sound_monitor
lemmas complete_monitor = monitor_\<phi>.complete_monitor
lemmas sliceable_M = monitor_\<phi>.sliceable_M

end

text \<open>The kernel's monitor on the prepared formula.\<close>

locale verimon_rewrite = maux + verimon_prepare
begin

interpretation verimon_\<psi>: verimon \<psi> "map_sig (convert_tysym o check_subst) sig" "convert_tysym o check_subst o TAny"
  by (intro verimon.intro verimon_spec_\<psi>) unfold_locales

lemma verimon_wf_mstate_minit: "wf_mstate (map_sig (convert_tysym o check_subst) sig) (convert_tysym o check_subst o TAny) \<psi> pnil R (minit \<psi>)"
  using prepare_\<psi>[symmetric] safe_\<psi> unfolding prepare_verimon_def
  using check_sound_proven[OF check_check_subst wf, unfolded wty_result_fX_def, THEN conjunct2, THEN spec, of "convert_tysym o check_subst"]
  by (auto split: sum.splits if_splits simp: Let_def type_check_def check_check_subst
    intro!: wf_mstate_minit wty_rrewrite wty_dual_since wty_normalize dest!: spec[of _ "convert_tysym"])

(* Correctness of output of the monitor (verdicts of \phi is the output) *)
lemmas wf_mstate_minit = verimon_wf_mstate_minit
lemmas wf_mstate_mstep = wf_mstate_mstep
lemmas mstep_mverdicts = verimon_\<psi>.mstep_mverdicts[unfolded Mt_exchange]

end

end
