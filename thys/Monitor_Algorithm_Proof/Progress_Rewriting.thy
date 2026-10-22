(*<*)
theory Progress_Rewriting
  imports Progress "MFODL_Logic.Preparation"
begin
(*>*)

unbundle MFODL_notation \<comment> \<open> enable notation \<close>

subsection \<open> Progress and safety \<close>

lemma safe_progress_get_and: "safe_formula \<phi> \<Longrightarrow>
  Min ((\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` set (get_and_list \<phi>)) = progress \<sigma> P \<phi> j"
  by (induction \<phi> rule: get_and_list.induct) auto

lemma progress_convert_multiway: "safe_formula \<phi> 
  \<Longrightarrow> progress \<sigma> P (convert_multiway \<phi>) j = progress \<sigma> P \<phi> j"
proof (induction \<phi> arbitrary: P rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp add: letpast_progress_def Let_def nfv_convert_multiway simp del: fun_upd_apply)
next
  case (And_safe \<phi> \<psi>)
  let ?c = "convert_multiway (Formula.And \<phi> \<psi>)"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have c_eq: "?c = Formula.Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  from \<open>safe_formula \<phi>\<close> have "safe_formula ?c\<phi>" by (rule safe_convert_multiway)
  moreover from \<open>safe_formula \<psi>\<close> have "safe_formula ?c\<psi>" by (rule safe_convert_multiway)
  ultimately show ?case
    unfolding c_eq
    using And_safe.IH
    by (auto simp: Min.union safe_progress_get_and)
next
  case (And_Not \<phi> \<psi>)
  let ?c = "convert_multiway (Formula.And \<phi> (Formula.Neg \<psi>))"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have c_eq: "?c = Formula.Ands (Formula.Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  from \<open>safe_formula \<phi>\<close> have "safe_formula ?c\<phi>" by (rule safe_convert_multiway)
  moreover from \<open>safe_formula \<psi>\<close> have "safe_formula ?c\<psi>" by (rule safe_convert_multiway)
  ultimately show ?case
    unfolding c_eq
    using And_Not.IH
    by (auto simp: Min.union safe_progress_get_and)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Formula.Trigger \<phi>' I \<psi>'"
  define f where "f = Formula.And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have t_prog: "progress \<sigma> P (convert_multiway t) j = progress \<sigma> P t j"
    using And_Trigger(6-7)[of P]
    unfolding t_def
    by auto

  show ?case
  proof (cases "safe_formula t")
  case True
    then obtain l where l_props:
      "convert_multiway f = Formula.Ands l"
      "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
      using t_not_safe_assign t_not_constraint And_Trigger(3)
      unfolding f_def t_def
      by (auto simp add: safe_dual_def split: if_splits)
  
    moreover have "progress \<sigma> P f j = Min (set (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) l))"
      using l_props(2) And_Trigger(5)[of P] t_prog safe_convert_multiway[OF And_Trigger(1)]
      unfolding f_def
    by (cases "convert_multiway \<phi>") (auto split: if_splits)
  
    ultimately show ?thesis 
      unfolding f_def t_def
      by auto
  next
    case False
    then have convert_f: "convert_multiway f 
      = Formula.And (convert_multiway \<phi>) (Formula.Trigger (convert_multiway \<phi>') I (convert_multiway \<psi>'))"
      using t_not_safe_assign t_not_constraint
      unfolding f_def t_def convert_multiway.simps
      by auto
    then show ?thesis
      using And_Trigger
      unfolding f_def t_def
      by (auto simp add: fv_convert_multiway safe_dual_def split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  then show ?case using progress_and_release_rewrite_bounded by auto
next
  case (Ands l)
  then show ?case
    unfolding progress.simps convert_multiway.simps
    by (force simp: list.pred_set convert_multiway_remove_neg intro!: Sup.SUP_cong)
next
  case (Trigger_0 \<phi> I \<psi>)
  show ?case
  proof (cases "safe_assignment (fv \<psi>) \<phi> \<or> is_constraint \<phi> 
  \<or> (case \<phi> of 
    Formula.formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' 
        \<and> (\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j) 
    | _ \<Rightarrow> False)")
    case True
    moreover {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis
        unfolding safe_assignment_def
        using Trigger_0
        by (cases \<phi>) (auto)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
        using Trigger_0
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using Trigger_0 assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of 
        Formula.formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' 
          \<and> (\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j) 
        | _ \<Rightarrow> False)"
      then obtain \<phi>' where \<phi>'_props:
        "\<phi> = Formula.formula.Neg \<phi>'"
        "safe_formula \<phi>'"
        "\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j"
        by (auto split: Formula.formula.splits)
      then have ?thesis using Trigger_0 by auto
    }
    ultimately show ?thesis by blast
  next
    case False
    then show ?thesis using Trigger_0 by (cases \<phi>) (auto simp del: convert_multiway.simps(19) safe_formula.simps(19))
  qed
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case
    by (simp del: convert_multiway.simps(10) add: min.commute min.left_commute)
next
  case (MatchP I r)
  from MatchP show ?case
    unfolding progress.simps regex.map convert_multiway.simps regex.set_map image_image
    by (intro if_cong arg_cong[of _ _ Min] image_cong)
      (auto 0 4 simp: safe_atms_def elim!: disjE_Not2 dest: safe_regex_safe_formula)
next
  case (MatchF I r)
  from MatchF show ?case
    unfolding progress.simps regex.map convert_multiway.simps regex.set_map image_image
    by (intro if_cong arg_cong[of _ _ Min] arg_cong[of _ _ Inf] arg_cong[of _ _ "(\<le>) _"]
      image_cong Collect_cong all_cong1 imp_cong conj_cong image_cong)
      (auto 0 4 simp: safe_atms_def elim!: disjE_Not2 dest: safe_regex_safe_formula)
qed (auto simp add: nfv_convert_multiway frz_progress_def)

subsection \<open> Progress and the rewritings of the preparation \<close>

declare progress_le_gen[simp]

lemma progress_map_formula[simp]: "progress \<sigma> P (Formula.formula.map_formula f \<phi>) j = progress \<sigma> P \<phi> j"
  by (induct \<phi> arbitrary: P j rule: formula_release_safe_bounded_induct)
    (auto simp: letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)
lemma progress_neg_dual[simp]: "progress \<sigma> P (neg_dual \<phi>) j = progress \<sigma> P \<phi> j"
  by (cases \<phi>) (auto simp: neg_dual_def)

lemma progress_dual_since: "progress \<sigma> P (dual_since \<phi>) j = progress \<sigma> P \<phi> j"
  by (induction \<phi> arbitrary: P j rule: dual_since.induct)
    (auto simp: dual_since_nfv letpast_progress_def frz_progress_def progress_regex_def regex.set_map image_image)

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

lemma progress_fresh[simp]: "p \<notin> preds \<phi> \<Longrightarrow> progress \<sigma> (P(p \<mapsto> x)) \<phi> j = progress \<sigma> P \<phi> j"
  by (rule not_contains_pred_progress) (auto dest: contains_pred_preds)

lemma progress_Frz_And:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P" and fresh: "(q, Formula.nfv \<alpha>) \<notin> preds \<alpha>"
  shows "progress \<sigma> P (Formula.Frz q \<alpha> (Formula.And \<alpha> \<psi>)) j =
    min (progress \<sigma> P \<alpha> j) (progress \<sigma> (P((q, Formula.nfv \<alpha>) \<mapsto> j)) \<psi> j)"
  using fresh by (subst progress_Frz_eq_le[OF P]) auto

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
      by (rule progress_Frz_eq_le[OF P, where \<alpha>="project (rewrite \<alpha> Same)", unfolded nfv_project nfv_rewrite]) (simp_all add: L h\<alpha>)
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
      by (rule progress_Frz_eq_le[OF P, where \<alpha>="project (rewrite \<gamma> Same)", unfolded nfv_project nfv_rewrite]) (simp_all add: L h\<gamma>)
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

unbundle MFODL_no_notation \<comment> \<open> enable notation \<close>

(*<*)
end
(*>*)
