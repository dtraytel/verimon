(*<*)
theory Monitorable
  imports
    Safety
begin
(*>*)

subsection \<open>Monitorable formulas\<close>

definition "mmonitorable \<phi> \<longleftrightarrow> safe_formula \<phi> \<and> Safety.future_bounded \<phi>"
definition "mmonitorable_regex b g r 
  \<longleftrightarrow> Regex.safe_regex fv rgx_safe_pred b g r \<and> Regex.pred_regex Safety.future_bounded r"

definition is_simple_eq :: "Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> bool" where
  "is_simple_eq t1 t2 = (Formula.is_Const t1 \<and> (Formula.is_Const t2 \<or> Formula.is_Var t2) \<or>
    Formula.is_Var t1 \<and> Formula.is_Const t2)"

function (sequential) mmonitorable_exec :: "'t Formula.formula \<Rightarrow> bool" where
  "mmonitorable_exec (Formula.Eq t1 t2) = is_simple_eq t1 t2"
| "mmonitorable_exec (Formula.Pred e ts) = list_all (\<lambda>t. Formula.is_Var t \<or> Formula.is_Const t) ts"
| "mmonitorable_exec (Formula.Let p \<phi> \<psi>) = ({0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.Frz p \<phi> \<psi>) = ({0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.LetPast p \<phi> \<psi>) = (Safety.safe_letpast (p, Formula.nfv \<phi>) \<phi> \<le> PastRec \<and>
    {0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.Neg \<phi>) = (fv \<phi> = {} \<and> mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Or \<phi> \<psi>) = (fv \<phi> = fv \<psi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.And \<phi> \<psi>) = (mmonitorable_exec \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> mmonitorable_exec \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> mmonitorable_exec \<psi>'
        | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> safe_dual True mmonitorable_exec \<phi>' I \<psi>'
        | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> (
          bounded I \<and> \<not> mem I 0 \<and>
          mmonitorable_exec \<phi>' \<and> mmonitorable_exec \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
          mmonitorable_exec (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
        )
        | _ \<Rightarrow> False
      ))))"
| "mmonitorable_exec (Formula.Ands l) = (let (pos, neg) = partition mmonitorable_exec l in
    pos \<noteq> [] \<and> list_all mmonitorable_exec (map remove_neg neg) \<and>
    \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
| "mmonitorable_exec (Formula.Exists t \<phi>) = (0 \<in> fv \<phi> \<and> mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Agg y \<omega> tys f \<phi>) = (mmonitorable_exec \<phi> \<and>
    y + length tys \<notin> Formula.fv \<phi> \<and> {0..<length tys} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
| "mmonitorable_exec (Formula.Prev I \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Next I \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Since \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.Until \<phi> I \<psi>) = (Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and> bounded I \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.Trigger \<phi> I \<psi>) = safe_dual False mmonitorable_exec \<phi> I \<psi>"
| "mmonitorable_exec (Formula.Release \<phi> I \<psi>) = (mem I 0 \<and> bounded I \<and> mmonitorable_exec \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> mmonitorable_exec (Formula.And \<psi> \<phi>))"
| "mmonitorable_exec (Formula.MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. mmonitorable_exec \<phi> \<or> (g = Lax \<and> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "mmonitorable_exec (Formula.MatchF I r) = (Regex.safe_regex fv (\<lambda>g \<phi>. mmonitorable_exec \<phi> \<or> (g = Lax \<and> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False))) Futu Strict r \<and> bounded I)"
| "mmonitorable_exec (Formula.TP t) = (Formula.is_Var t \<or> Formula.is_Const t)"
| "mmonitorable_exec (Formula.TS t) = (Formula.is_Var t \<or> Formula.is_Const t)"
| "mmonitorable_exec _ = False"
  by pat_completeness (simp_all only: formula.inject formula.distinct simp_thms)

termination mmonitorable_exec
proof ((relation "measure size'"; clarsimp dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size'),
    goal_cases R1 R2 R3 Ands1 R4)
  case (R1 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>)  auto
next
  case (R2 \<phi> \<psi>)
  then show ?case 
    by (cases \<psi>)  auto
next
  case (R3 \<phi> \<phi>' I \<psi>')
  then show ?case
    using size'_and_release[of \<phi> \<phi>' I \<psi>']
    by auto
next
  case (R4 \<phi> I \<psi>)
  then show ?case 
    by (simp split: formula.splits)
next
  case (Ands1 \<phi>s \<phi>)
  then show ?case
    by (metis dual_order.trans 
        le_imp_less_Suc size'_remove_neg)
qed

lemma safe_formula_mmonitorable_exec: 
  "safe_formula \<phi> \<Longrightarrow> Safety.future_bounded \<phi> \<Longrightarrow> mmonitorable_exec \<phi>"
proof (induct \<phi> rule: safe_formula.induct)
  case (10 \<phi> \<psi>)
  then show ?case
  proof (cases "fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>'
      | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> safe_dual True safe_formula \<phi>' I \<psi>'
      | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> (
        bounded I \<and> \<not>mem I 0 \<and>
        safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
        safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      )
      | _ \<Rightarrow> False
    ))")
    case True
    then have fvs: "fv \<psi> \<subseteq> fv \<phi>"
      by auto
    show ?thesis
      using True 10
    proof (cases "is_constraint \<psi>")
      case False
      then have \<psi>_props: "(case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>'
        | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> safe_dual True safe_formula \<phi>' I \<psi>'
        | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> (
          bounded I \<and> \<not>mem I 0 \<and>
          safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
          safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
        )
        | _ \<Rightarrow> False
      )" using True
        by auto
      then show ?thesis
      proof (cases "case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False")
        case True
        then obtain \<psi>' where "\<psi> = Formula.Neg \<psi>'" "safe_formula \<psi>'"
          by (auto split:formula.splits)
        then show ?thesis using 10 \<psi>_props by (auto split: formula.splits)
      next
        case f1: False
        then show ?thesis
        proof (cases "case \<psi> of Formula.Trigger \<phi>' I \<psi>' \<Rightarrow> safe_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> False")
          case True
          then obtain \<phi>' I \<psi>' where "\<psi> = Formula.Trigger \<phi>' I \<psi>'" "safe_dual True safe_formula \<phi>' I \<psi>'"
            using \<psi>_props
            by (auto split:formula.splits)
          then show ?thesis 
            using 10 \<psi>_props nat_le_iff_add 
            by (clarsimp simp add: safe_dual_def)
              (metis le_add2)
        next
          case False
          then obtain \<phi>' I \<psi>' where release_props:
            "\<psi> = Formula.Release \<phi>' I \<psi>'"
            "bounded I"
            "\<not>mem I 0"
            "safe_formula \<phi>'"
            "safe_formula \<psi>'"
            "fv \<phi>' = fv \<psi>'"
            "safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using f1 \<psi>_props
            by (auto split:formula.splits)
          
          have safe: "safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            unfolding and_release_safe_bounded_def
            using safe_formula_release_bounded release_props fvs release_fvi(2) 10(8)
            by auto
          
          have bounded: "Safety.future_bounded (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using release_bounded_future_bounded[of \<phi>' I \<psi>'] release_props(1-3) 10(9)
            by (auto simp add: and_release_safe_bounded_def)
          have "mmonitorable_exec (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using 10(7)[OF _ fvs release_props(1) release_props(2-6) safe bounded]
              "10.prems"(1) safe_formula.simps(10) by blast
          then show ?thesis 
            using 10 release_props 
            by (auto simp add: safe_assignment_def)
        qed
      qed
    qed (auto)
  qed (auto)
next
  case (11 l)
  from "11.prems"(2) have bounded: "Safety.future_bounded \<phi>" if "\<phi> \<in> set l" for \<phi>
    using that by (auto simp: list.pred_set)
  obtain poss negs where posnegs: "(poss, negs) = partition safe_formula l" by simp
  obtain posm negm where posnegm: "(posm, negm) = partition mmonitorable_exec l" by simp
  have "set poss \<subseteq> set posm"
  proof (rule subsetI)
    fix x assume "x \<in> set poss"
    then have "x \<in> set l" "safe_formula x" using posnegs by simp_all
    then have "mmonitorable_exec x" using "11.hyps"(1) bounded by blast
    then show "x \<in> set posm" using \<open>x \<in> set poss\<close> posnegm posnegs by simp
  qed
  then have "set negm \<subseteq> set negs" using posnegm posnegs by auto
  obtain "poss \<noteq> []" "list_all safe_formula (map remove_neg negs)"
    "(\<Union>x\<in>set negs. fv x) \<subseteq> (\<Union>x\<in>set poss. fv x)"
    using "11.prems"(1) posnegs by simp
  then have "posm \<noteq> []" using \<open>set poss \<subseteq> set posm\<close> by auto
  moreover have "list_all mmonitorable_exec (map remove_neg negm)"
  proof -
    let ?l = "map remove_neg negm"
    have "\<And>x. x \<in> set ?l \<Longrightarrow> mmonitorable_exec x"
    proof -
      fix x assume "x \<in> set ?l"
      then obtain y where "y \<in> set negm" "x = remove_neg y" by auto
      then have "y \<in> set negs" using \<open>set negm \<subseteq> set negs\<close> by blast
      then have "safe_formula x"
        unfolding \<open>x = remove_neg y\<close> using \<open>list_all safe_formula (map remove_neg negs)\<close>
        by (simp add: list_all_def)
      show "mmonitorable_exec x"
      proof (cases "\<exists>z. y = Formula.Neg z")
        case True
        then obtain z where "y = Formula.Neg z" by blast
        then show ?thesis
          using "11.hyps"(2)[OF posnegs refl] \<open>x = remove_neg y\<close> \<open>y \<in> set negs\<close> 
            posnegs bounded \<open>safe_formula x\<close> \<open>poss \<noteq> []\<close>
          by fastforce
      next
        case False
        then have "remove_neg y = y" by (cases y) simp_all
        then have "y = x" unfolding \<open>x = remove_neg y\<close> by simp
        show ?thesis
          using "11.hyps"(1) \<open>y \<in> set negs\<close> posnegs \<open>safe_formula x\<close> unfolding \<open>y = x\<close>
          by auto
      qed
    qed
    then show ?thesis by (simp add: list_all_iff)
  qed
  moreover have "(\<Union>x\<in>set negm. fv x) \<subseteq> (\<Union>x\<in>set posm. fv x)"
    using \<open>\<Union> (fv ` set negs) \<subseteq> \<Union> (fv ` set poss)\<close> \<open>set poss \<subseteq> set posm\<close> \<open>set negm \<subseteq> set negs\<close>
    by fastforce
  ultimately show ?case 
    using posnegm 
    by (simp add: list_all_iff)
next
  case (20 I r)
  then show ?case
    by (auto elim!: safe_regex_mono[rotated] simp: case_Neg_iff regex.pred_set)
next
  case (21 I r)
  then show ?case
    by (auto elim!: safe_regex_mono[rotated] simp: case_Neg_iff regex.pred_set)
qed (auto simp add: is_simple_eq_def list.pred_set case_Neg_iff safe_dual_def split: if_splits)

lemma safe_assignment_future_bounded: "safe_assignment X \<phi> \<Longrightarrow> Safety.future_bounded \<phi>"
  unfolding safe_assignment_def by (auto split: formula.splits)

lemma is_constraint_future_bounded: "is_constraint \<phi> \<Longrightarrow> Safety.future_bounded \<phi>"
  by (induction rule: is_constraint.induct) simp_all

lemma mmonitorable_exec_mmonitorable: "mmonitorable_exec \<phi> \<Longrightarrow> mmonitorable \<phi>"
proof (induct \<phi> rule: mmonitorable_exec.induct)
  case (8 \<phi> \<psi>)
  show ?case
  proof (cases "\<exists>\<psi>'. \<psi> = Formula.Neg \<psi>'")
    case True
    then show ?thesis
      using 8
      unfolding mmonitorable_def
      by (auto intro: safe_assignment_future_bounded is_constraint_future_bounded)
  next
    case non_neg: False
    then show ?thesis
    proof (cases "\<exists>\<phi>' I \<psi>'. \<psi> = Formula.Trigger \<phi>' I \<psi>'")
      case True
      then obtain \<phi>' I \<psi>' where \<psi>_def: "\<psi> = Formula.Trigger \<phi>' I \<psi>'"
        by blast
      then show ?thesis
        using 8(1-2,8) 8(4)[OF _ _ \<psi>_def]
        unfolding mmonitorable_def
        by (auto simp add: safe_assignment_def safe_dual_def 
            intro: is_constraint_future_bounded)
    next
      case no_trigger: False
      show ?thesis
      proof (cases "\<exists>\<phi>' I \<psi>'. \<psi> = Formula.Release \<phi>' I \<psi>'")
        case True
        then obtain \<phi>' I \<psi>' where \<psi>_def: "\<psi> = Formula.Release \<phi>' I \<psi>'"
          by blast
        have \<phi>_props: "mmonitorable \<phi>"
          using 8(1,8)
          by auto
        
        show ?thesis
        proof (cases "mmonitorable_exec \<psi>")
          case True
          then have \<psi>_props: "safe_formula \<psi> \<and> Safety.future_bounded \<psi>"
            using 8
            unfolding mmonitorable_def
            by auto
          then have "mem I 0" "bounded I" "fv \<phi>' \<subseteq> fv \<psi>'"
            unfolding \<psi>_def
            by auto
          then show ?thesis
            using \<phi>_props \<psi>_props
            unfolding mmonitorable_def
            by (auto simp add: safe_assignment_def)
        next
          case False
          then have "fv (formula.Release \<phi>' I \<psi>') \<subseteq> fv \<phi>"
            using 8(8) \<phi>_props
            unfolding mmonitorable_exec.simps \<psi>_def
            by (auto simp add: safe_assignment_def)

          moreover have "bounded I \<and> \<not>mem I 0 \<and>
            mmonitorable_exec \<phi>' \<and> mmonitorable_exec \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
            mmonitorable_exec (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using 8(8) False
            unfolding \<psi>_def
            by (auto simp add: safe_assignment_def)
         
          ultimately show ?thesis
            using 8(5-7)[OF _ _ \<psi>_def] \<phi>_props safe_formula_mmonitorable_exec
            unfolding mmonitorable_def
            by (auto simp add: \<psi>_def)
        qed
      next
        case False
        then have "mmonitorable_exec \<phi> \<and> (safe_assignment (fv \<phi>) \<psi> \<or> mmonitorable_exec \<psi> \<or> fv \<psi> \<subseteq> fv \<phi> \<and> is_constraint \<psi>)"
          using non_neg no_trigger 8(8)
          by (auto split: formula.splits)
        then show ?thesis
          using non_neg 8
          unfolding mmonitorable_def
          by (auto intro: safe_assignment_future_bounded is_constraint_future_bounded)
      qed
    qed
  qed
next
  case (9 l)
  obtain poss negs where posnegs: "(poss, negs) = partition safe_formula l" by simp
  obtain posm negm where posnegm: "(posm, negm) = partition mmonitorable_exec l" by simp
  have pos_monitorable: "list_all mmonitorable_exec posm" using posnegm by (simp add: list_all_iff)
  have neg_monitorable: "list_all mmonitorable_exec (map remove_neg negm)"
    using "9.prems" posnegm by (simp add: list_all_iff)
  have "set posm \<subseteq> set poss"
    using "9.hyps"(1) posnegs posnegm unfolding mmonitorable_def by auto
  then have "set negs \<subseteq> set negm"
    using posnegs posnegm by auto

  have "poss \<noteq> []" using "9.prems" posnegm \<open>set posm \<subseteq> set poss\<close> by auto
  moreover have "list_all safe_formula (map remove_neg negs)"
    using neg_monitorable "9.hyps"(2)[OF posnegm refl] \<open>set negs \<subseteq> set negm\<close> "9.prems" posnegm
    unfolding mmonitorable_def by (auto simp: list_all_iff)
  moreover have "\<Union> (fv ` set negm) \<subseteq> \<Union> (fv ` set posm)"
    using "9.prems" posnegm by simp
  then have "\<Union> (fv ` set negs) \<subseteq> \<Union> (fv ` set poss)"
    using \<open>set posm \<subseteq> set poss\<close> \<open>set negs \<subseteq> set negm\<close> by fastforce
  ultimately have "safe_formula (Formula.Ands l)" using posnegs by simp
  moreover have "Safety.future_bounded (Formula.Ands l)"
  proof -
    have "list_all Safety.future_bounded posm"
      using pos_monitorable "9.hyps"(1) posnegm unfolding mmonitorable_def
      by (auto elim!: list.pred_mono_strong)
    moreover have fnegm: "list_all Safety.future_bounded (map remove_neg negm)"
      using neg_monitorable "9.hyps"(2) posnegm "9.prems" unfolding mmonitorable_def
      by (auto elim!: list.pred_mono_strong)
    then have "list_all Safety.future_bounded negm"
    proof -
      have "\<And>x. x \<in> set negm \<Longrightarrow> Safety.future_bounded x"
      proof -
        fix x assume "x \<in> set negm"
        have "Safety.future_bounded (remove_neg x)" using fnegm \<open>x \<in> set negm\<close> by (simp add: list_all_iff)
        then show "Safety.future_bounded x" by (cases x) auto
      qed
      then show ?thesis by (simp add: list_all_iff)
    qed
    ultimately have "list_all Safety.future_bounded l" using posnegm by (auto simp: list_all_iff)
    then show ?thesis by (auto simp: list_all_iff)
  qed
  ultimately show ?case unfolding mmonitorable_def ..
next
  case (14 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce simp: case_Neg_iff)
next
  case (15 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce simp: one_enat_def case_Neg_iff)
next
  case (16 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    then show ?thesis
      using 16
      by (auto simp add: case_Neg_iff mmonitorable_def safe_dual_def split: if_splits)
  next
    case False
    then show ?thesis
      using 16
      by (auto simp add: case_Neg_iff mmonitorable_def safe_dual_def split: if_splits)
  qed
next
  case (17 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    then show ?thesis
      using 17
      by (auto simp add: case_Neg_iff mmonitorable_def safe_dual_def split: if_splits)
  next
    case False
    then show ?thesis
      using 17
      by (auto simp add: case_Neg_iff mmonitorable_def safe_dual_def split: if_splits)
  qed
next
  case (18 I r)
  then show ?case
    by (auto elim!: safe_regex_mono[rotated] dest: safe_regex_safe[rotated]
        simp: mmonitorable_regex_def mmonitorable_def case_Neg_iff regex.pred_set)
next
  case (19 I r)
  then show ?case
    by (auto 0 3 elim!: safe_regex_mono[rotated] dest: safe_regex_safe[rotated]
        simp: mmonitorable_regex_def mmonitorable_def case_Neg_iff regex.pred_set)
qed (auto simp add: mmonitorable_def mmonitorable_regex_def is_simple_eq_def 
    one_enat_def list.pred_set split: if_splits)

lemma monitorable_formula_code[code]: "mmonitorable \<phi> = mmonitorable_exec \<phi>"
  using mmonitorable_exec_mmonitorable safe_formula_mmonitorable_exec mmonitorable_def
  by blast

(*<*)
end
(*>*)
