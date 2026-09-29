(*<*)
theory Monitor
  imports
    Typing
    Frz_Locality
    Optimized_Join
    "HOL-Library.While_Combinator"
    "HOL-Library.Mapping"
begin
(*>*)


section \<open>Generic monitoring algorithm\<close>

text \<open>The algorithm defined here abstracts over the implementation of the temporal operators.\<close>


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
| "mmonitorable_exec (Formula.Release \<phi> I \<psi>) = (mem I 0 \<and> bounded I \<and> mmonitorable_exec \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> mmonitorable_exec (release_safe_0 \<phi> I \<psi>))"
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
    using size'_Release[of \<phi> I \<psi>]
    by auto
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


subsection \<open> Regular expressions\<close>

datatype mregex =
  MSkip nat
  | MTestPos nat
  | MTestNeg nat
  | MPlus mregex mregex
  | MTimes mregex mregex
  | MStar mregex

primrec ok where
  "ok _ (MSkip n) = True"
| "ok m (MTestPos n) = (n < m)"
| "ok m (MTestNeg n) = (n < m)"
| "ok m (MPlus r s) = (ok m r \<and> ok m s)"
| "ok m (MTimes r s) = (ok m r \<and> ok m s)"
| "ok m (MStar r) = ok m r"

primrec from_mregex where
  "from_mregex (MSkip n) _ = Regex.Skip n"
| "from_mregex (MTestPos n) \<phi>s = Regex.Test (\<phi>s ! n)"
| "from_mregex (MTestNeg n) \<phi>s = (if safe_formula (Formula.Neg (\<phi>s ! n))
    then Regex.Test (Formula.Neg (Formula.Neg (Formula.Neg (\<phi>s ! n))))
    else Regex.Test (Formula.Neg (\<phi>s ! n)))"
| "from_mregex (MPlus r s) \<phi>s = Regex.Plus (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MTimes r s) \<phi>s = Regex.Times (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MStar r) \<phi>s = Regex.Star (from_mregex r \<phi>s)"

primrec to_mregex_exec where
  "to_mregex_exec (Regex.Skip n) xs = (MSkip n, xs)"
| "to_mregex_exec (Regex.Test \<phi>) xs = (if safe_formula \<phi> then (MTestPos (length xs), xs @ [\<phi>])
     else case \<phi> of Formula.Neg \<phi>' \<Rightarrow> (MTestNeg (length xs), xs @ [\<phi>']) | _ \<Rightarrow> (MSkip 0, xs))"
| "to_mregex_exec (Regex.Plus r s) xs =
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MPlus mr ms, zs))"
| "to_mregex_exec (Regex.Times r s) xs =
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MTimes mr ms, zs))"
| "to_mregex_exec (Regex.Star r) xs =
     (let (mr, ys) = to_mregex_exec r xs in (MStar mr, ys))"

primrec shift where
  "shift (MSkip n) k = MSkip n"
| "shift (MTestPos i) k = MTestPos (i + k)"
| "shift (MTestNeg i) k = MTestNeg (i + k)"
| "shift (MPlus r s) k = MPlus (shift r k) (shift s k)"
| "shift (MTimes r s) k = MTimes (shift r k) (shift s k)"
| "shift (MStar r) k = MStar (shift r k)"

primrec to_mregex where
  "to_mregex (Regex.Skip n) = (MSkip n, [])"
| "to_mregex (Regex.Test \<phi>) = (if safe_formula \<phi> then (MTestPos 0, [\<phi>])
     else case \<phi> of Formula.Neg \<phi>' \<Rightarrow> (MTestNeg 0, [\<phi>']) | _ \<Rightarrow> (MSkip 0, []))"
| "to_mregex (Regex.Plus r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MPlus mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (Regex.Times r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MTimes mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (Regex.Star r) =
     (let (mr, ys) = to_mregex r in (MStar mr, ys))"

lemma shift_0: "shift r 0 = r"
  by (induct r) auto

lemma shift_shift: "shift (shift r k) j = shift r (k + j)"
  by (induct r) auto

lemma to_mregex_to_mregex_exec:
  "case to_mregex r of (mr, \<phi>s) \<Rightarrow> to_mregex_exec r xs = (shift mr (length xs), xs @ \<phi>s)"
  by (induct r arbitrary: xs)
    (auto simp: shift_shift ac_simps split: formula.splits prod.splits)

lemma to_mregex_to_mregex_exec_Nil[code]: "to_mregex r = to_mregex_exec r []"
  using to_mregex_to_mregex_exec[where xs="[]" and r = r] by (auto simp: shift_0)

lemma ok_mono: "ok m mr \<Longrightarrow> m \<le> n \<Longrightarrow> ok n mr"
  by (induct mr) auto

lemma from_mregex_cong: "ok m mr \<Longrightarrow> (\<forall>i < m. xs ! i = ys ! i) \<Longrightarrow> from_mregex mr xs = from_mregex mr ys"
  by (induct mr) auto

lemma to_mregex_exec_ok:
  "to_mregex_exec r xs = (mr, ys) \<Longrightarrow> \<exists>zs. ys = xs @ zs \<and> set zs = safe_atms r \<and> ok (length ys) mr"
proof (induct r arbitrary: xs mr ys)
  case (Skip x)
  then show ?case by (auto split: if_splits prod.splits simp: safe_atms_def elim: ok_mono)
next
  case (Test x)
  show ?case proof (cases "\<exists>x'. x = Formula.Neg x'")
    case True
    with Test show ?thesis by (auto split: if_splits prod.splits simp: safe_atms_def elim: ok_mono)
  next
    case False
    with Test show ?thesis by (auto split: if_splits prod.splits simp: safe_atms_def not_Neg_cases elim: ok_mono)
  qed
next
  case (Plus r1 r2)
  obtain mr1 ys1 where 1: "to_mregex_exec r1 xs = (mr1, ys1)"
    by (cases "to_mregex_exec r1 xs")
  obtain mr2 ys2 where 2: "to_mregex_exec r2 ys1 = (mr2, ys2)"
    by (cases "to_mregex_exec r2 ys1")
  from Plus.prems have mr_ys: "mr = MPlus mr1 mr2" "ys = ys2"
    by (simp_all add: 1 2)
  obtain zs1 where zs1: "ys1 = xs @ zs1" "set zs1 = safe_atms r1" "ok (length ys1) mr1"
    using Plus.hyps(1)[OF 1] by blast
  obtain zs2 where zs2: "ys2 = ys1 @ zs2" "set zs2 = safe_atms r2" "ok (length ys2) mr2"
    using Plus.hyps(2)[OF 2] by blast
  have "ok (length ys2) mr1"
    using zs1(3) by (rule ok_mono) (simp add: zs2(1))
  with zs1 zs2 show ?case
    unfolding mr_ys by (intro exI[of _ "zs1 @ zs2"]) simp
next
  case (Times r1 r2)
  obtain mr1 ys1 where 1: "to_mregex_exec r1 xs = (mr1, ys1)"
    by (cases "to_mregex_exec r1 xs")
  obtain mr2 ys2 where 2: "to_mregex_exec r2 ys1 = (mr2, ys2)"
    by (cases "to_mregex_exec r2 ys1")
  from Times.prems have mr_ys: "mr = MTimes mr1 mr2" "ys = ys2"
    by (simp_all add: 1 2)
  obtain zs1 where zs1: "ys1 = xs @ zs1" "set zs1 = safe_atms r1" "ok (length ys1) mr1"
    using Times.hyps(1)[OF 1] by blast
  obtain zs2 where zs2: "ys2 = ys1 @ zs2" "set zs2 = safe_atms r2" "ok (length ys2) mr2"
    using Times.hyps(2)[OF 2] by blast
  have "ok (length ys2) mr1"
    using zs1(3) by (rule ok_mono) (simp add: zs2(1))
  with zs1 zs2 show ?case
    unfolding mr_ys by (intro exI[of _ "zs1 @ zs2"]) simp
next
  case (Star r)
  then show ?case by (auto split: if_splits prod.splits simp: safe_atms_def elim: ok_mono)
qed

lemma ok_shift: "ok (i + m) (Monitor.shift r i) \<longleftrightarrow> ok m r"
  by (induct r) auto

lemma to_mregex_ok: "to_mregex r = (mr, ys) \<Longrightarrow> set ys = safe_atms r \<and> ok (length ys) mr"
proof (induct r arbitrary: mr ys)
  case (Skip x)
  then show ?case by (auto simp: safe_atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Test x)
  show ?case proof (cases "\<exists>x'. x = Formula.Neg x'")
    case True
    with Test show ?thesis 
      by (auto split: if_splits prod.splits simp: safe_atms_def elim: ok_mono)
  next
    case False
    with Test show ?thesis 
      by (auto split: if_splits prod.splits simp: safe_atms_def not_Neg_cases elim: ok_mono)
  qed
next
  case (Plus r1 r2)
  then show ?case by (fastforce simp: ok_shift safe_atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Times r1 r2)
  then show ?case by (fastforce simp: ok_shift safe_atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Star r)
  then show ?case by (auto simp: safe_atms_def elim: ok_mono split: if_splits prod.splits)
qed

lemmas to_mregex_safe_atms =
  to_mregex_ok[THEN conjunct1, THEN equalityD1, THEN set_mp, rotated]

lemma from_mregex_shift: "from_mregex (shift r (length xs)) (xs @ ys) = from_mregex r ys"
  by (induct r) (auto simp: nth_append)

lemma from_mregex_to_mregex: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> case_prod from_mregex (to_mregex r) = r"
  by (induct r rule: safe_regex.induct) 
      (auto dest: to_mregex_ok intro!: from_mregex_cong simp: nth_append from_mregex_shift case_Neg_iff
      split: prod.splits modality.splits if_splits)

lemma from_mregex_eq: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> from_mregex mr \<phi>s = r"
  using from_mregex_to_mregex[of m g r] by auto

lemma from_mregex_to_mregex_exec: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> case_prod from_mregex (to_mregex_exec r xs) = r"
proof (induct r arbitrary: xs rule: safe_regex_induct)
  case (Plus b g r s)
  from Plus(3) Plus(1)[of xs] Plus(2)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
        intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (TimesF g r s)
  from TimesF(3) TimesF(2)[of xs] TimesF(1)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
        intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (TimesP g r s)
  from TimesP(3) TimesP(1)[of xs] TimesP(2)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
        intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (Star b g r)
  from Star(2) Star(1)[of xs] show ?case
    by (auto split: prod.splits)
qed (auto split: prod.splits if_splits simp: case_Neg_iff )


derive linorder mregex

subsubsection \<open>Left Partial Derivative (LPD)\<close>

definition saturate where
  "saturate f = while (\<lambda>S. f S \<noteq> S) f"

lemma saturate_code[code]:
  "saturate f S = (let S' = f S in if S' = S then S else saturate f S')"
  unfolding saturate_def Let_def
  by (subst while_unfold) auto

definition "MTimesL r S = MTimes r ` S"
definition "MTimesR R s = (\<lambda>r. MTimes r s) ` R"

primrec LPD where
  "LPD (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {MSkip m})"
| "LPD (MTestPos \<phi>) = {}"
| "LPD (MTestNeg \<phi>) = {}"
| "LPD (MPlus r s) = (LPD r \<union> LPD s)"
| "LPD (MTimes r s) = MTimesR (LPD r) s \<union> LPD s"
| "LPD (MStar r) = MTimesR (LPD r) (MStar r)"

primrec LPDi where
  "LPDi 0 r = {r}"
| "LPDi (Suc i) r = (\<Union>s \<in> LPD r. LPDi i s)"

lemma LPDi_Suc_alt: "LPDi (Suc i) r = (\<Union>s \<in> LPDi i r. LPD s)"
  by (induct i arbitrary: r) fastforce+

definition "LPDs r = (\<Union>i. LPDi i r)"

lemma LPDs_refl: "r \<in> LPDs r"
  by (auto simp: LPDs_def intro: exI[of _ 0])
lemma LPDs_trans: "r \<in> LPD s \<Longrightarrow> s \<in> LPDs t \<Longrightarrow> r \<in> LPDs t"
  by (force simp: LPDs_def LPDi_Suc_alt simp del: LPDi.simps intro: exI[of _ "Suc _"])

lemma LPDi_Test:
  "LPDi i (MSkip 0) \<subseteq> {MSkip 0}"
  "LPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma LPDs_Test:
  "LPDs (MSkip 0) \<subseteq> {MSkip 0}"
  "LPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding LPDs_def using LPDi_Test by blast+

lemma LPDi_MSkip: "LPDi i (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  by (induct i arbitrary: n) (auto dest: set_mp[OF LPDi_Test(1)] simp: le_Suc_eq split: nat.splits)

lemma LPDs_MSkip: "LPDs (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  unfolding LPDs_def using LPDi_MSkip by auto

lemma LPDi_Plus: "LPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDi i r \<union> LPDi i s"
  by (induct i arbitrary: r s) auto

lemma LPDs_Plus: "LPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDs r \<union> LPDs s"
  unfolding LPDs_def using LPDi_Plus[of _ r s] by auto

lemma LPDi_Times:
  "LPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) s \<union> (\<Union>j \<le> i. LPDi j s)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case
    by (fastforce simp: MTimesR_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma LPDs_Times: "LPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (LPDs r) s \<union> LPDs s"
  unfolding LPDs_def using LPDi_Times[of _ r s] by (force simp: MTimesR_def)

lemma LPDi_Star: "j \<le> i \<Longrightarrow> LPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) (MStar r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case
    by (auto 0 5 simp: MTimesR_def image_iff le_Suc_eq
        dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF LPDi_Times])
qed simp

lemma LPDs_Star: "LPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesR (LPDs r) (MStar r)"
  unfolding LPDs_def using LPDi_Star[OF order_refl, of _ r] by (force simp: MTimesR_def)

lemma finite_LPDs: "finite (LPDs r)"
proof (induct r)
  case (MSkip n)
  then show ?case by (intro finite_subset[OF LPDs_MSkip]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF LPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF LPDs_Times]) (simp add: MTimesR_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF LPDs_Star]) (simp add: MTimesR_def)
qed

context begin

private abbreviation (input) "addLPD r \<equiv> \<lambda>S. insert r S \<union> Set.bind (insert r S) LPD"

private lemma mono_addLPD: "mono (addLPD r)"
  unfolding mono_def Set.bind_def by auto

private lemma LPDs_aux1: "lfp (addLPD r) \<subseteq> LPDs r"
  by (rule lfp_induct[OF mono_addLPD], auto intro: LPDs_refl LPDs_trans simp: Set.bind_def)

private lemma LPDs_aux2: "LPDi i r \<subseteq> lfp (addLPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) (auto simp: LPDi_Suc_alt simp del: LPDi.simps)
qed

lemma LPDs_alt: "LPDs r = lfp (addLPD r)"
  using LPDs_aux1 LPDs_aux2 by (force simp: LPDs_def)

lemma LPDs_code[code]:
  "LPDs r = saturate (addLPD r) {}"
  unfolding LPDs_alt saturate_def
  by (rule lfp_while[OF mono_addLPD _ finite_LPDs, of r]) (auto simp: LPDs_refl LPDs_trans Set.bind_def)

end

subsubsection \<open>Right Partial Derivative (RPD)\<close>

primrec RPD where
  "RPD (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {MSkip m})"
| "RPD (MTestPos \<phi>) = {}"
| "RPD (MTestNeg \<phi>) = {}"
| "RPD (MPlus r s) = (RPD r \<union> RPD s)"
| "RPD (MTimes r s) = MTimesL r (RPD s) \<union> RPD r"
| "RPD (MStar r) = MTimesL (MStar r) (RPD r)"

primrec RPDi where
  "RPDi 0 r = {r}"
| "RPDi (Suc i) r = (\<Union>s \<in> RPD r. RPDi i s)"

lemma RPDi_Suc_alt: "RPDi (Suc i) r = (\<Union>s \<in> RPDi i r. RPD s)"
  by (induct i arbitrary: r) fastforce+

definition "RPDs r = (\<Union>i. RPDi i r)"

lemma RPDs_refl: "r \<in> RPDs r"
  by (auto simp: RPDs_def intro: exI[of _ 0])
lemma RPDs_trans: "r \<in> RPD s \<Longrightarrow> s \<in> RPDs t \<Longrightarrow> r \<in> RPDs t"
  by (force simp: RPDs_def RPDi_Suc_alt simp del: RPDi.simps intro: exI[of _ "Suc _"])

lemma RPDi_Test:
  "RPDi i (MSkip 0) \<subseteq> {MSkip 0}"
  "RPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma RPDs_Test:
  "RPDs (MSkip 0) \<subseteq> {MSkip 0}"
  "RPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding RPDs_def using RPDi_Test by blast+

lemma RPDi_MSkip: "RPDi i (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  by (induct i arbitrary: n) (auto dest: set_mp[OF RPDi_Test(1)] simp: le_Suc_eq split: nat.splits)

lemma RPDs_MSkip: "RPDs (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  unfolding RPDs_def using RPDi_MSkip by auto

lemma RPDi_Plus: "RPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDi i r \<union> RPDi i s"
  by (induct i arbitrary: r s) auto

lemma RPDi_Suc_RPD_Plus:
  "RPDi (Suc i) r \<subseteq> RPDs (MPlus r s)"
  "RPDi (Suc i) s \<subseteq> RPDs (MPlus r s)"
  unfolding RPDs_def by (force intro!: exI[of _ "Suc i"])+

lemma RPDs_Plus: "RPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDs r \<union> RPDs s"
  unfolding RPDs_def using RPDi_Plus[of _ r s] by auto

lemma RPDi_Times:
  "RPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (\<Union>j \<le> i. RPDi j s) \<union> (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case
    by (fastforce simp: MTimesL_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma RPDs_Times: "RPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (RPDs s) \<union> RPDs r"
  unfolding RPDs_def using RPDi_Times[of _ r s] by (force simp: MTimesL_def)

lemma RPDi_Star: "j \<le> i \<Longrightarrow> RPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case
    by (auto 0 5 simp: MTimesL_def image_iff le_Suc_eq
        dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF RPDi_Times])
qed simp

lemma RPDs_Star: "RPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (RPDs r)"
  unfolding RPDs_def using RPDi_Star[OF order_refl, of _ r] by (force simp: MTimesL_def)

lemma finite_RPDs: "finite (RPDs r)"
proof (induct r)
  case MSkip
  then show ?case by (intro finite_subset[OF RPDs_MSkip]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF RPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF RPDs_Times]) (simp add: MTimesL_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF RPDs_Star]) (simp add: MTimesL_def)
qed

context begin

private abbreviation (input) "addRPD r \<equiv> \<lambda>S. insert r S \<union> Set.bind (insert r S) RPD"

private lemma mono_addRPD: "mono (addRPD r)"
  unfolding mono_def Set.bind_def by auto

private lemma RPDs_aux1: "lfp (addRPD r) \<subseteq> RPDs r"
  by (rule lfp_induct[OF mono_addRPD], auto intro: RPDs_refl RPDs_trans simp: Set.bind_def)

private lemma RPDs_aux2: "RPDi i r \<subseteq> lfp (addRPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) (auto simp: RPDi_Suc_alt simp del: RPDi.simps)
qed

lemma RPDs_alt: "RPDs r = lfp (addRPD r)"
  using RPDs_aux1 RPDs_aux2 by (force simp: RPDs_def)

lemma RPDs_code[code]:
  "RPDs r = saturate (addRPD r) {}"
  unfolding RPDs_alt saturate_def
  by (rule lfp_while[OF mono_addRPD _ finite_RPDs, of r]) (auto simp: RPDs_refl RPDs_trans Set.bind_def)

end

lemma regex_atms_size: "x \<in> regex.atms r \<Longrightarrow> size x < regex.size_regex size r"
  by (induct r) auto

lemma regex_atms_size': "x \<in> regex.atms r \<Longrightarrow> size' x < regex.size_regex size' r"
  by (induct r) auto

lemma atms_size:
  assumes "x \<in> safe_atms r"
  shows "size x < Regex.size_regex size r"
proof -
  { fix y assume "y \<in> regex.atms r" "case y of formula.Neg z \<Rightarrow> x = z | _ \<Rightarrow> False"
    then have "size x < Regex.size_regex size r"
      by (cases y rule: formula.exhaust) (auto dest: regex_atms_size)
  }
  with assms show ?thesis
    unfolding safe_atms_def
    by (auto split: formula.splits dest: regex_atms_size)
qed

lemma atms_size':
  assumes "x \<in> safe_atms r"
  shows "size' x < Regex.size_regex size' r"
proof -
  { fix y assume "y \<in> regex.atms r" "case y of formula.Neg z \<Rightarrow> x = z | _ \<Rightarrow> False"
    then have "size' x < Regex.size_regex size' r"
      by (cases y rule: formula.exhaust) (auto dest: regex_atms_size')
  }
  with assms show ?thesis
    unfolding safe_atms_def
    by (auto split: formula.splits dest: regex_atms_size')
qed


subsection \<open> Datatypes \<close>

type_synonym ts = nat

type_synonym 'a mbuf2 = "'a table list \<times> 'a table list"
type_synonym 'a mbuft2 = "('a table) list \<times> (nat list \<times> 'a table) list"
type_synonym 'a mbufn = "'a table list list"
type_synonym 'a mbuf2S = "'a table list \<times> 'a table list \<times> ts list \<times> bool"

type_synonym 'a msaux = "(ts \<times> 'a table) list"
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"
type_synonym 'a muaux = "(ts \<times> 'a table \<times> 'a table) list"
type_synonym 'a mr\<delta>aux = "(ts \<times> (mregex, 'a table) mapping) list" \<comment> \<open> right and left derivs. aux \<close>
type_synonym 'a ml\<delta>aux = "(ts \<times> 'a table list \<times> 'a table) list"

datatype mconstraint = MEq | MLess | MLessEq

text \<open>The columns of the aggregated formula (@{text aggargs_cols}) and of the two operands of a
  temporal operator (@{text args_L}, @{text args_R}) are the column lists of their tables.\<close>

record aggargs =
  aggargs_cols :: "nat list"
  aggargs_n :: nat
  aggargs_g0 :: bool
  aggargs_y :: nat
  aggargs_\<omega> :: "ty Formula.agg_op"
  aggargs_tys :: "ty list"
  aggargs_f :: "Formula.trm"

record args =
  args_ivl :: \<I>
  args_n :: nat
  args_L :: "nat list"
  args_R :: "nat list"
  args_pos :: bool
  args_agg :: "aggargs option"

datatype pred_mode = Copy | Simple | Match

datatype mtrm = MVar nat | MConst event_data

text \<open>Each node produces its tables over the column list @{const Formula.fv_list} of its
  formula.  A node records the column lists of its operands where it needs them to combine
  their tables: the conjunction, disjunction and existential quantifier, the bound formula
  of a @{text Let} (whose tables are read positionally as a predicate), the multi-way
  conjunction, the regular expressions (over the columns of the whole expression and of each
  atom), and the assignment and constraint conjuncts (to evaluate terms).\<close>

datatype (dead 'msaux, dead 'muaux, dead 'mtaux) mformula =
  MRel "event_data table"
  | MPred Formula.name "Formula.trm list" pred_mode
  | MLet Formula.name nat "nat list" "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula"
  | MFrz Formula.name nat "nat list" "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula"
     nat nat nat "event_data table list"
     "('msaux, 'muaux, 'mtaux) mformula" nat nat "ts list" "event_data table list" enat bool bool
     "nat option" "('msaux, 'muaux, 'mtaux) mformula"
  | MLetPast Formula.name nat "nat list" "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" nat "event_data table option"
  | MAnd "nat list" "('msaux, 'muaux, 'mtaux) mformula" bool "nat list" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2"
  | MAndAssign "nat list" "('msaux, 'muaux, 'mtaux) mformula" "nat \<times> Formula.trm"
  | MAndRel "nat list" "('msaux, 'muaux, 'mtaux) mformula" "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | MAndTrigger "nat list" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuft2" args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" "'mtaux"
  | MAnds "nat list" "nat list list" "nat list list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn"
  | MOr "nat list" "('msaux, 'muaux, 'mtaux) mformula" "nat list" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2"
  | MNeg "('msaux, 'muaux, 'mtaux) mformula"
  | MExists "nat list" "('msaux, 'muaux, 'mtaux) mformula"
  | MAgg "aggargs" "('msaux, 'muaux, 'mtaux) mformula"
  | MPrev \<I> "('msaux, 'muaux, 'mtaux) mformula" bool "event_data table list" "ts list"
  | MNext \<I> "('msaux, 'muaux, 'mtaux) mformula" bool "ts list"
  | MSince args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2S" "'msaux"
  | MUntil args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" ts "'muaux"
  | MTrigger args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" "'mtaux"
  | MMatchP \<I> "nat list" "nat list list" "mregex" "mregex list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn" "ts list" "event_data mr\<delta>aux"
  | MMatchF \<I> "nat list" "nat list list" "mregex" "mregex list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn" "ts list" ts "event_data ml\<delta>aux"
  | MTP mtrm nat
  | MTS mtrm

record ('msaux, 'muaux, 'mtaux) mstate =
  mstate_i :: nat
  mstate_j :: nat
  mstate_m :: "('msaux, 'muaux, 'mtaux) mformula"
  mstate_n :: nat
  mstate_t :: "ts list"

text \<open>The table of a formula @{term \<phi>} at time point @{term i} over the columns @{term cs}: its
  tuples, read as valuations of the first @{term n} variables, are the satisfying valuations in
  the slice @{term R}.\<close>

abbreviation sat_table :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
  ty Formula.formula \<Rightarrow> event_data table \<Rightarrow> bool" where
  "sat_table \<sigma> V n R cs i \<phi> \<equiv> qtable cs (mem_restr R cs) (\<lambda>v. Formula.sat \<sigma> V (val n cs v) i \<phi>)"

text \<open>Two valuations of the same length agree beyond it, so reading a restricted tuple needs no
  bound on the variables.\<close>

lemma nth_beyond_length: "length xs = length ys \<Longrightarrow> length xs \<le> i \<Longrightarrow> xs ! i = ys ! i"
proof (induct xs arbitrary: ys i)
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'"
    by (cases ys) auto
  obtain i' where i: "i = Suc i'"
    using Cons.prems(2) by (cases i) auto
  show ?case
    using Cons.hyps[of ys' i'] Cons.prems by (simp add: ys i)
qed simp

lemma val_restrict_nth:
  assumes "c \<in> set ds"
  shows "val n ds (restrict ds cs x) ! c = val n cs x ! c"
proof (cases "c < n")
  case False
  then show ?thesis
    by (intro nth_beyond_length) simp_all
qed (simp add: tup_get_restrict assms)
lemma sat_restrict: "fv \<phi> \<subseteq> set ds \<Longrightarrow>
  Formula.sat \<sigma> V (val n ds (restrict ds cs v)) i \<phi> = Formula.sat \<sigma> V (val n cs v) i \<phi>"
  by (rule sat_fv_cong) (auto simp: val_restrict_nth)

lemma eval_trm_restrict: "fv_trm t \<subseteq> set ds \<Longrightarrow>
  Formula.eval_trm (val n ds (restrict ds cs v)) t = Formula.eval_trm (val n cs v) t"
  by (rule eval_trm_fv_cong) (auto simp: val_restrict_nth)

text \<open>A join whose second operand's columns are among the first's keeps the first's columns.\<close>

lemma qtable_join_sub:
  assumes "qtable A (mem_restr R A) Q1 X" "qtable B (mem_restr R B) Q2 Y" "distinct A" "distinct B"
    "set B \<subseteq> set A"
    "\<And>x. b \<Longrightarrow> wf_tuple A x \<Longrightarrow> mem_restr R A x \<Longrightarrow> Q x \<longleftrightarrow> Q1 x \<and> Q2 (restrict B A x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple A x \<Longrightarrow> mem_restr R A x \<Longrightarrow> Q x \<longleftrightarrow> Q1 x \<and> \<not> Q2 (restrict B A x)"
  shows "qtable A (mem_restr R A) Q (join A X b B Y)"
proof -
  have A: "A = cols_union A B"
    using assms(5) by (simp add: cols_union_subset)
  show ?thesis
    using assms(1-5)
    by (rule qtable_join[where es=A, OF _ _ _ _ _ A])
      (auto simp: restrict_idle[OF assms(3)] assms(6,7) intro!: restrict_mem_restr)
qed
subsection \<open> Init \<close>

definition init_args :: "\<I> \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow> aggargs option \<Rightarrow> args" where
  "init_args I n L R pos agg = \<lparr>args_ivl = I, args_n = n, args_L = L, args_R = R,
    args_pos = pos, args_agg = agg\<rparr>"

definition init_aggargs :: "nat list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> ty Formula.agg_op \<Rightarrow> ty list \<Rightarrow>
  Formula.trm \<Rightarrow> aggargs" where
  "init_aggargs cs n g0 y \<omega> tys f = \<lparr>aggargs_cols = cs, aggargs_n = n, aggargs_g0 = g0,
    aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_tys = tys, aggargs_f = f\<rparr>"

text \<open>The table of an equation between a variable and a constant has the variable's single
  column; one between two constants has no columns.\<close>

fun eq_rel :: "Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> event_data table" where
  "eq_rel (Formula.Const x) (Formula.Const y) = (if x = y then unit_table else empty_table)"
| "eq_rel (Formula.Var x) (Formula.Const y) = singleton_table y"
| "eq_rel (Formula.Const x) (Formula.Var y) = singleton_table x"
| "eq_rel _ _ = undefined"

text \<open>A term evaluated on a tuple over the columns @{term cs}.\<close>

fun meval_trm :: "nat list \<Rightarrow> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> event_data" where
  "meval_trm cs (Formula.Var x) v = tup_get cs v x"
| "meval_trm cs (Formula.Const x) v = x"
| "meval_trm cs (Formula.Plus x y) v = meval_trm cs x v + meval_trm cs y v"
| "meval_trm cs (Formula.Minus x y) v = meval_trm cs x v - meval_trm cs y v"
| "meval_trm cs (Formula.UMinus x) v = - meval_trm cs x v"
| "meval_trm cs (Formula.Mult x y) v = meval_trm cs x v * meval_trm cs y v"
| "meval_trm cs (Formula.Div x y) v = meval_trm cs x v div meval_trm cs y v"
| "meval_trm cs (Formula.Mod x y) v = meval_trm cs x v mod meval_trm cs y v"
| "meval_trm cs (Formula.F2i x) v = EInt (integer_of_event_data (meval_trm cs x v))"
| "meval_trm cs (Formula.I2f x) v = EFloat (double_of_event_data (meval_trm cs x v))"

lemma meval_trm_eval_trm: "fv_trm t \<subseteq> set cs \<Longrightarrow> \<forall>i\<in>set cs. i < n \<Longrightarrow>
    meval_trm cs t x = Formula.eval_trm (val n cs x) t"
  by (induction t) auto

definition packagg :: "args \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "packagg args f = (case args_agg args of None \<Rightarrow> f
    | Some aggargs \<Rightarrow> Formula.Agg (aggargs_y aggargs)
      (aggargs_\<omega> aggargs) (aggargs_tys aggargs) (aggargs_f aggargs) f)"

text \<open>The aggregation over a table with the columns @{term cs}: the tuples are grouped by
  their values in the columns that are not bound by the aggregation (the key, over
  @{term "shift_cols (length tys) cs"}), and each group yields the aggregate followed by the
  key, a tuple over @{term "y # shift_cols (length tys) cs"}.\<close>

definition agg_key :: "nat \<Rightarrow> nat list \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple" where
  "agg_key k cs x = restrict (filter (\<lambda>x. k \<le> x) cs) cs x"

definition eval_agg :: "nat list \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> ty list \<Rightarrow> Formula.trm \<Rightarrow>
  event_data table \<Rightarrow> event_data table" where
  "eval_agg cs g0 \<omega> tys f rel = (if g0 \<and> rel = empty_table
    then singleton_table (eval_agg_op \<omega> {})
    else (\<lambda>k.
      let group = Set.filter (\<lambda>x. agg_key (length tys) cs x = k) rel;
        M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm cs f x = y) group))) ` meval_trm cs f ` group
      in eval_agg_op \<omega> M # k) ` agg_key (length tys) cs ` rel)"

definition eval_aggargs :: "aggargs \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eval_aggargs args = eval_agg (aggargs_cols args) (aggargs_g0 args)
    (aggargs_\<omega> args) (aggargs_tys args) (aggargs_f args)"

definition eval_args_agg :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eval_args_agg args X = (case args_agg args of None \<Rightarrow> X | Some aggargs \<Rightarrow> eval_aggargs aggargs X)"

definition type_restr :: "aggargs \<Rightarrow> event_data table \<Rightarrow> bool" where
  "type_restr args X = (let Z = meval_trm (aggargs_cols args) (aggargs_f args) ` X;
    all_int = Z \<subseteq> range EInt;
    all_float = Z \<subseteq> range EFloat;
    all_string = Z \<subseteq> range EString in
    case aggargs_\<omega> args of (Formula.Agg_Cnt, _) \<Rightarrow> True
    | (Formula.Agg_Min, _) \<Rightarrow> all_int \<or> all_string
    | (Formula.Agg_Max, _) \<Rightarrow> all_int \<or> all_string
    | (Formula.Agg_Sum, _) \<Rightarrow> all_int
    | (Formula.Agg_Avg, _) \<Rightarrow> all_int
    | (Formula.Agg_Med, _) \<Rightarrow> all_int)"

lemma meval_trm_cong: "(\<And>i. i \<in> Formula.fv_trm f \<Longrightarrow> tup_get cs ts i = tup_get cs' ts' i) \<Longrightarrow>
  meval_trm cs f ts = meval_trm cs' f ts'"
  by (induction cs f ts rule: meval_trm.induct) auto

definition safe_aggargs :: "aggargs \<Rightarrow> bool" where
  "safe_aggargs args = (aggargs_y args < aggargs_n args \<and> distinct (aggargs_cols args) \<and>
    (\<forall>i \<in> set (aggargs_cols args). i < length (aggargs_tys args) + aggargs_n args) \<and>
    aggargs_y args + length (aggargs_tys args) \<notin> set (aggargs_cols args) \<and>
    {0..<length (aggargs_tys args)} \<subseteq> set (aggargs_cols args) \<and>
    Formula.fv_trm (aggargs_f args) \<subseteq> set (aggargs_cols args) \<and>
    aggargs_g0 args = (set (aggargs_cols args) \<subseteq> {0..<length (aggargs_tys args)}))"

definition "valid_aggargs n R args = (case args of None \<Rightarrow> True | Some aggargs \<Rightarrow>
  n = length (aggargs_tys aggargs) + aggargs_n aggargs \<and> R = aggargs_cols aggargs \<and> safe_aggargs aggargs)"

text \<open>The columns of the result of a temporal operator, after the aggregation if any.\<close>

definition args_cols :: "args \<Rightarrow> nat list" where
  "args_cols args = (case args_agg args of None \<Rightarrow> args_R args
    | Some aggargs \<Rightarrow> aggargs_y aggargs # shift_cols (length (aggargs_tys aggargs)) (args_R args))"
locale msaux =
  fixes valid_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> event_data msaux \<Rightarrow> bool"
    and init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"
  assumes valid_init_msaux: "set L \<subseteq> set R \<Longrightarrow> distinct L \<Longrightarrow> distinct R \<Longrightarrow> valid_aggargs n R agg \<Longrightarrow>
    valid_msaux (init_args I n L R pos agg) 0 (init_msaux (init_args I n L R pos agg)) []"
  assumes valid_add_new_ts_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    valid_msaux args nt (add_new_ts_msaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  assumes valid_join_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow>
    table (args_L args) rel1 \<Longrightarrow>
    valid_msaux args cur (join_msaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) (args_L args) rel1)) auxlist)"
  assumes valid_add_new_table_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow>
    table (args_R args) rel2 \<Longrightarrow>
    valid_msaux args cur (add_new_table_msaux args rel2 aux)
    (case auxlist of
      [] => [(cur, rel2)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
  assumes valid_result_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow> result_msaux args aux =
    eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"

fun trigger_results :: "args \<Rightarrow> ts \<Rightarrow> event_data mtaux \<Rightarrow> (nat list \<times> event_data table)" where
  "trigger_results args cur auxlist = (
    if (length (filter (\<lambda> (t, _, _). mem (args_ivl args) (cur - t)) auxlist) > 0) then (
      (args_R args), {
      tuple. wf_tuple (args_R args) tuple \<and>
        \<comment> \<open>pretty much the definition of trigger\<close>
        (\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (cur - t) \<longrightarrow> 
          \<comment> \<open>either \<psi> holds or there is a later database where the same tuple satisfies \<phi>\<close>
          (
            tuple \<in> r \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) ((fst o snd) (auxlist!j)) (restrict (args_L args) (args_R args) tuple) \<comment> \<open>t < t' is given as the list is sorted\<close>
            )
          )
        )
      }
    ) else
    ([], unit_table)
)"

locale mtaux =
  fixes valid_mtaux :: "args \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    (* and update_mtaux_constraint :: "args \<Rightarrow> ts \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux" *)
    (* and update_mtaux_safe_assignment :: "args \<Rightarrow> ts \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux" *)
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat list \<times> event_data table)"

  (* the initial state should be valid *)
  assumes valid_init_mtaux: "(
    if (mem I 0)
      then
        set L \<subseteq> set R
      else 
        L = R
    ) \<Longrightarrow>
    distinct L \<Longrightarrow> distinct R \<Longrightarrow>
    \<not>mem I 0 \<longrightarrow> pos \<Longrightarrow>
    let args = init_args I n L R pos agg in
    valid_mtaux args 0 (init_mtaux args) []"

  (* assuming the previous state outputted the same result, the next will as well *)
  assumes valid_update_mtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (args_L args) l \<Longrightarrow>
    table (args_R args) r \<Longrightarrow>    valid_mtaux args cur aux auxlist \<Longrightarrow>
    valid_mtaux
      args
      nt
      (update_mtaux args nt l r aux)
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "

  and valid_result_mtaux: "
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    result_mtaux args aux = trigger_results args cur auxlist
  "

fun check_before :: "\<I> \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a \<times> 'b) \<Rightarrow> bool" where
  "check_before I dt (t, a, b) \<longleftrightarrow> \<not> memR I (dt - t)"

fun proj_thd :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c" where
  "proj_thd (t, a1, a2) = a2"

definition update_until :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow> event_data muaux" where
  "update_until args rel1 rel2 nt aux =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if (args_pos args) then a1 \<inter> rel1 else a1 \<union> rel1,
      if mem  (args_ivl args) (nt - t) then a2 \<union> join (args_R args) rel2 (args_pos args) (args_L args) a1 else a2)) aux) @
    [(nt, rel1, if memL (args_ivl args) 0 then rel2 else empty_table)]"
lemma map_proj_thd_update_until: "map proj_thd (takeWhile (check_before (args_ivl args) nt) auxlist) =
  map proj_thd (takeWhile (check_before (args_ivl args) nt) (update_until args rel1 rel2 nt auxlist))"
proof (induction auxlist)
  case Nil
  then show ?case by (simp add: update_until_def)
next
  case (Cons a auxlist)
  then show ?case
    by (auto simp add: update_until_def split: if_splits prod.splits)
qed

fun eval_until :: "\<I> \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow> event_data table list \<times> event_data muaux" where
  "eval_until I nt [] = ([], [])"
| "eval_until I nt ((t, a1, a2) # aux) = (if \<not> memR I (nt - t) then
    (let (xs, aux) = eval_until I nt aux in (a2 # xs, aux)) else ([], (t, a1, a2) # aux))"

lemma eval_until_length:
  "eval_until I nt auxlist = (res, auxlist') \<Longrightarrow> length auxlist = length res + length auxlist'"
  by (induction I nt auxlist arbitrary: res auxlist' rule: eval_until.induct)
    (auto split: if_splits prod.splits)

lemma eval_until_res: "eval_until I nt auxlist = (res, auxlist') \<Longrightarrow>
  res = map proj_thd (takeWhile (check_before I nt) auxlist)"
  by (induction I nt auxlist arbitrary: res auxlist' rule: eval_until.induct)
    (auto split: prod.splits)

lemma eval_until_auxlist': "eval_until I nt auxlist = (res, auxlist') \<Longrightarrow>
  auxlist' = drop (length res) auxlist"
  by (induction I nt auxlist arbitrary: res auxlist' rule: eval_until.induct)
    (auto split: if_splits prod.splits)

locale muaux =
  fixes valid_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data muaux \<Rightarrow> bool"
    and init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"
  assumes valid_init_muaux: "set L \<subseteq> set R \<Longrightarrow> distinct L \<Longrightarrow> distinct R \<Longrightarrow> valid_aggargs n R aggargs \<Longrightarrow>
    valid_muaux (init_args I n L R pos aggargs) 0 (init_muaux (init_args I n L R pos aggargs)) []"
  assumes valid_add_new_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow>
    table (args_L args) rel1 \<Longrightarrow>
    table (args_R args) rel2 \<Longrightarrow>    nt \<ge> cur \<Longrightarrow>
    valid_muaux args nt (add_new_muaux args rel1 rel2 nt aux)
    (update_until args rel1 rel2 nt auxlist)"
  assumes valid_length_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow> length_muaux args aux = length auxlist"
  assumes valid_eval_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    eval_muaux args nt aux = (res, aux') \<Longrightarrow> eval_until (args_ivl args) nt auxlist = (res', auxlist') \<Longrightarrow>
    valid_muaux args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"

locale maux = msaux valid_msaux init_msaux add_new_ts_msaux join_msaux add_new_table_msaux result_msaux +
  muaux valid_muaux init_muaux add_new_muaux length_muaux eval_muaux + 
  mtaux valid_mtaux init_mtaux update_mtaux result_mtaux
  for valid_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> event_data msaux \<Rightarrow> bool"
    and init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"

    and valid_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data muaux \<Rightarrow> bool"
    and init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> nat \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"

    and valid_mtaux :: "args \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat list \<times> event_data table)"

fun split_assignment :: "nat set \<Rightarrow> 't Formula.formula \<Rightarrow> nat \<times> Formula.trm" where
  "split_assignment X (Formula.Eq t1 t2) = (case (t1, t2) of
      (Formula.Var x, Formula.Var y) \<Rightarrow> if x \<in> X then (y, t1) else (x, t2)
    | (Formula.Var x, _) \<Rightarrow> (x, t2)
    | (_, Formula.Var y) \<Rightarrow> (y, t1))"
| "split_assignment _ _ = undefined"

fun split_constraint :: "'t Formula.formula \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "split_constraint (Formula.Eq t1 t2) = (t1, True, MEq, t2)"
| "split_constraint (Formula.Less t1 t2) = (t1, True, MLess, t2)"
| "split_constraint (Formula.LessEq t1 t2) = (t1, True, MLessEq, t2)"
| "split_constraint (Formula.Neg (Formula.Eq t1 t2)) = (t1, False, MEq, t2)"
| "split_constraint (Formula.Neg (Formula.Less t1 t2)) = (t1, False, MLess, t2)"
| "split_constraint (Formula.Neg (Formula.LessEq t1 t2)) = (t1, False, MLessEq, t2)"
| "split_constraint _ = undefined"

definition is_copy_pattern :: "nat \<Rightarrow> Formula.trm list \<Rightarrow> bool" where
  "is_copy_pattern n ts = (ts = map Formula.Var [0..<n])"

fun is_simple_pattern :: "Formula.trm list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_simple_pattern [] _ = True"
| "is_simple_pattern (Formula.Var y # ts) x = (x \<le> y \<and> is_simple_pattern ts (Suc y))"
| "is_simple_pattern _ _ = False"

definition pred_mode_of :: "nat \<Rightarrow> Formula.trm list \<Rightarrow> pred_mode" where
  "pred_mode_of n ts = (if is_copy_pattern n ts then Copy
    else if is_simple_pattern ts 0 then Simple else Match)"

abbreviation (input) "init_mbuf2S \<equiv> ([], [], [], False)"

definition (in msaux) "init_since minit0 n agg \<phi> I \<psi> =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) b agg)) in
   if safe_formula \<phi>
   then MSince (args True) (minit0 n \<phi>) (minit0 n \<psi>) init_mbuf2S (init_msaux (args True))
   else (case \<phi> of
     Formula.Neg \<phi>' \<Rightarrow> MSince (args False) (minit0 n \<phi>') (minit0 n \<psi>) init_mbuf2S (init_msaux (args False))
   | _ \<Rightarrow> MRel empty_table))"

lemma (in msaux) init_since_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<psi> \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_since minit0 n agg \<phi> I \<psi> = init_since minit0' n agg \<phi> I \<psi>"
  using assms
  by (auto simp: init_since_def split: formula.splits)

definition (in muaux) "init_until minit0 n agg \<phi> I \<psi> =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) b agg)) in
   if safe_formula \<phi>
   then MUntil (args True) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux (args True))
   else (case \<phi> of
     Formula.Neg \<phi>' \<Rightarrow> MUntil (args False) (minit0 n \<phi>') (minit0 n \<psi>) ([], []) [] 0 (init_muaux (args False))
   | _ \<Rightarrow> MRel empty_table))"

lemma (in muaux) init_until_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<psi> \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_until minit0 n agg \<phi> I \<psi> = init_until minit0' n agg \<phi> I \<psi>"
  using assms
  by (auto simp: init_until_def split: formula.splits)

definition (in mtaux) "init_and_trigger minit0 n agg \<phi> \<phi>' I \<psi>' =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>') (Formula.fv_list \<psi>') b agg)) in
    if (safe_formula \<phi>') then
      MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) (args True) (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mtaux (args True))
    else (case \<phi>' of 
      Formula.Neg \<phi>' \<Rightarrow> MAndTrigger (Formula.fv_list \<phi>) (minit0 n \<phi>) ([], []) (args False) (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mtaux (args False))
      | _ \<Rightarrow> MRel empty_table))"

lemma (in mtaux) init_and_trigger_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<phi>' + size' \<psi>' \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_and_trigger minit0 n agg \<phi> \<phi>' I \<psi>' = init_and_trigger minit0' n agg \<phi> \<phi>' I \<psi>'"
  using assms
  by (clarsimp simp: init_and_trigger_def split: formula.splits)

definition (in mtaux) "init_trigger minit0 n agg \<phi> I \<psi> =
  (let args = (\<lambda>b. (init_args I n (Formula.fv_list \<phi>) (Formula.fv_list \<psi>) b agg)) in
   if safe_formula \<phi>
    then MTrigger (args True) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mtaux (args True))
    else (case \<phi> of
      Formula.Neg \<phi> \<Rightarrow> MTrigger (args False) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mtaux (args False))
      | _ \<Rightarrow> MRel empty_table))"
lemma (in mtaux) init_trigger_cong[fundef_cong]:
  assumes "\<And>\<alpha> m. size' \<alpha> \<le> size' \<phi> + size' \<psi> \<Longrightarrow> minit0 m \<alpha> = minit0' m \<alpha>"
  shows "init_trigger minit0 n agg \<phi> I \<psi> = init_trigger minit0' n agg \<phi> I \<psi>"
  using assms
  by (auto simp: init_trigger_def split: formula.splits)



subsubsection \<open> minit0 \<close>

fun mtrm_of_trm :: "Formula.trm \<Rightarrow> mtrm" where
  "mtrm_of_trm (Formula.Var x) = MVar x"
| "mtrm_of_trm (Formula.Const x) = MConst x"
| "mtrm_of_trm _ = undefined"

text \<open>Whether a predicate occurs under a negation.  A freeze's replay base absorbs the time
  points that leave its window with some value of the frozen predicate; which value does not matter
  for the verdicts (they lie beyond the body's past reach), but it decides how much of the replay
  base's state the copies inherit and then throw away.  Under a negation the frozen predicate
  keeps the least with a large table, elsewhere with an empty one (@{text frz_fill} below).\<close>

fun neg_pred :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "neg_pred p (Formula.Neg \<phi>) = Formula.contains_pred p \<phi>"
| "neg_pred p (Formula.Let e \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Frz e \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.LetPast e \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Or \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.And \<phi> \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Ands l) = (\<exists>\<phi>\<in>set l. neg_pred p \<phi>)"
| "neg_pred p (Formula.Exists t \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Agg y \<omega> tys f \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Prev I \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Next I \<phi>) = neg_pred p \<phi>"
| "neg_pred p (Formula.Since \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Until \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Trigger \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.Release \<phi> I \<psi>) = (neg_pred p \<phi> \<or> neg_pred p \<psi>)"
| "neg_pred p (Formula.MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. neg_pred p \<phi>)"
| "neg_pred p (Formula.MatchF I r) = (\<exists>\<phi>\<in>Regex.atms r. neg_pred p \<phi>)"
| "neg_pred p _ = False"

function (in maux) (sequential) minit0 :: "nat \<Rightarrow> ty Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula" where
  "minit0 n (Formula.Neg \<phi>) = (if fv \<phi> = {} then MNeg (minit0 n \<phi>) else MRel empty_table)"
| "minit0 n (Formula.Eq t1 t2) = MRel (eq_rel t1 t2)"
| "minit0 n (Formula.Pred e ts) = MPred e ts (pred_mode_of n ts)"
| "minit0 n (Formula.Let p \<phi> \<psi>) = MLet p (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>)"
| "minit0 n (Formula.Frz p \<phi> \<psi>) = MFrz p (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>) 0 0 0 []
    (minit0 n \<psi>) 0 0 [] [] (past_reach \<psi>) (safe_letpast (p, Formula.nfv \<phi>) \<psi> \<le> NonFutuRec)
    (neg_pred (p, Formula.nfv \<phi>) \<psi>) None (minit0 n \<psi>)"
| "minit0 n (Formula.LetPast p \<phi> \<psi>) = MLetPast p (Formula.nfv \<phi>) (Formula.fv_list \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>) 0 None"
| "minit0 n (Formula.Or \<phi> \<psi>) = MOr (Formula.fv_list \<phi>) (minit0 n \<phi>) (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])"
| "minit0 n (Formula.And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      MAndAssign (Formula.fv_list \<phi>) (minit0 n \<phi>) (split_assignment (fv \<phi>) \<psi>)
    else if safe_formula \<psi> then
      MAnd (Formula.fv_list \<phi>) (minit0 n \<phi>) True (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])
    else if is_constraint \<psi> then
      MAndRel (Formula.fv_list \<phi>) (minit0 n \<phi>) (split_constraint \<psi>)
    else (case \<psi> of
        (Formula.Neg \<psi>) \<Rightarrow> MAnd (Formula.fv_list \<phi>) (minit0 n \<phi>) False (Formula.fv_list \<psi>) (minit0 n \<psi>) ([], [])
      | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> init_and_trigger minit0 n None \<phi> \<phi>' I \<psi>'
      | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      | _ \<Rightarrow> MRel empty_table))"
| "minit0 n (Formula.Ands l) = (let (pos, neg) = partition safe_formula l in
    let mpos = map (minit0 n) pos in
    let mneg = map (minit0 n) (map remove_neg neg) in \<comment> \<open>Trigger is passed as is\<close>
    let vpos = map Formula.fv_list pos in
    let vneg = map Formula.fv_list neg in
    MAnds (Formula.fv_list (Formula.Ands l)) vpos vneg (mpos @ mneg) (replicate (length l) []))"
| "minit0 n (Formula.Exists t \<phi>) = MExists (Formula.fv_list \<phi>) (minit0 (Suc n) \<phi>)"
| "minit0 n (Formula.Agg y \<omega> tys f \<phi>) = 
    (let default = MAgg (init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) (minit0 (length tys + n) \<phi>) in
    (case \<phi> of Formula.Since \<phi>' I \<psi>' \<Rightarrow>
        let agg = Some (init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) in
        init_since minit0 (length tys + n) agg \<phi>' I \<psi>'
     | Formula.Until \<phi>' I \<psi>' \<Rightarrow>
        let agg = Some (init_aggargs (Formula.fv_list \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) in
        init_until minit0 (length tys + n) agg \<phi>' I \<psi>'
     | _ \<Rightarrow> default))"
| "minit0 n (Formula.Prev I \<phi>) = MPrev I (minit0 n \<phi>) True [] []"
| "minit0 n (Formula.Next I \<phi>) = MNext I (minit0 n \<phi>) True []"
| "minit0 n (Formula.Since \<phi> I \<psi>) = init_since minit0 n None \<phi> I \<psi>"
| "minit0 n (Formula.Until \<phi> I \<psi>) = init_until minit0 n None \<phi> I \<psi>"
| "minit0 n (Formula.Trigger \<phi> I \<psi>) = init_trigger minit0 n None \<phi> I \<psi>"
| "minit0 n (Formula.Release \<phi> I \<psi>) = (
  if mem I 0
    then
      minit0 n (release_safe_0 \<phi> I \<psi>)
    else
      minit0 n (release_safe_bounded \<phi> I \<psi>))"
| "minit0 n (Formula.MatchP I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchP I (Formula.fv_list (Formula.MatchP I r)) (map Formula.fv_list \<phi>s) mr
      (sorted_list_of_set (RPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] [])"
| "minit0 n (Formula.MatchF I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchF I (Formula.fv_list (Formula.MatchF I r)) (map Formula.fv_list \<phi>s) mr
      (sorted_list_of_set (LPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] 0 [])"| "minit0 n (Formula.TP t) = MTP (mtrm_of_trm t) 0"
| "minit0 n (Formula.TS t) = MTS (mtrm_of_trm t)"
| "minit0 n _ = MRel empty_table"
  by pat_completeness auto

termination (in maux) minit0
proof ((relation "measure (\<lambda>(_, \<phi>). size' \<phi>)"; clarsimp), goal_cases)
  case (1 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>; clarsimp)
next
  case (2 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>; clarsimp)
next
  case (3 \<phi> \<psi>)
  then show ?case 
    by (cases \<psi>; clarsimp)
next
  case (4 \<phi> \<psi>)
  then show ?case 
    by (cases \<psi>; clarsimp)
next
  case (5 \<phi> \<phi>' I \<psi>')
  then show ?case
    using size'_and_release[of \<phi> \<phi>' I \<psi>']
    by simp
next
  case (6 \<phi>s \<phi>)
  then show ?case
    unfolding less_Suc_eq_le
    using size_list_estimation'[of \<phi> \<phi>s]
    by (simp add: sum_list_mem_leq)
next
  case (7 n \<phi>s \<phi>)
  then show ?case
    unfolding less_Suc_eq_le
    using sum_list_mem_leq[of \<phi> \<phi>s size']
      size'_remove_neg le_trans by metis
next
  case (8 \<phi> I \<psi>)
  then show ?case 
    using size'_release_aux(4)[of \<phi> I \<psi>]
    by simp
next
  case (9 \<phi> I \<psi>)
  then show ?case 
    using size'_release_aux(3)[of \<phi> I \<psi>]
    by simp
next
  case (10 r r' \<phi>s r'' \<phi>s' \<phi>)
  then show ?case 
    by (clarsimp  dest!: to_mregex_ok[OF sym] atms_size')
next
  case (11 r r' \<phi>s r'' \<phi>s' \<phi>)
  then show ?case 
    by (clarsimp  dest!: to_mregex_ok[OF sym] atms_size')
qed
  

lemma (in maux) minit0_release_0:
  assumes mem: "mem I 0"
  shows "minit0 n (Formula.Release \<phi> I \<psi>) = minit0 n (release_safe_0 \<phi> I \<psi>)"
  using assms
  by auto

lemma (in maux) minit0_release_bounded:
  assumes mem: "\<not>mem I 0"
  shows "minit0 n (Formula.Release \<phi> I \<psi>) = minit0 n (release_safe_bounded \<phi> I \<psi>)"
  using assms
  by auto

definition (in maux) minit :: "ty Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate" where
  "minit \<phi> = (let n = Formula.nfv \<phi>
              in \<lparr>mstate_i = 0, mstate_j = 0, mstate_m = minit0 n \<phi>, mstate_n = n, mstate_t = []\<rparr>)"

definition (in maux) minit_safe where
  "minit_safe \<phi> = (if mmonitorable_exec \<phi> then minit \<phi> else undefined)"


subsection \<open> Step \<close>

fun mprev_next :: "\<I> \<Rightarrow> (event_data table) list \<Rightarrow> ts list \<Rightarrow> (event_data table) list \<times> (event_data table) list \<times> ts list" where
  "mprev_next I [] ts = ([], [], ts)"
| "mprev_next I xs [] = ([], xs, [])"
| "mprev_next I xs [t] = ([], xs, [t])"
| "mprev_next I (x # xs) (t # t' # ts) = (let (ys, zs) = mprev_next I xs (t' # ts)
    in ((if mem I ((t' - t)) then x else (empty_table)) # ys, zs))"

fun mbuf2_add where
  "mbuf2_add xs' ys' (xs, ys) = (xs @ xs', ys @ ys')"

fun mbuf2S_add :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> ts list \<Rightarrow> event_data mbuf2S \<Rightarrow> event_data mbuf2S" where
  "mbuf2S_add xs' ys' ts' (xs, ys, ts, skew) = (xs @ xs', ys @ ys', ts @ ts', skew)"

fun mbuf2_take where
  "mbuf2_take f (x # xs, y # ys) = (let (zs, buf) = mbuf2_take f (xs, ys) in (f x y # zs, buf))"
| "mbuf2_take f (xs, ys) = ([], (xs, ys))"

fun mbuf2T_take where
  "mbuf2T_take f z (x # xs, y # ys) (t # ts) = mbuf2T_take f (f x y t z) (xs, ys) ts"
| "mbuf2T_take f z (xs, ys) ts = (z, (xs, ys), ts)"

fun mbuf2t_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    event_data mbuf2 \<Rightarrow> ts \<Rightarrow> ts list \<Rightarrow> 'b \<times> event_data mbuf2 \<times> ts \<times> ts list" where
  "mbuf2t_take f z (x # xs, y # ys) t0 (t # ts) = mbuf2t_take f (f x y t z) (xs, ys) t ts"
| "mbuf2t_take f z (xs, ys) t0 ts = (z, (xs, ys), (case ts of [] \<Rightarrow> t0 | t # _ \<Rightarrow> t), ts)"

context maux begin
context fixes args :: args begin

fun eval_since :: "event_data table list \<Rightarrow> event_data mbuf2S \<Rightarrow> 'msaux \<Rightarrow>
    event_data table list \<times> event_data mbuf2S \<times> 'msaux" where
  "eval_since rs (x # xs, [], t # ts, skew) aux =
    (if skew \<or> memL (args_ivl args) 0
    then (rev rs, (x # xs, [], t # ts, skew), aux)
    else (let aux' = join_msaux args x (add_new_ts_msaux args t aux)
      in (rev (result_msaux args aux' # rs), (xs, [], ts, True), aux')))"
| "eval_since rs (xs, y # ys, ts, True) aux =
    eval_since rs (xs, ys, ts, False) (add_new_table_msaux args y aux)"
| "eval_since rs (x # xs, y # ys, t # ts, False) aux =
    (let aux' = add_new_table_msaux args y (join_msaux args x (add_new_ts_msaux args t aux))
    in eval_since (result_msaux args aux' # rs) (xs, ys, ts, False) aux')"
| "eval_since rs buf aux = (rev rs, buf, aux)"

end (* fixes args *)
end (* maux *)

lemma size_list_length_diff1: "xs \<noteq> [] \<Longrightarrow> [] \<notin> set xs \<Longrightarrow>
  size_list (\<lambda>xs. length xs - Suc 0) xs < size_list length xs"
proof (induct xs)
  case (Cons x xs)
  then show ?case
    by (cases xs) auto
qed simp

fun mbufn_add :: "(event_data table) list list \<Rightarrow> event_data mbufn \<Rightarrow> event_data mbufn" where
  "mbufn_add xs' xs = List.map2 (@) xs xs'"

function mbufn_take :: "((event_data table) list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> event_data mbufn \<Rightarrow> 'b \<times> event_data mbufn" where
  "mbufn_take f z buf = (if buf = [] \<or> [] \<in> set buf then (z, buf)
    else mbufn_take f (f (map hd buf) z) (map tl buf))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(_, _, buf). size_list length buf)")
    (auto simp: comp_def Suc_le_eq size_list_length_diff1)

fun mbufnt_take' :: "((event_data table) list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mbufn \<Rightarrow> ts list \<Rightarrow> 'b \<times> event_data mbufn \<times> ts list" where
  "mbufnt_take' f z buf ts =
    (if [] \<in> set buf \<or> ts = [] then (z, buf, ts)
    else mbufnt_take' f (f (map hd buf) (hd ts) z) (map tl buf) (tl ts))"

fun mbufnt_take :: "(event_data table list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mbufn \<Rightarrow> ts \<Rightarrow> ts list \<Rightarrow> 'b \<times> event_data mbufn \<times> ts \<times> ts list" where
  "mbufnt_take f z buf t0 ts =
    (if [] \<in> set buf \<or> ts = [] then (z, buf, (case ts of [] \<Rightarrow> t0 | t # _ \<Rightarrow> t), ts)
    else mbufnt_take f (f (map hd buf) (hd ts) z) (map tl buf) (hd ts) (tl ts))"

fun match :: "Formula.trm list \<Rightarrow> event_data tuple \<Rightarrow> (nat \<rightharpoonup> event_data) option" where
  "match [] [] = Some Map.empty"
| "match (Formula.Const x # ts) (y # ys) = (if x = y then match ts ys else None)"
| "match (Formula.Var x # ts) (y # ys) = (case match ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "match _ _ = None"

text \<open>A predicate's table is over its variables in the order of their first occurrence.  With a
  simple pattern (distinct variables in increasing order) the tuples of the event are the
  tuples of the table; otherwise they are matched against the pattern and tabulated.\<close>

definition tabulate_match :: "nat list \<Rightarrow> (nat \<rightharpoonup> event_data) \<Rightarrow> event_data tuple" where
  "tabulate_match cs f = map (\<lambda>x. the (f x)) cs"
definition "lookup = Mapping.lookup_default empty_table"

text \<open>The tables of a regular expression's derivatives are over the columns @{term cs} of the
  whole expression, those of its atoms over the columns @{term dss} of each atom.  A lax test
  joins the atom's table into the guard; a strict test, whose atom has the same variables as the
  whole expression, reorders it.\<close>

fun \<epsilon>_lax where
  "\<epsilon>_lax cs dss guard \<phi>s (MSkip n) = (if n = 0 then guard else empty_table)"
| "\<epsilon>_lax cs dss guard \<phi>s (MTestPos i) = join cs guard True (dss ! i) (\<phi>s ! i)"
| "\<epsilon>_lax cs dss guard \<phi>s (MTestNeg i) = join cs guard False (dss ! i) (\<phi>s ! i)"
| "\<epsilon>_lax cs dss guard \<phi>s (MPlus r s) = \<epsilon>_lax cs dss guard \<phi>s r \<union> \<epsilon>_lax cs dss guard \<phi>s s"
| "\<epsilon>_lax cs dss guard \<phi>s (MTimes r s) = join cs (\<epsilon>_lax cs dss guard \<phi>s r) True cs (\<epsilon>_lax cs dss guard \<phi>s s)"
| "\<epsilon>_lax cs dss guard \<phi>s (MStar r) = guard"

fun r\<epsilon>_strict where
  "r\<epsilon>_strict cs dss \<phi>s (MSkip m) = (if m = 0 then unit_table else empty_table)"
| "r\<epsilon>_strict cs dss \<phi>s (MTestPos i) = reorder cs (dss ! i) (\<phi>s ! i)"
| "r\<epsilon>_strict cs dss \<phi>s (MTestNeg i) = (if \<phi>s ! i = empty_table then unit_table else empty_table)"
| "r\<epsilon>_strict cs dss \<phi>s (MPlus r s) = r\<epsilon>_strict cs dss \<phi>s r \<union> r\<epsilon>_strict cs dss \<phi>s s"
| "r\<epsilon>_strict cs dss \<phi>s (MTimes r s) = \<epsilon>_lax cs dss (r\<epsilon>_strict cs dss \<phi>s r) \<phi>s s"
| "r\<epsilon>_strict cs dss \<phi>s (MStar r) = unit_table"

fun l\<epsilon>_strict where
  "l\<epsilon>_strict cs dss \<phi>s (MSkip m) = (if m = 0 then unit_table else empty_table)"
| "l\<epsilon>_strict cs dss \<phi>s (MTestPos i) = reorder cs (dss ! i) (\<phi>s ! i)"
| "l\<epsilon>_strict cs dss \<phi>s (MTestNeg i) = (if \<phi>s ! i = empty_table then unit_table else empty_table)"
| "l\<epsilon>_strict cs dss \<phi>s (MPlus r s) = l\<epsilon>_strict cs dss \<phi>s r \<union> l\<epsilon>_strict cs dss \<phi>s s"
| "l\<epsilon>_strict cs dss \<phi>s (MTimes r s) = \<epsilon>_lax cs dss (l\<epsilon>_strict cs dss \<phi>s s) \<phi>s r"
| "l\<epsilon>_strict cs dss \<phi>s (MStar r) = unit_table"

fun r\<delta> :: "nat list \<Rightarrow> nat list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table"  where
  "r\<delta> cs dss \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> empty_table | Suc m \<Rightarrow> lookup X (\<kappa> (MSkip m)))"
| "r\<delta> cs dss \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "r\<delta> cs dss \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "r\<delta> cs dss \<kappa> X \<phi>s (MPlus r s) = r\<delta> cs dss \<kappa> X \<phi>s r \<union> r\<delta> cs dss \<kappa> X \<phi>s s"
| "r\<delta> cs dss \<kappa> X \<phi>s (MTimes r s) = r\<delta> cs dss (\<lambda>t. \<kappa> (MTimes r t)) X \<phi>s s \<union> \<epsilon>_lax cs dss (r\<delta> cs dss \<kappa> X \<phi>s r) \<phi>s s"
| "r\<delta> cs dss \<kappa> X \<phi>s (MStar r) = r\<delta> cs dss (\<lambda>t. \<kappa> (MTimes (MStar r) t)) X \<phi>s r"

fun l\<delta> :: "nat list \<Rightarrow> nat list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table" where
  "l\<delta> cs dss \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> empty_table | Suc m \<Rightarrow> lookup X (\<kappa> (MSkip m)))"
| "l\<delta> cs dss \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "l\<delta> cs dss \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "l\<delta> cs dss \<kappa> X \<phi>s (MPlus r s) = l\<delta> cs dss \<kappa> X \<phi>s r \<union> l\<delta> cs dss \<kappa> X \<phi>s s"
| "l\<delta> cs dss \<kappa> X \<phi>s (MTimes r s) = l\<delta> cs dss (\<lambda>t. \<kappa> (MTimes t s)) X \<phi>s r \<union> \<epsilon>_lax cs dss (l\<delta> cs dss \<kappa> X \<phi>s s) \<phi>s r"
| "l\<delta> cs dss \<kappa> X \<phi>s (MStar r) = l\<delta> cs dss (\<lambda>t. \<kappa> (MTimes t (MStar r))) X \<phi>s r"
lift_definition mrtabulate :: "mregex list \<Rightarrow> (mregex \<Rightarrow> 'b table) \<Rightarrow> (mregex, 'b table) mapping"
  is "\<lambda>ks f. (map_of (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) ks))" .

lemma lookup_tabulate:
  "distinct xs \<Longrightarrow> lookup (mrtabulate xs f) x = (if x \<in> set xs then f x else empty_table)"
  unfolding lookup_default_def lookup_def
  by transfer (auto simp: Let_def map_filter_def map_of_eq_None_iff o_def image_image dest!: map_of_SomeD
      split: if_splits option.splits)

definition update_matchP :: "nat list \<Rightarrow> nat list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> event_data table list \<Rightarrow> ts \<Rightarrow>
  event_data mr\<delta>aux \<Rightarrow> event_data table \<times> event_data mr\<delta>aux" where
  "update_matchP cs dss I mr mrs rels nt aux =
    (let aux = (case [(t, mrtabulate mrs (\<lambda>mr.
        r\<delta> cs dss id rel rels mr \<union> (if t = nt then r\<epsilon>_strict cs dss rels mr else {}))).
      (t, rel) \<leftarrow> aux, memR I (nt - t)]
      of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict cs dss rels))]
      | x # aux' \<Rightarrow> (if fst x = nt then x # aux'
                     else (nt, mrtabulate mrs (r\<epsilon>_strict cs dss rels)) # x # aux'))
    in (foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux, memL I (nt - t)] {}, aux))"

definition update_matchF_base where
  "update_matchF_base cs dss I mr mrs rels nt =
     (let X = mrtabulate mrs (l\<epsilon>_strict cs dss rels)
     in ([(nt, rels, if memL I 0 then lookup X mr else empty_table)], X))"

definition update_matchF_step where
  "update_matchF_step cs dss I mr mrs nt = (\<lambda>(t, rels', rel) (aux', X).
     (let Y = mrtabulate mrs (l\<delta> cs dss id X rels')
     in ((t, rels', if mem I ((nt - t)) then rel \<union> lookup Y mr else rel) # aux', Y)))"

definition update_matchF :: "nat list \<Rightarrow> nat list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> event_data table list \<Rightarrow> ts \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux" where
  "update_matchF cs dss I mr mrs rels nt aux =
     fst (foldr (update_matchF_step cs dss I mr mrs nt) aux (update_matchF_base cs dss I mr mrs rels nt))"
fun eval_matchF :: "\<I> \<Rightarrow> mregex \<Rightarrow> ts \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> event_data table list \<times> event_data ml\<delta>aux" where
  "eval_matchF I mr nt [] = ([], [])"
| "eval_matchF I mr nt ((t, rels, rel) # aux) = (if \<not> memR I (nt - t) then
    (let (xs, aux) = eval_matchF I mr nt aux in (rel # xs, aux)) else ([], (t, rels, rel) # aux))"

primrec map_split where
  "map_split f [] = ([], [])"
| "map_split f (x # xs) =
    (let (y, z) = f x; (ys, zs) = map_split f xs
    in (y # ys, z # zs))"

lemma map_split_map: "map_split f (map g xs) = map_split (f o g) xs"
  by (induct xs) auto

lemma map_split_alt: "map_split f xs = (map (fst o f) xs, map (snd o f) xs)"
  by (induct xs) (auto split: prod.splits)

text \<open>An assignment appends the assigned variable's column to the tuples over @{term cs}.\<close>

fun eval_assignment :: "nat list \<Rightarrow> nat \<times> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple" where
  "eval_assignment cs (x, t) y = y @ [meval_trm cs t y]"

fun eval_constraint0 :: "mconstraint \<Rightarrow> event_data \<Rightarrow> event_data \<Rightarrow> bool" where
  "eval_constraint0 MEq x y = (x = y)"
| "eval_constraint0 MLess x y = (x < y)"
| "eval_constraint0 MLessEq x y = (x \<le> y)"

fun eval_constraint :: "nat list \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> bool" where
  "eval_constraint cs (t1, p, c, t2) x = (eval_constraint0 c (meval_trm cs t1 x) (meval_trm cs t2 x) = p)"
function letpast_meval0 where
  "letpast_meval0 eval j i ys xs p ts db \<phi> =
     (let (ys', \<phi>') = eval ts (Mapping.update p xs db) \<phi>
     in if size \<phi>' \<noteq> size \<phi> then ([], 0, None, \<phi>)
     else (case ys' of
       [] \<Rightarrow> (ys @ ys', i + length xs, None, \<phi>')
     | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j then (ys @ ys', i + length xs, Some y, \<phi>')
         else letpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))"
  by auto
termination
  by (relation "measure (\<lambda>(_, j, i, _, xs, _). j - (i + length xs))")
    (auto simp: not_le min_def diff_less_mono2)

declare letpast_meval0.simps[simp del]

lemma letpast_meval0_cong[fundef_cong]:
  assumes "(\<And>ts db \<psi>. size \<psi> = size \<phi> \<Longrightarrow>  eval ts db \<psi> = eval' ts db \<psi>)"
  shows "letpast_meval0 eval j i ys xs p ts db \<phi> = letpast_meval0 eval' j i ys xs p ts db \<phi>"
  using assms
proof (induct eval j i ys xs p ts db \<phi> rule: letpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have eval': "eval' ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    using 1(2)[of \<phi>] eval by simp
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval eval' by (subst (1 2) letpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "letpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>' =
      letpast_meval0 eval' j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>'"
      if "size \<phi>' = size \<phi>" "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] 1(2) that by simp
    then show ?thesis
      using eval eval' Cons by (subst (1 2) letpast_meval0.simps) (simp add: Let_def)
  qed
qed

lemma size_letpast_meval: "(\<And>ts db \<psi>. size \<psi> = size \<phi> \<Longrightarrow> size (snd (eval ts db \<psi>)) = size \<psi>) \<Longrightarrow>
  size (snd (snd (snd (letpast_meval0 eval j i ys xs p ts db \<phi>)))) = size \<phi>"
proof (induct eval j i ys xs p ts db \<phi> rule: letpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have size: "size \<phi>' = size \<phi>"
    using 1(2)[of \<phi> ts "Mapping.update p xs db"] eval by simp
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval size by (subst letpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "size (snd (snd (snd (letpast_meval0 eval j (i + length xs) (ys @ ys') ys' p []
      (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))) = size \<phi>'" if "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] 1(2) size that by simp
    then show ?thesis
      using eval size Cons by (subst letpast_meval0.simps) (simp add: Let_def)
  qed
qed

text \<open>The copies stop at the first frozen table whose verdict is not out yet.  That copy's state
  is kept (the live copy), with the number of its verdicts still to come before the pending one,
  and in the next step it is fed the new time points instead of being replayed from the replay
  base again.  The live copy is kept in a slot of its own, @{text \<rho>L}, next to the number of its
  verdicts still to come; without a live copy the slot keeps its previous contents.  A new live
  copy replaces the slot only if it has the same size, which the live copies of a well-formed state
  always have (they are replays of the replay base): so evaluation keeps the size of the state,
  which the termination argument needs.\<close>

definition frz_keep_lv :: "(nat \<times> 'a :: size) option \<Rightarrow> 'a \<Rightarrow> nat option" where
  "frz_keep_lv lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if size st = size \<rho>L then Some g else None | None \<Rightarrow> None)"

definition frz_keep_st :: "(nat \<times> 'a :: size) option \<Rightarrow> 'a \<Rightarrow> 'a" where
  "frz_keep_st lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if size st = size \<rho>L then st else \<rho>L | None \<Rightarrow> \<rho>L)"

lemma size_frz_keep_st[simp]: "size (frz_keep_st lv \<rho>L) = size \<rho>L"
  by (auto simp: frz_keep_st_def split: option.splits)

text \<open>The windowed replay of @{const MFrz}: a time point whose timestamp is more than the past
  reach @{term d} of the body before that of a time point @{term i} is never looked at by the
  verdict at @{term i} or later ones.  The number of such time points at the front of the window
  @{term "tq"} (the timestamps from time point @{term w} on), by which the window can move forward
  before the copy of @{term i}, or, with @{term i} the first undecided time point, at the end of a
  step.  Once every verdict is out (@{term "i = j"}), the timestamp of @{term i} is not known yet;
  that of the last time point, @{term "j - 1"}, bounds it from below.  Without this, a frozen
  formula that never lags would keep the window at its start, and each copy would replay the whole
  prefix.

  When the body does not use the frozen predicate beyond the current time point (the flag
  @{term po}: @{const safe_letpast} of the frozen predicate is at most @{const NonFutuRec}, as for
  the recursive predicate of @{const Formula.LetPast}), a copy's verdict at a time point @{term i}
  needs the frozen predicate only up to @{term i}.  The copy of @{term i} is then fed it only up
  to @{term i}, not up to the last time point (@{text frz_cut}): this matters when the frozen
  formula lags, and the frozen tables of several time points arrive at once.\<close>
definition frz_adv :: "enat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> nat" where
  "frz_adv d w jfrz j tq = (if d \<noteq> \<infinity> \<and> w \<le> jfrz \<and> w < j
     then length (takeWhile (\<lambda>t. enat t + d < enat (tq ! (min jfrz (j - 1) - w))) tq) else 0)"

definition frz_cut :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "frz_cut po w i j = (if po then min (j - w) (Suc i - w) else j - w)"

text \<open>The value of the frozen predicate with which the replay base absorbs the time points that
  leave the window.  They lie beyond the past reach of every verdict still to be computed, so any
  table of the frozen formula will do.  The copies start from the replay base and throw away what
  it holds for those time points.  With the frozen predicate under a negation
  (@{const neg_pred}), the latest frozen table leaves the least of that: a copy's own frozen table
  is typically close to it.  Otherwise the empty table does.\<close>

definition frz_fill :: "bool \<Rightarrow> 'a set list \<Rightarrow> 'a set" where
  "frz_fill ng \<alpha>s = (if ng then last ({} # \<alpha>s) else {})"

lemma frz_fill_cases: "frz_fill ng \<alpha>s = {} \<or> frz_fill ng \<alpha>s \<in> set \<alpha>s"
  by (cases \<alpha>s rule: rev_cases) (auto simp: frz_fill_def)

text \<open>The copies, each with the window moved to its own time point.  The replay base and its window
  (the base, the window's start @{term w}, the base's progress, the window's timestamps and the
  base's verdicts from the first pending one on) are threaded through the copies: before the copy
  for the frozen table of time point @{term i}, the window moves as far as @{term i} allows
  (@{text frz_adv_st}), and after the last copy, as far as the first pending verdict allows.  The
  base's evaluation is a parameter @{term ev}; a moved base replaces the old one only if it has
  the same size @{term sz}, which the evaluation always keeps: the termination argument needs it,
  as for @{text letpast_meval0}.  A copy stops the loop if it does not have its verdict yet.\<close>

definition frz_adv_st :: "('m \<Rightarrow> nat) \<Rightarrow> (ts list \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'm \<Rightarrow> 't list \<times> 'm) \<Rightarrow>
    'k \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'a \<Rightarrow> enat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'm \<times> nat \<times> nat \<times> ts list \<times> 't list \<Rightarrow>
    'm \<times> nat \<times> nat \<times> ts list \<times> 't list" where
  "frz_adv_st sz ev pm dbe fl d j i s = (case s of (\<rho>, w, pR, tq, rb) \<Rightarrow>
     let a = frz_adv d w i j tq in
     (case ev [] (Mapping.update pm (replicate a fl) dbe) \<rho> of (rs, \<rho>') \<Rightarrow>
       if sz \<rho>' = sz \<rho>
       then (\<rho>', w + a, pR + length rs, drop a tq, drop (min i (pR + length rs) - (pR - length rb)) (rb @ rs))
       else s))"

primrec frz_loop :: "('m \<Rightarrow> nat) \<Rightarrow> (ts list \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'm \<Rightarrow> 't list \<times> 'm) \<Rightarrow>
    'k \<Rightarrow> ('k, 'a list) mapping \<Rightarrow> 'a \<Rightarrow> enat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'm \<times> nat \<times> nat \<times> ts list \<times> 't list \<Rightarrow>
    't list \<times> 'a list \<times> (nat \<times> 'm) option \<times> ('m \<times> nat \<times> nat \<times> ts list \<times> 't list)" where
  "frz_loop sz ev pm dbe fl d po j i [] s = ([], [], None, frz_adv_st sz ev pm dbe fl d j i s)"
| "frz_loop sz ev pm dbe fl d po j i (\<alpha> # \<alpha>s) s =
    (case frz_adv_st sz ev pm dbe fl d j i s of (\<rho>, w, pR, tq, rb) \<Rightarrow>
     (case ev [] (Mapping.update pm (replicate (frz_cut po w i j) \<alpha>) dbe) \<rho> of (us, \<sigma>) \<Rightarrow>
      (case drop (i - (pR - length rb)) (rb @ us) of
        [] \<Rightarrow> ([], \<alpha> # \<alpha>s, Some (i - (pR - length rb) - length (rb @ us), \<sigma>), (\<rho>, w, pR, tq, rb))
      | y # _ \<Rightarrow> (case frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) of
          (zs, \<alpha>s', lv, s') \<Rightarrow> (y # zs, \<alpha>s', lv, s')))))"

text \<open>With a live copy (@{term lr}, its verdicts after the new time points and its state), the
  first verdict is the live copy's, if it has it.\<close>

definition frz_live_loop where
  "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (case lr of
     None \<Rightarrow> frz_loop sz ev pm dbe fl d po j i \<alpha>s s
   | Some (g, us, st) \<Rightarrow> (case drop g us of
       [] \<Rightarrow> ([], \<alpha>s, Some (g - length us, st), frz_adv_st sz ev pm dbe fl d j i s)
     | y # _ \<Rightarrow> (case frz_loop sz ev pm dbe fl d po j (Suc i) (tl \<alpha>s) s of
         (zs, \<alpha>s', lv, s') \<Rightarrow> (y # zs, \<alpha>s', lv, s'))))"

lemma size_frz_adv_st: "sz (fst (frz_adv_st sz ev pm dbe fl d j i s)) = sz (fst s)"
  by (auto simp: frz_adv_st_def Let_def split: prod.splits)

lemma frz_loop_size:
  "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s', lv, s') \<Longrightarrow> sz (fst s') = sz (fst s)"
proof (induction \<alpha>s arbitrary: i s ys \<alpha>s' lv s')
  case Nil
  then show ?case
    using size_frz_adv_st[of sz ev pm dbe fl d j i s] by auto
next
  case (Cons \<alpha> \<alpha>s)
  obtain \<rho> w pR tq rb where s1: "frz_adv_st sz ev pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  have sz: "sz \<rho> = sz (fst s)"
    using size_frz_adv_st[of sz ev pm dbe fl d j i s] s1 by simp
  obtain us \<sigma> where e: "ev [] (Mapping.update pm (replicate (frz_cut po w i j) \<alpha>) dbe) \<rho> = (us, \<sigma>)"
    by fastforce
  show ?case
  proof (cases "drop (i - (pR - length rb)) (rb @ us)")
    case Nil
    then show ?thesis
      using Cons.prems s1 e sz by (auto simp: size_frz_adv_st)
  next
    case (Cons y r)
    obtain zs a l s2 where r: "frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) = (zs, a, l, s2)"
      by (metis prod_cases4)
    have "s' = s2"
      using Cons.prems s1 e Cons r by simp
    then show ?thesis
      using Cons.IH[OF r] sz by simp
  qed
qed

lemma frz_live_loop_size:
  "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s', lv, s') \<Longrightarrow> sz (fst s') = sz (fst s)"
  using frz_loop_size[of sz ev pm dbe fl d po j _ _ s] size_frz_adv_st[of sz ev pm dbe fl d j i s]
  by (auto simp: frz_live_loop_def split: option.splits list.splits prod.splits)

lemma frz_adv_st_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_adv_st sz ev pm dbe fl d j i s = frz_adv_st sz ev' pm dbe fl d j i s"
  using assms by (auto simp: frz_adv_st_def split: prod.splits)

lemma frz_loop_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = frz_loop sz ev' pm dbe fl d po j i \<alpha>s s"
  using assms
proof (induction \<alpha>s arbitrary: i s)
  case Nil
  then show ?case
    using frz_adv_st_cong[of sz s ev ev'] by simp
next
  case (Cons \<alpha> \<alpha>s)
  obtain \<rho> w pR tq rb where s': "frz_adv_st sz ev' pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  have adv: "frz_adv_st sz ev pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    using frz_adv_st_cong[of sz s ev ev', OF Cons.prems] s' by simp
  have sz: "sz \<rho> = sz (fst s)"
    using size_frz_adv_st[of sz ev' pm dbe fl d j i s] s' by simp
  have ev: "ev ts db \<rho> = ev' ts db \<rho>" for ts db
    using Cons.prems sz by simp
  have IH: "frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) =
    frz_loop sz ev' pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb)"
    by (rule Cons.IH) (use Cons.prems sz in simp)
  show ?case
    by (simp only: frz_loop.simps adv s' prod.case ev IH)
qed

lemma frz_live_loop_cong[fundef_cong]:
  assumes "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev ts db \<psi> = ev' ts db \<psi>"
  shows "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = frz_live_loop sz ev' pm dbe fl d po j i \<alpha>s lr s"
proof -
  have "frz_loop sz ev pm dbe fl d po j i' \<alpha>s' s = frz_loop sz ev' pm dbe fl d po j i' \<alpha>s' s" for i' \<alpha>s'
    using assms by (rule frz_loop_cong)
  moreover have "frz_adv_st sz ev pm dbe fl d j i s = frz_adv_st sz ev' pm dbe fl d j i s"
    using assms by (rule frz_adv_st_cong)
  ultimately show ?thesis
    by (simp only: frz_live_loop_def)
qed

text \<open>The loop under a simulation.  Two runs whose evaluations are related, on states related by
  @{term R} with the verdicts mapped by @{term g} and the frozen tables by @{term ga}, give related
  results, provided that the size guards of the two runs agree on related states.  And a property
  of the states and the tables that the evaluation keeps holds of the loop's results.  The
  evaluators of the executable and of the dense layers run the same loop on their own states.\<close>

definition frz_st_rel :: "('m \<Rightarrow> 'm' \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 't') \<Rightarrow> 'm \<times> nat \<times> nat \<times> ts list \<times> 't list \<Rightarrow>
    'm' \<times> nat \<times> nat \<times> ts list \<times> 't' list \<Rightarrow> bool" where
  "frz_st_rel R g s s' \<longleftrightarrow> (case s of (\<rho>, w, pR, tq, rb) \<Rightarrow> case s' of (\<rho>', w', pR', tq', rb') \<Rightarrow>
     R \<rho> \<rho>' \<and> w' = w \<and> pR' = pR \<and> tq' = tq \<and> rb' = map g rb)"

lemma frz_st_rel_simps[simp]: "frz_st_rel R g (\<rho>, w, pR, tq, rb) (\<rho>', w', pR', tq', rb') \<longleftrightarrow>
    R \<rho> \<rho>' \<and> w' = w \<and> pR' = pR \<and> tq' = tq \<and> rb' = map g rb"
  by (simp add: frz_st_rel_def)

definition frz_st_inv :: "('m \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> 'm \<times> nat \<times> nat \<times> ts list \<times> 't list \<Rightarrow> bool" where
  "frz_st_inv P T s \<longleftrightarrow> (case s of (\<rho>, w, pR, tq, rb) \<Rightarrow> P \<rho> \<and> list_all T rb)"

lemma frz_st_inv_simps[simp]: "frz_st_inv P T (\<rho>, w, pR, tq, rb) \<longleftrightarrow> P \<rho> \<and> list_all T rb"
  by (simp add: frz_st_inv_def)

lemma frz_adv_st_inv:
  assumes ev: "\<And>\<psi> c. sz \<psi> = sz (fst s) \<Longrightarrow> P \<psi> \<Longrightarrow>
      list_all T (fst (ev [] (Mapping.update pm (replicate c fl) dbe) \<psi>)) \<and>
      P (snd (ev [] (Mapping.update pm (replicate c fl) dbe) \<psi>))"
    and st: "frz_st_inv P T s"
  shows "frz_st_inv P T (frz_adv_st sz ev pm dbe fl d j i s)"
proof -
  obtain \<rho> w pR tq rb where s: "s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  let ?a = "frz_adv d w i j tq"
  obtain rs \<sigma> where e: "ev [] (Mapping.update pm (replicate ?a fl) dbe) \<rho> = (rs, \<sigma>)"
    by fastforce
  have "list_all T rs" "P \<sigma>"
    using ev[of \<rho> ?a] st s e by simp_all
  then show ?thesis
    using st s e by (auto simp: frz_adv_st_def Let_def list_all_iff dest: in_set_dropD)
qed

lemma frz_loop_inv:
  assumes ev: "\<And>\<psi> c X. sz \<psi> = sz (fst s) \<Longrightarrow> P \<psi> \<Longrightarrow> X \<in> insert fl (set \<alpha>s) \<Longrightarrow>
      list_all T (fst (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>)) \<and>
      P (snd (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>))"
    and st: "frz_st_inv P T s"
    and r: "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s1, lv, s1)"
  shows "list_all T ys \<and> set \<alpha>s1 \<subseteq> set \<alpha>s \<and> (\<forall>k \<sigma>. lv = Some (k, \<sigma>) \<longrightarrow> P \<sigma>) \<and> frz_st_inv P T s1"
  using ev st r
proof (induction \<alpha>s arbitrary: i s ys \<alpha>s1 lv s1)
  case Nil
  have "frz_st_inv P T (frz_adv_st sz ev pm dbe fl d j i s)"
    by (rule frz_adv_st_inv[OF _ Nil.prems(2)]) (use Nil.prems(1) in blast)
  then show ?case
    using Nil.prems(3) by auto
next
  case (Cons \<alpha> \<alpha>s)
  note prems = Cons.prems and IH = Cons.IH
  have adv: "frz_st_inv P T (frz_adv_st sz ev pm dbe fl d j i s)"
    by (rule frz_adv_st_inv[OF _ prems(2)]) (use prems(1) in blast)
  obtain \<rho> w pR tq rb where s1: "frz_adv_st sz ev pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  have sz\<rho>: "sz \<rho> = sz (fst s)"
    using size_frz_adv_st[of sz ev pm dbe fl d j i s] s1 by simp
  have P\<rho>: "P \<rho>" and Trb: "list_all T rb"
    using adv s1 by simp_all
  let ?c = "frz_cut po w i j"
  obtain us \<sigma> where e: "ev [] (Mapping.update pm (replicate ?c \<alpha>) dbe) \<rho> = (us, \<sigma>)"
    by fastforce
  have "list_all T (fst (ev [] (Mapping.update pm (replicate ?c \<alpha>) dbe) \<rho>)) \<and>
      P (snd (ev [] (Mapping.update pm (replicate ?c \<alpha>) dbe) \<rho>))"
    by (rule prems(1)) (use sz\<rho> P\<rho> in auto)
  then have Tus: "list_all T us" and P\<sigma>: "P \<sigma>"
    using e by simp_all
  show ?case
  proof (cases "drop (i - (pR - length rb)) (rb @ us)")
    case Nil
    then show ?thesis
      using prems(3) s1 e P\<sigma> adv by auto
  next
    case (Cons y r)
    obtain zs bs lv0 s2 where rec: "frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) = (zs, bs, lv0, s2)"
      by (metis prod_cases4)
    have IH': "list_all T zs \<and> set bs \<subseteq> set \<alpha>s \<and> (\<forall>k \<sigma>. lv0 = Some (k, \<sigma>) \<longrightarrow> P \<sigma>) \<and> frz_st_inv P T s2"
      by (rule IH[OF _ _ rec]) (use prems(1) sz\<rho> P\<rho> Trb in auto)
    have "T y"
      using Cons Tus Trb by (metis in_set_dropD list.set_intros(1) list_all_append list_all_iff)
    moreover have "ys = y # zs" "\<alpha>s1 = bs" "lv = lv0" "s1 = s2"
      using prems(3) s1 e Cons rec by auto
    ultimately show ?thesis
      using IH' by auto
  qed
qed

lemma frz_live_loop_inv:
  assumes ev: "\<And>\<psi> c X. sz \<psi> = sz (fst s) \<Longrightarrow> P \<psi> \<Longrightarrow> X \<in> insert fl (set \<alpha>s) \<Longrightarrow>
      list_all T (fst (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>)) \<and>
      P (snd (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>))"
    and st: "frz_st_inv P T s"
    and L: "\<And>k us \<sigma>. lr = Some (k, us, \<sigma>) \<Longrightarrow> list_all T us \<and> P \<sigma>"
    and r: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s1, lv, s1)"
  shows "list_all T ys \<and> set \<alpha>s1 \<subseteq> set \<alpha>s \<and> (\<forall>k \<sigma>. lv = Some (k, \<sigma>) \<longrightarrow> P \<sigma>) \<and> frz_st_inv P T s1"
proof (cases lr)
  case None
  with r have r0: "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s1, lv, s1)"
    by (simp add: frz_live_loop_def)
  show ?thesis
    by (rule frz_loop_inv[OF _ st r0]) (rule ev, assumption+)
next
  case (Some x)
  then obtain k us \<sigma> where lr: "lr = Some (k, us, \<sigma>)"
    by (cases x) auto
  have Tus: "list_all T us" and P\<sigma>: "P \<sigma>"
    using L[OF lr] by simp_all
  show ?thesis
  proof (cases "drop k us")
    case Nil
    have "frz_st_inv P T (frz_adv_st sz ev pm dbe fl d j i s)"
      by (rule frz_adv_st_inv[OF _ st]) (use ev in blast)
    then show ?thesis
      using r lr Nil P\<sigma> by (auto simp: frz_live_loop_def)
  next
    case (Cons y r0)
    obtain zs bs lv0 s2 where rec: "frz_loop sz ev pm dbe fl d po j (Suc i) (tl \<alpha>s) s = (zs, bs, lv0, s2)"
      by (metis prod_cases4)
    have IH': "list_all T zs \<and> set bs \<subseteq> set (tl \<alpha>s) \<and> (\<forall>k \<sigma>. lv0 = Some (k, \<sigma>) \<longrightarrow> P \<sigma>) \<and> frz_st_inv P T s2"
      by (rule frz_loop_inv[OF _ st rec]) (rule ev, assumption+, cases \<alpha>s; auto)
    have "T y"
      using Cons Tus by (metis in_set_dropD list.set_intros(1) list_all_iff)
    moreover have "ys = y # zs" "\<alpha>s1 = bs" "lv = lv0" "s1 = s2"
      using r lr Cons rec by (auto simp: frz_live_loop_def)
    moreover have "set (tl \<alpha>s) \<subseteq> set \<alpha>s"
      by (cases \<alpha>s) auto
    ultimately show ?thesis
      using IH' by auto
  qed
qed

lemma frz_adv_st_rel:
  assumes ev: "\<And>\<psi> \<psi>' c. sz \<psi> = sz (fst s) \<Longrightarrow> R \<psi> \<psi>' \<Longrightarrow>
      fst (ev' [] (Mapping.update pm' (replicate c (ga fl)) dbe') \<psi>') =
        map g (fst (ev [] (Mapping.update pm (replicate c fl) dbe) \<psi>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate c fl) dbe) \<psi>))
        (snd (ev' [] (Mapping.update pm' (replicate c (ga fl)) dbe') \<psi>'))"
    and sz: "\<And>\<psi>1 \<psi>1' \<psi>2 \<psi>2'. R \<psi>1 \<psi>1' \<Longrightarrow> R \<psi>2 \<psi>2' \<Longrightarrow> sz \<psi>1 = sz \<psi>2 \<longleftrightarrow> sz' \<psi>1' = sz' \<psi>2'"
    and st: "frz_st_rel R g s s'"
  shows "frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s')"
proof -
  obtain \<rho> w pR tq rb where s: "s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  with st obtain \<rho>' where s': "s' = (\<rho>', w, pR, tq, map g rb)" and R: "R \<rho> \<rho>'"
    by (cases s') auto
  let ?a = "frz_adv d w i j tq"
  obtain rs \<sigma> where e: "ev [] (Mapping.update pm (replicate ?a fl) dbe) \<rho> = (rs, \<sigma>)"
    by fastforce
  obtain rs' \<sigma>' where e': "ev' [] (Mapping.update pm' (replicate ?a (ga fl)) dbe') \<rho>' = (rs', \<sigma>')"
    by fastforce
  have rs': "rs' = map g rs" and R\<sigma>: "R \<sigma> \<sigma>'"
    using ev[of \<rho> \<rho>' ?a] R e e' s by simp_all
  have guard: "sz \<sigma> = sz \<rho> \<longleftrightarrow> sz' \<sigma>' = sz' \<rho>'"
    by (rule sz[OF R\<sigma> R])
  show ?thesis
    using s s' e e' rs' R\<sigma> R guard by (auto simp: frz_adv_st_def Let_def drop_map[symmetric])
qed

lemma frz_loop_rel:
  assumes ev: "\<And>\<psi> \<psi>' c X. sz \<psi> = sz (fst s) \<Longrightarrow> R \<psi> \<psi>' \<Longrightarrow> X \<in> insert fl (set \<alpha>s) \<Longrightarrow>
      fst (ev' [] (Mapping.update pm' (replicate c (ga X)) dbe') \<psi>') =
        map g (fst (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>))
        (snd (ev' [] (Mapping.update pm' (replicate c (ga X)) dbe') \<psi>'))"
    and sz: "\<And>\<psi>1 \<psi>1' \<psi>2 \<psi>2'. R \<psi>1 \<psi>1' \<Longrightarrow> R \<psi>2 \<psi>2' \<Longrightarrow> sz \<psi>1 = sz \<psi>2 \<longleftrightarrow> sz' \<psi>1' = sz' \<psi>2'"
    and st: "frz_st_rel R g s s'"
    and r: "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s1, lv, s1)"
    and r': "frz_loop sz' ev' pm' dbe' (ga fl) d po j i (map ga \<alpha>s) s' = (ys', \<alpha>s1', lv', s1')"
  shows "ys' = map g ys \<and> \<alpha>s1' = map ga \<alpha>s1 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv lv' \<and>
    frz_st_rel R g s1 s1'"
  using ev st r r'
proof (induction \<alpha>s arbitrary: i s s' ys \<alpha>s1 lv s1 ys' \<alpha>s1' lv' s1')
  case Nil
  have "frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s')"
    by (rule frz_adv_st_rel[OF _ sz Nil.prems(2)]) (use Nil.prems(1) in blast)
  then show ?case
    using Nil.prems(3,4) by auto
next
  case (Cons \<alpha> \<alpha>s)
  note prems = Cons.prems and IH = Cons.IH
  have adv: "frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s')"
    by (rule frz_adv_st_rel[OF _ sz prems(2)]) (use prems(1) in blast)
  obtain \<rho> w pR tq rb where s1: "frz_adv_st sz ev pm dbe fl d j i s = (\<rho>, w, pR, tq, rb)"
    by (metis prod_cases5)
  with adv obtain \<rho>' where s1': "frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s' = (\<rho>', w, pR, tq, map g rb)"
    and R: "R \<rho> \<rho>'"
    by (cases "frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s'") auto
  have sz\<rho>: "sz \<rho> = sz (fst s)"
    using size_frz_adv_st[of sz ev pm dbe fl d j i s] s1 by simp
  let ?c = "frz_cut po w i j"
  obtain us \<sigma> where e: "ev [] (Mapping.update pm (replicate ?c \<alpha>) dbe) \<rho> = (us, \<sigma>)"
    by fastforce
  obtain us' \<sigma>' where e': "ev' [] (Mapping.update pm' (replicate ?c (ga \<alpha>)) dbe') \<rho>' = (us', \<sigma>')"
    by fastforce
  have "fst (ev' [] (Mapping.update pm' (replicate ?c (ga \<alpha>)) dbe') \<rho>') =
      map g (fst (ev [] (Mapping.update pm (replicate ?c \<alpha>) dbe) \<rho>)) \<and>
    R (snd (ev [] (Mapping.update pm (replicate ?c \<alpha>) dbe) \<rho>))
      (snd (ev' [] (Mapping.update pm' (replicate ?c (ga \<alpha>)) dbe') \<rho>'))"
    by (rule prems(1)) (use sz\<rho> R in auto)
  then have us': "us' = map g us" and R\<sigma>: "R \<sigma> \<sigma>'"
    using e e' by simp_all
  have dr: "drop (i - (pR - length (map g rb))) (map g rb @ us') = map g (drop (i - (pR - length rb)) (rb @ us))"
    by (simp add: us' drop_map[symmetric])
  show ?case
  proof (cases "drop (i - (pR - length rb)) (rb @ us)")
    case Nil
    then have dr': "drop (i - (pR - length (map g rb))) (map g rb @ us') = []"
      using dr by simp
    have "ys = []" "\<alpha>s1 = \<alpha> # \<alpha>s" "lv = Some (i - (pR - length rb) - length (rb @ us), \<sigma>)"
      "s1 = (\<rho>, w, pR, tq, rb)"
      using prems(3) s1 e Nil by auto
    moreover have "ys' = []" "\<alpha>s1' = ga \<alpha> # map ga \<alpha>s"
      "lv' = Some (i - (pR - length rb) - length (rb @ us), \<sigma>')" "s1' = (\<rho>', w, pR, tq, map g rb)"
      using prems(4) s1' e' dr' us' by auto
    ultimately show ?thesis
      using R R\<sigma> by simp
  next
    case (Cons y r)
    obtain zs bs lv0 s2 where rec: "frz_loop sz ev pm dbe fl d po j (Suc i) \<alpha>s (\<rho>, w, pR, tq, rb) = (zs, bs, lv0, s2)"
      by (metis prod_cases4)
    obtain zs' bs' lv0' s2' where rec': "frz_loop sz' ev' pm' dbe' (ga fl) d po j (Suc i) (map ga \<alpha>s)
        (\<rho>', w, pR, tq, map g rb) = (zs', bs', lv0', s2')"
      by (metis prod_cases4)
    have IH': "zs' = map g zs \<and> bs' = map ga bs \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv0 lv0' \<and>
        frz_st_rel R g s2 s2'"
      by (rule IH[OF _ _ rec rec']) (use prems(1) sz\<rho> R in auto)
    have dr': "drop (i - (pR - length (map g rb))) (map g rb @ us') = g y # map g r"
      using dr[unfolded Cons] by simp
    have "ys = y # zs" "\<alpha>s1 = bs" "lv = lv0" "s1 = s2"
      using prems(3) s1 e Cons rec by auto
    moreover have "ys' = g y # zs'" "\<alpha>s1' = bs'" "lv' = lv0'" "s1' = s2'"
      using prems(4) s1' e' dr' rec' by auto
    ultimately show ?thesis
      using IH' by simp
  qed
qed

lemma frz_live_loop_rel:
  assumes ev: "\<And>\<psi> \<psi>' c X. sz \<psi> = sz (fst s) \<Longrightarrow> R \<psi> \<psi>' \<Longrightarrow> X \<in> insert fl (set \<alpha>s) \<Longrightarrow>
      fst (ev' [] (Mapping.update pm' (replicate c (ga X)) dbe') \<psi>') =
        map g (fst (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>)) \<and>
      R (snd (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>))
        (snd (ev' [] (Mapping.update pm' (replicate c (ga X)) dbe') \<psi>'))"
    and sz: "\<And>\<psi>1 \<psi>1' \<psi>2 \<psi>2'. R \<psi>1 \<psi>1' \<Longrightarrow> R \<psi>2 \<psi>2' \<Longrightarrow> sz \<psi>1 = sz \<psi>2 \<longleftrightarrow> sz' \<psi>1' = sz' \<psi>2'"
    and st: "frz_st_rel R g s s'"
    and L: "rel_option (\<lambda>(k, us, \<sigma>) (k', us', \<sigma>'). k' = k \<and> us' = map g us \<and> R \<sigma> \<sigma>') lr lr'"
    and r: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s1, lv, s1)"
    and r': "frz_live_loop sz' ev' pm' dbe' (ga fl) d po j i (map ga \<alpha>s) lr' s' = (ys', \<alpha>s1', lv', s1')"
  shows "ys' = map g ys \<and> \<alpha>s1' = map ga \<alpha>s1 \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv lv' \<and>
    frz_st_rel R g s1 s1'"
proof (cases lr)
  case None
  then have "lr' = None"
    using L by simp
  with None r r' have r0: "frz_loop sz ev pm dbe fl d po j i \<alpha>s s = (ys, \<alpha>s1, lv, s1)"
    and r0': "frz_loop sz' ev' pm' dbe' (ga fl) d po j i (map ga \<alpha>s) s' = (ys', \<alpha>s1', lv', s1')"
    by (simp_all add: frz_live_loop_def)
  show ?thesis
    by (rule frz_loop_rel[OF _ sz st r0 r0']) (rule ev, assumption+)
next
  case (Some x)
  then obtain k us \<sigma> where lr: "lr = Some (k, us, \<sigma>)"
    by (cases x) auto
  with L obtain \<sigma>' where lr': "lr' = Some (k, map g us, \<sigma>')" and R: "R \<sigma> \<sigma>'"
    by (cases lr') auto
  show ?thesis
  proof (cases "drop k us")
    case Nil
    have "frz_st_rel R g (frz_adv_st sz ev pm dbe fl d j i s) (frz_adv_st sz' ev' pm' dbe' (ga fl) d j i s')"
      by (rule frz_adv_st_rel[OF _ sz st]) (use ev in blast)
    then show ?thesis
      using r r' lr lr' R Nil by (auto simp: frz_live_loop_def drop_map)
  next
    case (Cons y r0)
    obtain zs bs lv0 s2 where rec: "frz_loop sz ev pm dbe fl d po j (Suc i) (tl \<alpha>s) s = (zs, bs, lv0, s2)"
      by (metis prod_cases4)
    obtain zs' bs' lv0' s2' where rec': "frz_loop sz' ev' pm' dbe' (ga fl) d po j (Suc i) (map ga (tl \<alpha>s)) s' =
        (zs', bs', lv0', s2')"
      by (metis prod_cases4)
    have IH': "zs' = map g zs \<and> bs' = map ga bs \<and> rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lv0 lv0' \<and>
        frz_st_rel R g s2 s2'"
      by (rule frz_loop_rel[OF _ sz st rec rec']) (rule ev, assumption+, cases \<alpha>s; auto)
    have "ys = y # zs" "\<alpha>s1 = bs" "lv = lv0" "s1 = s2"
      using r lr Cons rec by (auto simp: frz_live_loop_def)
    moreover have "ys' = g y # zs'" "\<alpha>s1' = bs'" "lv' = lv0'" "s1' = s2'"
      using r' lr' Cons rec' by (auto simp: frz_live_loop_def drop_map map_tl)
    ultimately show ?thesis
      using IH' by simp
  qed
qed

text \<open>A map of the states that commutes with the evaluation and keeps the size.\<close>

lemma frz_live_loop_map:
  assumes ev: "\<And>ts db \<psi>. sz \<psi> = sz (fst s) \<Longrightarrow> ev' ts db (f \<psi>) = apsnd f (ev ts db \<psi>)"
    and sz: "\<And>\<psi>. sz' (f \<psi>) = sz \<psi>"
    and r: "frz_live_loop sz ev pm dbe fl d po j i \<alpha>s lr s = (ys, \<alpha>s1, lv, s1)"
  shows "frz_live_loop sz' ev' pm dbe fl d po j i \<alpha>s (map_option (\<lambda>(k, us, \<sigma>). (k, us, f \<sigma>)) lr) (apfst f s) =
    (ys, \<alpha>s1, map_option (apsnd f) lv, apfst f s1)"
proof -
  obtain ys' \<alpha>s1' lv' s1' where r': "frz_live_loop sz' ev' pm dbe (id fl) d po j i (map id \<alpha>s)
      (map_option (\<lambda>(k, us, \<sigma>). (k, us, f \<sigma>)) lr) (apfst f s) = (ys', \<alpha>s1', lv', s1')"
    by (metis prod_cases4)
  have "ys' = map id ys \<and> \<alpha>s1' = map id \<alpha>s1 \<and>
      rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> \<sigma>' = f \<sigma>) lv lv' \<and> frz_st_rel (\<lambda>\<psi> \<psi>'. \<psi>' = f \<psi>) id s1 s1'"
  proof (rule frz_live_loop_rel[where R = "\<lambda>\<psi> \<psi>'. \<psi>' = f \<psi>" and g = id and ga = id, OF _ _ _ _ r r'])
    show "fst (ev' [] (Mapping.update pm (replicate c (id X)) dbe) \<psi>') =
        map id (fst (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>)) \<and>
      snd (ev' [] (Mapping.update pm (replicate c (id X)) dbe) \<psi>') =
        f (snd (ev [] (Mapping.update pm (replicate c X) dbe) \<psi>))"
      if "sz \<psi> = sz (fst s)" "\<psi>' = f \<psi>" for \<psi> \<psi>' c X
      using ev[OF that(1), of "[]" "Mapping.update pm (replicate c X) dbe"] that(2)
      by (cases "ev [] (Mapping.update pm (replicate c X) dbe) \<psi>") simp
    show "sz \<psi>1 = sz \<psi>2 \<longleftrightarrow> sz' \<psi>1' = sz' \<psi>2'" if "\<psi>1' = f \<psi>1" "\<psi>2' = f \<psi>2" for \<psi>1 \<psi>1' \<psi>2 \<psi>2'
      using that sz by simp
    show "frz_st_rel (\<lambda>\<psi> \<psi>'. \<psi>' = f \<psi>) id s (apfst f s)"
      by (cases s) simp
    show "rel_option (\<lambda>(k, us, \<sigma>) (k', us', \<sigma>'). k' = k \<and> us' = map id us \<and> \<sigma>' = f \<sigma>) lr
      (map_option (\<lambda>(k, us, \<sigma>). (k, us, f \<sigma>)) lr)"
      by (cases lr) auto
  qed
  then have "ys' = ys" "\<alpha>s1' = \<alpha>s1" "lv' = map_option (apsnd f) lv" "s1' = apfst f s1"
    by (cases lv; cases lv'; cases s1; cases s1'; auto)+
  then show ?thesis
    using r' by simp
qed

fun list_of_option :: "'a option \<Rightarrow> 'a list" where
  "list_of_option None = []"
| "list_of_option (Some x) = [x]"

fun eval_mtrm :: "mtrm \<Rightarrow> event_data \<Rightarrow> event_data table" where
  "eval_mtrm (MVar v) x = singleton_table x"
| "eval_mtrm (MConst c) x = (if c = x then unit_table else empty_table)"

lemma qtable_eval_mtrm:
  assumes "\<forall>x\<in>fv_trm t. x < n" 
    and "trm.is_Var t \<or> trm.is_Const t"
  shows "qtable (Formula.fv_trm_list t) R (\<lambda>v. Formula.eval_trm (val n (Formula.fv_trm_list t) v) t = x)
    (eval_mtrm (mtrm_of_trm t) x)"
  using assms unfolding qtable_iff table_def Formula.is_Var_def Formula.is_Const_def
  by (auto simp: singleton_table_def unit_table_def empty_table_def wf_tuple_def tup_get_Cons length_Suc_conv split: if_splits)

text \<open>The columns of a predicate's table.\<close>

definition pred_cols :: "Formula.trm list \<Rightarrow> nat list" where
  "pred_cols ts = fold (\<lambda>t cs. cols_union cs (Formula.fv_trm_list t)) ts []"

lemma fv_list_Pred: "Formula.fv_list (Formula.Pred e ts) = pred_cols ts"
  by (simp add: pred_cols_def)
type_synonym database = "(Formula.name \<times> nat, event_data table list) mapping"

context maux
begin

context
  fixes j :: nat
begin

text \<open>The tables of a formula bound to a predicate are read positionally, as the event tuples:
  @{const MLet}, @{const MFrz} and @{const MLetPast} reorder them from the formula's columns
  @{term cs} to @{term "[0..<m]"}.\<close>

function (sequential) meval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula \<Rightarrow>
    event_data table list \<times> ('msaux, 'muaux, 'mtaux) mformula" where
  "meval n ts db (MRel rel) = (replicate (length ts) rel, MRel rel)"
| "meval n ts db (MPred e tms mode) =
    ((case Mapping.lookup db (e, length tms) of
        None \<Rightarrow> replicate (length ts) {}
      | Some xs \<Rightarrow> (case mode of
          Copy \<Rightarrow> xs
        | Simple \<Rightarrow> xs
        | Match \<Rightarrow> map (\<lambda>X. tabulate_match (pred_cols tms) ` Option.these (match tms ` X)) xs)),
    MPred e tms mode)"
| "meval n ts db (MLet p m cs \<phi> \<psi>) =
    (let (xs, \<phi>) = meval m ts db \<phi>;
      (ys, \<psi>) = meval n ts (Mapping.update (p, m) (map (reorder [0..<m] cs) xs) db) \<psi>
    in (ys, MLet p m cs \<phi> \<psi>))"
| "meval n ts db (MFrz p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
    (let (xs, \<phi>) = meval m ts db \<phi>;
         db0 = Mapping.update (p, m) [] db;
         (zs0, \<psi>) = meval n ts db0 \<psi>;
         (rs, \<rho>) = meval n ts db0 \<rho>;
         (zs0_out, jfrz, fl, \<alpha>s, lr) =
           (let zs0_out = drop (jfrz - jpsi0) zs0;
                \<alpha>s0 = \<alpha>s @ map (reorder [0..<m] cs) xs;
                \<alpha>s1 = drop (jfrz - jphi + length zs0_out) \<alpha>s0
            in (zs0_out, jfrz + length zs0_out, frz_fill ng \<alpha>s0, \<alpha>s1,
              case lv of None \<Rightarrow> None | Some g \<Rightarrow>
                if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
                then Some (g, meval n ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
                else None));
         (ys, \<alpha>s', lv, \<rho>, w, pR, tq, rb) = frz_live_loop size (meval n) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
           fl d po j jfrz \<alpha>s lr (\<rho>, w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
             drop (min jfrz (pR + length rs) - (pR - length rb)) (rb @ rs))
     in (zs0_out @ ys, MFrz p m cs \<phi> \<psi> (jfrz + length ys) (jpsi0 + length zs0) (jphi + length xs) \<alpha>s' \<rho> w pR tq rb d po ng
       (frz_keep_lv (if po then None else lv) \<rho>L) (frz_keep_st (if po then None else lv) \<rho>L)))"
| "meval n ts db (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>r1 r2. bin_join A_\<phi> r1 pos A_\<psi> r2) (mbuf2_add xs ys buf)
    in (zs, MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf))"
| "meval n ts db (MLetPast p m cs \<phi> \<psi> i buf) =
    (let (xs, i, buf, \<phi>) = letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] cs)) (meval m ts db \<phi>))
           j i [] (list_of_option buf) (p, m) ts db \<phi>;
         (ys, \<psi>) = meval n ts (Mapping.update (p, m) xs db) \<psi>
    in (ys, MLetPast p m cs \<phi> \<psi> i buf))"
| "meval n ts db (MAndAssign cs \<phi> conf) =
    (let (xs, \<phi>) = meval n ts db \<phi> in
    (map (\<lambda>(r). (eval_assignment cs conf ` r)) xs, MAndAssign cs \<phi> conf))"
| "meval n ts db (MAndRel cs \<phi> conf) =
    (let (xs, \<phi>) = meval n ts db \<phi> in (map (\<lambda>(r). (Set.filter (eval_constraint cs conf) r)) xs, MAndRel cs \<phi> conf))"
| "meval n ts db (MAndTrigger V_\<phi> \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = (let
    (as, \<phi>) = meval n ts db \<phi>;
    (xs, \<phi>') = meval n ts db \<phi>';
    (ys, \<psi>') = meval n ts db \<psi>';
    ((zs_trigger, aux), buf2, nts) = mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
        let aux       = update_mtaux args t r1 r2 aux;
            (fv_z, z) = result_mtaux args aux
        in (zs @ [(fv_z, z)], aux)) ([], aux) (mbuf2_add xs ys buf2) (nts @ ts);
     \<comment> \<open>analogous to MAnd\<close>
    (zs, buf1) = mbuf2_take (\<lambda>r1 (V_trigger, r2).
        bin_join V_\<phi> r1 True V_trigger r2 \<comment> \<open>fix pos=True for the and join\<close>
    ) (mbuf2_add as zs_trigger buf1)
    in
    (zs, MAndTrigger V_\<phi> \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux)
)"
| "meval n ts db (MAnds cs A_pos A_neg L buf) =
    (let R = map (meval n ts db) L in
    let buf = mbufn_add (map fst R) buf in
    let (zs, buf) = mbufn_take (\<lambda>xs zs. zs @ [mmulti_join cs A_pos A_neg xs]) [] buf in
    (zs, MAnds cs A_pos A_neg (map snd R) buf))"
| "meval n ts db (MOr cs1 \<phi> cs2 \<psi> buf) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>(r1) (r2). (r1 \<union> reorder cs1 cs2 r2)) (mbuf2_add xs ys buf)
    in (zs, MOr cs1 \<phi> cs2 \<psi> buf))"
| "meval n ts db (MNeg \<phi>) =
    (let (xs, \<phi>) = meval n ts db \<phi> in (map (\<lambda>(r). (if r = empty_table then unit_table else empty_table)) xs, MNeg \<phi>))"
| "meval n ts db (MExists cs \<phi>) =
    (let (xs, \<phi>) = meval (Suc n) ts db \<phi> in (map (\<lambda>r. ex_proj cs ` r) xs, MExists cs \<phi>))"
| "meval n ts db (MAgg args \<phi>) =
    (let (xs, \<phi>) = meval (length (aggargs_tys args) + n) ts db \<phi> in (map (eval_aggargs args) xs, MAgg args \<phi>))"
| "meval n ts db (MPrev I \<phi> first buf nts) =
    (let (xs, \<phi>) = meval n ts db \<phi>
    in if first \<and> ts = [] then ([], MPrev I \<phi> True (buf @ xs) (nts @ ts))
    else let (zs, buf, nts) = mprev_next I (buf @ xs) (nts @ ts)
      in (if first then (empty_table) # zs else zs, MPrev I \<phi> False buf nts))"
| "meval n ts db (MNext I \<phi> first nts) =
    (let (xs, \<phi>) = meval n ts db \<phi>;
      (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
      (zs, _, nts) = mprev_next I xs (nts @ ts)
    in (zs, MNext I \<phi> first nts))"
| "meval n ts db (MSince args \<phi> \<psi> buf aux) =
    (let (xs, \<phi>) = meval (args_n args) ts db \<phi>; (ys, \<psi>) = meval (args_n args) ts db \<psi>;
      (zs, buf, aux) = eval_since args [] (mbuf2S_add xs ys ts buf) aux
    in (zs, MSince args \<phi> \<psi> buf aux))"
| "meval n ts db (MUntil args \<phi> \<psi> buf nts t aux) =
    (let (xs, \<phi>) = meval (args_n args) ts db \<phi>; (ys, \<psi>) = meval (args_n args) ts db \<psi>;
      (aux, buf, nt, nts') = mbuf2t_take (add_new_muaux args) aux (mbuf2_add xs ys buf) t (nts @ ts);
      (zs, aux) = eval_muaux args nt aux
    in (zs, MUntil args \<phi> \<psi> buf nts' nt aux))"
| "meval n ts db (MTrigger args \<phi> \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      ((zs, aux), buf, nts) = mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
        let aux       = update_mtaux args t r1 r2 aux;
            (fv_z, z) = result_mtaux args aux
        in (zs @ [(z)], aux)) ([], aux) (mbuf2_add xs ys buf) (nts @ ts)
    in (zs, MTrigger args \<phi> \<psi> buf nts aux))"
| "meval n ts db (MMatchP I cs dss mr mrs \<phi>s buf nts aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n ts db) \<phi>s);
      ((zs, aux), buf, _, nts) = mbufnt_take (\<lambda>rels t (zs, aux).
        let (z, aux) = update_matchP cs dss I mr mrs rels t aux
        in (zs @ [z], aux)) ([], aux) (mbufn_add xss buf) 0 (nts @ ts)
    in (zs, MMatchP I cs dss mr mrs \<phi>s buf nts aux))"
| "meval n ts db (MMatchF I cs dss mr mrs \<phi>s buf nts t aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n ts db) \<phi>s);
      (aux, buf, nt, nts') = mbufnt_take (update_matchF cs dss I mr mrs) aux (mbufn_add xss buf) t (nts @ ts);
      (zs, aux) = eval_matchF I mr nt aux
    in (zs, MMatchF I cs dss mr mrs \<phi>s buf nts' nt aux))"
| "meval n ts db (MTP mt i) = (map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) [i..<j], MTP mt j)"
| "meval n ts db (MTS mt) = (map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) ts, MTS mt)"  by pat_completeness (simp_all only: prod.inject mformula.inject mformula.distinct simp_thms)

lemma size_list_cong: "xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> size_list f xs = size_list g ys"
  by (induct xs arbitrary: ys) auto

lemma map_split_map: "map_split f (map g xs) = map_split (f o g) xs"
  by (induct xs) auto

lemma map_split_eq_Pair_iff: "map_split f xs = (ys, zs) \<longleftrightarrow> ys = map (fst o f) xs \<and> zs = map (snd o f) xs"
  by (induct xs arbitrary: ys zs) (auto split: prod.splits)

lemma
  psize_snd_meval: "meval_dom (n, t, db, \<phi>) \<Longrightarrow> size (snd (meval n t db \<phi>)) = size \<phi>"
proof (induct rule: meval.pinduct)
  case (6 n ts db p m cs \<phi> \<psi> i buf) \<comment> \<open>\<^const>\<open>MLetPast\<close>\<close>
  let ?eval = "\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] cs)) (meval m ts db \<phi>)"
  obtain xs i' buf' \<phi>' where lp: "letpast_meval0 ?eval j i [] (list_of_option buf) (p, m) ts db \<phi> = (xs, i', buf', \<phi>')"
    by (metis prod_cases4)
  have "size (snd (snd (snd (letpast_meval0 ?eval j i [] (list_of_option buf) (p, m) ts db \<phi>)))) = size \<phi>"
    using 6(2) by (intro size_letpast_meval) simp
  then have size_\<phi>': "size \<phi>' = size \<phi>"
    by (simp add: lp)
  obtain ys \<psi>' where \<psi>': "meval n ts (Mapping.update (p, m) xs db) \<psi> = (ys, \<psi>')"
    by fastforce
  have size_\<psi>': "size \<psi>' = size \<psi>"
    using 6(3)[OF lp[symmetric] refl refl refl] \<psi>' by simp
  show ?case
    using size_\<phi>' size_\<psi>' by (simp add: meval.psimps(6)[OF 6(1)] lp \<psi>')next
  case (15 n ts db I \<phi> first buf nts) \<comment> \<open>\<^const>\<open>MPrev\<close>\<close>
  obtain xs \<phi>' where \<phi>': "meval n ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "mprev_next I (buf @ xs) (nts @ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "size \<phi>' = size \<phi>"
    using 15(2) \<phi>' by simp
  then show ?case
    by (simp add: meval.psimps(15)[OF 15(1)] \<phi>' mp)
next
  case (4 n ts db p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) \<comment> \<open>\<^const>\<open>MFrz\<close>\<close>
  let ?db0 = "Mapping.update (p, m) [] db"
  obtain xs \<phi>' where \<phi>': "meval m ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs0 \<psi>' where \<psi>': "meval n ts ?db0 \<psi> = (zs0, \<psi>')"
    by fastforce
  obtain rs \<rho>' where \<rho>': "meval n ts ?db0 \<rho> = (rs, \<rho>')"
    by fastforce
  have s\<phi>: "size \<phi>' = size \<phi>"
    using 4(2) \<phi>' by simp
  have s\<psi>: "size \<psi>' = size \<psi>"
    using 4(3)[OF \<phi>'[symmetric] refl refl] \<psi>' by simp
  have s\<rho>: "size \<rho>' = size \<rho>"
    using 4(4)[OF \<phi>'[symmetric] refl refl \<psi>'[symmetric] refl] \<rho>' by simp
  obtain zo jf fl as lr where st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s0 = \<alpha>s @ map (reorder [0..<m] cs) xs;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) \<alpha>s0
     in (zs0_out, jfrz + length zs0_out, frz_fill ng \<alpha>s0, \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, meval n ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (zo, jf, fl, as, lr)"
    by (rule prod_cases5)
  obtain ys as' lv' s' where lp0: "frz_live_loop size (meval n) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
      fl d po j jf as lr (\<rho>', w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
        drop (min jf (pR + length rs) - (pR - length rb)) (rb @ rs)) = (ys, as', lv', s')"
    by (metis prod_cases4)
  obtain \<rho>'' w' pR' tq' rb' where s': "s' = (\<rho>'', w', pR', tq', rb')"
    by (metis prod_cases5)
  have s\<rho>'': "size \<rho>'' = size \<rho>"
    using frz_live_loop_size[OF lp0] s\<rho> s' by simp
  have "snd (meval n ts db (MFrz p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)) =
    MFrz p m cs \<phi>' \<psi>' (jf + length ys) (jpsi0 + length zs0) (jphi + length xs) as' \<rho>'' w' pR' tq' rb' d po ng      (frz_keep_lv (if po then None else lv') \<rho>L) (frz_keep_st (if po then None else lv') \<rho>L)"
    by (simp only: meval.psimps(4)[OF 4(1)] \<phi>' \<psi>' \<rho>' st lp0[unfolded s'] Let_def[where s = ?db0]
        Let_def[where s = "(xs, \<phi>')"] Let_def[where s = "(zs0, \<psi>')"] Let_def[where s = "(rs, \<rho>')"]
        Let_def[where s = "(zo, jf, fl, as, lr)"] Let_def[where s = "(ys, as', lv', \<rho>'', w', pR', tq', rb')"]
        prod.case snd_conv)
  then show ?case
    using s\<phi> s\<psi> s\<rho>'' by simp
  \<comment> \<open>in all other cases, the claim follows directly from the IHs for the subformulas\<close>
qed (auto simp only: prod.inject meval.psimps Let_def snd_conv mformula.size map_split_map id_o map_split_eq_Pair_iff size_list_map o_apply size_frz_keep_st cong: size_list_cong split: prod.splits)

lemma total_meval: "All meval_dom"
proof (relation "measure (\<lambda>(_, _, _, \<phi>). size \<phi>)", goal_cases)
  text \<open>The live copy is a subterm.  The copies and the window's moves evaluate a replay base of
    the size of the one the node holds (@{const frz_live_loop}): left to the automation below, this
    case takes long, since the many equations of the body's @{text let}s are tried in both
    orientations.

    The equation for @{const MFrz} computes the values each stage needs inside the bound term of
    that stage's recursive call and returns them as a tuple, so that only a few pair @{text let}s
    follow the calls.  With the values bound one by one at the top level, the definition takes
    minutes instead of seconds: the function package's congruence steps unify over the whole
    chain of @{text let}s that follows a call.\<close>
  case 7 \<comment> \<open>the live copy, a subterm\<close>
  then show ?case
    by simp
next
  case (8 n ts db p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L x xa y xb xc xd ya xe xf yb xg xh
    yc xi yd xj yca xk ycb tsa dba \<psi>')
  have "size yb = size \<rho>"
    using psize_snd_meval[of n ts xb \<rho>] 8 by (metis snd_conv)
  then show ?case
    using 8 by simp
qed (auto simp: termination_simp dest!: psize_snd_meval dest: sym)
lemmas size_snd_meval = psize_snd_meval[OF total_meval[THEN spec]]

termination meval
  by (rule total_meval)

end (* fixes j *)

lemma mformula_induct[case_names MRel MPred MLet MFrz MLetPast 
    MAnd MAndAssign MAndRel MAndTrigger MAnds MOr MNeg
    MExists MAgg MPrev MNext MSince MUntil MTrigger MMatchP MMatchF MTP MTS]:
  "(\<And>rel. P (MRel rel)) \<Longrightarrow>
   (\<And>e ts mode. P (MPred e ts mode)) \<Longrightarrow>
   (\<And>p m cs \<phi> \<psi>. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MLet p m cs \<phi> \<psi>)) \<Longrightarrow>
   (\<And>p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L. P \<phi> \<Longrightarrow> (\<And>\<psi>'. size \<psi>' = size \<psi> \<Longrightarrow> P \<psi>') \<Longrightarrow>
     (\<And>\<rho>'. size \<rho>' = size \<rho> \<Longrightarrow> P \<rho>') \<Longrightarrow> P \<rho>L \<Longrightarrow> P (MFrz p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)) \<Longrightarrow>
   (\<And>p m cs \<phi> \<psi> i buf. (\<And>\<phi>'. size \<phi>' = size \<phi> \<Longrightarrow> P \<phi>') \<Longrightarrow> P \<psi> \<Longrightarrow> P (MLetPast p m cs \<phi> \<psi> i buf)) \<Longrightarrow>
   (\<And>A_\<phi> \<phi> pos A_\<psi> \<psi> buf. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf)) \<Longrightarrow>
   (\<And>cs \<phi> conf. P \<phi> \<Longrightarrow> P (MAndAssign cs \<phi> conf)) \<Longrightarrow>
   (\<And>cs \<phi> conf. P \<phi> \<Longrightarrow> P (MAndRel cs \<phi> conf)) \<Longrightarrow>
   (\<And>args A_\<phi> \<phi> \<phi>' \<psi>' tbuf buf nts aux. P \<phi> \<Longrightarrow> P \<phi>' \<Longrightarrow> P \<psi>' \<Longrightarrow> P (MAndTrigger A_\<phi> \<phi> tbuf args \<phi>' \<psi>' buf nts aux)) \<Longrightarrow>
   (\<And>cs A_pos A_neg L buf. (\<And>\<phi>. \<phi> \<in> set L \<Longrightarrow> P \<phi>) \<Longrightarrow> P (MAnds cs A_pos A_neg L buf)) \<Longrightarrow>
   (\<And>cs1 \<phi> cs2 \<psi> buf. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MOr cs1 \<phi> cs2 \<psi> buf)) \<Longrightarrow>
   (\<And>\<phi>. P \<phi> \<Longrightarrow> P (MNeg \<phi>)) \<Longrightarrow>
   (\<And>cs \<phi>. P \<phi> \<Longrightarrow> P (MExists cs \<phi>)) \<Longrightarrow>
   (\<And>args \<phi>. P \<phi> \<Longrightarrow> P (MAgg args \<phi>)) \<Longrightarrow>
   (\<And>I \<phi> first buf nts. P \<phi> \<Longrightarrow> P (MPrev I \<phi> first buf nts)) \<Longrightarrow>
   (\<And>I \<phi> first nts. P \<phi> \<Longrightarrow> P (MNext I \<phi> first nts)) \<Longrightarrow>
   (\<And>args \<phi> \<psi> buf aux. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MSince args \<phi> \<psi> buf aux)) \<Longrightarrow>
   (\<And>args \<phi> \<psi> buf nts t aux. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MUntil args \<phi> \<psi> buf nts t aux)) \<Longrightarrow>
   (\<And>args \<phi> \<psi> buf nts aux. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MTrigger args \<phi> \<psi> buf nts aux)) \<Longrightarrow>
   (\<And>I cs dss mr mrs \<phi>s buf nts aux. (\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> P \<phi>) \<Longrightarrow> P (MMatchP I cs dss mr mrs \<phi>s buf nts aux)) \<Longrightarrow>
   (\<And>I cs dss mr mrs \<phi>s buf nts t aux. (\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> P \<phi>) \<Longrightarrow> P (MMatchF I cs dss mr mrs \<phi>s buf nts t aux)) \<Longrightarrow>
   (\<And>mt i. P (MTP mt i)) \<Longrightarrow>
   (\<And>mt. P (MTS mt)) \<Longrightarrow>
   P mf"
proof (induct "size mf" arbitrary: mf rule: less_induct)
  case less
  have IH: "P \<psi>" if "size \<psi> < size mf" for \<psi>
    using that less.prems by (rule less.hyps)
  have IH_set: "P \<phi>" if "\<phi> \<in> set \<phi>s" "size_list size \<phi>s < size mf" for \<phi> \<phi>s
    using size_list_estimation'[OF that(1), of "size \<phi>" size] that(2) by (intro IH) simp
  show ?case
  proof (cases mf)
    case (MRel rel)
    show ?thesis unfolding MRel by (rule less.prems(1))
  next
    case (MPred e ts mode)
    show ?thesis unfolding MPred by (rule less.prems(2))
  next
    case (MLet p m cs \<phi> \<psi>)
    show ?thesis unfolding MLet by (rule less.prems(3)) (rule IH, simp add: MLet)+
  next
    case (MFrz p m cs \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)
    show ?thesis unfolding MFrz by (rule less.prems(4)) (rule IH, simp add: MFrz)+
  next
    case (MLetPast p m cs \<phi> \<psi> i buf)
    show ?thesis unfolding MLetPast by (rule less.prems(5)) (rule IH, simp add: MLetPast)+
  next
    case (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf)
    show ?thesis unfolding MAnd by (rule less.prems(6)) (rule IH, simp add: MAnd)+
  next
    case (MAndAssign cs \<phi> conf)
    show ?thesis unfolding MAndAssign by (rule less.prems(7)) (rule IH, simp add: MAndAssign)
  next
    case (MAndRel cs \<phi> conf)
    show ?thesis unfolding MAndRel by (rule less.prems(8)) (rule IH, simp add: MAndRel)
  next
    case (MAndTrigger A_\<phi> \<phi> tbuf args \<phi>' \<psi>' buf nts aux)
    show ?thesis unfolding MAndTrigger by (rule less.prems(9)) (rule IH, simp add: MAndTrigger)+
  next
    case (MAnds cs A_pos A_neg L buf)
    show ?thesis unfolding MAnds by (rule less.prems(10)) (rule IH_set, assumption, simp add: MAnds)
  next
    case (MOr cs1 \<phi> cs2 \<psi> buf)
    show ?thesis unfolding MOr by (rule less.prems(11)) (rule IH, simp add: MOr)+
  next
    case (MNeg \<phi>)
    show ?thesis unfolding MNeg by (rule less.prems(12)) (rule IH, simp add: MNeg)
  next
    case (MExists cs \<phi>)
    show ?thesis unfolding MExists by (rule less.prems(13)) (rule IH, simp add: MExists)
  next
    case (MAgg args \<phi>)
    show ?thesis unfolding MAgg by (rule less.prems(14)) (rule IH, simp add: MAgg)
  next
    case (MPrev I \<phi> first buf nts)
    show ?thesis unfolding MPrev by (rule less.prems(15)) (rule IH, simp add: MPrev)
  next
    case (MNext I \<phi> first nts)
    show ?thesis unfolding MNext by (rule less.prems(16)) (rule IH, simp add: MNext)
  next
    case (MSince args \<phi> \<psi> buf aux)
    show ?thesis unfolding MSince by (rule less.prems(17)) (rule IH, simp add: MSince)+
  next
    case (MUntil args \<phi> \<psi> buf nts t aux)
    show ?thesis unfolding MUntil by (rule less.prems(18)) (rule IH, simp add: MUntil)+
  next
    case (MTrigger args \<phi> \<psi> buf nts aux)
    show ?thesis unfolding MTrigger by (rule less.prems(19)) (rule IH, simp add: MTrigger)+
  next
    case (MMatchP I cs dss mr mrs \<phi>s buf nts aux)
    show ?thesis unfolding MMatchP by (rule less.prems(20)) (rule IH_set, assumption, simp add: MMatchP)
  next
    case (MMatchF I cs dss mr mrs \<phi>s buf nts t aux)
    show ?thesis unfolding MMatchF by (rule less.prems(21)) (rule IH_set, assumption, simp add: MMatchF)
  next
    case (MTP mt i)
    show ?thesis unfolding MTP by (rule less.prems(22))
  next
    case (MTS mt)
    show ?thesis unfolding MTS by (rule less.prems(23))
  qed
qed

definition "letpast_meval m cs j =
  letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] cs)) (meval j m ts db \<phi>)) j"

lemma letpast_meval_code[code]:
  "letpast_meval m cs j i ys xs p ts db \<phi> =
     (let (ys', \<phi>') = apfst (map (reorder [0..<m] cs)) (meval j m ts (Mapping.update p xs db) \<phi>) in
       (case ys' of
         [] \<Rightarrow> (ys @ ys', i + length xs, None, \<phi>')
       | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j then (ys @ ys', i + length xs, Some y, \<phi>')
           else letpast_meval m cs j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))"
proof -
  obtain ys' \<phi>' where ev: "meval j m ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have "size \<phi>' = size \<phi>"
    using size_snd_meval[of j m ts "Mapping.update p xs db" \<phi>] ev by simp
  then show ?thesis
    unfolding letpast_meval_def by (subst (1) letpast_meval0.simps) (simp add: ev)
qed

declare meval.simps[simp del]
lemmas meval_simps[simp] = meval.simps[folded letpast_meval_def]

lemma letpast_meval_induct[case_names step]:
  assumes step:
    "\<And>i ys xs p ts db \<phi>.
      (\<And>ys' \<phi>'.
          (ys', \<phi>') = apfst (map (reorder [0..<m] cs)) (meval j m ts (Mapping.update p xs db) \<phi>) \<Longrightarrow>
          ys' \<noteq> [] \<Longrightarrow>
          Suc (i + length xs) < j \<Longrightarrow>
          P (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>') \<Longrightarrow>
      P i ys xs p ts db \<phi>"
  shows "P i ys xs p ts db \<phi>"
proof (induction eval\<equiv>"\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] cs)) (meval j m ts db \<phi>)" j\<equiv>j i ys xs p ts db \<phi>
    rule: letpast_meval0.induct)
  case (1 i ys xs p ts db \<phi>)
  show ?case
  proof (rule step)
    fix ys' \<phi>'
    assume ev: "(ys', \<phi>') = apfst (map (reorder [0..<m] cs)) (meval j m ts (Mapping.update p xs db) \<phi>)"
      and ne: "ys' \<noteq> []" and lt: "Suc (i + length xs) < j"
    from ne obtain y ys'' where ys': "ys' = y # ys''"
      by (auto simp: neq_Nil_conv)
    have "size \<phi>' = size \<phi>"
      using size_snd_meval[of j m ts "Mapping.update p xs db" \<phi>] ev[symmetric]
      by (cases "meval j m ts (Mapping.update p xs db) \<phi>") simp
    then show "P (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>'"
      using 1[OF ev refl _ ys'] lt by simp
  qed
qed

lemma letpast_meval_ys: 
  "(ys', i', buf', \<phi>f) = letpast_meval m cs j i ys xs p ts db \<phi> \<Longrightarrow> \<exists> zs. ys' = ys@zs"
proof (induction i ys xs p ts db \<phi> arbitrary: i' buf' ys' \<phi>f rule: letpast_meval_induct[where m=m and cs=cs and j=j])
  case (step i ys xs p ts db \<phi>)
  obtain zs \<phi>' where ev: "apfst (map (reorder [0..<m] cs)) (meval j m ts (Mapping.update p xs db) \<phi>) = (zs, \<phi>')"
    by fastforce
  note code = letpast_meval_code[of m cs j i ys xs p ts db \<phi>]
  show ?case
  proof (cases zs)
    case Nil
    then show ?thesis
      using step.prems ev by (simp add: code)
  next
    case (Cons y zs')
    show ?thesis
    proof (cases "j \<le> Suc (i + length xs)")
      case True
      then show ?thesis
        using step.prems ev Cons by (simp add: code)
    next
      case False
      then have "(ys', i', buf', \<phi>f) =
        letpast_meval m cs j (i + length xs) (ys @ zs) zs p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>'"
        using step.prems ev Cons by (simp add: code)
      moreover have "zs \<noteq> []" "Suc (i + length xs) < j"
        using Cons False by simp_all
      ultimately obtain zs'' where "ys' = (ys @ zs) @ zs''"
        using step.IH[OF ev[symmetric]] by blast
      then show ?thesis
        by simp
    qed
  qed
qed
end (* maux *)

definition (in maux) mstep :: "database \<times> ts \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list \<times> ('msaux, 'muaux, 'mtaux) mstate" where
  "mstep tdb st =
    (case meval (mstate_j st + 1) (mstate_n st) [snd tdb] (fst tdb) (mstate_m st) of
      (xs, m) \<Rightarrow> (List.enumerate (mstate_i st) (zip (mstate_t st @ [snd tdb]) xs),
        \<lparr> mstate_i = mstate_i st + length xs,
          mstate_j = mstate_j st + 1,
          mstate_m = m,
          mstate_n = mstate_n st,
          mstate_t = drop (length xs) (mstate_t st @ [snd tdb]) \<rparr>))"

lift_definition mk_db :: "(Formula.name \<times> event_data list) set \<Rightarrow> database" is
  "\<lambda>X (p, n). (if (\<exists>ts. (p, ts) \<in> X \<and> n = length ts) 
    then Some [{ts. (p, ts) \<in> X \<and> n = length ts}] 
    else None)" .

context maux
begin

primrec msteps0 where
  "msteps0 [] st = ([], st)"
| "msteps0 (tdb # \<pi>) st =
    (let (V', st') = mstep (apfst mk_db tdb) st; (V'', st'') = msteps0 \<pi> st' in (V' @ V'', st''))"

primrec msteps0_stateless where
  "msteps0_stateless [] st = []"
| "msteps0_stateless (tdb # \<pi>) st = (let (V', st') = mstep (apfst mk_db tdb) st in V' @ msteps0_stateless \<pi> st')"

lemma msteps0_msteps0_stateless: "fst (msteps0 w st) = msteps0_stateless w st"
  by (induct w arbitrary: st) (auto simp: split_beta)

lift_definition msteps :: "Formula.prefix \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate 
  \<Rightarrow> (nat \<times> ts \<times> event_data table) list \<times> ('msaux, 'muaux, 'mtaux) mstate"
  is msteps0 .

lift_definition msteps_stateless :: "Formula.prefix \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate 
  \<Rightarrow> (nat \<times> ts \<times> event_data table) list"
  is msteps0_stateless .

lemma msteps_msteps_stateless: "fst (msteps w st) = msteps_stateless w st"
  by transfer (rule msteps0_msteps0_stateless)

lemma msteps0_snoc: "msteps0 (\<pi> @ [tdb]) st =
   (let (V', st') = msteps0 \<pi> st; (V'', st'') = mstep (apfst mk_db tdb) st' in (V' @ V'', st''))"
  by (induct \<pi> arbitrary: st) (auto split: prod.splits)

lemma msteps_psnoc: "last_ts \<pi> \<le> snd tdb \<Longrightarrow> msteps (psnoc \<pi> tdb) st =
   (let (V', st') = msteps \<pi> st; (V'', st'') = mstep (apfst mk_db tdb) st' in (V' @ V'', st''))"
  by transfer' (auto simp: msteps0_snoc split: list.splits prod.splits if_splits)

definition monitor where
  "monitor \<phi> \<pi> = msteps_stateless \<pi> (minit_safe \<phi>)"

end (* maux *)


(*<*)
end
(*>*)
