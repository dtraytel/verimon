(*<*)
theory Multiway
  imports
    Safety
begin
(*>*)

unbundle MFODL_notation \<comment> \<open> enable notation \<close>


subsection \<open>Translation to n-ary conjunction\<close>

fun get_and_list :: "'t Formula.formula \<Rightarrow> 't Formula.formula list" where
  "get_and_list (\<And>\<^sub>F l) = (if l = [] then [\<And>\<^sub>F l] else l)"
| "get_and_list \<phi> = [\<phi>]"

lemma get_and_list_eventually [simp]: 
  "get_and_list (Formula.eventually I \<phi>) = [Formula.eventually I \<phi>]"
  unfolding Formula.eventually_def
  by simp

lemma get_and_list_once [simp]: 
  "get_and_list (once I \<phi>) = [once I \<phi>]"
  unfolding once_def
  by simp

lemma fv_get_and: "(\<Union>x\<in>(set (get_and_list \<phi>)). Formula.fvi b x) = Formula.fvi b \<phi>"
  by (induction \<phi> rule: get_and_list.induct) simp_all

lemma safe_remove_negI: "safe_formula \<phi> \<Longrightarrow> safe_formula (remove_neg \<phi>)"
  by (cases \<phi>) auto

lemma safe_get_and: "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) 
    (auto simp: safe_neg_def list_all_iff intro: safe_remove_negI)

lemma sat_get_and: "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> list_all (Formula.sat \<sigma> V v i) (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: list_all_iff)

lemma safe_letpast_get_and: "\<Squnion>(safe_letpast p ` set (get_and_list \<phi>)) = safe_letpast p \<phi>"
  by (induction \<phi> rule: get_and_list.induct) (simp_all flip: bot_rec_safety_def)

lemma not_contains_pred_get_and: "\<And>x.\<not> contains_pred p \<phi> \<Longrightarrow> x \<in> set (get_and_list \<phi>) 
  \<Longrightarrow> \<not> contains_pred p x"
  by (induction \<phi> rule: get_and_list.induct) (auto split: if_splits)

lemma get_and_nonempty[simp]: "get_and_list \<phi> \<noteq> []"
  by (induction \<phi>) auto

lemma future_bounded_get_and:
  "list_all Safety.future_bounded (get_and_list \<phi>) = Safety.future_bounded \<phi>"
  by (induction \<phi>) simp_all

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed auto

function (sequential) convert_multiway :: "'t Formula.formula \<Rightarrow> 't Formula.formula" 
  where "convert_multiway (Formula.Pred p ts) = (Formula.Pred p ts)"
  | "convert_multiway (Formula.Eq t u) = (Formula.Eq t u)"
  | "convert_multiway (Formula.Less t u) = (Formula.Less t u)"
  | "convert_multiway (Formula.LessEq t u) = (Formula.LessEq t u)"
  | "convert_multiway (Formula.Let p \<phi> \<psi>) = Formula.Let p (convert_multiway \<phi>) (convert_multiway \<psi>)"
  | "convert_multiway (Formula.Frz p \<phi> \<psi>) = Formula.Frz p (convert_multiway \<phi>) (convert_multiway \<psi>)"
  | "convert_multiway (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (convert_multiway \<phi>) (convert_multiway \<psi>)"
  | "convert_multiway (\<not>\<^sub>F \<phi>) = \<not>\<^sub>F (convert_multiway \<phi>)"
  | "convert_multiway (\<phi> \<or>\<^sub>F \<psi>) = (convert_multiway \<phi>) \<or>\<^sub>F (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<and>\<^sub>F \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
        (convert_multiway \<phi>) \<and>\<^sub>F \<psi>
      else if safe_formula \<psi> then
         \<And>\<^sub>F (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway \<psi>))
      else if is_constraint \<psi> then
         (convert_multiway \<phi>) \<and>\<^sub>F \<psi>
      else if (case \<psi> of (\<phi>' \<^bold>T I \<psi>') \<Rightarrow> True | _ \<Rightarrow> False) then
         (convert_multiway \<phi>) \<and>\<^sub>F (convert_multiway \<psi>)
      else if (case \<psi> of (\<phi>' \<^bold>R I \<psi>') \<Rightarrow> True | _ \<Rightarrow> False) then (
         case \<psi> of (\<phi>' \<^bold>R I \<psi>') \<Rightarrow>
           if mem I 0 then
             (convert_multiway \<phi>) \<and>\<^sub>F (convert_multiway \<psi>)
           else
             convert_multiway (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      )
      else \<And>\<^sub>F (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>)))"
  | "convert_multiway (\<And>\<^sub>F \<phi>s) = \<And>\<^sub>F (map convert_multiway \<phi>s)"
  | "convert_multiway (\<exists>\<^sub>F:t. \<phi>) = \<exists>\<^sub>F:t. (convert_multiway \<phi>)"
  | "convert_multiway (Formula.Agg y \<omega> b f \<phi>) = Formula.Agg y \<omega> b f (convert_multiway \<phi>)"
  | "convert_multiway (\<^bold>Y I \<phi>) = \<^bold>Y I (convert_multiway \<phi>)"
  | "convert_multiway (\<^bold>X I \<phi>) = \<^bold>X I (convert_multiway \<phi>)"
  | "convert_multiway (\<phi> \<^bold>S I \<psi>) = (convert_multiway \<phi>) \<^bold>S I (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<^bold>U I \<psi>) = (convert_multiway \<phi>) \<^bold>U I (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<^bold>T I \<psi>) = (convert_multiway \<phi>) \<^bold>T I (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<^bold>R I \<psi>) = (
      if mem I 0 then
        (convert_multiway (\<psi> \<and>\<^sub>F \<phi>)) \<^bold>R I (convert_multiway \<psi>)
      else (
        convert_multiway (release_safe_bounded \<phi> I \<psi>)
      )
    )"
  | "convert_multiway (Formula.MatchP I r) = Formula.MatchP I (Regex.map_regex convert_multiway r)"
  | "convert_multiway (Formula.MatchF I r) = Formula.MatchF I (Regex.map_regex convert_multiway r)"
  | "convert_multiway (Formula.TP t) = Formula.TP t"
  | "convert_multiway (Formula.TS t) = Formula.TS t"
  by pat_completeness auto
termination
proof (relation "measure size'", simp_all only: in_measure size'_Or,
    simp_all add: size'_release_aux, goal_cases Ands R MatchP MatchF)
  case (Ands \<phi>s \<phi>)
  then show ?case
    using sum_list_mem_leq[of \<phi> \<phi>s size']
    by simp
next
  case (R I \<psi> \<phi>)
  then show ?case
    by (simp split: formula.splits)
next
  case (MatchP r \<phi>)
  then show ?case
    using regex_atms_size'[of \<phi> r]
    by simp
next
  case (MatchF r \<phi>)
  then show ?case
    using regex_atms_size'[of \<phi> r]
    by simp
qed

lemma convert_multiway_TT [simp]: 
  "convert_multiway Formula.TT = Formula.TT"
  by (simp add: Formula.TT_def)

lemma convert_multiway_once [simp]: 
  "convert_multiway (once I \<psi>') = once I (convert_multiway \<psi>')"
  unfolding once_def
  by simp

lemma convert_multiway_eventually [simp]: 
  "convert_multiway (Formula.eventually I \<psi>') = Formula.eventually I (convert_multiway \<psi>')"
  unfolding Formula.eventually_def
  by simp

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex convert_multiway"


subsection \<open> convert multiway and fv \<close>

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (\<And>\<^sub>F l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (\<And>\<^sub>F l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma fv_convert_multiway_TT[simp]: "Formula.fvi b (convert_multiway Formula.TT) = {}"
  unfolding Formula.TT_def Formula.FF_def
  by auto

lemma fv_convert_multiway: "Formula.fvi b (convert_multiway \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: convert_multiway.induct)
next
  case (10 \<phi> \<psi>)
  show ?case
  proof (cases "safe_assignment (fv \<phi>) \<psi>")
    case True
    then show ?thesis
      using 10(1)[of b] by simp
  next
    case not_assign: False
    show ?thesis
    proof (cases "safe_formula \<psi>")
      case True
      then show ?thesis
        using not_assign 10(2,3)[of b] by (simp add: fv_get_and)
    next
      case not_safe: False
      show ?thesis
      proof (cases "is_constraint \<psi>")
        case True
        then show ?thesis
          using not_assign not_safe 10(4)[of b] by simp
      next
        case not_constraint: False
        note not_sc = not_assign not_safe not_constraint
        consider (Trigger) \<phi>' I \<psi>' where "\<psi> = \<phi>' \<^bold>T I \<psi>'"
          | (Release) \<phi>' I \<psi>' where "\<psi> = \<phi>' \<^bold>R I \<psi>'"
          | (Other) "\<not> (case \<psi> of \<phi>' \<^bold>T I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False)"
            "\<not> (case \<psi> of \<phi>' \<^bold>R I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False)"
          by (cases \<psi>) auto
        then show ?thesis
        proof cases
          case Trigger
          then show ?thesis
            using not_sc 10(5,6)[of b] by simp
        next
          case (Release \<phi>' I \<psi>')
          show ?thesis
          proof (cases "mem I 0")
            case True
            then show ?thesis
              using Release not_sc 10(7,8)[of \<phi>' I \<psi>' b]
              by (simp del: safe_formula.simps)
          next
            case False
            then show ?thesis
              using Release not_sc 10(9)[of \<phi>' I \<psi>' b] by simp
          qed
        next
          case Other
          then have "convert_multiway (\<phi> \<and>\<^sub>F \<psi>)
            = \<And>\<^sub>F (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>))"
            using not_sc by simp
          then show ?thesis
            using Other not_sc 10(10,11)[of b] by (simp add: fv_get_and sup_commute)
        qed
      qed
    qed
  qed
next
  case (19 \<phi> I \<psi>)
  then show ?case
    by (cases "mem I 0") auto
qed (simp_all add: fv_regex_alt regex.set_map)

lemma nfv_convert_multiway: "Formula.nfv (convert_multiway \<phi>) = Formula.nfv \<phi>"
  unfolding Formula.nfv_def by (auto simp: fv_convert_multiway)


subsection \<open> convert multiway and safety \<close>

lemma pred_cmultiway_conjD: "contains_pred p (convert_multiway (\<phi> \<and>\<^sub>F \<psi>)) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway \<psi>)
  \<Longrightarrow> contains_pred p (convert_multiway \<phi>)"
proof -
  \<comment> \<open>all cases of @{const convert_multiway} on a conjunction, except bounded release\<close>
  have main: "contains_pred p (convert_multiway \<phi>)"
    if cp: "contains_pred p (convert_multiway (\<phi> \<and>\<^sub>F \<chi>))"
      and ncp: "\<not> contains_pred p (convert_multiway \<chi>)"
      and rel: "\<And>\<phi>' I \<psi>'. \<chi> = \<phi>' \<^bold>R I \<psi>' \<Longrightarrow> mem I 0"
    for \<chi>
  proof (cases "safe_assignment (fv \<phi>) \<chi>")
    case True
    then have "\<not> contains_pred p \<chi>"
      by (auto simp: safe_assignment_iff)
    with True cp show ?thesis
      by simp
  next
    case not_assign: False
    show ?thesis
    proof (cases "safe_formula \<chi>")
      case True
      with not_assign cp obtain x where "contains_pred p x"
        "x \<in> set (get_and_list (convert_multiway \<phi>)) \<union> set (get_and_list (convert_multiway \<chi>))"
        by auto
      with ncp show ?thesis
        using not_contains_pred_get_and by blast
    next
      case not_safe: False
      show ?thesis
      proof (cases "is_constraint \<chi>")
        case True
        then have "\<not> contains_pred p \<chi>"
          by (auto simp: is_constraint_iff)
        with True not_assign not_safe cp show ?thesis
          by simp
      next
        case False
        with not_assign not_safe rel
        have "convert_multiway (\<phi> \<and>\<^sub>F \<chi>) = convert_multiway \<phi> \<and>\<^sub>F convert_multiway \<chi>
          \<or> convert_multiway (\<phi> \<and>\<^sub>F \<chi>) = \<And>\<^sub>F (convert_multiway \<chi> # get_and_list (convert_multiway \<phi>))"
          by (cases \<chi>) (simp_all del: safe_formula.simps)
        with cp ncp have "contains_pred p (convert_multiway \<phi>)
          \<or> (\<exists>x \<in> set (get_and_list (convert_multiway \<phi>)). contains_pred p x)"
          by (auto simp del: convert_multiway.simps)
        then show ?thesis
          using not_contains_pred_get_and by blast
      qed
    qed
  qed
  assume cp: "contains_pred p (convert_multiway (\<phi> \<and>\<^sub>F \<psi>))"
    and ncp: "\<not> contains_pred p (convert_multiway \<psi>)"
  show "contains_pred p (convert_multiway \<phi>)"
  proof (cases "\<exists>\<phi>' I \<psi>'. \<psi> = \<phi>' \<^bold>R I \<psi>' \<and> \<not> mem I 0")
    case False
    then show ?thesis
      using main cp ncp by blast
  next
    case True
    then obtain \<phi>' I \<psi>' where \<psi>: "\<psi> = \<phi>' \<^bold>R I \<psi>'" "\<not> mem I 0"
      by blast
    then have "convert_multiway (\<phi> \<and>\<^sub>F \<psi>) = convert_multiway (\<phi> \<and>\<^sub>F \<not>\<^sub>F Formula.eventually I Formula.TT)
      \<or>\<^sub>F convert_multiway (\<phi> \<and>\<^sub>F release_safe_bounded \<phi>' I \<psi>')"
      by (simp add: and_release_safe_bounded_def safe_assignment_iff)
    with cp consider
      (left) "contains_pred p (convert_multiway (\<phi> \<and>\<^sub>F \<not>\<^sub>F Formula.eventually I Formula.TT))"
      | (right) "contains_pred p (convert_multiway (\<phi> \<and>\<^sub>F release_safe_bounded \<phi>' I \<psi>'))"
      by (auto simp del: convert_multiway.simps)
    then show ?thesis
    proof cases
      case left
      have "\<not> contains_pred p (convert_multiway (\<not>\<^sub>F Formula.eventually I Formula.TT))"
        by (simp add: Formula.eventually_def Formula.TT_def Formula.FF_def)
      with left show ?thesis
        by (rule main) simp
    next
      case right
      have "\<not> contains_pred p (convert_multiway (release_safe_bounded \<phi>' I \<psi>'))"
        using ncp \<psi> by simp
      with right show ?thesis
        by (rule main) (simp add: release_safe_bounded_def)
    qed
  qed
qed

lemma no_pred_cmultiway_always_safe_0I: "\<not> contains_pred p (convert_multiway \<psi>) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway (always_safe_0 I \<psi>))"
  by (auto simp: always_safe_0_def simp del: convert_multiway.simps(10,11) 
      dest!: pred_cmultiway_conjD)

lemma convert_multiway_remove_neg: "safe_formula (remove_neg \<phi>) 
  \<Longrightarrow> convert_multiway (remove_neg \<phi>) = remove_neg (convert_multiway \<phi>)"
  by (cases \<phi>) (auto simp: and_release_safe_bounded_def release_safe_0_def 
      elim: case_NegE split: formula.splits)

lemma contains_pred_convert_multiway_always_safe_bounded [simp]: 
  "contains_pred p (convert_multiway (always_safe_bounded I \<psi>')) = contains_pred p (convert_multiway \<psi>')"
  unfolding always_safe_bounded_def
  by (auto simp: is_constraint_iff)

lemma no_pred_cmultiway_release_safe_boundedI: "\<not> contains_pred p (convert_multiway \<phi>) 
    \<Longrightarrow> \<not> contains_pred p (convert_multiway \<psi>) 
    \<Longrightarrow> \<not> contains_pred p (convert_multiway (release_safe_bounded \<phi> I \<psi>))"
  unfolding always_safe_0_def
  by (auto simp: release_safe_bounded_def simp del: convert_multiway.simps(10,11) 
      dest!: pred_cmultiway_conjD)

lemma contains_pred_convert_multiway: "\<not> contains_pred p \<phi> \<Longrightarrow> \<not> contains_pred p (convert_multiway \<phi>)"
proof (induction p \<phi> rule: contains_pred.induct)
  case(10 p \<phi> \<psi>)
  then have "\<not> contains_pred p (convert_multiway \<phi>)" "\<not> contains_pred p (convert_multiway \<psi>)"
    by simp_all
  then show ?case
    using pred_cmultiway_conjD by blast
next
  case(19 p \<phi> I \<psi>)
  then have "\<not> contains_pred p (convert_multiway \<phi>)" "\<not> contains_pred p (convert_multiway \<psi>)"
    by simp_all
  then show ?case
    using no_pred_cmultiway_release_safe_boundedI[of p \<phi> \<psi> I]
    by (cases "mem I 0")
      (auto simp del: convert_multiway.simps(10) dest!: pred_cmultiway_conjD)
next
  case(20 p I r)
  then show ?case by (auto simp add: regex.set_map)
next
  case(21 p I r)
  then show ?case by (auto simp add: regex.set_map)
qed (auto simp: nfv_convert_multiway)

lemma sf_letpast_cmultiway_subst1:
  "safe_letpast p (convert_multiway (\<phi> \<and>\<^sub>F \<not>\<^sub>F Formula.eventually I Formula.TT))
  = safe_letpast p (convert_multiway \<phi>) \<squnion> Unused"
  by (simp add: safe_letpast_get_and sup_commute)

lemma sf_letpast_cmultiway_subst2:
  "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi> 
  \<Longrightarrow> safe_letpast p (convert_multiway (\<phi> \<and>\<^sub>F release_safe_bounded \<phi>' I \<psi>')) 
  = (safe_letpast p \<phi>) \<squnion> safe_letpast p (convert_multiway (release_safe_bounded \<phi>' I \<psi>'))"
  by (auto simp: is_constraint_iff safe_assignment_iff
      Sup_rec_safety_union image_Un safe_letpast_get_and sup_commute) 
    (clarsimp simp: release_safe_bounded_def)

lemma sf_letpast_cmultiway_conj: "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi>
 \<Longrightarrow> safe_letpast p (convert_multiway \<psi>) = safe_letpast p \<psi>
  \<Longrightarrow> safe_letpast p (convert_multiway (\<phi> \<and>\<^sub>F \<psi>)) = safe_letpast p (\<phi> \<and>\<^sub>F \<psi>)"
  by (cases \<psi>; auto simp add: image_Un Sup_rec_safety_union safe_letpast_get_and sup_commute
        sf_letpast_cmultiway_subst1 simp del: convert_multiway.simps(19) safe_formula.simps(19))
    (simp add: and_release_safe_bounded_def bot_rec_safety_def[symmetric]
        sf_letpast_cmultiway_subst1 sf_letpast_cmultiway_subst2
        del: convert_multiway.simps(10))

lemma sf_letpast_cmultiway_subst5:
  "safe_letpast p (convert_multiway (always_safe_bounded I \<psi>))
  = AnyRec * (safe_letpast p (convert_multiway \<psi>))"
  by (simp add: always_safe_bounded_def safe_assignment_iff is_constraint_iff)
    (rule_tac y="safe_letpast p (convert_multiway \<psi>)" in rec_safety.exhaust; force)

lemma sf_letpast_cmultiway_subst6:
  "safe_letpast p (convert_multiway (and_release_safe_bounded (Formula.eventually J Formula.TT) \<phi>' I \<psi>')) =
    Unused \<squnion> safe_letpast p (convert_multiway (release_safe_bounded \<phi>' I \<psi>'))"
  by (clarsimp simp: and_release_safe_bounded_def sup_commute
          Sup_rec_safety_union image_Un safe_letpast_get_and split: if_splits) 
        (clarsimp simp: release_safe_bounded_def)

lemma sf_letpast_cmultiway_subst7:
  "safe_letpast p (convert_multiway ((Formula.eventually I Formula.TT) \<and>\<^sub>F \<gamma>)) 
  = Unused \<squnion> (safe_letpast p (convert_multiway \<gamma>))"
    by (auto simp: safe_assignment_iff is_constraint_iff case_release_iff case_trigger_iff
        Sup_rec_safety_union image_Un safe_letpast_get_and sup_commute
        sf_letpast_cmultiway_subst6)

lemma safe_letpast_convert_multiway: "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi>"
proof (induction p \<phi> rule: safe_letpast.induct)
  case (5 p e \<phi> \<psi>)
  then show?case 
    by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case (6 p e \<phi> \<psi>)
  then show ?case 
    by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case (7 p e \<phi> \<psi>)
  then show ?case 
    by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case(10 p \<phi> \<psi>)
  then show ?case
    by (intro sf_letpast_cmultiway_conj)
next
  case (19 p \<phi> I \<psi>)
  have "safe_letpast p (convert_multiway (\<psi> \<and>\<^sub>F \<phi>)) = safe_letpast p \<psi> \<squnion> safe_letpast p \<phi>"
    using sf_letpast_cmultiway_conj[of p \<psi> \<phi>] 19 by simp
  then have "memL I 0 \<Longrightarrow> safe_letpast p ((convert_multiway (\<psi> \<and>\<^sub>F \<phi>)) \<^bold>R I (convert_multiway \<psi>)) 
    = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
    using 19 by (simp add: sup_commute sup_left_commute)
  moreover have "\<not> memL I 0 \<Longrightarrow> safe_letpast p (convert_multiway (release_safe_bounded \<phi> I \<psi>)) 
    = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
    using 19 by (clarsimp simp: release_safe_bounded_def mult_sup_distrib mult.assoc[symmetric]
         sf_letpast_cmultiway_subst5 sf_letpast_cmultiway_subst7 sf_letpast_cmultiway_conj 
         bot_rec_safety_def[symmetric] simp del: convert_multiway.simps(10))
      (simp add: sup.commute)
  ultimately show ?case
    by simp
next
  case(20 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
next
  case(21 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
qed (auto simp add: image_image)

lemma safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway fv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  show ?case proof -
    let ?l = "get_and_list ?c\<phi> @ get_and_list ?c\<psi>"
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    have lsafe_neg: "list_all safe_neg ?l"
      using And_safe \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
      by (simp add: safe_get_and)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> set neg \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by auto
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis by (auto simp: list_all_iff)
    qed

    have pos_filter: "pos = filter safe_formula (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
      using posneg by simp
    have "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)"
    proof -
      have 1: "fv ?c\<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<phi>))). fv x)" (is "_ \<subseteq> ?fv\<phi>")
        using And_safe \<open>safe_formula \<phi>\<close> by (blast intro!: fv_safe_get_and)
      have 2: "fv ?c\<psi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<psi>))). fv x)" (is "_ \<subseteq> ?fv\<psi>")
        using And_safe \<open>safe_formula \<psi>\<close> by (blast intro!: fv_safe_get_and)
      have "(\<Union>x\<in>set neg. fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>" proof -
        have "\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` (set pos \<union> set neg))"
          by simp
        also have "... \<subseteq> fv (convert_multiway \<phi>) \<union> fv (convert_multiway \<psi>)"
          unfolding partition_set[OF posneg[symmetric], simplified]
          by (simp add: fv_get_and)
        finally show ?thesis .
      qed
      then have "(\<Union>x\<in>set neg. fv x) \<subseteq> ?fv\<phi> \<union> ?fv\<psi>" using 1 2 by blast
      then show ?thesis unfolding pos_filter by simp
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_safe \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  show ?case proof -
    let ?l = "\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>"
    note \<open>safe_formula ?c\<phi>\<close>
    then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
    moreover have "safe_neg (\<not>\<^sub>F ?c\<psi>)"
      using \<open>safe_formula ?c\<psi>\<close> by (simp add: safe_neg_def)
    then have lsafe_neg: "list_all safe_neg ?l" using calculation by simp
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> (set neg) \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by (auto simp del: filter.simps)
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis using Ball_set_list_all by force
    qed

    have pos_filter: "pos = filter safe_formula ?l"
      using posneg by simp
    have neg_filter: "neg = filter (Not \<circ> safe_formula) ?l"
      using posneg by simp
    have "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set pos). fv x)"
    proof -
      have fv_neg: "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set ?l). fv x)" using posneg by auto
      have "(\<Union>x\<in>(set ?l). fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
        by (simp add: fv_get_and fv_convert_multiway)
      also have "fv ?c\<phi> \<union> fv ?c\<psi> \<subseteq> fv ?c\<phi>"
        using \<open>fv (\<not>\<^sub>F \<psi>) \<subseteq> fv \<phi>\<close>
        by (simp add: fv_convert_multiway)
      finally have "(\<Union>x\<in>(set neg). fv x) \<subseteq> fv ?c\<phi>"
        using fv_neg unfolding neg_filter by blast
      then show ?thesis
        unfolding pos_filter
        using fv_safe_get_and[OF And_Not.IH(1)]
        by auto
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_Not.IH \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = \<phi>' \<^bold>T I \<psi>'"
  define f where "f = \<phi> \<and>\<^sub>F t"
  have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not> is_constraint t"
    by (auto simp add: t_def)

  have "\<exists>f \<in> set (get_and_list (convert_multiway \<phi>)). safe_formula f"
  proof -
    {
      assume assm: "\<forall>f \<in> set (get_and_list (convert_multiway \<phi>)). \<not> safe_formula f"
      then have "False"
      proof (cases "case (convert_multiway \<phi>) of (\<And>\<^sub>F l) \<Rightarrow> True | _ \<Rightarrow> False")
        case True
        then obtain l where "convert_multiway \<phi> = \<And>\<^sub>F l"
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Trigger(5)
          by (auto simp: list_all_iff split: if_splits)
      next
        case False
        then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
          using assm
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Trigger(5)
          by auto
      qed
    }
    then show ?thesis by auto
  qed
  then have filter_pos: "filter safe_formula (get_and_list (convert_multiway \<phi>)) \<noteq> []"
    by (simp add: filter_empty_conv)

  have \<phi>_fvs: "\<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>)))))) 
    \<subseteq> \<Union>(set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
    using And_Trigger
    by (cases "(convert_multiway \<phi>)") (auto)

  show ?case
  proof (cases "safe_formula t")
    define l where "l = get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t)"
    define pos where "pos = fst (partition safe_formula l)"
    define neg where "neg = snd (partition safe_formula l)"

    case True
    then have convert_f: "convert_multiway f = \<And>\<^sub>F l"
      unfolding f_def l_def
      using t_not_safe_assign
      by auto

    have "safe_formula (convert_multiway t)"
      using And_Trigger True
      unfolding t_def
      by (auto split: if_splits simp add: safe_dual_def fv_convert_multiway)
    then have neg_fv: "\<Union>(set (map fv neg)) 
      = \<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      unfolding neg_def l_def t_def
      by auto

    have mem:
      "mem I 0"
      "safe_formula \<psi>'"
      "fv \<phi>' \<subseteq> fv \<psi>'"
      "safe_formula \<phi>'"
      using True And_Trigger
      unfolding t_def
      by (auto split: if_splits simp add: safe_dual_def)
    have case_neg_to_fol: "(case \<gamma> of \<not>\<^sub>F x \<Rightarrow> safe_formula x | _ \<Rightarrow> safe_formula \<gamma>) \<longleftrightarrow> 
      (\<not> ((\<exists>x. \<gamma> = \<not>\<^sub>F x \<and> safe_formula x) \<longleftrightarrow> (\<forall>x. \<gamma> \<noteq> \<not>\<^sub>F x \<and> safe_formula \<gamma>)))"
      for \<gamma>:: "'a Formula.formula"
      by (cases \<gamma>, auto simp: trm.is_Var_def trm.is_Const_def simp del: safe_formula.simps)

    have "filter safe_formula pos \<noteq> []"
      using filter_pos
      unfolding pos_def l_def
      by auto
    moreover have "list_all (\<lambda>\<phi>. (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> safe_formula \<phi>)) neg"
    proof -
      have "safe_neg x" if "x \<in> set l" for x
        using that safe_get_and[OF And_Trigger(5)]
          safe_get_and[OF \<open>safe_formula (convert_multiway t)\<close>]
        unfolding l_def by (auto simp: list_all_iff)
      moreover have "(case x of \<not>\<^sub>F x' \<Rightarrow> safe_formula x' | _ \<Rightarrow> safe_formula x)
        = safe_formula (remove_neg x)" for x :: "'a Formula.formula"
        by (cases x) simp_all
      ultimately show ?thesis
        unfolding neg_def by (auto simp: list_all_iff safe_neg_def)
    qed
    moreover have "\<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))"
      using \<phi>_fvs neg_fv
      unfolding l_def pos_def
      by (auto simp add: fv_convert_multiway)
    ultimately have "safe_formula (\<And>\<^sub>F l)"
      unfolding pos_def neg_def
      by (auto simp: case_neg_to_fol list_all_iff split: if_splits)
    then show ?thesis
      using convert_f
      unfolding f_def t_def
      by auto
  next

    case False
    then have convert_f: "convert_multiway f 
      = (convert_multiway \<phi>) \<and>\<^sub>F ((convert_multiway \<phi>') \<^bold>T I (convert_multiway \<psi>'))"
      using t_not_safe_assign t_not_constraint
      unfolding f_def t_def convert_multiway.simps
      by auto

    then show ?thesis
      using And_Trigger
      unfolding f_def t_def
      by (auto simp add: safe_assignment_iff
          fv_convert_multiway safe_dual_def split: if_splits)
  qed
next
  case (Ands l pos neg)
  obtain pos' neg' where posneg': "(pos', neg') = partition safe_formula (map convert_multiway l)"
    by simp
  have pos: "\<phi> \<in> set pos \<longleftrightarrow> \<phi> \<in> set l \<and> safe_formula \<phi>"
    and neg: "\<phi> \<in> set neg \<longleftrightarrow> \<phi> \<in> set l \<and> \<not> safe_formula \<phi>" for \<phi>
    using Ands.hyps(1) by simp_all
  have pos': "\<psi> \<in> set pos' \<longleftrightarrow> \<psi> \<in> convert_multiway ` set l \<and> safe_formula \<psi>"
    and neg': "\<psi> \<in> set neg' \<longleftrightarrow> \<psi> \<in> convert_multiway ` set l \<and> \<not> safe_formula \<psi>" for \<psi>
    using posneg' by simp_all
  have safe_pos: "safe_formula (convert_multiway \<phi>)" if "\<phi> \<in> set pos" for \<phi>
    using Ands.IH(1) that by (simp add: list_all_iff)
  have safe_neg: "safe_formula (remove_neg (convert_multiway \<phi>))" if "\<phi> \<in> set neg" for \<phi>
  proof -
    have "safe_formula (remove_neg \<phi>)" and "safe_formula (convert_multiway (remove_neg \<phi>))"
      using Ands.hyps(4) Ands.IH(2) that by (simp_all add: list_all_iff)
    then show ?thesis
      by (simp add: convert_multiway_remove_neg)
  qed
  have unsafe_neg: "\<phi> \<in> set neg" if "\<phi> \<in> set l" and "\<not> safe_formula (convert_multiway \<phi>)" for \<phi>
    using that safe_pos pos neg by blast
  have pos_pos': "convert_multiway ` set pos \<subseteq> set pos'"
    using safe_pos pos pos' by blast
  have neg'_neg: "set neg' \<subseteq> convert_multiway ` set neg"
    using unsafe_neg by (auto simp: neg')
  have "pos' \<noteq> []"
    using hd_in_set[OF Ands.hyps(2)] pos_pos' by force
  moreover have "list_all safe_formula (map remove_neg neg')"
    using neg'_neg safe_neg by (auto simp: list_all_iff)
  moreover have "\<Union>(set (map fv neg')) \<subseteq> \<Union>(set (map fv pos'))"
  proof -
    have "\<Union>(set (map fv neg')) \<subseteq> (\<Union>\<phi>\<in>set neg. fv (convert_multiway \<phi>))"
      using neg'_neg by auto
    also have "\<dots> \<subseteq> (\<Union>\<phi>\<in>set pos. fv (convert_multiway \<phi>))"
      using Ands.hyps(5) by (simp add: fv_convert_multiway)
    also have "\<dots> \<subseteq> \<Union>(set (map fv pos'))"
      using pos_pos' by auto
    finally show ?thesis .
  qed
  ultimately show ?case
    unfolding convert_multiway.simps safe_formula.simps posneg'[symmetric] by simp
next
  case (Neg \<phi>)
  with Neg show ?case 
    by (simp add: fv_convert_multiway)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  moreover {
    assume "safe_formula \<phi> \<and> safe_formula (convert_multiway \<phi>)"
    then have ?case 
      using assms 
      by (auto simp add: fv_convert_multiway safe_dual_def safe_assignment_iff)
  }
  moreover {
    assume assm: "is_constraint \<phi>"
    then have "is_constraint (convert_multiway \<phi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    moreover have "FV (convert_multiway \<phi>) \<subseteq> FV (convert_multiway \<psi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assms(2-3) assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    ultimately have ?case
      using assms case_NegE
      by (auto simp add: fv_convert_multiway safe_dual_def
          \<open>FV (convert_multiway \<phi>) \<subseteq> FV (convert_multiway \<psi>)\<close>)
        fastforce
  }
  moreover {
    assume "(case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> safe_formula (convert_multiway \<phi>') | _ \<Rightarrow> False)"
    then obtain \<phi>' where \<phi>_def: "\<phi> = \<not>\<^sub>F \<phi>'" "safe_formula \<phi>'" "safe_formula (convert_multiway \<phi>')"
      by (auto split: formula.splits)
    then have ?case
      using assms
      by (auto simp add: fv_convert_multiway safe_dual_def)
  }
  ultimately show ?case by blast
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case
    by (auto simp: fv_convert_multiway simp del: convert_multiway.simps(10))
next
  case (MatchP I r)
  then show ?case
    by (auto 0 3 simp: safe_atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest:  split: if_splits)
next
  case (MatchF I r)
  then show ?case
    by (auto 0 3 simp: safe_atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: split: if_splits)
qed (auto simp add: fv_convert_multiway nfv_convert_multiway 
    safe_assignment_iff is_constraint_iff
    safe_dual_def case_Neg_iff)


subsection \<open> convert multiway and future bounded \<close>

lemma future_bounded_multiway_Ands: "Safety.future_bounded (convert_multiway \<phi>) = Safety.future_bounded \<phi> 
  \<Longrightarrow> Safety.future_bounded (\<And>\<^sub>F (get_and_list (convert_multiway \<phi>))) = Safety.future_bounded \<phi>"
  by (cases "case (convert_multiway \<phi>) of \<And>\<^sub>F l \<Rightarrow> True | _ \<Rightarrow> False") 
    (auto split: formula.splits)

lemma future_bounded_convert_multiway: 
  "safe_formula \<phi> \<Longrightarrow> Safety.future_bounded (convert_multiway \<phi>) = Safety.future_bounded \<phi>"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  have "Safety.future_bounded ?a = (Safety.future_bounded ?c\<phi> \<and> Safety.future_bounded ?c\<psi>)"
    using And_safe by simp
  moreover have "Safety.future_bounded ?c\<phi> = list_all Safety.future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "Safety.future_bounded ?c\<psi> = list_all Safety.future_bounded (get_and_list ?c\<psi>)"
    using \<open>safe_formula \<psi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "Safety.future_bounded ?b = list_all Safety.future_bounded (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    unfolding b_def by simp
  ultimately show ?case by simp
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = \<phi>' \<^bold>T I \<psi>'"
  define f where "f = \<phi> \<and>\<^sub>F t"
  have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not> is_constraint t"
    by (auto simp add: t_def)

  then show ?case proof (cases "safe_formula t")
    define l where "l = (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t))"
    case True
    then have f_convert: "convert_multiway f = \<And>\<^sub>F l"
      using t_not_safe_assign
      unfolding l_def f_def
      by auto
    have t_multiway: "Safety.future_bounded (convert_multiway t) = Safety.future_bounded t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
    have "list_all Safety.future_bounded l = (Safety.future_bounded \<phi> \<and> Safety.future_bounded (\<phi>' \<^bold>T I \<psi>'))"
      using future_bounded_multiway_Ands[OF t_multiway] future_bounded_multiway_Ands[OF And_Trigger(5)]
      unfolding l_def t_def
      by auto
    then show ?thesis
      using f_convert
      unfolding f_def t_def
      by auto
  next
    case False
    then have convert_f: "convert_multiway f 
      = (convert_multiway \<phi>) \<and>\<^sub>F ((convert_multiway \<phi>') \<^bold>T I (convert_multiway \<psi>'))"
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
  then show ?case 
    by (auto simp add: and_release_safe_bounded_def 
        release_bounded_future_bounded safe_assignment_iff)
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  have "Safety.future_bounded ?a = (Safety.future_bounded ?c\<phi> \<and> Safety.future_bounded ?c\<psi>)"
    using And_Not by simp
  moreover have "Safety.future_bounded ?c\<phi> = list_all Safety.future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "Safety.future_bounded ?b = list_all Safety.future_bounded (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    unfolding b_def by (simp add: list.pred_map o_def)
  ultimately show ?case by auto
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  then have "Safety.future_bounded (convert_multiway \<phi>) = Safety.future_bounded \<phi>"
  proof -
    {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis by (cases \<phi>) (auto simp add: safe_assignment_def)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' 
      \<and> Safety.future_bounded (convert_multiway \<phi>') = Safety.future_bounded \<phi>' | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms by auto
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp: safe_atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp: safe_atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
qed (auto simp: list.pred_set convert_multiway_remove_neg is_constraint_iff
    future_bounded_remove_neg case_Neg_iff safe_assignment_iff)

lemma sat_convert_multiway: 
  "safe_formula \<phi> \<Longrightarrow> Formula.sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> Formula.sat \<sigma> V v i \<phi>"
proof (induction \<phi> arbitrary: V v i rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "get_and_list (convert_multiway \<psi>)"
  let ?sat = "Formula.sat \<sigma> V v i"
  have b_def: "?b = \<And>\<^sub>F (?la @ ?lb)" using And_safe by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_safe sat_get_and by blast
  moreover have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>" using And_safe sat_get_and by blast
  ultimately show ?case using And_safe by (auto simp: list.pred_set)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = \<phi>' \<^bold>T I \<psi>'"

  have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not> is_constraint t"
    by (auto simp add: t_def)

  have get_and_list: "get_and_list (convert_multiway t) = [convert_multiway t]"
    unfolding t_def
    by auto

  show ?case
  proof (cases "safe_formula t")
    case True
    then obtain l where l_props:
      "convert_multiway (\<phi> \<and>\<^sub>F t) = \<And>\<^sub>F l"
      "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
      using t_not_safe_assign t_not_constraint get_and_list
      by simp
  
    have t_sat: "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> convert_multiway t = \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
  
    have "(\<forall>\<phi>\<in>set l. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>) \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>')"
    proof (cases "case (convert_multiway \<phi>) of (\<And>\<^sub>F l) \<Rightarrow> True | _ \<Rightarrow> False")
      case True
      then obtain l' where l'_props: "convert_multiway \<phi> = \<And>\<^sub>F l'" 
        by (auto split: formula.splits)
      then have "get_and_list (convert_multiway \<phi>) = (if l' = [] then [\<And>\<^sub>F l'] else l')"
        by (simp add: l'_props)
      moreover have "(\<forall>\<phi>\<in>set l'. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>) = \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
        using And_Trigger(5) l'_props
        by auto
      ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
    next
      case False
      then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
        by (auto split: formula.splits)
      moreover have "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> convert_multiway \<phi> = \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
        using And_Trigger(5)
        by auto
      ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
    qed
  
    then show ?thesis
      using l_props(1)
      unfolding t_def
      by auto
  next
    case False
    then show ?thesis
      using And_Trigger t_not_safe_assign t_not_constraint
      unfolding t_def
      by auto
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  then show ?case 
    using sat_and_release_rewrite[OF And_Release(5)] 
    by auto
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "convert_multiway \<psi>"
  let ?sat = "Formula.sat \<sigma> V v i"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?lb # ?la)" using And_Not by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_Not sat_get_and by blast
  then show ?case using And_Not by (auto simp: list.pred_set)
next
  case (Agg y \<omega> tys f \<phi>)
  then show ?case
    by (simp add: Formula.nfv_def fv_convert_multiway cong: conj_cong)
next
  case (MatchP I r)
  then have "Regex.match (Formula.sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (Formula.sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: safe_atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (MatchF I r)
  then have "Regex.match (Formula.sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (Formula.sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: safe_atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (Ands l pos neg)
  have sat_remove_neg: "(\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> (remove_neg \<phi>) \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>(remove_neg \<psi>)) 
    \<longleftrightarrow> (\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi> \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<psi>)" 
    if "Formula.is_Neg \<phi> \<longleftrightarrow> Formula.is_Neg \<psi>" for V v i \<phi> \<psi>
    using that 
    by (cases \<phi>; cases \<psi>) 
      (auto simp add: Formula.is_Neg_def)
  have "formula.is_Neg (convert_multiway (\<phi>1 \<and>\<^sub>F \<phi>2)) \<longleftrightarrow> False" 
    for \<phi>1 \<phi>2 :: "'t Formula.formula"
    by (clarsimp, cases \<phi>2; clarsimp simp: and_release_safe_bounded_def split: if_splits)
  hence is_Neg_cm: "Formula.is_Neg (convert_multiway \<phi>) \<longleftrightarrow> Formula.is_Neg \<phi>" 
    for \<phi> :: "'t Formula.formula"
    by (cases \<phi>; clarsimp simp: release_safe_0_def release_safe_bounded_def eventually_def 
        simp del: convert_multiway.simps(10)) blast+
  from Ands show ?case
    by (fastforce simp: list.pred_set convert_multiway_remove_neg sat_remove_neg[OF is_Neg_cm])
next
  case (Trigger_0 \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>; auto)
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case
    using sat_release_conj_0[OF Release_0(1), where \<phi>=\<phi> and \<psi>=\<psi>]
    by (simp del: convert_multiway.simps(10))
qed (auto simp: nfv_convert_multiway cong: nat.case_cong)

(*<*)
end
(*>*)
