(*<*)
theory Safety_Proofs
  imports Progress
begin
(*>*)

unbundle MFODL_notation \<comment> \<open> enable notation \<close>


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

lemma no_pred_cmultiway_release_safe_0I: "\<not> contains_pred p (convert_multiway \<phi>) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway \<psi>) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway (release_safe_0 \<phi> I \<psi>))"
  by (auto simp: release_safe_0_def simp del: convert_multiway.simps(10,11) 
      intro!: no_pred_cmultiway_always_safe_0I
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
    by (cases "mem I 0")
      (auto simp del: convert_multiway.simps(10) dest!: pred_cmultiway_conjD
        intro: no_pred_cmultiway_release_safe_boundedI)
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
  by (auto simp add: image_Un Sup_rec_safety_union safe_letpast_get_and sup_commute
        sf_letpast_cmultiway_subst1 split: formula.splits) 
      (simp add: and_release_safe_bounded_def bot_rec_safety_def[symmetric] 
        sf_letpast_cmultiway_subst1 sf_letpast_cmultiway_subst2 
        del: convert_multiway.simps(10))

lemma sf_letpast_cmultiway_subst3: "safe_letpast p (convert_multiway (always_safe_0 I \<psi>)) 
  = AnyRec * (safe_letpast p (convert_multiway \<psi>))"
  by (simp add: always_safe_0_def safe_assignment_iff safe_letpast_get_and)
    (rule_tac y="safe_letpast p (convert_multiway \<psi>)" in rec_safety.exhaust; clarsimp)

lemma sf_letpast_cmultiway_subst4:
  "safe_letpast p (convert_multiway (\<psi> \<and>\<^sub>F (\<^bold>X I Formula.TT))) 
  = safe_letpast p (convert_multiway \<psi>)"
  by (clarsimp simp: safe_assignment_iff Sup_rec_safety_union image_Un safe_letpast_get_and)

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
    using 19 by (clarsimp simp: release_safe_bounded_def mult_sup_distrib mult_assoc[symmetric]
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
    using sat_release_rewrite_0 
    by auto
qed (auto simp: nfv_convert_multiway cong: nat.case_cong)

subsection \<open> Finite @{term safe_formula} \<close>

text \<open>The finiteness argument works with partial valuations: lists of optional values of length
  @{term n} that are defined exactly at a set of variables.  They are not the monitor's tuples,
  which list the values at their columns only; @{text safe_formula_finite_dense} below transfers
  the result to those.\<close>

definition pwf_tuple :: "nat \<Rightarrow> nat set \<Rightarrow> 'a option list \<Rightarrow> bool" where
  "pwf_tuple n V x \<longleftrightarrow> length x = n \<and> (\<forall>i<n. x!i = None \<longleftrightarrow> i \<notin> V)"

lemma pwf_tuple_length: "pwf_tuple n V x \<Longrightarrow> length x = n"
  unfolding pwf_tuple_def by simp

lemma pwf_tuple_Nil[simp]: "pwf_tuple n A [] = (n = 0)"
  unfolding pwf_tuple_def by auto

lemma Suc_pred_case: "Suc (x - Suc 0) = (case x of 0 \<Rightarrow> Suc 0 | _ \<Rightarrow> x)"
  by (auto split: nat.splits)

lemma pwf_tuple_Cons[simp]:
  "pwf_tuple n A (x # xs) \<longleftrightarrow> ((if x = None then 0 \<notin> A else 0 \<in> A) \<and>
   (\<exists>m. n = Suc m \<and> pwf_tuple m ((\<lambda>x. x - 1) ` (A - {0})) xs))"
  unfolding pwf_tuple_def
  by (auto 0 3 simp: nth_Cons image_iff Ball_def gr0_conv_Suc Suc_pred_case split: nat.splits)

lemma pwf_tuple_empty_iff: "pwf_tuple n {} v \<longleftrightarrow> v = replicate n None"
  by (auto simp: pwf_tuple_def intro!: nth_equalityI)

definition "unit_ptable n = {replicate n None}"

lemma in_unit_ptable: "v \<in> unit_ptable n \<longleftrightarrow> pwf_tuple n {} v"
  unfolding unit_ptable_def pwf_tuple_def by (auto intro!: nth_equalityI)

definition prestrict :: "nat set \<Rightarrow> 'a option list \<Rightarrow> 'a option list" where
  "prestrict A v = map (\<lambda>i. if i \<in> A then v ! i else None) [0 ..< length v]"

lemma prestrict_Nil[simp]: "prestrict A [] = []"
  unfolding prestrict_def by auto

lemma prestrict_Cons[simp]: "prestrict A (x # xs) =
  (if 0 \<in> A then x # prestrict ((\<lambda>x. x - 1) ` (A - {0})) xs else None # prestrict ((\<lambda>x. x - 1) ` A) xs)"
  unfolding prestrict_def
  by (auto simp: map_upt_Suc image_iff Suc_pred_case Ball_def simp del: upt_Suc split: nat.splits)

lemma prestrict_prestrict: "prestrict A (prestrict B v) = prestrict (A \<inter> B) v"
  by (simp add: prestrict_def)

lemma prestrict_idle: "pwf_tuple n A v \<Longrightarrow> prestrict A v = v"
  by (induct v arbitrary: n A) (auto split: if_splits)

lemma length_prestrict[simp]: "length (prestrict A v) = length v"
  unfolding prestrict_def by auto

lemma map_the_prestrict: "i \<in> A \<Longrightarrow> map the (prestrict A v) ! i = map the v ! i"
  by (induct v arbitrary: A i) (auto simp: nth_Cons' gr0_conv_Suc split: option.splits)

lemma pwf_tuple_prestrict: "pwf_tuple n B v \<Longrightarrow> A \<inter> B = C \<Longrightarrow> pwf_tuple n C (prestrict A v)"
  unfolding prestrict_def pwf_tuple_def by auto

lemma pwf_tuple_prestrict_simple: "pwf_tuple n B v \<Longrightarrow> A \<subseteq> B \<Longrightarrow> pwf_tuple n A (prestrict A v)"
  unfolding prestrict_def pwf_tuple_def by auto

lemma prestrict_eq_Nil[simp]: "prestrict A v = [] \<longleftrightarrow> v = []"
  unfolding prestrict_def by auto

lemma sat_the_prestrict: "fv \<phi> \<subseteq> A \<Longrightarrow>
  Formula.sat \<sigma> V (map the (prestrict A v)) i \<phi> = Formula.sat \<sigma> V (map the v) i \<phi>"
  by (rule sat_fv_cong) (auto intro!: map_the_prestrict)

fun pjoin1 :: "'a option list \<times> 'a option list \<Rightarrow> 'a option list option" where
  "pjoin1 ([], []) = Some []"
| "pjoin1 (None # xs, None # ys) = map_option (Cons None) (pjoin1 (xs, ys))"
| "pjoin1 (Some x # xs, None # ys) = map_option (Cons (Some x)) (pjoin1 (xs, ys))"
| "pjoin1 (None # xs, Some y # ys) = map_option (Cons (Some y)) (pjoin1 (xs, ys))"
| "pjoin1 (Some x # xs, Some y # ys) = (if x = y
    then map_option (Cons (Some x)) (pjoin1 (xs, ys))
    else None)"
| "pjoin1 _ = None"

lemma pjoin1_Some_prestrict:
  fixes x y :: "'a option list"
  assumes "pwf_tuple n A x" "pwf_tuple n B y"
  shows "pjoin1 (x, y) = Some z \<longleftrightarrow> pwf_tuple n (A \<union> B) z \<and> prestrict A z = x \<and> prestrict B z = y"
  using assms
proof (induct "(x, y)" arbitrary: n x y z A B rule: pjoin1.induct)
  case (2 xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (3 x xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (4 xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (5 x xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
qed auto

definition pjoin :: "'a option list set \<Rightarrow> bool \<Rightarrow> 'a option list set \<Rightarrow> 'a option list set" where
  "pjoin A pos B = (if pos then Option.these (pjoin1 ` (A \<times> B))
    else A - Option.these (pjoin1 ` (A \<times> B)))"

lemma pjoin_prestrict:
  fixes X Y :: "'a option list set"
  assumes "\<And>v. v \<in> X \<Longrightarrow> pwf_tuple n A v" "\<And>v. v \<in> Y \<Longrightarrow> pwf_tuple n B v" "\<not> b \<Longrightarrow> B \<subseteq> A"
  shows "v \<in> pjoin X b Y \<longleftrightarrow>
    pwf_tuple n (A \<union> B) v \<and> prestrict A v \<in> X \<and> (if b then prestrict B v \<in> Y else prestrict B v \<notin> Y)"
  by (auto 4 4 simp: pjoin_def Option.these_def image_iff assms pwf_tuple_prestrict sup_absorb1 prestrict_idle
    prestrict_idle[OF assms(1)] elim: assms
    dest: pjoin1_Some_prestrict[OF assms(1,2), THEN iffD1, rotated -1]
    dest!: spec[of _ "Some v"]
    intro!: exI[of _ "Some v"] pjoin1_Some_prestrict[THEN iffD2, symmetric] bexI[rotated])

lemma inj_eval: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. map (Formula.eval_trm (map the v)) ts) {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
proof (intro inj_onI)
  fix x y
  assume vars: "\<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t"
    and x: "x \<in> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
    and y: "y \<in> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
    and eq: "map (Formula.eval_trm (map the x)) ts = map (Formula.eval_trm (map the y)) ts"
  show "x = y"
  proof (rule nth_equalityI)
    show "length x = length y"
      using x y by (simp add: pwf_tuple_def)
  next
    fix i
    assume "i < length x"
    with x y have i: "i < n" "i < length y"
      by (simp_all add: pwf_tuple_def)
    show "x ! i = y ! i"
    proof (cases "i \<in> \<Union> (fv_trm ` set ts)")
      case True
      with vars have "\<^bold>v i \<in> set ts"
        by (auto simp: Formula.is_Var_def Formula.is_Const_def)
      moreover from eq have "\<forall>t\<in>set ts. Formula.eval_trm (map the x) t = Formula.eval_trm (map the y) t"
        by simp
      ultimately have "map the x ! i = map the y ! i"
        by fastforce
      with \<open>i < length x\<close> i have "the (x ! i) = the (y ! i)"
        by simp
      moreover have "x ! i \<noteq> None" "y ! i \<noteq> None"
        using True x y i by (simp_all add: pwf_tuple_def)
      ultimately show ?thesis
        by (metis option.expand)
    next
      case False
      with x y i have "x ! i = None" "y ! i = None"
        by (auto simp: pwf_tuple_def)
      then show ?thesis
        by simp
    qed
  qed
qed

lemma inj_eval2: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  using inj_eval[of ts n] by (simp add: inj_on_def)

lemma finite_listset: "(\<And>A. A \<in> set xs \<Longrightarrow> finite A) \<Longrightarrow> finite (listset xs)"
  by (induct xs) (simp_all add: set_Cons_def finite_image_set2)

fun pjoinN :: "'a option list list \<Rightarrow> 'a option list option" where
"pjoinN [] = Some []"
|"pjoinN (a#b#cs) =  (case (pjoin1 (a, b)) of None \<Rightarrow> None| Some x \<Rightarrow> pjoinN (x#cs))"
|"pjoinN (a#[]) = Some a"

lemma in_listset_conv_list_all2: "xs \<in> listset ys \<longleftrightarrow> list_all2 (\<in>) xs ys"
  by (induct ys arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma pjoinN_Some_prestrict:
  fixes as :: "'a option list list"
  fixes bs :: "nat set list"
  assumes "list_all2 (pwf_tuple n) bs as"
  assumes "as\<noteq>[]"
  shows "pjoinN (as) = Some z \<longleftrightarrow> pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs as"
  using assms
proof (induct "as" arbitrary: n bs z rule: pjoinN.induct)
  case 1
  then show ?case
    by(auto)
next
  case (2 a b cs)
  from "2.prems"(1) obtain A B Cs where bs: "bs = A # B # Cs"
    and wf: "pwf_tuple n A a" "pwf_tuple n B b" "list_all2 (pwf_tuple n) Cs cs"
    by (auto simp: list_all2_Cons2)
  \<comment> \<open>the prestriction of @{term z} to @{term "A \<union> B"} is the only candidate for the pjoin of a and b\<close>
  have pjoin_prestrict: "pjoin1 (a, b) = Some (prestrict (A \<union> B) z) \<longleftrightarrow> prestrict A z = a \<and> prestrict B z = b"
    if "pwf_tuple n (\<Union> (set bs)) z"
  proof -
    have "pwf_tuple n (A \<union> B) (prestrict (A \<union> B) z)"
      using that by (auto simp: bs intro: pwf_tuple_prestrict_simple)
    then show ?thesis
      using pjoin1_Some_prestrict[OF wf(1,2)] by (simp add: prestrict_prestrict)
  qed
  show ?case
  proof (cases "pjoin1 (a, b)")
    case None
    then have "pjoinN (a # b # cs) \<noteq> Some z"
      by simp
    moreover have "\<not> (pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs (a # b # cs))"
      using pjoin_prestrict None by (auto simp: bs)
    ultimately show ?thesis
      by blast
  next
    case (Some c)
    with pjoin1_Some_prestrict[OF wf(1,2), of c] have c: "pwf_tuple n (A \<union> B) c"
      by simp
    have IH: "pjoinN (c # cs) = Some z \<longleftrightarrow> pwf_tuple n (A \<union> B \<union> \<Union> (set Cs)) z
      \<and> prestrict (A \<union> B) z = c \<and> list_all2 (\<lambda>b a. prestrict b z = a) Cs cs"
      using "2.hyps"[of c n "(A \<union> B) # Cs" z] Some c wf(3) by simp
    have "prestrict (A \<union> B) z = c \<longleftrightarrow> prestrict A z = a \<and> prestrict B z = b"
      if "pwf_tuple n (\<Union> (set bs)) z"
      using pjoin_prestrict[OF that] Some by auto
    with Some IH show ?thesis
      by (auto simp: bs Un_assoc)
  qed
next
  case (3 a)
  from "3.prems"(1) obtain b where bs: "bs = [b]" and wf: "pwf_tuple n b a"
    by (metis list_all2_Cons2 list_all2_Nil2)
  show ?case
  proof
    assume "pjoinN [a] = Some z"
    then have "z = a"
      by simp
    with wf show "pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs [a]"
      by (simp add: bs prestrict_idle)
  next
    assume "pwf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. prestrict b z = a) bs [a]"
    then have "pwf_tuple n b z" and "prestrict b z = a"
      by (simp_all add: bs)
    then show "pjoinN [a] = Some z"
      by (simp add: prestrict_idle)
  qed
qed

lemma finite_letpast:
  assumes fv: "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>"
  assumes V: "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
  assumes IH: "\<And>V i.
    \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
    finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  shows "finite {v. length v = Formula.nfv \<phi> \<and>
    letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) v i}"
proof (induction i rule: less_induct)
  case (less i)
  let ?F = "\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>"
  define X where "X = (\<lambda>w j. j < i \<and> letpast_sat ?F w j)"
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> X)"
  have "\<forall>pn\<in>dom ?V. \<forall>k. finite {v. length v = snd pn \<and> the (?V pn) v k}"
  proof (intro ballI allI)
    fix pn k
    assume "pn \<in> dom ?V"
    show "finite {v. length v = snd pn \<and> the (?V pn) v k}"
    proof (cases "pn = (p, Formula.nfv \<phi>)")
      case True
      then show ?thesis
        using less[of k] by (cases "k < i") (simp_all add: X_def fun_upd_same del: fun_upd_apply)
    next
      case False
      with \<open>pn \<in> dom ?V\<close> V show ?thesis
        by simp
    qed
  qed
  then have "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<phi>}"
    by (rule IH)
  moreover have "{v. length v = Formula.nfv \<phi> \<and> letpast_sat ?F v i}
    \<subseteq> map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<phi>}"
  proof
    fix v
    assume "v \<in> {v. length v = Formula.nfv \<phi> \<and> letpast_sat ?F v i}"
    then have len: "length v = Formula.nfv \<phi>" and "letpast_sat ?F v i"
      by simp_all
    then have "Formula.sat \<sigma> ?V v i \<phi>"
      unfolding X_def by (subst (asm) letpast_sat.simps)
    moreover have "pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) (map Some v)"
      using fv len by (auto simp: pwf_tuple_def)
    ultimately show "v \<in> map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<phi>}"
      by (intro image_eqI[where x = "map Some v"]) simp_all
  qed
  ultimately show ?case
    by (rule finite_surj)
qed

lemma safe_regex_Past_finite: "Regex.safe_regex fv rgx_safe_pred Past Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> safe_atms r \<Longrightarrow> finite {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"
proof (induct Past Strict r arbitrary: i rule: safe_regex_induct)
  case (Skip k)
  have "{v. pwf_tuple n (fv_regex (Regex.Skip k)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Skip k) j i)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
next
  case (Test \<phi>)
  then have "\<phi> \<in> safe_atms (Regex.Test \<phi>)"
    by simp
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Test \<phi>)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Test \<phi>) j i)}
    = {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}"
    by auto
  ultimately show ?case
    using Test(2) by simp
next
  case (Plus r s)
  have "finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"
    by (rule Plus.hyps(1)) (use Plus.prems in auto)
  moreover have "finite {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<le>i. Regex.match (test v) s j i)}"
    by (rule Plus.hyps(2)) (use Plus.prems in auto)
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Plus r s)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Plus r s) j i)}
    \<subseteq> {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}
      \<union> {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<le>i. Regex.match (test v) s j i)}"
    using Plus.prems(1) by auto
  ultimately show ?case
    by (simp add: finite_subset)
next
  case (TimesP r s)
  have fv: "fv_regex (Regex.Times r s) = fv_regex r"
    using TimesP.prems(1) by auto
  have r: "finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)}" for k
    by (rule TimesP.hyps) (use TimesP.prems in auto)
  have "{v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Times r s) j i)}
    \<subseteq> (\<Union>k\<in>{0..i}. {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)})"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Times r s) j i)}"
    then obtain j k where "pwf_tuple n (fv_regex r) v" "j \<le> i"
      "Regex.match (test v) r j k" "Regex.match (test v) s k i"
      unfolding fv by auto
    moreover from \<open>Regex.match (test v) s k i\<close> have "k \<le> i"
      by (rule match_le)
    ultimately show "v \<in> (\<Union>k\<in>{0..i}. {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)})"
      using match_le by fastforce
  qed
  moreover have "finite (\<Union>k\<in>{0..i}. {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>k. Regex.match (test v) r j k)})"
    using r by simp
  ultimately show ?case
    by (rule finite_subset)
next
  case (Star r)
  then have "{v. pwf_tuple n (fv_regex (Regex.Star r)) v \<and> (\<exists>j\<le>i. Regex.match (test v) (Regex.Star r) j i)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
qed

lemma safe_regex_Future_finite: "Regex.safe_regex fv rgx_safe_pred Futu Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> safe_atms r \<Longrightarrow> finite {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}"
proof (induct Futu Strict r arbitrary: i rule: safe_regex_induct)
  case (Skip k)
  have "{v. pwf_tuple n (fv_regex (Regex.Skip k)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Skip k) i j)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
next
  case (Test \<phi>)
  then have "\<phi> \<in> safe_atms (Regex.Test \<phi>)"
    by simp
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Test \<phi>)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Test \<phi>) i j)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> test v i \<phi>}"
    by auto
  ultimately show ?case
    using Test(2) by (blast intro: finite_subset)
next
  case (Plus r s)
  have "finite {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}"
    by (rule Plus.hyps(1)) (use Plus.prems in auto)
  moreover have "finite {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) s i j)}"
    by (rule Plus.hyps(2)) (use Plus.prems in auto)
  moreover have "{v. pwf_tuple n (fv_regex (Regex.Plus r s)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Plus r s) i j)}
    \<subseteq> {v. pwf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}
      \<union> {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) s i j)}"
    using Plus.prems(1) by auto
  ultimately show ?case
    by (simp add: finite_subset)
next
  case (TimesF r s)
  have fv: "fv_regex (Regex.Times r s) = fv_regex s"
    using TimesF.prems(1) by auto
  have s: "finite {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)}" for k
    by (rule TimesF.hyps) (use TimesF.prems in auto)
  have "{v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Times r s) i j)}
    \<subseteq> (\<Union>k\<in>{i..thr}. {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)})"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv_regex (Regex.Times r s)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Times r s) i j)}"
    then obtain j k where "pwf_tuple n (fv_regex s) v" "j \<le> thr"
      "Regex.match (test v) r i k" "Regex.match (test v) s k j"
      unfolding fv by auto
    moreover from this(3,4) have "i \<le> k" "k \<le> j"
      by (simp_all add: match_le)
    ultimately show "v \<in> (\<Union>k\<in>{i..thr}. {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)})"
      by fastforce
  qed
  moreover have "finite (\<Union>k\<in>{i..thr}. {v. pwf_tuple n (fv_regex s) v \<and> (\<exists>j\<in>{k..thr}. Regex.match (test v) s k j)})"
    using s by simp
  ultimately show ?case
    by (rule finite_subset)
next
  case (Star r)
  then have "{v. pwf_tuple n (fv_regex (Regex.Star r)) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) (Regex.Star r) i j)}
    \<subseteq> unit_ptable n"
    by (auto simp flip: in_unit_ptable)
  then show ?case
    by (rule finite_subset) (simp add: unit_ptable_def)
qed

lemma Collect_singleton_tuple_eq_image: "i < n \<Longrightarrow> {v. pwf_tuple n {i} v \<and> P (map the v ! i)} =
  (\<lambda>x. (replicate n None)[i := Some x]) ` Collect P"
  unfolding pwf_tuple_def
  by (auto simp add: list_eq_iff_nth_eq nth_list_update intro: rev_image_eqI)
  
lemma safe_formula_finite: "safe_formula \<phi> \<Longrightarrow> Safety.future_bounded \<phi> \<Longrightarrow> n\<ge> (Formula.nfv \<phi>) \<Longrightarrow> \<forall> i. finite (\<Gamma> \<sigma> i) \<Longrightarrow>
  \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
  finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
proof(induct \<phi> arbitrary: i n V rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case
    by(simp flip: in_unit_ptable add: unit_ptable_def)
next
  case (Eq_Var1 c x)
  then have "x < n"
    by (simp add: Formula.nfv_def)
  then show ?case
    using Collect_singleton_tuple_eq_image[of x n "\<lambda>y. c = y"] by simp
next
  case (Eq_Var2 c x)
  then have "x < n"
    by (simp add: Formula.nfv_def)
  then show ?case
    using Collect_singleton_tuple_eq_image[of x n "\<lambda>y. y = c"] by simp
next
  case (Pred e ts)
  then have vars: "\<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t"
    by simp
  show ?case
  proof (cases "V (e, length ts)")
    case None
    then have "{v. pwf_tuple n (fv (e \<dagger> ts)) v \<and> Formula.sat \<sigma> V (map the v) i (e \<dagger> ts)}
      = (\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) -` \<Gamma> \<sigma> i
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
      by auto
    moreover have "finite ((\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) -` \<Gamma> \<sigma> i
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v})"
      using Pred.prems inj_eval2[OF vars] by (intro finite_vimage_IntI) simp_all
    ultimately show ?thesis
      by simp
  next
    case (Some a)
    then have "{v. pwf_tuple n (fv (e \<dagger> ts)) v \<and> Formula.sat \<sigma> V (map the v) i (e \<dagger> ts)}
      = (\<lambda>v. map (Formula.eval_trm (map the v)) ts) -` {v. length v = length ts \<and> a v i}
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v}"
      by auto
    moreover from Pred.prems Some have "finite {v. length v = length ts \<and> a v i}"
      by (auto dest!: bspec[OF _ domI])
    then have "finite ((\<lambda>v. map (Formula.eval_trm (map the v)) ts) -` {v. length v = length ts \<and> a v i}
        \<inter> {v. pwf_tuple n (\<Union> (fv_trm ` set ts)) v})"
      using inj_eval[OF vars] by (rule finite_vimage_IntI)
    ultimately show ?thesis
      by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>)"
  have "{v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v j \<phi>}
    = map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) j \<phi>}" for j
    using Let.hyps(1) by (auto simp: pwf_tuple_def intro!: image_eqI[where x="map Some _"])
  moreover have "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) j \<phi>}" for j
    using Let by auto
  ultimately have "\<forall>pn\<in>dom ?V. \<forall>j. finite {v. length v = snd pn \<and> the (?V pn) v j}"
    using Let.prems by simp
  then have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<psi>}"
    using Let by auto
  then show ?case
    by simp
next
  case (Frz p \<phi> \<psi>)
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>)"
  have "{v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>}
    = map the ` {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    using Frz.hyps(1) by (auto simp: pwf_tuple_def intro!: image_eqI[where x="map Some _"])
  moreover have "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    using Frz by auto
  ultimately have "\<forall>pn\<in>dom ?V. \<forall>j. finite {v. length v = snd pn \<and> the (?V pn) v j}"
    using Frz.prems by simp
  then have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<psi>}"
    using Frz by auto
  then show ?case
    by simp
next
  case (LetPast p \<phi> \<psi>)
  let ?F = "\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>"
  let ?V = "V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat ?F)"
  have dom_V: "\<forall>pn\<in>dom ?V. \<forall>j. finite {v. length v = snd pn \<and> the (?V pn) v j}"
  proof (intro ballI allI)
    fix pn j
    assume "pn \<in> dom ?V"
    show "finite {v. length v = snd pn \<and> the (?V pn) v j}"
    proof (cases "pn = (p, Formula.nfv \<phi>)")
      case True
      have "finite {v. length v = Formula.nfv \<phi> \<and> letpast_sat ?F v j}"
      proof (rule finite_letpast)
        show "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>" "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
          using LetPast by auto
        show "finite {v. pwf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V' (map the v) k \<phi>}"
          if "\<forall>pn\<in>dom V'. \<forall>i. finite {v. length v = snd pn \<and> the (V' pn) v i}" for V' k
          using LetPast that by (intro LetPast.hyps(5)) auto
      qed
      with True show ?thesis
        by simp
    next
      case False
      with \<open>pn \<in> dom ?V\<close> LetPast.prems show ?thesis
        by auto
    qed
  qed
  have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> ?V (map the v) i \<psi>}"
    by (rule LetPast.hyps(6)[OF _ _ _ dom_V]) (use LetPast.prems in \<open>simp_all add: Formula.nfv_def\<close>)
  then show ?case
    by (simp add: Let_def)
next
  case (And_assign \<phi> \<psi>)
  then have IH: " finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by simp
  have fv_\<psi>_n: "\<forall>z\<in>fv \<psi>. z < n"
    using fvi_less_nfv[of \<psi>] And_assign(5) by fastforce
  \<comment> \<open>assigning a variable @{term x} that does not occur in @{term \<phi>} the value of a term over
    the variables of @{term \<phi>} is injective on the tuples satisfying @{term \<phi>}\<close>
  have assign: ?case
    if x: "x < n" "x \<notin> fv \<phi>" and t: "fv_trm t \<subseteq> fv \<phi>" and fv_\<psi>: "fv \<psi> = insert x (fv_trm t)"
      and sat_\<psi>: "\<And>v. Formula.sat \<sigma> V v i \<psi> \<longleftrightarrow> v ! x = Formula.eval_trm v t" for x t
  proof (rule finite_subset)
    let ?f = "\<lambda>v. v[x := Some (Formula.eval_trm (map the v) t)]"
    let ?A = "{v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    show "finite (?f ` ?A)"
      using IH by (rule finite_imageI)
    show "{v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<psi>)} \<subseteq> ?f ` ?A"
    proof
      fix v
      assume "v \<in> {v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<psi>)}"
      with t fv_\<psi> sat_\<psi> have wf: "pwf_tuple n (insert x (fv \<phi>)) v"
        and sat: "Formula.sat \<sigma> V (map the v) i \<phi>" and eq: "map the v ! x = Formula.eval_trm (map the v) t"
        by (simp_all add: Un_absorb2)
      let ?u = "v[x := None]"
      from wf x have "pwf_tuple n (fv \<phi>) ?u"
        by (auto simp: pwf_tuple_def nth_list_update)
      moreover from sat x(2) have "Formula.sat \<sigma> V (map the ?u) i \<phi>"
        by (simp add: sat_the_update)
      ultimately have "?u \<in> ?A"
        by simp
      moreover have "v = ?f ?u"
      proof (rule sym)
        from x(2) t have "\<forall>z\<in>fv_trm t. map the ?u ! z = map the v ! z"
          by (auto simp: map_update intro!: nth_list_update_neq)
        then have "Formula.eval_trm (map the ?u) t = Formula.eval_trm (map the v) t"
          by (rule eval_trm_fv_cong)
        moreover from wf x(1) have "v ! x = Some (map the v ! x)"
          by (auto simp: pwf_tuple_def)
        ultimately show "?f ?u = v"
          using eq x(1) pwf_tuple_length[OF wf] by (simp add: list_update_same_conv)
      qed
      ultimately show "v \<in> ?f ` ?A"
        by (rule rev_image_eqI)
    qed
  qed
  consider x y where "\<psi> = \<^bold>v x =\<^sub>F (\<^bold>v y)" and  "(x \<notin> fv \<phi> \<longleftrightarrow> y \<in> fv \<phi>)"
    |x t where "\<psi> = \<^bold>v x =\<^sub>F t" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    |x t where "\<psi> = t =\<^sub>F (\<^bold>v x)" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    using And_assign(2)
    by(simp add: safe_assignment_def Formula.is_Var_def split: Formula.formula.splits trm.splits)
  then show ?case
  proof cases
    case 1
    with fv_\<psi>_n have "x < n" "y < n"
      by simp_all
    show ?thesis
    proof (cases "x \<in> fv \<phi>")
      case True
      with 1 \<open>y < n\<close> show ?thesis
        by (intro assign[of y "\<^bold>v x"]) auto
    next
      case False
      with 1 \<open>x < n\<close> show ?thesis
        by (intro assign[of x "\<^bold>v y"]) auto
    qed
  next
    case 2
    with fv_\<psi>_n show ?thesis
      by (intro assign[of x t]) auto
  next
    case 3
    with fv_\<psi>_n show ?thesis
      by (intro assign[of x t]) auto
  qed
next
  case (And_safe \<phi> \<psi>)
  let ?A = "\<lambda>\<phi>. {v | v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (prestrict (fv \<phi>) v, prestrict (fv \<psi>) v)"
  let ?test = "(?A \<phi> \<times> ?A \<psi>)"
  have "finite (?A \<phi>)" and "finite (?A \<psi>)" using And_safe by auto
  then have "finite (?A \<phi> \<times> ?A \<psi>)" ..
  then have "finite (Option.these (pjoin1 ` (?A \<phi> \<times> ?A \<psi>)))"
    by (auto simp: Option.these_def)
  moreover have "{v. pwf_tuple n (fv \<phi> \<union> fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi> \<and> Formula.sat \<sigma> V (map the v) i \<psi>}
      \<subseteq> Option.these (pjoin1 ` (?A \<phi> \<times> ?A \<psi>))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have wf: "pwf_tuple n (fv \<phi> \<union> fv \<psi>) v"
      by simp
    from \<open>v \<in> ?B\<close> have "(prestrict (fv \<phi>) v, prestrict (fv \<psi>) v) \<in> ?A \<phi> \<times> ?A \<psi>"
      by (auto simp: pwf_tuple_prestrict_simple sat_the_prestrict)
    moreover have "pjoin1 (prestrict (fv \<phi>) v, prestrict (fv \<psi>) v) = Some v"
    proof -
      from wf have "pwf_tuple n (fv \<phi>) (prestrict (fv \<phi>) v)" "pwf_tuple n (fv \<psi>) (prestrict (fv \<psi>) v)"
        by (auto intro: pwf_tuple_prestrict_simple)
      with wf show ?thesis
        by (simp add: pjoin1_Some_prestrict)
    qed
    ultimately have "Some v \<in> pjoin1 ` (?A \<phi> \<times> ?A \<psi>)"
      by (rule rev_image_eqI[OF _ sym])
    then show "v \<in> ?B'"
      by (simp add: in_these_eq)
  qed
  ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (And_constraint \<phi> \<psi>)
  then have fin: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by simp
  have "fv (\<phi> \<and>\<^sub>F \<psi>) = fv \<phi>"
    using And_constraint.hyps(4) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<psi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by (simp add: Collect_mono_iff)
  from this fin show ?case
    by (rule finite_subset)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  hence obs: "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by simp
  have "FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>')) = FV \<phi>"
    using And_Trigger.hyps(4) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>'))) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>'))}
    \<subseteq> {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by (simp add: Collect_mono_iff)
  from this obs show ?case
    by (rule finite_subset)
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  hence obs: "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by simp
  have "FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>')) = FV \<phi>"
    using And_Release.hyps(7) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (FV (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>'))) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>'))}
    \<subseteq> {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by (simp add: Collect_mono_iff)
  from this obs show ?case
    by (rule finite_subset)
next
  case (And_Not \<phi> \<psi>)
  then have fin: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by simp
  have "fv (\<phi> \<and>\<^sub>F \<not>\<^sub>F \<psi>) = fv \<phi>"
    using And_Not.hyps(4) by (simp add: Un_absorb2)
  then have "{v. pwf_tuple n (fv (\<phi> \<and>\<^sub>F \<not>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<and>\<^sub>F \<not>\<^sub>F \<psi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by (simp add: Collect_mono_iff)
  from this fin show ?case
    by (rule finite_subset)
next
  case (Ands l pos neg)
  let ?A = "\<lambda>\<phi>. {v | v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (map (\<lambda> \<phi>.(prestrict (fv \<phi>) v)) pos)"
  let ?A_list = "listset (map (\<lambda> \<phi>. ?A \<phi>) pos)"
  from Ands.hyps(1) have pos: "set pos = {\<phi> \<in> set l. safe_formula \<phi>}"
    by simp
  have "finite (?A \<phi>)" if "\<phi> \<in> set pos" for \<phi>
  proof -
    from that pos have "\<phi> \<in> set l"
      by simp
    with Ands.prems(1) have "Safety.future_bounded \<phi>"
      by (simp add: list_all_iff)
    moreover from \<open>\<phi> \<in> set l\<close> Ands.prems(2) have "Formula.nfv \<phi> \<le> n"
      by (simp add: Max_ge_iff)
    ultimately show ?thesis
      using that Ands.hyps(6) Ands.prems(3,4) by (simp add: list_all_iff)
  qed
  then have "finite (?A_list)"
    by (intro finite_listset) auto
  then have "finite (Option.these (pjoinN ` (?A_list)))"
    by(auto simp: Option.these_def)
  moreover have "{v. pwf_tuple n (\<Union> (fv ` set l)) v \<and> (\<forall>x\<in>set l. Formula.sat \<sigma> V (map the v) i x)}
      \<subseteq> (Option.these (pjoinN ` (?A_list)))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have wf: "pwf_tuple n (\<Union> (fv ` set l)) v"
      by simp
    from \<open>v \<in> ?B\<close> have "?p v \<in> ?A_list"
      using Ands(1)
      by (auto simp: sat_the_prestrict in_listset_conv_list_all2 list.rel_map intro!: list.rel_refl_strong pwf_tuple_prestrict_simple)
    moreover have "pjoinN (?p v) = Some v"
    proof -
      have "set l = set pos \<union> set neg"
        using Ands.hyps(1) by auto
      with Ands.hyps(5) have fv_pos: "\<Union> (fv ` set pos) = \<Union> (fv ` set l)"
        by blast
      with wf have all2: "list_all2 (pwf_tuple n) (map fv pos) (?p v)"
        by (auto simp: list.rel_map intro!: list.rel_refl_strong pwf_tuple_prestrict_simple)
      from Ands.hyps(2) have "?p v \<noteq> []"
        by simp
      with wf fv_pos show ?thesis
        by (auto simp: pjoinN_Some_prestrict[OF all2] list.rel_map intro!: list.rel_refl_strong)
    qed
    ultimately have "Some v \<in> pjoinN ` ?A_list"
      by (rule rev_image_eqI[OF _ sym])
    then show "v \<in> ?B'"
      by (simp add: in_these_eq)
  qed
  ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (Neg \<phi>)
  then show ?case
   by(simp flip: in_unit_ptable add: unit_ptable_def)
next
  case (Or \<phi> \<psi>)
  then have "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  moreover from Or have "finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    by(simp)
  ultimately have "finite ({v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>} \<union> {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>})"
    (is "finite ?AB")
    by(simp)
  moreover have "{v. pwf_tuple n (fv (\<phi> \<or>\<^sub>F \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<phi> \<or>\<^sub>F \<psi>)} \<subseteq> ?AB"
    using Or.hyps(1) by auto
  ultimately show ?case
    by (rule finite_subset[rotated])
next
  case (Exists t \<phi>)
  from Exists have IH: "finite {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp add: Formula.nfv_def fvi_Suc_bound Suc_le_eq)
  have "{v. pwf_tuple n (fv (\<exists>\<^sub>F:t. \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<exists>\<^sub>F:t. \<phi>)}
    \<subseteq> tl ` {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv (\<exists>\<^sub>F:t. \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (\<exists>\<^sub>F:t. \<phi>)}"
    then obtain z where wf: "pwf_tuple n (Formula.fvi (Suc 0) \<phi>) v"
      and sat: "Formula.sat \<sigma> V (z # map the v) i \<phi>"
      by auto
    \<comment> \<open>the bound variable 0 occurs in @{term \<phi>}, so it gets a defined value\<close>
    from wf Exists.hyps(2) have "pwf_tuple (Suc n) (fv \<phi>) (Some z # v)"
      by (simp add: pwf_tuple_def All_less_Suc2 fvi_Suc)
    moreover from sat have "Formula.sat \<sigma> V (map the (Some z # v)) i \<phi>"
      by simp
    ultimately have "Some z # v \<in> {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
      by simp
    then show "v \<in> tl ` {v. pwf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
      by (rule rev_image_eqI) simp
  qed
  from this finite_imageI[OF IH] show ?case
    by (rule finite_subset)
next
  case (Agg y \<omega> tys f \<phi>)
  define b where [simp]: "b= length tys"
  from Agg have IH: "finite {v. pwf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(auto 0 4 simp add: Suc_le_eq ball_Un Formula.nfv_def intro!: Agg(5)[where ?n="n+(length tys)"] dest!: fvi_plus_bound[where b=0 and c=b, simplified])
  then have IH_alt: "finite (drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>})"
    by(auto)
  have drop_b: "finite (drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}})"
  proof (rule finite_subset)
    show "drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}} \<subseteq> {replicate n None}"
      by (auto simp add: pwf_tuple_def list_eq_iff_nth_eq[where ?ys="replicate n None"])
  qed simp
  have final_subset: "finite (drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"
    using drop_b IH_alt
    by (simp add: conj_disj_distribL Collect_disj_eq image_Un)
  \<comment> \<open>the variable @{term y} does not occur in @{term \<phi>} (shifted by @{term b})\<close>
  have upd_eq: "(zs @ map the (x[y := None])) ! j = (zs @ map the x) ! j"
    if "length zs = b" and "j \<in> fv \<phi>" for x and zs :: Formula.env and j
  proof (cases "j < b")
    case True
    with that(1) show ?thesis
      by (simp add: nth_append)
  next
    case False
    with that Agg.hyps(1) have "y \<noteq> j - b"
      by auto
    with False that(1) show ?thesis
      by (simp add: nth_append map_update)
  qed
  have sat_eq: "Formula.sat \<sigma> V (zs @ map the (x[y := None])) i \<phi> = Formula.sat \<sigma> V (zs @ map the (x)) i \<phi>" if "length zs = b" for x zs
    using that by (intro sat_fv_cong) (simp add: upd_eq)
  have eval_trm_eq: "Formula.eval_trm (zs @ map the (x[y := None])) f = Formula.eval_trm (zs @ map the (x)) f" if "length zs = b" for x zs
    using upd_eq[OF that] Agg.hyps(3) by (intro eval_trm_fv_cong) blast
  let ?M = "\<lambda>u. {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> Formula.sat \<sigma> V (zs @ u) i \<phi> \<and> Formula.eval_trm (zs @ u) f = x} \<and> Zs \<noteq> {}}"
  have sat_Agg: "Formula.sat \<sigma> V u i (Formula.Agg y \<omega> tys f \<phi>) \<longleftrightarrow>
    (?M u = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> u ! y = eval_agg_op \<omega> (?M u)" for u
    by (simp only: Formula.sat.simps Let_def b_def)
  have M_upd: "?M (map the (v[y := None])) = ?M (map the v)" for v
    by (simp only: sat_eq eval_trm_eq cong: conj_cong)
  have fv_Agg: "fv (Formula.Agg y \<omega> tys f \<phi>) = insert y (Formula.fvi b \<phi>)"
    using Agg.hyps(3) by (auto simp: fvi_iff_fv[of _ "length tys"] fvi_trm_iff_fv_trm[of _ "length tys"])
  have y_notin: "y \<notin> Formula.fvi b \<phi>"
    using Agg.hyps(1) by (simp add: fvi_iff_fv[of _ "length tys"])
  have "y < n"
    using fvi_less_nfv[of "Formula.Agg y \<omega> tys f \<phi>"] Agg.prems(2) fv_Agg by fastforce
  \<comment> \<open>a satisfying tuple is determined by its group, i.e., the values of all other variables\<close>
  let ?G = "{w. pwf_tuple n (Formula.fvi b \<phi>) w \<and> (?M (map the w) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b})}"
  let ?g = "\<lambda>w. w[y := Some (eval_agg_op \<omega> (?M (map the w)))]"
  have S_sub: "{v. pwf_tuple n (fv (Formula.Agg y \<omega> tys f \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)}
    \<subseteq> ?g ` ?G"
  proof
    fix v
    assume "v \<in> {v. pwf_tuple n (fv (Formula.Agg y \<omega> tys f \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)}"
    then have wf: "pwf_tuple n (insert y (Formula.fvi b \<phi>)) v"
      and sat: "(?M (map the v) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> map the v ! y = eval_agg_op \<omega> (?M (map the v))"
      unfolding mem_Collect_eq fv_Agg sat_Agg by blast+
    let ?w = "v[y := None]"
    from wf y_notin \<open>y < n\<close> have "pwf_tuple n (Formula.fvi b \<phi>) ?w"
      by (auto simp: pwf_tuple_def nth_list_update)
    moreover from sat have "?M (map the ?w) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}"
      unfolding M_upd by blast
    ultimately have "?w \<in> ?G"
      by blast
    moreover have "?g ?w = v"
    proof -
      from wf \<open>y < n\<close> have "v ! y \<noteq> None"
        by (simp add: pwf_tuple_def)
      with sat pwf_tuple_length[OF wf] \<open>y < n\<close> have vy: "v ! y = Some (eval_agg_op \<omega> (?M (map the v)))"
        by (cases "v ! y") auto
      have "?g ?w = v[y := Some (eval_agg_op \<omega> (?M (map the v)))]"
        by (simp only: list_update_overwrite M_upd)
      also have "\<dots> = v"
        using vy pwf_tuple_length[OF wf] \<open>y < n\<close> by (simp add: list_update_same_conv)
      finally show ?thesis .
    qed
    ultimately show "v \<in> ?g ` ?G"
      by (rule rev_image_eqI[OF _ sym])
  qed
  \<comment> \<open>every group extends to a satisfying tuple of @{term \<phi>}, unless @{term \<phi>} only has the bound variables\<close>
  have G_sub: "?G \<subseteq> drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
  proof
    fix w
    assume "w \<in> ?G"
    then have wf: "pwf_tuple n (Formula.fvi b \<phi>) w" and M: "?M (map the w) = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}"
      unfolding mem_Collect_eq by blast+
    show "w \<in> drop b`{v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
    proof (cases "?M (map the w) = {}")
      case False
      then obtain zs where zs: "length zs = b" "Formula.sat \<sigma> V (zs @ map the w) i \<phi>"
        by auto
      let ?u = "map2 (\<lambda>j z. if j \<in> fv \<phi> then Some z else None) [0..<b] zs @ w"
      have "pwf_tuple (n+b) (fv \<phi>) ?u"
        unfolding pwf_tuple_def
      proof (intro conjI allI impI)
        show "length ?u = n + b"
          using zs(1) pwf_tuple_length[OF wf] by simp
        fix j
        assume "j < n + b"
        show "?u ! j = None \<longleftrightarrow> j \<notin> fv \<phi>"
        proof (cases "j < b")
          case True
          with zs(1) show ?thesis
            by (simp add: nth_append)
        next
          case False
          with \<open>j < n + b\<close> wf have "w ! (j - b) = None \<longleftrightarrow> j - b \<notin> Formula.fvi b \<phi>"
            by (simp add: pwf_tuple_def)
          with False zs(1) show ?thesis
            by (simp add: nth_append fvi_iff_fv[of _ "length tys"])
        qed
      qed
      moreover have "Formula.sat \<sigma> V (map the ?u) i \<phi>"
      proof -
        have "\<forall>j\<in>fv \<phi>. map the ?u ! j = (zs @ map the w) ! j"
          using zs(1) by (auto simp: nth_append)
        then have "Formula.sat \<sigma> V (map the ?u) i \<phi> = Formula.sat \<sigma> V (zs @ map the w) i \<phi>"
          by (rule sat_fv_cong)
        with zs(2) show ?thesis
          by simp
      qed
      ultimately have "?u \<in> {v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
        by blast
      moreover have "drop b ?u = w"
        using zs(1) by simp
      ultimately show ?thesis
        by (rule rev_image_eqI[OF _ sym])
    next
      case True
      with M Agg.hyps(2) have fv_\<phi>: "fv \<phi> = {0..<b}"
        by auto
      then have "Formula.fvi b \<phi> = {}"
        by (auto simp: fvi_iff_fv[of _ "length tys"])
      with wf have w: "w = replicate n None"
        by (simp add: pwf_tuple_empty_iff)
      let ?u = "replicate b (Some undefined) @ w"
      have "pwf_tuple (n+b) (fv \<phi>) ?u"
        using w fv_\<phi> by (auto simp: pwf_tuple_def nth_append)
      with fv_\<phi> have "?u \<in> {v. pwf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})}"
        by blast
      moreover have "drop b ?u = w"
        by simp
      ultimately show ?thesis
        by (rule rev_image_eqI[OF _ sym])
    qed
  qed
  from G_sub final_subset have "finite ?G"
    by (rule finite_subset)
  then have "finite (?g ` ?G)"
    by (rule finite_imageI)
  with S_sub show ?case
    by (rule finite_subset)
next
  case (Prev I \<phi>)
  then have fin: "finite
            {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (i-1) \<phi>}"
    by simp
  have "{v. pwf_tuple n (fv (Formula.Prev I \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Prev I \<phi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (i-1) \<phi>}"
    by (cases i) auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Next I \<phi>)
  then have fin: "finite
     {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (Suc i) \<phi>}"
    by simp
  have "{v. pwf_tuple n (fv (Formula.Next I \<phi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Next I \<phi>)}
    \<subseteq> {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (Suc i) \<phi>}"
    by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  have "fv (Formula.Since \<phi> I \<psi>) = fv \<psi>"
    using Since.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Since \<phi> I \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Since \<phi> I \<psi>)}
    \<subseteq> (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Not_Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  have "fv (Formula.Since (Formula.Neg \<phi>) I \<psi>) = fv \<psi>"
    using Not_Since.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Since (Formula.Neg \<phi>) I \<psi>)) v
      \<and> Formula.sat \<sigma> V (map the v) i (Formula.Since (Formula.Neg \<phi>) I \<psi>)}
    \<subseteq> (\<Union> j\<le>i. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Until \<phi> I \<psi>)
  from Until.prems(1) obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  obtain j where j: "m + \<tau> \<sigma> i \<le> \<tau> \<sigma> j"
    using ex_le_\<tau> by blast
  \<comment> \<open>after @{term j}, the interval has been left\<close>
  have j2_le: "j2 \<le> j" if "memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)" for j2
  proof (rule ccontr)
    assume "\<not> j2 \<le> j"
    then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> j2"
      by (intro \<tau>_mono) simp
    with j have "m \<le> \<tau> \<sigma> j2 - \<tau> \<sigma> i"
      by linarith
    with that m show False
      using memR_antimono by blast
  qed
  from Until have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  have "fv (Formula.Until \<phi> I \<psi>) = fv \<psi>"
    using Until.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Until \<phi> I \<psi>)) v \<and> Formula.sat \<sigma> V (map the v) i (Formula.Until \<phi> I \<psi>)}
    \<subseteq> (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    using j2_le by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Not_Until \<phi> I \<psi>)
  from Not_Until.prems(1) obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  obtain j where j: "m + \<tau> \<sigma> i \<le> \<tau> \<sigma> j"
    using ex_le_\<tau> by blast
  \<comment> \<open>after @{term j}, the interval has been left\<close>
  have j2_le: "j2 \<le> j" if "memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)" for j2
  proof (rule ccontr)
    assume "\<not> j2 \<le> j"
    then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> j2"
      by (intro \<tau>_mono) simp
    with j have "m \<le> \<tau> \<sigma> j2 - \<tau> \<sigma> i"
      by linarith
    with that m show False
      using memR_antimono by blast
  qed
  from Not_Until have "\<forall> j. finite {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have fin: "finite (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  have "fv (Formula.Until (Formula.Neg \<phi>) I \<psi>) = fv \<psi>"
    using Not_Until.hyps(1) by (simp add: Un_absorb1)
  then have "{v. pwf_tuple n (fv (Formula.Until (Formula.Neg \<phi>) I \<psi>)) v
      \<and> Formula.sat \<sigma> V (map the v) i (Formula.Until (Formula.Neg \<phi>) I \<psi>)}
    \<subseteq> (\<Union> j'\<le>j. {v. pwf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    using j2_le by auto
  from this fin show ?case
    by (rule finite_subset)
next
  case (Trigger \<phi> I \<psi>) (* notice the False at the end *)
  let ?sats = "{v. pwf_tuple n (FV (\<phi> \<^bold>T I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>T I \<psi>}"
  have "finite (unit_ptable n)"
    by (auto simp: unit_ptable_def)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Trigger.prems
    by (auto simp: Formula.nfv_def)
  have phi_prptys: "Safety.future_bounded \<phi>" "Formula.nfv \<phi> \<le> n"
    using Trigger.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" 
    and "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}" 
    for j
    using Trigger.hyps(6)[OF phi_prptys Trigger.prems(3,4)]
    Trigger.hyps(7)[OF psi_prptys Trigger.prems(3,4)]
    by auto
  hence "finite ((\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}) \<union> 
    (\<Union>j\<le>i. {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}))" (is "finite ?bigU")
    by auto
  have False
    using Trigger(1) .
  thus ?case
    by blast
next
  case (Trigger_0 \<phi> I \<psi>)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Trigger_0.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" for j
    using Trigger_0.hyps(5)[OF psi_prptys Trigger_0.prems(3,4)]
    by force
  hence "finite (\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>})"
    by auto
  moreover have "{v. pwf_tuple n (FV (\<phi> \<^bold>T I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>T I \<psi>}
    \<subseteq> (\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>})"
    using Trigger_0.hyps
    by (auto simp add: Un_absorb1)
  ultimately show ?case 
    by (elim finite_subset[rotated])
next
  case (Release \<phi> I \<psi>) (* notice the False at the end *)
  let ?sats = "{v. pwf_tuple n (FV (\<phi> \<^bold>R I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>R I \<psi>}"
  have "finite (unit_ptable n)"
    by (auto simp: unit_ptable_def)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Release.prems
    by (auto simp: Formula.nfv_def)
  have phi_prptys: "Safety.future_bounded \<phi>" "Formula.nfv \<phi> \<le> n"
    using Release.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" 
    and "finite {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}" 
    for j
    using Release.hyps(6)[OF phi_prptys Release.prems(3,4)]
    Release.hyps(7)[OF psi_prptys Release.prems(3,4)]
    by auto
  hence "finite ((\<Union>j\<le>i. {v. pwf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}) \<union> 
    (\<Union>j\<le>i. {v. pwf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}))" (is "finite ?bigU")
    by auto
  have False
    using Release(1) .
  thus ?case
    by blast
next
  case (Release_0 \<phi> I \<psi>)
  thus ?case
    using release_fvi
    by (auto simp: Formula.nfv_def sat_release_rewrite_0[OF Release_0(1,2), symmetric])
next
  case (MatchP I r)
  have IH: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> safe_atms r" for k \<phi>
  proof -
    \<comment> \<open>@{term \<phi>} is an atom of @{term r} or the negation of @{term \<phi>} is one\<close>
    from that obtain \<psi> where \<psi>: "\<psi> \<in> Regex.atms r"
      and \<phi>\<psi>: "\<phi> \<in> (if safe_formula \<psi> then {\<psi>} else case \<psi> of Formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
      unfolding safe_atms_def by blast
    from \<phi>\<psi> have "\<phi> = \<psi> \<or> \<psi> = Formula.Neg \<phi>"
      by (cases \<psi> rule: Formula.formula.exhaust) (simp_all split: if_splits)
    then have fv: "fv \<phi> = fv \<psi>" and fb: "Safety.future_bounded \<phi> = Safety.future_bounded \<psi>"
      by auto
    from MatchP.prems(1) \<psi> fb have "Safety.future_bounded \<phi>"
      by (simp add: regex.pred_set)
    moreover have "Formula.nfv \<phi> \<le> n"
    proof -
      have "\<forall>x\<in>fv \<phi>. x < n"
        using fvi_less_nfv_regex[of r] MatchP.prems(2) \<psi> fv by (fastforce simp: fv_regex_alt)
      then show ?thesis
        by (simp add: Formula.nfv_def Suc_le_eq)
    qed
    ultimately show ?thesis
      using MatchP.prems(3,4) by (intro MatchP.hyps(2)[rule_format, OF that]) simp_all
  qed
  from MatchP(3-) show ?case
    by (intro finite_subset[OF _ safe_regex_Past_finite[OF MatchP(1) IH, of i]]) auto
next
  case (MatchF I r)
  from MatchF.prems(1) obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  obtain j where j: "m + \<tau> \<sigma> i \<le> \<tau> \<sigma> j"
    using ex_le_\<tau> by blast
  \<comment> \<open>after @{term j}, the interval has been left\<close>
  have j2_le: "j2 \<le> j" if "memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)" for j2
  proof (rule ccontr)
    assume "\<not> j2 \<le> j"
    then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> j2"
      by (intro \<tau>_mono) simp
    with j have "m \<le> \<tau> \<sigma> j2 - \<tau> \<sigma> i"
      by linarith
    with that m show False
      using memR_antimono by blast
  qed
  have IH: "finite {v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> safe_atms r" for k \<phi>
  proof -
    \<comment> \<open>@{term \<phi>} is an atom of @{term r} or the negation of @{term \<phi>} is one\<close>
    from that obtain \<psi> where \<psi>: "\<psi> \<in> Regex.atms r"
      and \<phi>\<psi>: "\<phi> \<in> (if safe_formula \<psi> then {\<psi>} else case \<psi> of Formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
      unfolding safe_atms_def by blast
    from \<phi>\<psi> have "\<phi> = \<psi> \<or> \<psi> = Formula.Neg \<phi>"
      by (cases \<psi> rule: Formula.formula.exhaust) (simp_all split: if_splits)
    then have fv: "fv \<phi> = fv \<psi>" and fb: "Safety.future_bounded \<phi> = Safety.future_bounded \<psi>"
      by auto
    from MatchF.prems(1) \<psi> fb have "Safety.future_bounded \<phi>"
      by (simp add: regex.pred_set)
    moreover have "Formula.nfv \<phi> \<le> n"
    proof -
      have "\<forall>x\<in>fv \<phi>. x < n"
        using fvi_less_nfv_regex[of r] MatchF.prems(2) \<psi> fv by (fastforce simp: fv_regex_alt)
      then show ?thesis
        by (simp add: Formula.nfv_def Suc_le_eq)
    qed
    ultimately show ?thesis
      using MatchF.prems(3,4) by (intro MatchF.hyps(2)[rule_format, OF that]) simp_all
  qed
  from MatchF(3-) show ?case
    using j2_le by (intro finite_subset[OF _ safe_regex_Future_finite[OF MatchF(1) IH, of i j]]) auto
next
  case (TP t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def 
    by (auto simp add: pwf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
next
  case (TS t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def
    by (auto simp add: pwf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
qed

text \<open>The same for the monitor's tuples, over any list of the free variables.\<close>

lemma safe_formula_finite_dense:
  assumes "safe_formula \<phi>" "Safety.future_bounded \<phi>" "n \<ge> Formula.nfv \<phi>" "\<forall>i. finite (\<Gamma> \<sigma> i)"
    "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
    and cs: "distinct cs" "set cs = fv \<phi>"
  shows "finite {v. wf_tuple cs v \<and> Formula.sat \<sigma> V (val n cs v) i \<phi>}"
    (is "finite ?D")
proof -
  let ?P = "{v. pwf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. map (\<lambda>x. if x \<in> set cs then Some (tup_get cs v x) else None) [0..<n]"
  have lt: "x < n" if "x \<in> set cs" for x
    using that assms(3) cs(2) fvi_less_nfv[of \<phi>] by fastforce
  have "?p v \<in> ?P" if "v \<in> ?D" for v
  proof -
    have "pwf_tuple n (fv \<phi>) (?p v)"
      using cs(2) by (auto simp: pwf_tuple_def)
    moreover have "Formula.sat \<sigma> V (map the (?p v)) i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V (val n cs v) i \<phi>"
      by (rule sat_fv_cong) (use cs(2) lt in auto)
    ultimately show ?thesis
      using that by simp
  qed
  moreover have "inj_on ?p ?D"
  proof (rule inj_onI)
    fix v w
    assume v: "v \<in> ?D" and w: "w \<in> ?D" and eq: "?p v = ?p w"
    have "tup_get cs v c = tup_get cs w c" if "c \<in> set cs" for c
      using arg_cong[OF eq, of "\<lambda>u. u ! c"] lt[OF that] that by simp
    with v w cs(1) show "v = w"
      by (auto intro: wf_tuple_cong)
  qed
  ultimately show ?thesis
    using inj_on_finite[of ?p ?D ?P] safe_formula_finite[OF assms(1-5)] by blast
qed


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
    formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' 
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
        formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' 
          \<and> (\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j) 
        | _ \<Rightarrow> False)"
      then obtain \<phi>' where \<phi>'_props:
        "\<phi> = formula.Neg \<phi>'"
        "safe_formula \<phi>'"
        "\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j"
        by (auto split: formula.splits)
      then have ?thesis using Trigger_0 by auto
    }
    ultimately show ?thesis by blast
  next
    case False
    then show ?thesis using Trigger_0 by (cases \<phi>) (auto)
  qed
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case using progress_release_rewrite_0 by auto
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

unbundle MFODL_no_notation \<comment> \<open> enable notation \<close>

(*<*)
end
(*>*)