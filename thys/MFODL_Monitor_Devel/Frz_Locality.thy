(*<*)
theory Frz_Locality
  imports Formula "HOL-Library.While_Combinator"
begin
(*>*)

section \<open>How far into the past a formula looks\<close>

text \<open>
  The satisfaction of a formula at a time point @{term i} depends on the valuations of the
  predicates only at time points whose timestamp is at most a bounded distance before
  @{term i}'s: the formula's past reach.  Future operators look only forward, and a lower-bounded
  past operator no further back than its interval's upper bound.  The monitor uses this for
  the frozen predicate of @{const Formula.Frz}: a time point older than the reach of every
  verdict still to be computed can be given any value for it.
\<close>

subsection \<open>The upper bound of an interval\<close>

definition ivl_ub :: "\<I> \<Rightarrow> enat" where
  "ivl_ub I = (if bounded I then enat (LEAST t. \<not> memR I t) else \<infinity>)"

lemma memR_less_ivl_ub: "memR I t \<Longrightarrow> enat t < ivl_ub I"
proof (cases "bounded I")
  case True
  then obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  assume t: "memR I t"
  have "\<not> memR I (LEAST t. \<not> memR I t)"
    using m by (rule LeastI)
  then have "t < (LEAST t. \<not> memR I t)"
    using t memR_antimono by (metis not_less)
  then show ?thesis
    using True by (simp add: ivl_ub_def)
qed (simp add: ivl_ub_def)

text \<open>The upper bound is computed by searching for the first time difference outside the
  interval; the search is linear in the bound, and runs once per operator at initialisation.\<close>

lemma while_option_Suc_Least:
  assumes "\<not> P m" "\<forall>t<k. P t" "k \<le> m"
  shows "while_option P Suc k = Some (LEAST t. \<not> P t)"
  using assms(2,3)
proof (induction "m - k" arbitrary: k)
  case 0
  then have "k = m"
    by simp
  with assms(1) 0(2) show ?case
    by (subst while_option_unfold) (auto intro!: Least_equality[symmetric] simp: not_less[symmetric])
next
  case (Suc x)
  show ?case
  proof (cases "P k")
    case True
    have "while_option P Suc (Suc k) = Some (LEAST t. \<not> P t)"
      by (rule Suc.hyps(1)) (use Suc.hyps(2) Suc.prems True in \<open>auto simp: less_Suc_eq\<close>)
    with True show ?thesis
      by (subst while_option_unfold) simp
  next
    case False
    with Suc.prems(1) show ?thesis
      by (subst while_option_unfold) (auto intro!: Least_equality[symmetric] simp: not_less[symmetric])
  qed
qed

lemma ivl_ub_code[code]:
  "ivl_ub I = (if bounded I then enat (the (while_option (memR I) Suc 0)) else \<infinity>)"
proof (cases "bounded I")
  case True
  then obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then have "while_option (memR I) Suc 0 = Some (LEAST t. \<not> memR I t)"
    by (rule while_option_Suc_Least) simp_all
  with True show ?thesis
    by (simp add: ivl_ub_def)
qed (simp add: ivl_ub_def)

subsection \<open>The reach\<close>

primrec regex_reach :: "('a \<Rightarrow> enat) \<Rightarrow> 'a Regex.regex \<Rightarrow> enat" where
  "regex_reach f (Regex.Skip n) = 0"
| "regex_reach f (Regex.Test \<phi>) = f \<phi>"
| "regex_reach f (Regex.Plus r s) = max (regex_reach f r) (regex_reach f s)"
| "regex_reach f (Regex.Times r s) = max (regex_reach f r) (regex_reach f s)"
| "regex_reach f (Regex.Star r) = regex_reach f r"

lemma regex_reach_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>z. z \<in> Regex.atms r \<Longrightarrow> f z = f' z) \<Longrightarrow> regex_reach f r = regex_reach f' r'"
  by (induct r arbitrary: r') auto

lemma regex_reach_upper: "z \<in> Regex.atms r \<Longrightarrow> f z \<le> regex_reach f r"
  by (induct r) (auto simp: le_max_iff_disj)

lemma foldr_max_upper: "x \<in> set l \<Longrightarrow> f x \<le> foldr max (map f l) (0 :: enat)"
  by (induct l) (auto simp: le_max_iff_disj)

function (sequential) past_reach :: "'t Formula.formula \<Rightarrow> enat" where
  "past_reach (Formula.Pred e ts) = 0"
| "past_reach (Formula.Let p \<phi> \<psi>) = past_reach \<phi> + past_reach \<psi>"
| "past_reach (Formula.Frz p \<phi> \<psi>) = max (past_reach \<phi>) (past_reach \<psi>)"
| "past_reach (Formula.LetPast p \<phi> \<psi>) = \<infinity>"
| "past_reach (Formula.Eq t1 t2) = 0"
| "past_reach (Formula.Less t1 t2) = 0"
| "past_reach (Formula.LessEq t1 t2) = 0"
| "past_reach (Formula.Neg \<phi>) = past_reach \<phi>"
| "past_reach (Formula.Or \<phi> \<psi>) = max (past_reach \<phi>) (past_reach \<psi>)"
| "past_reach (Formula.And \<phi> \<psi>) = max (past_reach \<phi>) (past_reach \<psi>)"
| "past_reach (Formula.Ands l) = foldr max (map past_reach l) 0"
| "past_reach (Formula.Exists t \<phi>) = past_reach \<phi>"
| "past_reach (Formula.Agg y \<omega> tys f \<phi>) = past_reach \<phi>"
| "past_reach (Formula.Prev I \<phi>) = ivl_ub I + past_reach \<phi>"
| "past_reach (Formula.Next I \<phi>) = past_reach \<phi>"
| "past_reach (Formula.Since \<phi> I \<psi>) = ivl_ub I + max (past_reach \<phi>) (past_reach \<psi>)"
| "past_reach (Formula.Until \<phi> I \<psi>) = max (past_reach \<phi>) (past_reach \<psi>)"
| "past_reach (Formula.Trigger \<phi> I \<psi>) = ivl_ub I + max (past_reach \<phi>) (past_reach \<psi>)"
| "past_reach (Formula.Release \<phi> I \<psi>) = max (past_reach \<phi>) (past_reach \<psi>)"
| "past_reach (Formula.MatchP I r) = ivl_ub I + regex_reach past_reach r"
| "past_reach (Formula.MatchF I r) = regex_reach past_reach r"
| "past_reach (Formula.TP t) = 0"
| "past_reach (Formula.TS t) = 0"
  by pat_completeness auto
termination
  by (relation "measure size") (auto simp: termination_simp)


subsection \<open>Valuations that agree within a reach\<close>

definition agree_from :: "Formula.trace \<Rightarrow> enat \<Rightarrow> nat \<Rightarrow>
    (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
    (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "agree_from \<sigma> d i V V' \<longleftrightarrow> (\<forall>p. rel_option
     (\<lambda>X X'. \<forall>v k. enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d \<longrightarrow> X v k = X' v k) (V p) (V' p))"

lemma agree_from_shift:
  assumes "agree_from \<sigma> d i V V'" "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> j) + e" "d' + e \<le> d"
  shows "agree_from \<sigma> d' j V V'"
  unfolding agree_from_def
proof
  fix p
  have le: "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d" if "enat (\<tau> \<sigma> j) \<le> enat (\<tau> \<sigma> k) + d'" for k
  proof -
    have "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d' + e"
      using assms(2) that by (metis add.commute add_right_mono order_trans)
    also have "\<dots> \<le> enat (\<tau> \<sigma> k) + d"
      using assms(3) by (metis add.assoc add_left_mono)
    finally show ?thesis .
  qed
  from assms(1)[unfolded agree_from_def, rule_format, of p]
  show "rel_option (\<lambda>X X'. \<forall>v k. enat (\<tau> \<sigma> j) \<le> enat (\<tau> \<sigma> k) + d' \<longrightarrow> X v k = X' v k) (V p) (V' p)"
    by (rule option.rel_mono_strong) (use le in blast)
qed

lemma agree_from_mono:
  assumes "agree_from \<sigma> d i V V'" "d' \<le> d"
  shows "agree_from \<sigma> d' i V V'"
  unfolding agree_from_def
proof
  fix p
  have le: "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d" if "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d'" for k
    using that assms(2) by (meson add_left_mono order_trans)
  from assms(1)[unfolded agree_from_def, rule_format, of p]
  show "rel_option (\<lambda>X X'. \<forall>v k. enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d' \<longrightarrow> X v k = X' v k) (V p) (V' p)"
    by (rule option.rel_mono_strong) (use le in blast)
qed

lemma agree_from_upd:
  "agree_from \<sigma> d i V V' \<Longrightarrow> (\<And>v k. enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d \<Longrightarrow> X v k = X' v k) \<Longrightarrow>
    agree_from \<sigma> d i (V(p \<mapsto> X)) (V'(p \<mapsto> X'))"
  by (auto simp: agree_from_def)

lemma agree_from_infinity: "agree_from \<sigma> \<infinity> i V V' \<Longrightarrow> V = V'"
  unfolding agree_from_def
  by (rule ext, erule_tac x=x in allE) (auto simp: option.rel_sel fun_eq_iff option.expand)

subsection \<open>Regular expressions between two positions\<close>

lemma match_le: "Regex.match t r i j \<Longrightarrow> i \<le> j"
proof (induct r arbitrary: i j)
  case (Star r)
  from Star(2) have "(Regex.match t r)\<^sup>*\<^sup>* i j"
    by simp
  then show ?case
    by (induct rule: rtranclp_induct) (auto dest: Star(1))
qed fastforce+

lemma match_cong_between:
  assumes "\<And>k z. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> z \<in> Regex.atms r \<Longrightarrow> t k z = t' k z"
  shows "Regex.match t r i j = Regex.match t' r i j"
  using assms
proof (induct r arbitrary: i j t t')
  case (Times r s)
  have r: "Regex.match t r i k = Regex.match t' r i k" if "k \<le> j" for k
    by (rule Times(1)) (use Times(3) that in auto)
  have s: "Regex.match t s k j = Regex.match t' s k j" if "i \<le> k" for k
    by (rule Times(2)) (use Times(3) that in auto)
  have "Regex.match t r i k \<and> Regex.match t s k j \<longleftrightarrow> Regex.match t' r i k \<and> Regex.match t' s k j"
    for k
    by (metis match_le r s)
  then show ?case
    by (simp add: OO_def)
next
  case (Star r)
  have one: "(Regex.match t' r)\<^sup>*\<^sup>* i j"
    if st: "(Regex.match t r)\<^sup>*\<^sup>* i j"
      and ag: "\<And>k z. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> z \<in> Regex.atms r \<Longrightarrow> t k z = t' k z"
      and IH: "\<And>i j t t'. (\<And>k z. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> z \<in> Regex.atms r \<Longrightarrow> t k z = t' k z) \<Longrightarrow>
        Regex.match t r i j = Regex.match t' r i j"
    for t t'
  proof -
    have "y \<le> j \<longrightarrow> (Regex.match t' r)\<^sup>*\<^sup>* i y" if "(Regex.match t r)\<^sup>*\<^sup>* i y" for y
      using that
    proof (induct rule: rtranclp_induct)
      case (step y z)
      have iy: "i \<le> y"
        using step(1) by (induct rule: rtranclp_induct) (auto dest: match_le)
      have yz: "y \<le> z"
        using step(2) by (rule match_le)
      show ?case
      proof
        assume "z \<le> j"
        then have "Regex.match t' r y z"
          using IH[of y z t t'] ag iy yz step(2) by auto
        then show "(Regex.match t' r)\<^sup>*\<^sup>* i z"
          using step(3) yz \<open>z \<le> j\<close> by (auto intro: rtranclp.rtrancl_into_rtrancl)
      qed
    qed simp
    then show ?thesis
      using st by blast
  qed
  have ag': "\<And>k z. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> z \<in> Regex.atms r \<Longrightarrow> t' k z = t k z"
    using Star(2) by (simp add: eq_commute[of "t' _ _"])
  have IH': "\<And>i j t t'. (\<And>k z. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> z \<in> Regex.atms r \<Longrightarrow> t k z = t' k z) \<Longrightarrow>
        Regex.match t r i j = Regex.match t' r i j"
    by (rule Star(1)) blast
  show ?case
    using one[of t t', OF _ _ IH'] one[of t' t, OF _ ag' IH'] Star(2)
    by (auto simp del: Regex.match.simps simp: Regex.match.simps(5))
next
  case (Plus r s)
  have "Regex.match t r i j = Regex.match t' r i j"
    by (rule Plus(1)) (use Plus(3) in auto)
  moreover have "Regex.match t s i j = Regex.match t' s i j"
    by (rule Plus(2)) (use Plus(3) in auto)
  ultimately show ?case
    by simp
next
  case (Test x)
  then show ?case
    by auto
qed simp

subsection \<open>Locality\<close>

lemma tau_win:
  assumes "j \<le> k"
  shows "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + enat (\<tau> \<sigma> i - \<tau> \<sigma> j)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k"
    using assms by simp
  then have "\<tau> \<sigma> i \<le> \<tau> \<sigma> k + (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    by arith
  then show ?thesis
    by simp
qed

lemma tau_fwd:
  assumes "i \<le> k"
  shows "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + 0"
  using assms by simp

lemma ub_add_le: "memR I t \<Longrightarrow> ivl_ub I + x \<le> d \<Longrightarrow> x + enat t \<le> d"
  using memR_less_ivl_ub[of I t]
  by (metis add.commute add_left_mono dual_order.trans less_imp_le)

lemma sat_agree_from:
  "past_reach \<phi> \<le> d \<Longrightarrow> agree_from \<sigma> d i V V' \<Longrightarrow> Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V' v i \<phi>"
proof (induction \<phi> arbitrary: V V' v i d)
  case (Pred e ts)
  have "rel_option (\<lambda>X X'. \<forall>v k. enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + d \<longrightarrow> X v k = X' v k)
      (V (e, length ts)) (V' (e, length ts))"
    using Pred.prems(2) unfolding agree_from_def by blast
  then show ?case
    by (cases "V (e, length ts)"; cases "V' (e, length ts)") auto
next
  case (Let p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  have d\<phi>: "past_reach \<phi> + past_reach \<psi> \<le> d"
    using Let.prems(1) by simp
  have ag: "agree_from \<sigma> (past_reach \<psi>) i (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>))
      (V'(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V' w j \<phi>))"
  proof (rule agree_from_upd)
    show "agree_from \<sigma> (past_reach \<psi>) i V V'"
      by (rule agree_from_mono[OF Let.prems(2)]) (use d\<phi> in \<open>metis add.commute le_iff_add order_trans\<close>)
  next
    fix w k
    assume "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + past_reach \<psi>"
    then have "agree_from \<sigma> (past_reach \<phi>) k V V'"
      by (rule agree_from_shift[OF Let.prems(2)]) (use d\<phi> in simp)
    then show "Formula.sat \<sigma> V w k \<phi> = Formula.sat \<sigma> V' w k \<phi>"
      by (rule Let.IH(1)[OF order_refl])
  qed
  show ?case
    using Let.IH(2)[OF order_refl ag] by (simp add: fun_upd_def)
next
  case (Frz p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  have \<phi>: "Formula.sat \<sigma> V w i \<phi> = Formula.sat \<sigma> V' w i \<phi>" for w
    by (rule Frz.IH(1)[OF order_refl agree_from_mono[OF Frz.prems(2)]]) (use Frz.prems(1) in simp)
  have ag: "agree_from \<sigma> (past_reach \<psi>) i (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>))
      (V'(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V' w i \<phi>))"
    by (rule agree_from_upd[OF agree_from_mono[OF Frz.prems(2)]]) (use Frz.prems(1) \<phi> in auto)
  show ?case
    using Frz.IH(2)[OF order_refl ag] by (simp add: fun_upd_def)
next
  case (LetPast p \<phi> \<psi>)
  then have "V = V'"
    by (intro agree_from_infinity) simp
  then show ?case
    by simp
next
  case (Ands l)
  have "Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V' v i \<phi>" if "\<phi> \<in> set l" for \<phi>
  proof (rule Ands.IH[OF that _ Ands.prems(2)])
    show "past_reach \<phi> \<le> d"
      using foldr_max_upper[OF that, of past_reach] Ands.prems(1) by simp
  qed
  then show ?case
    by simp
next
  case (Agg y \<omega> tys f \<phi>)
  have "Formula.sat \<sigma> V u i \<phi> = Formula.sat \<sigma> V' u i \<phi>" for u
    by (rule Agg.IH) (use Agg.prems in simp_all)
  then show ?case
    by simp
next
  case (Prev I \<phi>)
  show ?case
  proof (cases i)
    case (Suc j)
    have "Formula.sat \<sigma> V v j \<phi> = Formula.sat \<sigma> V' v j \<phi>" if "memR I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
      by (rule Prev.IH[OF order_refl agree_from_shift[OF Prev.prems(2) tau_win[OF order_refl]]])
        (use Prev.prems(1) that in \<open>simp add: ub_add_le\<close>)
    then show ?thesis
      using Suc by auto
  qed simp
next
  case (Next I \<phi>)
  have le: "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> (Suc i)) + 0"
    by (rule tau_fwd) simp
  have "Formula.sat \<sigma> V v (Suc i) \<phi> = Formula.sat \<sigma> V' v (Suc i) \<phi>"
    by (rule Next.IH[OF order_refl agree_from_shift[OF Next.prems(2) le]])
      (use Next.prems(1) in simp)
  then show ?case
    by simp
next
  case (Since \<phi> I \<psi>)
  have "(Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma> V' v j \<psi>) \<and>
    (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>)"
    if "j \<le> i" "memR I (\<tau> \<sigma> i - \<tau> \<sigma> j)" for j
  proof (intro conjI ballI)
    show "Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma> V' v j \<psi>"
      by (rule Since.IH(2)[OF order_refl agree_from_shift[OF Since.prems(2) tau_win[OF order_refl]]])
        (use Since.prems(1) that in \<open>auto intro: ub_add_le order_trans[rotated] add_right_mono\<close>)
  next
    fix k assume "k \<in> {j <.. i}"
    then show "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>"
      by (intro Since.IH(1)[OF order_refl agree_from_shift[OF Since.prems(2) tau_win[of j k]]])
        (use Since.prems(1) that in \<open>auto intro: ub_add_le order_trans[rotated] add_right_mono\<close>)
  qed
  then show ?case
    unfolding Formula.sat.simps by (intro ex_cong1) auto
next
  case (Until \<phi> I \<psi>)
  show ?case
    using Until.IH[OF _ agree_from_shift[OF Until.prems(2) tau_fwd]] Until.prems(1)
    by (auto 0 3)
next
  case (Trigger \<phi> I \<psi>)
  have "(Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma> V' v j \<psi>) \<and>
    (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>)"
    if "j \<le> i" "memR I (\<tau> \<sigma> i - \<tau> \<sigma> j)" for j
  proof (intro conjI ballI)
    show "Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma> V' v j \<psi>"
      by (rule Trigger.IH(2)[OF order_refl agree_from_shift[OF Trigger.prems(2) tau_win[OF order_refl]]])
        (use Trigger.prems(1) that in \<open>auto intro: ub_add_le order_trans[rotated] add_right_mono\<close>)
  next
    fix k assume "k \<in> {j <.. i}"
    then show "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>"
      by (intro Trigger.IH(1)[OF order_refl agree_from_shift[OF Trigger.prems(2) tau_win[of j k]]])
        (use Trigger.prems(1) that in \<open>auto intro: ub_add_le order_trans[rotated] add_right_mono\<close>)
  qed
  then show ?case
    unfolding Formula.sat.simps by (intro all_cong1) auto
next
  case (Release \<phi> I \<psi>)
  show ?case
    using Release.IH[OF _ agree_from_shift[OF Release.prems(2) tau_fwd]] Release.prems(1)
    by (auto 0 3)
next
  case (MatchP I r)
  have "Regex.match (Formula.sat \<sigma> V v) r j i = Regex.match (Formula.sat \<sigma> V' v) r j i"
    if "j \<le> i" "memR I (\<tau> \<sigma> i - \<tau> \<sigma> j)" for j
  proof (rule match_cong_between)
    fix k z assume "j \<le> k" "k \<le> i" "z \<in> Regex.atms r"
    then show "Formula.sat \<sigma> V v k z = Formula.sat \<sigma> V' v k z"
      by (intro MatchP.IH[OF _ order_refl agree_from_shift[OF MatchP.prems(2) tau_win[of j k]]])
        (use MatchP.prems(1) that in \<open>auto intro: ub_add_le order_trans[rotated] add_right_mono order_trans[OF regex_reach_upper]\<close>)
  qed
  then show ?case
    by auto
next
  case (MatchF I r)
  have "Regex.match (Formula.sat \<sigma> V v) r i j = Regex.match (Formula.sat \<sigma> V' v) r i j"
    if "i \<le> j" for j
  proof (rule match_cong_between)
    fix k z assume "i \<le> k" "k \<le> j" "z \<in> Regex.atms r"
    then show "Formula.sat \<sigma> V v k z = Formula.sat \<sigma> V' v k z"
      by (intro MatchF.IH[OF _ order_refl agree_from_shift[OF MatchF.prems(2) tau_fwd[of i k]]])
        (use MatchF.prems(1) in \<open>auto intro: order_trans[rotated] order_trans[OF regex_reach_upper]\<close>)
  qed
  then show ?case
    by auto
qed auto


subsection \<open>Formulas without future operators\<close>

text \<open>A formula without future operators, nested freezes, recursive lets and regular expressions.
  Its verdict at a time point i does not wait for input beyond i: once all of its predicates are
  known up to i, so is its verdict (@{text progress_past_only} in @{text Correctness}).  The
  replay of the freeze's body stops at the last pending verdict then.\<close>

fun past_only :: "'t Formula.formula \<Rightarrow> bool" where
  "past_only (Formula.Pred e ts) = True"
| "past_only (Formula.Let p \<phi> \<psi>) = (past_only \<phi> \<and> past_only \<psi>)"
| "past_only (Formula.Eq t1 t2) = True"
| "past_only (Formula.Less t1 t2) = True"
| "past_only (Formula.LessEq t1 t2) = True"
| "past_only (Formula.Neg \<phi>) = past_only \<phi>"
| "past_only (Formula.Or \<phi> \<psi>) = (past_only \<phi> \<and> past_only \<psi>)"
| "past_only (Formula.And \<phi> \<psi>) = (past_only \<phi> \<and> past_only \<psi>)"
| "past_only (Formula.Ands l) = list_all past_only l"
| "past_only (Formula.Exists t \<phi>) = past_only \<phi>"
| "past_only (Formula.Agg y \<omega> tys f \<phi>) = past_only \<phi>"
| "past_only (Formula.Prev I \<phi>) = past_only \<phi>"
| "past_only (Formula.Since \<phi> I \<psi>) = (past_only \<phi> \<and> past_only \<psi>)"
| "past_only (Formula.Trigger \<phi> I \<psi>) = (past_only \<phi> \<and> past_only \<psi>)"
| "past_only (Formula.TP t) = True"
| "past_only (Formula.TS t) = True"
| "past_only _ = False"

end
