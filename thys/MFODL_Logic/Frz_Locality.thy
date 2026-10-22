(*<*)
theory Frz_Locality
  imports Formula
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

subsection \<open>Locality\<close>

lemma tau_fwd:
  assumes "i \<le> k"
  shows "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + 0"
  using assms by simp

lemma frz_win_le:
  assumes "\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i)"
  shows "w \<le> i"
proof (rule ccontr)
  assume "\<not> w \<le> i"
  with assms have "enat (\<tau> \<sigma> i) + d < enat (\<tau> \<sigma> i)"
    by simp
  then show False
    by (simp add: not_less le_iff_add[symmetric])
qed

lemma frz_win_mono:
  assumes "\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i)" "i \<le> i'"
  shows "\<forall>k<w. enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i')"
proof (intro allI impI)
  fix k
  assume "k < w"
  with assms(1) have "enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i)"
    by simp
  also have "\<dots> \<le> enat (\<tau> \<sigma> i')"
    using assms(2) by simp
  finally show "enat (\<tau> \<sigma> k) + d < enat (\<tau> \<sigma> i')" .
qed

lemma ub_add_le: "memR I t \<Longrightarrow> ivl_ub I + x \<le> d \<Longrightarrow> x + enat t \<le> d"
  using memR_le_ivl_ub[of I t]
  by (metis add.commute add_left_mono dual_order.trans)

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
  proof (rule Regex.match_cong_strong)
    fix k z assume "k \<in> {j ..< i + 1}" "z \<in> Regex.atms r"
    then have "j \<le> k" "k \<le> i" "z \<in> Regex.atms r"
      by auto
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
  proof (rule Regex.match_cong_strong)
    fix k z assume "k \<in> {i ..< j + 1}" "z \<in> Regex.atms r"
    then have "i \<le> k" "k \<le> j" "z \<in> Regex.atms r"
      by auto
    then show "Formula.sat \<sigma> V v k z = Formula.sat \<sigma> V' v k z"
      by (intro MatchF.IH[OF _ order_refl agree_from_shift[OF MatchF.prems(2) tau_fwd[of i k]]])
        (use MatchF.prems(1) in \<open>auto intro: order_trans[rotated] order_trans[OF regex_reach_upper]\<close>)
  qed
  then show ?case
    by auto
qed auto


section \<open>A frozen predicate read only at the formula's own first variables\<close>

text \<open>
  A predicate @{term pn} of arity @{term m} is \<^emph>\<open>separable\<close> in a formula if it occurs there
  only applied to the formula's first @{term m} variables, in that order, under no quantifier and
  in no definition of a bound predicate.  The formula's satisfaction at a valuation then reads the
  predicate only at one tuple, the valuation's first @{term m} values: two interpretations of the
  predicate that agree on that tuple at all time points give the same satisfaction.  The monitor
  uses this for @{const Formula.Frz}: the body can be evaluated once with any table of the frozen
  predicate that contains the frozen one, and the verdicts restricted to the frozen tuples.
\<close>

fun key_sep :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "key_sep pn (Formula.Pred e ts) = ((e, length ts) = pn \<longrightarrow> ts = map Formula.Var [0..<length ts])"
| "key_sep pn (Formula.Let e \<phi> \<psi>) =
     (\<not> Formula.contains_pred pn \<phi> \<and> ((e, Formula.nfv \<phi>) = pn \<or> key_sep pn \<psi>))"
| "key_sep pn (Formula.Frz e \<phi> \<psi>) =
     (\<not> Formula.contains_pred pn \<phi> \<and> ((e, Formula.nfv \<phi>) = pn \<or> key_sep pn \<psi>))"
| "key_sep pn (Formula.LetPast e \<phi> \<psi>) =
     ((e, Formula.nfv \<phi>) = pn \<or> (\<not> Formula.contains_pred pn \<phi> \<and> key_sep pn \<psi>))"
| "key_sep pn (Formula.Neg \<phi>) = key_sep pn \<phi>"
| "key_sep pn (Formula.Or \<phi> \<psi>) = (key_sep pn \<phi> \<and> key_sep pn \<psi>)"
| "key_sep pn (Formula.And \<phi> \<psi>) = (key_sep pn \<phi> \<and> key_sep pn \<psi>)"
| "key_sep pn (Formula.Ands l) = (\<forall>\<phi> \<in> set l. key_sep pn \<phi>)"
| "key_sep pn (Formula.Exists t \<phi>) = (\<not> Formula.contains_pred pn \<phi>)"
| "key_sep pn (Formula.Agg y \<omega> tys f \<phi>) = (\<not> Formula.contains_pred pn \<phi>)"
| "key_sep pn (Formula.Prev I \<phi>) = key_sep pn \<phi>"
| "key_sep pn (Formula.Next I \<phi>) = key_sep pn \<phi>"
| "key_sep pn (Formula.Since \<phi> I \<psi>) = (key_sep pn \<phi> \<and> key_sep pn \<psi>)"
| "key_sep pn (Formula.Until \<phi> I \<psi>) = (key_sep pn \<phi> \<and> key_sep pn \<psi>)"
| "key_sep pn (Formula.Trigger \<phi> I \<psi>) = (key_sep pn \<phi> \<and> key_sep pn \<psi>)"
| "key_sep pn (Formula.Release \<phi> I \<psi>) = (key_sep pn \<phi> \<and> key_sep pn \<psi>)"
| "key_sep pn (Formula.MatchP I r) = (\<forall>\<phi> \<in> Regex.atms r. key_sep pn \<phi>)"
| "key_sep pn (Formula.MatchF I r) = (\<forall>\<phi> \<in> Regex.atms r. key_sep pn \<phi>)"
| "key_sep pn _ = True"

text \<open>The tuple of a valuation at which a separable predicate of arity @{term m} is read.\<close>

abbreviation sep_key :: "nat \<Rightarrow> Formula.env \<Rightarrow> event_data list" where
  "sep_key m v \<equiv> map ((!) v) [0..<m]"

lemma val_sep_key:
  assumes "m \<le> n"
  shows "val m cs x = sep_key m (val n cs x)"
  using assms by (auto simp: val_def)

lemma sat_not_contains_agree:
  assumes "\<not> Formula.contains_pred q \<phi>" "\<And>q'. q' \<noteq> q \<Longrightarrow> V q' = V' q'"
  shows "Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V' v i \<phi>"
proof -
  have "V(q \<mapsto> undefined) = V'(q \<mapsto> undefined)"
    using assms(2) by (auto simp: fun_eq_iff)
  then show ?thesis
    using not_contains_pred_sat[OF assms(1), of \<sigma> V undefined v i, symmetric]
      not_contains_pred_sat[OF assms(1), of \<sigma> V' undefined v i, symmetric] by simp
qed

lemma sat_key_sep_gen:
  assumes "key_sep (p, m) \<psi>" "V (p, m) = Some X" "V' (p, m) = Some X'"
    "\<And>q. q \<noteq> (p, m) \<Longrightarrow> V q = V' q" "\<And>k. X (sep_key m v) k = X' (sep_key m v) k"
  shows "Formula.sat \<sigma> V v i \<psi> = Formula.sat \<sigma> V' v i \<psi>"
  using assms
proof (induction \<psi> arbitrary: V V' X X' i)
  case (Pred e ts)
  show ?case
  proof (cases "(e, length ts) = (p, m)")
    case True
    then have "ts = map Formula.Var [0..<m]"
      using Pred by simp
    then show ?thesis
      using True Pred.prems by (simp add: comp_def)
  next
    case False
    then show ?thesis
      using Pred.prems(4)[OF False] by simp
  qed
next
  case (Let e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  have \<phi>: "Formula.sat \<sigma> V w j \<phi> = Formula.sat \<sigma> V' w j \<phi>" for w j
    using Let.prems(1,4) by (intro sat_not_contains_agree[of "(p, m)"]) auto
  show ?case
  proof (cases "?en = (p, m)")
    case True
    have "V(?en \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>) = V'(?en \<mapsto> \<lambda>w j. Formula.sat \<sigma> V' w j \<phi>)"
      using Let.prems(4) True by (auto simp: fun_eq_iff \<phi>)
    then show ?thesis
      by simp
  next
    case False
    then have "key_sep (p, m) \<psi>"
      using Let.prems(1) by auto
    have eqF: "(\<lambda>w j. Formula.sat \<sigma> V w j \<phi>) = (\<lambda>w j. Formula.sat \<sigma> V' w j \<phi>)"
      using \<phi> by auto
    show ?thesis
      unfolding Formula.sat.simps eqF
      by (rule Let.IH(2)[OF \<open>key_sep (p, m) \<psi>\<close>, where X=X and X'=X']) (use Let.prems(2-5) False in auto)
  qed
next
  case (Frz e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  have \<phi>: "Formula.sat \<sigma> V w j \<phi> = Formula.sat \<sigma> V' w j \<phi>" for w j
    using Frz.prems(1,4) by (intro sat_not_contains_agree[of "(p, m)"]) auto
  show ?case
  proof (cases "?en = (p, m)")
    case True
    have "V(?en \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w i \<phi>) = V'(?en \<mapsto> \<lambda>w j. Formula.sat \<sigma> V' w i \<phi>)"
      using Frz.prems(4) True by (auto simp: fun_eq_iff \<phi>)
    then show ?thesis
      by simp
  next
    case False
    then have "key_sep (p, m) \<psi>"
      using Frz.prems(1) by auto
    have eqF: "(\<lambda>w j. Formula.sat \<sigma> V w i \<phi>) = (\<lambda>w j. Formula.sat \<sigma> V' w i \<phi>)"
      using \<phi> by auto
    show ?thesis
      unfolding Formula.sat.simps eqF
      by (rule Frz.IH(2)[OF \<open>key_sep (p, m) \<psi>\<close>, where X=X and X'=X']) (use Frz.prems(2-5) False in auto)
  qed
next
  case (LetPast e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  show ?case
  proof (cases "?en = (p, m)")
    case True
    have "V(?en \<mapsto> Z) = V'(?en \<mapsto> Z)" for Z
      using LetPast.prems(4) True by (auto simp: fun_eq_iff)
    then show ?thesis
      by (simp add: Let_def)
  next
    case False
    then have \<psi>: "key_sep (p, m) \<psi>" and n\<phi>: "\<not> Formula.contains_pred (p, m) \<phi>"
      using LetPast.prems(1) by auto
    have \<phi>: "Formula.sat \<sigma> (V(?en \<mapsto> Z)) w j \<phi> = Formula.sat \<sigma> (V'(?en \<mapsto> Z)) w j \<phi>" for Z w j
      using n\<phi> LetPast.prems(4) by (intro sat_not_contains_agree[of "(p, m)"]) auto
    define F where "F = letpast_sat (\<lambda>Z u k. Formula.sat \<sigma> (V(?en \<mapsto> Z)) u k \<phi>)"
    have F': "letpast_sat (\<lambda>Z u k. Formula.sat \<sigma> (V'(?en \<mapsto> Z)) u k \<phi>) = F"
      unfolding F_def \<phi> ..
    show ?thesis
      unfolding Formula.sat.simps Let_def F' F_def[symmetric]
      by (rule LetPast.IH(2)[OF \<psi>, where X=X and X'=X']) (use LetPast.prems(2-5) False in auto)
  qed
next
  case (Exists t \<phi>)
  then show ?case
    using sat_not_contains_agree[of "(p, m)" \<phi> V V'] by simp
next
  case (Agg y \<omega> tys f \<phi>)
  then show ?case
    using sat_not_contains_agree[of "(p, m)" \<phi> V V'] by simp
next
  case (MatchP I r)
  have "Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat \<sigma> V' v) r"
  proof (rule match_cong[OF refl])
    fix k z
    assume "z \<in> Regex.atms r"
    then show "Formula.sat \<sigma> V v k z = Formula.sat \<sigma> V' v k z"
      using MatchP.prems by (intro MatchP.IH[where X=X and X'=X']) auto
  qed
  then show ?case
    by simp
next
  case (MatchF I r)
  have "Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat \<sigma> V' v) r"
  proof (rule match_cong[OF refl])
    fix k z
    assume "z \<in> Regex.atms r"
    then show "Formula.sat \<sigma> V v k z = Formula.sat \<sigma> V' v k z"
      using MatchF.prems by (intro MatchF.IH[where X=X and X'=X']) auto
  qed
  then show ?case
    by simp
next
  case (Ands l)
  have "Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V' v i \<phi>" if "\<phi> \<in> set l" for \<phi>
    by (rule Ands.IH[OF that, where X=X and X'=X']) (use Ands.prems that in simp_all)
  then show ?case
    by simp
next
  case (Since \<phi> I \<psi>)
  have "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>" for k
    by (rule Since.IH(1)[where X=X and X'=X']) (use Since.prems in simp_all)
  moreover have "Formula.sat \<sigma> V v k \<psi> = Formula.sat \<sigma> V' v k \<psi>" for k
    by (rule Since.IH(2)[where X=X and X'=X']) (use Since.prems in simp_all)
  ultimately show ?case
    by simp
next
  case (Until \<phi> I \<psi>)
  have "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>" for k
    by (rule Until.IH(1)[where X=X and X'=X']) (use Until.prems in simp_all)
  moreover have "Formula.sat \<sigma> V v k \<psi> = Formula.sat \<sigma> V' v k \<psi>" for k
    by (rule Until.IH(2)[where X=X and X'=X']) (use Until.prems in simp_all)
  ultimately show ?case
    by simp
next
  case (Trigger \<phi> I \<psi>)
  have "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>" for k
    by (rule Trigger.IH(1)[where X=X and X'=X']) (use Trigger.prems in simp_all)
  moreover have "Formula.sat \<sigma> V v k \<psi> = Formula.sat \<sigma> V' v k \<psi>" for k
    by (rule Trigger.IH(2)[where X=X and X'=X']) (use Trigger.prems in simp_all)
  ultimately show ?case
    by simp
next
  case (Release \<phi> I \<psi>)
  have "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>" for k
    by (rule Release.IH(1)[where X=X and X'=X']) (use Release.prems in simp_all)
  moreover have "Formula.sat \<sigma> V v k \<psi> = Formula.sat \<sigma> V' v k \<psi>" for k
    by (rule Release.IH(2)[where X=X and X'=X']) (use Release.prems in simp_all)
  ultimately show ?case
    by simp
next
  case (Or \<phi> \<psi>)
  have "Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V' v i \<phi>"
    by (rule Or.IH(1)[where X=X and X'=X']) (use Or.prems in simp_all)
  moreover have "Formula.sat \<sigma> V v i \<psi> = Formula.sat \<sigma> V' v i \<psi>"
    by (rule Or.IH(2)[where X=X and X'=X']) (use Or.prems in simp_all)
  ultimately show ?case
    by simp
next
  case (And \<phi> \<psi>)
  have "Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V' v i \<phi>"
    by (rule And.IH(1)[where X=X and X'=X']) (use And.prems in simp_all)
  moreover have "Formula.sat \<sigma> V v i \<psi> = Formula.sat \<sigma> V' v i \<psi>"
    by (rule And.IH(2)[where X=X and X'=X']) (use And.prems in simp_all)
  ultimately show ?case
    by simp
next
  case (Neg \<phi>)
  have "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>" for k
    by (rule Neg.IH[where X=X and X'=X']) (use Neg.prems in simp_all)
  then show ?case
    by (simp split: nat.splits)
next
  case (Prev I \<phi>)
  have "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>" for k
    by (rule Prev.IH[where X=X and X'=X']) (use Prev.prems in simp_all)
  then show ?case
    by (simp split: nat.splits)
next
  case (Next I \<phi>)
  have "Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma> V' v k \<phi>" for k
    by (rule Next.IH[where X=X and X'=X']) (use Next.prems in simp_all)
  then show ?case
    by (simp split: nat.splits)
qed simp_all

lemma sat_key_sep:
  assumes "key_sep (p, m) \<psi>" "\<And>k. X (sep_key m v) k = X' (sep_key m v) k"
  shows "Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<psi> = Formula.sat \<sigma> (V((p, m) \<mapsto> X')) v i \<psi>"
  by (rule sat_key_sep_gen[where X=X and X'=X', OF assms(1)]) (use assms(2) in auto)

text \<open>The verdict of a freeze at a valuation is that of its body with any interpretation of the
  frozen predicate that agrees with the frozen value on the valuation's tuple, from a time point
  beyond the body's past reach on.\<close>

lemma sat_Frz_sep:
  assumes sep: "key_sep (p, Formula.nfv \<phi>) \<psi>"
    and agree: "\<And>k. w \<le> k \<Longrightarrow> Q (sep_key (Formula.nfv \<phi>) v) k = Formula.sat \<sigma> V (sep_key (Formula.nfv \<phi>) v) i \<phi>"
    and win: "\<forall>k<w. enat (\<tau> \<sigma> k) + past_reach \<psi> < enat (\<tau> \<sigma> i)"
  shows "Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> Q)) v i \<psi> = Formula.sat \<sigma> V v i (Formula.Frz p \<phi> \<psi>)"
proof -
  let ?pn = "(p, Formula.nfv \<phi>)"
  define Q' where "Q' = (\<lambda>u k. if k < w then Q u k else Formula.sat \<sigma> V u i \<phi>)"
  have "Formula.sat \<sigma> (V(?pn \<mapsto> Q)) v i \<psi> = Formula.sat \<sigma> (V(?pn \<mapsto> Q')) v i \<psi>"
    by (rule sat_key_sep[OF sep]) (auto simp: Q'_def agree)
  also have "\<dots> = Formula.sat \<sigma> (V(?pn \<mapsto> \<lambda>u k. Formula.sat \<sigma> V u i \<phi>)) v i \<psi>"
  proof (rule sat_agree_from[OF order_refl])
    show "agree_from \<sigma> (past_reach \<psi>) i (V(?pn \<mapsto> Q')) (V(?pn \<mapsto> \<lambda>u k. Formula.sat \<sigma> V u i \<phi>))"
    proof (rule agree_from_upd)
      show "agree_from \<sigma> (past_reach \<psi>) i V V"
        by (auto simp: agree_from_def option.rel_refl)
    next
      fix u k
      assume "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + past_reach \<psi>"
      then have "w \<le> k"
        using win by (meson leD leI)
      then show "Q' u k = Formula.sat \<sigma> V u i \<phi>"
        by (simp add: Q'_def)
    qed
  qed
  finally show ?thesis
    by simp
qed

text \<open>A verdict computed with the frozen predicate empty before a time point @{term w} is the
  verdict of the freeze, provided @{term w} lies beyond the reach of the body.\<close>

lemma qtable_Frz_window:
  assumes q: "qtable cs R (\<lambda>v. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> Q)) (val n cs v) i \<psi>) X"
    and agree: "\<And>v k. w \<le> k \<Longrightarrow> Q v k = Formula.sat \<sigma> V v i \<phi>"
    and win: "\<forall>k<w. enat (\<tau> \<sigma> k) + past_reach \<psi> < enat (\<tau> \<sigma> i)"
  shows "qtable cs R (\<lambda>v. Formula.sat \<sigma> V (val n cs v) i (Formula.Frz p \<phi> \<psi>)) X"
proof -
  let ?pn = "(p, Formula.nfv \<phi>)"
  have ag: "agree_from \<sigma> (past_reach \<psi>) i (V(?pn \<mapsto> Q)) (V(?pn \<mapsto> \<lambda>v k. Formula.sat \<sigma> V v i \<phi>))"
    unfolding agree_from_def
  proof
    fix pn'
    show "rel_option (\<lambda>X X'. \<forall>v k. enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + past_reach \<psi> \<longrightarrow> X v k = X' v k)
      ((V(?pn \<mapsto> Q)) pn') ((V(?pn \<mapsto> \<lambda>v k. Formula.sat \<sigma> V v i \<phi>)) pn')"
    proof (cases "pn' = ?pn")
      case True
      have "w \<le> k" if "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + past_reach \<psi>" for k
        using win that by (meson leD leI)
      with True agree show ?thesis
        by auto
    next
      case False
      then show ?thesis
        by (cases "V pn'") auto
    qed
  qed
  have "Formula.sat \<sigma> (V(?pn \<mapsto> Q)) u i \<psi> \<longleftrightarrow> Formula.sat \<sigma> (V(?pn \<mapsto> \<lambda>v k. Formula.sat \<sigma> V v i \<phi>)) u i \<psi>" for u
    by (rule sat_agree_from[OF order_refl ag])
  then show ?thesis
    using q by (auto intro: qtable_cong[OF _ refl])
qed

text \<open>A separable predicate that occurs is applied to the formula's free variables.\<close>

lemma key_sep_fv:
  "key_sep (p, m) \<psi> \<Longrightarrow> Formula.contains_pred (p, m) \<psi> \<Longrightarrow> {0..<m} \<subseteq> Formula.fv \<psi>"
proof (induction \<psi>)
  case (Pred e ts)
  then have ts: "ts = map Formula.Var [0..<m]"
    by auto
  show ?case
  proof
    fix x
    assume "x \<in> {0..<m}"
    then have "Formula.Var x \<in> set ts"
      using ts by auto
    then show "x \<in> Formula.fv (Formula.Pred e ts)"
      by force
  qed
next
  case (Let e \<phi> \<psi>)
  then show ?case
    by (auto split: if_splits)
next
  case (Frz e \<phi> \<psi>)
  then show ?case
    by (auto split: if_splits)
next
  case (LetPast e \<phi> \<psi>)
  then show ?case
    by (auto simp: Let_def split: if_splits)
next
  case (MatchP I r)
  then show ?case
    by (auto simp: Regex.fv_regex_alt)
next
  case (MatchF I r)
  then show ?case
    by (auto simp: Regex.fv_regex_alt)
qed auto

text \<open>The combination of the two copies' rows at a time point @{term i}: the first copy's tuples
  whose frozen tuple is in the frozen table of @{term i}, the second copy's others.  The first
  copy's frozen predicate holds the frozen table's tuples (and maybe others), the second's none,
  from points beyond the body's reach on.\<close>

lemma qtable_frz_cmb:
  assumes sep: "key_sep (p, Formula.nfv \<phi>) \<psi>" and cont: "Formula.contains_pred (p, Formula.nfv \<phi>) \<psi>"
    and fvn: "\<forall>x \<in> Formula.fv \<psi>. x < n"
    and \<alpha>: "\<alpha> = {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>}"
    and S: "sat_table \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> QS)) n R (Formula.fv_list \<psi>) i \<psi> yS"
    and E: "sat_table \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> QE)) n R (Formula.fv_list \<psi>) i \<psi> yE"
    and agS: "\<And>u k. wS \<le> k \<Longrightarrow> u \<in> \<alpha> \<Longrightarrow> QS u k"
    and agE: "\<And>u k. wE \<le> k \<Longrightarrow> \<not> QE u k"
    and winS: "\<forall>k<wS. enat (\<tau> \<sigma> k) + past_reach \<psi> < enat (\<tau> \<sigma> i)"
    and winE: "\<forall>k<wE. enat (\<tau> \<sigma> k) + past_reach \<psi> < enat (\<tau> \<sigma> i)"
  shows "sat_table \<sigma> V n R (Formula.fv_list \<psi>) i (Formula.Frz p \<phi> \<psi>)
    ({x \<in> yS. val (Formula.nfv \<phi>) (Formula.fv_list \<psi>) x \<in> \<alpha>} \<union> {x \<in> yE. val (Formula.nfv \<phi>) (Formula.fv_list \<psi>) x \<notin> \<alpha>})"
proof -
  let ?m = "Formula.nfv \<phi>"
  let ?cs = "Formula.fv_list \<psi>"
  let ?pn = "(p, ?m)"
  have mn: "?m \<le> n"
  proof (cases "?m = 0")
    case False
    then have "?m - 1 \<in> Formula.fv \<psi>"
      using key_sep_fv[OF sep cont] by auto
    then show ?thesis
      using fvn False by fastforce
  qed simp
  have key: "val ?m ?cs x = sep_key ?m (val n ?cs x)" for x
    by (rule val_sep_key[OF mn])
  have satS: "Formula.sat \<sigma> (V(?pn \<mapsto> QS)) v i \<psi> = Formula.sat \<sigma> V v i (Formula.Frz p \<phi> \<psi>)"
    if "sep_key ?m v \<in> \<alpha>" for v
    by (rule sat_Frz_sep[OF sep _ winS]) (use that agS \<alpha> in auto)
  have satE: "Formula.sat \<sigma> (V(?pn \<mapsto> QE)) v i \<psi> = Formula.sat \<sigma> V v i (Formula.Frz p \<phi> \<psi>)"
    if "sep_key ?m v \<notin> \<alpha>" for v
    by (rule sat_Frz_sep[OF sep _ winE]) (use that agE \<alpha> in auto)
  show ?thesis
    unfolding qtable_iff
  proof (intro conjI allI impI)
    show "table ?cs ({x \<in> yS. val ?m ?cs x \<in> \<alpha>} \<union> {x \<in> yE. val ?m ?cs x \<notin> \<alpha>})"
      using qtableD(1)[OF S] qtableD(1)[OF E] by (auto simp: table_def)
    show "finite ({x \<in> yS. val ?m ?cs x \<in> \<alpha>} \<union> {x \<in> yE. val ?m ?cs x \<notin> \<alpha>})"
      using qtableD(5)[OF S] qtableD(5)[OF E] by simp
  next
    fix x
    assume r: "mem_restr R ?cs x"
    show "x \<in> {x \<in> yS. val ?m ?cs x \<in> \<alpha>} \<union> {x \<in> yE. val ?m ?cs x \<notin> \<alpha>} \<longleftrightarrow>
      Formula.sat \<sigma> V (val n ?cs x) i (Formula.Frz p \<phi> \<psi>) \<and> wf_tuple ?cs x"
    proof (cases "val ?m ?cs x \<in> \<alpha>")
      case True
      then show ?thesis
        using S r satS[of "val n ?cs x"] by (auto simp: key qtable_iff)
    next
      case False
      then show ?thesis
        using E r satE[of "val n ?cs x"] by (auto simp: key qtable_iff)
    qed
  qed
qed

subsection \<open>Interpretations of a frozen predicate by replay\<close>

text \<open>A valuation of a frozen predicate given by the time point whose frozen value it holds at
  each time point, if any (@{term frz_val}): the monitor replays a freeze with the frozen predicate
  interpreted in this way before the start of its window.\<close>

definition frz_val :: "Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
    ty Formula.formula \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> bool" where
  "frz_val \<sigma> V \<phi> L = (\<lambda>v k. case L k of None \<Rightarrow> False | Some i \<Rightarrow> Formula.sat \<sigma> V v i \<phi>)"

text \<open>A copy of the replay base for the frozen table of time point @{term i}: the frozen predicate
  holds that table from @{term w} on, and whatever the replay base absorbed before.\<close>

abbreviation frz_cv where
  "frz_cv \<sigma> V \<phi> N w i \<equiv> frz_val \<sigma> V \<phi> (\<lambda>k. if k < w then N k else Some i)"

lemma frz_cv_ge: "w \<le> k \<Longrightarrow> frz_cv \<sigma> V \<phi> N w i v k = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: frz_val_def)

lemma frz_val_sat: "frz_val \<sigma> V \<phi> L v k \<Longrightarrow> \<exists>i. Formula.sat \<sigma> V v i \<phi>"
  by (auto simp: frz_val_def split: option.splits)

text \<open>The replay base has absorbed the time points before its window's start @{term w}; what the
  frozen predicate holds from @{term w} on does not matter for its state, as long as it holds
  only tuples of the frozen formula (@{term frz_sup}): the copies of the separable evaluation give
  it a union of frozen tables, or the empty table.\<close>

definition frz_sup :: "Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
    ty Formula.formula \<Rightarrow> (Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "frz_sup \<sigma> V \<phi> M \<longleftrightarrow> (\<forall>v k. M v k \<longrightarrow> (\<exists>i. Formula.sat \<sigma> V v i \<phi>))"

definition frz_ext :: "Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
    ty Formula.formula \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> (Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
    Formula.env \<Rightarrow> nat \<Rightarrow> bool" where
  "frz_ext \<sigma> V \<phi> N w M = (\<lambda>v k. if k < w then frz_val \<sigma> V \<phi> N v k else M v k)"

lemma frz_sup_sat: "frz_sup \<sigma> V \<phi> (\<lambda>v k. Formula.sat \<sigma> V v i \<phi>)"
  by (auto simp: frz_sup_def)

lemma frz_sup_False: "frz_sup \<sigma> V \<phi> (\<lambda>_ _. False)"
  by (simp add: frz_sup_def)

lemma frz_sup_val: "frz_sup \<sigma> V \<phi> (frz_val \<sigma> V \<phi> L)"
  by (auto simp: frz_sup_def dest: frz_val_sat)

lemma frz_ext_sat: "frz_ext \<sigma> V \<phi> N w M v k \<Longrightarrow> frz_sup \<sigma> V \<phi> M \<Longrightarrow> \<exists>i. Formula.sat \<sigma> V v i \<phi>"
  by (auto simp: frz_ext_def frz_sup_def split: if_splits dest: frz_val_sat)

lemma frz_ext_cv: "frz_ext \<sigma> V \<phi> N w (\<lambda>v k. Formula.sat \<sigma> V v i \<phi>) = frz_cv \<sigma> V \<phi> N w i"
  by (auto simp: frz_ext_def frz_val_def fun_eq_iff)

lemma frz_ext_ge: "w \<le> k \<Longrightarrow> frz_ext \<sigma> V \<phi> N w M v k = M v k"
  by (simp add: frz_ext_def)

lemma frz_ext_val: "frz_ext \<sigma> V \<phi> N w (frz_val \<sigma> V \<phi> M) = frz_val \<sigma> V \<phi> (\<lambda>k. if k < w then N k else M k)"
  by (auto simp: frz_ext_def frz_val_def fun_eq_iff)

lemma frz_ext_False: "frz_ext \<sigma> V \<phi> N w (\<lambda>_ _. False) = frz_val \<sigma> V \<phi> (\<lambda>k. if k < w then N k else None)"
  by (auto simp: frz_ext_def frz_val_def fun_eq_iff)

text \<open>A table of the separable evaluation: finite, and holding tuples of the frozen formula.\<close>

definition frz_tab :: "Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
    ty Formula.formula \<Rightarrow> event_data list set \<Rightarrow> bool" where
  "frz_tab \<sigma> V m \<phi> L \<longleftrightarrow> finite L \<and> (\<forall>v \<in> L. length v = m \<and> (\<exists>i. Formula.sat \<sigma> V v i \<phi>))"

lemma frz_tab_empty[simp]: "frz_tab \<sigma> V m \<phi> {}"
  by (simp add: frz_tab_def)

lemma frz_tab_Un: "frz_tab \<sigma> V m \<phi> A \<Longrightarrow> frz_tab \<sigma> V m \<phi> B \<Longrightarrow> frz_tab \<sigma> V m \<phi> (A \<union> B)"
  by (auto simp: frz_tab_def)

lemma frz_tab_sup: "frz_tab \<sigma> V m \<phi> L \<Longrightarrow> frz_sup \<sigma> V \<phi> (\<lambda>v k. v \<in> L)"
  by (auto simp: frz_tab_def frz_sup_def)

end
