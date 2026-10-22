(*<*)
theory Share_Rewrite
  imports "MFODL_Monitor.Monitor" "MFODL_Logic.Typing"
begin
(*>*)



section \<open>The right operand of a release, evaluated once\<close>

text \<open>
  VeriMon's multiway conversion (@{const convert_multiway}) turns a release with 0 in its
  interval into a release whose left operand is the conjunction with the right operand, and the
  monitor evaluates a release without 0 by the formula that defines it in terms of the past and
  future operators (@{const and_release_safe_bounded}); both contain the right operand several
  times, each copy a subformula of its own that the monitor evaluates.  Binding the right operand
  with @{const Formula.Let} to a predicate that occurs nowhere else, and releasing that
  predicate, has it evaluated once.  The theory @{text Prepare} applies the rewrite before the
  multiway conversion.
\<close>

subsection \<open>The rewrite\<close>

text \<open>Whether a formula mentions a predicate, bound or not.\<close>

fun occurs :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "occurs pn (Formula.Pred e ts) = ((e, length ts) = pn)"
| "occurs pn (Formula.Let e \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Frz e \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.LetPast e \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Neg \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Or \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.And \<phi> \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Ands l) = (\<exists>\<phi>\<in>set l. occurs pn \<phi>)"
| "occurs pn (Formula.Exists t \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Agg y \<omega> tys f \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Prev I \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Next I \<phi>) = occurs pn \<phi>"
| "occurs pn (Formula.Since \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Until \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Trigger \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.Release \<phi> I \<psi>) = (occurs pn \<phi> \<or> occurs pn \<psi>)"
| "occurs pn (Formula.MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. occurs pn \<phi>)"
| "occurs pn (Formula.MatchF I r) = (\<exists>\<phi>\<in>Regex.atms r. occurs pn \<phi>)"
| "occurs pn _ = False"

definition shr :: Formula.name where
  "shr = string8_literal STR ''__release''"

definition share_ok :: "'t Formula.formula \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "share_ok \<alpha> \<psi> = ((\<forall>x\<in>{0..<Formula.nfv \<psi>}. x \<in> Formula.fv \<psi>) \<and> \<not> occurs (shr, Formula.nfv \<psi>) \<alpha> \<and>
     (case \<psi> of Formula.Pred _ _ \<Rightarrow> False | _ \<Rightarrow> True))"

definition shr_pred :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "shr_pred \<psi> = Formula.Pred shr (map Formula.Var [0..<Formula.nfv \<psi>])"

fun share_rw :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "share_rw (Formula.And \<alpha> (Formula.Release \<phi> I \<psi>)) = (let \<alpha>' = share_rw \<alpha>; \<phi>' = share_rw \<phi>; \<psi>' = share_rw \<psi> in
     if share_ok (Formula.And \<alpha>' \<phi>') \<psi>'
     then Formula.Let shr \<psi>' (Formula.And \<alpha>' (Formula.Release \<phi>' I (shr_pred \<psi>')))
     else Formula.And \<alpha>' (Formula.Release \<phi>' I \<psi>'))"
| "share_rw (Formula.Release \<phi> I \<psi>) = (let \<phi>' = share_rw \<phi>; \<psi>' = share_rw \<psi> in
     if share_ok \<phi>' \<psi>' then Formula.Let shr \<psi>' (Formula.Release \<phi>' I (shr_pred \<psi>'))
     else Formula.Release \<phi>' I \<psi>')"
| "share_rw (Formula.Let p \<phi> \<psi>) = Formula.Let p (share_rw \<phi>) (share_rw \<psi>)"
| "share_rw (Formula.Neg \<phi>) = Formula.Neg (share_rw \<phi>)"
| "share_rw (Formula.And \<phi> \<psi>) = Formula.And (share_rw \<phi>) (share_rw \<psi>)"
| "share_rw (Formula.Or \<phi> \<psi>) = Formula.Or (share_rw \<phi>) (share_rw \<psi>)"
| "share_rw (Formula.Ands l) = Formula.Ands (map share_rw l)"
| "share_rw (Formula.Exists t \<phi>) = Formula.Exists t (share_rw \<phi>)"
| "share_rw (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (share_rw \<phi>)"
| "share_rw (Formula.Prev I \<phi>) = Formula.Prev I (share_rw \<phi>)"
| "share_rw (Formula.Next I \<phi>) = Formula.Next I (share_rw \<phi>)"
| "share_rw (Formula.Since \<phi> I \<psi>) = Formula.Since (share_rw \<phi>) I (share_rw \<psi>)"
| "share_rw (Formula.Until \<phi> I \<psi>) = Formula.Until (share_rw \<phi>) I (share_rw \<psi>)"
| "share_rw \<phi> = \<phi>"

text \<open>As for the frozen predicates, the rewrite is applied only when its result is monitorable.\<close>

definition share_opt :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "share_opt \<phi> = (let \<phi>' = share_rw \<phi> in if mmonitorable_exec \<phi>' then \<phi>' else \<phi>)"

lemma tabulate_map_upt: "tabulate f x n = map f [x..<x + n]"
  by (induct n arbitrary: x) (auto simp: upt_rec)

lemma wty_shr_pred:
  "S((shr, Formula.nfv \<psi>) \<mapsto> tabulate E 0 (Formula.nfv \<psi>)), E \<turnstile> shr_pred \<psi>"
  by (auto simp: shr_pred_def tabulate_map_upt list.rel_map intro!: wty_formula.Pred
    list.rel_refl_strong wty_trm.Var)

lemma wty_fresh_upd:
  assumes "S(q \<mapsto> y), E \<turnstile> \<psi>" "q \<noteq> pn \<Longrightarrow> S(q \<mapsto> y, pn \<mapsto> x), E \<turnstile> \<psi>"
  shows "S(pn \<mapsto> x, q \<mapsto> y), E \<turnstile> \<psi>"
proof (cases "q = pn")
  case True
  then show ?thesis
    using assms(1) by simp
next
  case False
  then show ?thesis
    using assms(2) unfolding fun_upd_twist[OF not_sym[OF False]] by blast
qed

lemma wty_fresh': "S, E \<turnstile> \<phi> \<Longrightarrow> \<not> occurs pn \<phi> \<Longrightarrow> S' = S(pn \<mapsto> x) \<Longrightarrow> S', E \<turnstile> \<phi>"
proof (induct arbitrary: S' rule: wty_formula.induct)
  case (Let S E' \<phi> p E \<psi>)
  let ?q = "(p, Formula.nfv \<phi>)" and ?y = "tabulate E' 0 (Formula.nfv \<phi>)"
  show ?case
    unfolding Let(6)
  proof (rule wty_formula.Let)
    show "S(pn \<mapsto> x), E' \<turnstile> \<phi>"
      by (rule Let(2)[where S'="S(pn \<mapsto> x)", OF _ refl]) (use Let(5) in simp)
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E \<turnstile> \<psi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E \<turnstile> \<psi>"
        by (rule Let(3))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E \<turnstile> \<psi>"
        by (rule Let(4)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use Let(5) in simp)
    qed
  qed
next
  case (Frz S E' \<phi> p E \<psi>)
  let ?q = "(p, Formula.nfv \<phi>)" and ?y = "tabulate E' 0 (Formula.nfv \<phi>)"
  show ?case
    unfolding Frz(6)
  proof (rule wty_formula.Frz)
    show "S(pn \<mapsto> x), E' \<turnstile> \<phi>"
      by (rule Frz(2)[where S'="S(pn \<mapsto> x)", OF _ refl]) (use Frz(5) in simp)
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E \<turnstile> \<psi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E \<turnstile> \<psi>"
        by (rule Frz(3))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E \<turnstile> \<psi>"
        by (rule Frz(4)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use Frz(5) in simp)
    qed
  qed
next
  case (LetPast S p \<phi> E' E \<psi>)
  let ?q = "(p, Formula.nfv \<phi>)" and ?y = "tabulate E' 0 (Formula.nfv \<phi>)"
  show ?case
    unfolding LetPast(6)
  proof (rule wty_formula.LetPast)
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E' \<turnstile> \<phi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E' \<turnstile> \<phi>"
        by (rule LetPast(1))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E' \<turnstile> \<phi>"
        by (rule LetPast(2)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use LetPast(5) in simp)
    qed
    show "S(pn \<mapsto> x, ?q \<mapsto> ?y), E \<turnstile> \<psi>"
    proof (rule wty_fresh_upd)
      show "S(?q \<mapsto> ?y), E \<turnstile> \<psi>"
        by (rule LetPast(3))
      show "S(?q \<mapsto> ?y, pn \<mapsto> x), E \<turnstile> \<psi>"
        by (rule LetPast(4)[where S'="S(?q \<mapsto> ?y, pn \<mapsto> x)", OF _ refl]) (use LetPast(5) in simp)
    qed
  qed
next
  case (MatchP S E r I)
  show ?case
    unfolding MatchP(3) using MatchP(1,2)
    by (auto intro!: wty_formula.MatchP elim!: regex.pred_mono_strong)
next
  case (MatchF S E r I)
  show ?case
    unfolding MatchF(3) using MatchF(1,2)
    by (auto intro!: wty_formula.MatchF elim!: regex.pred_mono_strong)
qed (auto intro: wty_formula.intros)

lemma wty_fresh: "S, E \<turnstile> \<phi> \<Longrightarrow> \<not> occurs pn \<phi> \<Longrightarrow> S(pn \<mapsto> x), E \<turnstile> \<phi>"
  by (rule wty_fresh'[OF _ _ refl])

lemma wty_share_rw: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> share_rw \<phi>"
proof (induct \<phi> arbitrary: S E rule: share_rw.induct)
  case (1 \<alpha> \<phi> I \<psi>)
  let ?\<alpha> = "share_rw \<alpha>" and ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?S = "S((shr, Formula.nfv ?\<psi>) \<mapsto> tabulate E 0 (Formula.nfv ?\<psi>))"
  from 1(4) have "S, E \<turnstile> \<alpha>" "S, E \<turnstile> \<phi>" "S, E \<turnstile> \<psi>"
    by (auto dest: wty_formulaD)
  then have \<alpha>: "S, E \<turnstile> ?\<alpha>" and \<phi>: "S, E \<turnstile> ?\<phi>" and \<psi>: "S, E \<turnstile> ?\<psi>"
    using 1(1) 1(2)[OF refl] 1(3)[OF refl refl] by blast+
  show ?case
  proof (cases "share_ok (Formula.And ?\<alpha> ?\<phi>) ?\<psi>")
    case True
    then have "\<not> occurs (shr, Formula.nfv ?\<psi>) ?\<alpha>" "\<not> occurs (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def)
    then have "?S, E \<turnstile> Formula.And ?\<alpha> (Formula.Release ?\<phi> I (shr_pred ?\<psi>))"
      by (intro wty_formula.And wty_formula.Release wty_fresh[OF \<alpha>] wty_fresh[OF \<phi>] wty_shr_pred)
    then show ?thesis
      using True \<psi> by (auto simp: Let_def intro!: wty_formula.Let[where E'=E])
  next
    case False
    then show ?thesis
      using \<alpha> \<phi> \<psi> by (auto simp: Let_def intro!: wty_formula.And wty_formula.Release)
  qed
next
  case (2 \<phi> I \<psi>)
  let ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?S = "S((shr, Formula.nfv ?\<psi>) \<mapsto> tabulate E 0 (Formula.nfv ?\<psi>))"
  from 2(3) have "S, E \<turnstile> \<phi>" "S, E \<turnstile> \<psi>"
    by (auto dest: wty_formulaD)
  then have \<phi>: "S, E \<turnstile> ?\<phi>" and \<psi>: "S, E \<turnstile> ?\<psi>"
    using 2(1) 2(2)[OF refl] by blast+
  show ?case
  proof (cases "share_ok ?\<phi> ?\<psi>")
    case True
    then have "\<not> occurs (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def)
    then have "?S, E \<turnstile> Formula.Release ?\<phi> I (shr_pred ?\<psi>)"
      by (intro wty_formula.Release wty_fresh[OF \<phi>] wty_shr_pred)
    then show ?thesis
      using True \<psi> by (auto simp: Let_def intro!: wty_formula.Let[where E'=E])
  next
    case False
    then show ?thesis
      using \<phi> \<psi> by (auto simp: Let_def intro!: wty_formula.Release)
  qed
next
  case (3 p \<phi> \<psi>)
  from 3(3) obtain E' where \<phi>: "S, E' \<turnstile> \<phi>" and \<psi>: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    by (cases rule: wty_formula.cases) auto
  show ?case
    using wty_formula.Let[OF 3(1)[OF \<phi>]] 3(2)[OF \<psi>] by (simp add: fun_upd_def)
next
  case (7 l)
  show ?case
    using 7(1) wty_formula_AndsD[OF 7(2)] by (auto intro!: wty_formula.Ands)
qed (erule wty_formula.cases; auto intro: wty_formula.intros)+

lemma wty_share_opt: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> share_opt \<phi>"
  by (simp add: share_opt_def Let_def wty_share_rw)

lemma mmonitorable_share_opt: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (share_opt \<phi>)"
  by (simp add: share_opt_def Let_def mmonitorable_exec_mmonitorable)

(*<*)
end
(*>*)
