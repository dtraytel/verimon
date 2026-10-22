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

subsection \<open>The shared predicate\<close>

lemma not_contains_pred_preds: "\<not> occurs pn \<phi> \<Longrightarrow> \<not> contains_pred pn \<phi>"
  by (induct pn \<phi> rule: contains_pred.induct) auto

lemma sat_Release_cong:
  assumes "\<And>v j. Formula.sat \<sigma> V v j \<phi> = Formula.sat \<sigma> V' v j \<phi>'"
    "\<And>v j. Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma> V' v j \<psi>'"
  shows "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V' v i (Formula.Release \<phi>' I \<psi>')"
  using assms by simp

subsection \<open>The rewrite of the whole formula\<close>

lemma mmonitorable_share_opt: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (share_opt \<phi>)"
  by (simp add: share_opt_def Let_def mmonitorable_exec_mmonitorable)

(*<*)
end
(*>*)
