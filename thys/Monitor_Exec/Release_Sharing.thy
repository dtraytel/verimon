(*<*)
theory Release_Sharing
  imports "Monitor_Algorithm.Monitor" "MFODL_Logic.Typing" "MFODL_Logic.Multiway"
begin
(*>*)



section \<open>Sharing the release's right operand\<close>

text \<open>@{const convert_multiway} and @{const and_release_safe_bounded} copy a release's right
  operand; binding it with @{const Formula.Let} to a fresh predicate evaluates it once.\<close>

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

text \<open>The rewrite applies only if its result is monitorable.\<close>

definition share_opt :: "ty Formula.formula \<Rightarrow> ty Formula.formula" where
  "share_opt \<phi> = (let \<phi>' = share_rw \<phi> in if mmonitorable_exec \<phi>' then \<phi>' else \<phi>)"

end
(*>*)
