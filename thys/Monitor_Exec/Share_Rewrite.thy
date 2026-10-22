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

subsection \<open>The rewrite of the whole formula\<close>

lemma fvi_share_rw[simp]: "Formula.fvi b (share_rw \<phi>) = Formula.fvi b \<phi>"
  by (induct \<phi> arbitrary: b rule: share_rw.induct)
    (auto simp: Let_def share_ok_def fvi_shr_pred split: if_splits)

lemma nfv_share_rw[simp]: "Formula.nfv (share_rw \<phi>) = Formula.nfv \<phi>"
  by (simp add: Formula.nfv_def)

lemma sat_share_rw[simp]: "Formula.sat \<sigma> V v i (share_rw \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (induct \<phi> arbitrary: V v i rule: share_rw.induct)
  case (1 \<alpha> \<phi> I \<psi>)
  note IH\<alpha> = 1(1) and IH\<phi> = 1(2)[OF refl] and IH\<psi> = 1(3)[OF refl refl]
  let ?\<alpha> = "share_rw \<alpha>" and ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?V = "V((shr, Formula.nfv ?\<psi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j ?\<psi>)"
  show ?case
  proof (cases "share_ok (Formula.And ?\<alpha> ?\<phi>) ?\<psi>")
    case True
    then have n\<alpha>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<alpha>" and n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have p: "Formula.sat \<sigma> ?V v' j (shr_pred ?\<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
      by (rule trans[OF sat_shr_pred[OF True] IH\<psi>])
    have f: "Formula.sat \<sigma> ?V v' j ?\<phi> = Formula.sat \<sigma> V v' j \<phi>" for v' j
      by (rule trans[OF not_contains_pred_sat[OF n\<phi>] IH\<phi>])
    have a: "Formula.sat \<sigma> ?V v i ?\<alpha> = Formula.sat \<sigma> V v i \<alpha>"
      by (rule trans[OF not_contains_pred_sat[OF n\<alpha>] IH\<alpha>])
    show ?thesis
      using True a sat_Release_cong[of \<sigma> ?V ?\<phi> V \<phi> "shr_pred ?\<psi>" \<psi>, OF f p] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using IH\<alpha> IH\<phi> IH\<psi> sat_Release_cong[of \<sigma> V ?\<phi> V \<phi> ?\<psi> \<psi>] by (simp add: Let_def)
  qed
next
  case (2 \<phi> I \<psi>)
  note IH\<phi> = 2(1) and IH\<psi> = 2(2)[OF refl]
  let ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?V = "V((shr, Formula.nfv ?\<psi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j ?\<psi>)"
  show ?case
  proof (cases "share_ok ?\<phi> ?\<psi>")
    case True
    then have n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have p: "Formula.sat \<sigma> ?V v' j (shr_pred ?\<psi>) = Formula.sat \<sigma> V v' j \<psi>" for v' j
      by (rule trans[OF sat_shr_pred[OF True] IH\<psi>])
    have f: "Formula.sat \<sigma> ?V v' j ?\<phi> = Formula.sat \<sigma> V v' j \<phi>" for v' j
      by (rule trans[OF not_contains_pred_sat[OF n\<phi>] IH\<phi>])
    show ?thesis
      using True sat_Release_cong[of \<sigma> ?V ?\<phi> V \<phi> "shr_pred ?\<psi>" \<psi>, OF f p] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using IH\<phi> IH\<psi> sat_Release_cong[of \<sigma> V ?\<phi> V \<phi> ?\<psi> \<psi>] by (simp add: Let_def)
  qed
qed (auto split: nat.splits)

lemma fvi_share_opt[simp]: "Formula.fvi b (share_opt \<phi>) = Formula.fvi b \<phi>"
  by (simp add: share_opt_def Let_def)

lemma nfv_share_opt[simp]: "Formula.nfv (share_opt \<phi>) = Formula.nfv \<phi>"
  by (simp add: share_opt_def Let_def)

lemma sat_share_opt[simp]: "Formula.sat \<sigma> V v i (share_opt \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: share_opt_def Let_def)

lemma progress_share_opt_empty[simp]:
  "progress \<sigma> Map.empty (share_opt \<phi>) j = progress \<sigma> Map.empty \<phi> j"
  by (simp add: share_opt_def Let_def progress_share_rw)

end
(*>*)
