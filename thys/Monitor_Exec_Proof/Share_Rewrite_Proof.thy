(*<*)
theory Share_Rewrite_Proof
  imports "Monitor_Exec.Share_Rewrite" "MFODL_Monitor_Proof.Progress" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>The shared predicate\<close>

lemma not_contains_pred_preds: "\<not> occurs pn \<phi> \<Longrightarrow> \<not> contains_pred pn \<phi>"
  by (induct pn \<phi> rule: contains_pred.induct) auto

lemma fvi_shr_pred:
  assumes "\<forall>x\<in>{0..<Formula.nfv \<psi>}. x \<in> Formula.fv \<psi>"
  shows "Formula.fvi b (shr_pred \<psi>) = Formula.fvi b \<psi>"
proof (rule set_eqI)
  fix y
  have "y \<in> Formula.fvi b (shr_pred \<psi>) \<longleftrightarrow> y + b < Formula.nfv \<psi>"
  proof
    assume "y \<in> Formula.fvi b (shr_pred \<psi>)"
    then show "y + b < Formula.nfv \<psi>"
      by (auto simp: shr_pred_def split: if_splits)
  next
    assume "y + b < Formula.nfv \<psi>"
    then show "y \<in> Formula.fvi b (shr_pred \<psi>)"
      by (auto simp: shr_pred_def intro!: bexI[of _ "y + b"])
  qed
  also have "\<dots> \<longleftrightarrow> y + b \<in> Formula.fv \<psi>"
    using assms fvi_less_nfv[of \<psi>] by auto
  also have "\<dots> \<longleftrightarrow> y \<in> Formula.fvi b \<psi>"
    by (rule fvi_iff_fv[symmetric])
  finally show "y \<in> Formula.fvi b (shr_pred \<psi>) \<longleftrightarrow> y \<in> Formula.fvi b \<psi>" .
qed

lemma sat_shr_pred:
  assumes "share_ok \<alpha> \<psi>"
  shows "Formula.sat \<sigma> (V((shr, Formula.nfv \<psi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<psi>)) v i (shr_pred \<psi>) =
    Formula.sat \<sigma> V v i \<psi>"
proof -
  have "Formula.sat \<sigma> V (map ((!) v) [0..<Formula.nfv \<psi>]) i \<psi> = Formula.sat \<sigma> V v i \<psi>"
    using fvi_less_nfv[of \<psi>] by (intro sat_fv_cong) auto
  then show ?thesis
    by (simp add: shr_pred_def o_def)
qed

lemma progress_shr_pred:
  "progress \<sigma> (P((shr, Formula.nfv \<psi>) \<mapsto> k)) (shr_pred \<psi>) j = k"
  by (simp add: shr_pred_def)

lemma sat_Release_cong:
  assumes "\<And>v j. Formula.sat \<sigma> V v j \<phi> = Formula.sat \<sigma> V' v j \<phi>'"
    "\<And>v j. Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma> V' v j \<psi>'"
  shows "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V' v i (Formula.Release \<phi>' I \<psi>')"
  using assms by simp

lemma progress_Release_cong:
  assumes "progress \<sigma> P \<phi> j = progress \<sigma> P' \<phi>' j" "progress \<sigma> P \<psi> j = progress \<sigma> P' \<psi>' j"
  shows "progress \<sigma> P (Formula.Release \<phi> I \<psi>) j = progress \<sigma> P' (Formula.Release \<phi>' I \<psi>') j"
  using assms by (simp add: release_safe_bounded_def always_safe_bounded_def Formula.eventually_def
    Formula.once_def)

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

lemma progress_share_rw:
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P (share_rw \<phi>) j = progress \<sigma> P \<phi> j"
proof (induct \<phi> arbitrary: P rule: share_rw.induct)
  case (1 \<alpha> \<phi> I \<psi>)
  note IH\<alpha> = 1(1)[OF 1(4)] and IH\<phi> = 1(2)[OF refl 1(4)] and IH\<psi> = 1(3)[OF refl refl 1(4)]
  let ?\<alpha> = "share_rw \<alpha>" and ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?P = "P((shr, Formula.nfv ?\<psi>) \<mapsto> progress \<sigma> P ?\<psi> j)"
  show ?case
  proof (cases "share_ok (Formula.And ?\<alpha> ?\<phi>) ?\<psi>")
    case True
    then have n\<alpha>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<alpha>" and n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have a: "progress \<sigma> ?P ?\<alpha> j = progress \<sigma> P \<alpha> j"
      by (rule trans[OF not_contains_pred_progress[OF n\<alpha>] IH\<alpha>])
    have f: "progress \<sigma> ?P ?\<phi> j = progress \<sigma> P \<phi> j"
      by (rule trans[OF not_contains_pred_progress[OF n\<phi>] IH\<phi>])
    have p: "progress \<sigma> ?P (shr_pred ?\<psi>) j = progress \<sigma> P \<psi> j"
      by (rule trans[OF progress_shr_pred IH\<psi>])
    show ?thesis
      using True a progress_Release_cong[OF f p, of I] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using IH\<alpha> progress_Release_cong[OF IH\<phi> IH\<psi>, of I] by (simp add: Let_def)
  qed
next
  case (2 \<phi> I \<psi>)
  note IH\<phi> = 2(1)[OF 2(3)] and IH\<psi> = 2(2)[OF refl 2(3)]
  let ?\<phi> = "share_rw \<phi>" and ?\<psi> = "share_rw \<psi>"
  let ?P = "P((shr, Formula.nfv ?\<psi>) \<mapsto> progress \<sigma> P ?\<psi> j)"
  show ?case
  proof (cases "share_ok ?\<phi> ?\<psi>")
    case True
    then have n\<phi>: "\<not> contains_pred (shr, Formula.nfv ?\<psi>) ?\<phi>"
      by (auto simp: share_ok_def intro!: not_contains_pred_preds)
    have f: "progress \<sigma> ?P ?\<phi> j = progress \<sigma> P \<phi> j"
      by (rule trans[OF not_contains_pred_progress[OF n\<phi>] IH\<phi>])
    have p: "progress \<sigma> ?P (shr_pred ?\<psi>) j = progress \<sigma> P \<psi> j"
      by (rule trans[OF progress_shr_pred IH\<psi>])
    show ?thesis
      using True progress_Release_cong[OF f p, of I] by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using progress_Release_cong[OF IH\<phi> IH\<psi>, of I] by (simp add: Let_def)
  qed
next
  case (3 p \<phi> \<psi>)
  have "progress \<sigma> P \<phi> j \<le> j"
    by (rule progress_le_gen[OF 3(3)])
  then have pm: "pred_mapping (\<lambda>x. x \<le> j) (P((p, Formula.nfv \<phi>) \<mapsto> progress \<sigma> P \<phi> j))"
    using 3(3) by simp
  show ?case
    using 3(1)[OF 3(3)] 3(2)[OF pm] by (simp add: fun_upd_def)
qed (auto simp: o_def cong: map_cong)

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
