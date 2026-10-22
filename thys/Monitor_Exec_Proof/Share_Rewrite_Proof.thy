(*<*)
theory Share_Rewrite_Proof
  imports "Monitor_Exec.Share_Rewrite" "MFODL_Monitor_Proof.Progress" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>The shared predicate\<close>

lemma tabulate_map_upt: "tabulate f x n = map f [x..<x + n]"
  by (induct n arbitrary: x) (auto simp: upt_rec)

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

lemma fvi_share_opt[simp]: "Formula.fvi b (share_opt \<phi>) = Formula.fvi b \<phi>"
  by (simp add: share_opt_def Let_def)

lemma nfv_share_opt[simp]: "Formula.nfv (share_opt \<phi>) = Formula.nfv \<phi>"
  by (simp add: share_opt_def Let_def)

lemma sat_share_opt[simp]: "Formula.sat \<sigma> V v i (share_opt \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  by (simp add: share_opt_def Let_def)

lemma progress_share_opt_empty[simp]:
  "progress \<sigma> Map.empty (share_opt \<phi>) j = progress \<sigma> Map.empty \<phi> j"
  by (simp add: share_opt_def Let_def progress_share_rw)

lemma wty_share_opt: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> share_opt \<phi>"
  by (simp add: share_opt_def Let_def wty_share_rw)

lemma mmonitorable_share_opt: "mmonitorable \<phi> \<Longrightarrow> mmonitorable (share_opt \<phi>)"
  by (simp add: share_opt_def Let_def mmonitorable_exec_mmonitorable)

(*<*)
end
(*>*)
