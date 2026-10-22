(*<*)
theory Agg_Code_Proof
  imports "Monitor_Exec.Agg_Code" Mono_Sweep_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma split_min_p_eq: "t \<noteq> Leaf \<Longrightarrow> split_min_p t = split_min t"
  by (induction t rule: split_min_p.induct) (auto split: tree.split)

lemma del_max_p_eq: "t \<noteq> Leaf \<Longrightarrow> del_max_p t = del_max t"
  by (induction t rule: del_max_p.induct) (auto split: tree.split)

lemma combine_p_eq: "wbt l \<Longrightarrow> wbt r \<Longrightarrow> combine_p l r = Order_Statistic_Tree.combine l r"
  by (cases l; cases r) (simp_all add: combine_p_def split_min_p_eq del_max_p_eq)

lemma delete_p_eq: "wbt t \<Longrightarrow> delete_p x t = delete x t"
  by (induction x t rule: delete_p.induct) (simp_all add: combine_p_eq)

lemma select_0: "wbt t \<Longrightarrow> select t 0 = wbt_min t"
proof (induction t)
  case (Node l x r)
  then show ?case by (cases x; cases l) auto
qed simp

lemma select_last: "wbt t \<Longrightarrow> select t (size_wbt t - 1) = wbt_max t"
proof (induction t)
  case (Node l x r)
  then show ?case by (cases x; cases r) auto
qed simp

lemma tree_select_0: "tree_select t 0 = tree_min t"
  by transfer (simp add: select_0)

lemma tree_select_last: "tree_select t (tree_size t - 1) = tree_max t"
  by transfer (metis select_last)

lemma uagg_gins:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and fX: "finite X" and w: "\<forall>t\<in>X. length t = w"
    and a: "gins k (umeval_trm f) (csl X) (ginit \<omega>) = Some a"
  shows "gres g0 \<omega> pos (\<lambda>x. x) a = uagg g0 \<omega> f k pos X"
proof -
  let ?p = "(g0, \<omega>, f, k, pos)"
  let ?cc = "(Mapping.empty, {}) :: cntset"
  have cr: "cnt_rep (\<lambda>_. 0) ?cc"
    by (simp add: cnt_rep_def)
  have inv: "ag_inv ?p w (cnt_add X ?cc) (ag_ins ?p w X ?cc (ag_init ?p w))"
    by (rule ag_inv_ins[OF cr fX ok w _ ag_inv_init]) simp
  have snd: "snd (cnt_add X ?cc) = X"
    using cnt_rep_snd_add[OF cr fX] by simp
  have ins: "ag_ins ?p w X ?cc (ag_init ?p w) = Some a"
    using a by (simp add: ag_ins_def ag_init_def)
  have "ag_res ?p w (cnt_add X ?cc) (Some a) = eagg_p ?p X"
    using ag_res_inv[OF inv ok] snd w ins by simp
  then show ?thesis
    by (simp add: ag_res_def id_def)
qed

lemma uagg_g_eq:
  "uagg_g g0 \<omega> f k pos X = (let xs = csl X in case xs of
       [] \<Rightarrow> uagg_gen g0 \<omega> f k pos X
     | t # _ \<Rightarrow> (let w = length t in
         if eagg_ok (g0, \<omega>, f, k, pos) w \<and> list_all (\<lambda>u. length u = w) xs
         then (case gins k (umeval_trm f) xs (ginit \<omega>) of
                 Some a \<Rightarrow> gres g0 \<omega> pos (\<lambda>x. x) a
               | None \<Rightarrow> uagg_gen g0 \<omega> f k pos X)
         else uagg_gen g0 \<omega> f k pos X))"
proof (cases "csl X")
  case (Cons t ts)
  then have fX: "finite X"
    using csl_infinite by fastforce
  then have s: "set (csl X) = X"
    by (rule set_csl_ed)
  show ?thesis
  proof (cases "eagg_ok (g0, \<omega>, f, k, pos) (length t) \<and> list_all (\<lambda>u. length u = length t) (csl X)")
    case True
    then have w: "\<forall>u\<in>X. length u = length t"
      using s by (simp add: list_all_iff)
    show ?thesis
    proof (cases "gins k (umeval_trm f) (csl X) (ginit \<omega>)")
      case (Some a)
      then show ?thesis
        using True uagg_gins[OF _ fX w Some] by (simp add: Let_def Cons uagg_g_def)
    qed (use True Cons in \<open>simp add: Let_def uagg_gen_def uagg_g_def\<close>)
  next
    case False
    then show ?thesis
      by (simp only: Cons Let_def list.case if_False uagg_gen_def uagg_g_def)
  qed
qed (simp add: uagg_gen_def uagg_g_def)

end
(*>*)
