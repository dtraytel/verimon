(*<*)
theory Agg_Cache_Proof
  imports "Monitor_Exec.Agg_Cache" Until_Agg_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma cnt_ins_fold_cins: "cnt_ins_fold F xs c b = fold (cins F) xs (c, b)"
  unfolding cnt_ins_fold_def cins_def by (rule arg_cong[where f = "\<lambda>f. fold f xs (c, b)"]) (auto simp: fun_eq_iff)

lemma cnt_del_fold_cdel: "cnt_del_fold F xs c b = fold (cdel F) xs (c, b)"
  unfolding cnt_del_fold_def cdel_def by (rule arg_cong[where f = "\<lambda>f. fold f xs (c, b)"]) (auto simp: fun_eq_iff)


lifting_forget mapping.lifting

lemma uc_set_gcache: "cachedp (snd (uc_key x)) \<Longrightarrow> uc_ax x = Some a \<Longrightarrow>
    uc_set x = gcache (fst (uc_key x)) (snd (uc_key x)) a"
  by transfer auto

lemma cstep_fst: "fst (cstep S q p t axC) = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
    (case fst axC of None \<Rightarrow> None | Some a \<Rightarrow> S k (umeval_trm f) t (Some a)))"
  by (auto simp: cstep_def split: prod.splits option.splits)

lemma cstep_ins_fst: "fst (cstep gstep_ins q p t axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gstep_ins k (umeval_trm f) t (fst axC))"
  by (simp add: cstep_fst split: prod.splits option.splits)

lemma cstep_del_fst: "fst (cstep gstep_del q p t axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gstep_del k (umeval_trm f) t (fst axC))"
  by (simp add: cstep_fst split: prod.splits option.splits)

lemma fold_cstep_fst:
  "(\<And>t axC. fst (S t axC) = G t (fst axC)) \<Longrightarrow> fst (fold S xs axC) = fold G xs (fst axC)"
  by (induct xs arbitrary: axC) simp_all

lemma fst_fold_cstep_ins: "fst (fold (cstep gstep_ins q p) xs axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gins k (umeval_trm f) xs (fst axC))"
  by (cases p) (simp add: gins_def fold_cstep_fst[where G = "gstep_ins _ _"] cstep_ins_fst)

lemma fst_fold_cstep_del: "fst (fold (cstep gstep_del q p) xs axC) =
    (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gdel k (umeval_trm f) xs (fst axC))"
  by (cases p) (simp add: gdel_def fold_cstep_fst[where G = "gstep_del _ _"] cstep_del_fst)

lemma uc_step_ins_nc:
  assumes "\<not> cachedp p" "p = (g0, \<omega>, f, k, pos)"
  shows "(uc_cnt (uc_step_ins q p w X x), uc_ax (uc_step_ins q p w X x)) =
    cnt_ins_fold (gstep_ins k (umeval_trm f)) (csl X) (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rcnt (ek (snd key)) R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r)
  show ?thesis
  proof (cases "ek (snd key) = k")
    case True
    then have "rinv k R" using inv by simp
    from fold_rins[OF this, of "umeval_trm f" "csl X"] True show ?thesis using assms
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_ins.rep_eq r c ek_def cnt_ins_fold_cins)
  next
    case False
    then show ?thesis using assms rflat_x[OF inv]
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_ins.rep_eq r c ek_def split: prod.splits)
  qed
qed

lemma uc_step_ins_c:
  assumes "cachedp p"
  shows "uc_cnt (uc_step_ins q p w X x) = fold ucnt_add1 (csl X) (uc_cnt x)"
    "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rflat_x R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r rflat_x[OF inv])
  have h1: "fst (fold (cstep gstep_ins q p) (filter (\<lambda>t. Mapping.lookup (rflat_x R) t = None) (csl X))
      (rax R, C)) = uag_ins p w X (rflat_x R) (rax R)"
    by (simp add: fst_fold_cstep_ins uag_ins_def)
  show "uc_cnt (uc_step_ins q p w X x) = fold ucnt_add1 (csl X) (uc_cnt x)"
    using assms by (simp add: uc_cnt.rep_eq uc_step_ins.rep_eq r c cnt_ins_fold_eq[OF distinct_csl_edl]
        ucnt_add_def rflat_x[OF inv] split: prod.splits)
  show "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
    using assms h1 by (simp add: uc_ax.rep_eq uc_step_ins.rep_eq r c cnt_ins_fold_eq[OF distinct_csl_edl]
        split: prod.splits) (metis fst_conv)
qed

lemma uc_step_ins_cnt[simp]: "uc_cnt (uc_step_ins q p w X x) = ucnt_add X (uc_cnt x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_ins_c ucnt_add_def)
  next
    case False
    from uc_step_ins_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_ins_fold_eq[OF distinct_csl_edl] ucnt_add_def)
  qed
qed

lemma uc_step_ins_ax[simp]: "uc_ax (uc_step_ins q p w X x) = uag_ins p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_ins_c)
  next
    case False
    from uc_step_ins_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_ins_fold_eq[OF distinct_csl_edl] p uag_ins_def gins_def)
  qed
qed

lemma uc_step_del_nc:
  assumes "\<not> cachedp p" "p = (g0, \<omega>, f, k, pos)"
  shows "(uc_cnt (uc_step_del q p w X x), uc_ax (uc_step_del q p w X x)) =
    cnt_del_fold (gstep_del k (umeval_trm f)) (csl X) (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rcnt (ek (snd key)) R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r)
  show ?thesis
  proof (cases "ek (snd key) = k")
    case True
    then have "rinv k R" using inv by simp
    from fold_rdel[OF this, of "umeval_trm f" "csl X"] True show ?thesis using assms
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_del.rep_eq r c ek_def cnt_del_fold_cdel)
  next
    case False
    then show ?thesis using assms rflat_x[OF inv]
      by (simp add: uc_cnt.rep_eq uc_ax.rep_eq uc_step_del.rep_eq r c ek_def split: prod.splits)
  qed
qed

lemma uc_step_del_c:
  assumes "cachedp p"
  shows "uc_cnt (uc_step_del q p w X x) = fold ucnt_del1 (csl X) (uc_cnt x)"
    "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain key R C where r: "Rep_ucache x = (key, R, C)" by (cases "Rep_ucache x")
  have inv: "rinv (ek (snd key)) R" using uc_rep_inv[of x] by (simp add: uc_key.rep_eq uc_rep.rep_eq r)
  have c: "uc_cnt x = rflat_x R" "uc_ax x = rax R"
    by (simp_all add: uc_cnt.rep_eq uc_ax.rep_eq r rflat_x[OF inv])
  have h1: "fst (fold (cstep gstep_del q p) (filter (\<lambda>t. Mapping.lookup (rflat_x R) t = Some 1) (csl X))
      (rax R, C)) = uag_del p w X (rflat_x R) (rax R)"
    by (simp add: fst_fold_cstep_del uag_del_def)
  show "uc_cnt (uc_step_del q p w X x) = fold ucnt_del1 (csl X) (uc_cnt x)"
    using assms by (simp add: uc_cnt.rep_eq uc_step_del.rep_eq r c cnt_del_fold_eq[OF distinct_csl_edl]
        ucnt_del_def rflat_x[OF inv] split: prod.splits)
  show "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
    using assms h1 by (simp add: uc_ax.rep_eq uc_step_del.rep_eq r c cnt_del_fold_eq[OF distinct_csl_edl]
        split: prod.splits) (metis fst_conv)
qed

lemma uc_step_del_cnt[simp]: "uc_cnt (uc_step_del q p w X x) = ucnt_del X (uc_cnt x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_del_c ucnt_del_def)
  next
    case False
    from uc_step_del_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_del_fold_eq[OF distinct_csl_edl] ucnt_del_def)
  qed
qed

lemma uc_step_del_ax[simp]: "uc_ax (uc_step_del q p w X x) = uag_del p w X (uc_cnt x) (uc_ax x)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p) auto
  show ?thesis
  proof (cases "cachedp p")
    case True
    then show ?thesis by (simp add: uc_step_del_c)
  next
    case False
    from uc_step_del_nc[OF False p, of q w X x] show ?thesis
      by (simp add: cnt_del_fold_eq[OF distinct_csl_edl] p uag_del_def gdel_def)
  qed
qed

lifting_update mapping.lifting

lemma gempty_gkeys: "gempty a \<longleftrightarrow> gkeys a = {}"
  by (cases a) (simp_all add: Mapping.is_empty_def)

lemma uc_res: "uc_res q p w x = uag_res q p w (uc_cnt x) (uc_ax x)"
  by (auto simp: uc_res_def uag_res_code ugres_def gres_gvset ufilt_def uc_set_gcache gcache_def
      gempty_gkeys split: option.splits prod.splits)

lemma sa_init_rsc: "sa_init args p = rsc (usc_init args p q)"
  by (simp add: sa_init_def usc_init_def sw_init_def ucc.simps)

end
(*>*)
