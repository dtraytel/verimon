(*<*)
theory IWindow_Proof
  imports "Monitor_Exec.IWindow" Window_Dispatch_Proof ITable_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma isw_move_abs:
  "isw_move args nt pend win cc = (pend', win', cc') \<Longrightarrow>
     sw_move args nt pend win (icnt_abs cc) = (pend', win', icnt_abs cc')"
proof (induct args nt pend win cc arbitrary: pend' win' cc' rule: isw_move.induct)
  case (1 args nt pend win cc)
  obtain eo pq where h: "safe_hd pend = (eo, pq)" by (cases "safe_hd pend")
  show ?case
  proof (cases eo)
    case None
    then show ?thesis using 1(3) by (simp add: sw_move.simps[of args nt pend] isw_move.simps[of args nt pend] h)
  next
    case (Some e)
    then show ?thesis
      using 1(1)[OF h[symmetric] Some] 1(2)[OF h[symmetric] Some] 1(3)
      by (simp add: sw_move.simps[of args nt pend] isw_move.simps[of args nt pend] h icnt_abs_add
          split: if_splits)
  qed
qed

lemma isw_expire_abs:
  "isw_expire args nt win cc = (win', cc') \<Longrightarrow>
     sw_expire args nt win (icnt_abs cc) = (win', icnt_abs cc')"
proof (induct args nt win cc arbitrary: win' cc' rule: isw_expire.induct)
  case (1 args nt win cc)
  show ?case
    using 1 by (subst sw_expire.simps, subst (asm) isw_expire.simps)
      (auto simp: icnt_abs_del split: prod.splits option.splits if_splits)
qed

lemma isw_abs_add_new_ts: "isw_abs (isw_add_new_ts args nt aux) = sw_add_new_ts args nt (isw_abs aux)"
  by (auto simp: isw_abs_def isw_add_new_ts_def sw_add_new_ts_def
      dest!: isw_move_abs isw_expire_abs split: prod.splits)

lemma isw_abs_join: "isw_abs (isw_join args X aux) = sw_join args X (isw_abs aux)"
  by (simp add: isw_abs_def isw_join_def sw_join_def icnt_abs_def split: prod.splits)

lemma isw_abs_add_new_table:
  "isw_abs (isw_add_new_table args X aux) = sw_add_new_table args X (isw_abs aux)"
  by (simp add: isw_abs_def isw_add_new_table_def sw_add_new_table_def icnt_abs_add split: prod.splits)

lemma iset_isw_result: "iset (isw_result aux) = sw_result args (isw_abs aux)"
  by (simp add: isw_abs_def isw_result_def sw_result_def icnt_abs_def split: prod.splits)

lemma ims_abs_emb[simp]: "ims_abs (ims_emb a) = a"
  by (cases a rule: emsaux_cases) simp

lemma iemsaux_cases:
  fixes daux :: iemsaux
  obtains t gc msk data_prev data_in table_in idx_in tuple_in idx_since tuple_since
  where "daux = (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
    idx_since, tuple_since)"
  by (metis prod.collapse)

lemma ims_abs_shift_end: "ims_abs (ieshift_end args nt a) = eshift_end args nt (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def fold_filter_set_def split: prod.splits)

lemma ims_abs_add_new_ts': "ims_abs (ieadd_new_ts_msaux' args nt a) = eadd_new_ts_msaux' args nt (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def split: prod.splits)

lemma ims_abs_add_new_ts: "ims_abs (ieadd_new_ts_msaux args nt a) = eadd_new_ts_msaux args nt (ims_abs a)"
  by (simp add: ieadd_new_ts_msaux_def eadd_new_ts_msaux_def ims_abs_shift_end ims_abs_add_new_ts')

lemma ims_abs_gc: "ims_abs (iegc_msaux args a) = egc_msaux args (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def)

lemma ims_abs_add_new_table_msaux:
  "ims_abs (ieadd_new_table_msaux args X a) = eadd_new_table_msaux args X (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def)

lemma ims_abs_add_new_table_lz:
  "ims_abs (ieadd_new_table_lz args X a) = eadd_new_table_lz args X (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def)

lemma ims_abs_join: "ims_abs (iejoin_msaux args Y a) = ejoin_msaux args Y (ims_abs a)"
  by (cases a rule: iemsaux_cases) (auto simp: Let_def)

lemma ims_abs_gc_join: "ims_abs (iegc_join_msaux args Y a) = egc_join_msaux args Y (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp only: iegc_join_msaux.simps egc_join_msaux.simps ims_abs.simps
      if_distrib[of "ims_abs"] ims_abs_join ims_abs_gc)

lemma ims_abs_gc_join_lz: "ims_abs (iegc_join_lz args Y a) = egc_join_lz args Y (ims_abs a)"
  by (simp add: iegc_join_lz_def egc_join_lz_def ims_abs_join ims_abs_gc_join)

lemma iset_ieresult: "iset (ieresult_msaux a) = eresult_msaux args (ims_abs a)"
  by (cases a rule: iemsaux_cases) simp

lemma ims_abs_ensure[simp]: "ims_abs (iems_ensure msks a) = ims_abs a"
  by (cases a rule: iemsaux_cases) simp

lemma riu_iudsx_emb[simp]: "riu (iudsx_emb msks d) = d"
  by (cases d) (simp_all add: iudsx_emb_def)

lemma riu_add_new_ts[simp]: "riu (iudsx_add_new_ts args nt d) = udsx_add_new_ts args nt (riu d)"
  by (cases d) (simp_all add: isw_abs_add_new_ts ims_abs_add_new_ts)

lemma riu_join[simp]: "riu (iudsx_join args X d) = udsx_join args X (riu d)"
  by (cases d) (simp_all add: isw_abs_join ims_abs_gc_join_lz)

lemma riu_add_new_table[simp]: "riu (iudsx_add_new_table args X d) = udsx_add_new_table args X (riu d)"
  by (cases d) (simp_all add: isw_abs_add_new_table ims_abs_add_new_table_lz)

lemma iset_iudsx_result[simp]: "iset (iudsx_result args d) = udsx_result args (riu d)"
  by (cases d) (simp_all add: iset_isw_result iset_ieresult)

lemma riu_ensure[simp]: "riu (iudsx_ensure msks d) = riu d"
  by (induct msks d rule: iudsx_ensure.induct) simp_all

end
(*>*)
