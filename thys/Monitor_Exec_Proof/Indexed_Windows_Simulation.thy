(*<*)
theory Indexed_Windows_Simulation
  imports "Monitor_Exec.Indexed_Windows" Window_Dispatch_Simulation Indexed_Tables_Simulation "Monitor_Impl_Proof.Monitor_Instance_Valid"
begin
(*>*)



lemma icnt_abs_add1: "icnt_abs (icnt_add1 t cc) = cnt_add1 t (icnt_abs cc)"
  by (cases cc) (simp add: icnt_abs_def icnt_add1_def cnt_add1_def split: option.splits)

lemma icnt_abs_del1: "icnt_abs (icnt_del1 t cc) = cnt_del1 t (icnt_abs cc)"
  by (cases cc) (simp add: icnt_abs_def icnt_del1_def cnt_del1_def split: option.splits)

lemma icnt_abs_fold_add1: "icnt_abs (fold icnt_add1 xs cc) = fold cnt_add1 xs (icnt_abs cc)"
  by (induct xs arbitrary: cc) (simp_all add: icnt_abs_add1)

lemma icnt_abs_fold_del1: "icnt_abs (fold icnt_del1 xs cc) = fold cnt_del1 xs (icnt_abs cc)"
  by (induct xs arbitrary: cc) (simp_all add: icnt_abs_del1)

lemma icnt_abs_add: "icnt_abs (icnt_add T cc) = cnt_add T (icnt_abs cc)"
  by (simp add: icnt_add_def cnt_add_def icnt_abs_fold_add1)

lemma icnt_abs_del: "icnt_abs (icnt_del T cc) = cnt_del T (icnt_abs cc)"
  by (simp add: icnt_del_def cnt_del_def icnt_abs_fold_del1)

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

lemma iuw_extend_abs:
  "uw_extend args ts0 win rest bend (icnt_abs cc) =
     (case iuw_extend args ts0 win rest bend cc of (w, r, b, c) \<Rightarrow> (w, r, b, icnt_abs c))"
proof (induct args ts0 win rest bend cc rule: iuw_extend.induct)
  case (1 args ts0 win rest bend cc)
  show ?case
    by (subst uw_extend.simps, subst iuw_extend.simps)
      (use 1 in \<open>auto simp: icnt_abs_add split: prod.splits option.splits\<close>)
qed

lemma iuw_abs_step: "iuw_abs (iuw_step args ts0 aux) = uw_step args ts0 (iuw_abs aux)"
proof -
  obtain nts win rest len bend cc dn where a: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux) auto
  obtain win1 rest1 bend1 cc1 where x: "iuw_extend args ts0 win rest bend cc = (win1, rest1, bend1, cc1)"
    by (cases "iuw_extend args ts0 win rest bend cc") auto
  have u: "uw_extend args ts0 win rest bend (icnt_abs cc) = (win1, rest1, bend1, icnt_abs cc1)"
    by (simp add: iuw_extend_abs x)
  obtain eo w' where h: "safe_hd win1 = (eo, w')" by (cases "safe_hd win1")
  show ?thesis
    by (cases eo) (simp_all add: a x u h iuw_abs_def iuw_step_def uw_step_def Let_def icnt_abs_del)
qed

lemma iuw_abs_shift: "iuw_abs (iuw_shift args nt aux) = uw_shift args nt (iuw_abs aux)"
proof (induct args nt aux rule: iuw_shift.induct)
  case (1 args nt aux)
  obtain nts win rest len bend cc dn where a: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux) auto
  obtain to nts' where h: "safe_hd nts = (to, nts')" by (cases "safe_hd nts")
  show ?case
  proof (cases to)
    case None
    then show ?thesis
      by (subst iuw_shift.simps, subst uw_shift.simps) (simp add: a h)
  next
    case (Some ts0)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - ts0) \<or> len = 0")
      case True
      then show ?thesis using Some
        by (subst iuw_shift.simps, subst uw_shift.simps) (simp add: a h)
    next
      case False
      note IH = 1[OF a[symmetric] refl refl refl refl refl h[symmetric] Some False]
      show ?thesis using Some False IH[unfolded iuw_abs_step]
        by (subst iuw_shift.simps, subst uw_shift.simps)
          (simp add: a h)
    qed
  qed
qed

lemma iuw_abs_add_new: "iuw_abs (iuw_add_new args rel1 rel2 nt aux) = uw_add_new args rel1 rel2 nt (iuw_abs aux)"
  using iuw_abs_shift[of args nt aux]
  by (auto simp: iuw_add_new_def uw_add_new_def iuw_abs_def Let_def split: prod.splits)

lemma iuw_eval_abs: "iuw_eval args nt aux = (zs, aux') \<Longrightarrow>
    uw_eval args nt (iuw_abs aux) = (map iset zs, iuw_abs aux')"
  using iuw_abs_shift[of args nt aux]
  by (auto simp: iuw_eval_def uw_eval_def iuw_abs_def rev_map split: prod.splits)

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

lemma riud_add_new: "udux_add_new args msk rel1 rel2 nt (riud d) = riud (iudux_add_new args msk rel1 rel2 nt d)"
  by (cases d) (simp_all add: iuw_abs_add_new)

lemma riud_eval:
  "udux_eval args nt (riud d) = (case iudux_eval args nt d of (zs, d') \<Rightarrow> (map iset zs, riud d'))"
proof (cases d)
  case (IUDUX_win w)
  then show ?thesis
    using iuw_eval_abs[of args nt w] by (cases "iuw_eval args nt w") simp
qed (simp add: comp_def split: prod.splits)

lemma iuedsx_eval_since_abs:
  "uedsx_eval_since args (map iset rs) buf (riu aux) =
     (case iuedsx_eval_since args rs buf aux of (zs, b, a) \<Rightarrow> (map iset zs, b, riu a))"
proof (induct args rs buf aux rule: iuedsx_eval_since.induct)
  case (1 args rs xs ys ts skew aux)
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  note simps = uedsx_eval_since.simps[of args _ xs ys ts skew]
    iuedsx_eval_since.simps[of args _ xs ys ts skew]
  show ?case
  proof (cases y)
    case None
    then show ?thesis
      unfolding simps using x y t by (cases x; cases t) (simp_all add: rev_map Let_def)
  next
    case Y: (Some y1)
    show ?thesis
    proof (cases skew)
      case True
      have IH: "uedsx_eval_since args (map iset rs) (xs, ys', ts, False)
          (udsx_add_new_table args y1 (riu aux)) =
        (case iuedsx_eval_since args rs (xs, ys', ts, False) (iudsx_add_new_table args y1 aux) of
          (zs, b, a) \<Rightarrow> (map iset zs, b, riu a))"
        using 1(1)[OF y[symmetric] Y True] by simp
      show ?thesis
        unfolding simps using y Y True IH by simp
    next
      case False
      show ?thesis
      proof (cases x)
        case None
        then show ?thesis unfolding simps using x y Y False by (simp add: rev_map)
      next
        case X: (Some x1)
        show ?thesis
        proof (cases t)
          case None
          then show ?thesis unfolding simps using x y t Y X False by (simp add: rev_map)
        next
          case T: (Some t1)
          let ?a = "iudsx_add_new_table args y1 (iudsx_join args x1 (iudsx_add_new_ts args t1 aux))"
          have IH: "uedsx_eval_since args (map iset (iudsx_result args ?a # rs)) (xs', ys', ts', False)
              (riu ?a) =
            (case iuedsx_eval_since args (iudsx_result args ?a # rs) (xs', ys', ts', False) ?a of
              (zs, b, a) \<Rightarrow> (map iset zs, b, riu a))"
            by (rule 1(2)[OF y[symmetric] Y False x[symmetric] X t[symmetric] T refl])
          show ?thesis
            unfolding simps using x y t Y X T False IH by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed
(*<*)
end
(*>*)
