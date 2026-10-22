(*<*)
theory Since_Agg_Proof
  imports "Monitor_Exec.Since_Agg" Window_Proof Frame_Aux_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The parameters the compiler builds from a fused node's aggregation are well formed at the
  width of the node's operand.\<close>

lemma ins_pos_le: "ins_pos cs y \<le> length cs"
  by (simp add: ins_pos_def)

lemma eagg_ok_agg:
  assumes "Formula.fv_trm f \<subseteq> set (agg_cols k g)" and "g0 \<Longrightarrow> g = []"
  shows "eagg_ok (g0, \<omega>, reindex_trm (agg_cols k g) f, k, ins_pos g y) (length (agg_cols k g))"
  using fv_reindex_trm[OF assms(1)] assms(2) ins_pos_le[of g y] by auto

text \<open>The kernel reads a window's tuple at the frame: its group key is the tuple's suffix after
  the bound columns, and the shifted term evaluates to the term on the tuple.\<close>

text \<open>The executable aggregation is the kernel's aggregation at the ascending frame, with the result
  column moved into place.\<close>

lemma cnt_leave_rep: "cnt_rep f cc \<Longrightarrow> cnt_leave T cc = {x \<in> T. f x = 1}"
  unfolding cnt_leave_def cnt_rep_def by (auto split: if_splits)

lemma cnt_rep_snd_del: "cnt_rep f cc \<Longrightarrow> finite T \<Longrightarrow> snd (cnt_del T cc) = snd cc - cnt_leave T cc"
  using cnt_rep_del[of f cc T] cnt_leave_rep[of f cc T] unfolding cnt_rep_def by auto

lemma cnt_leave_sub: assumes "cnt_rep f cc" shows "cnt_leave T cc \<subseteq> snd cc"
  using assms unfolding cnt_leave_rep[OF assms] cnt_rep_def by auto

lemma kag_inv_del:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and inv: "kag_inv p w cc ax"
  shows "kag_inv p w (cnt_del T cc) (kag_del p w T cc ax)"
proof (cases ax)
  case None
  then show ?thesis by (simp add: kag_inv_def kag_del_def)
next
  case (Some a)
  let ?X = "snd cc" and ?Y = "cnt_leave T cc"
  have v: "valid_maggaux (eagg_args p w) a ?X" using inv by (simp add: kag_inv_def Some)
  have sub: "?Y \<subseteq> ?X" by (rule cnt_leave_sub[OF cr])
  have XY: "?X - ?Y = snd (cnt_del T cc)" unfolding cnt_rep_snd_del[OF cr fT] ..
  show ?thesis
    using valid_delete_maggaux[OF v sub] unfolding XY
    by (auto simp: kag_inv_def kag_del_def Some split: prod.splits)
qed

lemma delete_cnt_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
  shows "delete_cnt args t = gd_cnt k t"
  using assms by (intro ext) (auto simp: Let_def)

lemma delete_sum_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "delete_sum args t = gd_sum k ev t"
  using assms by (intro ext) (auto simp: Let_def)

lemma delete_rank_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "delete_rank args ty t = gd_rank k ev ty t"
  using assms by (intro ext) (auto simp: Let_def)

lemma cfc_delete_cnt: "comp_fun_commute_on UNIV (delete_cnt args)"
  using delete_cnt_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_sum: "comp_fun_commute_on UNIV (delete_sum args)"
  using delete_sum_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_rank: "comp_fun_commute_on UNIV (delete_rank args ty)"
  using delete_rank_comm by unfold_locales (auto simp: fun_eq_iff)

lemma delete_maggaux'_Rk_gen:
  assumes d: "distinct xs"
    and tup: "\<And>t. t \<in> set xs \<Longrightarrow> agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t \<and>
       meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "delete_maggaux' args (set xs) (map_option Rk ax) = map_option Rk (gdel k ev xs ax)"
proof -
  have c: "fold (delete_cnt args) xs s' = fold (gd_cnt k) xs s'" for s'
    by (rule fold_cong) (simp_all add: delete_cnt_Rk tup)
  have sm: "fold (delete_sum args) xs s' = fold (gd_sum k ev) xs s'" for s'
    by (rule fold_cong) (simp_all add: delete_sum_Rk tup)
  have r: "fold (delete_rank args ty) xs s' = fold (gd_rank k ev ty) xs s'" for ty s'
    by (rule fold_cong) (simp_all add: delete_rank_Rk tup)
  have fc: "fold (gstep_del k ev) xs (Some (GCnt m)) =
      (case fold (gd_cnt k) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GCnt m') else None)" for m
    by (rule fold_flag) (simp_all add: gstep_del_def)
  have fs: "fold (gstep_del k ev) xs (Some (GSum m)) =
      (case fold (gd_sum k ev) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GSum m') else None)" for m
    by (rule fold_flag) (simp_all add: gstep_del_def)
  have fr: "fold (gstep_del k ev) xs (Some (GRank m ty)) =
      (case fold (gd_rank k ev ty) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GRank m' ty) else None)"
    for m ty
    by (rule fold_flag[where C = "\<lambda>m. GRank m ty"]) (simp_all add: gstep_del_def)
  show ?thesis
  proof (cases ax)
    case (Some a)
    show ?thesis
    proof (cases a)
      case (GCnt m)
      show ?thesis
        unfolding Some GCnt gdel_def fc
        by (simp add: fold_set_list[OF cfc_delete_cnt d] c split: prod.splits)
    next
      case (GSum m)
      show ?thesis
        unfolding Some GSum gdel_def fs
        by (simp add: fold_set_list[OF cfc_delete_sum d] sm split: prod.splits)
    next
      case (GRank m ty)
      show ?thesis
        unfolding Some GRank gdel_def fr
        by (simp add: fold_set_list[OF cfc_delete_rank d] r split: prod.splits)
    qed
  qed simp
qed

lemma ag_del_Rk:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and fT: "finite T" and T: "ewf_table w T"
  shows "map_option Rk (ag_del (g0, \<omega>, f, k, pos) w T cc ax)
    = kag_del (g0, \<omega>, f, k, pos) w T cc (map_option Rk ax)"
proof -
  let ?xs = "filter (\<lambda>t. Mapping.lookup (fst cc) t = Some 1) (csl T)"
  have s: "set ?xs = cnt_leave T cc" and d: "distinct ?xs"
    using csl_etuple[OF fT] by (auto simp: cnt_leave_def)
  have tup: "t \<in> set ?xs \<Longrightarrow> agg_key (length (aggargs_tys (eagg_args (g0, \<omega>, f, k, pos) w)))
      (aggargs_cols (eagg_args (g0, \<omega>, f, k, pos) w)) t = drop k t \<and>
     meval_trm (aggargs_cols (eagg_args (g0, \<omega>, f, k, pos) w))
      (aggargs_f (eagg_args (g0, \<omega>, f, k, pos) w)) t = umeval_trm f t" for t
    using T csl_etuple[OF fT] agg_key_dagg[OF ok] meval_shift_dagg[OF ok]
    by (simp del: eagg_ccols.simps)
  show ?thesis
    unfolding ag_del_def kag_del_def prod.case
    using delete_maggaux'_Rk_gen[OF d tup, of ax] unfolding s by simp
qed

lemma ag_inv_del:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and ok: "eagg_ok p w"
    and T: "ewf_table w T" and S: "ewf_table w (snd cc)" and inv: "ag_inv p w cc ax"
  shows "ag_inv p w (cnt_del T cc) (ag_del p w T cc ax)"
proof -
  obtain g0 \<omega> f' k pos where p: "p = (g0, \<omega>, f', k, pos)" by (cases p)
  show ?thesis
    using kag_inv_del[OF cr fT inv[unfolded ag_inv_def]]
    unfolding ag_inv_def p ag_del_Rk[OF ok[unfolded p] fT T] .
qed

subsubsection \<open>The scans, and what the window's validity says about its tables\<close>

lemma sa_move_rep:
  assumes "linearize pend = pl" and "sa_move args p nt pend win cc ax = (pend', win', cc', ax')"
  shows "sw_move args nt pend win cc = (pend', win', cc') \<and>
    (cnt_rep f cc \<longrightarrow> eagg_ok p (args_n args) \<longrightarrow>
     (\<forall>e \<in> set pl. finite (snd e) \<and> ewf_table (args_n args) (snd e)) \<longrightarrow>
     ewf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
     ag_inv p (args_n args) cc' ax')"
  using assms
proof (induct pl arbitrary: pend win cc ax pend' win' cc' ax' f)
  case Nil
  obtain ho pend0 where sh: "safe_hd pend = (ho, pend0)" by (cases "safe_hd pend")
  have "ho = None" and "linearize pend0 = []"
    using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  then show ?case using Nil(2) by (subst (asm) sa_move.simps, subst sw_move.simps) (simp add: sh)
next
  case (Cons e rest)
  obtain ho pend0 where sh: "safe_hd pend = (ho, pend0)" by (cases "safe_hd pend")
  have l0: "linearize pend0 = e # rest" using safe_hd_rep[OF sh] Cons(2) by simp
  have ho: "ho = Some e" using safe_hd_rep[OF sh] l0 by (cases ho) auto
  have lt: "linearize (tl_queue pend0) = rest" by (simp add: tl_queue_rep l0)
  show ?case
  proof (cases "memL (args_ivl args) (nt - fst e)")
    case True
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - fst e)")
      case r: True
      have rec: "sa_move args p nt (tl_queue pend0) (append_queue e win) (cnt_add (snd e) cc)
          (ag_ins p (args_n args) (snd e) cc ax) = (pend', win', cc', ax')"
        using Cons(3) by (subst (asm) sa_move.simps) (simp add: sh ho True r)
      note IH = Cons(1)[OF lt rec, of "\<lambda>x. if x \<in> snd e then f x + 1 else f x"]
      have sw: "sw_move args nt pend win cc = (pend', win', cc')"
        using IH by (subst sw_move.simps) (simp add: sh ho True r)
      moreover have "ag_inv p (args_n args) cc' ax'"
        if cr: "cnt_rep f cc" and ok: "eagg_ok p (args_n args)"
          and tb: "\<forall>e \<in> set (e # rest). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
          and S: "ewf_table (args_n args) (snd cc)" and inv: "ag_inv p (args_n args) cc ax"
      proof -
        have fe: "finite (snd e)" and de: "ewf_table (args_n args) (snd e)" using tb by auto
        show ?thesis
          using IH[THEN conjunct2, rule_format, OF cnt_rep_add[OF cr fe] ok _ _
              ag_inv_ins[OF cr fe ok de S inv]] tb S de
          unfolding cnt_rep_snd_add[OF cr fe] by auto
      qed
      ultimately show ?thesis by blast
    next
      case r: False
      have rec: "sa_move args p nt (tl_queue pend0) win cc ax = (pend', win', cc', ax')"
        using Cons(3) by (subst (asm) sa_move.simps) (simp add: sh ho True r)
      note IH = Cons(1)[OF lt rec, of f]
      have "sw_move args nt pend win cc = (pend', win', cc')"
        using IH by (subst sw_move.simps) (simp add: sh ho True r)
      then show ?thesis using IH by auto
    qed
  next
    case False
    have "(pend0, win, cc, ax) = (pend', win', cc', ax')"
      using Cons(3) by (subst (asm) sa_move.simps) (simp add: sh ho False)
    then show ?thesis by (subst sw_move.simps) (simp add: sh ho False)
  qed
qed

lemma sa_expire_rep:
  assumes "linearize win = wl" and "sa_expire args p nt win cc ax = (win', cc', ax')"
  shows "sw_expire args nt win cc = (win', cc') \<and>
    (cnt_rep f cc \<longrightarrow> eagg_ok p (args_n args) \<longrightarrow>
     (\<forall>e \<in> set wl. finite (snd e) \<and> ewf_table (args_n args) (snd e)) \<longrightarrow>
     ewf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
     ag_inv p (args_n args) cc' ax')"
  using assms
proof (induct wl arbitrary: win cc ax win' cc' ax' f)
  case Nil
  obtain ho win0 where sh: "safe_hd win = (ho, win0)" by (cases "safe_hd win")
  have "ho = None" and "linearize win0 = []"
    using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  then show ?case using Nil(2) by (subst (asm) sa_expire.simps, subst sw_expire.simps) (simp add: sh)
next
  case (Cons e rest)
  obtain ho win0 where sh: "safe_hd win = (ho, win0)" by (cases "safe_hd win")
  have l0: "linearize win0 = e # rest" using safe_hd_rep[OF sh] Cons(2) by simp
  have ho: "ho = Some e" using safe_hd_rep[OF sh] l0 by (cases ho) auto
  have lt: "linearize (tl_queue win0) = rest" by (simp add: tl_queue_rep l0)
  show ?case
  proof (cases "memR (args_ivl args) (nt - fst e)")
    case True
    have "(win0, cc, ax) = (win', cc', ax')"
      using Cons(3) by (subst (asm) sa_expire.simps) (simp add: sh ho True)
    then show ?thesis by (subst sw_expire.simps) (simp add: sh ho True)
  next
    case False
    have rec: "sa_expire args p nt (tl_queue win0) (cnt_del (snd e) cc)
        (ag_del p (args_n args) (snd e) cc ax) = (win', cc', ax')"
      using Cons(3) by (subst (asm) sa_expire.simps) (simp add: sh ho False)
    note IH = Cons(1)[OF lt rec, of "\<lambda>x. if x \<in> snd e then f x - 1 else f x"]
    have sw: "sw_expire args nt win cc = (win', cc')"
      using IH by (subst sw_expire.simps) (simp add: sh ho False)
    moreover have "ag_inv p (args_n args) cc' ax'"
      if cr: "cnt_rep f cc" and ok: "eagg_ok p (args_n args)"
        and tb: "\<forall>e \<in> set (e # rest). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
        and S: "ewf_table (args_n args) (snd cc)" and inv: "ag_inv p (args_n args) cc ax"
    proof -
      have fe: "finite (snd e)" and de: "ewf_table (args_n args) (snd e)" using tb by auto
      show ?thesis
        using IH[THEN conjunct2, rule_format, OF cnt_rep_del[OF cr fe] ok _ _
            ag_inv_del[OF cr fe ok de S inv]] tb S de
        unfolding cnt_rep_snd_del[OF cr fe] by auto
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma valid_sw_tables:
  assumes v: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
  shows "\<forall>e \<in> set (linearize pend @ linearize win). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
    and "ewf_table (args_n args) (snd cc)" and "cnt_rep (cnt_of (map snd (linearize win))) cc"
proof -
  have tb: "\<And>e. e \<in> set (linearize pend @ linearize win) \<Longrightarrow> finite (snd e)"
    using v by (auto simp: valid_sw_def sw_inv_def)
  have at: "\<And>u. tbls_at u (linearize pend @ linearize win) = tbls_at u auxlist"
    using v by (auto simp: valid_sw_def)
  have aux: "\<And>t rel. (t, rel) \<in> set auxlist \<Longrightarrow> table (args_R args) rel"
    using v by (auto simp: valid_sw_def)
  have dwf: "ewf_table (args_n args) (snd e)" if e: "e \<in> set (linearize pend @ linearize win)" for e
  proof
    fix x assume x: "x \<in> snd e"
    obtain u rel where eu: "e = (u, rel)" by (cases e)
    have "x \<in> tbls_at u (linearize pend @ linearize win)" using e x by (auto simp: in_tbls_at eu)
    then obtain rel' where "(u, rel') \<in> set auxlist" "x \<in> rel'" unfolding at by (auto simp: in_tbls_at)
    then show "length x = args_n args" using aux R by (auto simp: table_def wf_tuple_def)
  qed
  show "\<forall>e \<in> set (linearize pend @ linearize win). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
    using tb dwf by auto
  show cr: "cnt_rep (cnt_of (map snd (linearize win))) cc" using v by (auto simp: valid_sw_def)
  show "ewf_table (args_n args) (snd cc)" using cnt_inv_set[OF cr] dwf by auto
qed

subsubsection \<open>Validity\<close>

lemma valid_sa_init: "length (args_R args) = args_n args \<Longrightarrow> eagg_ok p (args_n args) \<Longrightarrow>
  valid_sa args p 0 (sa_init args p) []"
  using valid_sw_init[of args] by (auto simp: valid_sa_def sa_init_def sw_init_def ag_inv_init)

lemma valid_sa_add_new_ts:
  assumes v: "valid_sa args p cur aux auxlist" and nt: "cur \<le> nt"
  shows "valid_sa args p nt (sa_add_new_ts args p nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  obtain pend' win' cc' ax' where m: "sa_move args p nt pend win cc ax = (pend', win', cc', ax')"
    by (cases "sa_move args p nt pend win cc ax")
  obtain win'' cc'' ax'' where x: "sa_expire args p nt win' cc' ax' = (win'', cc'', ax'')"
    by (cases "sa_expire args p nt win' cc' ax'")
  note tbl = valid_sw_tables[OF vsw R]
  note mr = sa_move_rep[OF refl m, of "cnt_of (map snd (linearize win))"]
  have sw1: "sw_move args nt pend win cc = (pend', win', cc')" using mr by simp
  have inv1: "ag_inv p (args_n args) cc' ax'" using mr tbl ok inv by auto
  let ?moved = "filter (\<lambda>e. memR (args_ivl args) (nt - fst e))
    (takeWhile (\<lambda>e. memL (args_ivl args) (nt - fst e)) (linearize pend))"
  have rep: "linearize win' = linearize win @ ?moved" "cc' = fold cnt_add (map snd ?moved) cc"
    using sw_move_rep[OF refl sw1] by simp_all
  have moved: "set ?moved \<subseteq> set (linearize pend)" by (auto dest: set_takeWhileD)
  have tb1: "\<forall>e \<in> set (linearize win'). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
    using tbl(1) moved unfolding rep(1) by auto
  have cr1: "cnt_rep (cnt_of (map snd (linearize win'))) cc'"
  proof -
    have fm: "\<forall>T \<in> set (map snd ?moved). finite T" using tbl(1) by (fastforce dest!: set_takeWhileD)
    show ?thesis unfolding rep using cnt_inv_adds[OF tbl(3) fm] by simp
  qed
  have S1: "ewf_table (args_n args) (snd cc')" using cnt_inv_set[OF cr1] tb1 by auto
  note xr = sa_expire_rep[OF refl x, of "cnt_of (map snd (linearize win'))"]
  have sw2: "sw_expire args nt win' cc' = (win'', cc'')" using xr by simp
  have inv2: "ag_inv p (args_n args) cc'' ax''" using xr cr1 ok tb1 S1 inv1 by auto
  have "sw_add_new_ts args nt (t, pend, win, cc) = (nt, pend', win'', cc'')"
    by (simp add: sw_add_new_ts_def sw1 sw2)
  then show ?thesis
    using valid_sw_add_new_ts[OF vsw nt] R ok inv2
    by (simp add: valid_sa_def sa_add_new_ts_def aux m x)
qed

lemma valid_sa_join:
  assumes v: "valid_sa args p cur aux auxlist"
    and t1: "table [] rel1" and X: "(X = {}) = (rel1 = {})"
  shows "valid_sa args p cur (sa_join args p X aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) [] rel1)) auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  show ?thesis
    using valid_sw_join[OF vsw t1 X] R ok inv ag_inv_init[of p "args_n args"]
    by (auto simp: valid_sa_def sa_join_def sw_join_def aux)
qed

lemma valid_sa_add_new_table:
  assumes v: "valid_sa args p cur aux auxlist"
    and t2: "table (args_R args) rel2" and f2: "finite rel2"
  shows "valid_sa args p cur (sa_add_new_table args p rel2 aux)
    (case auxlist of [] \<Rightarrow> [(cur, rel2)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  note tbl = valid_sw_tables[OF vsw R]
  have d2: "ewf_table (args_n args) rel2" using t2 R by (auto simp: table_def wf_tuple_def)
  have "ag_inv p (args_n args) (cnt_add rel2 cc) (ag_ins p (args_n args) rel2 cc ax)"
    by (rule ag_inv_ins[OF tbl(3) f2 ok d2 tbl(2) inv])
  then show ?thesis
    using valid_sw_add_new_table[OF vsw t2 f2] R ok inv
    by (auto simp: valid_sa_def sa_add_new_table_def sw_add_new_table_def aux)
qed

lemma valid_sa_result:
  assumes v: "valid_sa args p cur aux auxlist"
  shows "sa_result args p aux =
    eagg_p p (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  have "sa_result args p aux = eagg_p p (snd cc)"
    using ag_res_inv[OF inv ok valid_sw_tables(2)[OF vsw R]] by (simp add: sa_result_def aux)
  also have "snd cc = sw_result args (t, pend, win, cc)" by (simp add: sw_result_def)
  finally show ?thesis unfolding valid_sw_result[OF vsw] .
qed

lemma lookup_None_keys: "(Mapping.lookup c t = None) = (t \<notin> Mapping.keys c)"
  by (simp add: Mapping.keys_dom_lookup domIff)

lemma cnt_add1_ucc: "cnt_add1 t (ucc c) = ucc (ucnt_add1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: cnt_add1_def ucnt_add1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis by (simp add: cnt_add1_def ucnt_add1_def ucc.simps insert_absorb)
qed

lemma cnt_del1_ucc: "cnt_del1 t (ucc c) = ucc (ucnt_del1 t c)"
proof (cases "Mapping.lookup c t")
  case None
  then show ?thesis by (simp add: cnt_del1_def ucnt_del1_def ucc.simps)
next
  case (Some k)
  have "t \<in> Mapping.keys c" using Some lookup_None_keys[of c t] by simp
  with Some show ?thesis
    by (simp add: cnt_del1_def ucnt_del1_def ucc.simps insert_absorb)
qed

lemma fold_cnt_add1_ucc: "fold cnt_add1 xs (ucc c) = ucc (fold ucnt_add1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: cnt_add1_ucc)

lemma fold_cnt_del1_ucc: "fold cnt_del1 xs (ucc c) = ucc (fold ucnt_del1 xs c)"
  by (induct xs arbitrary: c) (simp_all add: cnt_del1_ucc)

lemma cnt_add_ucc[simp]: "cnt_add T (ucc c) = ucc (ucnt_add T c)"
  by (simp add: cnt_add_def ucnt_add_def fold_cnt_add1_ucc)

lemma cnt_del_ucc[simp]: "cnt_del T (ucc c) = ucc (ucnt_del T c)"
  by (simp add: cnt_del_def ucnt_del_def fold_cnt_del1_ucc)

lemma ag_ins_ucc[simp]: "ag_ins p w T (ucc c) ax = uag_ins p w T c ax"
  by (cases p) (simp add: ag_ins_def uag_ins_def ucc.simps lookup_None_keys)

lemma ufilt_Some: "ufilt (Some c) X = Set.filter (ueval_constraint c) X"
  by (simp add: ufilt_def uqok_def)

lemma ag_res_ucc: "ufilt q (ag_res p w (ucc c) ax) = uag_res q p w c ax"
  by (cases ax; cases p) (simp_all add: uag_res_def ag_res_def ucc.simps id_def)

lemma ag_res_ucc_None[simp]: "ag_res p w (ucc c) ax = uag_res None p w c ax"
  using ag_res_ucc[of None] by simp

(*<*)
end
(*>*)
