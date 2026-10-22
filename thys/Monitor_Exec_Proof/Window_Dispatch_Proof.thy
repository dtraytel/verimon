(*<*)
theory Window_Dispatch_Proof
  imports "Monitor_Exec.Window_Dispatch" Agg_Cache_Proof Match_Window_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma esx_post_add_new_ts[simp]: "esx_post (esx_add_new_ts args nt d) = esx_post d"
  by (cases d) simp_all

lemma esx_post_join[simp]: "esx_post (esx_join args X d) = esx_post d"
  by (cases d) simp_all

lemma esx_post_add_new_table[simp]: "esx_post (esx_add_new_table args X d) = esx_post d"
  by (cases d) simp_all

lemma esx_post_init[simp]: "esx_post (esx_init args msk) = id"
  by (simp add: esx_init_def)

lemma esx_post_init_agg[simp]: "esx_post (esx_init_agg args p) = eagg_p p"
  by (simp add: esx_init_agg_def)

lemma esx_post_eq: "esx_post d = (case esx_agg d of None \<Rightarrow> id | Some p \<Rightarrow> eagg_p p)"
  by (cases d) simp_all

lemma esx_agg_add_new_ts[simp]: "esx_agg (esx_add_new_ts args nt d) = esx_agg d"
  by (cases d) simp_all

lemma esx_agg_join[simp]: "esx_agg (esx_join args X d) = esx_agg d"
  by (cases d) simp_all

lemma esx_agg_add_new_table[simp]: "esx_agg (esx_add_new_table args X d) = esx_agg d"
  by (cases d) simp_all

lemma esx_agg_init[simp]: "esx_agg (esx_init args msk) = None"
  by (simp add: esx_init_def)

lemma esx_agg_init_agg[simp]: "esx_agg (esx_init_agg args p) = Some p"
  by (simp add: esx_init_agg_def)

lemma esxaux'_tables:
  "esxaux' kR cR cL args cur daux auxlist \<Longrightarrow> \<forall>(t, rel) \<in> set auxlist. table kR rel"
  by (cases daux) (auto simp: esxaux'_def esaux'_def)

lemma esxaux'_init:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "esxaux' kR cR cL args 0 (esx_init (eargs cR cL args) (emsk cR cL)) []"
  using esaux'_init[OF fR fL sub, of args] valid_sw_init
  by (auto simp: esxaux'_def esx_init_def eauxlist_def)

lemma esxaux'_init_agg:
  assumes c: "cL = []" and ok: "eagg_ok p (length cR)"
  shows "esxaux' kR cR cL args 0 (esx_init_agg (eargs cR cL args) p) []"
  using valid_sa_init[of "eargs cR cL args" p] c ok
  by (auto simp: esxaux'_def esx_init_agg_def eauxlist_def)

lemma esxaux'_add_new_ts:
  assumes v: "esxaux' kR cR cL args cur daux auxlist" and nt: "cur \<le> nt"
  shows "esxaux' kR cR cL args nt (esx_add_new_ts (eargs cR cL args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof (cases daux)
  case (ESX_gen d)
  then show ?thesis using esaux'_add_new_ts[OF _ nt, of kR cR cL args d auxlist] v
    by (simp add: esxaux'_def)
next
  case (ESX_win w)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sw (eargs cR cL args) cur w (eauxlist kR cR auxlist)"
    using v unfolding ESX_win esxaux'_def by auto
  have "valid_sw (eargs cR cL args) nt (sw_add_new_ts (eargs cR cL args) nt w)
      (filter (\<lambda>(t, rel). memR (args_ivl (eargs cR cL args)) (nt - t)) (eauxlist kR cR auxlist))"
    by (rule valid_sw_add_new_ts[OF vs nt])
  then show ?thesis using c w unfolding ESX_win by (simp add: esxaux'_def eauxlist_filter)
next
  case (ESX_wagg p a)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sa (eargs cR cL args) p cur a (eauxlist kR cR auxlist)"
    using v unfolding ESX_wagg esxaux'_def by auto
  have "valid_sa (eargs cR cL args) p nt (sa_add_new_ts (eargs cR cL args) p nt a)
      (filter (\<lambda>(t, rel). memR (args_ivl (eargs cR cL args)) (nt - t)) (eauxlist kR cR auxlist))"
    by (rule valid_sa_add_new_ts[OF vs nt])
  then show ?thesis using c w unfolding ESX_wagg by (simp add: esxaux'_def eauxlist_filter)
qed

lemma esxaux'_join:
  assumes v: "esxaux' kR cR cL args cur daux auxlist"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and t1: "table kL rel1"
  shows "esxaux' kR cR cL args cur (esx_join (eargs cR cL args) (etabc kL cL rel1) daux)
      (map (\<lambda>(t, rel). (t, join kR rel (args_pos args) kL rel1)) auxlist)"
proof (cases daux)
  case (ESX_gen d)
  have vd: "esaux' kR cR cL args cur d auxlist" using v unfolding ESX_gen by (simp add: esxaux'_def)
  show ?thesis unfolding ESX_gen by (simp add: esxaux'_def esaux'_join[OF vd fR fL sub t1])
next
  case (ESX_win w)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sw (eargs cR cL args) cur w (eauxlist kR cR auxlist)"
    using v unfolding ESX_win esxaux'_def by auto
  have t1': "table [] (etabc kL cL rel1)" using table_etabc[of cL kL rel1] c by simp
  have "valid_sw (eargs cR cL args) cur (sw_join (eargs cR cL args) (etabc kL cL rel1) w)
      (map (\<lambda>(t, rel). (t, join cR rel (args_pos args) cL (etabc kL cL rel1)))
        (eauxlist kR cR auxlist))"
    using valid_sw_join[OF vs t1' refl] c by simp
  then show ?thesis using c eauxlist_wf_join[OF w sub t1, of "args_pos args"] unfolding ESX_win
    by (simp add: esxaux'_def eauxlist_join[OF fR fL sub w t1])
next
  case (ESX_wagg p a)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sa (eargs cR cL args) p cur a (eauxlist kR cR auxlist)"
    using v unfolding ESX_wagg esxaux'_def by auto
  have t1': "table [] (etabc kL cL rel1)" using table_etabc[of cL kL rel1] c by simp
  have "valid_sa (eargs cR cL args) p cur (sa_join (eargs cR cL args) p (etabc kL cL rel1) a)
      (map (\<lambda>(t, rel). (t, join cR rel (args_pos args) cL (etabc kL cL rel1)))
        (eauxlist kR cR auxlist))"
    using valid_sa_join[OF vs t1' refl] c by simp
  then show ?thesis using c eauxlist_wf_join[OF w sub t1, of "args_pos args"] unfolding ESX_wagg
    by (simp add: esxaux'_def eauxlist_join[OF fR fL sub w t1])
qed

lemma esxaux'_add_new_table:
  assumes v: "esxaux' kR cR cL args cur daux auxlist"
    and t2: "table kR rel2" and f2: "finite rel2"
  shows "esxaux' kR cR cL args cur
      (esx_add_new_table (eargs cR cL args) (etabc kR cR rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof (cases daux)
  case (ESX_gen d)
  have vd: "esaux' kR cR cL args cur d auxlist" using v unfolding ESX_gen by (simp add: esxaux'_def)
  show ?thesis unfolding ESX_gen by (simp add: esxaux'_def esaux'_add_new_table[OF vd t2])
next
  case (ESX_win w)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sw (eargs cR cL args) cur w (eauxlist kR cR auxlist)"
    using v unfolding ESX_win esxaux'_def by auto
  have tt: "table (args_R (eargs cR cL args)) (etabc kR cR rel2)" by (simp add: table_etabc)
  have ff: "finite (etabc kR cR rel2)" using f2 by (rule finite_etabc)
  have "valid_sw (eargs cR cL args) cur
      (sw_add_new_table (eargs cR cL args) (etabc kR cR rel2) w)
      (case eauxlist kR cR auxlist of [] \<Rightarrow> [(cur, etabc kR cR rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> etabc kR cR rel2) # r
                         else (cur, etabc kR cR rel2) # eauxlist kR cR auxlist)"
    by (rule valid_sw_add_new_table[OF vs tt ff])
  then show ?thesis using c eauxlist_wf_add_new_table[OF w t2, of cur] unfolding ESX_win
    by (simp add: esxaux'_def eauxlist_add_new_table[symmetric])
next
  case (ESX_wagg p a)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sa (eargs cR cL args) p cur a (eauxlist kR cR auxlist)"
    using v unfolding ESX_wagg esxaux'_def by auto
  have tt: "table (args_R (eargs cR cL args)) (etabc kR cR rel2)" by (simp add: table_etabc)
  have ff: "finite (etabc kR cR rel2)" using f2 by (rule finite_etabc)
  have "valid_sa (eargs cR cL args) p cur
      (sa_add_new_table (eargs cR cL args) p (etabc kR cR rel2) a)
      (case eauxlist kR cR auxlist of [] \<Rightarrow> [(cur, etabc kR cR rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> etabc kR cR rel2) # r
                         else (cur, etabc kR cR rel2) # eauxlist kR cR auxlist)"
    by (rule valid_sa_add_new_table[OF vs tt ff])
  then show ?thesis using c eauxlist_wf_add_new_table[OF w t2, of cur] unfolding ESX_wagg
    by (simp add: esxaux'_def eauxlist_add_new_table[symmetric])
qed

lemma esxaux'_result:
  assumes v: "esxaux' kR cR cL args cur daux auxlist"
  shows "esx_result (eargs cR cL args) daux
      = esx_post daux (etabc kR cR (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist,
          memL (args_ivl args) (cur - t)] {}))"
proof (cases daux)
  case (ESX_gen d)
  then show ?thesis using esaux'_result[of kR cR cL args cur d auxlist] v
    by (simp add: esxaux'_def)
next
  case (ESX_win w)
  have vs: "valid_sw (eargs cR cL args) cur w (eauxlist kR cR auxlist)"
    using v unfolding ESX_win esxaux'_def by auto
  have "sw_result (eargs cR cL args) w
      = foldr (\<union>) [rel. (t, rel) \<leftarrow> eauxlist kR cR auxlist,
          memL (args_ivl (eargs cR cL args)) (cur - t)] {}"
    by (rule valid_sw_result[OF vs])
  then show ?thesis unfolding ESX_win by (simp add: etabc_result)
next
  case (ESX_wagg p a)
  have vs: "valid_sa (eargs cR cL args) p cur a (eauxlist kR cR auxlist)"
    using v unfolding ESX_wagg esxaux'_def by auto
  have "sa_result (eargs cR cL args) p a
      = eagg_p p (foldr (\<union>) [rel. (t, rel) \<leftarrow> eauxlist kR cR auxlist,
          memL (args_ivl (eargs cR cL args)) (cur - t)] {})"
    by (rule valid_sa_result[OF vs])
  then show ?thesis unfolding ESX_wagg by (simp add: etabc_result)
qed

lemma esx_agg_eval_since:
  "esx_eval_since args rs buf daux = (dzs, buf', daux') \<Longrightarrow> esx_agg daux' = esx_agg daux"
  by (induct args rs buf daux arbitrary: dzs buf' daux' rule: esx_eval_since.induct)
    (auto simp: Let_def split: if_splits)

lemma eux_post_eq: "eux_post d = (case eux_agg d of None \<Rightarrow> id | Some p \<Rightarrow> eagg_p p)"
  by (cases d) simp_all

lemma eux_post_add_new[simp]: "eux_post (eux_add_new args msk rel1 rel2 nt d) = eux_post d"
  by (cases d) simp_all

lemma eux_agg_add_new[simp]: "eux_agg (eux_add_new args msk rel1 rel2 nt d) = eux_agg d"
  by (cases d) simp_all

lemma eux_post_init[simp]: "eux_post (eux_init args) = id"
  by (simp add: eux_init_def)

lemma eux_agg_init[simp]: "eux_agg (eux_init args) = None"
  by (simp add: eux_init_def)

lemma eux_post_init_agg[simp]: "eux_post (eux_init_agg args p) = eagg_p p"
  by (simp add: eux_init_agg_def)

lemma eux_agg_init_agg[simp]: "eux_agg (eux_init_agg args p) = Some p"
  by (simp add: eux_init_agg_def)

lemma eux_post_eval[simp]: "eux_post (snd (eux_eval args nt d)) = eux_post d"
  by (cases d) (simp_all split: prod.splits)

lemma eux_agg_eval[simp]: "eux_agg (snd (eux_eval args nt d)) = eux_agg d"
  by (cases d) (simp_all split: prod.splits)

lemma euxaux'_tables:
  "euxaux' kL cL kR cR args cur daux auxlist \<Longrightarrow>
     \<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
  by (cases daux) (auto simp: euxaux'_def euaux'_def)

lemma euxaux'_init:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "euxaux' kL cL kR cR args 0 (eux_init (eargs cR cL args)) []"
  using euaux'_init[OF fR fL sub, of args, folded ginit_dq_eq] valid_uw_init
  by (auto simp: euxaux'_def eux_init_def eauxlist3_def)

lemma euxaux'_init_agg:
  assumes c: "cL = []" and inz: "memL (args_ivl args) 0"
    and ok: "eagg_ok p (length cR)"
  shows "euxaux' kL cL kR cR args 0 (eux_init_agg (eargs cR cL args) p) []"
  using valid_ua_init[of "eargs cR cL args" p] c inz ok
  by (auto simp: euxaux'_def eux_init_agg_def eauxlist3_def)

lemma euxaux'_add_new:
  assumes v: "euxaux' kL cL kR cR args cur daux auxlist"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and t1: "table kL rel1" and t2: "table kR rel2"
    and f2: "finite rel2" and nt: "cur \<le> nt"
  shows "euxaux' kL cL kR cR args nt
      (eux_add_new (eargs cR cL args) (emsk cR cL) (etabc kL cL rel1) (etabc kR cR rel2) nt daux)
      (update_until args rel1 rel2 nt auxlist)"
proof (cases daux)
  case (EUX_gen d)
  have vd: "euaux' kL cL kR cR args cur (fix_res d) auxlist"
    using v unfolding EUX_gen by (simp add: euxaux'_def)
  have sh: "ushape d" and a1: "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
    using euaux'_ushape[OF vd] by simp_all
  have g: "fix_res (gadd_new_dq (eargs cR cL args) (emsk cR cL) (etabc kL cL rel1)
        (etabc kR cR rel2) nt d)
      = eadd_new_dq (eargs cR cL args) (emsk cR cL) (etabc kL cL rel1) (etabc kR cR rel2) nt
        (fix_res d)"
    by (rule gadd_new_dq_eq(1)[OF _ sh a1]) simp
  show ?thesis
    using euaux'_add_new[OF vd fR fL sub aL aR t1 t2 f2 nt] unfolding EUX_gen
    by (simp add: euxaux'_def g)
next
  case (EUX_win w)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_uw (eargs cR cL args) cur w (eauxlist3 kL cL kR cR auxlist)"
    using v unfolding EUX_win euxaux'_def by auto
  have L: "args_L (eargs cR cL args) = []" using c by simp
  have t1': "table [] (etabc kL cL rel1)" using table_etabc[of cL kL rel1] c by simp
  have tt: "table (args_R (eargs cR cL args)) (etabc kR cR rel2)" by (simp add: table_etabc)
  have ff: "finite (etabc kR cR rel2)" using f2 by (rule finite_etabc)
  have "valid_uw (eargs cR cL args) nt
      (uw_add_new (eargs cR cL args) (etabc kL cL rel1) (etabc kR cR rel2) nt w)
      (update_until (eargs cR cL args) (etabc kL cL rel1) (etabc kR cR rel2) nt
        (eauxlist3 kL cL kR cR auxlist))"
    by (rule valid_uw_add_new[OF vs L t1' refl tt ff _ nt]) (simp add: inz)
  moreover have "eauxlist3 kL cL kR cR (update_until args rel1 rel2 nt auxlist)
      = update_until (eargs cR cL args) (etabc kL cL rel1) (etabc kR cR rel2) nt
          (eauxlist3 kL cL kR cR auxlist)"
    by (rule eauxlist3_update_until[OF fR fL sub w t1 t2 aL aR]) simp_all
  ultimately show ?thesis using c inz eauxlist3_wf_update_until[OF w sub t1 t2 aL aR, of nt]
    unfolding EUX_win by (simp add: euxaux'_def)
next
  case (EUX_wagg p a)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_ua (eargs cR cL args) p cur a (eauxlist3 kL cL kR cR auxlist)"
    using v unfolding EUX_wagg euxaux'_def by auto
  have L: "args_L (eargs cR cL args) = []" using c by simp
  have t1': "table [] (etabc kL cL rel1)" using table_etabc[of cL kL rel1] c by simp
  have tt: "table (args_R (eargs cR cL args)) (etabc kR cR rel2)" by (simp add: table_etabc)
  have ff: "finite (etabc kR cR rel2)" using f2 by (rule finite_etabc)
  have "valid_ua (eargs cR cL args) p nt
      (ua_add_new (eargs cR cL args) p (args_n (eargs cR cL args))
        (etabc kL cL rel1) (etabc kR cR rel2) nt a)
      (update_until (eargs cR cL args) (etabc kL cL rel1) (etabc kR cR rel2) nt
        (eauxlist3 kL cL kR cR auxlist))"
    by (rule valid_ua_add_new[OF vs L t1' refl tt ff _ nt]) (simp add: inz)
  moreover have "eauxlist3 kL cL kR cR (update_until args rel1 rel2 nt auxlist)
      = update_until (eargs cR cL args) (etabc kL cL rel1) (etabc kR cR rel2) nt
          (eauxlist3 kL cL kR cR auxlist)"
    by (rule eauxlist3_update_until[OF fR fL sub w t1 t2 aL aR]) simp_all
  ultimately show ?thesis using c inz eauxlist3_wf_update_until[OF w sub t1 t2 aL aR, of nt]
    unfolding EUX_wagg by (simp add: euxaux'_def)
qed

lemma euxaux'_eval:
  assumes v: "euxaux' kL cL kR cR args cur daux auxlist" and nt: "cur \<le> nt"
    and de: "eux_eval (eargs cR cL args) nt daux = (dres, daux')"
    and we: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
  shows "dres = map (eux_post daux \<circ> etabc kR cR) res \<and>
    euxaux' kL cL kR cR args cur daux' auxlist'"
proof (cases daux)
  case (EUX_gen d)
  have vd: "euaux' kL cL kR cR args cur (fix_res d) auxlist"
    using v unfolding EUX_gen by (simp add: euxaux'_def)
  have sh: "ushape d" using euaux'_ushape(1)[OF vd] by simp
  have ag: "args_agg (eargs cR cL args) = None" by simp
  obtain dres0 d0 where e: "eval_dq (eargs cR cL args) nt (fix_res d) = (dres0, d0)"
    by (cases "eval_dq (eargs cR cL args) nt (fix_res d)")
  obtain d' where g: "geval_dq (eargs cR cL args) nt d = (dres, d')" and d': "daux' = EUX_gen d'"
    using de unfolding EUX_gen by (auto simp del: geval_dq.simps split: prod.splits)
  have r: "dres = dres0" and f: "fix_res d' = d0"
    using geval_dq_eq[OF ag sh, of nt] unfolding g e by simp_all
  show ?thesis unfolding r d' EUX_gen using euaux'_eval[OF vd nt e we] f by (simp add: euxaux'_def)
next
  case (EUX_win w)
  obtain dres0 w' where e: "uw_eval (eargs cR cL args) nt w = (dres0, w')"
    by (cases "uw_eval (eargs cR cL args) nt w")
  have r: "dres = dres0" and d': "daux' = EUX_win w'"
    using de unfolding EUX_win by (simp_all add: e)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_uw (eargs cR cL args) cur w (eauxlist3 kL cL kR cR auxlist)"
    using v unfolding EUX_win euxaux'_def by auto
  have we': "eval_until (args_ivl (eargs cR cL args)) nt (eauxlist3 kL cL kR cR auxlist)
      = (map (etabc kR cR) res, eauxlist3 kL cL kR cR auxlist')"
    using eauxlist3_eval_until[OF we] by simp
  have vw: "valid_uw (eargs cR cL args) cur w' (eauxlist3 kL cL kR cR auxlist')"
    and rr: "dres0 = map (etabc kR cR) res"
    using valid_uw_eval[OF vs nt e we'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis unfolding r d' EUX_win using vw rr c inz w by (auto simp: euxaux'_def)
next
  case (EUX_wagg p a)
  have ne: "args_n (eargs cR cL args) = length cR" by simp
  obtain dres0 a' where e: "ua_eval (eargs cR cL args) p (length cR) nt a = (dres0, a')"
    by (cases "ua_eval (eargs cR cL args) p (length cR) nt a")
  have r: "dres = dres0" and d': "daux' = EUX_wagg p a'"
    using de unfolding EUX_wagg by (simp_all add: e)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_ua (eargs cR cL args) p cur a (eauxlist3 kL cL kR cR auxlist)"
    using v unfolding EUX_wagg euxaux'_def by auto
  have we': "eval_until (args_ivl (eargs cR cL args)) nt (eauxlist3 kL cL kR cR auxlist)
      = (map (etabc kR cR) res, eauxlist3 kL cL kR cR auxlist')"
    using eauxlist3_eval_until[OF we] by simp
  have vw: "valid_ua (eargs cR cL args) p cur a' (eauxlist3 kL cL kR cR auxlist')"
    and rr: "dres0 = map (eagg_p p) (map (etabc kR cR) res)"
    using valid_ua_eval[OF vs nt e[folded ne] we'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis unfolding r d' EUX_wagg using vw rr c inz w
    by (auto simp: euxaux'_def)
qed

lemma usx_q_add_new_ts[simp]: "usx_q (udsx_add_new_ts args nt d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_join[simp]: "usx_q (udsx_join args X d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_add_new_table[simp]: "usx_q (udsx_add_new_table args X d) = usx_q d"
  by (cases d) simp_all

lemma esx_init_rdsx: "esx_init args msk = rdsx (udsx_init args msk)"
  by (simp add: esx_init_def udsx_init_def)

lemma esx_init_agg_rdsx[simp]: "rdsx (udsx_init_agg args p q) = esx_init_agg args p"
  by (simp add: esx_init_agg_def udsx_init_agg_def sa_init_rsc[symmetric])

lemma usx_q_init_agg[simp]: "usx_q (udsx_init_agg args p q) = q"
  by (simp add: udsx_init_agg_def)

lemma usx_q_init[simp]: "usx_q (udsx_init args msk) = None"
  by (simp add: udsx_init_def)

lemma esx_add_new_ts_rdsx: "esx_add_new_ts args nt (rdsx d) = rdsx (udsx_add_new_ts args nt d)"
  by (cases d) (simp_all add: sa_add_new_ts_rsc)

lemma esx_join_rdsx: "esx_join args X (rdsx d) = rdsx (udsx_join args X d)"
  by (cases d) (simp_all add: sa_join_rsc)

lemma esx_add_new_table_rdsx:
  "esx_add_new_table args X (rdsx d) = rdsx (udsx_add_new_table args X d)"
  by (cases d) (simp_all add: sa_add_new_table_rsc)

text \<open>The structure above reports the node's whole result; this one reports it read through the
  guard straight away.\<close>

lemma esx_result_rdsx:
  "usx_q d = q \<Longrightarrow> ufilt q (esx_result args (rdsx d)) = udsx_result args d"
  by (cases d) (auto simp: sa_result_rsc)

lemma eux_init_rdux: "eux_init args = rdux (udux_init args)"
  by (simp add: eux_init_def udux_init_def)

lemma eux_init_agg_rdux: "eux_init_agg args p = rdux (udux_init_agg args p)"
  by (simp add: eux_init_agg_def udux_init_agg_def rua_init)

lemma eux_add_new_rdux:
  "eux_add_new args msk rel1 rel2 nt (rdux d) = rdux (udux_add_new args msk rel1 rel2 nt d)"
  by (cases d) (simp_all add: ua_add_new_rua)

lemma eux_eval_rdux:
  "eux_eval args nt (rdux d) = (case udux_eval args nt d of (zs, d') \<Rightarrow> (zs, rdux d'))"
  by (cases d) (simp_all add: ua_eval_rua split: prod.splits)

lemma mbuf2S_add_rbufS: "mbuf2S_add xs ys ts (rbufS buf) = rbufS (mebuf2S_add xs ys ts buf)"
  by (cases buf) (simp add: mbuf_t_append.rep_eq)

lemma mbuf2_add_rbuf2: "mbuf2_add xs ys (rbuf2 buf) = rbuf2 (mebuf2_add xs ys buf)"
  by (rule mbuf2_add)

lemma mbuf2_take_rbuf2:
  "mbuf2_take f (rbuf2 buf) = (case mebuf2_take f buf of (zs, buf') \<Rightarrow> (zs, rbuf2 buf'))"
  by (cases "mebuf2_take f buf") (simp add: mebuf2_take)

lemma mbuf2t_take_rbuf2:
  "mbuf2t_take f z (rbuf2 buf) t (Rep_mbuf_t nts @ ts)
   = (case mebuf2t_take f z buf t (nts @@ ts) of
        (z', buf', t', nts') \<Rightarrow> (z', rbuf2 buf', t', Rep_mbuf_t nts'))"
  by (cases "mebuf2t_take f z buf t (nts @@ ts)")
    (simp add: mebuf2t_take[where ts = "nts @@ ts", unfolded mbuf_t_append.rep_eq])

lemma mbuf2T_take_rbuf2:
  "mbuf2T_take f z (rbuf2 buf) (Rep_mbuf_t nts @ ts)
   = (case mebuf2T_take f z buf (nts @@ ts) of
        (z', buf', nts') \<Rightarrow> (z', rbuf2 buf', Rep_mbuf_t nts'))"
  by (cases "mebuf2T_take f z buf (nts @@ ts)")
    (simp add: mebuf2T_take[where ts = "nts @@ ts", unfolded mbuf_t_append.rep_eq])

lemma mprev_next_prev:
  "mprev_next I (Rep_mbuf_t buf @ xs) (Rep_mbuf_t nts @ ts)
   = (case meprev_next I (buf @@ xs) (nts @@ ts) of
        (zs, xs', ts') \<Rightarrow> (zs, Rep_mbuf_t xs', Rep_mbuf_t ts'))"
  by (cases "meprev_next I (buf @@ xs) (nts @@ ts)")
    (simp add: meprev_next[where xs = "buf @@ xs" and ts = "nts @@ ts", unfolded mbuf_t_append.rep_eq]
      del: mprev_next.simps meprev_next.simps)

lemma mprev_next_next:
  "mprev_next I xs (Rep_mbuf_t nts @ ts)
   = (case meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts) of
        (zs, xs', ts') \<Rightarrow> (zs, Rep_mbuf_t xs', Rep_mbuf_t ts'))"
  using mprev_next_prev[of I mbuf_t_empty xs nts ts]
  by (simp add: mbuf_t_empty.rep_eq del: mprev_next.simps meprev_next.simps)

lemma mbufn_add_rbl: "mbufn_add xss (map Rep_mbuf_t buf) = map Rep_mbuf_t (mebufn_add xss buf)"
  by (rule mbufn_add)

lemma mbufn_take_ands:
  "mbufn_take (\<lambda>as zs. zs @ [gmulti_join ps ns as]) [] (map Rep_mbuf_t buf)
   = (case mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty buf of
        (zs, buf') \<Rightarrow> (Rep_mbuf_t zs, map Rep_mbuf_t buf'))"
proof -
  obtain zs buf' where e: "mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty buf
      = (zs, buf')" by (cases "mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty buf")
  have m: "mbufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty (map Rep_mbuf_t buf)
      = (zs, map Rep_mbuf_t buf')"
    by (rule mebufn_take[OF e])
  obtain zs'' buf'' where m': "mbufn_take (\<lambda>as zs. zs @ [gmulti_join ps ns as])
      (Rep_mbuf_t mbuf_t_empty) (map Rep_mbuf_t buf) = (zs'', buf'')"
    by (cases "mbufn_take (\<lambda>as zs. zs @ [gmulti_join ps ns as]) (Rep_mbuf_t mbuf_t_empty)
      (map Rep_mbuf_t buf)")
  have "zs'' = Rep_mbuf_t zs \<and> buf'' = map Rep_mbuf_t buf'"
    using mbufn_take_app[OF m m'] .
  then show ?thesis using m' e
    by (simp add: mbuf_t_empty.rep_eq del: mbufn_take.simps)
qed

lemma mbufnt_take_rbl:
  "mbufnt_take f z (map Rep_mbuf_t buf) t0 (Rep_mbuf_t nts @ ts)
   = (case mebufnt_take f z buf t0 (nts @@ ts) of
        (z', buf', t', ts') \<Rightarrow> (z', map Rep_mbuf_t buf', t', Rep_mbuf_t ts'))"
  by (cases "mebufnt_take f z buf t0 (nts @@ ts)")
    (simp add: mebufnt_take[where nts = "nts @@ ts", unfolded mbuf_t_append.rep_eq]
      del: mbufnt_take.simps mebufnt_take.simps)

lemma mbufnt_take_matchP:
  "mbufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @ [z], ax)))
     ([], a0) (map Rep_mbuf_t buf) t0 (Rep_mbuf_t nts @ ts)
   = (case mebufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax)))
       (mbuf_t_empty, a0) buf t0 (nts @@ ts) of
        ((zs', a'), buf', t', ts') \<Rightarrow> ((Rep_mbuf_t zs', a'), map Rep_mbuf_t buf', t', Rep_mbuf_t ts'))"
proof -
  let ?F = "\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax))"
  let ?G = "\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @ [z], ax))"
  obtain zs' a' buf' t' ts' where e: "mebufnt_take ?F (mbuf_t_empty, a0) buf t0 (nts @@ ts)
      = ((zs', a'), buf', t', ts')"
    by (metis prod_cases4 surj_pair)
  have m: "mbufnt_take ?F (mbuf_t_empty, a0) (map Rep_mbuf_t buf) t0 (Rep_mbuf_t nts @ ts)
      = ((zs', a'), map Rep_mbuf_t buf', t', Rep_mbuf_t ts')"
    using mbufnt_take_rbl[of ?F "(mbuf_t_empty, a0)" buf t0 nts ts] e by simp
  obtain zs'' a'' buf'' t'' ts'' where m': "mbufnt_take ?G (Rep_mbuf_t mbuf_t_empty, a0)
      (map Rep_mbuf_t buf) t0 (Rep_mbuf_t nts @ ts) = ((zs'', a''), buf'', t'', ts'')"
    by (metis prod_cases4 surj_pair)
  have "zs'' = Rep_mbuf_t zs' \<and> a'' = a' \<and> buf'' = map Rep_mbuf_t buf' \<and> t'' = t' \<and>
      ts'' = Rep_mbuf_t ts'"
    by (rule mbufnt_take_app[OF m m'])
  then show ?thesis using m' e by (simp add: mbuf_t_empty.rep_eq del: mbufnt_take.simps)
qed

lemma usx_q_uedsx_eval_since:
  "usx_q (snd (snd (uedsx_eval_since args rs buf aux))) = usx_q aux"
proof (induct args rs buf aux rule: uedsx_eval_since.induct)
  case (1 args rs xs ys ts skew aux)
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  show ?case
    using 1 x y t
    by (cases y; cases x; cases t; subst uedsx_eval_since.simps)
      (auto simp: x y t Let_def simp del: uedsx_eval_since.simps split: prod.splits)
qed

lemma usx_q_uedsx_eval_since':
  "uedsx_eval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow> usx_q aux' = usx_q aux"
  using usx_q_uedsx_eval_since[of args rs buf aux] by simp

text \<open>The traversal commutes with the representations: the traversal of
  @{const esx_eval_since} on the images reports the same results, read through the node's guard.
  The accumulator is carried the same way, so the statement relates the two lists it is started
  with.\<close>

lemma esx_eval_since_rdsx:
  "map (ufilt (usx_q aux)) Rs = rs \<Longrightarrow>
   (case esx_eval_since args Rs (rbufS buf) (rdsx aux) of
      (Zs, bf, a) \<Rightarrow> (map (ufilt (usx_q aux)) Zs, bf, a))
   = (case uedsx_eval_since args rs buf aux of
        (zs, buf', aux') \<Rightarrow> (zs, rbufS buf', rdsx aux'))"
proof (induct args rs buf aux arbitrary: Rs rule: uedsx_eval_since.induct)
  case (1 args rs xs ys ts skew aux)
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  show ?case
    using 1 x y t
    by (cases y; cases x; cases t; simp only: rbufS.simps; subst uedsx_eval_since.simps)
      (auto simp: x y t Let_def rev_map[symmetric] esx_join_rdsx esx_add_new_ts_rdsx
        esx_add_new_table_rdsx esx_result_rdsx mbuf_t_Cons.rep_eq mbuf_t_empty.rep_eq
        Rep_mbuf_t_cases(1,2)[where xs = ts and xs' = ts'] Rep_mbuf_t_cases(1,2)[where xs = xs and xs' = xs']
        Rep_mbuf_t_cases(1,2)[where xs = ys and xs' = ys']
        simp del: uedsx_eval_since.simps split: prod.splits)
qed

lemma esx_eval_since_rdsx0:
  "(case esx_eval_since args [] (rbufS buf) (rdsx aux) of
      (Zs, bf, a) \<Rightarrow> (map (ufilt (usx_q aux)) Zs, bf, a))
   = (case uedsx_eval_since args [] buf aux of
        (zs, buf', aux') \<Rightarrow> (zs, rbufS buf', rdsx aux'))"
  using esx_eval_since_rdsx[where rs = "[]" and Rs = "[]"] by simp

subsection \<open>The Until buffer's traversal, and the two buffers of the fused And-Trigger\<close>

lemma mebuf2t_take_nat:
  assumes "\<And>x y t z. f x y t (h z) = h (g x y t z)"
  shows "mebuf2t_take f (h z) buf t ts
    = (case mebuf2t_take g z buf t ts of (z', b) \<Rightarrow> (h z', b))"
  using assms
proof (induct g z buf t ts rule: mebuf2t_take.induct)
  case (1 g z xs ys t0 ts)
  obtain ot ts' where t: "mbuf_t_cases ts = (ot, ts')" by fastforce
  obtain ox xs' where x: "mbuf_t_cases xs = (ox, xs')" by fastforce
  obtain oy ys' where y: "mbuf_t_cases ys = (oy, ys')" by fastforce
  show ?case
  proof (cases "ot = None \<or> ox = None \<or> oy = None")
    case True
    then show ?thesis
      using t x y by (subst (1 2) mebuf2t_take.simps) (auto simp del: mebuf2t_take.simps split: option.splits)
  next
    case False
    then obtain t1 x1 y1 where s: "ot = Some t1" "ox = Some x1" "oy = Some y1"
      by auto
    have IH: "mebuf2t_take f (h (g x1 y1 t1 z)) (xs', ys') t1 ts' =
        (case mebuf2t_take g (g x1 y1 t1 z) (xs', ys') t1 ts' of (z', b) \<Rightarrow> (h z', b))"
      by (rule 1(1)[OF t[symmetric] s(1) x[symmetric] s(2) y[symmetric] s(3) 1(2)])
    show ?thesis
      by (subst (1 2) mebuf2t_take.simps) (simp only: t x y s prod.case option.case 1(2) IH)
  qed
qed

lemma mbuf2t_take_until:
  "mbuf2t_take (eux_add_new dags msk) (rdux aux) (rbuf2 buf) t (Rep_mbuf_t nts @ ts)
   = (case mebuf2t_take (udux_add_new dags msk) aux buf t (nts @@ ts) of
        (aux', buf', t', nts') \<Rightarrow> (rdux aux', rbuf2 buf', t', Rep_mbuf_t nts'))"
  using mbuf2t_take_rbuf2[of "eux_add_new dags msk" "rdux aux" buf t nts ts]
    mebuf2t_take_nat[of "eux_add_new dags msk" rdux "udux_add_new dags msk" aux buf t "nts @@ ts"]
  by (simp add: eux_add_new_rdux split: prod.splits)

lemma mbuf2_add_rbufo: "mbuf2_add xs ys (rbufo buf) = rbufo (mebuf2_add xs ys buf)"
  by (rule mbuf2_add)

lemma mbuf2_take_rbufo:
  "mbuf2_take f (rbufo buf) = (case mebuf2_take f buf of (zs, buf') \<Rightarrow> (zs, rbufo buf'))"
  by (cases "mebuf2_take f buf") (simp add: mebuf2_take)

(*<*)
end
(*>*)
