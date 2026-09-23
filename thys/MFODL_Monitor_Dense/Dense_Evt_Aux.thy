(*<*)
theory Dense_Evt_Aux
  imports Dense_Until_Gen Dense_Evt_UAgg
begin
(*>*)

section \<open>Choosing the structure at the dense frame\<close>

text \<open>
  The dense Since and Until nodes carry one of two structures: the general one of
  @{theory MFODL_Monitor_Dense.Dense_Aux}, or the sliding window of
  @{theory MFODL_Monitor_Dense.Dense_Evt} where the left operand is closed (and, for the Until,
  the interval contains zero).  The choice is made once, when the node is built, from the
  arguments alone; the operations dispatch on it, and the relation to the kernel's abstract
  auxiliary list is the disjunction of the two structures' relations.  The five Since lemmas and
  the four Until lemmas that the simulation uses are restated for the sum, so that nothing
  downstream needs to know which structure runs.
\<close>

subsection \<open>The Since structure\<close>

datatype dsaux_x = DSX_gen "event_data dmsaux" | DSX_win swaux | DSX_wagg daggp swagg

text \<open>The window is chosen from the arguments alone; the window with the aggregate is chosen by
  the compiler, which knows the aggregation the kernel fused into the node.\<close>

definition dsx_init :: "args \<Rightarrow> bool list \<Rightarrow> dsaux_x" where
  "dsx_init args msk = (if args_L args = {} then DSX_win (sw_init args)
     else DSX_gen (dinit_msaux args msk))"

definition dsx_init_agg :: "args \<Rightarrow> daggp \<Rightarrow> dsaux_x" where
  "dsx_init_agg args p = DSX_wagg p (sa_init args p)"

fun dsx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> dsaux_x \<Rightarrow> dsaux_x" where
  "dsx_add_new_ts args nt (DSX_gen d) = DSX_gen (dadd_new_ts_msaux args nt d)"
| "dsx_add_new_ts args nt (DSX_win w) = DSX_win (sw_add_new_ts args nt w)"
| "dsx_add_new_ts args nt (DSX_wagg p a) = DSX_wagg p (sa_add_new_ts args p nt a)"

fun dsx_join :: "args \<Rightarrow> event_data table \<Rightarrow> dsaux_x \<Rightarrow> dsaux_x" where
  "dsx_join args X (DSX_gen d) = DSX_gen (dgc_join_lz args X d)"
| "dsx_join args X (DSX_win w) = DSX_win (sw_join args X w)"
| "dsx_join args X (DSX_wagg p a) = DSX_wagg p (sa_join args p X a)"

fun dsx_add_new_table :: "args \<Rightarrow> event_data table \<Rightarrow> dsaux_x \<Rightarrow> dsaux_x" where
  "dsx_add_new_table args X (DSX_gen d) = DSX_gen (dadd_new_table_lz args X d)"
| "dsx_add_new_table args X (DSX_win w) = DSX_win (sw_add_new_table args X w)"
| "dsx_add_new_table args X (DSX_wagg p a) = DSX_wagg p (sa_add_new_table args p X a)"

fun dsx_result :: "args \<Rightarrow> dsaux_x \<Rightarrow> event_data table" where
  "dsx_result args (DSX_gen d) = dresult_msaux args d"
| "dsx_result args (DSX_win w) = sw_result args w"
| "dsx_result args (DSX_wagg p a) = sa_result args p a"

text \<open>What a structure reports, relative to the window's union: the union itself, or its
  aggregate.  The choice is fixed with the structure and no operation changes it.\<close>

fun dsx_post :: "dsaux_x \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dsx_post (DSX_gen d) = id"
| "dsx_post (DSX_win w) = id"
| "dsx_post (DSX_wagg p a) = dagg_p p"

lemma dsx_post_add_new_ts[simp]: "dsx_post (dsx_add_new_ts args nt d) = dsx_post d"
  by (cases d) simp_all

lemma dsx_post_join[simp]: "dsx_post (dsx_join args X d) = dsx_post d"
  by (cases d) simp_all

lemma dsx_post_add_new_table[simp]: "dsx_post (dsx_add_new_table args X d) = dsx_post d"
  by (cases d) simp_all

lemma dsx_post_init[simp]: "dsx_post (dsx_init args msk) = id"
  by (simp add: dsx_init_def)

lemma dsx_post_init_agg[simp]: "dsx_post (dsx_init_agg args p) = dagg_p p"
  by (simp add: dsx_init_agg_def)

text \<open>Which aggregate, if any, a structure reports; the compiler and the simulation tell the
  structures apart by it.\<close>

fun dsx_agg :: "dsaux_x \<Rightarrow> daggp option" where
  "dsx_agg (DSX_gen d) = None"
| "dsx_agg (DSX_win w) = None"
| "dsx_agg (DSX_wagg p a) = Some p"

lemma dsx_post_eq: "dsx_post d = (case dsx_agg d of None \<Rightarrow> id | Some p \<Rightarrow> dagg_p p)"
  by (cases d) simp_all

lemma dsx_agg_add_new_ts[simp]: "dsx_agg (dsx_add_new_ts args nt d) = dsx_agg d"
  by (cases d) simp_all

lemma dsx_agg_join[simp]: "dsx_agg (dsx_join args X d) = dsx_agg d"
  by (cases d) simp_all

lemma dsx_agg_add_new_table[simp]: "dsx_agg (dsx_add_new_table args X d) = dsx_agg d"
  by (cases d) simp_all

lemma dsx_agg_init[simp]: "dsx_agg (dsx_init args msk) = None"
  by (simp add: dsx_init_def)

lemma dsx_agg_init_agg[simp]: "dsx_agg (dsx_init_agg args p) = Some p"
  by (simp add: dsx_init_agg_def)

definition dsxaux' :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> dsaux_x \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "dsxaux' n cs_R cs_L args cur daux auxlist \<longleftrightarrow> (case daux of
     DSX_gen d \<Rightarrow> dsaux' n cs_R cs_L args cur d auxlist
   | DSX_win w \<Rightarrow> cpos cs_R (set cs_L) = {} \<and>
       (\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel) \<and>
       valid_sw (dargs cs_R cs_L args) cur w (dauxlist n cs_R auxlist)
   | DSX_wagg p a \<Rightarrow> cpos cs_R (set cs_L) = {} \<and>
       (\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel) \<and>
       valid_sa (dargs cs_R cs_L args) p cur a (dauxlist n cs_R auxlist))"

lemma dsxaux'_tables:
  "dsxaux' n cs_R cs_L args cur daux auxlist \<Longrightarrow> \<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
  by (cases daux) (auto simp: dsxaux'_def dsaux'_def)

lemma dsxaux'_init:
  assumes sub: "set cs_L \<subseteq> set cs_R"
  shows "dsxaux' n cs_R cs_L args 0 (dsx_init (dargs cs_R cs_L args) (dmsk cs_R cs_L)) []"
  using dsaux'_init[OF sub, of n args] valid_sw_init
  by (auto simp: dsxaux'_def dsx_init_def dauxlist_def)

lemma dsxaux'_init_agg:
  assumes c: "cpos cs_R (set cs_L) = {}" and ok: "dagg_ok p (length cs_R)"
  shows "dsxaux' n cs_R cs_L args 0 (dsx_init_agg (dargs cs_R cs_L args) p) []"
  using valid_sa_init[of "dargs cs_R cs_L args" p] c ok
  by (auto simp: dsxaux'_def dsx_init_agg_def dauxlist_def)

lemma dsxaux'_add_new_ts:
  assumes v: "dsxaux' n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
  shows "dsxaux' n cs_R cs_L args nt (dsx_add_new_ts (dargs cs_R cs_L args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof (cases daux)
  case (DSX_gen d)
  then show ?thesis using dsaux'_add_new_ts[OF _ nt, of n cs_R cs_L args d auxlist] v
    by (simp add: dsxaux'_def)
next
  case (DSX_win w)
  have c: "cpos cs_R (set cs_L) = {}" and w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sw (dargs cs_R cs_L args) cur w (dauxlist n cs_R auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have "valid_sw (dargs cs_R cs_L args) nt (sw_add_new_ts (dargs cs_R cs_L args) nt w)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cs_R cs_L args)) (nt - t)) (dauxlist n cs_R auxlist))"
    by (rule valid_sw_add_new_ts[OF vs nt])
  then show ?thesis using c w unfolding DSX_win by (simp add: dsxaux'_def dauxlist_filter)
next
  case (DSX_wagg p a)
  have c: "cpos cs_R (set cs_L) = {}" and w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sa (dargs cs_R cs_L args) p cur a (dauxlist n cs_R auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have "valid_sa (dargs cs_R cs_L args) p nt (sa_add_new_ts (dargs cs_R cs_L args) p nt a)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cs_R cs_L args)) (nt - t)) (dauxlist n cs_R auxlist))"
    by (rule valid_sa_add_new_ts[OF vs nt])
  then show ?thesis using c w unfolding DSX_wagg by (simp add: dsxaux'_def dauxlist_filter)
qed

lemma dsxaux'_join:
  assumes v: "dsxaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b_R: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R" and t1: "table n (set cs_L) rel1"
  shows "dsxaux' n cs_R cs_L args cur
      (dsx_join (dargs cs_R cs_L args) (dtabc n cs_L rel1) daux)
      (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
proof (cases daux)
  case (DSX_gen d)
  have vd: "dsaux' n cs_R cs_L args cur d auxlist" using v unfolding DSX_gen by (simp add: dsxaux'_def)
  show ?thesis unfolding DSX_gen by (simp add: dsxaux'_def dsaux'_join[OF vd s_R s_L b_R sub t1])
next
  case (DSX_win w)
  have c: "cpos cs_R (set cs_L) = {}" and w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sw (dargs cs_R cs_L args) cur w (dauxlist n cs_R auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have t1': "table (args_n (dargs cs_R cs_L args)) {} (dtabc n cs_R rel1)"
    using table_dtabc_cpos[OF s_R b_R sub t1] c by simp
  have X: "(dtabc n cs_L rel1 = {}) = (dtabc n cs_R rel1 = {})"
    by (simp add: dtabc_empty_iff)
  have "valid_sw (dargs cs_R cs_L args) cur (sw_join (dargs cs_R cs_L args) (dtabc n cs_L rel1) w)
      (map (\<lambda>(t, rel). (t, join rel (args_pos (dargs cs_R cs_L args)) (dtabc n cs_R rel1)))
        (dauxlist n cs_R auxlist))"
    by (rule valid_sw_join[OF vs t1' X])
  then show ?thesis using c dauxlist_wf_join[OF w sub t1, of "args_pos args"] unfolding DSX_win
    by (simp add: dsxaux'_def dauxlist_join[OF s_R b_R sub w t1])
next
  case (DSX_wagg p a)
  have c: "cpos cs_R (set cs_L) = {}" and w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sa (dargs cs_R cs_L args) p cur a (dauxlist n cs_R auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have t1': "table (args_n (dargs cs_R cs_L args)) {} (dtabc n cs_R rel1)"
    using table_dtabc_cpos[OF s_R b_R sub t1] c by simp
  have X: "(dtabc n cs_L rel1 = {}) = (dtabc n cs_R rel1 = {})"
    by (simp add: dtabc_empty_iff)
  have "valid_sa (dargs cs_R cs_L args) p cur (sa_join (dargs cs_R cs_L args) p (dtabc n cs_L rel1) a)
      (map (\<lambda>(t, rel). (t, join rel (args_pos (dargs cs_R cs_L args)) (dtabc n cs_R rel1)))
        (dauxlist n cs_R auxlist))"
    by (rule valid_sa_join[OF vs t1' X])
  then show ?thesis using c dauxlist_wf_join[OF w sub t1, of "args_pos args"] unfolding DSX_wagg
    by (simp add: dsxaux'_def dauxlist_join[OF s_R b_R sub w t1])
qed

lemma dsxaux'_add_new_table:
  assumes v: "dsxaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and b_R: "\<forall>c \<in> set cs_R. c < n"
    and t2: "table n (set cs_R) rel2" and f2: "finite rel2"
  shows "dsxaux' n cs_R cs_L args cur
      (dsx_add_new_table (dargs cs_R cs_L args) (dtabc n cs_R rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof (cases daux)
  case (DSX_gen d)
  have vd: "dsaux' n cs_R cs_L args cur d auxlist" using v unfolding DSX_gen by (simp add: dsxaux'_def)
  show ?thesis unfolding DSX_gen by (simp add: dsxaux'_def dsaux'_add_new_table[OF vd s_R b_R t2])
next
  case (DSX_win w)
  have c: "cpos cs_R (set cs_L) = {}" and w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sw (dargs cs_R cs_L args) cur w (dauxlist n cs_R auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have ff: "finite (dtabc n cs_R rel2)" using f2 by (simp add: dtabc_def)
  have "valid_sw (dargs cs_R cs_L args) cur
      (sw_add_new_table (dargs cs_R cs_L args) (dtabc n cs_R rel2) w)
      (case dauxlist n cs_R auxlist of [] \<Rightarrow> [(cur, dtabc n cs_R rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc n cs_R rel2) # r
                         else (cur, dtabc n cs_R rel2) # dauxlist n cs_R auxlist)"
    by (rule valid_sw_add_new_table[OF vs tt ff])
  then show ?thesis using c dauxlist_wf_add_new_table[OF w t2, of cur] unfolding DSX_win
    by (simp add: dsxaux'_def dauxlist_add_new_table[symmetric])
next
  case (DSX_wagg p a)
  have c: "cpos cs_R (set cs_L) = {}" and w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sa (dargs cs_R cs_L args) p cur a (dauxlist n cs_R auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have ff: "finite (dtabc n cs_R rel2)" using f2 by (simp add: dtabc_def)
  have "valid_sa (dargs cs_R cs_L args) p cur
      (sa_add_new_table (dargs cs_R cs_L args) p (dtabc n cs_R rel2) a)
      (case dauxlist n cs_R auxlist of [] \<Rightarrow> [(cur, dtabc n cs_R rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc n cs_R rel2) # r
                         else (cur, dtabc n cs_R rel2) # dauxlist n cs_R auxlist)"
    by (rule valid_sa_add_new_table[OF vs tt ff])
  then show ?thesis using c dauxlist_wf_add_new_table[OF w t2, of cur] unfolding DSX_wagg
    by (simp add: dsxaux'_def dauxlist_add_new_table[symmetric])
qed

lemma dsxaux'_result:
  assumes v: "dsxaux' n cs_R cs_L args cur daux auxlist"
  shows "dsx_result (dargs cs_R cs_L args) daux
      = dsx_post daux (dtabc n cs_R (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist,
          memL (args_ivl args) (cur - t)] {}))"
proof (cases daux)
  case (DSX_gen d)
  then show ?thesis using dsaux'_result[of n cs_R cs_L args cur d auxlist] v
    by (simp add: dsxaux'_def)
next
  case (DSX_win w)
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sw (dargs cs_R cs_L args) cur w (dauxlist n cs_R auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have "sw_result (dargs cs_R cs_L args) w
      = foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist n cs_R auxlist,
          memL (args_ivl (dargs cs_R cs_L args)) (cur - t)] {}"
    by (rule valid_sw_result[OF vs])
  then show ?thesis unfolding DSX_win by (simp add: dtabc_result[OF w])
next
  case (DSX_wagg p a)
  have w: "\<forall>(t, rel) \<in> set auxlist. table n (set cs_R) rel"
    and vs: "valid_sa (dargs cs_R cs_L args) p cur a (dauxlist n cs_R auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have "sa_result (dargs cs_R cs_L args) p a
      = dagg_p p (foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist n cs_R auxlist,
          memL (args_ivl (dargs cs_R cs_L args)) (cur - t)] {})"
    by (rule valid_sa_result[OF vs])
  then show ?thesis unfolding DSX_wagg by (simp add: dtabc_result[OF w])
qed

text \<open>The kernel's @{text eval_since} with the dispatching operations put in.\<close>

fun dsx_eval_since :: "args \<Rightarrow> event_data table list \<Rightarrow> event_data mbuf2S \<Rightarrow> dsaux_x \<Rightarrow>
    event_data table list \<times> event_data mbuf2S \<times> dsaux_x" where
  "dsx_eval_since args rs (x # xs, [], t # ts, skew) daux =
    (if skew \<or> memL (args_ivl args) 0
     then (rev rs, (x # xs, [], t # ts, skew), daux)
     else (let daux' = dsx_join args x (dsx_add_new_ts args t daux)
       in (rev (dsx_result args daux' # rs), (xs, [], ts, True), daux')))"
| "dsx_eval_since args rs (xs, y # ys, ts, True) daux =
    dsx_eval_since args rs (xs, ys, ts, False) (dsx_add_new_table args y daux)"
| "dsx_eval_since args rs (x # xs, y # ys, t # ts, False) daux =
    (let daux' = dsx_add_new_table args y
       (dsx_join args x (dsx_add_new_ts args t daux))
     in dsx_eval_since args (dsx_result args daux' # rs) (xs, ys, ts, False) daux')"
| "dsx_eval_since args rs buf daux = (rev rs, buf, daux)"

lemma dsx_agg_eval_since:
  "dsx_eval_since args rs buf daux = (dzs, buf', daux') \<Longrightarrow> dsx_agg daux' = dsx_agg daux"
  by (induct args rs buf daux arbitrary: dzs buf' daux' rule: dsx_eval_since.induct)
    (auto simp: Let_def split: if_splits)

subsection \<open>The Until structure\<close>

datatype duaux_x = DUX_gen "event_data mmuaux_dq" | DUX_win uwaux | DUX_wagg daggp uwagg

definition dux_init :: "args \<Rightarrow> duaux_x" where
  "dux_init args = (if args_L args = {} \<and> memL (args_ivl args) 0 then DUX_win (uw_init args)
     else DUX_gen (ginit_dq args))"

fun dux_add_new :: "args \<Rightarrow> bool list \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
    duaux_x \<Rightarrow> duaux_x" where
  "dux_add_new args msk rel1 rel2 nt (DUX_gen d) = DUX_gen (gadd_new_dq args msk rel1 rel2 nt d)"
| "dux_add_new args msk rel1 rel2 nt (DUX_win w) = DUX_win (uw_add_new args rel1 rel2 nt w)"
| "dux_add_new args msk rel1 rel2 nt (DUX_wagg p a) =
     DUX_wagg p (ua_add_new args p (args_n args) rel1 rel2 nt a)"

fun dux_eval :: "args \<Rightarrow> ts \<Rightarrow> duaux_x \<Rightarrow> event_data table list \<times> duaux_x" where
  "dux_eval args nt (DUX_gen d) = (let (zs, d') = geval_dq args nt d in (zs, DUX_gen d'))"
| "dux_eval args nt (DUX_win w) = (let (zs, w') = uw_eval args nt w in (zs, DUX_win w'))"
| "dux_eval args nt (DUX_wagg p a) =
     (let (zs, a') = ua_eval args p (args_n args) nt a in (zs, DUX_wagg p a'))"

fun dux_length :: "args \<Rightarrow> duaux_x \<Rightarrow> nat" where
  "dux_length args (DUX_gen d) = glength_dq args d"
| "dux_length args (DUX_win w) = uw_length args w"
| "dux_length args (DUX_wagg p a) = ua_length args a"

definition dux_init_agg :: "args \<Rightarrow> daggp \<Rightarrow> duaux_x" where
  "dux_init_agg args p = DUX_wagg p (ua_init args p)"

text \<open>What a structure reports for each finished time point, relative to the window's union at
  it: the union itself, or its aggregate.  As on the Since side the choice is fixed with the
  structure and no operation changes it.\<close>

fun dux_post :: "duaux_x \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dux_post (DUX_gen d) = id"
| "dux_post (DUX_win w) = id"
| "dux_post (DUX_wagg p a) = dagg_p p"

fun dux_agg :: "duaux_x \<Rightarrow> daggp option" where
  "dux_agg (DUX_gen d) = None"
| "dux_agg (DUX_win w) = None"
| "dux_agg (DUX_wagg p a) = Some p"

lemma dux_post_eq: "dux_post d = (case dux_agg d of None \<Rightarrow> id | Some p \<Rightarrow> dagg_p p)"
  by (cases d) simp_all

lemma dux_post_add_new[simp]: "dux_post (dux_add_new args msk rel1 rel2 nt d) = dux_post d"
  by (cases d) simp_all

lemma dux_agg_add_new[simp]: "dux_agg (dux_add_new args msk rel1 rel2 nt d) = dux_agg d"
  by (cases d) simp_all

lemma dux_post_init[simp]: "dux_post (dux_init args) = id"
  by (simp add: dux_init_def)

lemma dux_agg_init[simp]: "dux_agg (dux_init args) = None"
  by (simp add: dux_init_def)

lemma dux_post_init_agg[simp]: "dux_post (dux_init_agg args p) = dagg_p p"
  by (simp add: dux_init_agg_def)

lemma dux_agg_init_agg[simp]: "dux_agg (dux_init_agg args p) = Some p"
  by (simp add: dux_init_agg_def)

lemma dux_post_eval[simp]: "dux_post (snd (dux_eval args nt d)) = dux_post d"
  by (cases d) (simp_all split: prod.splits)

lemma dux_agg_eval[simp]: "dux_agg (snd (dux_eval args nt d)) = dux_agg d"
  by (cases d) (simp_all split: prod.splits)

definition duxaux' :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> duaux_x \<Rightarrow>
    event_data muaux \<Rightarrow> bool" where
  "duxaux' n cs_R cs_L args cur daux auxlist \<longleftrightarrow> (case daux of
     DUX_gen d \<Rightarrow> duaux' n cs_R cs_L args cur (fix_res d) auxlist
   | DUX_win w \<Rightarrow> cpos cs_R (set cs_L) = {} \<and> memL (args_ivl args) 0 \<and>
       (\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2) \<and>
       valid_uw (dargs cs_R cs_L args) cur w (dauxlist3 n cs_R auxlist)
   | DUX_wagg p a \<Rightarrow> cpos cs_R (set cs_L) = {} \<and> memL (args_ivl args) 0 \<and>
       (\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2) \<and>
       valid_ua (dargs cs_R cs_L args) p cur a (dauxlist3 n cs_R auxlist))"

lemma duxaux'_tables:
  "duxaux' n cs_R cs_L args cur daux auxlist \<Longrightarrow>
     \<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
  by (cases daux) (auto simp: duxaux'_def duaux'_def)

lemma duxaux'_init:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and sub: "set cs_L \<subseteq> set cs_R"
  shows "duxaux' n cs_R cs_L args 0 (dux_init (dargs cs_R cs_L args)) []"
  using duaux'_init[OF s_R s_L sub, of n args, folded ginit_dq_eq] valid_uw_init
  by (auto simp: duxaux'_def dux_init_def dauxlist3_def)

lemma duxaux'_init_agg:
  assumes c: "cpos cs_R (set cs_L) = {}" and inz: "memL (args_ivl args) 0"
    and ok: "dagg_ok p (length cs_R)"
  shows "duxaux' n cs_R cs_L args 0 (dux_init_agg (dargs cs_R cs_L args) p) []"
  using valid_ua_init[of "dargs cs_R cs_L args" p] c inz ok
  by (auto simp: duxaux'_def dux_init_agg_def dauxlist3_def)

lemma duxaux'_add_new:
  assumes v: "duxaux' n cs_R cs_L args cur daux auxlist"
    and s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b_R: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and t1: "table n (set cs_L) rel1" and t2: "table n (set cs_R) rel2"
    and f2: "finite rel2" and nt: "cur \<le> nt"
  shows "duxaux' n cs_R cs_L args nt
      (dux_add_new (dargs cs_R cs_L args) (dmsk cs_R cs_L)
        (dtabc n cs_L rel1) (dtabc n cs_R rel2) nt daux)
      (update_until args rel1 rel2 nt auxlist)"
proof (cases daux)
  case (DUX_gen d)
  have vd: "duaux' n cs_R cs_L args cur (fix_res d) auxlist"
    using v unfolding DUX_gen by (simp add: duxaux'_def)
  have sh: "ushape d" and a1: "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
    using duaux'_ushape[OF vd] by simp_all
  have g: "fix_res (gadd_new_dq (dargs cs_R cs_L args) (dmsk cs_R cs_L) (dtabc n cs_L rel1)
        (dtabc n cs_R rel2) nt d)
      = dadd_new_dq (dargs cs_R cs_L args) (dmsk cs_R cs_L) (dtabc n cs_L rel1) (dtabc n cs_R rel2) nt
        (fix_res d)"
    by (rule gadd_new_dq_eq(1)[OF _ sh a1]) (simp add: dargs_def init_args_def)
  show ?thesis
    using duaux'_add_new[OF vd s_R s_L b_R sub t1 t2 f2 nt] unfolding DUX_gen
    by (simp add: duxaux'_def g)
next
  case (DUX_win w)
  have c: "cpos cs_R (set cs_L) = {}" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and vs: "valid_uw (dargs cs_R cs_L args) cur w (dauxlist3 n cs_R auxlist)"
    using v unfolding DUX_win duxaux'_def by auto
  have t1': "table (args_n (dargs cs_R cs_L args)) {} (dtabc n cs_R rel1)"
    using table_dtabc_cpos[OF s_R b_R sub t1] c by simp
  have X: "(dtabc n cs_L rel1 = {}) = (dtabc n cs_R rel1 = {})"
    by (simp add: dtabc_empty_iff)
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have ff: "finite (dtabc n cs_R rel2)" using f2 by (simp add: dtabc_def)
  have "valid_uw (dargs cs_R cs_L args) nt
      (uw_add_new (dargs cs_R cs_L args) (dtabc n cs_L rel1) (dtabc n cs_R rel2) nt w)
      (update_until (dargs cs_R cs_L args) (dtabc n cs_R rel1) (dtabc n cs_R rel2) nt
        (dauxlist3 n cs_R auxlist))"
    by (rule valid_uw_add_new[OF vs t1' X tt ff _ nt]) (simp add: inz)
  then show ?thesis using c inz dauxlist3_wf_update_until[OF w sub t1 t2, of args nt]
    unfolding DUX_win
    by (simp add: duxaux'_def dauxlist3_update_until[OF s_R b_R sub w t1 t2, symmetric])
next
  case (DUX_wagg p a)
  have c: "cpos cs_R (set cs_L) = {}" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and vs: "valid_ua (dargs cs_R cs_L args) p cur a (dauxlist3 n cs_R auxlist)"
    using v unfolding DUX_wagg duxaux'_def by auto
  have t1': "table (args_n (dargs cs_R cs_L args)) {} (dtabc n cs_R rel1)"
    using table_dtabc_cpos[OF s_R b_R sub t1] c by simp
  have X: "(dtabc n cs_L rel1 = {}) = (dtabc n cs_R rel1 = {})"
    by (simp add: dtabc_empty_iff)
  have tt: "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R rel2)"
    using table_dtabc_cpos[OF s_R b_R subset_refl t2] by (simp add: cpos_all)
  have ff: "finite (dtabc n cs_R rel2)" using f2 by (simp add: dtabc_def)
  have "valid_ua (dargs cs_R cs_L args) p nt
      (ua_add_new (dargs cs_R cs_L args) p (args_n (dargs cs_R cs_L args))
        (dtabc n cs_L rel1) (dtabc n cs_R rel2) nt a)
      (update_until (dargs cs_R cs_L args) (dtabc n cs_R rel1) (dtabc n cs_R rel2) nt
        (dauxlist3 n cs_R auxlist))"
    by (rule valid_ua_add_new[OF vs t1' X tt ff _ nt]) (simp add: inz)
  then show ?thesis using c inz dauxlist3_wf_update_until[OF w sub t1 t2, of args nt]
    unfolding DUX_wagg
    by (simp add: duxaux'_def dauxlist3_update_until[OF s_R b_R sub w t1 t2, symmetric])
qed

lemma duxaux'_eval:
  assumes v: "duxaux' n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
    and de: "dux_eval (dargs cs_R cs_L args) nt daux = (dres, daux')"
    and we: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
  shows "dres = map (dux_post daux \<circ> dtabc n cs_R) res \<and>
    duxaux' n cs_R cs_L args cur daux' auxlist'"
proof (cases daux)
  case (DUX_gen d)
  have vd: "duaux' n cs_R cs_L args cur (fix_res d) auxlist"
    using v unfolding DUX_gen by (simp add: duxaux'_def)
  have sh: "ushape d" using duaux'_ushape(1)[OF vd] by simp
  have ag: "args_agg (dargs cs_R cs_L args) = None" by (simp add: dargs_def init_args_def)
  obtain dres0 d0 where e: "eval_dq (dargs cs_R cs_L args) nt (fix_res d) = (dres0, d0)"
    by (cases "eval_dq (dargs cs_R cs_L args) nt (fix_res d)")
  obtain d' where g: "geval_dq (dargs cs_R cs_L args) nt d = (dres, d')" and d': "daux' = DUX_gen d'"
    using de unfolding DUX_gen by (auto simp del: geval_dq.simps split: prod.splits)
  have r: "dres = dres0" and f: "fix_res d' = d0"
    using geval_dq_eq[OF ag sh, of nt] unfolding g e by simp_all
  show ?thesis unfolding r d' DUX_gen using duaux'_eval[OF vd nt e we] f by (simp add: duxaux'_def)
next
  case (DUX_win w)
  obtain dres0 w' where e: "uw_eval (dargs cs_R cs_L args) nt w = (dres0, w')"
    by (cases "uw_eval (dargs cs_R cs_L args) nt w")
  have r: "dres = dres0" and d': "daux' = DUX_win w'"
    using de unfolding DUX_win by (simp_all add: e)
  have c: "cpos cs_R (set cs_L) = {}" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and vs: "valid_uw (dargs cs_R cs_L args) cur w (dauxlist3 n cs_R auxlist)"
    using v unfolding DUX_win duxaux'_def by auto
  have we': "eval_until (args_ivl (dargs cs_R cs_L args)) nt (dauxlist3 n cs_R auxlist)
      = (map (dtabc n cs_R) res, dauxlist3 n cs_R auxlist')"
    using dauxlist3_eval_until[OF we] by simp
  have vw: "valid_uw (dargs cs_R cs_L args) cur w' (dauxlist3 n cs_R auxlist')"
    and rr: "dres0 = map (dtabc n cs_R) res"
    using valid_uw_eval[OF vs nt e we'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis unfolding r d' DUX_win using vw rr c inz w by (auto simp: duxaux'_def)
next
  case (DUX_wagg p a)
  have ne: "args_n (dargs cs_R cs_L args) = length cs_R" by simp
  obtain dres0 a' where e: "ua_eval (dargs cs_R cs_L args) p (length cs_R) nt a = (dres0, a')"
    by (cases "ua_eval (dargs cs_R cs_L args) p (length cs_R) nt a")
  have r: "dres = dres0" and d': "daux' = DUX_wagg p a'"
    using de unfolding DUX_wagg by (simp_all add: e)
  have c: "cpos cs_R (set cs_L) = {}" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table n (set cs_L) a1 \<and> table n (set cs_R) a2"
    and vs: "valid_ua (dargs cs_R cs_L args) p cur a (dauxlist3 n cs_R auxlist)"
    using v unfolding DUX_wagg duxaux'_def by auto
  have we': "eval_until (args_ivl (dargs cs_R cs_L args)) nt (dauxlist3 n cs_R auxlist)
      = (map (dtabc n cs_R) res, dauxlist3 n cs_R auxlist')"
    using dauxlist3_eval_until[OF we] by simp
  have vw: "valid_ua (dargs cs_R cs_L args) p cur a' (dauxlist3 n cs_R auxlist')"
    and rr: "dres0 = map (dagg_p p) (map (dtabc n cs_R) res)"
    using valid_ua_eval[OF vs nt e[folded ne] we'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis unfolding r d' DUX_wagg using vw rr c inz w
    by (auto simp: duxaux'_def)
qed

lemma duxaux'_length:
  "duxaux' n cs_R cs_L args cur daux auxlist \<Longrightarrow>
     dux_length (dargs cs_R cs_L args) daux = length auxlist"
  using duaux'_length valid_uw_length valid_ua_length
  by (cases daux) (auto simp: duxaux'_def dauxlist3_def glength_dq_eq[symmetric])

(*<*)
end
(*>*)
