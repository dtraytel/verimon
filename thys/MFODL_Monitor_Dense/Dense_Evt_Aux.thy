(*<*)
theory Dense_Evt_Aux
  imports Dense_Until_Gen Dense_Agg_Cache
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
  "dsx_init args msk = (if args_L args = [] then DSX_win (sw_init args)
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

text \<open>The windows are used for a closed left operand, whose kernel columns are then empty as
  well.\<close>

lemma dframe_Nil: "dframe kL [] \<Longrightarrow> kL = []"
  by (simp add: dframe_def)

definition dsxaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> dsaux_x \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "dsxaux' kR cR cL args cur daux auxlist \<longleftrightarrow> (case daux of
     DSX_gen d \<Rightarrow> dsaux' kR cR cL args cur d auxlist
   | DSX_win w \<Rightarrow> cL = [] \<and> (\<forall>(t, rel) \<in> set auxlist. table kR rel) \<and>
       valid_sw (dargs cR cL args) cur w (dauxlist kR cR auxlist)
   | DSX_wagg p a \<Rightarrow> cL = [] \<and> (\<forall>(t, rel) \<in> set auxlist. table kR rel) \<and>
       valid_sa (dargs cR cL args) p cur a (dauxlist kR cR auxlist))"

lemma dsxaux'_tables:
  "dsxaux' kR cR cL args cur daux auxlist \<Longrightarrow> \<forall>(t, rel) \<in> set auxlist. table kR rel"
  by (cases daux) (auto simp: dsxaux'_def dsaux'_def)

lemma dsxaux'_init:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "dsxaux' kR cR cL args 0 (dsx_init (dargs cR cL args) (dmsk cR cL)) []"
  using dsaux'_init[OF fR fL sub, of args] valid_sw_init
  by (auto simp: dsxaux'_def dsx_init_def dauxlist_def)

lemma dsxaux'_init_agg:
  assumes c: "cL = []" and ok: "dagg_ok p (length cR)"
  shows "dsxaux' kR cR cL args 0 (dsx_init_agg (dargs cR cL args) p) []"
  using valid_sa_init[of "dargs cR cL args" p] c ok
  by (auto simp: dsxaux'_def dsx_init_agg_def dauxlist_def)

lemma dsxaux'_add_new_ts:
  assumes v: "dsxaux' kR cR cL args cur daux auxlist" and nt: "cur \<le> nt"
  shows "dsxaux' kR cR cL args nt (dsx_add_new_ts (dargs cR cL args) nt daux)
      (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof (cases daux)
  case (DSX_gen d)
  then show ?thesis using dsaux'_add_new_ts[OF _ nt, of kR cR cL args d auxlist] v
    by (simp add: dsxaux'_def)
next
  case (DSX_win w)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sw (dargs cR cL args) cur w (dauxlist kR cR auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have "valid_sw (dargs cR cL args) nt (sw_add_new_ts (dargs cR cL args) nt w)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cR cL args)) (nt - t)) (dauxlist kR cR auxlist))"
    by (rule valid_sw_add_new_ts[OF vs nt])
  then show ?thesis using c w unfolding DSX_win by (simp add: dsxaux'_def dauxlist_filter)
next
  case (DSX_wagg p a)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sa (dargs cR cL args) p cur a (dauxlist kR cR auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have "valid_sa (dargs cR cL args) p nt (sa_add_new_ts (dargs cR cL args) p nt a)
      (filter (\<lambda>(t, rel). memR (args_ivl (dargs cR cL args)) (nt - t)) (dauxlist kR cR auxlist))"
    by (rule valid_sa_add_new_ts[OF vs nt])
  then show ?thesis using c w unfolding DSX_wagg by (simp add: dsxaux'_def dauxlist_filter)
qed

lemma dsxaux'_join:
  assumes v: "dsxaux' kR cR cL args cur daux auxlist"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and t1: "table kL rel1"
  shows "dsxaux' kR cR cL args cur (dsx_join (dargs cR cL args) (dtabc kL cL rel1) daux)
      (map (\<lambda>(t, rel). (t, join kR rel (args_pos args) kL rel1)) auxlist)"
proof (cases daux)
  case (DSX_gen d)
  have vd: "dsaux' kR cR cL args cur d auxlist" using v unfolding DSX_gen by (simp add: dsxaux'_def)
  show ?thesis unfolding DSX_gen by (simp add: dsxaux'_def dsaux'_join[OF vd fR fL sub t1])
next
  case (DSX_win w)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sw (dargs cR cL args) cur w (dauxlist kR cR auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have t1': "table [] (dtabc kL cL rel1)" using table_dtabc[of cL kL rel1] c by simp
  have "valid_sw (dargs cR cL args) cur (sw_join (dargs cR cL args) (dtabc kL cL rel1) w)
      (map (\<lambda>(t, rel). (t, join cR rel (args_pos args) cL (dtabc kL cL rel1)))
        (dauxlist kR cR auxlist))"
    using valid_sw_join[OF vs t1' refl] c by simp
  then show ?thesis using c dauxlist_wf_join[OF w sub t1, of "args_pos args"] unfolding DSX_win
    by (simp add: dsxaux'_def dauxlist_join[OF fR fL sub w t1])
next
  case (DSX_wagg p a)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sa (dargs cR cL args) p cur a (dauxlist kR cR auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have t1': "table [] (dtabc kL cL rel1)" using table_dtabc[of cL kL rel1] c by simp
  have "valid_sa (dargs cR cL args) p cur (sa_join (dargs cR cL args) p (dtabc kL cL rel1) a)
      (map (\<lambda>(t, rel). (t, join cR rel (args_pos args) cL (dtabc kL cL rel1)))
        (dauxlist kR cR auxlist))"
    using valid_sa_join[OF vs t1' refl] c by simp
  then show ?thesis using c dauxlist_wf_join[OF w sub t1, of "args_pos args"] unfolding DSX_wagg
    by (simp add: dsxaux'_def dauxlist_join[OF fR fL sub w t1])
qed

lemma dsxaux'_add_new_table:
  assumes v: "dsxaux' kR cR cL args cur daux auxlist"
    and t2: "table kR rel2" and f2: "finite rel2"
  shows "dsxaux' kR cR cL args cur
      (dsx_add_new_table (dargs cR cL args) (dtabc kR cR rel2) daux)
      (case auxlist of [] \<Rightarrow> [(cur, rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> rel2) # r else (cur, rel2) # auxlist)"
proof (cases daux)
  case (DSX_gen d)
  have vd: "dsaux' kR cR cL args cur d auxlist" using v unfolding DSX_gen by (simp add: dsxaux'_def)
  show ?thesis unfolding DSX_gen by (simp add: dsxaux'_def dsaux'_add_new_table[OF vd t2])
next
  case (DSX_win w)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sw (dargs cR cL args) cur w (dauxlist kR cR auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have tt: "table (args_R (dargs cR cL args)) (dtabc kR cR rel2)" by (simp add: table_dtabc)
  have ff: "finite (dtabc kR cR rel2)" using f2 by (rule finite_dtabc)
  have "valid_sw (dargs cR cL args) cur
      (sw_add_new_table (dargs cR cL args) (dtabc kR cR rel2) w)
      (case dauxlist kR cR auxlist of [] \<Rightarrow> [(cur, dtabc kR cR rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc kR cR rel2) # r
                         else (cur, dtabc kR cR rel2) # dauxlist kR cR auxlist)"
    by (rule valid_sw_add_new_table[OF vs tt ff])
  then show ?thesis using c dauxlist_wf_add_new_table[OF w t2, of cur] unfolding DSX_win
    by (simp add: dsxaux'_def dauxlist_add_new_table[symmetric])
next
  case (DSX_wagg p a)
  have c: "cL = []" and w: "\<forall>(t, rel) \<in> set auxlist. table kR rel"
    and vs: "valid_sa (dargs cR cL args) p cur a (dauxlist kR cR auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have tt: "table (args_R (dargs cR cL args)) (dtabc kR cR rel2)" by (simp add: table_dtabc)
  have ff: "finite (dtabc kR cR rel2)" using f2 by (rule finite_dtabc)
  have "valid_sa (dargs cR cL args) p cur
      (sa_add_new_table (dargs cR cL args) p (dtabc kR cR rel2) a)
      (case dauxlist kR cR auxlist of [] \<Rightarrow> [(cur, dtabc kR cR rel2)]
       | ((t, y) # r) \<Rightarrow> if t = cur then (t, y \<union> dtabc kR cR rel2) # r
                         else (cur, dtabc kR cR rel2) # dauxlist kR cR auxlist)"
    by (rule valid_sa_add_new_table[OF vs tt ff])
  then show ?thesis using c dauxlist_wf_add_new_table[OF w t2, of cur] unfolding DSX_wagg
    by (simp add: dsxaux'_def dauxlist_add_new_table[symmetric])
qed

lemma dsxaux'_result:
  assumes v: "dsxaux' kR cR cL args cur daux auxlist"
  shows "dsx_result (dargs cR cL args) daux
      = dsx_post daux (dtabc kR cR (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist,
          memL (args_ivl args) (cur - t)] {}))"
proof (cases daux)
  case (DSX_gen d)
  then show ?thesis using dsaux'_result[of kR cR cL args cur d auxlist] v
    by (simp add: dsxaux'_def)
next
  case (DSX_win w)
  have vs: "valid_sw (dargs cR cL args) cur w (dauxlist kR cR auxlist)"
    using v unfolding DSX_win dsxaux'_def by auto
  have "sw_result (dargs cR cL args) w
      = foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist kR cR auxlist,
          memL (args_ivl (dargs cR cL args)) (cur - t)] {}"
    by (rule valid_sw_result[OF vs])
  then show ?thesis unfolding DSX_win by (simp add: dtabc_result)
next
  case (DSX_wagg p a)
  have vs: "valid_sa (dargs cR cL args) p cur a (dauxlist kR cR auxlist)"
    using v unfolding DSX_wagg dsxaux'_def by auto
  have "sa_result (dargs cR cL args) p a
      = dagg_p p (foldr (\<union>) [rel. (t, rel) \<leftarrow> dauxlist kR cR auxlist,
          memL (args_ivl (dargs cR cL args)) (cur - t)] {})"
    by (rule valid_sa_result[OF vs])
  then show ?thesis unfolding DSX_wagg by (simp add: dtabc_result)
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
  "dux_init args = (if args_L args = [] \<and> memL (args_ivl args) 0 then DUX_win (uw_init args)
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

definition duxaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> duaux_x \<Rightarrow>
    event_data muaux \<Rightarrow> bool" where
  "duxaux' kL cL kR cR args cur daux auxlist \<longleftrightarrow> (case daux of
     DUX_gen d \<Rightarrow> duaux' kL cL kR cR args cur (fix_res d) auxlist
   | DUX_win w \<Rightarrow> cL = [] \<and> memL (args_ivl args) 0 \<and>
       (\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2) \<and>
       valid_uw (dargs cR cL args) cur w (dauxlist3 kL cL kR cR auxlist)
   | DUX_wagg p a \<Rightarrow> cL = [] \<and> memL (args_ivl args) 0 \<and>
       (\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2) \<and>
       valid_ua (dargs cR cL args) p cur a (dauxlist3 kL cL kR cR auxlist))"

lemma duxaux'_tables:
  "duxaux' kL cL kR cR args cur daux auxlist \<Longrightarrow>
     \<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
  by (cases daux) (auto simp: duxaux'_def duaux'_def)

lemma duxaux'_init:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
  shows "duxaux' kL cL kR cR args 0 (dux_init (dargs cR cL args)) []"
  using duaux'_init[OF fR fL sub, of args, folded ginit_dq_eq] valid_uw_init
  by (auto simp: duxaux'_def dux_init_def dauxlist3_def)

lemma duxaux'_init_agg:
  assumes c: "cL = []" and inz: "memL (args_ivl args) 0"
    and ok: "dagg_ok p (length cR)"
  shows "duxaux' kL cL kR cR args 0 (dux_init_agg (dargs cR cL args) p) []"
  using valid_ua_init[of "dargs cR cL args" p] c inz ok
  by (auto simp: duxaux'_def dux_init_agg_def dauxlist3_def)

lemma duxaux'_add_new:
  assumes v: "duxaux' kL cL kR cR args cur daux auxlist"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and t1: "table kL rel1" and t2: "table kR rel2"
    and f2: "finite rel2" and nt: "cur \<le> nt"
  shows "duxaux' kL cL kR cR args nt
      (dux_add_new (dargs cR cL args) (dmsk cR cL) (dtabc kL cL rel1) (dtabc kR cR rel2) nt daux)
      (update_until args rel1 rel2 nt auxlist)"
proof (cases daux)
  case (DUX_gen d)
  have vd: "duaux' kL cL kR cR args cur (fix_res d) auxlist"
    using v unfolding DUX_gen by (simp add: duxaux'_def)
  have sh: "ushape d" and a1: "\<And>k v. Mapping.lookup (ua1 d) k = Some v \<Longrightarrow> v < utp d"
    using duaux'_ushape[OF vd] by simp_all
  have g: "fix_res (gadd_new_dq (dargs cR cL args) (dmsk cR cL) (dtabc kL cL rel1)
        (dtabc kR cR rel2) nt d)
      = dadd_new_dq (dargs cR cL args) (dmsk cR cL) (dtabc kL cL rel1) (dtabc kR cR rel2) nt
        (fix_res d)"
    by (rule gadd_new_dq_eq(1)[OF _ sh a1]) simp
  show ?thesis
    using duaux'_add_new[OF vd fR fL sub aL aR t1 t2 f2 nt] unfolding DUX_gen
    by (simp add: duxaux'_def g)
next
  case (DUX_win w)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_uw (dargs cR cL args) cur w (dauxlist3 kL cL kR cR auxlist)"
    using v unfolding DUX_win duxaux'_def by auto
  have L: "args_L (dargs cR cL args) = []" using c by simp
  have t1': "table [] (dtabc kL cL rel1)" using table_dtabc[of cL kL rel1] c by simp
  have tt: "table (args_R (dargs cR cL args)) (dtabc kR cR rel2)" by (simp add: table_dtabc)
  have ff: "finite (dtabc kR cR rel2)" using f2 by (rule finite_dtabc)
  have "valid_uw (dargs cR cL args) nt
      (uw_add_new (dargs cR cL args) (dtabc kL cL rel1) (dtabc kR cR rel2) nt w)
      (update_until (dargs cR cL args) (dtabc kL cL rel1) (dtabc kR cR rel2) nt
        (dauxlist3 kL cL kR cR auxlist))"
    by (rule valid_uw_add_new[OF vs L t1' refl tt ff _ nt]) (simp add: inz)
  moreover have "dauxlist3 kL cL kR cR (update_until args rel1 rel2 nt auxlist)
      = update_until (dargs cR cL args) (dtabc kL cL rel1) (dtabc kR cR rel2) nt
          (dauxlist3 kL cL kR cR auxlist)"
    by (rule dauxlist3_update_until[OF fR fL sub w t1 t2 aL aR]) simp_all
  ultimately show ?thesis using c inz dauxlist3_wf_update_until[OF w sub t1 t2 aL aR, of nt]
    unfolding DUX_win by (simp add: duxaux'_def)
next
  case (DUX_wagg p a)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_ua (dargs cR cL args) p cur a (dauxlist3 kL cL kR cR auxlist)"
    using v unfolding DUX_wagg duxaux'_def by auto
  have L: "args_L (dargs cR cL args) = []" using c by simp
  have t1': "table [] (dtabc kL cL rel1)" using table_dtabc[of cL kL rel1] c by simp
  have tt: "table (args_R (dargs cR cL args)) (dtabc kR cR rel2)" by (simp add: table_dtabc)
  have ff: "finite (dtabc kR cR rel2)" using f2 by (rule finite_dtabc)
  have "valid_ua (dargs cR cL args) p nt
      (ua_add_new (dargs cR cL args) p (args_n (dargs cR cL args))
        (dtabc kL cL rel1) (dtabc kR cR rel2) nt a)
      (update_until (dargs cR cL args) (dtabc kL cL rel1) (dtabc kR cR rel2) nt
        (dauxlist3 kL cL kR cR auxlist))"
    by (rule valid_ua_add_new[OF vs L t1' refl tt ff _ nt]) (simp add: inz)
  moreover have "dauxlist3 kL cL kR cR (update_until args rel1 rel2 nt auxlist)
      = update_until (dargs cR cL args) (dtabc kL cL rel1) (dtabc kR cR rel2) nt
          (dauxlist3 kL cL kR cR auxlist)"
    by (rule dauxlist3_update_until[OF fR fL sub w t1 t2 aL aR]) simp_all
  ultimately show ?thesis using c inz dauxlist3_wf_update_until[OF w sub t1 t2 aL aR, of nt]
    unfolding DUX_wagg by (simp add: duxaux'_def)
qed

lemma duxaux'_eval:
  assumes v: "duxaux' kL cL kR cR args cur daux auxlist" and nt: "cur \<le> nt"
    and de: "dux_eval (dargs cR cL args) nt daux = (dres, daux')"
    and we: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
  shows "dres = map (dux_post daux \<circ> dtabc kR cR) res \<and>
    duxaux' kL cL kR cR args cur daux' auxlist'"
proof (cases daux)
  case (DUX_gen d)
  have vd: "duaux' kL cL kR cR args cur (fix_res d) auxlist"
    using v unfolding DUX_gen by (simp add: duxaux'_def)
  have sh: "ushape d" using duaux'_ushape(1)[OF vd] by simp
  have ag: "args_agg (dargs cR cL args) = None" by simp
  obtain dres0 d0 where e: "eval_dq (dargs cR cL args) nt (fix_res d) = (dres0, d0)"
    by (cases "eval_dq (dargs cR cL args) nt (fix_res d)")
  obtain d' where g: "geval_dq (dargs cR cL args) nt d = (dres, d')" and d': "daux' = DUX_gen d'"
    using de unfolding DUX_gen by (auto simp del: geval_dq.simps split: prod.splits)
  have r: "dres = dres0" and f: "fix_res d' = d0"
    using geval_dq_eq[OF ag sh, of nt] unfolding g e by simp_all
  show ?thesis unfolding r d' DUX_gen using duaux'_eval[OF vd nt e we] f by (simp add: duxaux'_def)
next
  case (DUX_win w)
  obtain dres0 w' where e: "uw_eval (dargs cR cL args) nt w = (dres0, w')"
    by (cases "uw_eval (dargs cR cL args) nt w")
  have r: "dres = dres0" and d': "daux' = DUX_win w'"
    using de unfolding DUX_win by (simp_all add: e)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_uw (dargs cR cL args) cur w (dauxlist3 kL cL kR cR auxlist)"
    using v unfolding DUX_win duxaux'_def by auto
  have we': "eval_until (args_ivl (dargs cR cL args)) nt (dauxlist3 kL cL kR cR auxlist)
      = (map (dtabc kR cR) res, dauxlist3 kL cL kR cR auxlist')"
    using dauxlist3_eval_until[OF we] by simp
  have vw: "valid_uw (dargs cR cL args) cur w' (dauxlist3 kL cL kR cR auxlist')"
    and rr: "dres0 = map (dtabc kR cR) res"
    using valid_uw_eval[OF vs nt e we'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis unfolding r d' DUX_win using vw rr c inz w by (auto simp: duxaux'_def)
next
  case (DUX_wagg p a)
  have ne: "args_n (dargs cR cL args) = length cR" by simp
  obtain dres0 a' where e: "ua_eval (dargs cR cL args) p (length cR) nt a = (dres0, a')"
    by (cases "ua_eval (dargs cR cL args) p (length cR) nt a")
  have r: "dres = dres0" and d': "daux' = DUX_wagg p a'"
    using de unfolding DUX_wagg by (simp_all add: e)
  have c: "cL = []" and inz: "memL (args_ivl args) 0"
    and w: "\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2"
    and vs: "valid_ua (dargs cR cL args) p cur a (dauxlist3 kL cL kR cR auxlist)"
    using v unfolding DUX_wagg duxaux'_def by auto
  have we': "eval_until (args_ivl (dargs cR cL args)) nt (dauxlist3 kL cL kR cR auxlist)
      = (map (dtabc kR cR) res, dauxlist3 kL cL kR cR auxlist')"
    using dauxlist3_eval_until[OF we] by simp
  have vw: "valid_ua (dargs cR cL args) p cur a' (dauxlist3 kL cL kR cR auxlist')"
    and rr: "dres0 = map (dagg_p p) (map (dtabc kR cR) res)"
    using valid_ua_eval[OF vs nt e[folded ne] we'] by simp_all
  have "set auxlist' \<subseteq> set auxlist"
    using eval_until_auxlist'[OF we] by (simp add: set_drop_subset)
  then show ?thesis unfolding r d' DUX_wagg using vw rr c inz w
    by (auto simp: duxaux'_def)
qed

lemma duxaux'_length:
  "duxaux' kL cL kR cR args cur daux auxlist \<Longrightarrow>
     dux_length (dargs cR cL args) daux = length auxlist"
  using duaux'_length valid_uw_length valid_ua_length
  by (cases daux) (auto simp: duxaux'_def dauxlist3_def glength_dq_eq[symmetric])

section \<open>The structures the evaluator runs\<close>

text \<open>
  The evaluator runs the structures above in the representations of
  @{theory MFODL_Monitor_Dense.Dense_Unbox_Eval}, @{theory MFODL_Monitor_Dense.Dense_Unbox_UAgg}
  and @{theory MFODL_Monitor_Dense.Dense_Agg_Cache}, and its buffers in queues
  (@{typ "'a mbuf_t"}).  Each is related to the structure above by a function -- @{text rdsx},
  @{text rdux} and @{const Rep_mbuf_t} -- with which every operation commutes on every input,
  so the simulation states its relations on the images.
\<close>

subsection \<open>The Since and Until structures, dispatched\<close>

text \<open>The structure of a fused aggregating window carries the node's guard: the constraint the
  node's own result is read through, if it has one.  Only the read looks at it; every other
  operation passes it along, and the structure above it stands for does not have it at all.\<close>

datatype udsaux_x = UDSX_gen "event_data dmsaux" | UDSX_win swaux
  | UDSX_wagg daggp "uconstr option" uswaggc

fun rdsx :: "udsaux_x \<Rightarrow> dsaux_x" where
  "rdsx (UDSX_gen d) = DSX_gen d"
| "rdsx (UDSX_win w) = DSX_win w"
| "rdsx (UDSX_wagg p q a) = DSX_wagg p (rsa (ucs a))"

fun usx_q :: "udsaux_x \<Rightarrow> uconstr option" where
  "usx_q (UDSX_wagg p q a) = q"
| "usx_q _ = None"

definition udsx_init :: "args \<Rightarrow> bool list \<Rightarrow> udsaux_x" where
  "udsx_init args msk = (if args_L args = [] then UDSX_win (sw_init args)
     else UDSX_gen (dinit_msaux args msk))"

definition udsx_init_agg :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> udsaux_x" where
  "udsx_init_agg args p q = UDSX_wagg p q (usc_init args p q)"

fun udsx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_ts args nt (UDSX_gen d) = UDSX_gen (dadd_new_ts_msaux args nt d)"
| "udsx_add_new_ts args nt (UDSX_win w) = UDSX_win (sw_add_new_ts args nt w)"
| "udsx_add_new_ts args nt (UDSX_wagg p q a) = UDSX_wagg p q (usc_add_new_ts args p q nt a)"

fun udsx_join :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_join args X (UDSX_gen d) = UDSX_gen (dgc_join_lz args X d)"
| "udsx_join args X (UDSX_win w) = UDSX_win (sw_join args X w)"
| "udsx_join args X (UDSX_wagg p q a) = UDSX_wagg p q (usc_join args p q X a)"

fun udsx_add_new_table :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_table args X (UDSX_gen d) = UDSX_gen (dadd_new_table_lz args X d)"
| "udsx_add_new_table args X (UDSX_win w) = UDSX_win (sw_add_new_table args X w)"
| "udsx_add_new_table args X (UDSX_wagg p q a) = UDSX_wagg p q (usc_add_new_table args p q X a)"

fun udsx_result :: "args \<Rightarrow> udsaux_x \<Rightarrow> utable" where
  "udsx_result args (UDSX_gen d) = dresult_msaux args d"
| "udsx_result args (UDSX_win w) = sw_result args w"
| "udsx_result args (UDSX_wagg p q a) = usc_result q args p a"

lemma usx_q_add_new_ts[simp]: "usx_q (udsx_add_new_ts args nt d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_join[simp]: "usx_q (udsx_join args X d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_add_new_table[simp]: "usx_q (udsx_add_new_table args X d) = usx_q d"
  by (cases d) simp_all

lemma dsx_init_rdsx: "dsx_init args msk = rdsx (udsx_init args msk)"
  by (simp add: dsx_init_def udsx_init_def)

lemma dsx_init_agg_rdsx[simp]: "rdsx (udsx_init_agg args p q) = dsx_init_agg args p"
  by (simp add: dsx_init_agg_def udsx_init_agg_def sa_init_rsa usc_init_ucs)

lemma usx_q_init_agg[simp]: "usx_q (udsx_init_agg args p q) = q"
  by (simp add: udsx_init_agg_def)

lemma usx_q_init[simp]: "usx_q (udsx_init args msk) = None"
  by (simp add: udsx_init_def)

lemma dsx_add_new_ts_rdsx: "dsx_add_new_ts args nt (rdsx d) = rdsx (udsx_add_new_ts args nt d)"
  by (cases d) (simp_all add: sa_add_new_ts_rsa usc_add_new_ts_ucs)

lemma dsx_join_rdsx: "dsx_join args X (rdsx d) = rdsx (udsx_join args X d)"
  by (cases d) (simp_all add: sa_join_rsa usc_join_ucs)

lemma dsx_add_new_table_rdsx:
  "dsx_add_new_table args X (rdsx d) = rdsx (udsx_add_new_table args X d)"
  by (cases d) (simp_all add: sa_add_new_table_rsa usc_add_new_table_ucs)

text \<open>The structure above reports the node's whole result; this one reports it read through the
  guard straight away.\<close>

lemma dsx_result_rdsx:
  "usx_q d = q \<Longrightarrow> ufilt q (dsx_result args (rdsx d)) = udsx_result args d"
  by (cases d) (auto simp: sa_result_rsa usc_result_ucs)

datatype uduaux_x = UDUX_gen "event_data mmuaux_dq" | UDUX_win uwaux | UDUX_wagg daggp uuwagg

fun rdux :: "uduaux_x \<Rightarrow> duaux_x" where
  "rdux (UDUX_gen d) = DUX_gen d"
| "rdux (UDUX_win w) = DUX_win w"
| "rdux (UDUX_wagg p a) = DUX_wagg p (rua a)"

definition udux_init :: "args \<Rightarrow> uduaux_x" where
  "udux_init args = (if args_L args = [] \<and> memL (args_ivl args) 0 then UDUX_win (uw_init args)
     else UDUX_gen (ginit_dq args))"

definition udux_init_agg :: "args \<Rightarrow> daggp \<Rightarrow> uduaux_x" where
  "udux_init_agg args p = UDUX_wagg p (uua_init args p)"

fun udux_add_new :: "args \<Rightarrow> bool list \<Rightarrow> utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> uduaux_x \<Rightarrow> uduaux_x" where
  "udux_add_new args msk rel1 rel2 nt (UDUX_gen d) = UDUX_gen (gadd_new_dq args msk rel1 rel2 nt d)"
| "udux_add_new args msk rel1 rel2 nt (UDUX_win w) = UDUX_win (uw_add_new args rel1 rel2 nt w)"
| "udux_add_new args msk rel1 rel2 nt (UDUX_wagg p a) =
     UDUX_wagg p (uua_add_new args p (args_n args) rel1 rel2 nt a)"

fun udux_eval :: "args \<Rightarrow> ts \<Rightarrow> uduaux_x \<Rightarrow> utable list \<times> uduaux_x" where
  "udux_eval args nt (UDUX_gen d) = (let (zs, d') = geval_dq args nt d in (zs, UDUX_gen d'))"
| "udux_eval args nt (UDUX_win w) = (let (zs, w') = uw_eval args nt w in (zs, UDUX_win w'))"
| "udux_eval args nt (UDUX_wagg p a) =
     (let (zs, a') = uua_eval args p (args_n args) nt a in (zs, UDUX_wagg p a'))"

fun udux_length :: "args \<Rightarrow> uduaux_x \<Rightarrow> nat" where
  "udux_length args (UDUX_gen d) = glength_dq args d"
| "udux_length args (UDUX_win w) = uw_length args w"
| "udux_length args (UDUX_wagg p a) = uua_length args a"

lemma dux_init_rdux: "dux_init args = rdux (udux_init args)"
  by (simp add: dux_init_def udux_init_def)

lemma dux_init_agg_rdux: "dux_init_agg args p = rdux (udux_init_agg args p)"
  by (simp add: dux_init_agg_def udux_init_agg_def rua_init)

lemma dux_add_new_rdux:
  "dux_add_new args msk rel1 rel2 nt (rdux d) = rdux (udux_add_new args msk rel1 rel2 nt d)"
  by (cases d) (simp_all add: ua_add_new_rua)

lemma dux_eval_rdux:
  "dux_eval args nt (rdux d) = (case udux_eval args nt d of (zs, d') \<Rightarrow> (zs, rdux d'))"
  by (cases d) (simp_all add: ua_eval_rua split: prod.splits)

lemma dux_length_rdux: "dux_length args (rdux d) = udux_length args d"
  by (cases d) (simp_all add: ua_length_rua)

subsection \<open>The buffers\<close>

type_synonym uebuf2 = "event_data mebuf2"
type_synonym uebufn = "event_data mebufn"
type_synonym uebuf2S = "event_data mebuf2S"

abbreviation rbuf2 :: "uebuf2 \<Rightarrow> event_data mbuf2" where
  "rbuf2 \<equiv> map_prod Rep_mbuf_t Rep_mbuf_t"

fun rbufS :: "uebuf2S \<Rightarrow> event_data mbuf2S" where
  "rbufS (xs, ys, ts, skew) = (Rep_mbuf_t xs, Rep_mbuf_t ys, Rep_mbuf_t ts, skew)"

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

abbreviation rbufo :: "utable mbuf_t \<times> utable option mbuf_t \<Rightarrow>
    event_data table list \<times> event_data table option list" where
  "rbufo \<equiv> map_prod Rep_mbuf_t Rep_mbuf_t"

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
  "mbufn_take (\<lambda>as zs. zs @ [dmulti_join ps ns as]) [] (map Rep_mbuf_t buf)
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
    by (simp add: mbuf_t_empty.rep_eq gmulti_join_eq[abs_def] del: mbufn_take.simps)
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

subsection \<open>The Since buffer's traversal\<close>

fun uedsx_eval_since :: "args \<Rightarrow> utable list \<Rightarrow> uebuf2S \<Rightarrow> udsaux_x \<Rightarrow>
    utable list \<times> uebuf2S \<times> udsaux_x" where
  "uedsx_eval_since args rs (xs, ys, ts, skew) aux =
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow>
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          (if skew \<or> memL (args_ivl args) 0
           then (rev rs, (x ## xs', mbuf_t_empty, t ## ts', skew), aux)
           else (let aux' = udsx_join args x (udsx_add_new_ts args t aux)
             in (rev (udsx_result args aux' # rs), (xs', mbuf_t_empty, ts', True), aux')))
        | (None, ts') \<Rightarrow> (rev rs, (x ## xs', mbuf_t_empty, mbuf_t_empty, skew), aux))
      | (None, xs') \<Rightarrow> (rev rs, (mbuf_t_empty, mbuf_t_empty, ts, skew), aux))
    | (Some y, ys') \<Rightarrow>
      if skew then uedsx_eval_since args rs (xs, ys', ts, False) (udsx_add_new_table args y aux)
      else
      (case mbuf_t_cases xs of (Some x1, xs1) \<Rightarrow>
        (case mbuf_t_cases ts of (Some t1, ts1) \<Rightarrow>
          (let aux1 = udsx_add_new_table args y (udsx_join args x1 (udsx_add_new_ts args t1 aux))
           in uedsx_eval_since args (udsx_result args aux1 # rs) (xs1, ys', ts1, False) aux1)
        | (None, ts1) \<Rightarrow> (rev rs, (x1 ## xs1, y ## ys', ts1, skew), aux))
      | (None, xs1) \<Rightarrow> (rev rs, (mbuf_t_empty, y ## ys', ts, skew), aux)))"

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
  @{const dsx_eval_since} on the images reports the same results, read through the node's guard.
  The accumulator is carried the same way, so the statement relates the two lists it is started
  with.\<close>

lemma dsx_eval_since_rdsx:
  "map (ufilt (usx_q aux)) Rs = rs \<Longrightarrow>
   (case dsx_eval_since args Rs (rbufS buf) (rdsx aux) of
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
      (auto simp: x y t Let_def rev_map[symmetric] dsx_join_rdsx dsx_add_new_ts_rdsx
        dsx_add_new_table_rdsx dsx_result_rdsx mbuf_t_Cons.rep_eq mbuf_t_empty.rep_eq
        Rep_mbuf_t_cases(1,2)[where xs = ts and xs' = ts'] Rep_mbuf_t_cases(1,2)[where xs = xs and xs' = xs']
        Rep_mbuf_t_cases(1,2)[where xs = ys and xs' = ys']
        simp del: uedsx_eval_since.simps split: prod.splits)
qed

lemma dsx_eval_since_rdsx0:
  "(case dsx_eval_since args [] (rbufS buf) (rdsx aux) of
      (Zs, bf, a) \<Rightarrow> (map (ufilt (usx_q aux)) Zs, bf, a))
   = (case uedsx_eval_since args [] buf aux of
        (zs, buf', aux') \<Rightarrow> (zs, rbufS buf', rdsx aux'))"
  using dsx_eval_since_rdsx[where rs = "[]" and Rs = "[]"] by simp

(*<*)
end
(*>*)