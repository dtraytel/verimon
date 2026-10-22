(*<*)
theory Window_Dispatch
  imports Agg_Cache Match_Window
begin
(*>*)



section \<open>Choosing the structure at the ascending frame\<close>

text \<open>
  The executable Since and Until nodes carry one of two structures: the general one of
  @{theory MFODL_Monitor_Exec.Frame_Aux}, or the sliding window of
  @{theory MFODL_Monitor_Exec.Window} where the left operand is closed (and, for the Until,
  the interval contains zero).  The choice is made once, when the node is built, from the
  arguments alone; the operations dispatch on it, and the relation to the kernel's abstract
  auxiliary list is the disjunction of the two structures' relations.  The five Since lemmas and
  the four Until lemmas that the simulation uses are restated for the sum, so that nothing
  downstream needs to know which structure runs.
\<close>

subsection \<open>The Since structure\<close>

datatype esaux_x = ESX_gen "event_data emsaux" | ESX_win swaux | ESX_wagg eaggp swagg

text \<open>The window is chosen from the arguments alone; the window with the aggregate is chosen by
  the compiler, which knows the aggregation the kernel fused into the node.\<close>

definition esx_init :: "args \<Rightarrow> bool list \<Rightarrow> esaux_x" where
  "esx_init args msk = (if args_L args = [] then ESX_win (sw_init args)
     else ESX_gen (einit_msaux args msk))"

definition esx_init_agg :: "args \<Rightarrow> eaggp \<Rightarrow> esaux_x" where
  "esx_init_agg args p = ESX_wagg p (sa_init args p)"

fun esx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> esaux_x \<Rightarrow> esaux_x" where
  "esx_add_new_ts args nt (ESX_gen d) = ESX_gen (eadd_new_ts_msaux args nt d)"
| "esx_add_new_ts args nt (ESX_win w) = ESX_win (sw_add_new_ts args nt w)"
| "esx_add_new_ts args nt (ESX_wagg p a) = ESX_wagg p (sa_add_new_ts args p nt a)"

fun esx_join :: "args \<Rightarrow> event_data table \<Rightarrow> esaux_x \<Rightarrow> esaux_x" where
  "esx_join args X (ESX_gen d) = ESX_gen (egc_join_lz args X d)"
| "esx_join args X (ESX_win w) = ESX_win (sw_join args X w)"
| "esx_join args X (ESX_wagg p a) = ESX_wagg p (sa_join args p X a)"

fun esx_add_new_table :: "args \<Rightarrow> event_data table \<Rightarrow> esaux_x \<Rightarrow> esaux_x" where
  "esx_add_new_table args X (ESX_gen d) = ESX_gen (eadd_new_table_lz args X d)"
| "esx_add_new_table args X (ESX_win w) = ESX_win (sw_add_new_table args X w)"
| "esx_add_new_table args X (ESX_wagg p a) = ESX_wagg p (sa_add_new_table args p X a)"

fun esx_result :: "args \<Rightarrow> esaux_x \<Rightarrow> event_data table" where
  "esx_result args (ESX_gen d) = eresult_msaux args d"
| "esx_result args (ESX_win w) = sw_result args w"
| "esx_result args (ESX_wagg p a) = sa_result args p a"

text \<open>What a structure reports, relative to the window's union: the union itself, or its
  aggregate.  The choice is fixed with the structure and no operation changes it.\<close>

fun esx_post :: "esaux_x \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "esx_post (ESX_gen d) = id"
| "esx_post (ESX_win w) = id"
| "esx_post (ESX_wagg p a) = eagg_p p"

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

text \<open>Which aggregate, if any, a structure reports; the compiler and the simulation tell the
  structures apart by it.\<close>

fun esx_agg :: "esaux_x \<Rightarrow> eaggp option" where
  "esx_agg (ESX_gen d) = None"
| "esx_agg (ESX_win w) = None"
| "esx_agg (ESX_wagg p a) = Some p"

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

text \<open>The windows are used for a closed left operand, whose kernel columns are then empty as
  well.\<close>

definition esxaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> esaux_x \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "esxaux' kR cR cL args cur daux auxlist \<longleftrightarrow> (case daux of
     ESX_gen d \<Rightarrow> esaux' kR cR cL args cur d auxlist
   | ESX_win w \<Rightarrow> cL = [] \<and> (\<forall>(t, rel) \<in> set auxlist. table kR rel) \<and>
       valid_sw (eargs cR cL args) cur w (eauxlist kR cR auxlist)
   | ESX_wagg p a \<Rightarrow> cL = [] \<and> (\<forall>(t, rel) \<in> set auxlist. table kR rel) \<and>
       valid_sa (eargs cR cL args) p cur a (eauxlist kR cR auxlist))"

text \<open>The kernel's @{text eval_since} with the dispatching operations put in.\<close>

fun esx_eval_since :: "args \<Rightarrow> event_data table list \<Rightarrow> event_data mbuf2S \<Rightarrow> esaux_x \<Rightarrow>
    event_data table list \<times> event_data mbuf2S \<times> esaux_x" where
  "esx_eval_since args rs (x # xs, [], t # ts, skew) daux =
    (if skew \<or> memL (args_ivl args) 0
     then (rev rs, (x # xs, [], t # ts, skew), daux)
     else (let daux' = esx_join args x (esx_add_new_ts args t daux)
       in (rev (esx_result args daux' # rs), (xs, [], ts, True), daux')))"
| "esx_eval_since args rs (xs, y # ys, ts, True) daux =
    esx_eval_since args rs (xs, ys, ts, False) (esx_add_new_table args y daux)"
| "esx_eval_since args rs (x # xs, y # ys, t # ts, False) daux =
    (let daux' = esx_add_new_table args y
       (esx_join args x (esx_add_new_ts args t daux))
     in esx_eval_since args (esx_result args daux' # rs) (xs, ys, ts, False) daux')"
| "esx_eval_since args rs buf daux = (rev rs, buf, daux)"

subsection \<open>The Until structure\<close>

datatype euaux_x = EUX_gen "event_data mmuaux_dq" | EUX_win uwaux | EUX_wagg eaggp uwagg

definition eux_init :: "args \<Rightarrow> euaux_x" where
  "eux_init args = (if args_L args = [] \<and> memL (args_ivl args) 0 then EUX_win (uw_init args)
     else EUX_gen (ginit_dq args))"

fun eux_add_new :: "args \<Rightarrow> bool list \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
    euaux_x \<Rightarrow> euaux_x" where
  "eux_add_new args msk rel1 rel2 nt (EUX_gen d) = EUX_gen (gadd_new_dq args msk rel1 rel2 nt d)"
| "eux_add_new args msk rel1 rel2 nt (EUX_win w) = EUX_win (uw_add_new args rel1 rel2 nt w)"
| "eux_add_new args msk rel1 rel2 nt (EUX_wagg p a) =
     EUX_wagg p (ua_add_new args p (args_n args) rel1 rel2 nt a)"

fun eux_eval :: "args \<Rightarrow> ts \<Rightarrow> euaux_x \<Rightarrow> event_data table list \<times> euaux_x" where
  "eux_eval args nt (EUX_gen d) = (let (zs, d') = geval_dq args nt d in (zs, EUX_gen d'))"
| "eux_eval args nt (EUX_win w) = (let (zs, w') = uw_eval args nt w in (zs, EUX_win w'))"
| "eux_eval args nt (EUX_wagg p a) =
     (let (zs, a') = ua_eval args p (args_n args) nt a in (zs, EUX_wagg p a'))"

definition eux_init_agg :: "args \<Rightarrow> eaggp \<Rightarrow> euaux_x" where
  "eux_init_agg args p = EUX_wagg p (ua_init args p)"

text \<open>What a structure reports for each finished time point, relative to the window's union at
  it: the union itself, or its aggregate.  As on the Since side the choice is fixed with the
  structure and no operation changes it.\<close>

fun eux_post :: "euaux_x \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eux_post (EUX_gen d) = id"
| "eux_post (EUX_win w) = id"
| "eux_post (EUX_wagg p a) = eagg_p p"

fun eux_agg :: "euaux_x \<Rightarrow> eaggp option" where
  "eux_agg (EUX_gen d) = None"
| "eux_agg (EUX_win w) = None"
| "eux_agg (EUX_wagg p a) = Some p"

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

definition euxaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> euaux_x \<Rightarrow>
    event_data muaux \<Rightarrow> bool" where
  "euxaux' kL cL kR cR args cur daux auxlist \<longleftrightarrow> (case daux of
     EUX_gen d \<Rightarrow> euaux' kL cL kR cR args cur (fix_res d) auxlist
   | EUX_win w \<Rightarrow> cL = [] \<and> memL (args_ivl args) 0 \<and>
       (\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2) \<and>
       valid_uw (eargs cR cL args) cur w (eauxlist3 kL cL kR cR auxlist)
   | EUX_wagg p a \<Rightarrow> cL = [] \<and> memL (args_ivl args) 0 \<and>
       (\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2) \<and>
       valid_ua (eargs cR cL args) p cur a (eauxlist3 kL cL kR cR auxlist))"

section \<open>The structures the evaluator runs\<close>

text \<open>
  The evaluator runs the structures above in the representations of
  the executable windows of @{theory MFODL_Monitor_Exec.Since_Agg}, @{theory MFODL_Monitor_Exec.Until_Agg}
  and @{theory MFODL_Monitor_Exec.Agg_Cache}, and its buffers in queues
  (@{typ "'a mbuf_t"}).  Each is related to the structure above by a function -- @{text rdsx},
  @{text rdux} and @{const Rep_mbuf_t} -- with which every operation commutes on every input,
  so the simulation states its relations on the images.
\<close>

subsection \<open>The Since and Until structures, dispatched\<close>

text \<open>The structure of a fused aggregating window carries the node's guard: the constraint the
  node's own result is read through, if it has one.  Only the read looks at it; every other
  operation passes it along, and the structure above it stands for does not have it at all.\<close>

datatype udsaux_x = UDSX_gen "event_data emsaux" | UDSX_win swaux
  | UDSX_wagg eaggp "uconstr option" uswaggc

fun rdsx :: "udsaux_x \<Rightarrow> esaux_x" where
  "rdsx (UDSX_gen d) = ESX_gen d"
| "rdsx (UDSX_win w) = ESX_win w"
| "rdsx (UDSX_wagg p q a) = ESX_wagg p (rsc a)"

fun usx_q :: "udsaux_x \<Rightarrow> uconstr option" where
  "usx_q (UDSX_wagg p q a) = q"
| "usx_q _ = None"

definition udsx_init :: "args \<Rightarrow> bool list \<Rightarrow> udsaux_x" where
  "udsx_init args msk = (if args_L args = [] then UDSX_win (sw_init args)
     else UDSX_gen (einit_msaux args msk))"

definition udsx_init_agg :: "args \<Rightarrow> eaggp \<Rightarrow> uconstr option \<Rightarrow> udsaux_x" where
  "udsx_init_agg args p q = UDSX_wagg p q (usc_init args p q)"

fun udsx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_ts args nt (UDSX_gen d) = UDSX_gen (eadd_new_ts_msaux args nt d)"
| "udsx_add_new_ts args nt (UDSX_win w) = UDSX_win (sw_add_new_ts args nt w)"
| "udsx_add_new_ts args nt (UDSX_wagg p q a) = UDSX_wagg p q (usc_add_new_ts args p q nt a)"

fun udsx_join :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_join args X (UDSX_gen d) = UDSX_gen (egc_join_lz args X d)"
| "udsx_join args X (UDSX_win w) = UDSX_win (sw_join args X w)"
| "udsx_join args X (UDSX_wagg p q a) = UDSX_wagg p q (usc_join args p q X a)"

fun udsx_add_new_table :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_table args X (UDSX_gen d) = UDSX_gen (eadd_new_table_lz args X d)"
| "udsx_add_new_table args X (UDSX_win w) = UDSX_win (sw_add_new_table args X w)"
| "udsx_add_new_table args X (UDSX_wagg p q a) = UDSX_wagg p q (usc_add_new_table args p q X a)"

fun udsx_result :: "args \<Rightarrow> udsaux_x \<Rightarrow> utable" where
  "udsx_result args (UDSX_gen d) = eresult_msaux args d"
| "udsx_result args (UDSX_win w) = sw_result args w"
| "udsx_result args (UDSX_wagg p q a) = usc_result q args p a"

lemma usx_q_add_new_ts[simp]: "usx_q (udsx_add_new_ts args nt d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_join[simp]: "usx_q (udsx_join args X d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_add_new_table[simp]: "usx_q (udsx_add_new_table args X d) = usx_q d"
  by (cases d) simp_all

lemma esx_init_agg_rdsx[simp]: "rdsx (udsx_init_agg args p q) = esx_init_agg args p"
  by (simp add: esx_init_agg_def udsx_init_agg_def sa_init_rsc[symmetric])

lemma usx_q_init_agg[simp]: "usx_q (udsx_init_agg args p q) = q"
  by (simp add: udsx_init_agg_def)

lemma usx_q_init[simp]: "usx_q (udsx_init args msk) = None"
  by (simp add: udsx_init_def)

datatype uduaux_x = UDUX_gen "event_data mmuaux_dq" | UDUX_win uwaux | UDUX_wagg eaggp uuwagg

fun rdux :: "uduaux_x \<Rightarrow> euaux_x" where
  "rdux (UDUX_gen d) = EUX_gen d"
| "rdux (UDUX_win w) = EUX_win w"
| "rdux (UDUX_wagg p a) = EUX_wagg p (rua a)"

definition udux_init :: "args \<Rightarrow> uduaux_x" where
  "udux_init args = (if args_L args = [] \<and> memL (args_ivl args) 0 then UDUX_win (uw_init args)
     else UDUX_gen (ginit_dq args))"

definition udux_init_agg :: "args \<Rightarrow> eaggp \<Rightarrow> uduaux_x" where
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

subsection \<open>The buffers\<close>

type_synonym uebuf2 = "event_data mebuf2"
type_synonym uebufn = "event_data mebufn"
type_synonym uebuf2S = "event_data mebuf2S"

abbreviation rbuf2 :: "uebuf2 \<Rightarrow> event_data mbuf2" where
  "rbuf2 \<equiv> map_prod Rep_mbuf_t Rep_mbuf_t"

fun rbufS :: "uebuf2S \<Rightarrow> event_data mbuf2S" where
  "rbufS (xs, ys, ts, skew) = (Rep_mbuf_t xs, Rep_mbuf_t ys, Rep_mbuf_t ts, skew)"

abbreviation rbufo :: "utable mbuf_t \<times> utable option mbuf_t \<Rightarrow>
    event_data table list \<times> event_data table option list" where
  "rbufo \<equiv> map_prod Rep_mbuf_t Rep_mbuf_t"

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

end
(*>*)
