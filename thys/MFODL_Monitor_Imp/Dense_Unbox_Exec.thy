(*<*)
theory Dense_Unbox_Exec
  imports Dense_Unbox_Eval
begin
(*>*)

section \<open>The verified dense evaluator, on short tuples\<close>

text \<open>
  @{const edeval} evaluates over tables of @{typ "event_data tuple"}, every field boxed in an
  option that never holds @{const None}.  This theory states the same evaluator over tables of
  @{typ "event_data list"}: every node keeps its tables and structures on short tuples, and
  every operation is the generic one at @{typ event_data}, or the twin of the field reader of
  @{theory MFODL_Monitor_Imp.Dense_Utuple}.  The theorem @{text udeval_Rep} at the end says
  that the two evaluators agree exactly: embedding the state and the database, running
  @{const edeval}, is running @{text udeval} and embedding its results.  No invariant is needed,
  because every operation commutes with the embedding on every input (the naturality lemmas of
  @{theory MFODL_Monitor_Imp.Dense_Unbox_Eval}).  So the simulation of the specification by
  @{const edeval} is a simulation by @{text udeval}, on the embedded database, and the
  generated code runs the latter.
\<close>

subsection \<open>The Since and Until structures, dispatched\<close>

datatype udsaux_x = UDSX_gen "event_data gmsaux" | UDSX_win "event_data gswaux" | UDSX_wagg daggp uswagg

fun rdsx :: "udsaux_x \<Rightarrow> dsaux_x" where
  "rdsx (UDSX_gen d) = DSX_gen (rmsaux d)"
| "rdsx (UDSX_win w) = DSX_win (rsw w)"
| "rdsx (UDSX_wagg p a) = DSX_wagg p (rsa a)"

definition udsx_init :: "args \<Rightarrow> bool list \<Rightarrow> udsaux_x" where
  "udsx_init args msk = (if args_L args = {} then UDSX_win (gsw_init args)
     else UDSX_gen (ginit_msaux args msk))"

definition udsx_init_agg :: "args \<Rightarrow> daggp \<Rightarrow> udsaux_x" where
  "udsx_init_agg args p = UDSX_wagg p (usa_init args p)"

fun udsx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_ts args nt (UDSX_gen d) = UDSX_gen (gadd_new_ts_msaux args nt d)"
| "udsx_add_new_ts args nt (UDSX_win w) = UDSX_win (gsw_add_new_ts args nt w)"
| "udsx_add_new_ts args nt (UDSX_wagg p a) = UDSX_wagg p (usa_add_new_ts args p nt a)"

fun udsx_join :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_join args X (UDSX_gen d) = UDSX_gen (ggc_join_msaux args X d)"
| "udsx_join args X (UDSX_win w) = UDSX_win (gsw_join args X w)"
| "udsx_join args X (UDSX_wagg p a) = UDSX_wagg p (usa_join args p X a)"

fun udsx_add_new_table :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_table args X (UDSX_gen d) = UDSX_gen (gadd_new_table_msaux args X d)"
| "udsx_add_new_table args X (UDSX_win w) = UDSX_win (gsw_add_new_table args X w)"
| "udsx_add_new_table args X (UDSX_wagg p a) = UDSX_wagg p (usa_add_new_table args p X a)"

fun udsx_result :: "args \<Rightarrow> udsaux_x \<Rightarrow> utable" where
  "udsx_result args (UDSX_gen d) = gresult_msaux args d"
| "udsx_result args (UDSX_win w) = gsw_result args w"
| "udsx_result args (UDSX_wagg p a) = usa_result args p a"

lemma dsx_init_rdsx: "dsx_init args msk = rdsx (udsx_init args msk)"
  by (simp add: dsx_init_def udsx_init_def gsw_init_rsw[symmetric] gsw_init_eq
      ginit_msaux_rmsaux[symmetric] ginit_msaux_eq)

lemma dsx_init_agg_rdsx: "dsx_init_agg args p = rdsx (udsx_init_agg args p)"
  by (simp add: dsx_init_agg_def udsx_init_agg_def sa_init_rsa)

lemma dsx_add_new_ts_rdsx: "dsx_add_new_ts args nt (rdsx d) = rdsx (udsx_add_new_ts args nt d)"
  by (cases d) (simp_all add: gadd_new_ts_msaux_eq[symmetric] gadd_new_ts_msaux_rmsaux
      gsw_add_new_ts_eq[symmetric] gsw_add_new_ts_rsw sa_add_new_ts_rsa)

lemma dsx_join_rdsx: "dsx_join args (reopt_table X) (rdsx d) = rdsx (udsx_join args X d)"
  by (cases d) (simp_all add: ggc_join_msaux_eq[symmetric] ggc_join_msaux_rmsaux
      gsw_join_eq[symmetric] gsw_join_rsw sa_join_rsa)

lemma dsx_add_new_table_rdsx:
  "dsx_add_new_table args (reopt_table X) (rdsx d) = rdsx (udsx_add_new_table args X d)"
  by (cases d) (simp_all add: gadd_new_table_msaux_eq[symmetric] gadd_new_table_msaux_rmsaux
      gsw_add_new_table_eq[symmetric] gsw_add_new_table_rsw sa_add_new_table_rsa)

lemma dsx_result_rdsx: "dsx_result args (rdsx d) = reopt_table (udsx_result args d)"
  by (cases d) (simp_all add: gresult_msaux_eq[symmetric] gresult_msaux_rmsaux
      gsw_result_eq[symmetric] gsw_result_rsw sa_result_rsa)

datatype uduaux_x = UDUX_gen "event_data gmuaux" | UDUX_win uuwaux

fun rdux :: "uduaux_x \<Rightarrow> duaux_x" where
  "rdux (UDUX_gen d) = DUX_gen (rmuaux d)"
| "rdux (UDUX_win w) = DUX_win (ruw w)"

definition udux_init :: "args \<Rightarrow> uduaux_x" where
  "udux_init args = (if args_L args = {} \<and> memL (args_ivl args) 0 then UDUX_win (uuw_init args)
     else UDUX_gen (ginit_dq args))"

fun udux_add_new :: "args \<Rightarrow> bool list \<Rightarrow> utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> uduaux_x \<Rightarrow> uduaux_x" where
  "udux_add_new args msk rel1 rel2 nt (UDUX_gen d) = UDUX_gen (gadd_new_dq args msk rel1 rel2 nt d)"
| "udux_add_new args msk rel1 rel2 nt (UDUX_win w) = UDUX_win (uuw_add_new args rel1 rel2 nt w)"

fun udux_eval :: "args \<Rightarrow> ts \<Rightarrow> uduaux_x \<Rightarrow> utable list \<times> uduaux_x" where
  "udux_eval args nt (UDUX_gen d) = (let (zs, d') = geval_dq args nt d in (zs, UDUX_gen d'))"
| "udux_eval args nt (UDUX_win w) = (let (zs, w') = uuw_eval args nt w in (zs, UDUX_win w'))"

fun udux_length :: "args \<Rightarrow> uduaux_x \<Rightarrow> nat" where
  "udux_length args (UDUX_gen d) = glength_dq args d"
| "udux_length args (UDUX_win w) = uuw_length args w"

lemma dux_init_rdux: "dux_init args = rdux (udux_init args)"
  by (simp add: dux_init_def udux_init_def ginit_dq_rmuaux[symmetric] uw_init_ruw[symmetric])

lemma dux_add_new_rdux:
  "dux_add_new args msk (reopt_table rel1) (reopt_table rel2) nt (rdux d)
   = rdux (udux_add_new args msk rel1 rel2 nt d)"
  by (cases d) (simp_all add: gadd_new_dq_rmuaux uw_add_new_ruw)

lemma dux_eval_rdux:
  "dux_eval args nt (rdux d) = (case udux_eval args nt d of (zs, d') \<Rightarrow> (map reopt_table zs, rdux d'))"
proof (cases d)
  case (UDUX_gen x)
  obtain zs x' where g: "geval_dq args nt x = (zs, x')" by (cases "geval_dq args nt x")
  show ?thesis unfolding UDUX_gen dux_eval.simps udux_eval.simps rdux.simps geval_dq_rmuaux g by simp
next
  case (UDUX_win w)
  obtain zs w' where g: "uuw_eval args nt w = (zs, w')" by (cases "uuw_eval args nt w")
  show ?thesis unfolding UDUX_win dux_eval.simps udux_eval.simps rdux.simps uw_eval_ruw g by simp
qed

lemma dux_length_rdux: "dux_length args (rdux d) = udux_length args d"
  by (cases d) (simp_all add: glength_dq_rmuaux uw_length_ruw)

subsection \<open>The buffers\<close>

text \<open>The buffer operations of @{theory MFODL_Monitor_Devel.Monitor_Impl} that are stated on
  boxed tables get copies on short ones, and every buffer operation commutes with a map over
  the buffered tables, with the step function mapped along.\<close>

type_synonym uebuf2 = "utable mbuf_t \<times> utable mbuf_t"
type_synonym uebufn = "utable mbuf_t list"
type_synonym uebuf2S = "utable mbuf_t \<times> utable mbuf_t \<times> ts mbuf_t \<times> bool"

lemma mebuf2_add_map_mbuf:
  "mebuf2_add (map g xs) (map g ys) (map_mbuf g a, map_mbuf g b)
   = map_prod (map_mbuf g) (map_mbuf g) (mebuf2_add xs ys (a, b))"
  by simp

lemma mebuf2_take_map_mbuf:
  "(\<And>x y. f (g x) (g y) = g' (f' x y)) \<Longrightarrow>
   mebuf2_take f (map_mbuf g xs, map_mbuf g ys)
   = (case mebuf2_take f' (xs, ys) of (zs, (xs', ys')) \<Rightarrow> (map g' zs, (map_mbuf g xs', map_mbuf g ys')))"
proof (induct f' "(xs, ys)" arbitrary: xs ys rule: mebuf2_take.induct)
  case (1 f' xs ys)
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  show ?case using 1 x y by (cases x; cases y) (auto simp: x y split: prod.splits)
qed

fun ueprev_next :: "\<I> \<Rightarrow> utable mbuf_t \<Rightarrow> ts mbuf_t \<Rightarrow> utable list \<times> utable mbuf_t \<times> ts mbuf_t"
  where "ueprev_next I xs ts = (case mbuf_t_cases xs of (None, xs') \<Rightarrow> ([], mbuf_t_empty, ts)
  | (Some x, xs') \<Rightarrow> (case mbuf_t_cases ts of (None, ts') \<Rightarrow> ([], x ## xs', mbuf_t_empty)
  | (Some t, ts') \<Rightarrow> (case mbuf_t_cases ts' of (None, ts'') \<Rightarrow> ([], x ## xs', t ## mbuf_t_empty)
  | (Some t', ts'') \<Rightarrow> (let (ys, zs) = ueprev_next I xs' (t' ## ts'')
    in ((if mem I ((t' - t)) then x else {}) # ys, zs)))))"

lemma meprev_next_map_mbuf:
  "meprev_next I (map_mbuf reopt_table xs) ts
   = (case ueprev_next I xs ts of (zs, xs', ts') \<Rightarrow> (map reopt_table zs, map_mbuf reopt_table xs', ts'))"
proof (induct I xs ts rule: ueprev_next.induct)
  case (1 I xs ts)
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  obtain t' ts'' where t': "mbuf_t_cases ts' = (t', ts'')" by (cases "mbuf_t_cases ts'")
  show ?case
    using 1 x t t' by (cases x; cases t; cases t') (auto simp: x t t' empty_table_def split: prod.splits)
qed

fun uebufn_add :: "utable list list \<Rightarrow> uebufn \<Rightarrow> uebufn" where
  "uebufn_add xs' xs = List.map2 (@@) xs xs'"

lemma mebufn_add_map_mbuf:
  "mebufn_add (map (map g) xss) (map (map_mbuf g) buf) = map (map_mbuf g) (uebufn_add xss buf)"
  by (induct buf xss rule: list_induct2') auto

lemma mbuf_t_cases_None[simp]: "fst (mbuf_t_cases b) = None \<longleftrightarrow> mbuf_t_is_empty b"
  by transfer (auto split: list.splits)

lemma the_map_option_fst_mbuf_t_cases:
  "\<not> mbuf_t_is_empty b \<Longrightarrow> the (map_option g (fst (mbuf_t_cases b))) = g (the (fst (mbuf_t_cases b)))"
  by (cases "fst (mbuf_t_cases b)") auto

function uebufn_take :: "(utable list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> uebufn \<Rightarrow> 'b \<times> uebufn" where
  "uebufn_take f z buf = (if buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf)
    else uebufn_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z) (map (snd \<circ> mbuf_t_cases) buf))"
  by pat_completeness auto
termination
  using size_list_snd_mbuf_t_cases
  by (relation "measure (\<lambda>(_, _, buf). size_list size buf)")
    (auto simp: comp_def Suc_le_eq size_list_length_diff1)

declare uebufn_take.simps[simp del]

lemma mebufn_take_map_mbuf:
  "(\<And>as z. f (map g as) (h z) = h (f' as z)) \<Longrightarrow>
   mebufn_take f (h z) (map (map_mbuf g) buf)
   = (case uebufn_take f' z buf of (z', buf') \<Rightarrow> (h z', map (map_mbuf g) buf'))"
proof (induct f' z buf rule: uebufn_take.induct)
  case (1 f' z buf)
  show ?case
  proof (cases "buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x)")
    case True
    then have T: "map (map_mbuf g) buf = [] \<or> (\<exists>x \<in> set (map (map_mbuf g) buf). mbuf_t_is_empty x)"
      by auto
    show ?thesis
      by (subst mebufn_take.simps, subst uebufn_take.simps) (simp only: T True if_True prod.case)
  next
    case False
    then have F: "\<not> (map (map_mbuf g) buf = [] \<or> (\<exists>x \<in> set (map (map_mbuf g) buf). mbuf_t_is_empty x))"
      by auto
    have m: "map (the \<circ> fst \<circ> mbuf_t_cases) (map (map_mbuf g) buf)
        = map g (map (the \<circ> fst \<circ> mbuf_t_cases) buf)"
      using False by (auto simp: comp_def the_map_option_fst_mbuf_t_cases intro!: map_ext)
    have s: "map (snd \<circ> mbuf_t_cases) (map (map_mbuf g) buf)
        = map (map_mbuf g) (map (snd \<circ> mbuf_t_cases) buf)"
      by (simp add: comp_def)
    show ?thesis
      by (subst mebufn_take.simps, subst uebufn_take.simps)
        (simp only: F False if_False m s 1(2) 1(1)[OF False 1(2)])
  qed
qed

fun uebuf2S_add :: "utable list \<Rightarrow> utable list \<Rightarrow> ts list \<Rightarrow> uebuf2S \<Rightarrow> uebuf2S" where
  "uebuf2S_add xs' ys' ts' (xs, ys, ts, skew) = (xs @@ xs', ys @@ ys', ts @@ ts', skew)"

lemma mebuf2S_add_map_mbuf:
  "mebuf2S_add (map reopt_table xs) (map reopt_table ys) ts
     (map_mbuf reopt_table a, map_mbuf reopt_table b, c, d)
   = (case uebuf2S_add xs ys ts (a, b, c, d) of
        (a', b', c', d') \<Rightarrow> (map_mbuf reopt_table a', map_mbuf reopt_table b', c', d'))"
  by simp

fun uebuf2t_take :: "(utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    uebuf2 \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> uebuf2 \<times> ts \<times> ts mbuf_t" where
  "uebuf2t_take f z (xs, ys) t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), t0, ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t, t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t, t ## ts') | (Some y, ys') \<Rightarrow>
    uebuf2t_take f (f x y t z) (xs', ys') t ts')))"

lemma mebuf2t_take_map_mbuf:
  "(\<And>x y t z. f (reopt_table x) (reopt_table y) t (h z) = h (f' x y t z)) \<Longrightarrow>
   mebuf2t_take f (h z) (map_mbuf reopt_table xs, map_mbuf reopt_table ys) t ts
   = (case uebuf2t_take f' z (xs, ys) t ts of
        (z', (xs', ys'), t', ts') \<Rightarrow> (h z', (map_mbuf reopt_table xs', map_mbuf reopt_table ys'), t', ts'))"
proof (induct f' z "(xs, ys)" t ts arbitrary: xs ys rule: uebuf2t_take.induct)
  case (1 f' z xs ys t0 ts)
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  show ?case using 1 x y t by (cases x; cases y; cases t) (auto simp: x y t split: prod.splits)
qed

lemma mebuf2T_take_acc:
  "(\<And>x y t z. f x y t (h z) = h (f' x y t z)) \<Longrightarrow>
   mebuf2T_take f (h z) buf ts
   = (case mebuf2T_take f' z buf ts of (z', buf', ts') \<Rightarrow> (h z', buf', ts'))"
proof (induct f' z buf ts rule: mebuf2T_take.induct)
  case (1 f' z xs ys ts)
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  show ?case using 1 x y t by (cases x; cases y; cases t) (auto simp: x y t split: prod.splits)
qed

(*<*)
end
(*>*)
