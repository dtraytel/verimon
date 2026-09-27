(*<*)
theory Dense_Unbox_Exec
  imports Dense_Agg_Cache Dense_Descend_Code
begin
(*>*)

section \<open>The verified dense evaluator, on short tuples\<close>

text \<open>
  @{const edeval} evaluates over tables of @{typ "event_data tuple"}, every field boxed in an
  option that never holds @{const None}.  This theory states the same evaluator over tables of
  @{typ "event_data list"}: every node keeps its tables and structures on short tuples, and
  every operation is the generic one at @{typ event_data}, or the twin of the field reader of
  @{theory MFODL_Monitor_Dense.Dense_Utuple}.  The theorem @{text udeval_Rep} at the end says
  that the two evaluators agree exactly: embedding the state and the database, running
  @{const edeval}, is running @{text udeval} and embedding its results.  No invariant is needed,
  because every operation commutes with the embedding on every input (the naturality lemmas of
  @{theory MFODL_Monitor_Dense.Dense_Unbox_Eval}).  So the simulation of the specification by
  @{const edeval} is a simulation by @{text udeval}, on the embedded database, and the
  generated code runs the latter.
\<close>

subsection \<open>The Since and Until structures, dispatched\<close>

text \<open>The structure of a fused aggregating window carries the node's guard: the constraint the
  node's own result is read through, if it has one (@{theory MFODL_Monitor_Dense.Dense_Unbox_Eval}).
  Only the read looks at it; every other operation passes it along, and the boxed structure it
  stands for does not have it at all -- there the constraint stays a filter over the node.\<close>

datatype udsaux_x = UDSX_gen "event_data gmsaux" | UDSX_win "event_data gswaux"
  | UDSX_wagg daggp "uconstr option" uswaggc

fun rdsx :: "udsaux_x \<Rightarrow> dsaux_x" where
  "rdsx (UDSX_gen d) = DSX_gen (rmsaux d)"
| "rdsx (UDSX_win w) = DSX_win (rsw w)"
| "rdsx (UDSX_wagg p q a) = DSX_wagg p (rsa (ucs a))"

fun usx_q :: "udsaux_x \<Rightarrow> uconstr option" where
  "usx_q (UDSX_wagg p q a) = q"
| "usx_q _ = None"

definition udsx_init :: "args \<Rightarrow> bool list \<Rightarrow> udsaux_x" where
  "udsx_init args msk = (if args_L args = {} then UDSX_win (gsw_init args)
     else UDSX_gen (ginit_msaux args msk))"

definition udsx_init_agg :: "args \<Rightarrow> daggp \<Rightarrow> uconstr option \<Rightarrow> udsaux_x" where
  "udsx_init_agg args p q = UDSX_wagg p q (usc_init args p q)"

fun udsx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_ts args nt (UDSX_gen d) = UDSX_gen (gadd_new_ts_msaux args nt d)"
| "udsx_add_new_ts args nt (UDSX_win w) = UDSX_win (gsw_add_new_ts args nt w)"
| "udsx_add_new_ts args nt (UDSX_wagg p q a) = UDSX_wagg p q (usc_add_new_ts args p q nt a)"

fun udsx_join :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_join args X (UDSX_gen d) = UDSX_gen (ggc_join_msaux args X d)"
| "udsx_join args X (UDSX_win w) = UDSX_win (gsw_join args X w)"
| "udsx_join args X (UDSX_wagg p q a) = UDSX_wagg p q (usc_join args p q X a)"

fun udsx_add_new_table :: "args \<Rightarrow> utable \<Rightarrow> udsaux_x \<Rightarrow> udsaux_x" where
  "udsx_add_new_table args X (UDSX_gen d) = UDSX_gen (gadd_new_table_msaux args X d)"
| "udsx_add_new_table args X (UDSX_win w) = UDSX_win (gsw_add_new_table args X w)"
| "udsx_add_new_table args X (UDSX_wagg p q a) = UDSX_wagg p q (usc_add_new_table args p q X a)"

fun udsx_result :: "args \<Rightarrow> udsaux_x \<Rightarrow> utable" where
  "udsx_result args (UDSX_gen d) = gresult_msaux args d"
| "udsx_result args (UDSX_win w) = gsw_result args w"
| "udsx_result args (UDSX_wagg p q a) = usc_result q args p a"

lemma usx_q_add_new_ts[simp]: "usx_q (udsx_add_new_ts args nt d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_join[simp]: "usx_q (udsx_join args X d) = usx_q d"
  by (cases d) simp_all

lemma usx_q_add_new_table[simp]: "usx_q (udsx_add_new_table args X d) = usx_q d"
  by (cases d) simp_all

lemma dsx_init_rdsx: "dsx_init args msk = rdsx (udsx_init args msk)"
  by (simp add: dsx_init_def udsx_init_def gsw_init_rsw[symmetric] gsw_init_eq
      ginit_msaux_rmsaux[symmetric] ginit_msaux_eq)

lemma dsx_init_agg_rdsx[simp]: "rdsx (udsx_init_agg args p q) = dsx_init_agg args p"
  by (simp add: dsx_init_agg_def udsx_init_agg_def sa_init_rsa usc_init_ucs)

lemma usx_q_init_agg[simp]: "usx_q (udsx_init_agg args p q) = q"
  by (simp add: udsx_init_agg_def)

lemma usx_q_init[simp]: "usx_q (udsx_init args msk) = None"
  by (simp add: udsx_init_def)

lemma dsx_add_new_ts_rdsx: "dsx_add_new_ts args nt (rdsx d) = rdsx (udsx_add_new_ts args nt d)"
  by (cases d) (simp_all add: gadd_new_ts_msaux_eq[symmetric] gadd_new_ts_msaux_rmsaux
      gsw_add_new_ts_eq[symmetric] gsw_add_new_ts_rsw sa_add_new_ts_rsa usc_add_new_ts_ucs)

lemma dsx_join_rdsx: "dsx_join args (reopt_table X) (rdsx d) = rdsx (udsx_join args X d)"
  by (cases d) (simp_all add: ggc_join_msaux_eq[symmetric] ggc_join_msaux_rmsaux
      gsw_join_eq[symmetric] gsw_join_rsw sa_join_rsa usc_join_ucs)

lemma dsx_add_new_table_rdsx:
  "dsx_add_new_table args (reopt_table X) (rdsx d) = rdsx (udsx_add_new_table args X d)"
  by (cases d) (simp_all add: gadd_new_table_msaux_eq[symmetric] gadd_new_table_msaux_rmsaux
      gsw_add_new_table_eq[symmetric] gsw_add_new_table_rsw sa_add_new_table_rsa usc_add_new_table_ucs)

text \<open>The boxed structure reports the node's whole result and the node filters it; the short
  one reports the filtered result straight away.\<close>

lemma dsx_result_rdsx:
  "usx_q d = q \<Longrightarrow> dfilt q (dsx_result args (rdsx d)) = reopt_table (udsx_result args d)"
  by (cases d) (simp_all add: gresult_msaux_eq[symmetric] gresult_msaux_rmsaux
      gsw_result_eq[symmetric] gsw_result_rsw sa_result_rsa usc_result_ucs)

datatype uduaux_x = UDUX_gen "event_data gmuaux" | UDUX_win uuwaux | UDUX_wagg daggp uuwagg

fun rdux :: "uduaux_x \<Rightarrow> duaux_x" where
  "rdux (UDUX_gen d) = DUX_gen (rmuaux d)"
| "rdux (UDUX_win w) = DUX_win (ruw w)"
| "rdux (UDUX_wagg p a) = DUX_wagg p (rua a)"

definition udux_init :: "args \<Rightarrow> uduaux_x" where
  "udux_init args = (if args_L args = {} \<and> memL (args_ivl args) 0 then UDUX_win (uuw_init args)
     else UDUX_gen (ginit_dq args))"

definition udux_init_agg :: "args \<Rightarrow> daggp \<Rightarrow> uduaux_x" where
  "udux_init_agg args p = UDUX_wagg p (uua_init args p)"

fun udux_add_new :: "args \<Rightarrow> bool list \<Rightarrow> utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> uduaux_x \<Rightarrow> uduaux_x" where
  "udux_add_new args msk rel1 rel2 nt (UDUX_gen d) = UDUX_gen (gadd_new_dq args msk rel1 rel2 nt d)"
| "udux_add_new args msk rel1 rel2 nt (UDUX_win w) = UDUX_win (uuw_add_new args rel1 rel2 nt w)"
| "udux_add_new args msk rel1 rel2 nt (UDUX_wagg p a) =
     UDUX_wagg p (uua_add_new args p (args_n args) rel1 rel2 nt a)"

fun udux_eval :: "args \<Rightarrow> ts \<Rightarrow> uduaux_x \<Rightarrow> utable list \<times> uduaux_x" where
  "udux_eval args nt (UDUX_gen d) = (let (zs, d') = geval_dq args nt d in (zs, UDUX_gen d'))"
| "udux_eval args nt (UDUX_win w) = (let (zs, w') = uuw_eval args nt w in (zs, UDUX_win w'))"
| "udux_eval args nt (UDUX_wagg p a) =
     (let (zs, a') = uua_eval args p (args_n args) nt a in (zs, UDUX_wagg p a'))"

fun udux_length :: "args \<Rightarrow> uduaux_x \<Rightarrow> nat" where
  "udux_length args (UDUX_gen d) = glength_dq args d"
| "udux_length args (UDUX_win w) = uuw_length args w"
| "udux_length args (UDUX_wagg p a) = uua_length args a"

lemma dux_init_rdux: "dux_init args = rdux (udux_init args)"
  by (simp add: dux_init_def udux_init_def ginit_dq_rmuaux[symmetric] uw_init_ruw[symmetric])

lemma dux_init_agg_rdux: "dux_init_agg args p = rdux (udux_init_agg args p)"
  by (simp add: dux_init_agg_def udux_init_agg_def rdux.simps rua_init)

lemma dux_add_new_rdux:
  "dux_add_new args msk (reopt_table rel1) (reopt_table rel2) nt (rdux d)
   = rdux (udux_add_new args msk rel1 rel2 nt d)"
  by (cases d) (simp_all add: gadd_new_dq_rmuaux uw_add_new_ruw ua_add_new_rua rdux.simps)

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
next
  case (UDUX_wagg p a)
  obtain zs a' where g: "uua_eval args p (args_n args) nt a = (zs, a')"
    by (cases "uua_eval args p (args_n args) nt a")
  show ?thesis
    unfolding UDUX_wagg dux_eval.simps udux_eval.simps rdux.simps ua_eval_rua g by simp
qed

lemma dux_length_rdux: "dux_length args (rdux d) = udux_length args d"
  by (cases d)
    (simp_all add: glength_dq_rmuaux uw_length_ruw rdux.simps rua.simps
      ua_length_def uua_length_def uuwm_length_ucc)

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

text \<open>The same traversal with the time stamps alongside, which the match nodes step.\<close>

fun uebufnt_take :: "(utable list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> uebufn \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> uebufn \<times> ts \<times> ts mbuf_t" where
  "uebufnt_take f z buf t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, buf, t0, ts) | (Some t, ts') \<Rightarrow>
    (if (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf, t, mbuf_t_Cons t ts')
    else uebufnt_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) t z)
      (map (snd \<circ> mbuf_t_cases) buf) t ts'))"

lemma mebufnt_take_map_mbuf:
  "(\<And>as t z. f (map g as) t (h z) = h (f' as t z)) \<Longrightarrow>
   mebufnt_take f (h z) (map (map_mbuf g) buf) t0 ts
   = (case uebufnt_take f' z buf t0 ts of
        (z', buf', t', ts') \<Rightarrow> (h z', map (map_mbuf g) buf', t', ts'))"
proof (induct f' z buf t0 ts rule: uebufnt_take.induct)
  case (1 f' z buf t0 ts)
  obtain to ts'' where T: "mbuf_t_cases ts = (to, ts'')" by fastforce
  have m: "\<forall>x \<in> set buf. \<not> mbuf_t_is_empty x \<Longrightarrow>
      map (\<lambda>x. the (map_option g (fst (mbuf_t_cases x)))) buf
        = map g (map (\<lambda>x. the (fst (mbuf_t_cases x))) buf)"
    by (auto simp: the_map_option_fst_mbuf_t_cases intro!: map_ext)
  show ?case
  proof (cases to)
    case None
    then show ?thesis
      unfolding uebufnt_take.simps[of _ _ buf] mebufnt_take.simps[of _ _ "map (map_mbuf g) buf"]
      by (simp add: T)
  next
    case (Some a)
    show ?thesis
    proof (cases "\<exists>x \<in> set buf. mbuf_t_is_empty x")
      case True
      then show ?thesis
        unfolding uebufnt_take.simps[of _ _ buf] mebufnt_take.simps[of _ _ "map (map_mbuf g) buf"]
        by (simp add: T Some)
    next
      case False
      then have ne: "\<forall>x \<in> set buf. \<not> mbuf_t_is_empty x" by simp
      have S: "f (map (\<lambda>x. g (the (fst (mbuf_t_cases x)))) buf) a (h z)
          = h (f' (map (\<lambda>x. the (fst (mbuf_t_cases x))) buf) a z)"
        using 1(2)[of "map (\<lambda>x. the (fst (mbuf_t_cases x))) buf" a z] by (simp add: comp_def)
      show ?thesis
        using 1(1)[OF T[symmetric] Some False 1(2)]
        unfolding uebufnt_take.simps[of _ _ buf] mebufnt_take.simps[of _ _ "map (map_mbuf g) buf"]
        by (simp add: T Some comp_def m[OF ne] S
            del: mebufnt_take.simps uebufnt_take.simps)
    qed
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

text \<open>The buffer traversal the trigger node runs, at the short tables: the same scan as
  @{const mebuf2T_take}, and natural in the relabelling of both the buffer and the accumulator.\<close>

fun uebuf2T_take :: "(utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    uebuf2 \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> uebuf2 \<times> ts mbuf_t" where
  "uebuf2T_take f z (xs, ys) ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t ## ts') | (Some y, ys') \<Rightarrow>
    uebuf2T_take f (f x y t z) (xs', ys') ts')))"

lemma mebuf2T_take_map_mbuf:
  "(\<And>x y t z. f (reopt_table x) (reopt_table y) t (h z) = h (f' x y t z)) \<Longrightarrow>
   mebuf2T_take f (h z) (map_mbuf reopt_table xs, map_mbuf reopt_table ys) ts
   = (case uebuf2T_take f' z (xs, ys) ts of
        (z', (xs', ys'), ts') \<Rightarrow>
          (h z', (map_mbuf reopt_table xs', map_mbuf reopt_table ys'), ts'))"
proof (induct f' z "(xs, ys)" ts arbitrary: xs ys rule: uebuf2T_take.induct)
  case (1 f' z xs ys ts)
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  show ?case using 1 x y t by (cases x; cases y; cases t) (auto simp: x y t split: prod.splits)
qed

lemma mebuf2_add_rbuf:
  "mebuf2_add (map reopt_table xs) (map reopt_table ys) (map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) buf)
   = map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) (mebuf2_add xs ys buf)"
  by (cases buf) simp

lemma mebuf2_take_rbuf:
  assumes "\<And>x y. f (reopt_table x) (reopt_table y) = reopt_table (f' x y)"
  shows "mebuf2_take f (map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) (buf :: uebuf2))
   = (case mebuf2_take f' buf of
        (zs, buf') \<Rightarrow> (map reopt_table zs, map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) buf'))"
  by (cases buf)
    (simp add: mebuf2_take_map_mbuf[where f = f and g = reopt_table and g' = reopt_table and f' = f',
       OF assms] split: prod.splits del: mebuf2_take.simps)

fun rbufS :: "uebuf2S \<Rightarrow> event_data mebuf2S" where
  "rbufS (a, b, c, d) = (map_mbuf reopt_table a, map_mbuf reopt_table b, c, d)"

lemma mebuf2S_add_rbufS:
  "mebuf2S_add (map reopt_table xs) (map reopt_table ys) ts (rbufS buf) = rbufS (uebuf2S_add xs ys ts buf)"
  by (cases buf) simp

lemma mebuf2t_take_rbuf:
  assumes "\<And>x y t z. f (reopt_table x) (reopt_table y) t (h z) = h (f' x y t z)"
  shows "mebuf2t_take f (h z) (map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) buf) t ts
   = (case uebuf2t_take f' z buf t ts of
        (z', buf', t', ts') \<Rightarrow> (h z', map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) buf', t', ts'))"
  by (cases buf)
    (simp add: mebuf2t_take_map_mbuf[where f = f and h = h and f' = f', OF assms] split: prod.splits
       del: mebuf2t_take.simps uebuf2t_take.simps)

subsection \<open>The join\<close>

abbreviation rmkl :: "(event_data list, event_data list list) mapping \<Rightarrow>
    (event_data tuple, event_data tuple list) mapping" where
  "rmkl \<equiv> rmk (map reopt)"

lemma rmk_update_single[simp]:
  "Mapping.update (reopt k) [reopt b] (rmkl m) = rmkl (Mapping.update k [b] m)"
  using rmk_update[of k "map reopt" "[b]" m] by simp

lemma rmk_update_Cons[simp]:
  "Mapping.update (reopt k) (reopt b # map reopt l) (rmkl m) = rmkl (Mapping.update k (b # l) m)"
  using rmk_update[of k "map reopt" "b # l" m] by simp

lemma gindex_step_rmkl: "gindex_step msk (reopt b) (rmkl m) = rmkl (gindex_step msk b m)"
  by (simp add: gindex_step_def Let_def split: option.splits)

lemma fold_gindex_step_rmkl:
  "fold (gindex_step msk) (map reopt xs) (rmkl m) = rmkl (fold (gindex_step msk) xs m)"
  by (induct xs arbitrary: m) (simp_all add: gindex_step_rmkl)

lemma gindex_reopt_table: "gindex msk (reopt_table B) = rmkl (gindex msk B)"
  by (simp add: gindex_def csl_reopt_table fold_gindex_step_rmkl[where m = Mapping.empty, simplified])

lemma fold_insert_dmerge_l:
  "fold (\<lambda>b acc. Set.insert (dmerge p (reopt a) b) acc) (map reopt l) (reopt_table acc)
   = reopt_table (fold (\<lambda>b acc. Set.insert (dmerge p a b) acc) l acc)"
  by (induct l arbitrary: acc) simp_all

lemma fold_insert_dmerge_r:
  "fold (\<lambda>x acc. Set.insert (dmerge p x (reopt y)) acc) (map reopt l) (reopt_table acc)
   = reopt_table (fold (\<lambda>x acc. Set.insert (dmerge p x y) acc) l acc)"
  by (induct l arbitrary: acc) simp_all

lemma gprobe_step_rmkl:
  "gprobe_step p msk (rmkl m) (reopt a) (reopt_table acc) = reopt_table (gprobe_step p msk m a acc)"
  by (simp add: gprobe_step_def fold_insert_dmerge_l split: option.splits)

lemma gprobe_step_l_rmkl:
  "gprobe_step_l p rk (rmkl m) (reopt y) (reopt_table acc) = reopt_table (gprobe_step_l p rk m y acc)"
  by (simp add: gprobe_step_l_def fold_insert_dmerge_r split: option.splits)

lemma fold_gprobe_step_rmkl:
  "fold (gprobe_step p msk (rmkl m)) (map reopt xs) (reopt_table acc)
   = reopt_table (fold (gprobe_step p msk m) xs acc)"
  by (induct xs arbitrary: acc) (simp_all add: gprobe_step_rmkl)

lemma fold_gprobe_step_l_rmkl:
  "fold (gprobe_step_l p rk (rmkl m)) (map reopt xs) (reopt_table acc)
   = reopt_table (fold (gprobe_step_l p rk m) xs acc)"
  by (induct xs arbitrary: acc) (simp_all add: gprobe_step_l_rmkl)

lemma ggen_join_reopt_table:
  "ggen_join p lk rk (reopt_table (A :: utable)) (reopt_table B) = reopt_table (ggen_join p lk rk A B)"
  by (simp add: ggen_join_def Let_def csl_reopt_table gindex_reopt_table
      fold_gprobe_step_rmkl[where acc = "{}", simplified]
      fold_gprobe_step_l_rmkl[where acc = "{}", simplified])

lemma filter_dproj_reopt_table:
  "Set.filter (\<lambda>b. dproj msk b \<in> reopt_table A) (reopt_table B)
   = reopt_table (Set.filter (\<lambda>b. dproj msk b \<in> A) B)"
  "{b \<in> reopt_table B. dproj msk b \<in> reopt_table A} = reopt_table {b \<in> B. dproj msk b \<in> A}"
  by (auto simp: reopt_table_def image_iff inj_reopt inj_image_mem_iff)

lemma gbin_join0_reopt_table:
  "gbin_join0 pl (reopt_table (A :: utable)) pos (reopt_table B) = reopt_table (gbin_join0 pl A pos B)"
  by (cases pl) (simp_all add: ggen_join_reopt_table filter_dproj_reopt_table)

lemma gbin_join_reopt_table:
  "gbin_join pl (reopt_table (A :: utable)) pos (reopt_table B) = reopt_table (gbin_join pl A pos B)"
  by (simp add: gbin_join_def gbin_join0_reopt_table)

lemma gands_pos_reopt_table:
  "gands_pos ps (reopt_table (t :: utable)) (map reopt_table us) = reopt_table (gands_pos ps t us)"
  by (induct ps t us rule: gands_pos.induct) (simp_all add: gbin_join_reopt_table)

lemma gands_neg_reopt_table:
  "gands_neg ps (reopt_table (t :: utable)) (map reopt_table us) = reopt_table (gands_neg ps t us)"
  by (induct ps t us rule: gands_neg.induct) (simp_all add: gbin_join_reopt_table)

lemma gmulti_join_reopt_table:
  "gmulti_join ps ns (map reopt_table (us :: utable list)) = reopt_table (gmulti_join ps ns us)"
  by (simp add: gmulti_join_def gands_pos_reopt_table gands_neg_reopt_table take_map drop_map
      split: list.splits)

lemma dbin_join_reopt_table:
  "dbin_join pl (reopt_table A) pos (reopt_table B) = reopt_table (gbin_join pl A pos B)"
  by (simp add: gbin_join_eq[symmetric] gbin_join_reopt_table)

lemma dmulti_join_reopt_table:
  "dmulti_join ps ns (map reopt_table us) = reopt_table (gmulti_join ps ns us)"
  by (simp add: gmulti_join_eq[symmetric] gmulti_join_reopt_table)

subsection \<open>The node operations\<close>

lemma dmatch_table_reopt_table:
  "dmatch_table tms cs (reopt_table X) = reopt_table (umatch_table tms cs X)"
  by (simp add: dmatch_table_def)

lemma dagg_reopt_table: "dagg g0 \<omega> f k pos (reopt_table X) = reopt_table (uagg g0 \<omega> f k pos X)"
  by (simp add: dagg_def)

lemma dassign_reopt_table: "dassign p t (reopt_table X) = reopt_table (uassign p t X)"
  by (simp add: dassign_def uassign_def dassign1_def reopt_table_def image_image)

lemma filter_deval_constraint_reopt_table:
  "Set.filter (deval_constraint conf) (reopt_table X) = reopt_table (Set.filter (ueval_constraint conf) X)"
  "{a \<in> reopt_table X. deval_constraint conf a} = reopt_table {a \<in> X. ueval_constraint conf a}"
  by (auto simp: reopt_table_def)

lemma dmtrm_umtrm: "dmtrm mt x = reopt_table (umtrm mt x)"
  by (cases mt) (simp_all add: reopt_table_def unit_table_def empty_table_def reopt_def)

lemma neg_reopt_table:
  "(if reopt_table r = empty_table then unit_table 0 else empty_table)
   = reopt_table (if r = {} then {[]} else {})"
  by (simp add: empty_table_def unit_table_def reopt_table_def reopt_def)

subsection \<open>The database\<close>

type_synonym udatabase = "(Formula.name \<times> nat, utable list) mapping"

definition rdb :: "udatabase \<Rightarrow> database" where
  "rdb = Mapping.map_values (\<lambda>_ xs. map reopt_table xs)"

lemma lookup_rdb[simp]:
  "Mapping.lookup (rdb db) k = map_option (map reopt_table) (Mapping.lookup db k)"
  by (simp add: rdb_def lookup_map_values)

lemma rdb_update[simp]: "Mapping.update k (map reopt_table xs) (rdb db) = rdb (Mapping.update k xs db)"
  by (simp add: rdb_def map_values_update)

lemma rdb_update_Nil[simp]: "Mapping.update k [] (rdb db) = rdb (Mapping.update k [] db)"
  using rdb_update[of k "[]"] by simp

lemma rdb_update_replicate[simp]:
  "Mapping.update k (replicate j (reopt_table \<alpha>)) (rdb db) = rdb (Mapping.update k (replicate j \<alpha>) db)"
  using rdb_update[of k "replicate j \<alpha>"] by simp

lemma rdb_update_replicate_empty[simp]:
  "Mapping.update k (replicate j {}) (rdb db) = rdb (Mapping.update k (replicate j {}) db)"
  using rdb_update_replicate[of k j "{}"] by (simp add: reopt_table_def)

lemma rdb_map_values_Nil[simp]:
  "Mapping.map_values (\<lambda>_ _. []) (rdb db) = rdb (Mapping.map_values (\<lambda>_ _. []) db)"
  by (auto simp: rdb_def lookup_map_values option.map_comp comp_def intro!: mapping_eqI)

subsection \<open>The recursive let operators\<close>

text \<open>The size guard of @{const letpast_meval0} never fires on either side: both evaluators
  return a formula of the size they were given, so the two runs take the same branch whatever
  the embedding does to the size.\<close>

lemma letpast_meval0_rdb:
  assumes sz': "\<And>ts db e. size (snd (eval ts db e)) = size e"
  shows "(\<And>ts db \<psi>. size (snd (eval' ts db \<psi>)) = size \<psi>) \<Longrightarrow>
    (\<And>ts db \<psi>. size \<psi> = n \<Longrightarrow>
      eval ts (rdb db) (R \<psi>) = (case eval' ts db \<psi> of (ys, \<psi>') \<Rightarrow> (map reopt_table ys, R \<psi>'))) \<Longrightarrow>
    size \<phi> = n \<Longrightarrow>
    letpast_meval0 eval j i (map reopt_table ys) (map reopt_table xs) p ts (rdb db) (R \<phi>)
    = (case letpast_meval0 eval' j i ys xs p ts db \<phi> of
        (ys', i', b, \<phi>') \<Rightarrow> (map reopt_table ys', i', map_option reopt_table b, R \<phi>'))"
proof (induct eval' j i ys xs p ts db \<phi> rule: letpast_meval0.induct)
  case (1 eval' j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where e: "eval' ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by (cases "eval' ts (Mapping.update p xs db) \<phi>")
  have L: "eval ts (rdb (Mapping.update p xs db)) (R \<phi>) = (map reopt_table ys', R \<phi>')"
    using "1.prems"(2)[OF "1.prems"(3), of ts "Mapping.update p xs db"] by (simp add: e)
  have s1: "size \<phi>' = size \<phi>"
    using "1.prems"(1)[of ts "Mapping.update p xs db" \<phi>] by (simp add: e)
  have s2: "size (R \<phi>') = size (R \<phi>)"
    using sz'[of ts "rdb (Mapping.update p xs db)" "R \<phi>"] by (simp add: L)
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      by (subst (1 2) letpast_meval0.simps) (auto simp: Let_def L e s1 s2 "1.prems"(3))
  next
    case (Cons y ys'')
    note IH = "1.hyps"[OF refl e[symmetric] _ _ _ "1.prems"(1) "1.prems"(2),
        unfolded map_append]
    show ?thesis
    proof (cases "j \<le> Suc (i + length xs)")
      case True
      then show ?thesis
        by (subst (1 2) letpast_meval0.simps) (simp add: Let_def L e s1 s2 Cons)
    next
      case False
      have n: "size \<phi>' = n"
        using s1 "1.prems"(3) by simp
      have rec: "letpast_meval0 eval j (i + length xs) (map reopt_table (ys @ ys'))
          (map reopt_table ys') p [] (rdb (Mapping.map_values (\<lambda>_ _. []) db)) (R \<phi>') =
        (case letpast_meval0 eval' j (i + length xs) (ys @ ys') ys' p []
            (Mapping.map_values (\<lambda>_ _. []) db) \<phi>' of
          (ys', i', b, \<phi>') \<Rightarrow> (map reopt_table ys', i', map_option reopt_table b, R \<phi>'))"
        using IH[OF _ Cons False _ n] s1 by simp
      show ?thesis
        using False rec
        by (subst (1 2) letpast_meval0.simps) (simp add: Let_def L e s1 s2 Cons)
    qed
  qed
qed

lemma freeze_meval0_rdb:
  "(\<And>\<alpha>. \<alpha> \<in> set \<alpha>s \<Longrightarrow> fst (eval (reopt_table \<alpha>)) = map reopt_table (fst (eval' \<alpha>))) \<Longrightarrow>
   freeze_meval0 eval k (map reopt_table \<alpha>s)
   = (case freeze_meval0 eval' k \<alpha>s of (ys, \<alpha>s') \<Rightarrow> (map reopt_table ys, map reopt_table \<alpha>s'))"
proof (induct eval' k \<alpha>s rule: freeze_meval0.induct)
  case (2 eval' k \<alpha> \<alpha>s)
  obtain ys \<psi> where e: "eval' \<alpha> = (ys, \<psi>)" by (cases "eval' \<alpha>")
  obtain ys' \<psi>' where e': "eval (reopt_table \<alpha>) = (ys', \<psi>')" by (cases "eval (reopt_table \<alpha>)")
  have ys': "ys' = map reopt_table ys" using 2(2)[of \<alpha>] e e' by simp
  have IH: "freeze_meval0 eval (Suc k) (map reopt_table \<alpha>s)
      = (case freeze_meval0 eval' (Suc k) \<alpha>s of (ys, \<alpha>s') \<Rightarrow> (map reopt_table ys, map reopt_table \<alpha>s'))"
    if "drop k ys = y # ys''" for y ys''
    by (rule 2(1)[OF refl e[symmetric] that]) (auto simp: 2(2))
  show ?case by (cases "drop k ys") (auto simp: e e' ys' drop_map IH split: prod.splits)
qed simp

subsection \<open>The formula\<close>

datatype udformula =
    UDFail
  | UDRel utable
  | UDPredS Formula.name nat
  | UDPredM Formula.name nat "Formula.trm list" cols
  | UDAndRel udformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | UDNeg udformula
  | UDExists udformula bool
  | UDAgg bool "ty Formula.agg_op" Formula.trm nat nat udformula
  | UDOr udformula udformula uebuf2
  | UDAnd djoin_plan udformula bool udformula uebuf2
  | UDPrev \<I> udformula bool "utable mbuf_t" "ts mbuf_t"
  | UDNext \<I> udformula bool "ts mbuf_t"
  | UDAnds "djoin_plan list" "djoin_plan list" "udformula list" uebufn
  | UDSince args udformula udformula uebuf2S udsaux_x
  | UDUntil args "bool list" udformula udformula uebuf2 "ts mbuf_t" ts uduaux_x
  | UDAndAssign nat Formula.trm udformula
  | UDTP mtrm nat
  | UDTS mtrm
  | UDLet Formula.name nat udformula udformula
  | UDFrz Formula.name nat udformula udformula nat nat nat "utable list"
      udformula nat nat "ts list" "utable list" enat bool
  | UDLetPast Formula.name nat udformula udformula nat "utable option"
  | UDTrigger args "nat option list" udformula udformula uebuf2 "ts mbuf_t"
      "event_data gmmtaux"
  | UDAndTrigger djoin_plan udformula "utable mbuf_t \<times> utable option mbuf_t" args
      udformula udformula uebuf2 "ts mbuf_t" "event_data gmmtaux"
  | UDMatchP nat \<I> mregex "mregex list" "nat option list list" "udformula list"
      uebufn "ts mbuf_t" "event_data gmrdaux"
  | UDMatchF nat \<I> mregex "mregex list" "nat option list list" "udformula list"
      uebufn "ts mbuf_t" ts "event_data gmldaux"

text \<open>The two match nodes run the windows of @{theory MFODL_Monitor_Dense.Dense_Unbox} over short
  tuples; the boxed nodes run the same windows over the boxed ones, and the two differ by the
  option around every field of every table in them.\<close>

definition rmrd :: "event_data gmrdaux \<Rightarrow> event_data mr\<delta>aux" where
  "rmrd = map (\<lambda>(t, X). (t, Mapping.map_values (\<lambda>_. reopt_table) X))"

definition rmld :: "event_data gmldaux \<Rightarrow> event_data ml\<delta>aux" where
  "rmld = map (\<lambda>(t, rls, rel). (t, map reopt_table rls, reopt_table rel))"

abbreviation rbuf2 :: "uebuf2 \<Rightarrow> event_data mebuf2" where
  "rbuf2 \<equiv> map_prod (map_mbuf reopt_table) (map_mbuf reopt_table)"

text \<open>The trigger's buffers are the short ones like every other node's: its left operand stays
  at its own frame, so nothing it holds has a hole, and @{const bmm} relabels the structure.\<close>

text \<open>A guarded Since node stands for the boxed node read through the constraint: the guard is
  the short evaluator's alone, and the two agree because filtering the whole result is filtering
  the groups as they are read.\<close>

definition edandrel :: "uconstr option \<Rightarrow> edformula \<Rightarrow> edformula" where
  "edandrel q e = (case q of None \<Rightarrow> e | Some c \<Rightarrow> EDAndRel e c)"

lemma edandrel_None[simp]: "edandrel None e = e"
  by (simp add: edandrel_def)

lemma edeval_edandrel:
  "edeval j ts db (edandrel q e)
   = (case edeval j ts db e of (zs, e') \<Rightarrow> (map (dfilt q) zs, edandrel q e'))"
  by (simp add: edandrel_def dfilt_Some split: option.splits prod.splits)

lemma evdfail_nodes_edandrel[simp]: "evdfail_nodes (edandrel q e) = evdfail_nodes e"
  by (simp add: edandrel_def split: option.splits)

fun Rep_udformula :: "udformula \<Rightarrow> edformula" where
  "Rep_udformula UDFail = EDFail"
| "Rep_udformula (UDRel rel) = EDRel (reopt_table rel)"
| "Rep_udformula (UDPredS e ar) = EDPredS e ar"
| "Rep_udformula (UDPredM e ar tms cs) = EDPredM e ar tms cs"
| "Rep_udformula (UDAndRel \<phi> conf) = EDAndRel (Rep_udformula \<phi>) conf"
| "Rep_udformula (UDNeg \<phi>) = EDNeg (Rep_udformula \<phi>)"
| "Rep_udformula (UDExists \<phi> b) = EDExists (Rep_udformula \<phi>) b"
| "Rep_udformula (UDAgg g0 \<omega> f k pos \<phi>) = EDAgg g0 \<omega> f k pos (Rep_udformula \<phi>)"
| "Rep_udformula (UDOr \<phi> \<psi> buf) = EDOr (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 buf)"
| "Rep_udformula (UDAnd pl \<phi> pos \<psi> buf) =
     EDAnd pl (Rep_udformula \<phi>) pos (Rep_udformula \<psi>) (rbuf2 buf)"
| "Rep_udformula (UDPrev I \<phi> first buf nts) =
     EDPrev I (Rep_udformula \<phi>) first (map_mbuf reopt_table buf) nts"
| "Rep_udformula (UDNext I \<phi> first nts) = EDNext I (Rep_udformula \<phi>) first nts"
| "Rep_udformula (UDAnds ps ns L buf) =
     EDAnds ps ns (map Rep_udformula L) (map (map_mbuf reopt_table) buf)"
| "Rep_udformula (UDSince args \<phi> \<psi> buf aux) =
     edandrel (usx_q aux)
       (EDSince args (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbufS buf) (rdsx aux))"
| "Rep_udformula (UDUntil args msk \<phi> \<psi> buf nts t aux) =
     EDUntil args msk (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 buf) nts t (rdux aux)"
| "Rep_udformula (UDAndAssign p t \<phi>) = EDAndAssign p t (Rep_udformula \<phi>)"
| "Rep_udformula (UDTP mt i) = EDTP mt i"
| "Rep_udformula (UDTS mt) = EDTS mt"
| "Rep_udformula (UDLet p m \<phi> \<psi>) = EDLet p m (Rep_udformula \<phi>) (Rep_udformula \<psi>)"
| "Rep_udformula (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po) =
     EDFrz p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) jfrz jpsi0 jphi (map reopt_table \<alpha>s)
       (Rep_udformula \<rho>) w pR tq (map reopt_table rb) d po"
| "Rep_udformula (UDLetPast p m \<phi> \<psi> i buf) =
     EDLetPast p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) i (map_option reopt_table buf)"
| "Rep_udformula (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     EDTrigger dags pl (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbuf) nts (bmm daux)"
| "Rep_udformula (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     EDAndTrigger pl (Rep_udformula \<alpha>)
       (map_prod (map_mbuf reopt_table) (map_mbuf (map_option reopt_table)) dbf1) dags
       (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbf2) nts (bmm daux)"
| "Rep_udformula (UDMatchP m I mr mrs pls Ld dbuf nts daux) =
     EDMatchP m I mr mrs pls (map Rep_udformula Ld) (map (map_mbuf reopt_table) dbuf) nts (rmrd daux)"
| "Rep_udformula (UDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     EDMatchF m I mr mrs pls (map Rep_udformula Ld) (map (map_mbuf reopt_table) dbuf) nts t (rmld daux)"

fun uvdfail_nodes :: "udformula \<Rightarrow> nat" where
  "uvdfail_nodes UDFail = 1"
| "uvdfail_nodes (UDAndRel \<phi> conf) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDNeg \<phi>) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDExists \<phi> b) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDAgg g0 \<omega> f k pos \<phi>) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDOr \<phi> \<psi> buf) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDAnd pl \<phi> pos \<psi> buf) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDPrev I \<phi> f buf nts) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDNext I \<phi> f nts) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDAnds ps ns L buf) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes (UDSince args \<phi> \<psi> buf aux) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDUntil args msk \<phi> \<psi> buf nts t aux) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDAndAssign p t \<phi>) = uvdfail_nodes \<phi>"
| "uvdfail_nodes (UDLet p m \<phi> \<psi>) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po) =
    uvdfail_nodes \<phi> + uvdfail_nodes \<psi> + uvdfail_nodes \<rho>"
| "uvdfail_nodes (UDLetPast p m \<phi> \<psi> i buf) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     uvdfail_nodes \<alpha> + uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDMatchP m I mr mrs pls L dbuf nts daux) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes (UDMatchF m I mr mrs pls L dbuf nts t daux) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes \<phi> = 0"

lemma evdfail_nodes_Rep: "evdfail_nodes (Rep_udformula \<phi>) = uvdfail_nodes \<phi>"
  by (induct \<phi>) (auto simp: comp_def intro: arg_cong[of _ _ sum_list])

subsection \<open>The Since buffer\<close>

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

text \<open>The two agree on the whole run: the boxed evaluator's results, read through the node's
  guard, are the short evaluator's.  The accumulator is carried the same way, so the statement
  relates the two lists it is started with.\<close>

lemma edsx_eval_since_rdsx:
  "map (dfilt (usx_q aux)) Rs = map reopt_table rs \<Longrightarrow>
   (case edsx_eval_since args Rs (rbufS buf) (rdsx aux) of
      (Zs, bf, a) \<Rightarrow> (map (dfilt (usx_q aux)) Zs, bf, a))
   = (case uedsx_eval_since args rs buf aux of
        (zs, buf', aux') \<Rightarrow> (map reopt_table zs, rbufS buf', rdsx aux'))"
proof (induct args rs buf aux arbitrary: Rs rule: uedsx_eval_since.induct)
  case (1 args rs xs ys ts skew aux)
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  show ?case
    using 1 x y t
    by (cases y; cases x; cases t; simp only: rbufS.simps;
        subst edsx_eval_since.simps; subst uedsx_eval_since.simps)
      (auto simp: x y t Let_def rev_map[symmetric] dsx_join_rdsx dsx_add_new_ts_rdsx
        dsx_add_new_table_rdsx dsx_result_rdsx
        simp del: edsx_eval_since.simps uedsx_eval_since.simps split: prod.splits)
qed

subsection \<open>The evaluator\<close>

function (sequential) udeval :: "nat \<Rightarrow> ts list \<Rightarrow> udatabase \<Rightarrow> udformula \<Rightarrow>
    utable list \<times> udformula" where
  "udeval j ts db UDFail = ([], UDFail)"
| "udeval j ts db (UDRel rel) = (replicate (length ts) rel, UDRel rel)"
| "udeval j ts db (UDPredS e ar) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> xs), UDPredS e ar)"
| "udeval j ts db (UDPredM e ar tms cs) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> map (umatch_table tms cs) xs), UDPredM e ar tms cs)"
| "udeval j ts db (UDAndRel \<phi> conf) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in (map (Set.filter (ueval_constraint conf)) xs, UDAndRel \<phi>' conf))"
| "udeval j ts db (UDNeg \<phi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in (map (\<lambda>r. if r = {} then {[]} else {}) xs, UDNeg \<phi>'))"
| "udeval j ts db (UDExists \<phi> drop0) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in (if drop0 then map (\<lambda>r. tl ` r) xs else xs, UDExists \<phi>' drop0))"
| "udeval j ts db (UDAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi> in (map (uagg g0 \<omega> f k pos) xs, UDAgg g0 \<omega> f k pos \<phi>'))"
| "udeval j ts db (UDOr \<phi> \<psi> buf) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
      in (zs, UDOr \<phi>' \<psi>' buf'))"
| "udeval j ts db (UDAnd pl \<phi> pos \<psi> buf) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2) (mebuf2_add xs ys buf)
      in (zs, UDAnd pl \<phi>' pos \<psi>' buf'))"
| "udeval j ts db (UDPrev I \<phi> first buf nts) =
     (let (xs, \<phi>') = udeval j ts db \<phi>
      in if first \<and> ts = [] then ([], UDPrev I \<phi>' True (buf @@ xs) (nts @@ ts))
      else let (zs, buf', nts') = ueprev_next I (buf @@ xs) (nts @@ ts)
        in (if first then {} # zs else zs, UDPrev I \<phi>' False buf' nts'))"
| "udeval j ts db (UDNext I \<phi> first nts) =
     (let (xs, \<phi>') = udeval j ts db \<phi>;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = ueprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
      in (zs, UDNext I \<phi>' first' nts'))"
| "udeval j ts db (UDAnds ps ns Ld dbuf) =
     (let R = map (udeval j ts db) Ld;
          (zs, dbuf') = uebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty
            (uebufn_add (map fst R) dbuf)
      in (Rep_mbuf_t zs, UDAnds ps ns (map snd R) dbuf'))"
| "udeval j ts db (UDSince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (zs, buf', aux') = uedsx_eval_since dags [] (uebuf2S_add xs ys ts buf) aux
      in (zs, UDSince dags \<phi>' \<psi>' buf' aux'))"
| "udeval j ts db (UDUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (aux', buf', nt, nts') = uebuf2t_take (udux_add_new dags msk) aux
            (mebuf2_add xs ys buf) t (nts @@ ts);
          (zs, aux'') = udux_eval dags nt aux'
      in (zs, UDUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "udeval j ts db (UDAndAssign p t \<phi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi> in (map (uassign p t) xs, UDAndAssign p t \<phi>'))"
| "udeval j ts db (UDTP mt i) =
     (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) [i..<j], UDTP mt j)"
| "udeval j ts db (UDTS mt) = (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) ts, UDTS mt)"
| "udeval j ts db (UDLet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = udeval j ts db \<phi>;
          (ys, \<psi>') = udeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, UDLet p m \<phi>' \<psi>'))"
| "udeval j ts db (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po) =
     (let (xs, \<phi>) = udeval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = udeval j ts db0 \<psi>;
          zs0_out = drop (jfrz - jpsi0) zs0;
          jpsi0 = jpsi0 + length zs0;
          \<alpha>s = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs);
          jfrz = jfrz + length zs0_out;
          (rs, \<rho>) = udeval j ts db0 \<rho>;
          rb0 = pR - length rb;
          rb = rb @ rs;
          pR = pR + length rs;
          dbe = Mapping.map_values (\<lambda>_ _. []) db;
          c = frz_cut po w jphi (length xs) j;
          (ys, \<alpha>s') = freeze_meval0 (\<lambda>\<alpha>. (rb @ fst (udeval j []
            (Mapping.update (p, m) (replicate c \<alpha>) dbe) \<rho>), ())) (jfrz - rb0) \<alpha>s;
          jphi = jphi + length xs;
          jfrz = jfrz + length ys;
          tq = (if d = \<infinity> then [] else tq @ ts);
          a = frz_adv d w jfrz j tq;
          (rs2, \<rho>) = udeval j [] (Mapping.update (p, m) (replicate a {}) dbe) \<rho>;
          rb = rb @ rs2;
          pR = pR + length rs2
      in (zs0_out @ ys, UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s' \<rho> (w + a) pR (drop a tq) (drop (min jfrz pR - rb0) rb) d po))"
| "udeval j ts db (UDLetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            letpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
          (ys, \<psi>) = udeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, UDLetPast p m \<phi> \<psi> i buf))"
| "udeval j ts db (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = uebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
            (mebuf2_add xs ys dbuf) (nts @@ ts)
      in (zs, UDTrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "udeval j ts db (UDMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (udeval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = uebufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @@ [z], ax)) (mbuf_t_empty, daux)
             (uebufn_add (map fst R) dbuf) 0 (nts @@ ts)
      in (Rep_mbuf_t zs,
          UDMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "udeval j ts db (UDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (udeval j ts db) Ld;
          (daux', dbuf', nt, nts') = uebufnt_take
             (\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels)
             daux (uebufn_add (map fst R) dbuf) t (nts @@ ts);
          (zs, daux'') = geval_matchF I mr nt daux'
      in (zs,
          UDMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
| "udeval j ts db (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     (let (as, \<alpha>') = udeval j ts db \<alpha>; (xs, \<phi>') = udeval j ts db \<phi>;
          (ys, \<psi>') = udeval j ts db \<psi>;
          ((ws, daux'), dbf2', nts') = uebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (ws @ [if gmmtaux_empty ax then None
                      else Some (gresult_mmtaux dags ax)], ax)) ([], daux)
            (mebuf2_add xs ys dbf2) (nts @@ ts);
          (zs, dbf1') = mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> gbin_join pl r1 True z) (mebuf2_add as ws dbf1)
      in (zs, UDAndTrigger pl \<alpha>' dbf1' dags \<phi>' \<psi>' dbf2' nts' daux'))"
  by pat_completeness safe

lemma psize_snd_udeval:
  "udeval_dom (j, ts, db, \<phi>) \<Longrightarrow> size (snd (udeval j ts db \<phi>)) = size \<phi>"
proof (induct rule: udeval.pinduct)
  case (11 j ts db I \<phi> first buf nts) \<comment> \<open>\<^const>\<open>UDPrev\<close>\<close>
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "ueprev_next I (buf @@ xs) (nts @@ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "size \<phi>' = size \<phi>"
    using 11(2) \<phi>' by simp
  then show ?case
    by (simp add: udeval.psimps(11)[OF 11(1)] \<phi>' mp del: ueprev_next.simps)
next
  case (21 j ts db p m \<phi> \<psi> i buf) \<comment> \<open>\<^const>\<open>UDLetPast\<close>\<close>
  obtain xs i' buf' \<phi>' where lp:
    "letpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi> = (xs, i', buf', \<phi>')"
    by (metis prod_cases4)
  have "size (snd (snd (snd
      (letpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>)))) = size \<phi>"
    by (rule size_letpast_meval) (simp add: 21(2))
  then have size_\<phi>': "size \<phi>' = size \<phi>"
    by (simp add: lp)
  obtain ys \<psi>' where \<psi>': "udeval j ts (Mapping.update (p, m) xs db) \<psi> = (ys, \<psi>')"
    by fastforce
  have size_\<psi>': "size \<psi>' = size \<psi>"
    using 21(3)[OF lp[symmetric] refl refl refl] \<psi>' by simp
  show ?case
    using size_\<phi>' size_\<psi>' by (simp add: udeval.psimps(21)[OF 21(1)] lp \<psi>')
  \<comment> \<open>in all other cases, the claim follows directly from the IHs for the subformulas,
    since evaluation keeps the node's constructor and its non-formula arguments do not count\<close>
qed (auto simp only: prod.inject udeval.psimps Let_def snd_conv fst_conv
    udformula.size list.map map_map o_apply size_list_map cong: size_list_cong
    split: prod.splits)

lemma total_udeval: "All udeval_dom"
proof (relation "measure (\<lambda>(j, ts, db, \<phi>). size \<phi>)", goal_cases)
  text \<open>The freeze's replays and the advance of its window, as for @{const meval}.\<close>
  case (23 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po x xa y xb xc xd ya xe xf xg xh xi xj yb)
  have "size yb = size \<rho>"
    using psize_snd_udeval[OF 23(17)] 23(10,11) by (metis snd_conv)
  then show ?case
    by simp
next
  case (24 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po x xa y xb xc xd ya xe xf xg xh xi xj yb)
  have "size yb = size \<rho>"
    using psize_snd_udeval[OF 24(24)] 24(10,11) by (metis snd_conv)
  then show ?case
    by simp
qed (auto simp: termination_simp dest!: psize_snd_udeval dest: sym)

termination udeval by (rule total_udeval)

lemma size_snd_udeval[simp]: "size (snd (udeval j ts db \<phi>)) = size \<phi>"
  by (rule psize_snd_udeval[OF total_udeval[THEN spec]])

subsection \<open>The two evaluators agree\<close>

lemma mebuf2_take_or:
  "mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (rbuf2 buf)
   = (case mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) buf of (zs, buf') \<Rightarrow> (map reopt_table zs, rbuf2 buf'))"
  by (rule mebuf2_take_rbuf) simp

lemma mebuf2_take_and:
  "mebuf2_take (\<lambda>r1 r2. dbin_join pl r1 pos r2) (rbuf2 buf)
   = (case mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2) buf of
        (zs, buf') \<Rightarrow> (map reopt_table zs, rbuf2 buf'))"
  by (rule mebuf2_take_rbuf) (simp add: dbin_join_reopt_table)

lemma mebufn_take_ands:
  "mebufn_take (\<lambda>as zs. zs @@ [dmulti_join ps ns as]) mbuf_t_empty (map (map_mbuf reopt_table) buf)
   = (case uebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty buf of
        (zs, buf') \<Rightarrow> (map_mbuf reopt_table zs, map (map_mbuf reopt_table) buf'))"
  using mebufn_take_map_mbuf[of "\<lambda>as zs. zs @@ [dmulti_join ps ns as]" reopt_table
      "map_mbuf reopt_table" "\<lambda>as zs. zs @@ [gmulti_join ps ns as]" mbuf_t_empty buf]
  by (simp add: dmulti_join_reopt_table)

text \<open>The past-match window commutes with putting the option back on the fields: the semi-join,
  the unions and intersections, the unit table and the tabulation all do, for every argument.\<close>

lemma gnth_map_reopt[simp]: "gnth (map reopt_table xs) i = reopt_table (gnth xs i)"
  by (simp add: gnth_def)

lemma reopt_table_unit[simp]: "reopt_table {[]} = {[]}"
  by (simp add: reopt_table_def)

lemma reopt_table_if_empty[simp]:
  "(if b then reopt_table X else {}) = reopt_table (if b then X else {})"
  by simp

lemma glookup_rmap[simp]:
  "glookup (Mapping.map_values (\<lambda>_. reopt_table) X) ms = reopt_table (glookup X ms)"
  by (simp add: glookup_def Mapping.lookup_default_def Mapping.lookup_map_values
      split: option.splits)

lemma gmrtabulate_reopt[simp]:
  "gmrtabulate xs (\<lambda>ms. reopt_table (f ms))
   = Mapping.map_values (\<lambda>_. reopt_table) (gmrtabulate xs f)"
  by transfer (rule ext, induct_tac xs, auto simp: Let_def)

lemma geps_lax_reopt[simp]:
  "geps_lax msks (reopt_table g) (map reopt_table \<phi>s) r = reopt_table (geps_lax msks g \<phi>s r)"
  by (induct r arbitrary: g) auto

lemma greps_strict_reopt[simp]:
  "greps_strict msks (map reopt_table \<phi>s) r = reopt_table (greps_strict msks \<phi>s r)"
  by (induct r) auto

lemma grdelta_reopt[simp]:
  "grdelta msks \<kappa> (Mapping.map_values (\<lambda>_. reopt_table) X) (map reopt_table \<phi>s) r
   = reopt_table (grdelta msks \<kappa> X \<phi>s r)"
  by (induct r arbitrary: \<kappa>) (auto split: nat.splits)

lemma rmrd_simps[simp]: "rmrd [] = []"
  "rmrd ((t, X) # aux) = (t, Mapping.map_values (\<lambda>_. reopt_table) X) # rmrd aux"
  by (simp_all add: rmrd_def)

lemma foldr_glookup_rmrd:
  "foldr (\<union>) [glookup rel mr. (t, rel) \<leftarrow> rmrd A, P t] {}
   = reopt_table (foldr (\<union>) [glookup rel mr. (t, rel) \<leftarrow> A, P t] {})"
  by (induct A) auto

lemma rmrd_case:
  "(case rmrd W of [] \<Rightarrow> [(nt, Mapping.map_values (\<lambda>_. reopt_table) H)]
    | x # w \<Rightarrow> (if fst x = nt then x # w else (nt, Mapping.map_values (\<lambda>_. reopt_table) H) # x # w))
   = rmrd (case W of [] \<Rightarrow> [(nt, H)] | x # w \<Rightarrow> (if fst x = nt then x # w else (nt, H) # x # w))"
  by (cases W) (auto simp: rmrd_def split: prod.splits)

lemma gupdate_matchP_reopt:
  "gupdate_matchP msks I mr mrs (map reopt_table rels) nt (rmrd aux)
   = map_prod reopt_table rmrd (gupdate_matchP msks I mr mrs rels nt aux)"
proof -
  let ?W = "\<lambda>rels aux. [(t, gmrtabulate mrs (\<lambda>mr. grdelta msks id rel rels mr
      \<union> (if t = nt then greps_strict msks rels mr else {}))). (t, rel) \<leftarrow> aux, memR I (nt - t)]"
  have W: "?W (map reopt_table rels) (rmrd aux) = rmrd (?W rels aux)"
    by (induct aux) (auto cong: if_cong)
  have H: "greps_strict msks (map reopt_table rels) = (\<lambda>ms. reopt_table (greps_strict msks rels ms))"
    by (rule ext) simp
  show ?thesis
    unfolding gupdate_matchP_def Let_def unfolding W unfolding H gmrtabulate_reopt rmrd_case
    by (simp only: foldr_glookup_rmrd map_prod_simp)
qed

lemma mebufnt_take_matchP:
  "mebufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax)))
     (map_prod (map_mbuf reopt_table) rmrd z0) (map (map_mbuf reopt_table) buf) t0 ts
   = (case uebufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax))) z0 buf t0 ts of
        (z', buf', t', ts') \<Rightarrow>
          (map_prod (map_mbuf reopt_table) rmrd z', map (map_mbuf reopt_table) buf', t', ts'))"
  by (rule mebufnt_take_map_mbuf) (auto simp: gupdate_matchP_reopt split: prod.splits)

text \<open>The future window likewise; it keeps the operands' tables of every time point it has not
  decided yet, so the relabelling covers those too.\<close>

lemma gleps_strict_reopt[simp]:
  "gleps_strict msks (map reopt_table \<phi>s) r = reopt_table (gleps_strict msks \<phi>s r)"
  by (induct r) auto

lemma gldelta_reopt[simp]:
  "gldelta msks \<kappa> (Mapping.map_values (\<lambda>_. reopt_table) X) (map reopt_table \<phi>s) r
   = reopt_table (gldelta msks \<kappa> X \<phi>s r)"
  by (induct r arbitrary: \<kappa>) (auto split: nat.splits)

lemma rmld_simps[simp]: "rmld [] = []"
  "rmld ((t, rls, rel) # aux) = (t, map reopt_table rls, reopt_table rel) # rmld aux"
  by (simp_all add: rmld_def)

lemma gupdate_matchF_base_reopt:
  "gupdate_matchF_base msks I mr mrs (map reopt_table rels) nt
   = map_prod rmld (Mapping.map_values (\<lambda>_. reopt_table))
       (gupdate_matchF_base msks I mr mrs rels nt)"
proof -
  have H: "gleps_strict msks (map reopt_table rels) = (\<lambda>ms. reopt_table (gleps_strict msks rels ms))"
    by (rule ext) simp
  show ?thesis
    unfolding gupdate_matchF_base_def Let_def H gmrtabulate_reopt by (simp cong: if_cong)
qed

lemma gupdate_matchF_step_reopt:
  "gupdate_matchF_step msks I mr mrs nt (t, map reopt_table rls, reopt_table rel)
     (rmld aux, Mapping.map_values (\<lambda>_. reopt_table) X)
   = map_prod rmld (Mapping.map_values (\<lambda>_. reopt_table))
       (gupdate_matchF_step msks I mr mrs nt (t, rls, rel) (aux, X))"
proof -
  have H: "gldelta msks id (Mapping.map_values (\<lambda>_. reopt_table) X) (map reopt_table rls)
      = (\<lambda>ms. reopt_table (gldelta msks id X rls ms))"
    by (rule ext) simp
  show ?thesis
    unfolding gupdate_matchF_step_def Let_def prod.case H gmrtabulate_reopt by (simp cong: if_cong)
qed

lemma gupdate_matchF_foldr_reopt:
  "foldr (gupdate_matchF_step msks I mr mrs nt) (rmld aux)
     (gupdate_matchF_base msks I mr mrs (map reopt_table rels) nt)
   = map_prod rmld (Mapping.map_values (\<lambda>_. reopt_table))
       (foldr (gupdate_matchF_step msks I mr mrs nt) aux (gupdate_matchF_base msks I mr mrs rels nt))"
proof (induct aux)
  case Nil
  then show ?case by (simp add: gupdate_matchF_base_reopt)
next
  case (Cons a aux)
  obtain t rls rel where a: "a = (t, rls, rel)" by (cases a)
  obtain A X where F: "foldr (gupdate_matchF_step msks I mr mrs nt) aux
      (gupdate_matchF_base msks I mr mrs rels nt) = (A, X)" by fastforce
  show ?case using Cons by (simp add: a F gupdate_matchF_step_reopt)
qed

lemma gupdate_matchF_reopt:
  "gupdate_matchF msks I mr mrs (map reopt_table rels) nt (rmld aux)
   = rmld (gupdate_matchF msks I mr mrs rels nt aux)"
  using gupdate_matchF_foldr_reopt[of msks I mr mrs nt aux rels]
  by (simp add: gupdate_matchF_def)

lemma geval_matchF_reopt:
  "geval_matchF I mr nt (rmld aux) = map_prod (map reopt_table) rmld (geval_matchF I mr nt aux)"
  by (induct aux) (auto split: prod.splits)

lemma mebufnt_take_matchF:
  "mebufnt_take (\<lambda>rels. gupdate_matchF msks I mr mrs rels)
     (rmld z0) (map (map_mbuf reopt_table) buf) t0 ts
   = (case uebufnt_take (\<lambda>rels. gupdate_matchF msks I mr mrs rels) z0 buf t0 ts of
        (z', buf', t', ts') \<Rightarrow> (rmld z', map (map_mbuf reopt_table) buf', t', ts'))"
  by (rule mebufnt_take_map_mbuf) (simp add: gupdate_matchF_reopt)

lemma mebufnt_take_matchP':
  assumes "uebufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax)))
     (mbuf_t_empty, a0) buf t0 ts = ((zs', a'), buf', t', ts')"
  shows "mebufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax)))
     (mbuf_t_empty, rmrd a0) (map (map_mbuf reopt_table) buf) t0 ts
     = ((map_mbuf reopt_table zs', rmrd a'), map (map_mbuf reopt_table) buf', t', ts')"
  using mebufnt_take_matchP[of msks I mr mrs "(mbuf_t_empty, a0)" buf t0 ts] assms
  by simp

lemma mebufnt_take_matchF':
  assumes "uebufnt_take (\<lambda>rels. gupdate_matchF msks I mr mrs rels) z0 buf t0 ts = (z', buf', t', ts')"
  shows "mebufnt_take (\<lambda>rels. gupdate_matchF msks I mr mrs rels)
      (rmld z0) (map (map_mbuf reopt_table) buf) t0 ts
    = (rmld z', map (map_mbuf reopt_table) buf', t', ts')"
  using mebufnt_take_matchF[of msks I mr mrs z0 buf t0 ts] assms by simp

lemma map_dsan_reopt_deopt: "map dsan xs = map reopt_table (map deopt_table xs)"
  by (simp add: dsan_def)

lemma mebuf2t_take_until:
  "mebuf2t_take (dux_add_new dags msk) (rdux aux) (rbuf2 buf) t ts
   = (case uebuf2t_take (udux_add_new dags msk) aux buf t ts of
        (aux', buf', t', ts') \<Rightarrow> (rdux aux', rbuf2 buf', t', ts'))"
  by (rule mebuf2t_take_rbuf) (simp add: dux_add_new_rdux)

lemma mebuf2T_take_rbuf:
  assumes "\<And>x y t z. f (reopt_table x) (reopt_table y) t (h z) = h (f' x y t z)"
  shows "mebuf2T_take f (h z) (rbuf2 buf) ts
   = (case uebuf2T_take f' z buf ts of (z', buf', ts') \<Rightarrow> (h z', rbuf2 buf', ts'))"
  by (cases buf)
    (simp add: mebuf2T_take_map_mbuf[where f = f and h = h and f' = f', OF assms]
       split: prod.splits del: mebuf2T_take.simps uebuf2T_take.simps)

text \<open>The trigger's buffer traversal, relabelled: the structure by @{const bmm} and the output
  list tablewise.  The step commutes with the pair of them by @{thm [source] gupdate_mmtaux_bmm}
  and @{thm [source] gresult_mmtaux_bmm}, with no invariant.\<close>

lemma mebuf2T_take_trigger:
  "mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [dsan (gresult_mmtaux dags ax)], ax))
     ([], bmm daux) (rbuf2 buf) ts
   = (case uebuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux) buf ts of
        (z', buf', ts') \<Rightarrow> (map_prod (map reopt_table) bmm z', rbuf2 buf', ts'))"
proof -
  have "mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (zs @ [dsan (gresult_mmtaux dags ax)], ax))
        (map_prod (map reopt_table) bmm ([], daux)) (rbuf2 buf) ts
      = (case uebuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux) buf ts of
          (z', buf', ts') \<Rightarrow> (map_prod (map reopt_table) bmm z', rbuf2 buf', ts'))"
    by (rule mebuf2T_take_rbuf)
      (simp add: Let_def case_prod_beta map_prod_def gupdate_mmtaux_bmm gresult_mmtaux_bmm)
  then show ?thesis by simp
qed

text \<open>The fused And-Trigger's two traversals.  The inner one is the trigger's, with the empty
  window kept as @{term None}; the outer one relabels its two sides differently, the left
  operand's tables and the trigger's optional reads.\<close>

lemma mebuf2T_take_andtrigger:
  "mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None
                else Some (dsan (gresult_mmtaux dags ax))], ax))
     ([], bmm daux) (rbuf2 buf) ts
   = (case uebuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
      ([], daux) buf ts of
        (z', buf', ts') \<Rightarrow> (map_prod (map (map_option reopt_table)) bmm z', rbuf2 buf', ts'))"
proof -
  have "mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (ws @ [if gmmtaux_empty ax then None
                  else Some (dsan (gresult_mmtaux dags ax))], ax))
        (map_prod (map (map_option reopt_table)) bmm ([], daux)) (rbuf2 buf) ts
      = (case uebuf2T_take (\<lambda>r1 r2 t (ws, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
        ([], daux) buf ts of
          (z', buf', ts') \<Rightarrow> (map_prod (map (map_option reopt_table)) bmm z', rbuf2 buf', ts'))"
    by (rule mebuf2T_take_rbuf)
      (simp add: Let_def case_prod_beta map_prod_def gupdate_mmtaux_bmm gresult_mmtaux_bmm
        gmmtaux_empty_bmm)
  then show ?thesis by simp
qed

lemma mebuf2_take_map_mbuf2:
  "(\<And>x y. f (ga x) (gb y) = g' (f' x y)) \<Longrightarrow>
   mebuf2_take f (map_mbuf ga xs, map_mbuf gb ys)
   = (case mebuf2_take f' (xs, ys) of
        (zs, (xs', ys')) \<Rightarrow> (map g' zs, (map_mbuf ga xs', map_mbuf gb ys')))"
proof (induct f' "(xs, ys)" arbitrary: xs ys rule: mebuf2_take.induct)
  case (1 f' xs ys)
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  show ?case using 1 x y by (cases x; cases y) (auto simp: x y split: prod.splits)
qed

lemma mebuf2_take_andtrigger:
  "mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> dbin_join pl r1 True z)
     (map_prod (map_mbuf reopt_table) (map_mbuf (map_option reopt_table)) buf)
   = (case mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> gbin_join pl r1 True z) buf of
        (zs, buf') \<Rightarrow>
          (map reopt_table zs, map_prod (map_mbuf reopt_table) (map_mbuf (map_option reopt_table)) buf'))"
proof -
  have "(case map_option reopt_table y of None \<Rightarrow> reopt_table x | Some z \<Rightarrow> dbin_join pl (reopt_table x) True z)
    = reopt_table (case y of None \<Rightarrow> x | Some z \<Rightarrow> gbin_join pl x True z)" for x y
    by (cases y) (simp_all add: dbin_join_reopt_table)
  from mebuf2_take_map_mbuf2[where ga = reopt_table and gb = "map_option reopt_table"
      and g' = reopt_table
      and f = "\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> dbin_join pl r1 True z"
      and f' = "\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> gbin_join pl r1 True z"
      and xs = "fst buf" and ys = "snd buf", OF this]
  show ?thesis by (cases buf) (simp split: prod.splits del: mebuf2_take.simps)
qed

lemma mebuf2_add_map_prod:
  "mebuf2_add (map g1 xs) (map g2 ys) (map_prod (map_mbuf g1) (map_mbuf g2) buf)
   = map_prod (map_mbuf g1) (map_mbuf g2) (mebuf2_add xs ys buf)"
  by (cases buf) simp

text \<open>The buffer lemmas in the shapes the simplifier leaves the evaluator's buffers in.\<close>

lemma meprev_next_prev:
  "meprev_next I (map_mbuf reopt_table buf @@ map reopt_table xs) ts
   = (case ueprev_next I (buf @@ xs) ts of
        (zs, xs', ts') \<Rightarrow> (map reopt_table zs, map_mbuf reopt_table xs', ts'))"
  using meprev_next_map_mbuf[of I "buf @@ xs" ts] unfolding map_mbuf_append .

lemma meprev_next_next1:
  "meprev_next I (mbuf_t_empty @@ map reopt_table xs) ts
   = (case ueprev_next I (mbuf_t_empty @@ xs) ts of
        (zs, xs', ts') \<Rightarrow> (map reopt_table zs, map_mbuf reopt_table xs', ts'))"
  using meprev_next_map_mbuf[of I "mbuf_t_empty @@ xs" ts] unfolding map_mbuf_append map_mbuf_empty .

lemma meprev_next_next2:
  "meprev_next I (mbuf_t_empty @@ []) ts
   = (case ueprev_next I (mbuf_t_empty @@ []) ts of
        (zs, xs', ts') \<Rightarrow> (map reopt_table zs, map_mbuf reopt_table xs', ts'))"
  using meprev_next_map_mbuf[of I "mbuf_t_empty @@ []" ts]
  unfolding map_mbuf_append map_mbuf_empty list.map .

lemma meprev_next_next3:
  "meprev_next I (mbuf_t_empty @@ reopt_table x # map reopt_table xs) ts
   = (case ueprev_next I (mbuf_t_empty @@ x # xs) ts of
        (zs, xs', ts') \<Rightarrow> (map reopt_table zs, map_mbuf reopt_table xs', ts'))"
  using meprev_next_map_mbuf[of I "mbuf_t_empty @@ x # xs" ts]
  unfolding map_mbuf_append map_mbuf_empty list.map .

lemma edsx_eval_since_rdsx0:
  "(case edsx_eval_since args [] (rbufS buf) (rdsx aux) of
      (Zs, bf, a) \<Rightarrow> (map (dfilt (usx_q aux)) Zs, bf, a))
   = (case uedsx_eval_since args [] buf aux of
        (zs, buf', aux') \<Rightarrow> (map reopt_table zs, rbufS buf', rdsx aux'))"
  using edsx_eval_since_rdsx[where rs = "[]" and Rs = "[]"] by simp

lemma mebuf2T_take_acc0:
  assumes "\<And>x y t zs ax. f x y t (map reopt_table zs, ax)
    = map_prod (map reopt_table) (\<lambda>a. a) (f' x y t (zs, ax))"
  shows "mebuf2T_take f ([], daux) buf ts
    = (case mebuf2T_take f' ([], daux) buf ts of
        (z', buf', ts') \<Rightarrow> (map_prod (map reopt_table) (\<lambda>a. a) z', buf', ts'))"
proof -
  have "f x y t (map_prod (map reopt_table) (\<lambda>a. a) z)
      = map_prod (map reopt_table) (\<lambda>a. a) (f' x y t z)" for x y t z
    by (cases z) (simp add: assms)
  then show ?thesis
    using mebuf2T_take_acc[of f "map_prod (map reopt_table) (\<lambda>a. a)" f' "([], daux)" buf ts] by simp
qed

lemma udeval_Rep:
  "edeval j ts (rdb db) (Rep_udformula \<phi>)
   = (case udeval j ts db \<phi> of (zs, \<phi>') \<Rightarrow> (map reopt_table zs, Rep_udformula \<phi>'))"
proof (induction j ts db \<phi> rule: udeval.induct)
  case (13 j ts db ps ns L buf)
  have "map fst (map (edeval j ts (rdb db)) (map Rep_udformula L))
      = map (map reopt_table) (map fst (map (udeval j ts db) L))"
    "map snd (map (edeval j ts (rdb db)) (map Rep_udformula L))
      = map Rep_udformula (map snd (map (udeval j ts db) L))"
    by (auto simp: 13 split: prod.splits)
  then show ?case
    by (auto simp only: Let_def edeval.simps udeval.simps Rep_udformula.simps
        mebufn_add_map_mbuf mebufn_take_ands Rep_map_mbuf split: prod.splits)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po)
  let ?db0 = "Mapping.update (p, m) [] db"
  let ?dbe = "Mapping.map_values (\<lambda>_ _. []) db"
  obtain xs \<phi>' where \<phi>: "udeval j ts db \<phi> = (xs, \<phi>')"
    by (cases "udeval j ts db \<phi>")
  obtain zs0 \<psi>' where \<psi>: "udeval j ts ?db0 \<psi> = (zs0, \<psi>')"
    by (cases "udeval j ts ?db0 \<psi>")
  obtain rs \<rho>' where \<rho>: "udeval j ts ?db0 \<rho> = (rs, \<rho>')"
    by (cases "udeval j ts ?db0 \<rho>")
  let ?k = "jfrz + length (drop (jfrz - jpsi0) zs0) - (pR - length rb)"
  let ?as = "drop (jfrz - jphi + length (drop (jfrz - jpsi0) zs0)) (\<alpha>s @ xs)"
  let ?c = "frz_cut po w jphi (length xs) j"
  have IH1: "edeval j ts (rdb db) (Rep_udformula \<phi>) = (map reopt_table xs, Rep_udformula \<phi>')"
    using 20(1) \<phi> by simp
  have IH2: "edeval j ts (rdb ?db0) (Rep_udformula \<psi>) = (map reopt_table zs0, Rep_udformula \<psi>')"
    using 20(2)[OF refl \<phi>[symmetric] refl] \<psi> by simp
  have IH3: "edeval j ts (rdb ?db0) (Rep_udformula \<rho>) = (map reopt_table rs, Rep_udformula \<rho>')"
    using 20(3)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric] refl refl refl refl] \<rho> by simp
  have IH4: "fst (edeval j [] (rdb (Mapping.update (p, m) (replicate ?c \<alpha>) ?dbe)) (Rep_udformula \<rho>')) =
    map reopt_table (fst (udeval j [] (Mapping.update (p, m) (replicate ?c \<alpha>) ?dbe) \<rho>'))" for \<alpha>
    using 20(4)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric] refl refl refl refl refl \<rho>[symmetric]
        refl refl refl refl refl, of \<alpha>]
    by (simp split: prod.splits)
  obtain ys \<alpha>s' where fr0: "freeze_meval0 (\<lambda>\<alpha>. ((rb @ rs) @
      fst (udeval j [] (Mapping.update (p, m) (replicate ?c \<alpha>) ?dbe) \<rho>'), ())) ?k ?as = (ys, \<alpha>s')"
    by (cases "freeze_meval0 (\<lambda>\<alpha>. ((rb @ rs) @
      fst (udeval j [] (Mapping.update (p, m) (replicate ?c \<alpha>) ?dbe) \<rho>'), ())) ?k ?as")
  have fr: "freeze_meval0 (\<lambda>\<alpha>. (map reopt_table (rb @ rs) @
      fst (edeval j [] (Mapping.update (p, m) (replicate ?c \<alpha>) (rdb ?dbe)) (Rep_udformula \<rho>')), ()))
      ?k (map reopt_table ?as) = (map reopt_table ys, map reopt_table \<alpha>s')"
  proof -
    have "freeze_meval0 (\<lambda>\<alpha>. (map reopt_table (rb @ rs) @
      fst (edeval j [] (Mapping.update (p, m) (replicate ?c \<alpha>) (rdb ?dbe)) (Rep_udformula \<rho>')), ()))
      ?k (map reopt_table ?as) = (case freeze_meval0 (\<lambda>\<alpha>. ((rb @ rs) @
      fst (udeval j [] (Mapping.update (p, m) (replicate ?c \<alpha>) ?dbe) \<rho>'), ())) ?k ?as of
        (ys, \<alpha>s') \<Rightarrow> (map reopt_table ys, map reopt_table \<alpha>s'))"
      by (rule freeze_meval0_rdb) (simp add: IH4[symmetric])
    then show ?thesis
      unfolding fr0 by simp
  qed
  let ?a = "frz_adv d w (jfrz + length (drop (jfrz - jpsi0) zs0) + length ys) j (if d = \<infinity> then [] else tq @ ts)"
  obtain rs2 \<rho>2 where adv: "udeval j [] (Mapping.update (p, m) (replicate ?a {}) ?dbe) \<rho>' = (rs2, \<rho>2)"
    by (cases "udeval j [] (Mapping.update (p, m) (replicate ?a {}) ?dbe) \<rho>'")
  have IH5: "edeval j [] (rdb (Mapping.update (p, m) (replicate ?a {}) ?dbe)) (Rep_udformula \<rho>') =
    (map reopt_table rs2, Rep_udformula \<rho>2)"
    using 20(5)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric] refl refl refl refl refl \<rho>[symmetric]
        refl refl refl refl refl refl fr0[symmetric] refl refl refl refl] adv
    by simp
  show ?case
    by (simp only: Rep_udformula.simps edeval.simps udeval.simps Let_def rdb_update_Nil rdb_map_values_Nil
        rdb_update_replicate_empty IH1 IH2 IH3 map_append[symmetric] drop_map length_map \<phi> \<psi> \<rho> fr fr0 adv IH5
        prod.case)
next
  case (21 j ts db p m \<phi> \<psi> i buf)
  have IH: "size \<psi> = size \<phi> \<Longrightarrow> edeval j ts (rdb db) (Rep_udformula \<psi>) =
    (case udeval j ts db \<psi> of (zs, \<psi>') \<Rightarrow> (map reopt_table zs, Rep_udformula \<psi>'))" for ts db \<psi>
    using 21 by auto
  have lp: "letpast_meval0 (edeval j) j i [] (list_of_option (map_option reopt_table buf)) (p, m) ts
      (rdb db) (Rep_udformula \<phi>)
    = (case letpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi> of
        (ys', i', b, \<phi>') \<Rightarrow> (map reopt_table ys', i', map_option reopt_table b, Rep_udformula \<phi>'))"
    using letpast_meval0_rdb[where R = Rep_udformula and n = "size \<phi>" and eval = "edeval j"
        and eval' = "udeval j" and j = j and i = i and ys = "[]" and xs = "list_of_option buf"
        and p = "(p, m)" and ts = ts and db = db and \<phi> = \<phi>,
        OF size_snd_edeval size_snd_udeval IH refl]
    by (cases buf) simp_all
  show ?case
    using 21(2)[OF refl _ refl refl]
    by (cases "letpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>")
      (auto simp: lp split: prod.splits)
next
  case (1 j ts db)
  then show ?case by simp
next
  case (2 j ts db rel)
  then show ?case by simp
next
  case (3 j ts db e ar)
  then show ?case by (simp add: empty_table_def split: option.splits)
next
  case (4 j ts db e ar tms cs)
  then show ?case by (simp add: empty_table_def dmatch_table_reopt_table split: option.splits)
next
  case (5 j ts db \<phi> conf)
  then show ?case by (simp add: filter_deval_constraint_reopt_table split: prod.splits)
next
  case (6 j ts db \<phi>)
  then show ?case by (simp add: neg_reopt_table split: prod.splits)
next
  case (7 j ts db \<phi> drop0)
  then show ?case by (simp split: prod.splits)
next
  case (8 j ts db g0 \<omega> f k pos \<phi>)
  then show ?case by (simp add: dagg_reopt_table split: prod.splits)
next
  case (9 j ts db \<phi> \<psi> buf)
  then show ?case by (simp add: mebuf2_add_rbuf mebuf2_take_or split: prod.splits)
next
  case (10 j ts db pl \<phi> pos \<psi> buf)
  then show ?case by (simp add: mebuf2_add_rbuf mebuf2_take_and split: prod.splits)
next
  case (11 j ts db I \<phi> first buf nts)
  then show ?case
    by (simp add: meprev_next_prev empty_table_def
        del: meprev_next.simps ueprev_next.simps split: prod.splits)
next
  case (12 j ts db I \<phi> first nts)
  then show ?case
    by (simp add: meprev_next_next1 meprev_next_next2 meprev_next_next3
        del: meprev_next.simps ueprev_next.simps split: prod.splits list.splits bool.splits)
next
  case (14 j ts db dags \<phi> \<psi> buf aux)
  obtain xs \<phi>' where e1: "udeval j ts db \<phi> = (xs, \<phi>')" by (cases "udeval j ts db \<phi>")
  obtain ys \<psi>' where e2: "udeval j ts db \<psi> = (ys, \<psi>')" by (cases "udeval j ts db \<psi>")
  obtain zs buf' aux' where e3: "uedsx_eval_since dags [] (uebuf2S_add xs ys ts buf) aux
      = (zs, buf', aux')"
    by (cases "uedsx_eval_since dags [] (uebuf2S_add xs ys ts buf) aux")
  obtain Zs Bf Ax where E3: "edsx_eval_since dags [] (rbufS (uebuf2S_add xs ys ts buf)) (rdsx aux)
      = (Zs, Bf, Ax)"
    by (cases "edsx_eval_since dags [] (rbufS (uebuf2S_add xs ys ts buf)) (rdsx aux)")
  have Z: "map (dfilt (usx_q aux)) Zs = map reopt_table zs" and B: "Bf = rbufS buf'"
    and A: "Ax = rdsx aux'"
    using edsx_eval_since_rdsx0[where args = dags and buf = "uebuf2S_add xs ys ts buf" and aux = aux] by (simp_all add: e3 E3)
  have q: "usx_q aux' = usx_q aux" by (rule usx_q_uedsx_eval_since'[OF e3])
  show ?case
    using 14
    by (simp add: e1 e2 e3 E3 Z B A q mebuf2S_add_rbufS edeval_edandrel
        del: edsx_eval_since.simps uedsx_eval_since.simps split: prod.splits)
next
  case (15 j ts db dags msk \<phi> \<psi> buf nts t aux)
  then show ?case
    by (simp add: mebuf2_add_rbuf mebuf2t_take_until dux_eval_rdux split: prod.splits)
next
  case (16 j ts db p t \<phi>)
  then show ?case by (simp add: dassign_reopt_table split: prod.splits)
next
  case (17 j ts db mt i)
  then show ?case by (simp add: dmtrm_umtrm)
next
  case (18 j ts db mt)
  then show ?case by (simp add: dmtrm_umtrm)
next
  case (19 j ts db p m \<phi> \<psi>)
  then show ?case by (auto split: prod.splits)
next
  case (22 j ts db dags pl \<phi> \<psi> dbuf nts daux)
  then show ?case
    by (simp add: mebuf2_add_rbuf mebuf2T_take_trigger
        del: mebuf2T_take.simps uebuf2T_take.simps split: prod.splits)
next
  case (23 j ts db m I mr mrs pls Ld dbuf nts daux)
  have R: "map fst (map (edeval j ts (rdb db)) (map Rep_udformula Ld))
      = map (map reopt_table) (map fst (map (udeval j ts db) Ld))"
    "map snd (map (edeval j ts (rdb db)) (map Rep_udformula Ld))
      = map Rep_udformula (map snd (map (udeval j ts db) Ld))"
    by (auto simp: 23 split: prod.splits)
  let ?F = "\<lambda>rels t (zs, ax).
      (case gupdate_matchP (map emb_msk pls) I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax))"
  let ?B = "uebufn_add (map fst (map (udeval j ts db) Ld)) dbuf"
  obtain zs daux' dbuf' tt nts' where U:
    "uebufnt_take ?F (mbuf_t_empty, daux) ?B 0 (nts @@ ts) = ((zs, daux'), dbuf', tt, nts')"
    by (cases "uebufnt_take ?F (mbuf_t_empty, daux) ?B 0 (nts @@ ts)") auto
  have E: "mebufnt_take ?F (mbuf_t_empty, rmrd daux) (map (map_mbuf reopt_table) ?B) 0 (nts @@ ts)
      = ((map_mbuf reopt_table zs, rmrd daux'), map (map_mbuf reopt_table) dbuf', tt, nts')"
    by (rule mebufnt_take_matchP'[OF U])
  have Z: "map dsan (Rep_mbuf_t (map_mbuf reopt_table zs)) = map reopt_table (Rep_mbuf_t zs)"
    by simp
  show ?case
    by (simp only: Let_def edeval.simps udeval.simps R mebufn_add_map_mbuf U E
        prod.case Z Rep_udformula.simps)
next
  case (24 j ts db m I mr mrs pls Ld dbuf nts t daux)
  have R: "map fst (map (edeval j ts (rdb db)) (map Rep_udformula Ld))
      = map (map reopt_table) (map fst (map (udeval j ts db) Ld))"
    "map snd (map (edeval j ts (rdb db)) (map Rep_udformula Ld))
      = map Rep_udformula (map snd (map (udeval j ts db) Ld))"
    by (auto simp: 24 split: prod.splits)
  let ?F = "\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels"
  let ?B = "uebufn_add (map fst (map (udeval j ts db) Ld)) dbuf"
  obtain daux' dbuf' nt nts' where U:
    "uebufnt_take ?F daux ?B t (nts @@ ts) = (daux', dbuf', nt, nts')"
    by (cases "uebufnt_take ?F daux ?B t (nts @@ ts)") auto
  have E: "mebufnt_take ?F (rmld daux) (map (map_mbuf reopt_table) ?B) t (nts @@ ts)
      = (rmld daux', map (map_mbuf reopt_table) dbuf', nt, nts')"
    by (rule mebufnt_take_matchF'[OF U])
  obtain zs daux'' where V: "geval_matchF I mr nt daux' = (zs, daux'')"
    by (cases "geval_matchF I mr nt daux'") auto
  have V': "geval_matchF I mr nt (rmld daux') = (map reopt_table zs, rmld daux'')"
    by (simp add: geval_matchF_reopt V)
  have Z: "map dsan (map reopt_table zs) = map reopt_table zs"
    by simp
  show ?case
    by (simp only: Let_def edeval.simps udeval.simps R mebufn_add_map_mbuf U E V V'
        prod.case Z Rep_udformula.simps)
next
  case (25 j ts db pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux)
  then show ?case
    by (simp add: mebuf2_add_rbuf mebuf2_add_map_prod mebuf2T_take_andtrigger
        mebuf2_take_andtrigger
        del: mebuf2T_take.simps uebuf2T_take.simps mebuf2_take.simps split: prod.splits)
qed

subsection \<open>The compiler, the state and the step\<close>

text \<open>
  A constraint over a node whose result is an aggregate becomes the node's guard rather than a
  filter above it, when the node is a fused aggregating Since: the constraint is on the node's
  own columns, which are exactly the aggregation's, so the groups that fail it never have to be
  built.  Nothing else is fused -- every other node keeps the filter above it -- and the boxed
  compiler of @{theory MFODL_Monitor_Dense.Dense_Descend_Code} keeps it above this one too,
  which is what @{const edandrel} in @{const Rep_udformula} says.
\<close>

fun uset_q :: "uconstr \<Rightarrow> udformula \<Rightarrow> udformula option" where
  "uset_q c (UDSince args \<phi> \<psi> buf aux) =
     (case aux of UDSX_wagg p None a \<Rightarrow> Some (UDSince args \<phi> \<psi> buf (UDSX_wagg p (Some c) a))
      | _ \<Rightarrow> None)"
| "uset_q c \<phi> = None"

lemma Rep_uset_q:
  "uset_q c d = Some d' \<Longrightarrow> Rep_udformula d' = EDAndRel (Rep_udformula d) c"
  by (cases d) (auto simp: edandrel_def split: udsaux_x.splits option.splits)

text \<open>The compiler of @{theory MFODL_Monitor_Dense.Dense_Descend_Code} into the short formula: the
  same placement, with the structures initialised on short tuples.\<close>

function (sequential) udof ::
    "nat \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) meformula \<Rightarrow> udformula" where
  "udof n cs (meformula.MRel rel) = UDRel (deopt_table (dtabc n cs rel))"
| "udof n cs (meformula.MPred e tms mode) =
     (if mode = Match then UDPredM e (length tms) tms cs
      else if (mode = Copy \<and> tms = map Formula.Var [0..<n] \<and> cs = [0..<n])
           \<or> (mode = Simple \<and> is_simple_pattern tms 0 \<and> cs = smp_cols tms)
      then UDPredS e (length tms)
      else UDFail)"
| "udof n cs (meformula.MAndRel \<phi> conf) =
     (if Formula.fv_trm (fst conf) \<subseteq> set cs \<and> Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
      then (let d = udof n cs \<phi>; c = reindex_constraint cs conf
            in case uset_q c d of Some d' \<Rightarrow> d' | None \<Rightarrow> UDAndRel d c)
      else UDFail)"
| "udof n cs (meformula.MNeg \<phi>) =
     (if cs = [] then UDNeg (udof n [] \<phi>)
      else UDFail)"
| "udof n cs (meformula.MExists \<phi>) = UDExists (udof (Suc n) (0 # map Suc cs) \<phi>) True"
| "udof n cs (meformula.MOr \<phi> \<psi> buf) =
     (if mbuf_t_is_empty (fst buf) \<and> mbuf_t_is_empty (snd buf)
      then UDOr (udof n cs \<phi>) (udof n cs \<psi>) (mbuf_t_empty, mbuf_t_empty) else UDFail)"
| "udof n cs (meformula.MAnd A \<phi> pos B \<psi> buf) =
     (let cs1 = set_cols A; cs2 = set_cols B in
      if cs = merge_cols cs1 cs2 \<and> (pos \<or> B \<subseteq> A) \<and>
         mbuf_t_is_empty (fst buf) \<and> mbuf_t_is_empty (snd buf)
      then UDAnd (mk_djoin cs1 cs2) (udof n cs1 \<phi>) pos (udof n cs2 \<psi>)
             (mbuf_t_empty, mbuf_t_empty)
      else UDFail)"
| "udof n cs (meformula.MPrev I \<phi> first buf nts) =
     (if mbuf_t_is_empty buf then UDPrev I (udof n cs \<phi>) first mbuf_t_empty nts else UDFail)"
| "udof n cs (meformula.MNext I \<phi> first nts) =
     UDNext I (udof n cs \<phi>) first nts"
| "udof n cs (meformula.MAnds A_pos A_neg L buf) =
     (case A_pos of [] \<Rightarrow> UDFail
      | A # As \<Rightarrow>
        (let c0 = set_cols A; css = map set_cols As; nss = map set_cols A_neg in
         if cs = dands_cols c0 css \<and> length L = length A_pos + length A_neg \<and>
            list_all mbuf_t_is_empty buf
         then UDAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
                (map2 (udof n) (c0 # css @ nss) L) (map (\<lambda>_. mbuf_t_empty) L)
         else UDFail))"
| "udof n cs (meformula.MAgg args \<phi>) =
     (let m = length (aggargs_tys args); g = dagg_gcols args; y = aggargs_y args in
      if cs = merge_cols g [y] \<and> set_cols (aggargs_cols args) = agg_cols m g
      then UDAgg (aggargs_g0 args) (aggargs_\<omega> args)
             (reindex_trm (agg_cols m g) (aggargs_f args)) m (ins_pos g y)
             (udof (m + n) (agg_cols m g) \<phi>)
      else UDFail)"
| "udof n cs (meformula.MSince args \<phi> \<psi> buf aux) =
     (let cs_L = set_cols (args_L args); cs_R = set_cols (args_R args);
          \<phi>d = udof (dnode_n n args) cs_L \<phi>; \<psi>d = udof (dnode_n n args) cs_R \<psi>;
          bf = (case buf of (a, b, c, d) \<Rightarrow> (Rep_mbuf_t a, Rep_mbuf_t b, Rep_mbuf_t c, d)) in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> cs = cs_R \<and> set cs_L \<subseteq> set cs_R \<and> bf = init_mbuf2S
           then UDSince (dargs cs cs_L args) \<phi>d \<psi>d init_mebuf2S
                  (udsx_init (dargs cs cs_L args) (dmsk cs cs_L))
           else UDFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if args_n args = m + aggargs_n ag \<and> aggargs_n ag = n \<and> set cs_L \<subseteq> set cs_R \<and>
              bf = init_mbuf2S \<and> agg_cols m g = cs_R \<and> cs = merge_cols g [y] \<and>
              wf_cols n g \<and> y < n \<and> y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and>
              Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R
           then (if cpos cs_R (set cs_L) = {}
                 then UDSince (dargs cs_R cs_L args) \<phi>d \<psi>d init_mebuf2S
                        (udsx_init_agg (dargs cs_R cs_L args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
                           m, ins_pos g y) None)
                 else UDAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
                        m (ins_pos g y)
                        (UDSince (dargs cs_R cs_L args) \<phi>d \<psi>d init_mebuf2S
                          (udsx_init (dargs cs_R cs_L args) (dmsk cs_R cs_L))))
           else UDFail))"
| "udof n cs (meformula.MUntil args \<phi> \<psi> buf nts t aux) =
     (let cs_L = set_cols (args_L args); cs_R = set_cols (args_R args);
          \<phi>d = udof (dnode_n n args) cs_L \<phi>; \<psi>d = udof (dnode_n n args) cs_R \<psi> in
      case args_agg args of
        None \<Rightarrow>
          (if args_n args = n \<and> cs = cs_R \<and> set cs_L \<subseteq> set cs_R \<and>
              map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and> Rep_mbuf_t nts = [] \<and> t = 0
           then UDUntil (dargs cs cs_L args) (dmsk cs cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                  mbuf_t_empty 0 (udux_init (dargs cs cs_L args))
           else UDFail)
      | Some ag \<Rightarrow>
          (let m = length (aggargs_tys ag); g = dagg_gcols ag; y = aggargs_y ag in
           if args_n args = m + aggargs_n ag \<and> aggargs_n ag = n \<and> set cs_L \<subseteq> set cs_R \<and>
              map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and> Rep_mbuf_t nts = [] \<and> t = 0 \<and>
              agg_cols m g = cs_R \<and> cs = merge_cols g [y] \<and>
              wf_cols n g \<and> y < n \<and> y \<notin> set g \<and> (aggargs_g0 ag \<longrightarrow> g = []) \<and>
              Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R
           then (if cpos cs_R (set cs_L) = {} \<and> memL (args_ivl args) 0
                 then UDUntil (dargs cs_R cs_L args) (dmsk cs_R cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0
                        (udux_init_agg (dargs cs_R cs_L args)
                          (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
                           m, ins_pos g y))
                 else UDAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
                  m (ins_pos g y)
                  (UDUntil (dargs cs_R cs_L args) (dmsk cs_R cs_L) \<phi>d \<psi>d
                    (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0
                    (udux_init (dargs cs_R cs_L args))))
           else UDFail))"
| "udof n cs (meformula.MAndAssign \<phi> conf) =
     (let y = fst conf; t = snd conf; cs0 = rem_col cs y in
      if y \<in> set cs \<and> Formula.fv_trm t \<subseteq> set cs0
      then UDAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) (udof n cs0 \<phi>)
      else UDFail)"
| "udof n cs (meformula.MLet p m \<phi> \<psi>) = UDLet p m (udof m [0..<m] \<phi>) (udof n cs \<psi>)"
| "udof n cs (meformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po) =
     (if \<alpha>s = [] \<and> rb = [] then UDFrz p m (udof m [0..<m] \<phi>) (udof n cs \<psi>) jfrz jpsi0 jphi []
        (udof n cs \<rho>) w pR tq [] d po else UDFail)"
| "udof n cs (meformula.MLetPast p m \<phi> \<psi> i buf) =
     (if buf = None then UDLetPast p m (udof m [0..<m] \<phi>) (udof n cs \<psi>) i None else UDFail)"
| "udof n cs (meformula.MTrigger args \<phi> \<psi> buf nts aux) =
     (let cs_L = set_cols (args_L args) in
      if args_n args = n \<and> args_R args = set cs \<and> set cs_L \<subseteq> set cs \<and>
         mem (args_ivl args) 0 \<and> map_prod Rep_mbuf_t Rep_mbuf_t buf = ([], []) \<and>
         Rep_mbuf_t nts = []
      then UDTrigger (dargs cs cs_L args) (emb_plan cs cs_L)
             (udof n cs_L \<phi>) (udof n cs \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (ginit_mmtaux (dargs cs cs_L args) (dmsk cs cs_L))
      else UDFail)"
| "udof n cs (meformula.MAndTrigger A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) =
     (let cs_R = set_cols (args_R args); cs_L = set_cols (args_L args) in
      if args_n args = n \<and> cs = set_cols A \<and> set cs_R \<subseteq> set cs \<and> set cs_L \<subseteq> set cs_R \<and>
         tok cs_R cs_L args \<and> mbuf_t_is_empty (fst buf1) \<and> mbuf_t_is_empty (snd buf1) \<and>
         mbuf_t_is_empty (fst buf2) \<and> mbuf_t_is_empty (snd buf2) \<and> mbuf_t_is_empty nts
      then UDAndTrigger (mk_djoin cs cs_R) (udof n cs \<alpha>) (mbuf_t_empty, mbuf_t_empty)
             (dargs cs_R cs_L args) (udof n cs_L \<phi>) (udof n cs_R \<psi>)
             (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
             (ginit_mmtaux (dargs cs_R cs_L args) (dmsk cs_R cs_L))
      else UDFail)"
| "udof n cs (meformula.MTP mt i) =
     (if cs = mtrm_dcols mt then UDTP mt i
      else UDFail)"
| "udof n cs (meformula.MTS mt) =
     (if cs = mtrm_dcols mt then UDTS mt
      else UDFail)"
| "udof n cs (meformula.MMatchP I mr mrs L buf nts aux) =
     (case those (map (emfcols n) L) of None \<Rightarrow> UDFail
      | Some css \<Rightarrow>
        (if length buf = length L \<and> list_all mbuf_t_is_empty buf \<and> aux = [] \<and>
            (\<forall>c \<in> set css. set c \<subseteq> set cs)
         then UDMatchP (length cs) I mr mrs (map (emb_plan cs) css) (map2 (udof n) css L)
                (map (\<lambda>_. mbuf_t_empty) L) nts []
         else UDFail))"
| "udof n cs (meformula.MMatchF I mr mrs L buf nts t aux) =
     (case those (map (emfcols n) L) of None \<Rightarrow> UDFail
      | Some css \<Rightarrow>
        (if length buf = length L \<and> list_all mbuf_t_is_empty buf \<and> aux = [] \<and>
            (\<forall>c \<in> set css. set c \<subseteq> set cs)
         then UDMatchF (length cs) I mr mrs (map (emb_plan cs) css) (map2 (udof n) css L)
                (map (\<lambda>_. mbuf_t_empty) L) nts t []
         else UDFail))"
  by pat_completeness safe

termination udof
  by (relation "measure (\<lambda>(n, cs, \<phi>). size \<phi>)")
    (auto simp: termination_simp dest!: set_zip_rightD)

lemma udof_edof: "Rep_udformula (udof n cs e) = edof n cs e"
proof (induct n cs e rule: udof.induct)
  case (3 n cs \<phi> conf)
  then show ?case
    by (auto simp: Let_def Rep_uset_q split: option.splits)
next
  case (12 n cs args \<phi> \<psi> buf aux)
  then show ?case
    by (cases "args_agg args") (simp_all add: Let_def dsx_init_rdsx dsx_init_agg_rdsx)
next
  case (13 n cs args \<phi> \<psi> buf nts t aux)
  then show ?case
    by (cases "args_agg args") (simp_all add: Let_def dux_init_rdux dux_init_agg_rdux)
next
  case (19 n cs A \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)
  then show ?case by (auto simp: Let_def ginit_mmtaux_bmm[symmetric])
qed (simp_all add: Let_def dsan_def dsx_init_rdsx ginit_mmtaux_bmm[symmetric] zip_map2 o_def
      split: list.splits option.splits prod.splits cong: map_cong)

text \<open>The kernel's executable formula, rebuilt from the specification's: the inverse of
  @{const Rep_meformula}, so that the compiler can be stated on the specification's state and
  run on the executable one.\<close>

fun Abs_meformula :: "('msaux, 'muaux, 'mtaux) mformula \<Rightarrow> ('msaux, 'muaux, 'mtaux) meformula" where
  "Abs_meformula (mformula.MRel rel) = MRel rel"
| "Abs_meformula (mformula.MPred e tms mode) = MPred e tms mode"
| "Abs_meformula (mformula.MLet p m \<phi> \<psi>) = MLet p m (Abs_meformula \<phi>) (Abs_meformula \<psi>)"
| "Abs_meformula (mformula.MFrz p m \<phi> \<psi> i j k \<alpha> \<rho> w pR tq rb d po) =
    MFrz p m (Abs_meformula \<phi>) (Abs_meformula \<psi>) i j k \<alpha> (Abs_meformula \<rho>) w pR tq rb d po"
| "Abs_meformula (mformula.MLetPast p m \<phi> \<psi> i buf) = MLetPast p m (Abs_meformula \<phi>) (Abs_meformula \<psi>) i buf"
| "Abs_meformula (mformula.MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf) =
     MAnd A_\<phi> (Abs_meformula \<phi>) pos A_\<psi> (Abs_meformula \<psi>) (map_prod Abs_mbuf_t Abs_mbuf_t buf)"
| "Abs_meformula (mformula.MAndAssign \<phi> conf) = MAndAssign (Abs_meformula \<phi>) conf"
| "Abs_meformula (mformula.MAndRel \<phi> conf) = MAndRel (Abs_meformula \<phi>) conf"
| "Abs_meformula (mformula.MAndTrigger fv\<phi> \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
     MAndTrigger fv\<phi> (Abs_meformula \<phi>) (map_prod Abs_mbuf_t Abs_mbuf_t buf1) args (Abs_meformula \<phi>')
       (Abs_meformula \<psi>') (map_prod Abs_mbuf_t Abs_mbuf_t buf2) (Abs_mbuf_t nts) aux"
| "Abs_meformula (mformula.MAnds A_pos A_neg L buf) =
     MAnds A_pos A_neg (map Abs_meformula L) (map Abs_mbuf_t buf)"
| "Abs_meformula (mformula.MOr \<phi> \<psi> buf) =
     MOr (Abs_meformula \<phi>) (Abs_meformula \<psi>) (map_prod Abs_mbuf_t Abs_mbuf_t buf)"
| "Abs_meformula (mformula.MNeg \<phi>) = MNeg (Abs_meformula \<phi>)"
| "Abs_meformula (mformula.MExists \<phi>) = MExists (Abs_meformula \<phi>)"
| "Abs_meformula (mformula.MAgg args \<phi>) = MAgg args (Abs_meformula \<phi>)"
| "Abs_meformula (mformula.MPrev I \<phi> first buf nts) =
     MPrev I (Abs_meformula \<phi>) first (Abs_mbuf_t buf) (Abs_mbuf_t nts)"
| "Abs_meformula (mformula.MNext I \<phi> first nts) = MNext I (Abs_meformula \<phi>) first (Abs_mbuf_t nts)"
| "Abs_meformula (mformula.MSince args \<phi> \<psi> buf aux) =
     MSince args (Abs_meformula \<phi>) (Abs_meformula \<psi>)
       (case buf of (a, b, c, d) \<Rightarrow> (Abs_mbuf_t a, Abs_mbuf_t b, Abs_mbuf_t c, d)) aux"
| "Abs_meformula (mformula.MUntil args \<phi> \<psi> buf nts t aux) =
     MUntil args (Abs_meformula \<phi>) (Abs_meformula \<psi>) (map_prod Abs_mbuf_t Abs_mbuf_t buf)
       (Abs_mbuf_t nts) t aux"
| "Abs_meformula (mformula.MTrigger args \<phi> \<psi> buf nts aux) =
     MTrigger args (Abs_meformula \<phi>) (Abs_meformula \<psi>) (map_prod Abs_mbuf_t Abs_mbuf_t buf)
       (Abs_mbuf_t nts) aux"
| "Abs_meformula (mformula.MMatchP I mr mrs \<phi>s buf nts aux) =
     MMatchP I mr mrs (map Abs_meformula \<phi>s) (map Abs_mbuf_t buf) (Abs_mbuf_t nts) aux"
| "Abs_meformula (mformula.MMatchF I mr mrs \<phi>s buf nts t aux) =
     MMatchF I mr mrs (map Abs_meformula \<phi>s) (map Abs_mbuf_t buf) (Abs_mbuf_t nts) t aux"
| "Abs_meformula (mformula.MTP mt i) = MTP mt i"
| "Abs_meformula (mformula.MTS mt) = MTS mt"

lemma Rep_Abs_mbuf_t[simp]: "Rep_mbuf_t (Abs_mbuf_t xs) = xs"
  by (rule Abs_mbuf_t_inverse) simp

lemma Rep_Abs_meformula[simp]: "Rep_meformula (Abs_meformula m) = m"
  by (induct m) (auto simp: comp_def map_prod_def Rep_mbuf_t_inverse split: prod.splits
      intro: map_idI)

lemma Abs_Rep_meformula[simp]: "Abs_meformula (Rep_meformula e) = e"
  by (induct e) (auto simp: comp_def map_prod_def Rep_mbuf_t_inverse split: prod.splits
      intro: map_idI)

definition udof_m :: "nat \<Rightarrow> cols \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> udformula" where
  "udof_m n cs m = udof n cs (Abs_meformula m)"

lemma udof_m_code[code]: "udof_m n cs (Rep_meformula e) = udof n cs e"
  by (simp add: udof_m_def)

lemma udof_m_dof: "Rep_edformula (Rep_udformula (udof_m n cs m)) = dof n cs m"
  by (simp add: udof_m_def udof_edof edof_dof)

record udmstate =
  udmstate_i :: nat
  udmstate_j :: nat
  udmstate_m :: udformula
  udmstate_n :: nat
  udmstate_cs :: cols
  udmstate_t :: "ts mbuf_t"

definition Rep_udmstate :: "udmstate \<Rightarrow> dmstate" where
  "Rep_udmstate st =
     \<lparr> dmstate_i = udmstate_i st, dmstate_j = udmstate_j st,
       dmstate_m = Rep_edformula (Rep_udformula (udmstate_m st)),
       dmstate_n = udmstate_n st, dmstate_cs = udmstate_cs st, dmstate_t = udmstate_t st \<rparr>"

definition udof_state :: "nat \<Rightarrow> cols \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mstate \<Rightarrow> udmstate" where
  "udof_state n cs st =
     \<lparr> udmstate_i = mstate_i st, udmstate_j = mstate_j st,
       udmstate_m = udof_m n cs (mstate_m st),
       udmstate_n = n, udmstate_cs = cs, udmstate_t = mbuf_t_empty @@ mstate_t st \<rparr>"

lemma Rep_udof_state: "Rep_udmstate (udof_state n cs st) = dof_state n cs st"
  by (simp add: Rep_udmstate_def udof_state_def dof_state_def udof_m_dof)

definition udminit_safe :: "ty Formula.formula \<Rightarrow> udmstate" where
  "udminit_safe \<phi> = udof_state (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) (minit_safe \<phi>)"

lemma Rep_udminit_safe:
  "Rep_udmstate (udminit_safe \<phi>) = dof_state (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) (minit_safe \<phi>)"
  by (simp add: udminit_safe_def Rep_udof_state)

lemma vdfail_nodes_Rep_udmstate:
  "vdfail_nodes (dmstate_m (Rep_udmstate st)) = uvdfail_nodes (udmstate_m st)"
  by (simp add: Rep_udmstate_def vdfail_nodes_Rep evdfail_nodes_Rep)

definition udmstep :: "udatabase \<times> ts \<Rightarrow> udmstate \<Rightarrow> (nat \<times> ts \<times> utable) list \<times> udmstate" where
  "udmstep tdb st =
    (case udeval (udmstate_j st + 1) [snd tdb] (fst tdb) (udmstate_m st) of
      (xs, m) \<Rightarrow>
      (case dannotate (udmstate_i st) (udmstate_t st @@ [snd tdb]) xs [] of
        (i', tq, vs) \<Rightarrow> (vs,
        \<lparr> udmstate_i = i',
          udmstate_j = udmstate_j st + 1,
          udmstate_m = m,
          udmstate_n = udmstate_n st,
          udmstate_cs = udmstate_cs st,
          udmstate_t = tq \<rparr>)))"

lemma dannotate_map:
  "dannotate i tq (map g vs) (map (\<lambda>(i, t, v). (i, t, g v)) acc)
   = (case dannotate i tq vs acc of (i', tq', vs') \<Rightarrow> (i', tq', map (\<lambda>(i, t, v). (i, t, g v)) vs'))"
proof (induct vs arbitrary: i tq acc)
  case (Cons v vs)
  obtain a tq0 where h: "mbuf_t_cases tq = (a, tq0)" by (cases "mbuf_t_cases tq")
  show ?case
  proof (cases a)
    case None
    then show ?thesis by (simp add: h rev_map)
  next
    case (Some t)
    show ?thesis
      using Cons[of "i + 1" tq0 "(i, t, v) # acc"] by (simp add: h Some split: prod.splits)
  qed
qed (simp add: rev_map)

theorem udmstep_Rep:
  "dmstep (rdb db, t) (Rep_udmstate st)
   = (case udmstep (db, t) st of
        (vs, st') \<Rightarrow> (map (\<lambda>(i, t, X). (i, t, reopt_table X)) vs, Rep_udmstate st'))"
proof -
  obtain xs m where e: "udeval (Suc (udmstate_j st)) [t] db (udmstate_m st) = (xs, m)"
    by (cases "udeval (Suc (udmstate_j st)) [t] db (udmstate_m st)")
  obtain i' tq vs where d: "dannotate (udmstate_i st) (udmstate_t st @@ [t]) xs [] = (i', tq, vs)"
    by (metis prod_cases3)
  show ?thesis
    unfolding dmstep_def udmstep_def Rep_udmstate_def
    by (simp add: edeval_Rep udeval_Rep e dannotate_map[where acc = "[]", simplified] d)
qed

(*<*)
end
(*>*)
