(*<*)
theory Dense_Unbox_Exec
  imports Dense_Agg_Cache
begin
(*>*)

section \<open>The verified dense evaluator, on short tuples\<close>

text \<open>
  @{const deval} evaluates over tables of @{typ "event_data tuple"}, every field boxed in an
  option that never holds @{const None}, and buffers them in lists.  This theory states the same
  evaluator over tables of @{typ "event_data list"}, with its buffers in queues
  (@{typ "'a mbuf_t"}): every node keeps its tables and structures on short tuples, and every
  operation is the generic one at @{typ event_data}, or the twin of the field reader of
  @{theory MFODL_Monitor_Dense.Dense_Utuple}.  The theorem @{text udeval_Rep} at the end says
  that the two evaluators agree exactly: embedding the state and the database, running
  @{const deval}, is running @{text udeval} and embedding its results.  No invariant is needed,
  because every operation commutes with the embedding on every input (the naturality lemmas of
  @{theory MFODL_Monitor_Dense.Dense_Unbox_Eval}) and every queue operation is the list
  operation read through @{const Rep_mbuf_t}.  So the simulation of the kernel by @{const deval}
  (@{theory MFODL_Monitor_Dense.Dense_Eval}) is a simulation by @{text udeval}, on the embedded
  database, and the generated code runs the latter.
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

lemma mebuf2_take_rbuf:
  assumes "\<And>x y. f (reopt_table x) (reopt_table y) = reopt_table (f' x y)"
  shows "mebuf2_take f (map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) (buf :: uebuf2))
   = (case mebuf2_take f' buf of
        (zs, buf') \<Rightarrow> (map reopt_table zs, map_prod (map_mbuf reopt_table) (map_mbuf reopt_table) buf'))"
  by (cases buf)
    (simp add: mebuf2_take_map_mbuf[where f = f and g = reopt_table and g' = reopt_table and f' = f',
       OF assms] split: prod.splits del: mebuf2_take.simps)

fun rbufS :: "uebuf2S \<Rightarrow> event_data mbuf2S" where
  "rbufS (a, b, c, d) =
     (map reopt_table (Rep_mbuf_t a), map reopt_table (Rep_mbuf_t b), Rep_mbuf_t c, d)"

lemma mbuf2S_add_rbufS:
  "mbuf2S_add (map reopt_table xs) (map reopt_table ys) ts (rbufS buf) = rbufS (uebuf2S_add xs ys ts buf)"
  by (cases buf) (simp add: mbuf_t_append.rep_eq)
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

lemma frz_fill_reopt: "frz_fill ng (map reopt_table \<alpha>s) = reopt_table (frz_fill ng \<alpha>s)"
  by (cases \<alpha>s rule: rev_cases) (simp_all add: frz_fill_def)

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
      udformula nat nat "ts list" "utable list" enat bool bool "nat option" udformula
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

text \<open>A buffer of short tables stands for the list of their boxed versions.\<close>

abbreviation rbl :: "utable mbuf_t \<Rightarrow> event_data table list" where
  "rbl b \<equiv> map reopt_table (Rep_mbuf_t b)"

abbreviation rbuf2 :: "uebuf2 \<Rightarrow> event_data mbuf2" where
  "rbuf2 \<equiv> map_prod (\<lambda>b. rbl b) (\<lambda>b. rbl b)"

text \<open>The same relabelling of a buffer, as a queue: the buffer lemmas are proved on queues first,
  and read back as lists through @{const Rep_mbuf_t}.\<close>

abbreviation qbuf2 :: "uebuf2 \<Rightarrow> event_data mebuf2" where
  "qbuf2 \<equiv> map_prod (map_mbuf reopt_table) (map_mbuf reopt_table)"

text \<open>The trigger's buffers are the short ones like every other node's: its left operand stays
  at its own frame, so nothing it holds has a hole, and @{const bmm} relabels the structure.\<close>

text \<open>A guarded Since node stands for the boxed node read through the constraint: the guard is
  the short evaluator's alone, and the two agree because filtering the whole result is filtering
  the groups as they are read.\<close>

definition dandrel :: "uconstr option \<Rightarrow> dformula \<Rightarrow> dformula" where
  "dandrel q e = (case q of None \<Rightarrow> e | Some c \<Rightarrow> DAndRel e c)"

lemma dandrel_None[simp]: "dandrel None e = e"
  by (simp add: dandrel_def)

lemma deval_dandrel:
  "deval j ts db (dandrel q e)
   = (case deval j ts db e of (zs, e') \<Rightarrow> (map (dfilt q) zs, dandrel q e'))"
  by (simp add: dandrel_def dfilt_Some split: option.splits prod.splits)

lemma vdfail_nodes_dandrel[simp]: "vdfail_nodes (dandrel q e) = vdfail_nodes e"
  by (simp add: dandrel_def split: option.splits)

fun Rep_udformula :: "udformula \<Rightarrow> dformula" where
  "Rep_udformula UDFail = DFail"
| "Rep_udformula (UDRel rel) = DRel (reopt_table rel)"
| "Rep_udformula (UDPredS e ar) = DPredS e ar"
| "Rep_udformula (UDPredM e ar tms cs) = DPredM e ar tms cs"
| "Rep_udformula (UDAndRel \<phi> conf) = DAndRel (Rep_udformula \<phi>) conf"
| "Rep_udformula (UDNeg \<phi>) = DNeg (Rep_udformula \<phi>)"
| "Rep_udformula (UDExists \<phi> b) = DExists (Rep_udformula \<phi>) b"
| "Rep_udformula (UDAgg g0 \<omega> f k pos \<phi>) = DAgg g0 \<omega> f k pos (Rep_udformula \<phi>)"
| "Rep_udformula (UDOr \<phi> \<psi> buf) = DOr (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 buf)"
| "Rep_udformula (UDAnd pl \<phi> pos \<psi> buf) =
     DAnd pl (Rep_udformula \<phi>) pos (Rep_udformula \<psi>) (rbuf2 buf)"
| "Rep_udformula (UDPrev I \<phi> first buf nts) =
     DPrev I (Rep_udformula \<phi>) first (rbl buf) (Rep_mbuf_t nts)"
| "Rep_udformula (UDNext I \<phi> first nts) = DNext I (Rep_udformula \<phi>) first (Rep_mbuf_t nts)"
| "Rep_udformula (UDAnds ps ns L buf) =
     DAnds ps ns (map Rep_udformula L) (map (\<lambda>b. rbl b) buf)"
| "Rep_udformula (UDSince args \<phi> \<psi> buf aux) =
     dandrel (usx_q aux)
       (DSince args (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbufS buf) (rdsx aux))"
| "Rep_udformula (UDUntil args msk \<phi> \<psi> buf nts t aux) =
     DUntil args msk (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 buf) (Rep_mbuf_t nts) t (rdux aux)"
| "Rep_udformula (UDAndAssign p t \<phi>) = DAndAssign p t (Rep_udformula \<phi>)"
| "Rep_udformula (UDTP mt i) = DTP mt i"
| "Rep_udformula (UDTS mt) = DTS mt"
| "Rep_udformula (UDLet p m \<phi> \<psi>) = DLet p m (Rep_udformula \<phi>) (Rep_udformula \<psi>)"
| "Rep_udformula (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     DFrz p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) jfrz jpsi0 jphi (map reopt_table \<alpha>s)
       (Rep_udformula \<rho>) w pR tq (map reopt_table rb) d po ng lv (Rep_udformula \<rho>L)"
| "Rep_udformula (UDLetPast p m \<phi> \<psi> i buf) =
     DLetPast p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) i (map_option reopt_table buf)"
| "Rep_udformula (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     DTrigger dags pl (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbuf) (Rep_mbuf_t nts) (bmm daux)"
| "Rep_udformula (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     DAndTrigger pl (Rep_udformula \<alpha>)
       (map_prod (\<lambda>b. rbl b) (\<lambda>b. map (map_option reopt_table) (Rep_mbuf_t b)) dbf1) dags
       (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbf2) (Rep_mbuf_t nts) (bmm daux)"
| "Rep_udformula (UDMatchP m I mr mrs pls Ld dbuf nts daux) =
     DMatchP m I mr mrs pls (map Rep_udformula Ld) (map (\<lambda>b. rbl b) dbuf) (Rep_mbuf_t nts) (rmrd daux)"
| "Rep_udformula (UDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     DMatchF m I mr mrs pls (map Rep_udformula Ld) (map (\<lambda>b. rbl b) dbuf) (Rep_mbuf_t nts) t (rmld daux)"

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
| "uvdfail_nodes (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
    uvdfail_nodes \<phi> + uvdfail_nodes \<psi> + uvdfail_nodes \<rho>"
| "uvdfail_nodes (UDLetPast p m \<phi> \<psi> i buf) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) = uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     uvdfail_nodes \<alpha> + uvdfail_nodes \<phi> + uvdfail_nodes \<psi>"
| "uvdfail_nodes (UDMatchP m I mr mrs pls L dbuf nts daux) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes (UDMatchF m I mr mrs pls L dbuf nts t daux) = sum_list (map uvdfail_nodes L)"
| "uvdfail_nodes \<phi> = 0"

lemma vdfail_nodes_Rep: "vdfail_nodes (Rep_udformula \<phi>) = uvdfail_nodes \<phi>"
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

lemma dsx_eval_since_rdsx:
  "map (dfilt (usx_q aux)) Rs = map reopt_table rs \<Longrightarrow>
   (case dsx_eval_since args Rs (rbufS buf) (rdsx aux) of
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
    by (cases y; cases x; cases t; simp only: rbufS.simps; subst uedsx_eval_since.simps)
      (auto simp: x y t Let_def rev_map[symmetric] dsx_join_rdsx dsx_add_new_ts_rdsx
        dsx_add_new_table_rdsx dsx_result_rdsx mbuf_t_Cons.rep_eq mbuf_t_empty.rep_eq
        Rep_mbuf_t_cases(1,2)[where xs = ts and xs' = ts'] Rep_mbuf_t_cases(1,2)[where xs = xs and xs' = xs']
        Rep_mbuf_t_cases(1,2)[where xs = ys and xs' = ys']
        simp del: uedsx_eval_since.simps split: prod.splits)
qed
subsection \<open>The evaluator\<close>

subsection \<open>The size of the boxed formula\<close>

text \<open>The guarded Since node stands for two boxed nodes, so the short formula's own size is not
  that of the boxed one it stands for.  The two guards of the evaluator that compare formulas,
  the one keeping the freeze's live copy and the one of the recursive let, compare the size of the
  boxed formula instead, computed on the short one; so they take the boxed evaluator's branches on
  every formula, and the evaluator terminates by the same measure.\<close>

fun ursize :: "udformula \<Rightarrow> nat" where
  "ursize (UDAndRel \<phi> conf) = ursize \<phi> + 1"
| "ursize (UDNeg \<phi>) = ursize \<phi> + 1"
| "ursize (UDExists \<phi> b) = ursize \<phi> + 1"
| "ursize (UDAgg g0 \<omega> f k pos \<phi>) = ursize \<phi> + 1"
| "ursize (UDOr \<phi> \<psi> buf) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDAnd pl \<phi> pos \<psi> buf) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDPrev I \<phi> first buf nts) = ursize \<phi> + 1"
| "ursize (UDNext I \<phi> first nts) = ursize \<phi> + 1"
| "ursize (UDAnds ps ns L buf) = sum_list (map ursize L) + length L + 1"
| "ursize (UDSince args \<phi> \<psi> buf aux) =
     ursize \<phi> + ursize \<psi> + (case usx_q aux of None \<Rightarrow> 1 | Some _ \<Rightarrow> 2)"
| "ursize (UDUntil args msk \<phi> \<psi> buf nts t aux) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDAndAssign p t \<phi>) = ursize \<phi> + 1"
| "ursize (UDLet p m \<phi> \<psi>) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     ursize \<phi> + ursize \<psi> + ursize \<rho> + ursize \<rho>L + 1"
| "ursize (UDLetPast p m \<phi> \<psi> i buf) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) = ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) = ursize \<alpha> + ursize \<phi> + ursize \<psi> + 1"
| "ursize (UDMatchP m I mr mrs pls Ld dbuf nts daux) = sum_list (map ursize Ld) + length Ld + 1"
| "ursize (UDMatchF m I mr mrs pls Ld dbuf nts t daux) = sum_list (map ursize Ld) + length Ld + 1"
| "ursize _ = 0"

lemma size_list_sum_list: "size_list f xs = sum_list (map f xs) + length xs"
  by (induction xs) auto

lemma ursize_Rep: "ursize \<phi> = size (Rep_udformula \<phi>)"
  by (induction \<phi> rule: ursize.induct)
    (auto simp: dandrel_def size_list_sum_list comp_def split: option.splits intro!: arg_cong[of _ _ sum_list])

lemma ursize_in_set: "x \<in> set L \<Longrightarrow> ursize x < Suc (sum_list (map ursize L) + length L)"
  by (induction L) auto

definition ufrz_keep_lv :: "(nat \<times> udformula) option \<Rightarrow> udformula \<Rightarrow> nat option" where
  "ufrz_keep_lv lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if ursize st = ursize \<rho>L then Some g else None
     | None \<Rightarrow> None)"

definition ufrz_keep_st :: "(nat \<times> udformula) option \<Rightarrow> udformula \<Rightarrow> udformula" where
  "ufrz_keep_st lv \<rho>L = (case lv of Some (g, st) \<Rightarrow> if ursize st = ursize \<rho>L then st else \<rho>L
     | None \<Rightarrow> \<rho>L)"

lemma ursize_ufrz_keep_st[simp]: "ursize (ufrz_keep_st lv \<rho>L) = ursize \<rho>L"
  by (auto simp: ufrz_keep_st_def split: option.splits)

lemma frz_keep_Rep:
  "frz_keep_lv (map_option (apsnd Rep_udformula) lv) (Rep_udformula \<rho>L) = ufrz_keep_lv lv \<rho>L"
  "frz_keep_st (map_option (apsnd Rep_udformula) lv) (Rep_udformula \<rho>L) = Rep_udformula (ufrz_keep_st lv \<rho>L)"
  by (auto simp: frz_keep_lv_def frz_keep_st_def ufrz_keep_lv_def ufrz_keep_st_def ursize_Rep
      split: option.splits)

function uletpast_meval0 where
  "uletpast_meval0 eval j i ys xs p ts db \<phi> =
     (let (ys', \<phi>') = eval ts (Mapping.update p xs db) \<phi>
     in if ursize \<phi>' \<noteq> ursize \<phi> then ([], 0, None, \<phi>)
     else (case ys' of
       [] \<Rightarrow> (ys @ ys', i + length xs, None, \<phi>')
     | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j then (ys @ ys', i + length xs, Some y, \<phi>')
         else uletpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))"
  by auto
termination
  by (relation "measure (\<lambda>(_, j, i, _, xs, _). j - (i + length xs))")
    (auto simp: not_le min_def diff_less_mono2)

declare uletpast_meval0.simps[simp del]

lemma uletpast_meval0_cong[fundef_cong]:
  assumes "(\<And>ts db \<psi>. ursize \<psi> = ursize \<phi> \<Longrightarrow> eval ts db \<psi> = eval' ts db \<psi>)"
  shows "uletpast_meval0 eval j i ys xs p ts db \<phi> = uletpast_meval0 eval' j i ys xs p ts db \<phi>"
  using assms
proof (induct eval j i ys xs p ts db \<phi> rule: uletpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  have eval': "eval' ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    using 1(2)[of \<phi>] eval by simp
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval eval' by (subst (1 2) uletpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "uletpast_meval0 eval j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>' =
      uletpast_meval0 eval' j (i + length xs) (ys @ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>'"
      if "ursize \<phi>' = ursize \<phi>" "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] 1(2) that by simp
    then show ?thesis
      using eval eval' Cons by (subst (1 2) uletpast_meval0.simps) (simp add: Let_def)
  qed
qed

lemma ursize_uletpast_meval:
  "ursize (snd (snd (snd (uletpast_meval0 eval j i ys xs p ts db \<phi>)))) = ursize \<phi>"
proof (induct eval j i ys xs p ts db \<phi> rule: uletpast_meval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where eval: "eval ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by fastforce
  show ?case
  proof (cases ys')
    case Nil
    then show ?thesis
      using eval by (subst uletpast_meval0.simps) simp
  next
    case (Cons y ys'')
    have "ursize (snd (snd (snd (uletpast_meval0 eval j (i + length xs) (ys @ ys') ys' p []
      (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))) = ursize \<phi>'"
      if "ursize \<phi>' = ursize \<phi>" "\<not> j \<le> Suc (i + length xs)"
      using 1(1)[OF eval[symmetric] refl _ Cons] that by simp
    then show ?thesis
      using eval Cons by (subst uletpast_meval0.simps) (simp add: Let_def)
  qed
qed

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
| "udeval j ts db (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     (let (xs, \<phi>) = udeval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = udeval j ts db0 \<psi>;
          (rs, \<rho>) = udeval j ts db0 \<rho>;
          (zs0_out, jfrz, fl, \<alpha>s, lr) =
            (let zs0_out = drop (jfrz - jpsi0) zs0;
                 \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
             in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
               case lv of None \<Rightarrow> None | Some g \<Rightarrow>
                 if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
                 then Some (g, udeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
                 else None));
          (ys, \<alpha>s', lv, \<rho>, w, pR, tq, rb) = frz_live_loop ursize (udeval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
            fl d po j jfrz \<alpha>s lr (\<rho>, w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
              drop (min jfrz (pR + length rs) - (pR - length rb)) (rb @ rs))
      in (zs0_out @ ys, UDFrz p m \<phi> \<psi> (jfrz + length ys) (jpsi0 + length zs0) (jphi + length xs) \<alpha>s' \<rho> w pR tq rb d po ng
        (ufrz_keep_lv (if po then None else lv) \<rho>L) (ufrz_keep_st (if po then None else lv) \<rho>L)))"
| "udeval j ts db (UDLetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
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
  "udeval_dom (j, ts, db, \<phi>) \<Longrightarrow> ursize (snd (udeval j ts db \<phi>)) = ursize \<phi>"
proof (induct rule: udeval.pinduct)
  case (11 j ts db I \<phi> first buf nts) \<comment> \<open>\<^const>\<open>UDPrev\<close>\<close>
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "ueprev_next I (buf @@ xs) (nts @@ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "ursize \<phi>' = ursize \<phi>"
    using 11(2) \<phi>' by simp
  then show ?case
    by (simp add: udeval.psimps(11)[OF 11(1)] \<phi>' mp del: ueprev_next.simps)
next
  case (14 j ts db dags \<phi> \<psi> buf aux) \<comment> \<open>\<^const>\<open>UDSince\<close>\<close>
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain ys \<psi>' where \<psi>': "udeval j ts db \<psi> = (ys, \<psi>')"
    by fastforce
  obtain zs buf' aux' where e: "uedsx_eval_since dags [] (uebuf2S_add xs ys ts buf) aux = (zs, buf', aux')"
    by (metis prod_cases3)
  have "ursize \<phi>' = ursize \<phi>" "ursize \<psi>' = ursize \<psi>"
    using 14(2) 14(3)[OF refl \<phi>'[symmetric]] \<phi>' \<psi>' by simp_all
  then show ?case
    using usx_q_uedsx_eval_since'[OF e] by (simp add: udeval.psimps(14)[OF 14(1)] \<phi>' \<psi>' e)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) \<comment> \<open>\<^const>\<open>UDFrz\<close>\<close>
  let ?db0 = "Mapping.update (p, m) [] db"
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs0 \<psi>' where \<psi>': "udeval j ts ?db0 \<psi> = (zs0, \<psi>')"
    by fastforce
  obtain rs \<rho>' where \<rho>': "udeval j ts ?db0 \<rho> = (rs, \<rho>')"
    by fastforce
  have s\<phi>: "ursize \<phi>' = ursize \<phi>"
    using 20(2) \<phi>' by simp
  have s\<psi>: "ursize \<psi>' = ursize \<psi>"
    using 20(3)[OF \<phi>'[symmetric] refl refl] \<psi>' by simp
  have s\<rho>: "ursize \<rho>' = ursize \<rho>"
    using 20(4)[OF \<phi>'[symmetric] refl refl \<psi>'[symmetric] refl] \<rho>' by simp
  obtain zo jf fl as lr where st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, udeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (zo, jf, fl, as, lr)"
    by (rule prod_cases5)
  obtain ys as' lv' s' where lp0: "frz_live_loop ursize (udeval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
      fl d po j jf as lr (\<rho>', w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
        drop (min jf (pR + length rs) - (pR - length rb)) (rb @ rs)) = (ys, as', lv', s')"
    by (metis prod_cases4)
  obtain \<rho>'' w' pR' tq' rb' where s': "s' = (\<rho>'', w', pR', tq', rb')"
    by (metis prod_cases5)
  have s\<rho>'': "ursize \<rho>'' = ursize \<rho>"
    using frz_live_loop_size[OF lp0] s\<rho> s' by simp
  have "snd (udeval j ts db (UDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)) =
    UDFrz p m \<phi>' \<psi>' (jf + length ys) (jpsi0 + length zs0) (jphi + length xs) as' \<rho>'' w' pR' tq' rb' d po ng
      (ufrz_keep_lv (if po then None else lv') \<rho>L) (ufrz_keep_st (if po then None else lv') \<rho>L)"
    by (simp only: udeval.psimps(20)[OF 20(1)] \<phi>' \<psi>' \<rho>' st lp0[unfolded s'] Let_def[where s = ?db0]
        Let_def[where s = "(xs, \<phi>')"] Let_def[where s = "(zs0, \<psi>')"] Let_def[where s = "(rs, \<rho>')"]
        Let_def[where s = "(zo, jf, fl, as, lr)"] Let_def[where s = "(ys, as', lv', \<rho>'', w', pR', tq', rb')"]
        prod.case snd_conv)
  then show ?case
    using s\<phi> s\<psi> s\<rho>'' by simp
next
  case (21 j ts db p m \<phi> \<psi> i buf) \<comment> \<open>\<^const>\<open>UDLetPast\<close>\<close>
  obtain xs i' buf' \<phi>' where lp:
    "uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi> = (xs, i', buf', \<phi>')"
    by (metis prod_cases4)
  have ursize_\<phi>': "ursize \<phi>' = ursize \<phi>"
    using ursize_uletpast_meval[of "udeval j" j i "[]" "list_of_option buf" "(p, m)" ts db \<phi>]
    by (simp add: lp)
  obtain ys \<psi>' where \<psi>': "udeval j ts (Mapping.update (p, m) xs db) \<psi> = (ys, \<psi>')"
    by fastforce
  have ursize_\<psi>': "ursize \<psi>' = ursize \<psi>"
    using 21(3)[OF lp[symmetric] refl refl refl] \<psi>' by simp
  show ?case
    using ursize_\<phi>' ursize_\<psi>' by (simp add: udeval.psimps(21)[OF 21(1)] lp \<psi>')
  \<comment> \<open>in all other cases, the claim follows directly from the IHs for the subformulas,
    since evaluation keeps the node's constructor and its non-formula arguments do not count\<close>
qed (auto simp only: prod.inject udeval.psimps Let_def snd_conv fst_conv
    ursize.simps list.map map_map o_apply length_map ursize_ufrz_keep_st cong: map_cong
    split: prod.splits)

lemma total_udeval: "All udeval_dom"
proof (relation "measure (\<lambda>(j, ts, db, \<phi>). ursize \<phi>)", goal_cases)
  text \<open>The live copy and the replays of @{const UDFrz}, as for @{const meval}.\<close>
  case 23 \<comment> \<open>the live copy, a subterm\<close>
  then show ?case
    by simp
next
  case (24 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L x xa y xb xc xd ya xe xf yb xg xh
    yc xi yd xj yca xk ycb tsa dba \<psi>')
  have "ursize yb = ursize \<rho>"
    using psize_snd_udeval[of j ts xb \<rho>] 24 by (metis snd_conv)
  then show ?case
    using 24 by simp
qed (auto simp: ursize_in_set dest!: psize_snd_udeval dest: sym split: option.splits)

termination udeval by (rule total_udeval)

lemma ursize_snd_udeval[simp]: "ursize (snd (udeval j ts db \<phi>)) = ursize \<phi>"
  by (rule psize_snd_udeval[OF total_udeval[THEN spec]])

subsection \<open>The two evaluators agree\<close>

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

lemma map_dsan_reopt_deopt: "map dsan xs = map reopt_table (map deopt_table xs)"
  by (simp add: dsan_def)

lemma mebuf2t_take_until:
  "mebuf2t_take (dux_add_new dags msk) (rdux aux) (qbuf2 buf) t ts
   = (case uebuf2t_take (udux_add_new dags msk) aux buf t ts of
        (aux', buf', t', ts') \<Rightarrow> (rdux aux', qbuf2 buf', t', ts'))"
  by (rule mebuf2t_take_rbuf) (simp add: dux_add_new_rdux)

lemma mebuf2T_take_rbuf:
  assumes "\<And>x y t z. f (reopt_table x) (reopt_table y) t (h z) = h (f' x y t z)"
  shows "mebuf2T_take f (h z) (qbuf2 buf) ts
   = (case uebuf2T_take f' z buf ts of (z', buf', ts') \<Rightarrow> (h z', qbuf2 buf', ts'))"
  by (cases buf)
    (simp add: mebuf2T_take_map_mbuf[where f = f and h = h and f' = f', OF assms]
       split: prod.splits del: mebuf2T_take.simps uebuf2T_take.simps)

text \<open>The fused And-Trigger's two traversals.  The inner one is the trigger's, with the empty
  window kept as @{term None}; the outer one relabels its two sides differently, the left
  operand's tables and the trigger's optional reads.\<close>

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

text \<open>The list operations of @{const deval} on the buffers the short ones stand for, in the shapes
  the simplifier leaves the evaluator's buffers in.  Each is the naturality of the queue operation
  above, read back through @{const Rep_mbuf_t} by the agreement of the queue operation with the
  list one (@{theory MFODL_Monitor_Devel.Monitor_Impl}).\<close>

lemma rbuf2_qbuf2: "rbuf2 buf = map_prod Rep_mbuf_t Rep_mbuf_t (qbuf2 buf)"
  by (cases buf) simp

lemma mbuf2_add_rbuf2:
  "mbuf2_add (map reopt_table xs) (map reopt_table ys) (rbuf2 buf) = rbuf2 (mebuf2_add xs ys buf)"
  by (cases buf) (simp add: mbuf_t_append.rep_eq)

lemma mbuf2_take_rbuf2:
  assumes "\<And>x y. f (reopt_table x) (reopt_table y) = reopt_table (f' x y)"
  shows "mbuf2_take f (rbuf2 buf)
   = (case mebuf2_take f' buf of (zs, buf') \<Rightarrow> (map reopt_table zs, rbuf2 buf'))"
proof -
  obtain zs buf' where e: "mebuf2_take f' buf = (zs, buf')" by (cases "mebuf2_take f' buf")
  have "mebuf2_take f (qbuf2 buf) = (map reopt_table zs, qbuf2 buf')"
    using mebuf2_take_rbuf[where f = f and f' = f' and buf = buf, OF assms] e by simp
  from mebuf2_take[OF this] show ?thesis
    unfolding rbuf2_qbuf2 e by (simp only: prod.case)
qed

lemma mbuf2_take_or:
  "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (rbuf2 buf)
   = (case mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) buf of (zs, buf') \<Rightarrow> (map reopt_table zs, rbuf2 buf'))"
  by (rule mbuf2_take_rbuf2) simp

lemma mbuf2_take_and:
  "mbuf2_take (\<lambda>r1 r2. dbin_join pl r1 pos r2) (rbuf2 buf)
   = (case mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2) buf of
        (zs, buf') \<Rightarrow> (map reopt_table zs, rbuf2 buf'))"
  by (rule mbuf2_take_rbuf2) (simp add: dbin_join_reopt_table)

lemma mbuf2t_take_until:
  "mbuf2t_take (dux_add_new dags msk) (rdux aux) (rbuf2 buf) t (Rep_mbuf_t nts @ ts)
   = (case uebuf2t_take (udux_add_new dags msk) aux buf t (nts @@ ts) of
        (aux', buf', t', nts') \<Rightarrow> (rdux aux', rbuf2 buf', t', Rep_mbuf_t nts'))"
proof -
  obtain aux' buf' t' nts' where e:
    "uebuf2t_take (udux_add_new dags msk) aux buf t (nts @@ ts) = (aux', buf', t', nts')"
    by (metis prod_cases4)
  have "mebuf2t_take (dux_add_new dags msk) (rdux aux) (qbuf2 buf) t (nts @@ ts)
      = (rdux aux', qbuf2 buf', t', nts')"
    using mebuf2t_take_until[of dags msk aux buf t "nts @@ ts"] e by simp
  from mebuf2t_take[OF this] show ?thesis
    unfolding rbuf2_qbuf2 e by (simp only: prod.case mbuf_t_append.rep_eq)
qed

lemma mbuf2T_take_rbuf2:
  assumes "\<And>x y t z. f (reopt_table x) (reopt_table y) t (h z) = h (f' x y t z)"
  shows "mbuf2T_take f (h z) (rbuf2 buf) (Rep_mbuf_t nts @ ts)
   = (case uebuf2T_take f' z buf (nts @@ ts) of
        (z', buf', nts') \<Rightarrow> (h z', rbuf2 buf', Rep_mbuf_t nts'))"
proof -
  obtain z' buf' nts' where e: "uebuf2T_take f' z buf (nts @@ ts) = (z', buf', nts')"
    by (metis prod_cases3)
  have "mebuf2T_take f (h z) (qbuf2 buf) (nts @@ ts) = (h z', qbuf2 buf', nts')"
    using mebuf2T_take_rbuf[where f = f and h = h and f' = f' and z = z and buf = buf
        and ts = "nts @@ ts", OF assms] e by simp
  from mebuf2T_take[OF this] show ?thesis
    unfolding rbuf2_qbuf2 e by (simp only: prod.case mbuf_t_append.rep_eq)
qed

lemma mbuf2T_take_trigger:
  "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [dsan (gresult_mmtaux dags ax)], ax))
     ([], bmm daux) (rbuf2 buf) (Rep_mbuf_t nts @ ts)
   = (case uebuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux) buf (nts @@ ts) of
        (z', buf', nts') \<Rightarrow> (map_prod (map reopt_table) bmm z', rbuf2 buf', Rep_mbuf_t nts'))"
proof -
  have "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (zs @ [dsan (gresult_mmtaux dags ax)], ax))
        (map_prod (map reopt_table) bmm ([], daux)) (rbuf2 buf) (Rep_mbuf_t nts @ ts)
      = (case uebuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux) buf (nts @@ ts) of
          (z', buf', nts') \<Rightarrow> (map_prod (map reopt_table) bmm z', rbuf2 buf', Rep_mbuf_t nts'))"
    by (rule mbuf2T_take_rbuf2)
      (simp add: Let_def case_prod_beta map_prod_def gupdate_mmtaux_bmm gresult_mmtaux_bmm)
  then show ?thesis by simp
qed

lemma mbuf2T_take_andtrigger:
  "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None
                else Some (dsan (gresult_mmtaux dags ax))], ax))
     ([], bmm daux) (rbuf2 buf) (Rep_mbuf_t nts @ ts)
   = (case uebuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
      ([], daux) buf (nts @@ ts) of
        (z', buf', nts') \<Rightarrow>
          (map_prod (map (map_option reopt_table)) bmm z', rbuf2 buf', Rep_mbuf_t nts'))"
proof -
  have "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (ws @ [if gmmtaux_empty ax then None
                  else Some (dsan (gresult_mmtaux dags ax))], ax))
        (map_prod (map (map_option reopt_table)) bmm ([], daux)) (rbuf2 buf) (Rep_mbuf_t nts @ ts)
      = (case uebuf2T_take (\<lambda>r1 r2 t (ws, ax).
        let ax = gupdate_mmtaux dags t r1 r2 ax
        in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
        ([], daux) buf (nts @@ ts) of
          (z', buf', nts') \<Rightarrow>
            (map_prod (map (map_option reopt_table)) bmm z', rbuf2 buf', Rep_mbuf_t nts'))"
    by (rule mbuf2T_take_rbuf2)
      (simp add: Let_def case_prod_beta map_prod_def gupdate_mmtaux_bmm gresult_mmtaux_bmm
        gmmtaux_empty_bmm)
  then show ?thesis by simp
qed

abbreviation rbufo :: "utable mbuf_t \<times> utable option mbuf_t \<Rightarrow>
    event_data table list \<times> event_data table option list" where
  "rbufo \<equiv> map_prod (\<lambda>b. rbl b) (\<lambda>b. map (map_option reopt_table) (Rep_mbuf_t b))"

lemma mbuf2_add_andtrigger:
  "mbuf2_add (map reopt_table as) (map (map_option reopt_table) ws) (rbufo buf)
   = rbufo (mebuf2_add as ws buf)"
  by (cases buf) (simp add: mbuf_t_append.rep_eq)

lemma mbuf2_take_andtrigger:
  "mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> dbin_join pl r1 True z) (rbufo buf)
   = (case mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> gbin_join pl r1 True z) buf of
        (zs, buf') \<Rightarrow> (map reopt_table zs, rbufo buf'))"
proof -
  obtain zs buf' where e:
    "mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> gbin_join pl r1 True z) buf = (zs, buf')"
    by (cases "mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> gbin_join pl r1 True z) buf")
  have "mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> dbin_join pl r1 True z)
      (map_prod (map_mbuf reopt_table) (map_mbuf (map_option reopt_table)) buf)
      = (map reopt_table zs, map_prod (map_mbuf reopt_table) (map_mbuf (map_option reopt_table)) buf')"
    using mebuf2_take_andtrigger[of pl buf] e by (simp del: mebuf2_take.simps)
  moreover have "rbufo b = map_prod Rep_mbuf_t Rep_mbuf_t
      (map_prod (map_mbuf reopt_table) (map_mbuf (map_option reopt_table)) b)" for b
    by (cases b) simp
  ultimately show ?thesis
    using mebuf2_take by (simp only: e prod.case)
qed

lemma mprev_next_prev:
  "mprev_next I (rbl buf @ map reopt_table xs) (Rep_mbuf_t nts @ ts)
   = (case ueprev_next I (buf @@ xs) (nts @@ ts) of
        (zs, xs', ts') \<Rightarrow> (map reopt_table zs, rbl xs', Rep_mbuf_t ts'))"
proof -
  obtain zs xs' ts' where e: "ueprev_next I (buf @@ xs) (nts @@ ts) = (zs, xs', ts')"
    by (metis prod_cases3)
  have "meprev_next I (map_mbuf reopt_table (buf @@ xs)) (nts @@ ts)
      = (map reopt_table zs, map_mbuf reopt_table xs', ts')"
    using meprev_next_map_mbuf[of I "buf @@ xs" "nts @@ ts"] e
    by (simp del: meprev_next.simps ueprev_next.simps map_mbuf_append)
  from meprev_next[OF this] show ?thesis
    by (simp add: e mbuf_t_append.rep_eq del: mprev_next.simps ueprev_next.simps)
qed

lemma mprev_next_next:
  "mprev_next I (map reopt_table xs) (Rep_mbuf_t nts @ ts)
   = (case ueprev_next I (mbuf_t_empty @@ xs) (nts @@ ts) of
        (zs, xs', ts') \<Rightarrow> (map reopt_table zs, rbl xs', Rep_mbuf_t ts'))"
  using mprev_next_prev[of I mbuf_t_empty xs nts ts]
  by (simp add: mbuf_t_empty.rep_eq del: mprev_next.simps ueprev_next.simps)
lemma dsx_eval_since_rdsx0:
  "(case dsx_eval_since args [] (rbufS buf) (rdsx aux) of
      (Zs, bf, a) \<Rightarrow> (map (dfilt (usx_q aux)) Zs, bf, a))
   = (case uedsx_eval_since args [] buf aux of
        (zs, buf', aux') \<Rightarrow> (map reopt_table zs, rbufS buf', rdsx aux'))"
  using dsx_eval_since_rdsx[where rs = "[]" and Rs = "[]"] by simp

lemma mbufn_add_rbl:
  "mbufn_add (map (map reopt_table) xss) (map (\<lambda>b. rbl b) buf) = map (\<lambda>b. rbl b) (uebufn_add xss buf)"
  by (induct buf xss rule: list_induct2') (auto simp: mbuf_t_append.rep_eq)

lemma mbufn_take_rbl:
  assumes "\<And>as z. f (map reopt_table as) (h z) = h (f' as z)"
  shows "mbufn_take f (h z) (map (\<lambda>b. rbl b) buf)
   = (case uebufn_take f' z buf of (z', buf') \<Rightarrow> (h z', map (\<lambda>b. rbl b) buf'))"
proof -
  obtain z' buf' where e: "uebufn_take f' z buf = (z', buf')" by (cases "uebufn_take f' z buf")
  have "mebufn_take f (h z) (map (map_mbuf reopt_table) buf) = (h z', map (map_mbuf reopt_table) buf')"
    using mebufn_take_map_mbuf[of f reopt_table h f' z buf, OF assms] e
    by (simp del: mebufn_take.simps)
  from mebufn_take[OF this] show ?thesis
    by (simp add: e comp_def del: mbufn_take.simps)
qed

lemma mbufn_take_ands:
  "mbufn_take (\<lambda>as zs. zs @ [dmulti_join ps ns as]) [] (map (\<lambda>b. rbl b) buf)
   = (case uebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty buf of
        (zs, buf') \<Rightarrow> (rbl zs, map (\<lambda>b. rbl b) buf'))"
proof -
  have "mbufn_take (\<lambda>as zs. zs @ [dmulti_join ps ns as]) (rbl mbuf_t_empty) (map (\<lambda>b. rbl b) buf)
   = (case uebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty buf of
        (zs, buf') \<Rightarrow> (rbl zs, map (\<lambda>b. rbl b) buf'))"
    by (rule mbufn_take_rbl) (simp add: mbuf_t_append.rep_eq dmulti_join_reopt_table)
  then show ?thesis by (simp add: mbuf_t_empty.rep_eq del: mbufn_take.simps)
qed

lemma mbufnt_take_rbl:
  assumes "\<And>as t z. f (map reopt_table as) t (h z) = h (f' as t z)"
  shows "mbufnt_take f (h z) (map (\<lambda>b. rbl b) buf) t0 (Rep_mbuf_t nts @ ts)
   = (case uebufnt_take f' z buf t0 (nts @@ ts) of
        (z', buf', t', ts') \<Rightarrow> (h z', map (\<lambda>b. rbl b) buf', t', Rep_mbuf_t ts'))"
proof -
  obtain z' buf' t' ts' where e: "uebufnt_take f' z buf t0 (nts @@ ts) = (z', buf', t', ts')"
    by (metis prod_cases4)
  have "mebufnt_take f (h z) (map (map_mbuf reopt_table) buf) t0 (nts @@ ts)
      = (h z', map (map_mbuf reopt_table) buf', t', ts')"
    using mebufnt_take_map_mbuf[of f reopt_table h f' z buf t0 "nts @@ ts", OF assms] e
    by (simp del: mebufnt_take.simps uebufnt_take.simps)
  from mebufnt_take[OF this] show ?thesis
    by (simp add: e comp_def mbuf_t_append.rep_eq del: mbufnt_take.simps uebufnt_take.simps)
qed
lemma mbufnt_take_matchP:
  "mbufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @ [z], ax)))
     ([], rmrd a0) (map (\<lambda>b. rbl b) buf) t0 (Rep_mbuf_t nts @ ts)
   = (case uebufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax)))
       (mbuf_t_empty, a0) buf t0 (nts @@ ts) of
        ((zs', a'), buf', t', ts') \<Rightarrow> ((rbl zs', rmrd a'), map (\<lambda>b. rbl b) buf', t', Rep_mbuf_t ts'))"
proof -
  have "mbufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @ [z], ax)))
     (map_prod (\<lambda>b. rbl b) rmrd (mbuf_t_empty, a0)) (map (\<lambda>b. rbl b) buf) t0 (Rep_mbuf_t nts @ ts)
   = (case uebufnt_take (\<lambda>rels t (zs, ax).
       (case gupdate_matchP msks I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax)))
       (mbuf_t_empty, a0) buf t0 (nts @@ ts) of
        (z', buf', t', ts') \<Rightarrow> (map_prod (\<lambda>b. rbl b) rmrd z', map (\<lambda>b. rbl b) buf', t', Rep_mbuf_t ts'))"
    by (rule mbufnt_take_rbl)
      (auto simp: gupdate_matchP_reopt mbuf_t_append.rep_eq split: prod.splits)
  then show ?thesis by (simp add: mbuf_t_empty.rep_eq split: prod.splits)
qed

lemma mbufnt_take_matchF:
  "mbufnt_take (\<lambda>rels. gupdate_matchF msks I mr mrs rels)
     (rmld z0) (map (\<lambda>b. rbl b) buf) t0 (Rep_mbuf_t nts @ ts)
   = (case uebufnt_take (\<lambda>rels. gupdate_matchF msks I mr mrs rels) z0 buf t0 (nts @@ ts) of
        (z', buf', t', ts') \<Rightarrow> (rmld z', map (\<lambda>b. rbl b) buf', t', Rep_mbuf_t ts'))"
  by (rule mbufnt_take_rbl) (simp add: gupdate_matchF_reopt)

lemma uletpast_meval0_rdb:
  "(\<And>ts db \<psi>. ursize \<psi> = n \<Longrightarrow>
      eval ts (rdb db) (Rep_udformula \<psi>) = (case eval' ts db \<psi> of (ys, \<psi>') \<Rightarrow> (map reopt_table ys, Rep_udformula \<psi>'))) \<Longrightarrow>
    ursize \<phi> = n \<Longrightarrow>
    letpast_meval0 eval j i (map reopt_table ys) (map reopt_table xs) p ts (rdb db) (Rep_udformula \<phi>)
    = (case uletpast_meval0 eval' j i ys xs p ts db \<phi> of
        (ys', i', b, \<phi>') \<Rightarrow> (map reopt_table ys', i', map_option reopt_table b, Rep_udformula \<phi>'))"
proof (induct eval' j i ys xs p ts db \<phi> rule: uletpast_meval0.induct)
  case (1 eval' j i ys xs p ts db \<phi>)
  obtain ys' \<phi>' where e: "eval' ts (Mapping.update p xs db) \<phi> = (ys', \<phi>')"
    by (cases "eval' ts (Mapping.update p xs db) \<phi>")
  have L: "eval ts (rdb (Mapping.update p xs db)) (Rep_udformula \<phi>) = (map reopt_table ys', Rep_udformula \<phi>')"
    using "1.prems"(1)[OF "1.prems"(2), of ts "Mapping.update p xs db"] by (simp add: e)
  have g: "(size (Rep_udformula \<phi>') \<noteq> size (Rep_udformula \<phi>)) = (ursize \<phi>' \<noteq> ursize \<phi>)"
    by (simp add: ursize_Rep)
  show ?case
  proof (cases "ursize \<phi>' = ursize \<phi>")
    case False
    then show ?thesis
      by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
  next
    case True
    show ?thesis
    proof (cases ys')
      case Nil
      then show ?thesis
        using True by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
    next
      case (Cons y ys'')
      show ?thesis
      proof (cases "j \<le> Suc (i + length xs)")
        case le: True
        then show ?thesis
          using True Cons
          by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
      next
        case False
        have n: "ursize \<phi>' = n"
          using True "1.prems"(2) by simp
        have rec: "letpast_meval0 eval j (i + length xs) (map reopt_table (ys @ ys'))
            (map reopt_table ys') p [] (rdb (Mapping.map_values (\<lambda>_ _. []) db)) (Rep_udformula \<phi>') =
          (case uletpast_meval0 eval' j (i + length xs) (ys @ ys') ys' p []
              (Mapping.map_values (\<lambda>_ _. []) db) \<phi>' of
            (ys', i', b, \<phi>') \<Rightarrow> (map reopt_table ys', i', map_option reopt_table b, Rep_udformula \<phi>'))"
          using "1.hyps"[OF e[symmetric] refl _ Cons False "1.prems"(1) n] True by simp
        show ?thesis
          using True False Cons rec
          by (subst letpast_meval0.simps, subst uletpast_meval0.simps) (simp add: Let_def L e g)
      qed
    qed
  qed
qed

lemma udeval_Rep:
  "deval j ts (rdb db) (Rep_udformula \<phi>)
   = (case udeval j ts db \<phi> of (zs, \<phi>') \<Rightarrow> (map reopt_table zs, Rep_udformula \<phi>'))"
proof (induction j ts db \<phi> rule: udeval.induct)
  case (13 j ts db ps ns L buf)
  have "map fst (map (deval j ts (rdb db)) (map Rep_udformula L))
      = map (map reopt_table) (map fst (map (udeval j ts db) L))"
    "map snd (map (deval j ts (rdb db)) (map Rep_udformula L))
      = map Rep_udformula (map snd (map (udeval j ts db) L))"
    by (auto simp: 13 split: prod.splits)
  then show ?case
    by (auto simp only: Let_def deval.simps udeval.simps Rep_udformula.simps
        mbufn_add_rbl mbufn_take_ands split: prod.splits)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)
  let ?db0 = "Mapping.update (p, m) [] db"
  let ?dbe = "Mapping.map_values (\<lambda>_ _. []) db"
  obtain xs \<phi>' where \<phi>: "udeval j ts db \<phi> = (xs, \<phi>')"
    by (cases "udeval j ts db \<phi>")
  obtain zs0 \<psi>' where \<psi>: "udeval j ts ?db0 \<psi> = (zs0, \<psi>')"
    by (cases "udeval j ts ?db0 \<psi>")
  obtain rs \<rho>' where \<rho>: "udeval j ts ?db0 \<rho> = (rs, \<rho>')"
    by (cases "udeval j ts ?db0 \<rho>")
  have IH1: "deval j ts (rdb db) (Rep_udformula \<phi>) = (map reopt_table xs, Rep_udformula \<phi>')"
    using 20(1) \<phi> by simp
  have IH2: "deval j ts (rdb ?db0) (Rep_udformula \<psi>) = (map reopt_table zs0, Rep_udformula \<psi>')"
    using 20(2)[OF refl \<phi>[symmetric] refl] \<psi> by simp
  have IH3: "deval j ts (rdb ?db0) (Rep_udformula \<rho>) = (map reopt_table rs, Rep_udformula \<rho>')"
    using 20(3)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric]] \<rho> by simp
  let ?z = "drop (jfrz - jpsi0) zs0"
  let ?as = "drop (jfrz - jphi + length ?z) (\<alpha>s @ xs)"
  let ?dbL = "Mapping.update (p, m) (replicate (length ts) (hd ?as)) db"
  define lru where "lru = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if ?z = [] \<and> ?as \<noteq> [] then Some (g, udeval j ts ?dbL \<rho>L) else None)"
  define lre where "lre = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if map reopt_table ?z = [] \<and> map reopt_table ?as \<noteq> []
    then Some (g, deval j ts (Mapping.update (p, m) (replicate (length ts) (hd (map reopt_table ?as)))
      (rdb db)) (Rep_udformula \<rho>L)) else None)"
  have st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, udeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (?z, jfrz + length ?z, frz_fill ng (\<alpha>s @ xs), ?as, lru)"
    by (simp only: Let_def lru_def)
  have IHL: "lre = map_option (\<lambda>(g, us, st). (g, map reopt_table us, Rep_udformula st)) lru"
  proof (cases lv)
    case (Some g)
    show ?thesis
    proof (cases "?z = [] \<and> ?as \<noteq> []")
      case True
      have hd: "hd (map reopt_table ?as) = reopt_table (hd ?as)"
        using True hd_map[of "?as" reopt_table] by blast
      have "deval j ts (rdb ?dbL) (Rep_udformula \<rho>L) =
          (case udeval j ts ?dbL \<rho>L of (zs, \<phi>') \<Rightarrow> (map reopt_table zs, Rep_udformula \<phi>'))"
        by (rule 20(4)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric] refl \<rho>[symmetric] refl refl Some True])
      then show ?thesis
        using Some True hd by (simp add: lru_def lre_def split: prod.splits)
    qed (use Some in \<open>auto simp: lru_def lre_def\<close>)
  qed (simp add: lru_def lre_def)
  have IHloop: "deval j ts' (rdb db') (Rep_udformula \<chi>) =
      (case udeval j ts' db' \<chi> of (zs, \<chi>') \<Rightarrow> (map reopt_table zs, Rep_udformula \<chi>'))"
    if "ursize \<chi> = ursize \<rho>'" for ts' db' \<chi>
    using 20(5)[OF refl \<phi>[symmetric] refl refl \<psi>[symmetric] refl \<rho>[symmetric] refl st[symmetric]
        refl refl refl, of \<chi> ts' db'] that
    by simp
  let ?k = "min (jfrz + length ?z) (pR + length rs) - (pR - length rb)"
  let ?tq = "if d = \<infinity> then [] else tq @ ts"
  obtain ys as' lvu \<rho>2 w2 pR2 tq2 rb2 where fr0: "frz_live_loop ursize (udeval j) (p, m) ?dbe
      (frz_fill ng (\<alpha>s @ xs)) d po j (jfrz + length ?z) ?as lru (\<rho>', w, pR + length rs, ?tq, drop ?k (rb @ rs))
      = (ys, as', lvu, \<rho>2, w2, pR2, tq2, rb2)"
    by (metis prod_cases4 prod_cases5)
  obtain yse ase lve se where fre: "frz_live_loop size (deval j) (p, m) (rdb ?dbe)
      (reopt_table (frz_fill ng (\<alpha>s @ xs))) d po j (jfrz + length ?z) (map reopt_table ?as) lre
      (Rep_udformula \<rho>', w, pR + length rs, ?tq, map reopt_table (drop ?k (rb @ rs))) = (yse, ase, lve, se)"
    by (metis prod_cases4)
  have rel: "yse = map reopt_table ys \<and> ase = map reopt_table as' \<and>
      rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> \<sigma>' = Rep_udformula \<sigma>) lvu lve \<and>
      frz_st_rel (\<lambda>\<sigma> \<sigma>'. \<sigma>' = Rep_udformula \<sigma>) reopt_table (\<rho>2, w2, pR2, tq2, rb2) se"
  proof (rule frz_live_loop_rel[OF _ _ _ _ fr0 fre])
    fix \<chi> \<chi>' c X
    assume "ursize \<chi> = ursize (fst (\<rho>', w, pR + length rs, ?tq, drop ?k (rb @ rs)))" and "\<chi>' = Rep_udformula \<chi>"
    then show "fst (deval j [] (Mapping.update (p, m) (replicate c (reopt_table X)) (rdb ?dbe)) \<chi>') =
        map reopt_table (fst (udeval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>)) \<and>
      snd (deval j [] (Mapping.update (p, m) (replicate c (reopt_table X)) (rdb ?dbe)) \<chi>') =
        Rep_udformula (snd (udeval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>))"
      using IHloop[of \<chi> "[]" "Mapping.update (p, m) (replicate c X) ?dbe"] by (simp split: prod.splits)
  qed (use IHL in \<open>auto simp: ursize_Rep option.rel_map intro: option.rel_refl\<close>)
  obtain \<rho>e2 where se: "se = (\<rho>e2, w2, pR2, tq2, map reopt_table rb2)" and \<rho>e2: "\<rho>e2 = Rep_udformula \<rho>2"
    using rel by (cases se) auto
  have lve: "lve = map_option (apsnd Rep_udformula) lvu"
    using rel by (cases lvu; cases lve) auto
  have keep: "frz_keep_lv (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      ufrz_keep_lv (if po then None else lvu) \<rho>L"
    "frz_keep_st (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      Rep_udformula (ufrz_keep_st (if po then None else lvu) \<rho>L)"
  proof -
    have ifm: "(if po then None else map_option (apsnd Rep_udformula) lvu) =
      map_option (apsnd Rep_udformula) (if po then None else lvu)"
      by simp
    show "frz_keep_lv (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      ufrz_keep_lv (if po then None else lvu) \<rho>L"
      "frz_keep_st (if po then None else map_option (apsnd Rep_udformula) lvu) (Rep_udformula \<rho>L) =
      Rep_udformula (ufrz_keep_st (if po then None else lvu) \<rho>L)"
      by (simp_all only: ifm frz_keep_Rep)
  qed
  show ?case
    by (simp only: Rep_udformula.simps deval.simps udeval.simps Let_def rdb_update_Nil rdb_map_values_Nil
        rdb_update_replicate_empty IH1 IH2 IH3 map_append[symmetric] frz_fill_reopt drop_map length_map \<phi> \<psi> \<rho>
        lre_def[symmetric] lru_def[symmetric] fr0 fre rel[THEN conjunct1] rel[THEN conjunct2, THEN conjunct1]
        se \<rho>e2 lve keep prod.case)
next
  case (21 j ts db p m \<phi> \<psi> i buf)
  have IH: "ursize \<psi> = ursize \<phi> \<Longrightarrow> deval j ts (rdb db) (Rep_udformula \<psi>) =
    (case udeval j ts db \<psi> of (zs, \<psi>') \<Rightarrow> (map reopt_table zs, Rep_udformula \<psi>'))" for ts db \<psi>
    using 21 by auto
  have lp: "letpast_meval0 (deval j) j i [] (list_of_option (map_option reopt_table buf)) (p, m) ts
      (rdb db) (Rep_udformula \<phi>)
    = (case uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi> of
        (ys', i', b, \<phi>') \<Rightarrow> (map reopt_table ys', i', map_option reopt_table b, Rep_udformula \<phi>'))"
    using uletpast_meval0_rdb[where n = "ursize \<phi>" and eval = "deval j"
        and eval' = "udeval j" and j = j and i = i and ys = "[]" and xs = "list_of_option buf"
        and p = "(p, m)" and ts = ts and db = db and \<phi> = \<phi>, OF IH refl]
    by (cases buf) simp_all
  show ?case
    using 21(2)[OF refl _ refl refl]
    by (cases "uletpast_meval0 (udeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>")
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
  then show ?case by (simp add: mbuf2_add_rbuf2 mbuf2_take_or split: prod.splits)
next
  case (10 j ts db pl \<phi> pos \<psi> buf)
  then show ?case by (simp add: mbuf2_add_rbuf2 mbuf2_take_and split: prod.splits)
next
  case (11 j ts db I \<phi> first buf nts)
  then show ?case
    by (simp add: mprev_next_prev empty_table_def mbuf_t_append.rep_eq
        del: mprev_next.simps ueprev_next.simps split: prod.splits)
next
  case (12 j ts db I \<phi> first nts)
  obtain xs \<phi>' where e: "udeval j ts db \<phi> = (xs, \<phi>')" by (cases "udeval j ts db \<phi>")
  obtain xs1 f1 where c: "(case xs of [] \<Rightarrow> ([], first)
      | x # xs' \<Rightarrow> (case first of True \<Rightarrow> (xs', False) | False \<Rightarrow> (x # xs', False))) = (xs1, f1)"
    by (cases "case xs of [] \<Rightarrow> ([], first)
      | x # xs' \<Rightarrow> (case first of True \<Rightarrow> (xs', False) | False \<Rightarrow> (x # xs', False))")
  have c': "(case map reopt_table xs of [] \<Rightarrow> ([], first)
      | x # xs' \<Rightarrow> (case first of True \<Rightarrow> (xs', False) | False \<Rightarrow> (x # xs', False)))
      = (map reopt_table xs1, f1)"
    using c by (cases xs; cases first) auto
  obtain zs b nts' where u: "ueprev_next I (mbuf_t_empty @@ xs1) (nts @@ ts) = (zs, b, nts')"
    by (metis prod_cases3)
  have IH: "deval j ts (rdb db) (Rep_udformula \<phi>) = (map reopt_table xs, Rep_udformula \<phi>')"
    using 12 e by simp
  have p: "mprev_next I (map reopt_table xs1) (Rep_mbuf_t nts @ ts) = (map reopt_table zs, rbl b, Rep_mbuf_t nts')"
    using mprev_next_next[of I xs1 nts ts] u by simp
  show ?case
    by (simp only: Rep_udformula.simps deval.simps udeval.simps Let_def IH e c c' u p prod.case)
next  case (14 j ts db dags \<phi> \<psi> buf aux)
  obtain xs \<phi>' where e1: "udeval j ts db \<phi> = (xs, \<phi>')" by (cases "udeval j ts db \<phi>")
  obtain ys \<psi>' where e2: "udeval j ts db \<psi> = (ys, \<psi>')" by (cases "udeval j ts db \<psi>")
  obtain zs buf' aux' where e3: "uedsx_eval_since dags [] (uebuf2S_add xs ys ts buf) aux
      = (zs, buf', aux')"
    by (cases "uedsx_eval_since dags [] (uebuf2S_add xs ys ts buf) aux")
  obtain Zs Bf Ax where E3: "dsx_eval_since dags [] (rbufS (uebuf2S_add xs ys ts buf)) (rdsx aux)
      = (Zs, Bf, Ax)"
    by (cases "dsx_eval_since dags [] (rbufS (uebuf2S_add xs ys ts buf)) (rdsx aux)")
  have Z: "map (dfilt (usx_q aux)) Zs = map reopt_table zs" and B: "Bf = rbufS buf'"
    and A: "Ax = rdsx aux'"
    using dsx_eval_since_rdsx0[where args = dags and buf = "uebuf2S_add xs ys ts buf" and aux = aux]
    by (simp_all add: e3 E3)
  have q: "usx_q aux' = usx_q aux" by (rule usx_q_uedsx_eval_since'[OF e3])
  show ?case
    using 14
    by (simp add: e1 e2 e3 E3 Z B A q mbuf2S_add_rbufS deval_dandrel
        del: dsx_eval_since.simps uedsx_eval_since.simps split: prod.splits)
next
  case (15 j ts db dags msk \<phi> \<psi> buf nts t aux)
  then show ?case
    by (simp add: mbuf2_add_rbuf2 mbuf2t_take_until dux_eval_rdux split: prod.splits)
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
    by (simp add: mbuf2_add_rbuf2 mbuf2T_take_trigger
        del: mbuf2T_take.simps uebuf2T_take.simps split: prod.splits)
next
  case (23 j ts db m I mr mrs pls Ld dbuf nts daux)
  have R: "map fst (map (deval j ts (rdb db)) (map Rep_udformula Ld))
      = map (map reopt_table) (map fst (map (udeval j ts db) Ld))"
    "map snd (map (deval j ts (rdb db)) (map Rep_udformula Ld))
      = map Rep_udformula (map snd (map (udeval j ts db) Ld))"
    by (auto simp: 23 split: prod.splits)
  let ?F = "\<lambda>rels t (zs, ax).
      (case gupdate_matchP (map emb_msk pls) I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @@ [z], ax))"
  let ?B = "uebufn_add (map fst (map (udeval j ts db) Ld)) dbuf"
  obtain zs daux' dbuf' tt nts' where U:
    "uebufnt_take ?F (mbuf_t_empty, daux) ?B 0 (nts @@ ts) = ((zs, daux'), dbuf', tt, nts')"
    by (cases "uebufnt_take ?F (mbuf_t_empty, daux) ?B 0 (nts @@ ts)") auto
  have E: "mbufnt_take (\<lambda>rels t (zs, ax).
      (case gupdate_matchP (map emb_msk pls) I mr mrs rels t ax of (z, ax) \<Rightarrow> (zs @ [z], ax)))
      ([], rmrd daux) (map (\<lambda>b. rbl b) ?B) 0 (Rep_mbuf_t nts @ ts)
      = ((rbl zs, rmrd daux'), map (\<lambda>b. rbl b) dbuf', tt, Rep_mbuf_t nts')"
    using mbufnt_take_matchP[of "map emb_msk pls" I mr mrs daux ?B 0 nts ts] U by simp
  have Z: "map dsan (rbl zs) = rbl zs"
    by simp
  show ?case
    by (simp only: Let_def deval.simps udeval.simps R mbufn_add_rbl U E
        prod.case Z Rep_udformula.simps)
next
  case (24 j ts db m I mr mrs pls Ld dbuf nts t daux)
  have R: "map fst (map (deval j ts (rdb db)) (map Rep_udformula Ld))
      = map (map reopt_table) (map fst (map (udeval j ts db) Ld))"
    "map snd (map (deval j ts (rdb db)) (map Rep_udformula Ld))
      = map Rep_udformula (map snd (map (udeval j ts db) Ld))"
    by (auto simp: 24 split: prod.splits)
  let ?F = "\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels"
  let ?B = "uebufn_add (map fst (map (udeval j ts db) Ld)) dbuf"
  obtain daux' dbuf' nt nts' where U:
    "uebufnt_take ?F daux ?B t (nts @@ ts) = (daux', dbuf', nt, nts')"
    by (cases "uebufnt_take ?F daux ?B t (nts @@ ts)") auto
  have E: "mbufnt_take ?F (rmld daux) (map (\<lambda>b. rbl b) ?B) t (Rep_mbuf_t nts @ ts)
      = (rmld daux', map (\<lambda>b. rbl b) dbuf', nt, Rep_mbuf_t nts')"
    using mbufnt_take_matchF[of "map emb_msk pls" I mr mrs daux ?B t nts ts] U by simp
  obtain zs daux'' where V: "geval_matchF I mr nt daux' = (zs, daux'')"
    by (cases "geval_matchF I mr nt daux'") auto
  have V': "geval_matchF I mr nt (rmld daux') = (map reopt_table zs, rmld daux'')"
    by (simp add: geval_matchF_reopt V)
  have Z: "map dsan (map reopt_table zs) = map reopt_table zs"
    by simp
  show ?case
    by (simp only: Let_def deval.simps udeval.simps R mbufn_add_rbl U E V V'
        prod.case Z Rep_udformula.simps)
next
  case (25 j ts db pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux)
  then show ?case
    by (simp add: mbuf2_add_rbuf2 mbuf2_add_andtrigger mbuf2T_take_andtrigger
        mbuf2_take_andtrigger
        del: mbuf2T_take.simps uebuf2T_take.simps mbuf2_take.simps split: prod.splits)
qed

subsection \<open>The compiler, the state and the step\<close>

text \<open>
  A constraint over a node whose result is an aggregate becomes the node's guard rather than a
  filter above it, when the node is a fused aggregating Since: the constraint is on the node's
  own columns, which are exactly the aggregation's, so the groups that fail it never have to be
  built.  Nothing else is fused -- every other node keeps the filter above it -- and the boxed
  compiler @{const dof} keeps it above this one too, which is what @{const dandrel} in
  @{const Rep_udformula} says.
\<close>

fun uset_q :: "uconstr \<Rightarrow> udformula \<Rightarrow> udformula option" where
  "uset_q c (UDSince args \<phi> \<psi> buf aux) =
     (case aux of UDSX_wagg p None a \<Rightarrow> Some (UDSince args \<phi> \<psi> buf (UDSX_wagg p (Some c) a))
      | _ \<Rightarrow> None)"
| "uset_q c \<phi> = None"

lemma Rep_uset_q:
  "uset_q c d = Some d' \<Longrightarrow> Rep_udformula d' = DAndRel (Rep_udformula d) c"
  by (cases d) (auto simp: dandrel_def split: udsaux_x.splits option.splits)

text \<open>The initial state of the short formula, compiled from the input formula.  The function
  @{text udinit} places each node the way the compiler @{const dof} of
  @{theory MFODL_Monitor_Dense.Dense_Descend} places the kernel's initial state @{const minit0},
  with the structures initialised on short tuples, and descends the formula the way @{const minit0}
  does; @{text fcols} is the column list @{const mfcols} reads off the kernel's initial state, for
  the atoms of a match node.  Both are proved against the kernel's initial state
  (@{text fcols_mfcols}, @{text udinit_dof}) and are the code, so the kernel's formulas are not
  exported.\<close>

lemmas minit0_init_defs = default_mmasaux.init_since_def dq_muaux.init_until_def
  verimon_maux.init_trigger_def verimon_maux.init_and_trigger_def

lemma mbuf_t_empty_append_Nil[simp]: "mbuf_t_empty @@ [] = mbuf_t_empty"
  by transfer simp

lemma minit0_Agg_default:
  assumes "\<forall>\<phi>' I \<psi>'. \<phi> \<noteq> Formula.Since \<phi>' I \<psi>'" "\<forall>\<phi>' I \<psi>'. \<phi> \<noteq> Formula.Until \<phi>' I \<psi>'"
  shows "minit0 n (Formula.Agg y \<omega> tys f \<phi>) =
    MAgg (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) (minit0 (length tys + n) \<phi>)"
  using assms by (cases \<phi>) (simp_all add: Let_def)

function (sequential) fcols :: "nat \<Rightarrow> ty Formula.formula \<Rightarrow> cols option" where
  "fcols n (Formula.Pred e ts) = (case pred_mode_of n ts of Copy \<Rightarrow> Some [0..<n]
     | _ \<Rightarrow> Some (set_cols (\<Union>t \<in> set ts. Formula.fv_trm t)))"
| "fcols n (Formula.Let p \<phi> \<psi>) = fcols n \<psi>"
| "fcols n (Formula.Frz p \<phi> \<psi>) = fcols n \<psi>"
| "fcols n (Formula.LetPast p \<phi> \<psi>) = fcols n \<psi>"
| "fcols n (Formula.Neg \<phi>) = (if fv \<phi> = {} then Some [] else None)"
| "fcols n (Formula.Or \<phi> \<psi>) = fcols n \<phi>"
| "fcols n (Formula.And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi>
       then map_option (\<lambda>c. merge_cols c [fst (split_assignment (fv \<phi>) \<psi>)]) (fcols n \<phi>)
     else if safe_formula \<psi> then
       (case (fcols n \<phi>, fcols n \<psi>) of (Some c1, Some c2) \<Rightarrow> Some (merge_cols c1 c2) | _ \<Rightarrow> None)
     else if is_constraint \<psi> then fcols n \<phi>
     else (case \<psi> of
         Formula.Neg \<psi>' \<Rightarrow> (case (fcols n \<phi>, fcols n \<psi>') of (Some c1, Some c2) \<Rightarrow> Some c1 | _ \<Rightarrow> None)
       | Formula.Trigger \<phi>' I \<psi>' \<Rightarrow> (if safe_formula \<phi>' then fcols n \<phi>
           else case \<phi>' of Formula.Neg _ \<Rightarrow> fcols n \<phi> | _ \<Rightarrow> None)
       | Formula.Release \<phi>' I \<psi>' \<Rightarrow> fcols n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
       | _ \<Rightarrow> None))"
| "fcols n (Formula.Ands l) = (case those (map (fcols n) (filter safe_formula l)) of
     Some (c0 # cs') \<Rightarrow> Some (dands_cols c0 cs') | _ \<Rightarrow> None)"
| "fcols n (Formula.Exists T \<phi>) = map_option (ungroup_cols (Suc 0)) (fcols (Suc n) \<phi>)"
| "fcols n (Formula.Agg y \<omega> tys f \<phi>) =
    (let m = length tys; col = map_option (\<lambda>r. merge_cols (ungroup_cols m r) [y]) in
     case \<phi> of
       Formula.Since \<phi>' I \<psi>' \<Rightarrow> (if safe_formula \<phi>' then col (fcols (m + n) \<psi>')
         else case \<phi>' of Formula.Neg _ \<Rightarrow> col (fcols (m + n) \<psi>') | _ \<Rightarrow> None)
     | Formula.Until \<phi>' I \<psi>' \<Rightarrow> (if safe_formula \<phi>' then col (fcols (m + n) \<psi>')
         else case \<phi>' of Formula.Neg _ \<Rightarrow> col (fcols (m + n) \<psi>') | _ \<Rightarrow> None)
     | _ \<Rightarrow> col (fcols (m + n) \<phi>))"
| "fcols n (Formula.Prev I \<phi>) = fcols n \<phi>"
| "fcols n (Formula.Next I \<phi>) = fcols n \<phi>"
| "fcols n (Formula.Since \<phi> I \<psi>) =
     (if safe_formula \<phi> then fcols n \<psi> else case \<phi> of Formula.Neg _ \<Rightarrow> fcols n \<psi> | _ \<Rightarrow> None)"
| "fcols n (Formula.Until \<phi> I \<psi>) =
     (if safe_formula \<phi> then fcols n \<psi> else case \<phi> of Formula.Neg _ \<Rightarrow> fcols n \<psi> | _ \<Rightarrow> None)"
| "fcols n (Formula.Trigger \<phi> I \<psi>) =
     (if safe_formula \<phi> then fcols n \<psi> else case \<phi> of Formula.Neg _ \<Rightarrow> fcols n \<psi> | _ \<Rightarrow> None)"
| "fcols n (Formula.Release \<phi> I \<psi>) = (if mem I 0
     then fcols n (release_safe_0 \<phi> I \<psi>) else fcols n (release_safe_bounded \<phi> I \<psi>))"
| "fcols n (Formula.TP t) = Some (mtrm_dcols (mtrm_of_trm t))"
| "fcols n (Formula.TS t) = Some (mtrm_dcols (mtrm_of_trm t))"
| "fcols n _ = None"
  by pat_completeness auto

termination
proof ((relation "measure (\<lambda>(_, \<phi>). size' \<phi>)"; clarsimp), goal_cases)
  case (5 \<phi> \<phi>' I \<psi>')
  then show ?case using size'_and_release[of \<phi> \<phi>' I \<psi>'] by simp
next
  case (6 l x)
  then show ?case unfolding less_Suc_eq_le using sum_list_mem_leq[of x l size'] by simp
next
  case (7 \<phi> I \<psi>)
  then show ?case using size'_release_aux(4)[of \<phi> I \<psi>] by simp
next
  case (8 \<phi> I \<psi>)
  then show ?case using size'_release_aux(3)[of \<phi> I \<psi>] by simp
qed (case_tac \<psi>; clarsimp)+

lemma fcols_mfcols: "fcols n \<phi> = mfcols n (minit0 n \<phi>)"
proof (induct n \<phi> rule: fcols.induct)
  case (10 n y \<omega> tys f \<phi>)
  show ?case
  proof (cases "\<exists>\<phi>' I \<psi>'. \<phi> = Formula.Since \<phi>' I \<psi>' \<or> \<phi> = Formula.Until \<phi>' I \<psi>'")
    case True
    then obtain \<phi>' I \<psi>' where "\<phi> = Formula.Since \<phi>' I \<psi>' \<or> \<phi> = Formula.Until \<phi>' I \<psi>'" by blast
    then show ?thesis
    proof
      assume S: "\<phi> = Formula.Since \<phi>' I \<psi>'"
      show ?thesis unfolding S using 10(16,17)[OF refl refl S]
        by (auto simp: minit0_init_defs init_args_def init_aggargs_def dnode_n_def Let_def
            split: formula.splits)
    next
      assume U: "\<phi> = Formula.Until \<phi>' I \<psi>'"
      show ?thesis unfolding U using 10(18,19)[OF refl refl U]
        by (auto simp: minit0_init_defs init_args_def init_aggargs_def dnode_n_def Let_def
            split: formula.splits)
    qed
  next
    case False
    then have nS: "\<forall>\<phi>' I \<psi>'. \<phi> \<noteq> Formula.Since \<phi>' I \<psi>'" and nU: "\<forall>\<phi>' I \<psi>'. \<phi> \<noteq> Formula.Until \<phi>' I \<psi>'"
      by blast+
    have ih: "fcols (length tys + n) \<phi> = mfcols (length tys + n) (minit0 (length tys + n) \<phi>)"
      using False by (cases \<phi>) (rule 10[OF refl refl], assumption | simp)+
    have "fcols n (Formula.Agg y \<omega> tys f \<phi>) =
        map_option (\<lambda>r. merge_cols (ungroup_cols (length tys) r) [y]) (fcols (length tys + n) \<phi>)"
      using nS nU by (cases \<phi>) (simp_all add: Let_def)
    then show ?thesis unfolding minit0_Agg_default[OF nS nU] ih by (simp add: init_aggargs_def)
  qed
next
  case (7 n \<phi> \<psi>)
  show ?case
  proof (cases "safe_assignment (fv \<phi>) \<psi>")
    case True
    then show ?thesis using 7(1) by simp
  next
    case sa: False
    show ?thesis
    proof (cases "safe_formula \<psi>")
      case True
      then show ?thesis using sa 7(2,3) by (simp split: option.splits)
    next
      case sf: False
      show ?thesis
      proof (cases "is_constraint \<psi>")
        case True
        then show ?thesis using sa sf 7(4) by simp
      next
        case ic: False
        have l: "fcols n (Formula.And \<phi> \<psi>) = (case \<psi> of
            Formula.Neg \<psi>' \<Rightarrow> (case (fcols n \<phi>, fcols n \<psi>') of (Some c1, Some c2) \<Rightarrow> Some c1 | _ \<Rightarrow> None)
          | Formula.Trigger \<phi>' I \<psi>' \<Rightarrow> (if safe_formula \<phi>' then fcols n \<phi>
              else case \<phi>' of Formula.Neg _ \<Rightarrow> fcols n \<phi> | _ \<Rightarrow> None)
          | Formula.Release \<phi>' I \<psi>' \<Rightarrow> fcols n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
          | _ \<Rightarrow> None)"
          using sa sf ic by simp
        have r: "minit0 n (Formula.And \<phi> \<psi>) = (case \<psi> of
            Formula.Neg \<psi> \<Rightarrow> MAnd (fv \<phi>) (minit0 n \<phi>) False (fv \<psi>) (minit0 n \<psi>) ([], [])
          | Formula.Trigger \<phi>' I \<psi>' \<Rightarrow> verimon_maux.init_and_trigger minit0 n None \<phi> \<phi>' I \<psi>'
          | Formula.Release \<phi>' I \<psi>' \<Rightarrow> minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
          | _ \<Rightarrow> MRel empty_table)"
          using sa sf ic by simp
        show ?thesis unfolding l r
          by (cases \<psi>) (simp_all add: 7(5-)[OF sa sf ic] minit0_init_defs init_args_def Let_def
              split: option.splits formula.splits)
      qed
    qed
  qed
next
  case (8 n l)
  have m: "map (\<lambda>x. mfcols n (minit0 n x)) (filter safe_formula l) = map (fcols n) (filter safe_formula l)"
    by (intro map_cong refl) (simp add: 8)
  show ?case by (simp add: Let_def o_def m)
next
  case (13 n \<phi> I \<psi>)
  then show ?case by (auto simp: minit0_init_defs init_args_def Let_def split: formula.splits)
next
  case (14 n \<phi> I \<psi>)
  then show ?case by (auto simp: minit0_init_defs init_args_def Let_def split: formula.splits)
next
  case (15 n \<phi> I \<psi>)
  then show ?case by (auto simp: minit0_init_defs init_args_def Let_def split: formula.splits)
qed (simp_all add: Let_def split: prod.splits)

function (sequential) udinit :: "nat \<Rightarrow> cols \<Rightarrow> ty Formula.formula \<Rightarrow> udformula" where
  "udinit n cs (Formula.Pred e ts) = (let mode = pred_mode_of n ts in
     if mode = Match then UDPredM e (length ts) ts cs
     else if (mode = Copy \<and> ts = map Formula.Var [0..<n] \<and> cs = [0..<n])
          \<or> (mode = Simple \<and> is_simple_pattern ts 0 \<and> cs = smp_cols ts)
     then UDPredS e (length ts)
     else UDFail)"
| "udinit n cs (Formula.Let p \<phi> \<psi>) =
     (let m = Formula.nfv \<phi> in UDLet p m (udinit m [0..<m] \<phi>) (udinit n cs \<psi>))"
| "udinit n cs (Formula.Frz p \<phi> \<psi>) =
     (let m = Formula.nfv \<phi>; d = udinit n cs \<psi> in
      UDFrz p m (udinit m [0..<m] \<phi>) d 0 0 0 [] d 0 0 [] [] (past_reach \<psi>)
        (safe_letpast (p, m) \<psi> \<le> NonFutuRec) (neg_pred (p, m) \<psi>) None d)"
| "udinit n cs (Formula.LetPast p \<phi> \<psi>) =
     (let m = Formula.nfv \<phi> in UDLetPast p m (udinit m [0..<m] \<phi>) (udinit n cs \<psi>) 0 None)"
| "udinit n cs (Formula.Eq t1 t2) = UDRel (deopt_table (dtabc n cs (eq_rel n t1 t2)))"
| "udinit n cs (Formula.Less t1 t2) = UDRel (deopt_table empty_table)"
| "udinit n cs (Formula.LessEq t1 t2) = UDRel (deopt_table empty_table)"
| "udinit n cs (Formula.Neg \<phi>) = (if fv \<phi> = {}
     then (if cs = [] then UDNeg (udinit n [] \<phi>) else UDFail)
     else UDRel (deopt_table empty_table))"
| "udinit n cs (Formula.Or \<phi> \<psi>) =
     UDOr (udinit n cs \<phi>) (udinit n cs \<psi>) (mbuf_t_empty, mbuf_t_empty)"
| "udinit n cs (Formula.And \<phi> \<psi>) =
    (if safe_assignment (fv \<phi>) \<psi> then
       (let conf = split_assignment (fv \<phi>) \<psi>; y = fst conf; t = snd conf; cs0 = rem_col cs y in
        if y \<in> set cs \<and> Formula.fv_trm t \<subseteq> set cs0
        then UDAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) (udinit n cs0 \<phi>)
        else UDFail)
     else if safe_formula \<psi> then
       (let cs1 = set_cols (fv \<phi>); cs2 = set_cols (fv \<psi>) in
        if cs = merge_cols cs1 cs2
        then UDAnd (mk_djoin cs1 cs2) (udinit n cs1 \<phi>) True (udinit n cs2 \<psi>)
               (mbuf_t_empty, mbuf_t_empty)
        else UDFail)
     else if is_constraint \<psi> then
       (let conf = split_constraint \<psi> in
        if Formula.fv_trm (fst conf) \<subseteq> set cs \<and> Formula.fv_trm (snd (snd (snd conf))) \<subseteq> set cs
        then (let d = udinit n cs \<phi>; c = reindex_constraint cs conf
              in case uset_q c d of Some d' \<Rightarrow> d' | None \<Rightarrow> UDAndRel d c)
        else UDFail)
     else (case \<psi> of
       Formula.Neg \<psi>' \<Rightarrow>
         (let cs1 = set_cols (fv \<phi>); cs2 = set_cols (fv \<psi>') in
          if cs = merge_cols cs1 cs2 \<and> fv \<psi>' \<subseteq> fv \<phi>
          then UDAnd (mk_djoin cs1 cs2) (udinit n cs1 \<phi>) False (udinit n cs2 \<psi>')
                 (mbuf_t_empty, mbuf_t_empty)
          else UDFail)
     | Formula.Trigger \<phi>' I \<psi>' \<Rightarrow>
         (let cs_R = set_cols (fv \<psi>'); \<phi>d = udinit n cs \<phi>; \<psi>d = udinit n cs_R \<psi>';
              tr = (\<lambda>b \<alpha> \<alpha>d.
            let args = init_args I n (fv \<alpha>) (fv \<psi>') b None; cs_L = set_cols (fv \<alpha>) in
            if cs = set_cols (fv \<phi>) \<and> set cs_R \<subseteq> set cs \<and> set cs_L \<subseteq> set cs_R \<and> tok cs_R cs_L args
            then UDAndTrigger (mk_djoin cs cs_R) \<phi>d (mbuf_t_empty, mbuf_t_empty)
                   (dargs cs_R cs_L args) \<alpha>d \<psi>d
                   (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
                   (ginit_mmtaux (dargs cs_R cs_L args) (dmsk cs_R cs_L))
            else UDFail) in
          if safe_formula \<phi>' then tr True \<phi>' (udinit n (set_cols (fv \<phi>')) \<phi>')
          else case \<phi>' of Formula.Neg \<alpha> \<Rightarrow> tr False \<alpha> (udinit n (set_cols (fv \<alpha>)) \<alpha>)
            | _ \<Rightarrow> UDRel (deopt_table empty_table))
     | Formula.Release \<phi>' I \<psi>' \<Rightarrow> udinit n cs (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
     | _ \<Rightarrow> UDRel (deopt_table empty_table)))"
| "udinit n cs (Formula.Ands l) =
    (let (pos, neg) = partition safe_formula l in
     case pos of [] \<Rightarrow> UDFail
     | p # ps \<Rightarrow>
       (let c0 = set_cols (fv p); css = map (\<lambda>\<psi>. set_cols (fv \<psi>)) ps;
            nss = map (\<lambda>\<psi>. set_cols (fv \<psi>)) neg in
        if cs = dands_cols c0 css
        then UDAnds (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
               (map2 (udinit n) (c0 # css @ nss) (pos @ map remove_neg neg))
               (map (\<lambda>_. mbuf_t_empty) (pos @ neg))
        else UDFail))"
| "udinit n cs (Formula.Exists T \<phi>) = UDExists (udinit (Suc n) (0 # map Suc cs) \<phi>) True"
| "udinit n cs (Formula.Agg y \<omega> tys f \<phi>) =
    (let m = length tys; g0 = fv \<phi> \<subseteq> {0..<m}; ag = init_aggargs (fv \<phi>) n g0 y \<omega> tys f;
         g = dagg_gcols ag;
         ok = (\<lambda>cs_L cs_R. set cs_L \<subseteq> set cs_R \<and> agg_cols m g = cs_R \<and> cs = merge_cols g [y] \<and>
           wf_cols n g \<and> y < n \<and> y \<notin> set g \<and> (g0 \<longrightarrow> g = []) \<and> Formula.fv_trm f \<subseteq> set cs_R) in
     case \<phi> of
       Formula.Since \<phi>' I \<psi>' \<Rightarrow>
         (let cs_R = set_cols (fv \<psi>'); \<psi>d = udinit (m + n) cs_R \<psi>'; sn = (\<lambda>b \<alpha> \<phi>d.
            let args = init_args I (m + n) (fv \<alpha>) (fv \<psi>') b (Some ag);
                cs_L = set_cols (fv \<alpha>); da = dargs cs_R cs_L args in
            if ok cs_L cs_R
            then (if cpos cs_R (set cs_L) = {}
                  then UDSince da \<phi>d \<psi>d init_mebuf2S
                         (udsx_init_agg da (g0, \<omega>, reindex_trm cs_R f, m, ins_pos g y) None)
                  else UDAgg g0 \<omega> (reindex_trm cs_R f) m (ins_pos g y)
                         (UDSince da \<phi>d \<psi>d init_mebuf2S (udsx_init da (dmsk cs_R cs_L))))
            else UDFail) in
          if safe_formula \<phi>' then sn True \<phi>' (udinit (m + n) (set_cols (fv \<phi>')) \<phi>')
          else case \<phi>' of Formula.Neg \<alpha> \<Rightarrow> sn False \<alpha> (udinit (m + n) (set_cols (fv \<alpha>)) \<alpha>)
            | _ \<Rightarrow> UDRel (deopt_table empty_table))
     | Formula.Until \<phi>' I \<psi>' \<Rightarrow>
         (let cs_R = set_cols (fv \<psi>'); \<psi>d = udinit (m + n) cs_R \<psi>'; un = (\<lambda>b \<alpha> \<phi>d.
            let args = init_args I (m + n) (fv \<alpha>) (fv \<psi>') b (Some ag);
                cs_L = set_cols (fv \<alpha>); da = dargs cs_R cs_L args in
            if ok cs_L cs_R
            then (if cpos cs_R (set cs_L) = {} \<and> memL I 0
                  then UDUntil da (dmsk cs_R cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0
                         (udux_init_agg da (g0, \<omega>, reindex_trm cs_R f, m, ins_pos g y))
                  else UDAgg g0 \<omega> (reindex_trm cs_R f) m (ins_pos g y)
                         (UDUntil da (dmsk cs_R cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)
                           mbuf_t_empty 0 (udux_init da)))
            else UDFail) in
          if safe_formula \<phi>' then un True \<phi>' (udinit (m + n) (set_cols (fv \<phi>')) \<phi>')
          else case \<phi>' of Formula.Neg \<alpha> \<Rightarrow> un False \<alpha> (udinit (m + n) (set_cols (fv \<alpha>)) \<alpha>)
            | _ \<Rightarrow> UDRel (deopt_table empty_table))
     | _ \<Rightarrow> (if cs = merge_cols g [y] \<and> set_cols (fv \<phi>) = agg_cols m g
            then UDAgg g0 \<omega> (reindex_trm (agg_cols m g) f) m (ins_pos g y)
                   (udinit (m + n) (agg_cols m g) \<phi>)
            else UDFail))"
| "udinit n cs (Formula.Prev I \<phi>) = UDPrev I (udinit n cs \<phi>) True mbuf_t_empty mbuf_t_empty"
| "udinit n cs (Formula.Next I \<phi>) = UDNext I (udinit n cs \<phi>) True mbuf_t_empty"
| "udinit n cs (Formula.Since \<phi> I \<psi>) =
    (let cs_R = set_cols (fv \<psi>); \<psi>d = udinit n cs_R \<psi>; sn = (\<lambda>b \<alpha> \<phi>d.
       let args = init_args I n (fv \<alpha>) (fv \<psi>) b None; cs_L = set_cols (fv \<alpha>) in
       if cs = cs_R \<and> set cs_L \<subseteq> set cs_R
       then UDSince (dargs cs cs_L args) \<phi>d \<psi>d init_mebuf2S
              (udsx_init (dargs cs cs_L args) (dmsk cs cs_L))
       else UDFail) in
     if safe_formula \<phi> then sn True \<phi> (udinit n (set_cols (fv \<phi>)) \<phi>)
     else case \<phi> of Formula.Neg \<alpha> \<Rightarrow> sn False \<alpha> (udinit n (set_cols (fv \<alpha>)) \<alpha>)
       | _ \<Rightarrow> UDRel (deopt_table empty_table))"
| "udinit n cs (Formula.Until \<phi> I \<psi>) =
    (let cs_R = set_cols (fv \<psi>); \<psi>d = udinit n cs_R \<psi>; un = (\<lambda>b \<alpha> \<phi>d.
       let args = init_args I n (fv \<alpha>) (fv \<psi>) b None; cs_L = set_cols (fv \<alpha>) in
       if cs = cs_R \<and> set cs_L \<subseteq> set cs_R
       then UDUntil (dargs cs cs_L args) (dmsk cs cs_L) \<phi>d \<psi>d
              (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0 (udux_init (dargs cs cs_L args))
       else UDFail) in
     if safe_formula \<phi> then un True \<phi> (udinit n (set_cols (fv \<phi>)) \<phi>)
     else case \<phi> of Formula.Neg \<alpha> \<Rightarrow> un False \<alpha> (udinit n (set_cols (fv \<alpha>)) \<alpha>)
       | _ \<Rightarrow> UDRel (deopt_table empty_table))"
| "udinit n cs (Formula.Trigger \<phi> I \<psi>) =
    (let \<psi>d = udinit n cs \<psi>; tr = (\<lambda>b \<alpha> \<phi>d.
       let args = init_args I n (fv \<alpha>) (fv \<psi>) b None; cs_L = set_cols (fv \<alpha>) in
       if fv \<psi> = set cs \<and> set cs_L \<subseteq> set cs \<and> mem I 0
       then UDTrigger (dargs cs cs_L args) (emb_plan cs cs_L) \<phi>d \<psi>d
              (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
              (ginit_mmtaux (dargs cs cs_L args) (dmsk cs cs_L))
       else UDFail) in
     if safe_formula \<phi> then tr True \<phi> (udinit n (set_cols (fv \<phi>)) \<phi>)
     else case \<phi> of Formula.Neg \<alpha> \<Rightarrow> tr False \<alpha> (udinit n (set_cols (fv \<alpha>)) \<alpha>)
       | _ \<Rightarrow> UDRel (deopt_table empty_table))"
| "udinit n cs (Formula.Release \<phi> I \<psi>) = (if mem I 0
     then udinit n cs (release_safe_0 \<phi> I \<psi>)
     else udinit n cs (release_safe_bounded \<phi> I \<psi>))"
| "udinit n cs (Formula.MatchP I r) =
    (let (mr, \<phi>s) = to_mregex r in
     case those (map (fcols n) \<phi>s) of None \<Rightarrow> UDFail
     | Some css \<Rightarrow> (if \<forall>c \<in> set css. set c \<subseteq> set cs
         then UDMatchP (length cs) I mr (sorted_list_of_set (RPDs mr)) (map (emb_plan cs) css)
                (map2 (udinit n) css \<phi>s) (map (\<lambda>_. mbuf_t_empty) \<phi>s) mbuf_t_empty []
         else UDFail))"
| "udinit n cs (Formula.MatchF I r) =
    (let (mr, \<phi>s) = to_mregex r in
     case those (map (fcols n) \<phi>s) of None \<Rightarrow> UDFail
     | Some css \<Rightarrow> (if \<forall>c \<in> set css. set c \<subseteq> set cs
         then UDMatchF (length cs) I mr (sorted_list_of_set (LPDs mr)) (map (emb_plan cs) css)
                (map2 (udinit n) css \<phi>s) (map (\<lambda>_. mbuf_t_empty) \<phi>s) mbuf_t_empty 0 []
         else UDFail))"
| "udinit n cs (Formula.TP t) =
     (let mt = mtrm_of_trm t in if cs = mtrm_dcols mt then UDTP mt 0 else UDFail)"
| "udinit n cs (Formula.TS t) =
     (let mt = mtrm_of_trm t in if cs = mtrm_dcols mt then UDTS mt else UDFail)"
  by pat_completeness auto

termination
proof ((relation "measure (\<lambda>(_, _, \<phi>). size' \<phi>)"; clarsimp), goal_cases)
  case (5 \<phi> \<phi>' I \<psi>')
  then show ?case using size'_and_release[of \<phi> \<phi>' I \<psi>'] by simp
next
  case (6 l x xs c \<psi>)
  then have "\<psi> \<in> set (filter safe_formula l @ map remove_neg (filter (Not \<circ> safe_formula) l))"
    by (auto dest: set_zip_rightD)
  then obtain x where "x \<in> set l" "size' \<psi> \<le> size' x"
    using size'_remove_neg by fastforce
  then show ?case using sum_list_mem_leq[of x l size'] by linarith
next
  case (7 \<phi> I \<psi>)
  then show ?case using size'_release_aux(4)[of \<phi> I \<psi>] by simp
next
  case (8 \<phi> I \<psi>)
  then show ?case using size'_release_aux(3)[of \<phi> I \<psi>] by simp
next
  case (9 n cs r a b xa y x2 aa ba)
  then show ?case by (clarsimp dest!: to_mregex_ok[OF sym] atms_size' set_zip_rightD)
next
  case (10 n cs r a b xa y x2 aa ba)
  then show ?case by (clarsimp dest!: to_mregex_ok[OF sym] atms_size' set_zip_rightD)
qed (case_tac \<psi>; clarsimp)+

lemma map_Rep_map2_udinit:
  "(\<And>c \<psi>. (c, \<psi>) \<in> set (zip cs \<psi>s) \<Longrightarrow> Rep_udformula (udinit n c \<psi>) = dof n c (minit0 n \<psi>)) \<Longrightarrow>
   map Rep_udformula (map2 (udinit n) cs \<psi>s) = map2 (dof n) cs (map (minit0 n) \<psi>s)"
  by (unfold zip_map2 map_map, rule map_cong[OF refl]) auto

lemma udinit_dof: "Rep_udformula (udinit n cs \<phi>) = dof n cs (minit0 n \<phi>)"
proof (induct n cs \<phi> rule: udinit.induct)
  case (10 n cs \<phi> \<psi>)
  show ?case
  proof (cases "safe_assignment (fv \<phi>) \<psi>")
    case True
    then show ?thesis using 10(1)[OF True refl refl refl refl] by (auto simp: Let_def)
  next
    case sa: False
    show ?thesis
    proof (cases "safe_formula \<psi>")
      case True
      then show ?thesis using sa 10(2,3)[OF sa True refl refl]
        by (auto simp: Let_def mbuf_t_empty.rep_eq)
    next
      case sf: False
      show ?thesis
      proof (cases "is_constraint \<psi>")
        case True
        then show ?thesis using sa sf 10(4)[OF sa sf True refl]
          by (auto simp: Let_def Rep_uset_q split: option.splits)
      next
        case ic: False
        note eqs = udinit.simps(10) default_maux.minit0.simps(8) if_not_P[OF sa] if_not_P[OF sf]
            if_not_P[OF ic]
        note ih = 10(5-)[OF sa sf ic]
        consider (N) \<chi> where "\<psi> = Formula.Neg \<chi>"
          | (T) \<phi>' I \<psi>' where "\<psi> = Formula.Trigger \<phi>' I \<psi>'"
          | (R) \<phi>' I \<psi>' where "\<psi> = Formula.Release \<phi>' I \<psi>'"
          | (O) "\<forall>\<chi>. \<psi> \<noteq> Formula.Neg \<chi>" "\<forall>\<phi>' I \<psi>'. \<psi> \<noteq> Formula.Trigger \<phi>' I \<psi>'"
            "\<forall>\<phi>' I \<psi>'. \<psi> \<noteq> Formula.Release \<phi>' I \<psi>'"
          by (cases \<psi>) auto
        then show ?thesis
        proof cases
          case N
          then show ?thesis unfolding eqs unfolding N formula.case using ih(1,2)[OF N]
            by (simp add: Let_def mbuf_t_empty.rep_eq)
        next
          case T
          note eqT = eqs verimon_maux.init_and_trigger_def Let_def
          have ih3: "cs = set_cols (fv \<phi>) \<Longrightarrow>
              Rep_udformula (udinit n (set_cols (fv \<phi>)) \<phi>) = dof n (set_cols (fv \<phi>)) (minit0 n \<phi>)"
            using ih(3)[OF T refl] by simp
          show ?thesis
          proof (cases "safe_formula \<phi>'")
            case True
            then show ?thesis unfolding eqT unfolding T formula.case if_P[OF True]
              using ih(3,4,5)[OF T] ih3
              by (auto simp: Let_def init_args_def ginit_mmtaux_bmm[symmetric] mbuf_t_empty.rep_eq)
          next
            case sf': False
            show ?thesis
            proof (cases "\<exists>\<alpha>. \<phi>' = Formula.Neg \<alpha>")
              case True
              then obtain \<alpha> where N': "\<phi>' = Formula.Neg \<alpha>" by blast
              show ?thesis unfolding eqT unfolding T formula.case if_not_P[OF sf'] unfolding N'
                using ih(3,4,6)[OF T] ih3 sf' N'
                by (auto simp: Let_def init_args_def ginit_mmtaux_bmm[symmetric] mbuf_t_empty.rep_eq)
            next
              case False
              then show ?thesis unfolding eqT unfolding T formula.case if_not_P[OF sf']
                by (cases \<phi>') (simp_all add: dsan_def)
            qed
          qed
        next
          case R
          then show ?thesis unfolding eqs unfolding R formula.case using ih(7)[OF R] by (simp add: Let_def)
        next
          case O
          then show ?thesis unfolding eqs by (cases \<psi>) (simp_all add: dsan_def)
        qed
      qed
    qed
  qed
next
  case (13 n cs y \<omega> tys f \<phi>)
  show ?case
  proof (cases "\<exists>\<phi>' I \<psi>'. \<phi> = Formula.Since \<phi>' I \<psi>' \<or> \<phi> = Formula.Until \<phi>' I \<psi>'")
    case True
    then obtain \<phi>' I \<psi>' where "\<phi> = Formula.Since \<phi>' I \<psi>' \<or> \<phi> = Formula.Until \<phi>' I \<psi>'" by blast
    then show ?thesis
    proof
      assume S: "\<phi> = Formula.Since \<phi>' I \<psi>'"
      note eqs = udinit.simps(13) default_maux.minit0.simps(11) default_mmasaux.init_since_def Let_def formula.case
      show ?thesis
      proof (cases "safe_formula \<phi>'")
        case True
        then show ?thesis unfolding S eqs if_P[OF True] using 13(16,17)[unfolded S]
          by (simp add: Let_def init_args_def init_aggargs_def dnode_n_def dsx_init_rdsx mbuf_t_empty.rep_eq
                if_distrib[where f=Rep_udformula] cong: if_cong split del: if_split)
      next
        case sf: False
        show ?thesis
        proof (cases "\<exists>\<alpha>. \<phi>' = Formula.Neg \<alpha>")
          case True
          then obtain \<alpha> where N: "\<phi>' = Formula.Neg \<alpha>" by blast
          show ?thesis unfolding S eqs if_not_P[OF sf] unfolding N
            using 13(16)[OF refl refl refl refl refl S refl]
              13(18)[OF refl refl refl refl refl S refl refl refl sf N]
            by (simp add: Let_def init_args_def init_aggargs_def dnode_n_def dsx_init_rdsx mbuf_t_empty.rep_eq
                if_distrib[where f=Rep_udformula] cong: if_cong split del: if_split)
        next
          case False
          then show ?thesis unfolding S eqs if_not_P[OF sf] by (cases \<phi>') (simp_all add: dsan_def)
        qed
      qed
    next
      assume U: "\<phi> = Formula.Until \<phi>' I \<psi>'"
      note eqs = udinit.simps(13) default_maux.minit0.simps(11) dq_muaux.init_until_def Let_def formula.case
      show ?thesis
      proof (cases "safe_formula \<phi>'")
        case True
        then show ?thesis unfolding U eqs if_P[OF True] using 13(19,20)[unfolded U]
          by (simp add: Let_def init_args_def init_aggargs_def dnode_n_def dux_init_rdux dux_init_agg_rdux mbuf_t_empty.rep_eq
                if_distrib[where f=Rep_udformula] cong: if_cong split del: if_split)
      next
        case sf: False
        show ?thesis
        proof (cases "\<exists>\<alpha>. \<phi>' = Formula.Neg \<alpha>")
          case True
          then obtain \<alpha> where N: "\<phi>' = Formula.Neg \<alpha>" by blast
          show ?thesis unfolding U eqs if_not_P[OF sf] unfolding N
            using 13(19)[OF refl refl refl refl refl U refl]
              13(21)[OF refl refl refl refl refl U refl refl refl sf N]
            by (simp add: Let_def init_args_def init_aggargs_def dnode_n_def dux_init_rdux dux_init_agg_rdux mbuf_t_empty.rep_eq
                if_distrib[where f=Rep_udformula] cong: if_cong split del: if_split)
        next
          case False
          then show ?thesis unfolding U eqs if_not_P[OF sf] by (cases \<phi>') (simp_all add: dsan_def)
        qed
      qed
    qed
  next
    case False
    then have nS: "\<forall>\<phi>' I \<psi>'. \<phi> \<noteq> Formula.Since \<phi>' I \<psi>'" and nU: "\<forall>\<phi>' I \<psi>'. \<phi> \<noteq> Formula.Until \<phi>' I \<psi>'"
      by blast+
    define g where "g = dagg_gcols (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f)"
    have ih: "cs = merge_cols g [y] \<and> set_cols (fv \<phi>) = agg_cols (length tys) g \<Longrightarrow>
        Rep_udformula (udinit (length tys + n) (agg_cols (length tys) g) \<phi>) =
        dof (length tys + n) (agg_cols (length tys) g) (minit0 (length tys + n) \<phi>)"
      using False unfolding g_def
      by (cases \<phi>) (rule 13[OF refl refl refl refl refl], assumption, assumption | simp)+
    have "udinit n cs (Formula.Agg y \<omega> tys f \<phi>) =
        (if cs = merge_cols g [y] \<and> set_cols (fv \<phi>) = agg_cols (length tys) g
         then UDAgg (fv \<phi> \<subseteq> {0..<length tys}) \<omega> (reindex_trm (agg_cols (length tys) g) f)
           (length tys) (ins_pos g y) (udinit (length tys + n) (agg_cols (length tys) g) \<phi>)
         else UDFail)"
      using nS nU unfolding g_def by (cases \<phi>) (simp_all add: Let_def)
    then show ?thesis unfolding minit0_Agg_default[OF nS nU] using ih
      by (auto simp: g_def Let_def init_aggargs_def)
  qed
next
  case (11 n cs l)
  show ?case
  proof (cases "filter safe_formula l")
    case Nil
    then show ?thesis by (simp add: Let_def)
  next
    case (Cons p ps)
    show ?thesis
    proof (cases "cs = dands_cols (set_cols (fv p)) (map (\<lambda>\<psi>. set_cols (fv \<psi>)) ps)")
      case False
      then show ?thesis using Cons by (simp add: Let_def o_def)
    next
      case True
      define negl where "negl = filter (\<lambda>x. \<not> safe_formula x) l"
      define c0 where "c0 = set_cols (fv p)"
      define css where "css = map (\<lambda>\<psi>. set_cols (fv \<psi>)) ps"
      define nss where "nss = map (\<lambda>\<psi>. set_cols (fv \<psi>)) negl"
      define L where "L = p # ps @ map remove_neg negl"
      have part: "partition safe_formula l = (p # ps, negl)"
        using Cons by (simp add: negl_def o_def)
      note ih = 11[OF refl part[symmetric] refl refl refl refl True _ refl]
      have m: "map Rep_udformula (map2 (udinit n) (c0 # css @ nss) L) =
          map2 (dof n) (c0 # css @ nss) (map (minit0 n) L)"
        unfolding c0_def css_def nss_def L_def by (rule map_Rep_map2_udinit) (rule ih, simp)
      have l: "udinit n cs (Formula.Ands l) = UDAnds (dands_plans c0 css)
          (dands_plans (dands_cols c0 css) nss) (map2 (udinit n) (c0 # css @ nss) L)
          (map (\<lambda>_. mbuf_t_empty) ((p # ps) @ negl))"
        using Cons True by (simp add: Let_def c0_def css_def nss_def L_def negl_def o_def)
      have r: "minit0 n (Formula.Ands l) =
          MAnds (map fv (p # ps)) (map fv negl) (map (minit0 n) L) (replicate (length l) [])"
        using Cons by (simp add: L_def negl_def o_def)
      have len: "length l = Suc (length ps) + length negl"
        using sum_length_filter_compl[of safe_formula l] Cons by (simp add: negl_def o_def)
      show ?thesis unfolding l r Rep_udformula.simps m using True len
        by (simp add: c0_def css_def nss_def L_def Let_def mbuf_t_empty.rep_eq o_def
            map_replicate_const)
    qed
  qed
next
  case (16 n cs \<phi> I \<psi>)
  note eqs = udinit.simps(16) default_maux.minit0.simps(14) default_mmasaux.init_since_def Let_def
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    then show ?thesis unfolding eqs if_P[OF True] using 16
      by (simp add: Let_def init_args_def dnode_n_def dsx_init_rdsx mbuf_t_empty.rep_eq)
  next
    case sf: False
    show ?thesis
    proof (cases "\<exists>\<alpha>. \<phi> = Formula.Neg \<alpha>")
      case True
      then obtain \<alpha> where N: "\<phi> = Formula.Neg \<alpha>" by blast
      show ?thesis unfolding eqs if_not_P[OF sf] unfolding N using sf[unfolded N] 16[unfolded N]
        by (simp add: Let_def init_args_def dnode_n_def dsx_init_rdsx mbuf_t_empty.rep_eq)
    next
      case False
      then show ?thesis unfolding eqs if_not_P[OF sf] by (cases \<phi>) (simp_all add: dsan_def)
    qed
  qed
next
  case (17 n cs \<phi> I \<psi>)
  note eqs = udinit.simps(17) default_maux.minit0.simps(15) dq_muaux.init_until_def Let_def
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    then show ?thesis unfolding eqs if_P[OF True] using 17
      by (simp add: Let_def init_args_def dnode_n_def dux_init_rdux mbuf_t_empty.rep_eq)
  next
    case sf: False
    show ?thesis
    proof (cases "\<exists>\<alpha>. \<phi> = Formula.Neg \<alpha>")
      case True
      then obtain \<alpha> where N: "\<phi> = Formula.Neg \<alpha>" by blast
      show ?thesis unfolding eqs if_not_P[OF sf] unfolding N using sf[unfolded N] 17[unfolded N]
        by (simp add: Let_def init_args_def dnode_n_def dux_init_rdux mbuf_t_empty.rep_eq)
    next
      case False
      then show ?thesis unfolding eqs if_not_P[OF sf] by (cases \<phi>) (simp_all add: dsan_def)
    qed
  qed
next
  case (18 n cs \<phi> I \<psi>)
  note eqs = udinit.simps(18) default_maux.minit0.simps(16) verimon_maux.init_trigger_def Let_def
  show ?case
  proof (cases "safe_formula \<phi>")
    case True
    then show ?thesis unfolding eqs if_P[OF True] using 18
      by (simp add: Let_def init_args_def dnode_n_def ginit_mmtaux_bmm[symmetric] mbuf_t_empty.rep_eq)
  next
    case sf: False
    show ?thesis
    proof (cases "\<exists>\<alpha>. \<phi> = Formula.Neg \<alpha>")
      case True
      then obtain \<alpha> where N: "\<phi> = Formula.Neg \<alpha>" by blast
      show ?thesis unfolding eqs if_not_P[OF sf] unfolding N using sf[unfolded N] 18[unfolded N]
        by (simp add: Let_def init_args_def dnode_n_def ginit_mmtaux_bmm[symmetric] mbuf_t_empty.rep_eq)
    next
      case False
      then show ?thesis unfolding eqs if_not_P[OF sf] by (cases \<phi>) (simp_all add: dsan_def)
    qed
  qed
qed (simp_all add: minit0_init_defs init_args_def dnode_n_def Let_def dsan_def
    ginit_mmtaux_bmm[symmetric] zip_map2 o_def fcols_mfcols
    mbuf_t_empty.rep_eq mbuf_t_append.rep_eq split: list.splits option.splits prod.splits
    cong: map_cong)

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
       dmstate_m = Rep_udformula (udmstate_m st),
       dmstate_n = udmstate_n st, dmstate_cs = udmstate_cs st, dmstate_t = udmstate_t st \<rparr>"

definition udminit_safe :: "ty Formula.formula \<Rightarrow> udmstate" where
  "udminit_safe \<phi> = (if mmonitorable_exec \<phi>
     then (let n = Formula.nfv \<phi>; cs = set_cols (Formula.fv \<phi>) in
       \<lparr>udmstate_i = 0, udmstate_j = 0, udmstate_m = udinit n cs \<phi>, udmstate_n = n,
        udmstate_cs = cs, udmstate_t = mbuf_t_empty\<rparr>)
     else undefined)"

lemma Rep_udminit_safe:
  assumes "mmonitorable \<phi>"
  shows "Rep_udmstate (udminit_safe \<phi>) = dof_state (Formula.nfv \<phi>) (set_cols (Formula.fv \<phi>)) (minit_safe \<phi>)"
  using assms
  by (simp add: udminit_safe_def Rep_udmstate_def dof_state_def default_maux.minit_safe_def
      default_maux.minit_def udinit_dof monitorable_formula_code Let_def)

lemma vdfail_nodes_Rep_udmstate:
  "vdfail_nodes (dmstate_m (Rep_udmstate st)) = uvdfail_nodes (udmstate_m st)"
  by (simp add: Rep_udmstate_def vdfail_nodes_Rep)
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
    by (simp add: udeval_Rep e dannotate_map[where acc = "[]", simplified] d)
qed

(*<*)
end
(*>*)
