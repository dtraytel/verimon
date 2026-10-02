(*<*)
theory Dense_Unbox_Exec
  imports Dense_Agg_Cache
begin
(*>*)

section \<open>The executable dense evaluator\<close>

text \<open>
  @{const deval} keeps its buffers in lists and its fused aggregation windows in the structures
  of @{theory MFODL_Monitor_Dense.Dense_Evt_Agg} and @{theory MFODL_Monitor_Dense.Dense_Evt_UAgg}.
  This theory states the same evaluator, @{text udeval}, with its buffers in queues
  (@{typ "'a mbuf_t"}), the fused windows of @{theory MFODL_Monitor_Dense.Dense_Unbox_Eval},
  @{theory MFODL_Monitor_Dense.Dense_Unbox_UAgg} and @{theory MFODL_Monitor_Dense.Dense_Agg_Cache},
  and the constraint over a fused aggregating Since node carried by the node as its guard.  The
  theorem @{text udeval_Rep} at the end says that the two evaluators agree exactly: running
  @{const deval} on the represented state is running @{text udeval} and representing its
  results.  No invariant is needed, because every operation commutes with the representation on
  every input.  So the simulation of the kernel by @{const deval}
  (@{theory MFODL_Monitor_Dense.Dense_Eval}) is a simulation by @{text udeval}, and the generated
  code runs the latter.
\<close>

subsection \<open>The Since and Until structures, dispatched\<close>

text \<open>The structure of a fused aggregating window carries the node's guard: the constraint the
  node's own result is read through, if it has one.  Only the read looks at it; every other
  operation passes it along, and the dense structure it stands for does not have it at all --
  there the constraint stays a filter over the node.\<close>

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

text \<open>The dense structure reports the node's whole result and the node filters it; the
  executable one reports the filtered result straight away.\<close>

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
      uebufn "ts mbuf_t" "event_data mr\<delta>aux"
  | UDMatchF nat \<I> mregex "mregex list" "nat option list list" "udformula list"
      uebufn "ts mbuf_t" ts "event_data ml\<delta>aux"

text \<open>A guarded Since node stands for the dense node read through the constraint: the guard is
  the executable evaluator's alone, and the two agree because filtering the whole result is
  filtering the groups as they are read.\<close>

definition dandrel :: "uconstr option \<Rightarrow> dformula \<Rightarrow> dformula" where
  "dandrel q e = (case q of None \<Rightarrow> e | Some c \<Rightarrow> DAndRel e c)"

lemma dandrel_None[simp]: "dandrel None e = e"
  by (simp add: dandrel_def)

lemma deval_dandrel:
  "deval j ts db (dandrel q e)
   = (case deval j ts db e of (zs, e') \<Rightarrow> (map (ufilt q) zs, dandrel q e'))"
  by (simp add: dandrel_def ufilt_Some split: option.splits prod.splits)

lemma vdfail_nodes_dandrel[simp]: "vdfail_nodes (dandrel q e) = vdfail_nodes e"
  by (simp add: dandrel_def split: option.splits)

fun Rep_udformula :: "udformula \<Rightarrow> dformula" where
  "Rep_udformula UDFail = DFail"
| "Rep_udformula (UDRel rel) = DRel rel"
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
     DPrev I (Rep_udformula \<phi>) first (Rep_mbuf_t buf) (Rep_mbuf_t nts)"
| "Rep_udformula (UDNext I \<phi> first nts) = DNext I (Rep_udformula \<phi>) first (Rep_mbuf_t nts)"
| "Rep_udformula (UDAnds ps ns L buf) =
     DAnds ps ns (map Rep_udformula L) (map Rep_mbuf_t buf)"
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
     DFrz p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) jfrz jpsi0 jphi \<alpha>s
       (Rep_udformula \<rho>) w pR tq rb d po ng lv (Rep_udformula \<rho>L)"
| "Rep_udformula (UDLetPast p m \<phi> \<psi> i buf) =
     DLetPast p m (Rep_udformula \<phi>) (Rep_udformula \<psi>) i buf"
| "Rep_udformula (UDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     DTrigger dags pl (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbuf) (Rep_mbuf_t nts) daux"
| "Rep_udformula (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     DAndTrigger pl (Rep_udformula \<alpha>) (rbufo dbf1) dags
       (Rep_udformula \<phi>) (Rep_udformula \<psi>) (rbuf2 dbf2) (Rep_mbuf_t nts) daux"
| "Rep_udformula (UDMatchP m I mr mrs pls Ld dbuf nts daux) =
     DMatchP m I mr mrs pls (map Rep_udformula Ld) (map Rep_mbuf_t dbuf) (Rep_mbuf_t nts) daux"
| "Rep_udformula (UDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     DMatchF m I mr mrs pls (map Rep_udformula Ld) (map Rep_mbuf_t dbuf) (Rep_mbuf_t nts) t daux"

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

text \<open>The two agree on the whole run: the dense evaluator's results, read through the node's
  guard, are the executable evaluator's.  The accumulator is carried the same way, so the
  statement relates the two lists it is started with.\<close>

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

subsection \<open>The size of the represented formula\<close>

text \<open>The guarded Since node stands for two dense nodes, so the executable formula's own size is
  not that of the dense one it stands for.  The two guards of the evaluator that compare formulas,
  the one keeping the freeze's live copy and the one of the recursive let, compare the size of the
  represented formula instead, computed on the executable one; so they take the dense evaluator's
  branches on every formula, and the evaluator terminates by the same measure.\<close>

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

subsection \<open>The evaluator\<close>

function (sequential) udeval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> udformula \<Rightarrow>
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
      else let (zs, buf', nts') = meprev_next I (buf @@ xs) (nts @@ ts)
        in (if first then {} # zs else zs, UDPrev I \<phi>' False buf' nts'))"
| "udeval j ts db (UDNext I \<phi> first nts) =
     (let (xs, \<phi>') = udeval j ts db \<phi>;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
      in (zs, UDNext I \<phi>' first' nts'))"
| "udeval j ts db (UDAnds ps ns Ld dbuf) =
     (let R = map (udeval j ts db) Ld;
          (zs, dbuf') = mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty
            (mebufn_add (map fst R) dbuf)
      in (Rep_mbuf_t zs, UDAnds ps ns (map snd R) dbuf'))"
| "udeval j ts db (UDSince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (zs, buf', aux') = uedsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux
      in (zs, UDSince dags \<phi>' \<psi>' buf' aux'))"
| "udeval j ts db (UDUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = udeval j ts db \<phi>; (ys, \<psi>') = udeval j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (udux_add_new dags msk) aux
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
          ((zs, daux'), dbuf', nts') = mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
            (mebuf2_add xs ys dbuf) (nts @@ ts)
      in (zs, UDTrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "udeval j ts db (UDMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (udeval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mebufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @@ [z], ax)) (mbuf_t_empty, daux)
             (mebufn_add (map fst R) dbuf) 0 (nts @@ ts)
      in (Rep_mbuf_t zs,
          UDMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "udeval j ts db (UDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (udeval j ts db) Ld;
          (daux', dbuf', nt, nts') = mebufnt_take
             (\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels)
             daux (mebufn_add (map fst R) dbuf) t (nts @@ ts);
          (zs, daux'') = geval_matchF I mr nt daux'
      in (zs,
          UDMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
| "udeval j ts db (UDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     (let (as, \<alpha>') = udeval j ts db \<alpha>; (xs, \<phi>') = udeval j ts db \<phi>;
          (ys, \<psi>') = udeval j ts db \<psi>;
          ((ws, daux'), dbf2', nts') = mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (ws @ [if gmmtaux_empty ax then None
                      else Some (gresult_mmtaux dags ax)], ax)) ([], daux)
            (mebuf2_add xs ys dbf2) (nts @@ ts);
          (zs, dbf1') = mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> gbin_join pl r1 True z) (mebuf2_add as ws dbf1)
      in (zs, UDAndTrigger pl \<alpha>' dbf1' dags \<phi>' \<psi>' dbf2' nts' daux'))"
  by pat_completeness (simp_all only: prod.inject udformula.inject udformula.distinct simp_thms)

lemma psize_snd_udeval:
  "udeval_dom (j, ts, db, \<phi>) \<Longrightarrow> ursize (snd (udeval j ts db \<phi>)) = ursize \<phi>"
proof (induct rule: udeval.pinduct)
  case (11 j ts db I \<phi> first buf nts) \<comment> \<open>\<^const>\<open>UDPrev\<close>\<close>
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "meprev_next I (buf @@ xs) (nts @@ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "ursize \<phi>' = ursize \<phi>"
    using 11(2) \<phi>' by simp
  then show ?case
    by (simp add: udeval.psimps(11)[OF 11(1)] \<phi>' mp del: meprev_next.simps)
next
  case (14 j ts db dags \<phi> \<psi> buf aux) \<comment> \<open>\<^const>\<open>UDSince\<close>\<close>
  obtain xs \<phi>' where \<phi>': "udeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain ys \<psi>' where \<psi>': "udeval j ts db \<psi> = (ys, \<psi>')"
    by fastforce
  obtain zs buf' aux' where e: "uedsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux = (zs, buf', aux')"
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

end
