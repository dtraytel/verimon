(*<*)
theory Dense_Eval
  imports Dense
begin
(*>*)

section \<open>The dense evaluator simulates the kernel's\<close>

text \<open>
  Every theorem of @{theory MFODL_Monitor_Imp.Dense} needs its operand tables to be finite and
  well formed over the node's columns.  That is not a property of a single call but of a
  formula's whole future, so it is stated coinductively: @{term "produces n A \<phi>"} says that
  @{const meval} on @{term \<phi>} only ever yields finite tables over @{term A}, and that its
  successors do the same.  The kernel's own well-formedness invariant implies it, which is
  where -- and the only place where -- this development touches the kernel's correctness proof.
\<close>

abbreviation (input) ftable :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> bool" where
  "ftable n A X \<equiv> table n A X \<and> finite X"

text \<open>
  A database is well formed when the table stored at a name of arity @{term ar} holds tuples of
  that width with no holes -- which is what the trace's own databases look like.  The dense
  formula only ever reads a database at a genuine input predicate (a let-bound one is always
  inside a @{term DPure} node, where the kernel's own evaluator handles it), so this is exactly
  the condition its predicate nodes need.  The tables are also required to be finite: the dense
  multi-way join and the dense aggregation need it, and it cannot come from anywhere else -- the
  kernel's own invariant does not carry finiteness (@{term qtable} does not), and the trace does
  not either.  It is a property of the input, and a real log has it.
\<close>

definition wf_db :: "database \<Rightarrow> bool" where
  "wf_db db \<longleftrightarrow> (\<forall>e ar X. Mapping.lookup db (e, ar) = Some X \<longrightarrow>
     list_all (\<lambda>T. table ar {0..<ar} T \<and> finite T) X)"

lemma wf_dbD:
  "wf_db db \<Longrightarrow> Mapping.lookup db (e, ar) = Some X \<Longrightarrow> T \<in> set X \<Longrightarrow>
     table ar {0..<ar} T"
  by (auto simp: wf_db_def list_all_iff)

lemma wf_dbD_finite:
  "wf_db db \<Longrightarrow> Mapping.lookup db (e, ar) = Some X \<Longrightarrow> T \<in> set X \<Longrightarrow> finite T"
  by (auto simp: wf_db_def list_all_iff)

coinductive produces :: "nat \<Rightarrow> nat set \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool"
  where produces: "(\<And>j ts db xs \<phi>'. wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable n A) xs \<and> produces n A \<phi>') \<Longrightarrow> produces n A \<phi>"

lemma produces_step:
  "produces n A \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
     list_all (ftable n A) xs \<and> produces n A \<phi>'"
  by (erule produces.cases) blast

lemma produces_tables:
  "produces n A \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
     list_all (ftable n A) xs"
  by (drule produces_step) auto

lemma produces_next:
  "produces n A \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> produces n A \<phi>'"
  by (drule produces_step) auto

section \<open>The dense formula\<close>

text \<open>
  A dense formula mirrors the kernel's @{typ "('msaux, 'muaux, 'mtaux) mformula"} node by node,
  but every node carries the data the short representation needs instead of the data the wide
  one needs: a join plan instead of two variable sets, a term already reindexed against the
  operand's column list, a mask at the boundary.  @{term "DPure \<phi> m msk"} is the escape hatch:
  it runs the kernel's own evaluator on a subformula and narrows its output, so a dense formula
  need not cover every node of the kernel's language to be usable.
\<close>

datatype dformula =
    DPure "(mmasaux, muaux_dq, event_data mmtaux) mformula" nat "bool list"
  | DRel "event_data table"
  | DPredS Formula.name nat
  | DPredM Formula.name nat "Formula.trm list" cols
  | DAndRel dformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | DNeg dformula
  | DExists dformula bool
  | DAgg bool "ty Formula.agg_op" Formula.trm nat nat dformula
  | DOr dformula dformula "event_data mbuf2"
  | DAnd djoin_plan dformula bool dformula "event_data mbuf2"
  | DPrev \<I> dformula bool "event_data table list" "ts list"
  | DNext \<I> dformula bool "ts list"
  | DAnds "djoin_plan list" "djoin_plan list" "dformula list" "event_data mbufn"
  | DSince args "nat option list" dformula dformula "event_data mbuf2S" mmasaux
  | DUntil args "nat option list" dformula dformula "event_data mbuf2" "ts list" ts muaux_dq

fun deval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> dformula \<Rightarrow> event_data table list \<times> dformula"
  and deval_list :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> dformula list \<Rightarrow>
    (event_data table list \<times> dformula) list" where
  "deval_list j ts db [] = []"
| "deval_list j ts db (\<phi> # r) = deval j ts db \<phi> # deval_list j ts db r"
| "deval j ts db (DPure \<phi> m msk) =
     (let (xs, \<phi>') = meval j m ts db \<phi> in (map (dnarrow msk) xs, DPure \<phi>' m msk))"
| "deval j ts db (DRel rel) = (replicate (length ts) rel, DRel rel)"
| "deval j ts db (DPredS e ar) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) empty_table
       | Some xs \<Rightarrow> xs), DPredS e ar)"
| "deval j ts db (DPredM e ar tms cs) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) empty_table
       | Some xs \<Rightarrow> map (dmatch_table tms cs) xs), DPredM e ar tms cs)"
| "deval j ts db (DAndRel \<phi> conf) =
     (let (xs, \<phi>') = deval j ts db \<phi>
      in (map (Set.filter (eval_constraint conf)) xs, DAndRel \<phi>' conf))"
| "deval j ts db (DNeg \<phi>) =
     (let (xs, \<phi>') = deval j ts db \<phi>
      in (map (\<lambda>r. if r = empty_table then unit_table 0 else empty_table) xs, DNeg \<phi>'))"
| "deval j ts db (DExists \<phi> drop0) =
     (let (xs, \<phi>') = deval j ts db \<phi>
      in (if drop0 then map (\<lambda>r. tl ` r) xs else xs, DExists \<phi>' drop0))"
| "deval j ts db (DAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = deval j ts db \<phi> in (map (dagg g0 \<omega> f k pos) xs, DAgg g0 \<omega> f k pos \<phi>'))"
| "deval j ts db (DOr \<phi> \<psi> buf) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          (zs, buf') = mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add xs ys buf)
      in (zs, DOr \<phi>' \<psi>' buf'))"
| "deval j ts db (DAnd pl \<phi> pos \<psi> buf) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          (zs, buf') = mbuf2_take (\<lambda>r1 r2. dbin_join pl r1 pos r2) (mbuf2_add xs ys buf)
      in (zs, DAnd pl \<phi>' pos \<psi>' buf'))"
| "deval j ts db (DPrev I \<phi> first buf nts) =
     (let (xs, \<phi>') = deval j ts db \<phi>
      in if first \<and> ts = [] then ([], DPrev I \<phi>' True (buf @ xs) (nts @ ts))
      else let (zs, buf', nts') = mprev_next I (buf @ xs) (nts @ ts)
        in (if first then empty_table # zs else zs, DPrev I \<phi>' False buf' nts'))"
| "deval j ts db (DNext I \<phi> first nts) =
     (let (xs, \<phi>') = deval j ts db \<phi>;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = mprev_next I xs (nts @ ts)
      in (zs, DNext I \<phi>' first' nts'))"
| "deval j ts db (DAnds ps ns Ld dbuf) =
     (let R = deval_list j ts db Ld;
          (zs, dbuf') = mbufn_take (\<lambda>as zs. zs @ [dmulti_join ps ns as]) []
            (mbufn_add (map fst R) dbuf)
      in (zs, DAnds ps ns (map snd R) dbuf'))"
| "deval j ts db (DSince dags pl \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          (zs, buf', aux') =
            meval_since dags [] (mbuf2S_add (map (dembedp pl) xs) ys ts buf) aux
      in (zs, DSince dags pl \<phi>' \<psi>' buf' aux'))"
| "deval j ts db (DUntil dags pl \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          (aux', buf', nt, nts') = mbuf2t_take (add_new_muaux_dq dags) aux
            (mbuf2_add (map (dembedp pl) xs) ys buf) t (nts @ ts);
          (zs, aux'') = eval_muaux_dq dags nt aux'
      in (zs, DUntil dags pl \<phi>' \<psi>' buf' nts' nt aux''))"

section \<open>The simulation relation\<close>

text \<open>
  @{term "dsim n cs \<phi>d \<phi>"} relates a dense formula to a kernel one at a frame of width
  @{term n} whose live columns are @{term cs}.  Every rule carries the node's own
  @{const produces}, so the relation alone gives the operand well-formedness that the
  @{theory MFODL_Monitor_Imp.Dense} theorems ask for, at every node and after every step.
\<close>

abbreviation (input) wf_cols :: "nat \<Rightarrow> cols \<Rightarrow> bool" where
  "wf_cols n cs \<equiv> sorted_wrt (<) cs \<and> (\<forall>c \<in> set cs. c < n)"

definition dbuf2 :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> event_data mbuf2 \<Rightarrow> event_data mbuf2 \<Rightarrow> bool" where
  "dbuf2 n cs1 cs2 buf dbuf \<longleftrightarrow>
     list_all (ftable n (set cs1)) (fst buf) \<and> list_all (ftable n (set cs2)) (snd buf) \<and>
     dbuf = (map (dtabc n cs1) (fst buf), map (dtabc n cs2) (snd buf))"

definition dbufn :: "nat \<Rightarrow> cols list \<Rightarrow> event_data mbufn \<Rightarrow> event_data mbufn \<Rightarrow> bool" where
  "dbufn n css buf dbuf \<longleftrightarrow> length buf = length css \<and>
     (\<forall>i < length css. list_all (ftable n (set (css ! i))) (buf ! i)) \<and>
     dbuf = map2 map (map (dtabc n) css) buf"

text \<open>
  The relation carries a timestamp bound: @{term "dsim n cs tw \<phi>d \<phi>"} is read as \<open>every
  timestamp stored anywhere inside is at most tw\<close>.  Only the temporal nodes look at it -- the
  verified Since structure accepts a new timestamp only at or after the one it is already at, and
  a fresh batch of timestamps arrives at the node from outside, where the relation cannot see it.
  Every other rule carries the bound without using it.  After a step the bound moves to the last
  timestamp of the batch.
\<close>

definition dnext :: "ts \<Rightarrow> ts list \<Rightarrow> ts" where
  "dnext tw ts = (if ts = [] then tw else last ts)"

lemma dnext_ge: "\<forall>t \<in> set ts. tw \<le> t \<Longrightarrow> tw \<le> dnext tw ts"
  by (auto simp: dnext_def)

lemma dnext_bound: "sorted ts \<Longrightarrow> \<forall>t \<in> set ts. t \<le> dnext tw ts"
proof (induct ts rule: rev_induct)
  case (snoc a ts) then show ?case by (auto simp: dnext_def sorted_append)
qed (simp add: dnext_def)

subsection \<open>The Since structure at the dense frame, and its buffer\<close>

text \<open>
  The dense Since node runs the verified structure at @{const dargs} (20.6).  What the node
  carries is the pair of structures -- the wide one the kernel steps and the dense one -- related
  through the abstract auxiliary list they are both valid for, together with the two buffers.  The
  current timestamp is shared: the structure's, and the lower bound on the timestamps still in the
  buffer.  The left operand's tables enter the buffer already embedded into the wider dense frame,
  which by @{thm [source] dembed_dtabc} is the same as narrowing them at the right operand's
  columns.
\<close>

definition dsince_rel :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    mmasaux \<Rightarrow> mmasaux \<Rightarrow> event_data mbuf2S \<Rightarrow> event_data mbuf2S \<Rightarrow> bool" where
  "dsince_rel n cs_R cs_L args tw aux daux buf dbuf \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmasaux args cur aux auxlist \<and>
        dsaux n cs_R cs_L args cur daux auxlist \<and> cur \<le> tw \<and>
        (case buf of (xs, ys, tss, sk) \<Rightarrow>
           list_all (ftable n (set cs_L)) xs \<and> list_all (ftable n (set cs_R)) ys \<and>
           sorted tss \<and> (\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw) \<and>
           dbuf = (map (dtabc n cs_R) xs, map (dtabc n cs_R) ys, tss, sk)))"

lemma dsince_relI:
  "valid_mmasaux args cur aux auxlist \<Longrightarrow> dsaux n cs_R cs_L args cur daux auxlist \<Longrightarrow>
   cur \<le> tw \<Longrightarrow>
   list_all (ftable n (set cs_L)) xs \<Longrightarrow> list_all (ftable n (set cs_R)) ys \<Longrightarrow>
   sorted tss \<Longrightarrow> \<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw \<Longrightarrow>
   dsince_rel n cs_R cs_L args tw aux daux (xs, ys, tss, sk)
     (map (dtabc n cs_R) xs, map (dtabc n cs_R) ys, tss, sk)"
  unfolding dsince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma dsince_relE:
  assumes "dsince_rel n cs_R cs_L args tw aux daux (xs, ys, tss, sk) dbuf"
  obtains cur auxlist where "valid_mmasaux args cur aux auxlist"
    and "dsaux n cs_R cs_L args cur daux auxlist" and "cur \<le> tw"
    and "list_all (ftable n (set cs_L)) xs" and "list_all (ftable n (set cs_R)) ys"
    and "sorted tss" and "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and "dbuf = (map (dtabc n cs_R) xs, map (dtabc n cs_R) ys, tss, sk)"
  using assms unfolding dsince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma dsince_relD_buf:
  "dsince_rel n cs_R cs_L args tw aux daux buf dbuf \<Longrightarrow>
     dbuf = (map (dtabc n cs_R) (fst buf), map (dtabc n cs_R) (fst (snd buf)),
             fst (snd (snd buf)), snd (snd (snd buf)))"
  by (cases buf) (auto elim!: dsince_relE)

text \<open>Widening the bound is harmless, which is what the node needs when a new batch of
  timestamps arrives.\<close>

lemma dsince_rel_mono:
  "dsince_rel n cs_R cs_L args tw aux daux buf dbuf \<Longrightarrow> tw \<le> tw' \<Longrightarrow>
     dsince_rel n cs_R cs_L args tw' aux daux buf dbuf"
  unfolding dsince_rel_def by (fastforce simp del: valid_mmasaux.simps)

text \<open>A fresh batch of operand tables and timestamps enters the buffer at both frames at once.
  The batch's timestamps are all at or after the old bound, and the buffer's are all at or before
  it, so the concatenation stays sorted and the new bound is the batch's last timestamp.\<close>

lemma dsince_rel_add:
  assumes r: "dsince_rel n cs_R cs_L args tw aux daux buf dbuf"
    and lx: "list_all (ftable n (set cs_L)) xs" and ly: "list_all (ftable n (set cs_R)) ys"
    and s: "sorted ts" and b: "\<forall>t \<in> set ts. tw \<le> t"
  shows "dsince_rel n cs_R cs_L args (dnext tw ts) aux daux (mbuf2S_add xs ys ts buf)
     (mbuf2S_add (map (dtabc n cs_R) xs) (map (dtabc n cs_R) ys) ts dbuf)"
proof (cases buf)
  case (fields us vs tss sk)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsaux n cs_R cs_L args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable n (set cs_L)) us" and lv: "list_all (ftable n (set cs_R)) vs"
    and st: "sorted tss" and ct: "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_R) us, map (dtabc n cs_R) vs, tss, sk)"
    using r unfolding fields by (rule dsince_relE)
  have "sorted (tss @ ts)" using st s ct b
    by (fastforce simp: sorted_append intro: order_trans)
  moreover have "\<forall>t \<in> set (tss @ ts). cur \<le> t \<and> t \<le> dnext tw ts"
    using ct b ctw dnext_ge[OF b] dnext_bound[OF s] by fastforce
  ultimately show ?thesis unfolding fields dbuf
    using dsince_relI[OF vw vd order_trans[OF ctw dnext_ge[OF b]],
      of "us @ xs" "vs @ ys" "tss @ ts" sk] lu lx lv ly
    by simp
qed

subsection \<open>The Until structure at the dense frame, and its buffer\<close>

text \<open>
  The Until node's state is the pair of verified structures, related through the abstract
  auxiliary list they are both valid for, together with the current timestamp.  Since the
  structure is stepped from inside a buffer traversal, that part is factored out on its own.
\<close>

definition duaux_rel :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> muaux_dq \<Rightarrow> bool" where
  "duaux_rel n cs_R cs_L args cur aux daux \<longleftrightarrow>
     (\<exists>auxlist. valid_muaux_dq args cur aux auxlist \<and>
        duaux n cs_R cs_L args cur daux auxlist)"

lemma duaux_rel_step:
  assumes v: "duaux_rel n cs_R cs_L args u aux daux"
    and sR: "sorted_wrt (<) cs_R" and bR: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
    and t1: "table n (set cs_L) a" and t2: "table n (set cs_R) b" and ut: "u \<le> t"
  shows "duaux_rel n cs_R cs_L args t (add_new_muaux_dq args a b t aux)
     (add_new_muaux_dq (dargs cs_R cs_L args) (dtabc n cs_R a) (dtabc n cs_R b) t daux)"
proof -
  obtain auxlist where vw: "valid_muaux_dq args u aux auxlist"
    and vd: "duaux n cs_R cs_L args u daux auxlist"
    using v unfolding duaux_rel_def by blast
  have "valid_muaux_dq args t (add_new_muaux_dq args a b t aux) (update_until args a b t auxlist)"
    by (rule valid_add_new_muaux_dq[OF vw _ _ ut]) (use t1 t2 an aL aR in simp_all)
  moreover have "duaux n cs_R cs_L args t
      (add_new_muaux_dq (dargs cs_R cs_L args) (dtabc n cs_R a) (dtabc n cs_R b) t daux)
      (update_until args a b t auxlist)"
    by (rule duaux_add_new[OF vd sR bR sub t1 t2 ut])
  ultimately show ?thesis unfolding duaux_rel_def by blast
qed

lemma duaux_rel_eval:
  assumes v: "duaux_rel n cs_R cs_L args cur aux daux" and nt: "cur \<le> nt"
    and agg: "args_agg args = None"
    and we: "eval_muaux_dq args nt aux = (zs, aux')"
    and de: "eval_muaux_dq (dargs cs_R cs_L args) nt daux = (dzs, daux')"
  shows "dzs = map (dtabc n cs_R) zs \<and> duaux_rel n cs_R cs_L args cur aux' daux'"
proof -
  obtain auxlist where vw: "valid_muaux_dq args cur aux auxlist"
    and vd: "duaux n cs_R cs_L args cur daux auxlist"
    using v unfolding duaux_rel_def by blast
  obtain res auxlist' where eu: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
    by (cases "eval_until (args_ivl args) nt auxlist")
  have w: "valid_muaux_dq args cur aux' auxlist' \<and> zs = map (eval_args_agg args) res"
    by (rule valid_eval_muaux_dq[OF vw nt we eu])
  have d: "dzs = map (dtabc n cs_R) res \<and> duaux n cs_R cs_L args cur daux' auxlist'"
    by (rule duaux_eval[OF vd nt de eu])
  show ?thesis using w d agg unfolding duaux_rel_def by auto
qed

text \<open>The node relation.  The stored timestamp is at or after the structure's current one and
  at or before the bound, and so is every timestamp still queued.\<close>

definition duntil_rel :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> muaux_dq \<Rightarrow> event_data mbuf2 \<Rightarrow> event_data mbuf2 \<Rightarrow>
    ts list \<Rightarrow> bool" where
  "duntil_rel n cs_R cs_L args tw t aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur. duaux_rel n cs_R cs_L args cur aux daux \<and> cur \<le> t \<and> t \<le> tw \<and>
        list_all (ftable n (set cs_L)) (fst buf) \<and>
        list_all (ftable n (set cs_R)) (snd buf) \<and>
        dbuf = (map (dtabc n cs_R) (fst buf), map (dtabc n cs_R) (snd buf)) \<and>
        sorted nts \<and> (\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw))"

text \<open>
  One firing of the Until node: the buffer traversal steps the two structures in lockstep, and
  then one evaluation at the timestamp the traversal reports yields the narrowing of what the wide
  one yields.
\<close>

lemma until_step_rel:
  assumes sR: "sorted_wrt (<) cs_R" and bR: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R" and agg: "args_agg args = None"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
    and rel: "duntil_rel n cs_R cs_L args tw t aux daux buf dbuf nts"
    and ta: "list_all (ftable n (set cs_L)) as" and tb: "list_all (ftable n (set cs_R)) bs"
    and s: "sorted tss" and bnd: "\<forall>u \<in> set tss. tw \<le> u"
    and we: "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ tss)
      = (aux1, buf1, nt, nts1)"
    and de: "mbuf2t_take (add_new_muaux_dq (dargs cs_R cs_L args)) daux
      (mbuf2_add (map (dtabc n cs_R) as) (map (dtabc n cs_R) bs) dbuf) t (nts @ tss)
      = (daux1, dbuf1, dnt, dnts1)"
    and wev: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    and dev: "eval_muaux_dq (dargs cs_R cs_L args) dnt daux1 = (dzs, daux2)"
  shows "dzs = map (dtabc n cs_R) zs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
     dbuf1 = (map (dtabc n cs_R) (fst buf1), map (dtabc n cs_R) (snd buf1)) \<and>
     duntil_rel n cs_R cs_L args (dnext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
proof -
  obtain cur where vr: "duaux_rel n cs_R cs_L args cur aux daux"
    and ct: "cur \<le> t" and ttw: "t \<le> tw"
    and lu: "list_all (ftable n (set cs_L)) (fst buf)"
    and lv: "list_all (ftable n (set cs_R)) (snd buf)"
    and dbe: "dbuf = (map (dtabc n cs_R) (fst buf), map (dtabc n cs_R) (snd buf))"
    and sn: "sorted nts" and cn: "\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw"
    using rel unfolding duntil_rel_def by blast
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mda: "mbuf2_add (map (dtabc n cs_R) as) (map (dtabc n cs_R) bs) dbuf
      = (map (dtabc n cs_R) us, map (dtabc n cs_R) vs)"
    unfolding dbe us_def vs_def by (cases buf) simp
  have lus: "list_all (ftable n (set cs_L)) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable n (set cs_R)) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a b t' u z z'. a \<in> set us \<Longrightarrow> b \<in> set vs \<Longrightarrow>
      duaux_rel n cs_R cs_L args u z z' \<Longrightarrow> u \<le> t' \<Longrightarrow>
      duaux_rel n cs_R cs_L args t' (add_new_muaux_dq args a b t' z)
        (add_new_muaux_dq (dargs cs_R cs_L args) (dtabc n cs_R a) (dtabc n cs_R b) t' z')"
    using lus lvs by (intro duaux_rel_step[OF _ sR bR sub an aL aR]) (auto simp: list_all_iff)
  have sts: "sorted (nts @ tss)"
    using sn s cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>u \<in> set (nts @ tss). cur \<le> u" using cn bnd ct ttw by fastforce
  have tdn: "t \<le> dnext tw tss" using ttw dnext_ge[OF bnd] by simp
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext tw tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF s] by fastforce
  have we': "mbuf2t_take (add_new_muaux_dq args) aux (us, vs) t (nts @ tss)
      = (aux1, (b1, b2), nt, nts1)" using we unfolding ma bfs by simp
  have de': "mbuf2t_take (add_new_muaux_dq (dargs cs_R cs_L args)) daux
      (map (dtabc n cs_R) us, map (dtabc n cs_R) vs) t (nts @ tss) = (daux1, dbuf1, dnt, dnts1)"
    using de unfolding mda by simp
  have R: "(\<exists>u. duaux_rel n cs_R cs_L args u aux1 daux1 \<and> u \<le> nt \<and>
        (\<forall>v \<in> set nts1. u \<le> v)) \<and> sorted nts1 \<and>
      (nt = t \<or> nt \<in> set (nts @ tss)) \<and> set nts1 \<subseteq> set (nts @ tss) \<and>
      dbuf1 = (map (dtabc n cs_R) b1, map (dtabc n cs_R) b2) \<and> dnt = nt \<and> dnts1 = nts1"
    by (rule mbuf2t_take_rel_ts[OF step vr ct sts cts we' de'])
  obtain u where vu: "duaux_rel n cs_R cs_L args u aux1 daux1" and unt: "u \<le> nt"
    and un: "\<forall>v \<in> set nts1. u \<le> v" using R by blast
  have dn: "dnt = nt" and dns: "dnts1 = nts1" and sn1: "sorted nts1"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf: "dbuf1 = (map (dtabc n cs_R) b1, map (dtabc n cs_R) b2)" using R by blast+
  have ntdn: "nt \<le> dnext tw tss" using R tdn bound by blast
  have ev: "dzs = map (dtabc n cs_R) zs \<and> duaux_rel n cs_R cs_L args u aux2 daux2"
    by (rule duaux_rel_eval[OF vu unt agg wev dev[unfolded dn]])
  have sb: "set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs" by (rule mbuf2t_take_sub[OF we'])
  have lb1: "list_all (ftable n (set cs_L)) b1" using sb lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable n (set cs_R)) b2" using sb lvs by (auto simp: list_all_iff)
  have "duaux_rel n cs_R cs_L args u aux2 daux2 \<and> u \<le> nt \<and> nt \<le> dnext tw tss \<and>
      list_all (ftable n (set cs_L)) (fst buf1) \<and>
      list_all (ftable n (set cs_R)) (snd buf1) \<and>
      dbuf1 = (map (dtabc n cs_R) (fst buf1), map (dtabc n cs_R) (snd buf1)) \<and>
      sorted nts1 \<and> (\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> dnext tw tss)"
    using ev unt ntdn lb1 lb2 dbf sn1 un sub1 bound bfs by auto
  then have "duntil_rel n cs_R cs_L args (dnext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
    unfolding duntil_rel_def by blast
  then show ?thesis using ev dn dns dbf bfs by simp
qed

subsection \<open>The relation itself\<close>

inductive dsim :: "nat \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> dformula \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  DsPure: "wf_cols n cs \<Longrightarrow> produces n (set cs) \<phi> \<Longrightarrow>
    dsim n cs tw (DPure \<phi> n (wide_mask n cs)) \<phi>"
| DsRel: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MRel rel) \<Longrightarrow>
    table n (set cs) rel \<Longrightarrow>
    dsim n cs tw (DRel (dtabc n cs rel)) (mformula.MRel rel)"
| DsPredC: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPred e tms Copy) \<Longrightarrow>
    tms = map Formula.Var [0..<n] \<Longrightarrow> cs = [0..<n] \<Longrightarrow>
    dsim n cs tw (DPredS e n) (mformula.MPred e tms Copy)"
| DsPredS: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPred e tms Simple) \<Longrightarrow>
    is_simple_pattern tms 0 \<Longrightarrow> cs = smp_cols tms \<Longrightarrow>
    dsim n cs tw (DPredS e (length tms)) (mformula.MPred e tms Simple)"
| DsPredM: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPred e tms Match) \<Longrightarrow>
    dsim n cs tw (DPredM e (length tms) tms cs) (mformula.MPred e tms Match)"
| DsAndRel: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MAndRel \<phi> (t1, p, c, t2)) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow>
    Formula.fv_trm t1 \<subseteq> set cs \<Longrightarrow> Formula.fv_trm t2 \<subseteq> set cs \<Longrightarrow>
    dsim n cs tw (DAndRel \<phi>d (reindex_constraint cs (t1, p, c, t2)))
      (mformula.MAndRel \<phi> (t1, p, c, t2))"
| DsNeg: "produces n {} (mformula.MNeg \<phi>) \<Longrightarrow> dsim n [] tw \<phi>d \<phi> \<Longrightarrow>
    dsim n [] tw (DNeg \<phi>d) (mformula.MNeg \<phi>)"
| DsExists: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MExists \<phi>) \<Longrightarrow>
    dsim (Suc n) ccs tw \<phi>d \<phi> \<Longrightarrow> cs = ex_cols ccs \<Longrightarrow> b = ex_drop0 ccs \<Longrightarrow>
    dsim n cs tw (DExists \<phi>d b) (mformula.MExists \<phi>)"
| DsOr: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MOr \<phi> \<psi> buf) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    dbuf2 n cs cs buf dbuf \<Longrightarrow>
    dsim n cs tw (DOr \<phi>d \<psi>d dbuf) (mformula.MOr \<phi> \<psi> buf)"
| DsAnd: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MAnd (set cs1) \<phi> pos (set cs2) \<psi> buf) \<Longrightarrow>
    dsim n cs1 tw \<phi>d \<phi> \<Longrightarrow> dsim n cs2 tw \<psi>d \<psi> \<Longrightarrow>
    cs = merge_cols cs1 cs2 \<Longrightarrow> pl = mk_djoin cs1 cs2 \<Longrightarrow>
    (\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1) \<Longrightarrow>
    dbuf2 n cs1 cs2 buf dbuf \<Longrightarrow>
    dsim n cs tw (DAnd pl \<phi>d pos \<psi>d dbuf) (mformula.MAnd (set cs1) \<phi> pos (set cs2) \<psi> buf)"
| DsPrev: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPrev I \<phi> first buf nts) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow>
    list_all (ftable n (set cs)) buf \<Longrightarrow> dbuf = map (dtabc n cs) buf \<Longrightarrow>
    dsim n cs tw (DPrev I \<phi>d first dbuf nts) (mformula.MPrev I \<phi> first buf nts)"
| DsNext: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MNext I \<phi> first nts) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow>
    dsim n cs tw (DNext I \<phi>d first nts) (mformula.MNext I \<phi> first nts)"
| DsAnds: "wf_cols n cs \<Longrightarrow>
    produces n (set cs)
      (mformula.MAnds (set c0 # map set css) (map set nss) L buf) \<Longrightarrow>
    (\<forall>i < length L. dsim n ((c0 # css @ nss) ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    length Ld = length L \<Longrightarrow> length (c0 # css @ nss) = length L \<Longrightarrow>
    (\<forall>c \<in> set (c0 # css @ nss). wf_cols n c) \<Longrightarrow>
    (\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)) \<Longrightarrow>
    cs = dands_cols c0 css \<Longrightarrow>
    ps = dands_plans c0 css \<Longrightarrow> ns = dands_plans (dands_cols c0 css) nss \<Longrightarrow>
    dbufn n (c0 # css @ nss) buf dbuf \<Longrightarrow>
    dsim n cs tw (DAnds ps ns Ld dbuf)
      (mformula.MAnds (set c0 # map set css) (map set nss) L buf)"
| DsAgg: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MAgg args \<phi>) \<Longrightarrow>
    dsim (length (aggargs_tys args) + n) (agg_cols (length (aggargs_tys args)) gcols) tw \<phi>d \<phi> \<Longrightarrow>
    wf_cols n gcols \<Longrightarrow> aggargs_n args = n \<Longrightarrow> aggargs_y args = y \<Longrightarrow>
    y < n \<Longrightarrow> y \<notin> set gcols \<Longrightarrow>
    (aggargs_g0 args \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f args) \<subseteq> set (agg_cols (length (aggargs_tys args)) gcols) \<Longrightarrow>
    cs = merge_cols gcols [y] \<Longrightarrow>
    dsim n cs tw (DAgg (aggargs_g0 args) (aggargs_\<omega> args)
        (reindex_trm (agg_cols (length (aggargs_tys args)) gcols) (aggargs_f args))
        (length (aggargs_tys args)) (ins_pos gcols y) \<phi>d) (mformula.MAgg args \<phi>)"
| DsSince: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MSince args \<phi> \<psi> buf aux) \<Longrightarrow>
    dsim n cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols n cs_L \<Longrightarrow> set cs_L \<subseteq> set cs \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs \<Longrightarrow>
    dags = dargs cs cs_L args \<Longrightarrow> pl = emb_plan cs cs_L \<Longrightarrow>
    dsince_rel n cs cs_L args tw aux daux buf dbuf \<Longrightarrow>
    dsim n cs tw (DSince dags pl \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
| DsUntil: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<Longrightarrow>
    dsim n cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols n cs_L \<Longrightarrow> set cs_L \<subseteq> set cs \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs \<Longrightarrow>
    dags = dargs cs cs_L args \<Longrightarrow> pl = emb_plan cs cs_L \<Longrightarrow>
    duntil_rel n cs cs_L args tw t aux daux buf dbuf nts \<Longrightarrow>
    dsim n cs tw (DUntil dags pl \<phi>d \<psi>d dbuf nts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"

text \<open>The two facts the relation is designed to hand out at every node.\<close>

lemma dsim_wf_cols: "dsim n cs tw \<phi>d \<phi> \<Longrightarrow> wf_cols n cs"
  by (induct rule: dsim.induct)
    (auto simp: ex_cols_sorted ex_cols_bound sorted_merge_cols set_merge_cols)

lemma dsim_produces: "dsim n cs tw \<phi>d \<phi> \<Longrightarrow> produces n (set cs) \<phi>"
  by (erule dsim.cases) auto

section \<open>The simulation\<close>

lemma list_all_ftable_append:
  "list_all (ftable n A) xs \<Longrightarrow> list_all (ftable n A) ys \<Longrightarrow> list_all (ftable n A) (xs @ ys)"
  by simp

lemma dbuf2_add:
  assumes b: "dbuf2 n cs1 cs2 buf dbuf"
    and x: "list_all (ftable n (set cs1)) xs" and y: "list_all (ftable n (set cs2)) ys"
  shows "dbuf2 n cs1 cs2 (mbuf2_add xs ys buf)
      (mbuf2_add (map (dtabc n cs1) xs) (map (dtabc n cs2) ys) dbuf)"
  using assms by (cases buf) (auto simp: dbuf2_def)

lemma dbuf2_take:
  assumes b: "dbuf2 n cs1 cs2 buf dbuf"
    and eq: "\<And>a b. ftable n (set cs1) a \<Longrightarrow> ftable n (set cs2) b \<Longrightarrow> g (dtabc n cs1 a) (dtabc n cs2 b) = dtabc n cs (f a b)"
    and t1: "mbuf2_take f buf = (zs, buf')"
  shows "\<exists>dbuf'. mbuf2_take g dbuf = (map (dtabc n cs) zs, dbuf') \<and> dbuf2 n cs1 cs2 buf' dbuf'"
proof -
  obtain b1 b2 where buf: "buf = (b1, b2)" by (cases buf)
  obtain c1 c2 where buf': "buf' = (c1, c2)" by (cases buf')
  have l1: "list_all (ftable n (set cs1)) b1" and l2: "list_all (ftable n (set cs2)) b2"
    and d: "dbuf = (map (dtabc n cs1) b1, map (dtabc n cs2) b2)"
    using b buf by (auto simp: dbuf2_def)
  have "mbuf2_take g (map (dtabc n cs1) b1, map (dtabc n cs2) b2)
      = (map (dtabc n cs) zs, (map (dtabc n cs1) c1, map (dtabc n cs2) c2))"
    using t1 buf buf' l1 l2 by (intro mbuf2_take_map) (auto simp: list_all_iff intro!: eq)
  moreover have "set c1 \<subseteq> set b1" "set c2 \<subseteq> set b2"
    using mbuf2_take_sub[of f b1 b2 zs c1 c2] t1 buf buf' by auto
  ultimately show ?thesis using d l1 l2 buf' by (auto simp: dbuf2_def list_all_iff)
qed

subsection \<open>The multi-way buffer of narrowed tables\<close>

lemma map2_apply_map: "map2 (\<lambda>h a. h a) (map f as) bs = map2 f as bs"
proof (induct as arbitrary: bs)
  case (Cons a as) then show ?case by (cases bs) auto
qed simp

lemma map2_map_map: "map2 map (map f css) xss = map2 (\<lambda>c x. map (f c) x) css xss"
proof (induct css arbitrary: xss)
  case (Cons c css) then show ?case by (cases xss) auto
qed simp

lemma dbufn_add:
  assumes b: "dbufn n css buf dbuf" and l: "length xss = length css"
    and t: "\<forall>i < length css. list_all (ftable n (set (css ! i))) (xss ! i)"
  shows "dbufn n css (mbufn_add xss buf)
      (mbufn_add (map2 (\<lambda>c x. map (dtabc n c) x) css xss) dbuf)"
proof -
  have lb: "length buf = length css"
    and lt: "\<forall>i < length css. list_all (ftable n (set (css ! i))) (buf ! i)"
    and d: "dbuf = map2 map (map (dtabc n) css) buf"
    using b by (auto simp: dbufn_def)
  have "\<forall>i < length css. list_all (ftable n (set (css ! i))) (mbufn_add xss buf ! i)"
    using lt t lb l by (auto simp: list_all_iff)
  moreover have "mbufn_add (map2 (\<lambda>c x. map (dtabc n c) x) css xss) dbuf
      = map2 map (map (dtabc n) css) (mbufn_add xss buf)"
  proof -
    have "map2 map (map (dtabc n) css) (mbufn_add xss buf)
        = mbufn_add (map2 map (map (dtabc n) css) xss) (map2 map (map (dtabc n) css) buf)"
      by (rule mbufn_add_map2) (use lb l in simp_all)
    then show ?thesis unfolding d by (simp add: map2_map_map)
  qed
  ultimately show ?thesis using lb l by (simp add: dbufn_def)
qed

lemma dbufn_take:
  fixes f g :: "event_data table list \<Rightarrow> event_data table"
    and buf buf' dbuf :: "event_data mbufn" and zs :: "event_data table list"
  assumes b: "dbufn n css buf dbuf"
    and eq: "\<And>as :: event_data table list. length as = length css \<Longrightarrow>
        (\<forall>i < length css. ftable n (set (css ! i)) (as ! i)) \<Longrightarrow>
        dtabc n cs (f as) = g (map2 (dtabc n) css as)"
    and t: "mbufn_take (\<lambda>as zs. zs @ [f as]) [] buf = (zs, buf')"
  shows "\<exists>dbuf'. mbufn_take (\<lambda>as zs. zs @ [g as]) [] dbuf = (map (dtabc n cs) zs, dbuf')
      \<and> dbufn n css buf' dbuf'"
proof -
  have lb: "length buf = length css"
    and lt: "\<forall>i < length css. list_all (ftable n (set (css ! i))) (buf ! i)"
    and d: "dbuf = map2 map (map (dtabc n) css) buf"
    using b by (auto simp: dbufn_def)
  define hs :: "(event_data table \<Rightarrow> event_data table) list"
    where "hs = map (dtabc n) css"
  define Ss :: "event_data table set list"
    where "Ss = map (\<lambda>c. {T. ftable n (set c) T}) css"
  obtain w2 buf2 where e2: "mbufn_take (\<lambda>as zs. zs @ [g as])
      ([] :: event_data table list) dbuf = (w2, buf2)"
    by (cases "mbufn_take (\<lambda>as zs. zs @ [g as]) ([] :: event_data table list) dbuf") auto
  have sub: "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i"
    using lt lb by (auto simp: Ss_def list_all_iff)
  have step: "\<And>as :: event_data table list. \<And>u u' :: event_data table list.
      length as = length hs \<Longrightarrow>
      (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> u' = map (dtabc n cs) u \<Longrightarrow>
      u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (dtabc n cs) (u @ [f as])"
  proof -
    fix as u u' :: "event_data table list"
    assume la: "length as = length hs"
      and ma: "\<forall>i < length as. as ! i \<in> Ss ! i" and mu: "u' = map (dtabc n cs) u"
    have la': "length as = length css" using la by (simp add: hs_def)
    have ma': "\<forall>i < length css. ftable n (set (css ! i)) (as ! i)"
      using ma la' by (auto simp: Ss_def)
    show "u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (dtabc n cs) (u @ [f as])"
      using mu eq[OF la' ma'] by (simp add: hs_def map2_apply_map)
  qed
  have r: "(w2 = map (dtabc n cs) zs) \<and> buf2 = map2 map hs buf'"
  proof (rule mbufn_take_rel[where R = "\<lambda>u u'. u' = map (dtabc n cs) u" and Ss = Ss
        and hs = hs and f = "\<lambda>as zs. zs @ [f as]" and g = "\<lambda>as zs. zs @ [g as]"
        and z = "[]" and z' = "[]" and buf = buf and buf' = buf' and w = zs])
    show "length hs = length buf" using lb by (simp add: hs_def)
    show "length Ss = length buf" using lb by (simp add: Ss_def)
    show "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i" by (rule sub)
    show "\<And>as u u'. length as = length hs \<Longrightarrow>
        (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> u' = map (dtabc n cs) u \<Longrightarrow>
        u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (dtabc n cs) (u @ [f as])"
      by (rule step)
    show "([] :: event_data table list) = map (dtabc n cs) []" by simp
    show "mbufn_take (\<lambda>as zs. zs @ [f as]) [] buf = (zs, buf')" by (rule t)
    show "mbufn_take (\<lambda>as zs. zs @ [g as]) [] (map2 map hs buf) = (w2, buf2)"
      using e2 d by (simp add: hs_def)
  qed
  have ls: "length buf' = length buf"
    and ss: "\<forall>i < length buf. set (buf' ! i) \<subseteq> set (buf ! i)"
    using mbufn_take_sub[OF t] by auto
  have "dbufn n css buf' buf2"
    using lt lb ls ss r by (fastforce simp: dbufn_def hs_def list_all_iff)
  then show ?thesis using e2 r by auto
qed

subsection \<open>Stepping a list of operands\<close>

lemma dsims_tables:
  "(\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
   length Ld = length L \<Longrightarrow> length css = length L \<Longrightarrow> wf_db db \<Longrightarrow> i < length L \<Longrightarrow>
     list_all (ftable n (set (css ! i))) (fst (meval j n ts db (L ! i)))"
proof (induct L arbitrary: css Ld i)
  case (Cons \<psi> L')
  note la = Cons(2) and l1 = Cons(3) and l2 = Cons(4) and w = Cons(5) and i = Cons(6)
    and IH = Cons(1)
  obtain c css' where c: "css = c # css'" using l2 by (cases css) auto
  obtain \<psi>d Ld' where d: "Ld = \<psi>d # Ld'" using l1 by (cases Ld) auto
  show ?case
  proof (cases i)
    case 0
    have h: "dsim n c tw \<psi>d \<psi>" using la unfolding c d by (auto dest: spec[of _ 0])
    obtain as \<psi>2 where e: "meval j n ts db \<psi> = (as, \<psi>2)" by (cases "meval j n ts db \<psi>")
    have "list_all (ftable n (set c)) as" by (rule produces_tables[OF dsim_produces[OF h] w e])
    then show ?thesis unfolding c 0 using e by simp
  next
    case (Suc i')
    have ta: "\<forall>k < length L'. dsim n (css' ! k) tw (Ld' ! k) (L' ! k)"
      using la unfolding c d by auto
    show ?thesis using IH[OF ta _ _ w] l1 l2 i unfolding c d Suc by simp
  qed
qed simp

lemma deval_list_rel:
  "length Ld = length L \<Longrightarrow> length css = length L \<Longrightarrow>
   (\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i) \<and>
       (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
          (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (css ! i)) as, \<psi>d')
             \<and> dsim n (css ! i) tw' \<psi>d' \<psi>'))) \<Longrightarrow>
   length (deval_list j ts db Ld) = length L \<and>
   map fst (deval_list j ts db Ld)
       = map2 (\<lambda>c x. map (dtabc n c) x) css (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
   (\<forall>i < length L. dsim n (css ! i) tw' (map snd (deval_list j ts db Ld) ! i)
       (snd (meval j n ts db (L ! i))))"
proof (induct L arbitrary: css Ld)
  case (Cons \<psi> L')
  note l1 = Cons(2) and l2 = Cons(3) and la = Cons(4) and IH = Cons(1)
  obtain c css' where c: "css = c # css'" using l2 by (cases css) auto
  obtain \<psi>d Ld' where d: "Ld = \<psi>d # Ld'" using l1 by (cases Ld) auto
  have h: "dsim n c tw \<psi>d \<psi> \<and> (\<forall>as \<psi>'. meval j n ts db \<psi> = (as, \<psi>') \<longrightarrow>
      (\<exists>\<psi>d'. deval j ts db \<psi>d = (map (dtabc n c) as, \<psi>d') \<and> dsim n c tw' \<psi>d' \<psi>'))"
    using la unfolding c d by (auto dest: spec[of _ 0])
  have ta: "\<forall>k < length L'. dsim n (css' ! k) tw (Ld' ! k) (L' ! k) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L' ! k) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld' ! k) = (map (dtabc n (css' ! k)) as, \<psi>d')
            \<and> dsim n (css' ! k) tw' \<psi>d' \<psi>'))"
    using la unfolding c d by auto
  obtain as \<psi>2 where e: "meval j n ts db \<psi> = (as, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain \<psi>d2 where dv: "deval j ts db \<psi>d = (map (dtabc n c) as, \<psi>d2)"
    and sm: "dsim n c tw' \<psi>d2 \<psi>2" using h e by blast
  have rest: "length (deval_list j ts db Ld') = length L' \<and>
      map fst (deval_list j ts db Ld')
        = map2 (\<lambda>c x. map (dtabc n c) x) css'
            (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L') \<and>
      (\<forall>k < length L'. dsim n (css' ! k) tw' (map snd (deval_list j ts db Ld') ! k)
          (snd (meval j n ts db (L' ! k))))"
  proof (rule IH)
    show "length Ld' = length L'" using l1 unfolding d by simp
    show "length css' = length L'" using l2 unfolding c by simp
    show "\<forall>k < length L'. dsim n (css' ! k) tw (Ld' ! k) (L' ! k) \<and>
        (\<forall>as \<psi>'. meval j n ts db (L' ! k) = (as, \<psi>') \<longrightarrow>
           (\<exists>\<psi>d'. deval j ts db (Ld' ! k) = (map (dtabc n (css' ! k)) as, \<psi>d')
              \<and> dsim n (css' ! k) tw' \<psi>d' \<psi>'))" by (rule ta)
  qed
  show ?case unfolding c d using rest dv sm e by (auto simp: nth_Cons split: nat.splits)
qed simp

subsection \<open>One firing of the Since structure\<close>

text \<open>
  One firing of @{const meval_since} at the dense frame yields the narrowing of what one firing at
  the wide frame yields, and the relation is preserved.  The recursion is driven by the buffer
  alone, so the two sides step in lockstep; the induction is over the kernel's own recursion.
\<close>

lemma eval_since_rel:
  fixes cs_R cs_L :: cols and args :: args
  assumes sR: "sorted_wrt (<) cs_R" and bR: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R" and agg: "args_agg args = None"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
  shows "meval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow>
    meval_since (dargs cs_R cs_L args) (map (dtabc n cs_R) rs) dbuf daux
      = (dzs, dbuf', daux') \<Longrightarrow>
    dsince_rel n cs_R cs_L args tw aux daux buf dbuf \<Longrightarrow>
    dzs = map (dtabc n cs_R) zs \<and> dsince_rel n cs_R cs_L args tw aux' daux' buf' dbuf'"
proof (induction rs buf aux arbitrary: daux dbuf zs buf' aux' dzs dbuf' daux'
    taking: args rule: default_maux.eval_since.induct)
  case (1 rs x xs t tss skew aux)
  note E = 1(1) and D = 1(2) and R = 1(3)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsaux n cs_R cs_L args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable n (set cs_L)) (x # xs)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_R) (x # xs), map (dtabc n cs_R) [], t # tss, skew)"
    using R by (rule dsince_relE)
  have tx: "table n (set cs_L) x" using lx by simp
  have ctu: "cur \<le> t" using ct by simp
  show ?case
  proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev rs, (x # xs, [], t # tss, skew), aux)" using True by simp
    have DW: "meval_since (dargs cs_R cs_L args) (map (dtabc n cs_R) rs) dbuf daux
        = (rev (map (dtabc n cs_R) rs), dbuf, daux)" unfolding dbuf using True by simp
    have EE: "(rev rs, (x # xs, [], t # tss, skew), aux) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev (map (dtabc n cs_R) rs), dbuf, daux) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    show ?thesis using EE DD R by (auto simp: rev_map)
  next
    case False
    let ?wa = "gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)"
    let ?da = "gc_join_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R x)
        (add_new_ts_mmasaux (dargs cs_R cs_L args) t daux)"
    let ?al = "map (\<lambda>(u, rel). (u, join rel (args_pos args) x))
        (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
    have vw': "valid_mmasaux args t ?wa ?al"
      by (rule default_mmasaux.valid_join_msaux
          [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
    have vd': "dsaux n cs_R cs_L args t ?da ?al"
      by (rule dsaux_join[OF dsaux_add_new_ts[OF vd ctu] sR bR sub tx])
    have res: "result_mmasaux (dargs cs_R cs_L args) ?da
        = dtabc n cs_R (result_mmasaux args ?wa)"
      using dsaux_result[OF vd'] default_mmasaux.valid_result_msaux[OF vw'] agg by simp
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa)"
      using False by (simp add: Let_def)
    have DW: "meval_since (dargs cs_R cs_L args) (map (dtabc n cs_R) rs) dbuf daux
        = (rev (result_mmasaux (dargs cs_R cs_L args) ?da # map (dtabc n cs_R) rs),
           (map (dtabc n cs_R) xs, map (dtabc n cs_R) [], tss, True), ?da)"
      unfolding dbuf using False by (simp add: Let_def)
    have EE: "(rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev (result_mmasaux (dargs cs_R cs_L args) ?da # map (dtabc n cs_R) rs),
        (map (dtabc n cs_R) xs, map (dtabc n cs_R) [], tss, True), ?da) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    have R': "dsince_rel n cs_R cs_L args tw ?wa ?da (xs, [], tss, True)
        (map (dtabc n cs_R) xs, map (dtabc n cs_R) [], tss, True)"
      by (rule dsince_relI[OF vw' vd']) (use lx st ct in auto)
    show ?thesis using EE DD res R' by (auto simp: rev_map)
  qed
next
  case (2 rs xs y ys tss aux)
  note IH = 2(1) and E = 2(2) and D = 2(3) and R = 2(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsaux n cs_R cs_L args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable n (set cs_L)) xs"
    and ly: "list_all (ftable n (set cs_R)) (y # ys)"
    and st: "sorted tss" and ct: "\<forall>u \<in> set tss. cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_R) xs, map (dtabc n cs_R) (y # ys), tss, True)"
    using R by (rule dsince_relE)
  have ty: "table n (set cs_R) y" using ly by simp
  let ?al = "case auxlist of [] \<Rightarrow> [(cur, y)]
      | ((u, w) # r) \<Rightarrow> if u = cur then (u, w \<union> y) # r else (cur, y) # auxlist"
  have vw': "valid_mmasaux args cur (add_new_table_mmasaux args y aux) ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vw]) (use ty an aR in simp)
  have vd': "dsaux n cs_R cs_L args cur
      (add_new_table_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R y) daux) ?al"
    by (rule dsaux_add_new_table[OF vd sR bR ty])
  have E': "meval_since args rs (xs, ys, tss, False) (add_new_table_mmasaux args y aux)
      = (zs, buf', aux')" using E by simp
  have D': "meval_since (dargs cs_R cs_L args) (map (dtabc n cs_R) rs)
      (map (dtabc n cs_R) xs, map (dtabc n cs_R) ys, tss, False)
      (add_new_table_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R y) daux)
      = (dzs, dbuf', daux')" using D unfolding dbuf by simp
  have R': "dsince_rel n cs_R cs_L args tw (add_new_table_mmasaux args y aux)
      (add_new_table_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R y) daux)
      (xs, ys, tss, False) (map (dtabc n cs_R) xs, map (dtabc n cs_R) ys, tss, False)"
    by (rule dsince_relI[OF vw' vd' ctw]) (use lx ly st ct in auto)
  show ?case by (rule IH[OF E' D' R'])
next
  case (3 rs x xs y ys t tss aux)
  note IH = 3(1) and E = 3(2) and D = 3(3) and R = 3(4)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsaux n cs_R cs_L args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable n (set cs_L)) (x # xs)"
    and ly: "list_all (ftable n (set cs_R)) (y # ys)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_R) (x # xs), map (dtabc n cs_R) (y # ys), t # tss, False)"
    using R by (rule dsince_relE)
  have tx: "table n (set cs_L) x" using lx by simp
  have ty: "table n (set cs_R) y" using ly by simp
  have ctu: "cur \<le> t" using ct by simp
  let ?jl = "map (\<lambda>(u, rel). (u, join rel (args_pos args) x))
      (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
  let ?al = "case ?jl of [] \<Rightarrow> [(t, y)]
      | ((u, w) # r) \<Rightarrow> if u = t then (u, w \<union> y) # r else (t, y) # ?jl"
  let ?wa = "add_new_table_mmasaux args y
      (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux))"
  let ?da = "add_new_table_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R y)
      (gc_join_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R x)
        (add_new_ts_mmasaux (dargs cs_R cs_L args) t daux))"
  have vwj: "valid_mmasaux args t (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)) ?jl"
    by (rule default_mmasaux.valid_join_msaux
        [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
  have vdj: "dsaux n cs_R cs_L args t
      (gc_join_mmasaux (dargs cs_R cs_L args) (dtabc n cs_R x)
        (add_new_ts_mmasaux (dargs cs_R cs_L args) t daux)) ?jl"
    by (rule dsaux_join[OF dsaux_add_new_ts[OF vd ctu] sR bR sub tx])
  have vw': "valid_mmasaux args t ?wa ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vwj]) (use ty an aR in simp)
  have vd': "dsaux n cs_R cs_L args t ?da ?al"
    by (rule dsaux_add_new_table[OF vdj sR bR ty])
  have res: "result_mmasaux (dargs cs_R cs_L args) ?da = dtabc n cs_R (result_mmasaux args ?wa)"
    using dsaux_result[OF vd'] default_mmasaux.valid_result_msaux[OF vw'] agg by simp
  have E': "meval_since args (result_mmasaux args ?wa # rs) (xs, ys, tss, False) ?wa
      = (zs, buf', aux')" using E by (simp add: Let_def)
  have D': "meval_since (dargs cs_R cs_L args)
      (map (dtabc n cs_R) (result_mmasaux args ?wa # rs))
      (map (dtabc n cs_R) xs, map (dtabc n cs_R) ys, tss, False) ?da = (dzs, dbuf', daux')"
    using D res unfolding dbuf by (simp add: Let_def)
  have R': "dsince_rel n cs_R cs_L args tw ?wa ?da (xs, ys, tss, False)
      (map (dtabc n cs_R) xs, map (dtabc n cs_R) ys, tss, False)"
    by (rule dsince_relI[OF vw' vd']) (use lx ly st ct in auto)
  show ?case by (rule IH[OF refl E' D' R'])
qed ((frule dsince_relD_buf, simp add: rev_map)+)

text \<open>
  The simulation itself.  Every case is one theorem of @{theory MFODL_Monitor_Imp.Dense}
  applied pointwise to the operand's output list, with @{const produces} supplying the
  operand well-formedness and @{thm produces_next} re-establishing it for the successor.
\<close>

theorem dsim_deval:
  "dsim n cs tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc n cs) xs, \<phi>d')
     \<and> dsim n cs (dnext tw ts) \<phi>d' \<phi>'"
proof (induct arbitrary: j ts db xs \<phi>' rule: dsim.induct)
  case (DsPure n cs \<phi> tw)
  note wf = DsPure.hyps(1) and p = DsPure.hyps(2)
    and w = DsPure.prems(1) and sts = DsPure.prems(2)
    and mts = DsPure.prems(3) and m = DsPure.prems(4)
  have t: "list_all (ftable n (set cs)) xs" by (rule produces_tables[OF p w m])
  have "map (dnarrow (wide_mask n cs)) xs = map (dtabc n cs) xs"
    using t by (intro map_cong refl dnarrow_dtabc) (auto simp: list_all_iff)
  then show ?case using m wf produces_next[OF p w m] by (auto intro!: dsim.DsPure)
next
  case (DsRel n cs rel tw)
  note wf = DsRel.hyps(1) and p = DsRel.hyps(2) and t = DsRel.hyps(3)
    and w = DsRel.prems(1) and sts = DsRel.prems(2)
    and mts = DsRel.prems(3) and m = DsRel.prems(4)
  have x: "xs = replicate (length ts) rel" and f: "\<phi>' = mformula.MRel rel" using m by simp_all
  show ?case using wf p t by (simp add: x f dsim.DsRel)
next
  case (DsPredC n cs e tms tw)
  note wf = DsPredC.hyps(1) and pr = DsPredC.hyps(2) and tm = DsPredC.hyps(3)
    and cse = DsPredC.hyps(4) and w = DsPredC.prems(1) and sts = DsPredC.prems(2)
    and mts = DsPredC.prems(3) and m = DsPredC.prems(4)
  have ar: "length tms = n" using tm by simp
  have f: "\<phi>' = mformula.MPred e tms Copy" using m by simp
  show ?case
  proof (cases "Mapping.lookup db (e, n)")
    case None
    have x: "xs = replicate (length ts) empty_table"
      using m ar None by (simp add: empty_table_def)
    show ?thesis using wf pr tm cse produces_next[OF pr w m] None x f
      by (auto intro!: dsim.DsPredC)
  next
    case (Some ys)
    have x: "xs = ys" using m ar Some by simp
    have dt: "\<And>T. T \<in> set ys \<Longrightarrow> dtabc n cs T = T"
    proof -
      fix T assume "T \<in> set ys"
      then have "table n {0..<n} T" by (rule wf_dbD[OF w Some])
      then show "dtabc n cs T = T" unfolding cse by (rule dtabc_upt)
    qed
    have mp: "map (dtabc n cs) ys = ys" using dt by (induct ys) auto
    show ?thesis using wf pr tm cse produces_next[OF pr w m] Some x f mp
      by (auto intro!: dsim.DsPredC)
  qed
next
  case (DsPredS n cs e tms tw)
  note wf = DsPredS.hyps(1) and pr = DsPredS.hyps(2) and sp = DsPredS.hyps(3)
    and cse = DsPredS.hyps(4) and w = DsPredS.prems(1) and sts = DsPredS.prems(2)
    and mts = DsPredS.prems(3) and m = DsPredS.prems(4)
  have f: "\<phi>' = mformula.MPred e tms Simple" using m by simp
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) empty_table"
      using m None by (simp add: empty_table_def)
    show ?thesis using wf pr sp cse produces_next[OF pr w m] None x f
      by (auto intro!: dsim.DsPredS)
  next
    case (Some ys)
    have x: "xs = map (\<lambda>T. simple_match n 0 tms ` T) ys" using m Some by simp
    have b: "\<forall>y \<in> set (smp_cols tms). y < n" using wf cse by simp
    have dt: "\<And>T. T \<in> set ys \<Longrightarrow> dtabc n cs (simple_match n 0 tms ` T) = T"
    proof -
      fix T assume "T \<in> set ys"
      then have "table (length tms) {0..<length tms} T" by (rule wf_dbD[OF w Some])
      then have l: "\<forall>x \<in> T. length x = length tms"
        by (simp add: table_def wf_tuple_def)
      show "dtabc n cs (simple_match n 0 tms ` T) = T"
        unfolding cse by (rule dtabc_simple_match[OF sp b l])
    qed
    have mp: "map (dtabc n cs) (map (\<lambda>T. simple_match n 0 tms ` T) ys) = ys"
      using dt by (induct ys) auto
    show ?thesis using wf pr sp cse produces_next[OF pr w m] Some x f mp
      by (auto intro!: dsim.DsPredS)
  qed
next
  case (DsPredM n cs e tms tw)
  note wf = DsPredM.hyps(1) and pr = DsPredM.hyps(2)
    and w = DsPredM.prems(1) and sts = DsPredM.prems(2)
    and mts = DsPredM.prems(3) and m = DsPredM.prems(4)
  have f: "\<phi>' = mformula.MPred e tms Match" using m by simp
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) empty_table"
      using m None by (simp add: empty_table_def)
    show ?thesis using wf pr produces_next[OF pr w m] None x f
      by (auto intro!: dsim.DsPredM)
  next
    case (Some ys)
    have x: "xs = map (\<lambda>T. (\<lambda>g. Table.tabulate g 0 n) ` Option.these (match tms ` T)) ys"
      using m Some by simp
    have dt: "\<And>T. dmatch_table tms cs T
        = dtabc n cs ((\<lambda>g. Table.tabulate g 0 n) ` Option.these (match tms ` T))"
      using wf by (intro dmatch_table_dtabc) simp_all
    have mp: "map (dmatch_table tms cs) ys
        = map (dtabc n cs) (map (\<lambda>T. (\<lambda>g. Table.tabulate g 0 n) ` Option.these (match tms ` T)) ys)"
      using dt by (induct ys) auto
    show ?thesis using wf pr produces_next[OF pr w m] Some x f mp
      by (auto intro!: dsim.DsPredM)
  qed
next
  case (DsAndRel n cs \<phi> t1 p c t2 tw \<phi>d)
  note wf = DsAndRel.hyps(1) and pr = DsAndRel.hyps(2) and sim = DsAndRel.hyps(3)
    and IH = DsAndRel.hyps(4) and fv1 = DsAndRel.hyps(5) and fv2 = DsAndRel.hyps(6)
    and w = DsAndRel.prems(1) and sts = DsAndRel.prems(2)
    and mts = DsAndRel.prems(3) and m = DsAndRel.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (Set.filter (eval_constraint (t1, p, c, t2))) ys"
    and f: "\<phi>' = mformula.MAndRel \<psi>' (t1, p, c, t2)" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e] by blast
  have t: "list_all (ftable n (set cs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w e])
  have pc: "\<And>r. r \<in> set ys \<Longrightarrow>
      dtabc n cs (Set.filter (eval_constraint (t1, p, c, t2)) r)
        = Set.filter (eval_constraint (reindex_constraint cs (t1, p, c, t2))) (dtabc n cs r)"
    using t wf fv1 fv2 by (intro eval_constraint_reindex) (auto simp: list_all_iff)
  have "map (Set.filter (eval_constraint (reindex_constraint cs (t1, p, c, t2))))
        (map (dtabc n cs) ys) = map (dtabc n cs) xs"
    unfolding x map_map
  proof (intro map_cong refl)
    fix r assume r: "r \<in> set ys"
    show "(Set.filter (eval_constraint (reindex_constraint cs (t1, p, c, t2))) \<circ> dtabc n cs) r
        = (dtabc n cs \<circ> Set.filter (eval_constraint (t1, p, c, t2))) r"
      using pc[OF r] by simp
  qed
  then show ?case using d sim' produces_next[OF pr w m] wf fv1 fv2 f
    by (auto intro!: dsim.DsAndRel)
next
  case (DsNeg n \<phi> tw \<phi>d)
  note pr = DsNeg.hyps(1) and sim = DsNeg.hyps(2) and IH = DsNeg.hyps(3)
    and w = DsNeg.prems(1) and sts = DsNeg.prems(2)
    and mts = DsNeg.prems(3) and m = DsNeg.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. if r = empty_table then unit_table n else empty_table) ys"
    and f: "\<phi>' = mformula.MNeg \<psi>'" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n []) ys, \<psi>d')"
    and sim': "dsim n [] (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e] by blast
  have "map (\<lambda>r. if r = empty_table then unit_table 0 else empty_table) (map (dtabc n []) ys)
      = map (dtabc n []) xs"
    unfolding x by (simp add: dtabc_neg)
  then show ?case using d sim' produces_next[OF pr w m] f by (auto intro!: dsim.DsNeg)
next
  case (DsExists n cs \<phi> ccs tw \<phi>d b)
  note wf = DsExists.hyps(1) and pr = DsExists.hyps(2) and sim = DsExists.hyps(3)
    and IH = DsExists.hyps(4) and cse = DsExists.hyps(5) and be = DsExists.hyps(6)
    and w = DsExists.prems(1) and sts = DsExists.prems(2)
    and mts = DsExists.prems(3) and m = DsExists.prems(4)
  obtain ys \<psi>' where e: "meval j (Suc n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (Suc n) ts db \<phi>")
  have x: "xs = map (\<lambda>r. tl ` r) ys" and f: "\<phi>' = mformula.MExists \<psi>'" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (Suc n) ccs) ys, \<psi>d')"
    and sim': "dsim (Suc n) ccs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e] by blast
  have wfc: "wf_cols (Suc n) ccs" by (rule dsim_wf_cols[OF sim])
  have t: "list_all (ftable (Suc n) (set ccs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w e])
  have pe: "\<And>r. r \<in> set ys \<Longrightarrow>
      (if ex_drop0 ccs then tl ` dtabc (Suc n) ccs r else dtabc (Suc n) ccs r)
        = dtabc n (ex_cols ccs) (tl ` r)"
    using t wfc by (intro dtabc_exists) (auto simp: list_all_iff)
  have "(if ex_drop0 ccs then map (\<lambda>r. tl ` r) (map (dtabc (Suc n) ccs) ys)
         else map (dtabc (Suc n) ccs) ys) = map (dtabc n cs) xs"
    unfolding x cse
  proof -
    have "(if ex_drop0 ccs then map (\<lambda>r. tl ` r) (map (dtabc (Suc n) ccs) ys)
           else map (dtabc (Suc n) ccs) ys)
        = map (\<lambda>r. if ex_drop0 ccs then tl ` dtabc (Suc n) ccs r else dtabc (Suc n) ccs r) ys"
      by simp
    also have "\<dots> = map (dtabc n (ex_cols ccs)) (map (\<lambda>r. tl ` r) ys)"
      unfolding map_map
    proof (intro map_cong refl)
      fix r assume r: "r \<in> set ys"
      show "(if ex_drop0 ccs then tl ` dtabc (Suc n) ccs r else dtabc (Suc n) ccs r)
          = (dtabc n (ex_cols ccs) \<circ> (\<lambda>r. tl ` r)) r"
        using pe[OF r] by simp
    qed
    finally show "(if ex_drop0 ccs then map (\<lambda>r. tl ` r) (map (dtabc (Suc n) ccs) ys)
         else map (dtabc (Suc n) ccs) ys) = map (dtabc n (ex_cols ccs)) (map (\<lambda>r. tl ` r) ys)" .
  qed
  then show ?case using d sim' produces_next[OF pr w m] wf cse be f
    by (auto intro!: dsim.DsExists)
next
  case (DsOr n cs \<phi> \<psi> buf tw \<phi>d \<psi>d dbuf)
  note wf = DsOr.hyps(1) and pr = DsOr.hyps(2) and sim1 = DsOr.hyps(3) and IH1 = DsOr.hyps(4)
    and sim2 = DsOr.hyps(5) and IH2 = DsOr.hyps(6) and bf = DsOr.hyps(7)
    and w = DsOr.prems(1) and sts = DsOr.prems(2)
    and mts = DsOr.prems(3) and m = DsOr.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MOr \<phi>2 \<psi>2 buf2" using m e1 e2 e3 by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs) as, \<phi>d2)"
    and s1: "dsim n cs (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2] by blast
  have ta: "list_all (ftable n (set cs)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w e2])
  have badd: "dbuf2 n cs cs (mbuf2_add as bs buf)
      (mbuf2_add (map (dtabc n cs) as) (map (dtabc n cs) bs) dbuf)"
    by (rule dbuf2_add[OF bf ta tb])
  have step: "\<And>a b. ftable n (set cs) a \<Longrightarrow> ftable n (set cs) b \<Longrightarrow>
      dtabc n cs a \<union> dtabc n cs b = dtabc n cs (a \<union> b)"
    by (simp add: dtabc_Un_img)
  obtain dbuf2' where dt: "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2)
        (mbuf2_add (map (dtabc n cs) as) (map (dtabc n cs) bs) dbuf)
      = (map (dtabc n cs) zs, dbuf2')"
    and bf': "dbuf2 n cs cs buf2 dbuf2'"
    using dbuf2_take[OF badd step e3] by blast
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr w m] wf x f
    by (auto intro!: dsim.DsOr)
next
  case (DsAnd n cs cs1 \<phi> pos cs2 \<psi> buf tw \<phi>d \<psi>d pl dbuf)
  note wf = DsAnd.hyps(1) and pr = DsAnd.hyps(2) and sim1 = DsAnd.hyps(3)
    and IH1 = DsAnd.hyps(4) and sim2 = DsAnd.hyps(5) and IH2 = DsAnd.hyps(6)
    and cse = DsAnd.hyps(7) and ple = DsAnd.hyps(8) and neg = DsAnd.hyps(9)
    and bf = DsAnd.hyps(10)
    and w = DsAnd.prems(1) and sts = DsAnd.prems(2)
    and mts = DsAnd.prems(3) and m = DsAnd.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. bin_join n (set cs1) r1 pos (set cs2) r2)
        (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. bin_join n (set cs1) r1 pos (set cs2) r2)
        (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MAnd (set cs1) \<phi>2 pos (set cs2) \<psi>2 buf2"
    using m e1 e2 e3 by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs1) as, \<phi>d2)"
    and s1: "dsim n cs1 (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs2) bs, \<psi>d2)"
    and s2: "dsim n cs2 (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2] by blast
  have so1: "sorted_wrt (<) cs1" and b1: "\<forall>c \<in> set cs1. c < n"
    using dsim_wf_cols[OF sim1] by (blast dest: conjunct1 conjunct2)+
  have so2: "sorted_wrt (<) cs2" and b2: "\<forall>c \<in> set cs2. c < n"
    using dsim_wf_cols[OF sim2] by (blast dest: conjunct1 conjunct2)+
  have ta: "list_all (ftable n (set cs1)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w e1])
  have tb: "list_all (ftable n (set cs2)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w e2])
  have badd: "dbuf2 n cs1 cs2 (mbuf2_add as bs buf)
      (mbuf2_add (map (dtabc n cs1) as) (map (dtabc n cs2) bs) dbuf)"
    by (rule dbuf2_add[OF bf ta tb])
  have step: "\<And>a b. ftable n (set cs1) a \<Longrightarrow> ftable n (set cs2) b \<Longrightarrow>
      dbin_join pl (dtabc n cs1 a) pos (dtabc n cs2 b)
        = dtabc n cs (bin_join n (set cs1) a pos (set cs2) b)"
    unfolding ple cse
    by (rule dbin_join_bin_join[OF so1 so2 b1 b2 _ _ neg]) (elim conjE, assumption)+
  obtain dbuf2' where dt: "mbuf2_take (\<lambda>r1 r2. dbin_join pl r1 pos r2)
        (mbuf2_add (map (dtabc n cs1) as) (map (dtabc n cs2) bs) dbuf)
      = (map (dtabc n cs) zs, dbuf2')"
    and bf': "dbuf2 n cs1 cs2 buf2 dbuf2'"
    using dbuf2_take[OF badd step e3] by blast
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr w m] wf cse ple neg x f
    by (auto intro!: dsim.DsAnd)
next
  case (DsPrev n cs I \<phi> first buf nts tw \<phi>d dbuf)
  note wf = DsPrev.hyps(1) and pr = DsPrev.hyps(2) and sim = DsPrev.hyps(3)
    and IH = DsPrev.hyps(4) and lb = DsPrev.hyps(5) and be = DsPrev.hyps(6)
    and w = DsPrev.prems(1) and sts = DsPrev.prems(2)
    and mts = DsPrev.prems(3) and m = DsPrev.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e] by blast
  have t: "list_all (ftable n (set cs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w e])
  have tb: "list_all (ftable n (set cs)) (buf @ ys)" using lb t by simp
  show ?case
  proof (cases "first \<and> ts = []")
    case True
    have x: "xs = []" and f: "\<phi>' = mformula.MPrev I \<psi>' True (buf @ ys) (nts @ ts)"
      using m e True by simp_all
    show ?thesis using d be True x f sim' produces_next[OF pr w m] wf tb
      by (auto intro!: dsim.DsPrev)
  next
    case False
    obtain zs buf' nts' where g: "mprev_next I (buf @ ys) (nts @ ts) = (zs, buf', nts')"
      by (cases "mprev_next I (buf @ ys) (nts @ ts)") auto
    have x: "xs = (if first then empty_table # zs else zs)"
      and f: "\<phi>' = mformula.MPrev I \<psi>' False buf' nts'"
      using m e g False by (simp_all add: Let_def)
    have g': "mprev_next I (map (dtabc n cs) (buf @ ys)) (nts @ ts)
        = (map (dtabc n cs) zs, map (dtabc n cs) buf', nts')"
      by (rule mprev_next_map[OF _ g]) simp
    have tb': "list_all (ftable n (set cs)) buf'"
      using mprev_next_sub[OF g] tb by (auto simp: list_all_iff)
    show ?thesis using d be False x f sim' produces_next[OF pr w m] wf tb' g'
      by (auto intro!: dsim.DsPrev)
  qed
next
  case (DsNext n cs I \<phi> first nts tw \<phi>d)
  note wf = DsNext.hyps(1) and pr = DsNext.hyps(2) and sim = DsNext.hyps(3)
    and IH = DsNext.hyps(4) and w = DsNext.prems(1) and sts = DsNext.prems(2)
    and mts = DsNext.prems(3) and m = DsNext.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e] by blast
  obtain ys0 first0 where c:
      "(case (ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a) = (ys0, first0)"
    by (cases "(case (ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a)") auto
  have c': "(case (map (dtabc n cs) ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a)
      = (map (dtabc n cs) ys0, first0)"
    using c by (cases ys; cases first) auto
  obtain zs buf' nts' where g: "mprev_next I ys0 (nts @ ts) = (zs, buf', nts')"
    by (cases "mprev_next I ys0 (nts @ ts)") auto
  have x: "xs = zs" and f: "\<phi>' = mformula.MNext I \<psi>' first0 nts'"
    using m e c g by (simp_all add: Let_def split: prod.splits)
  have g': "mprev_next I (map (dtabc n cs) ys0) (nts @ ts)
      = (map (dtabc n cs) zs, map (dtabc n cs) buf', nts')"
    by (rule mprev_next_map[OF _ g]) simp
  show ?case using d c' g' x f sim' produces_next[OF pr w m] wf
    by (auto intro!: dsim.DsNext)
next
  case (DsAnds n cs c0 css nss L buf tw Ld ps ns dbuf)
  note wf = DsAnds.hyps(1) and pr = DsAnds.hyps(2) and la = DsAnds.hyps(3)
    and l1 = DsAnds.hyps(4) and l2 = DsAnds.hyps(5) and wc = DsAnds.hyps(6)
    and sb = DsAnds.hyps(7) and cse = DsAnds.hyps(8) and pse = DsAnds.hyps(9)
    and nse = DsAnds.hyps(10) and bf = DsAnds.hyps(11)
    and w = DsAnds.prems(1) and sts = DsAnds.prems(2)
    and mts = DsAnds.prems(3) and m = DsAnds.prems(4)
  let ?cs' = "c0 # css @ nss"
  let ?R = "map (meval j n ts db) L"
  obtain zs buf' where g0: "mbufn_take
      (\<lambda>as zs. zs @ [mmulti_join n (set c0 # map set css) (map set nss) as])
      ([] :: event_data table list) (mbufn_add (map fst ?R) buf) = (zs, buf')"
    by (cases "mbufn_take
      (\<lambda>as zs. zs @ [mmulti_join n (set c0 # map set css) (map set nss) as])
      ([] :: event_data table list) (mbufn_add (map fst ?R) buf)") auto
  have x: "xs = zs"
    and fe: "\<phi>' = mformula.MAnds (set c0 # map set css) (map set nss) (map snd ?R) buf'"
    using m g0 by (simp_all add: Let_def del: mbufn_take.simps mmulti_join.simps)
  \<comment> \<open>the operands, and their narrowing\<close>
  have la0: "\<forall>i < length L. dsim n (?cs' ! i) tw (Ld ! i) (L ! i)" using la by blast
  have tabs: "\<forall>i < length ?cs'. list_all (ftable n (set (?cs' ! i))) (map fst ?R ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length ?cs'"
    then have iL: "i < length L" using l2 by simp
    have "list_all (ftable n (set (?cs' ! i))) (fst (meval j n ts db (L ! i)))"
      by (rule dsims_tables[OF la0 l1 l2 w iL])
    then show "list_all (ftable n (set (?cs' ! i))) (map fst ?R ! i)"
      using iL by simp
  qed
  have la1: "\<forall>i < length L. dsim n (?cs' ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (?cs' ! i)) as, \<psi>d')
            \<and> dsim n (?cs' ! i) (dnext tw ts) \<psi>d' \<psi>'))"
    using la w sts mts by blast
  have dlr: "length (deval_list j ts db Ld) = length L \<and>
      map fst (deval_list j ts db Ld)
        = map2 (\<lambda>c y. map (dtabc n c) y) ?cs'
            (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (?cs' ! i) (dnext tw ts) (map snd (deval_list j ts db Ld) ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF l1 l2 la1])
  have dl0: "length (deval_list j ts db Ld) = length L" using dlr by blast
  have dl: "map fst (deval_list j ts db Ld)
      = map2 (\<lambda>c y. map (dtabc n c) y) ?cs' (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (?cs' ! i) (dnext tw ts) (map snd (deval_list j ts db Ld) ! i)
      (snd (meval j n ts db (L ! i)))" using dlr by blast
  \<comment> \<open>the buffer\<close>
  have badd: "dbufn n ?cs' (mbufn_add (map fst ?R) buf)
      (mbufn_add (map fst (deval_list j ts db Ld)) dbuf)"
    unfolding dl by (rule dbufn_add[OF bf _ tabs]) (use l2 in simp)
  \<comment> \<open>the join at each firing\<close>
  have step: "\<And>as :: event_data table list. length as = length ?cs' \<Longrightarrow>
      (\<forall>i < length ?cs'. ftable n (set (?cs' ! i)) (as ! i)) \<Longrightarrow>
      dtabc n cs (mmulti_join n (set c0 # map set css) (map set nss) as)
        = dmulti_join ps ns (map2 (dtabc n) ?cs' as)"
  proof -
    fix as :: "event_data table list"
    assume las: "length as = length ?cs'"
      and mas: "\<forall>i < length ?cs'. ftable n (set (?cs' ! i)) (as ! i)"
    obtain T0 r where a0: "as = T0 # r" using las by (cases as) auto
    have lr: "length r = length css + length nss" using las a0 by simp
    define Us where "Us = take (length css) r"
    define Vs where "Vs = drop (length css) r"
    have uv: "r = Us @ Vs" by (simp add: Us_def Vs_def)
    have lu: "length Us = length css" using lr by (simp add: Us_def)
    have lv: "length Vs = length nss" using lr by (simp add: Vs_def)
    have p0: "\<forall>i < length css. ftable n (set (css ! i)) (Us ! i)"
    proof (intro allI impI)
      fix i assume i: "i < length css"
      have "ftable n (set (?cs' ! Suc i)) (as ! Suc i)"
        using mas[rule_format, of "Suc i"] i by simp
      then show "ftable n (set (css ! i)) (Us ! i)"
        using i lu unfolding a0 uv by (simp add: nth_append)
    qed
    have p1: "\<forall>i < length nss. ftable n (set (nss ! i)) (Vs ! i)"
    proof (intro allI impI)
      fix i assume i: "i < length nss"
      have "ftable n (set (?cs' ! Suc (length css + i))) (as ! Suc (length css + i))"
        using mas[rule_format, of "Suc (length css + i)"] i by simp
      then show "ftable n (set (nss ! i)) (Vs ! i)"
        using i lu unfolding a0 uv by (simp add: nth_append)
    qed
    have wc0: "wf_cols n c0" and wcp: "\<forall>c \<in> set css. wf_cols n c"
        and wcn: "\<forall>c \<in> set nss. wf_cols n c"
      using wc by auto
    have t0: "table n (set c0) T0" and f0: "finite T0"
      using mas[rule_format, of 0] a0 by auto
    have pos: "list_all2 (wf_operand n) css Us"
      using lu p0 wcp by (auto simp: list_all2_conv_all_nth)
    have neg: "list_all2 (wf_operand n) nss Vs"
      using lv p1 wcn by (auto simp: list_all2_conv_all_nth)
    have DJ: "dmulti_join (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
          (map2 (dtabc n) (c0 # css @ nss) ((T0 # Us) @ Vs))
        = dtabc n (dands_cols c0 css)
            (mmulti_join n (set c0 # map set css) (map set nss) ((T0 # Us) @ Vs))"
      by (rule dmulti_join_eq[OF conjunct1[OF wc0] conjunct2[OF wc0] t0 f0 pos neg sb])
    show "dtabc n cs (mmulti_join n (set c0 # map set css) (map set nss) as)
        = dmulti_join ps ns (map2 (dtabc n) ?cs' as)"
      using DJ unfolding cse pse nse a0 uv by simp
  qed
  obtain dbuf' where dt: "mbufn_take (\<lambda>as zs. zs @ [dmulti_join ps ns as])
        ([] :: event_data table list) (mbufn_add (map fst (deval_list j ts db Ld)) dbuf)
      = (map (dtabc n cs) zs, dbuf')"
    and bf': "dbufn n ?cs' buf' dbuf'"
    using dbufn_take[OF badd step g0] by blast
  have dv: "deval j ts db (DAnds ps ns Ld dbuf)
      = (map (dtabc n cs) xs, DAnds ps ns (map snd (deval_list j ts db Ld)) dbuf')"
    using dt x by (simp add: Let_def del: mbufn_take.simps)
  have s2: "dsim n cs (dnext tw ts) (DAnds ps ns (map snd (deval_list j ts db Ld)) dbuf')
      (mformula.MAnds (set c0 # map set css) (map set nss) (map snd ?R) buf')"
  proof (rule dsim.DsAnds)
    show "wf_cols n cs" by (rule wf)
    show "produces n (set cs)
        (mformula.MAnds (set c0 # map set css) (map set nss) (map snd ?R) buf')"
      using produces_next[OF pr w m] fe by simp
    show "\<forall>i < length (map snd ?R). dsim n (?cs' ! i) (dnext tw ts)
        (map snd (deval_list j ts db Ld) ! i) (map snd ?R ! i)"
    proof (intro allI impI)
      fix i assume "i < length (map snd ?R)"
      then have iL: "i < length L" by simp
      show "dsim n (?cs' ! i) (dnext tw ts) (map snd (deval_list j ts db Ld) ! i) (map snd ?R ! i)"
        using dl2 iL by simp
    qed
    show "length (map snd (deval_list j ts db Ld)) = length (map snd ?R)"
      using dl0 by simp
    show "length ?cs' = length (map snd ?R)" using l2 by simp
    show "\<forall>c \<in> set ?cs'. wf_cols n c" by (rule wc)
    show "\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)" by (rule sb)
    show "cs = dands_cols c0 css" by (rule cse)
    show "ps = dands_plans c0 css" by (rule pse)
    show "ns = dands_plans (dands_cols c0 css) nss" by (rule nse)
    show "dbufn n ?cs' buf' dbuf'" by (rule bf')
  qed
  show ?case using dv s2 fe by auto
next
  case (DsAgg n cs args \<phi> gcols tw \<phi>d y)
  note wf = DsAgg.hyps(1) and pr = DsAgg.hyps(2) and sim = DsAgg.hyps(3) and IH = DsAgg.hyps(4)
    and wg = DsAgg.hyps(5) and ne = DsAgg.hyps(6) and ye = DsAgg.hyps(7) and yn = DsAgg.hyps(8)
    and yg = DsAgg.hyps(9) and g0 = DsAgg.hyps(10) and fv = DsAgg.hyps(11)
    and cse = DsAgg.hyps(12)
    and w = DsAgg.prems(1) and sts = DsAgg.prems(2)
    and mts = DsAgg.prems(3) and m = DsAgg.prems(4)
  let ?mm = "length (aggargs_tys args)"
  let ?cc = "agg_cols ?mm gcols"
  obtain ys \<psi>' where e: "meval j (?mm + n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (?mm + n) ts db \<phi>")
  have x: "xs = map (eval_aggargs args) ys" and f: "\<phi>' = mformula.MAgg args \<psi>'"
    using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (?mm + n) ?cc) ys, \<psi>d')"
    and sim': "dsim (?mm + n) ?cc (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e] by blast
  have t: "list_all (ftable (?mm + n) (set ?cc)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w e])
  have "map (dagg (aggargs_g0 args) (aggargs_\<omega> args) (reindex_trm ?cc (aggargs_f args)) ?mm
          (ins_pos gcols y)) (map (dtabc (?mm + n) ?cc) ys) = map (dtabc n cs) xs"
    unfolding x cse using t wg yn yg fv g0 ne ye
    by (intro nth_equalityI)
      (auto simp: list_all_iff eval_aggargs_def dagg_eval_agg)
  then show ?case using d sim' produces_next[OF pr w m] wf wg ne ye yn yg g0 fv cse f
    by (auto intro!: dsim.DsAgg)
next
  case (DsSince n cs args \<phi> \<psi> buf aux cs_L tw \<phi>d \<psi>d dags pl daux dbuf)
  note wf = DsSince.hyps(1) and pr = DsSince.hyps(2)
    and sim1 = DsSince.hyps(3) and IH1 = DsSince.hyps(4)
    and sim2 = DsSince.hyps(5) and IH2 = DsSince.hyps(6)
    and wfL = DsSince.hyps(7) and sub = DsSince.hyps(8) and agg = DsSince.hyps(9)
    and an = DsSince.hyps(10) and aL = DsSince.hyps(11) and aR = DsSince.hyps(12)
    and dag = DsSince.hyps(13) and pe = DsSince.hyps(14) and rel = DsSince.hyps(15)
    and w = DsSince.prems(1) and sts = DsSince.prems(2)
    and mts = DsSince.prems(3) and m = DsSince.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 an by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs_L) as, \<phi>d2)"
    and s1: "dsim n cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2] by blast
  have ta: "list_all (ftable n (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w e2])
  have emb: "map (dembedp pl \<circ> dtabc n cs_L) as = map (dtabc n cs) as"
  proof (intro map_cong refl)
    fix a assume "a \<in> set as"
    then have "table n (set cs_L) a" using ta by (simp add: list_all_iff)
    then show "(dembedp pl \<circ> dtabc n cs_L) a = dtabc n cs a"
      unfolding pe o_def using wf wfL by (intro dembedp_dtabc) auto
  qed
  obtain dzs dbuf2 daux2 where d3: "meval_since dags []
      (mbuf2S_add (map (dtabc n cs) as) (map (dtabc n cs) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)"
    by (cases "meval_since dags []
      (mbuf2S_add (map (dtabc n cs) as) (map (dtabc n cs) bs) ts dbuf) daux")
  have radd: "dsince_rel n cs cs_L args (dnext tw ts) aux daux (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (dtabc n cs) as) (map (dtabc n cs) bs) ts dbuf)"
    by (rule dsince_rel_add[OF rel ta tb sts mts])
  have d3': "meval_since (dargs cs cs_L args) (map (dtabc n cs) [])
      (mbuf2S_add (map (dtabc n cs) as) (map (dtabc n cs) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)" using d3 unfolding dag by simp
  have step: "dzs = map (dtabc n cs) zs \<and>
      dsince_rel n cs cs_L args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using eval_since_rel[OF _ _ sub agg an aL aR e3 d3' radd] wf by simp
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DSince dags pl \<phi>d \<psi>d dbuf daux)
        = (map (dtabc n cs) xs, DSince dags pl \<phi>d2 \<psi>d2 dbuf2 daux2)"
      using d1 d2 d3 step x by (simp add: emb)
    show "dsim n cs (dnext tw ts) (DSince dags pl \<phi>d2 \<psi>d2 dbuf2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsSince[OF wf produces_next[OF pr w m, unfolded f] s1 s2 wfL sub agg an aL aR
            dag pe]) (use step in simp)
  qed
next
  case (DsUntil n cs args \<phi> \<psi> buf nts t aux cs_L tw \<phi>d \<psi>d dags pl daux dbuf)
  note wf = DsUntil.hyps(1) and pr = DsUntil.hyps(2)
    and sim1 = DsUntil.hyps(3) and IH1 = DsUntil.hyps(4)
    and sim2 = DsUntil.hyps(5) and IH2 = DsUntil.hyps(6)
    and wfL = DsUntil.hyps(7) and sub = DsUntil.hyps(8) and agg = DsUntil.hyps(9)
    and an = DsUntil.hyps(10) and aL = DsUntil.hyps(11) and aR = DsUntil.hyps(12)
    and dag = DsUntil.hyps(13) and pe = DsUntil.hyps(14) and rel = DsUntil.hyps(15)
    and w = DsUntil.prems(1) and sts = DsUntil.prems(2)
    and mts = DsUntil.prems(3) and m = DsUntil.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain aux1 buf1 nt nts1 where e3: "mbuf2t_take (add_new_muaux_dq args) aux
      (mbuf2_add as bs buf) t (nts @ ts) = (aux1, buf1, nt, nts1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ ts)")
  obtain zs aux2 where e4: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    by (cases "eval_muaux_dq args nt aux1")
  have x: "xs = zs" and f: "\<phi>' = mformula.MUntil args \<phi>2 \<psi>2 buf1 nts1 nt aux2"
    using m e1 e2 e3 e4 an by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs_L) as, \<phi>d2)"
    and s1: "dsim n cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2] by blast
  have ta: "list_all (ftable n (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w e2])
  have emb: "map (dembedp pl \<circ> dtabc n cs_L) as = map (dtabc n cs) as"
  proof (intro map_cong refl)
    fix a assume "a \<in> set as"
    then have "table n (set cs_L) a" using ta by (simp add: list_all_iff)
    then show "(dembedp pl \<circ> dtabc n cs_L) a = dtabc n cs a"
      unfolding pe o_def using wf wfL by (intro dembedp_dtabc) auto
  qed
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (add_new_muaux_dq dags) daux
      (mbuf2_add (map (dtabc n cs) as) (map (dtabc n cs) bs) dbuf) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (add_new_muaux_dq dags) daux
      (mbuf2_add (map (dtabc n cs) as) (map (dtabc n cs) bs) dbuf) t (nts @ ts)")
  obtain dzs daux2 where d4: "eval_muaux_dq dags dnt daux1 = (dzs, daux2)"
    by (cases "eval_muaux_dq dags dnt daux1")
  have step: "dzs = map (dtabc n cs) zs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (dtabc n cs) (fst buf1), map (dtabc n cs) (snd buf1)) \<and>
      duntil_rel n cs cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF _ _ sub agg an aL aR rel ta tb sts mts e3
        d3[unfolded dag] e4 d4[unfolded dag]]) (use wf in auto)
  have dz: "dzs = map (dtabc n cs) zs" and dn: "dnt = nt" and dns: "dnts1 = nts1"
    and rel': "duntil_rel n cs cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DUntil dags pl \<phi>d \<psi>d dbuf nts t daux)
        = (map (dtabc n cs) xs, DUntil dags pl \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2)"
      using d1 d2 d3 d4 dz dn dns x by (simp add: emb)
    show "dsim n cs (dnext tw ts) (DUntil dags pl \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsUntil[OF wf produces_next[OF pr w m, unfolded f] s1 s2 wfL sub agg an aL aR
            dag pe rel'])
  qed
qed

(*<*)
end
(*>*)
