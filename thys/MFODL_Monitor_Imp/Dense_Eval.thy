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
  the condition its predicate nodes need.
\<close>

definition wf_db :: "database \<Rightarrow> bool" where
  "wf_db db \<longleftrightarrow> (\<forall>e ar X. Mapping.lookup db (e, ar) = Some X \<longrightarrow>
     list_all (\<lambda>T. table ar {0..<ar} T) X)"

lemma wf_dbD:
  "wf_db db \<Longrightarrow> Mapping.lookup db (e, ar) = Some X \<Longrightarrow> T \<in> set X \<Longrightarrow>
     table ar {0..<ar} T"
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

inductive dsim :: "nat \<Rightarrow> cols \<Rightarrow> dformula \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  DsPure: "wf_cols n cs \<Longrightarrow> produces n (set cs) \<phi> \<Longrightarrow>
    dsim n cs (DPure \<phi> n (wide_mask n cs)) \<phi>"
| DsRel: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MRel rel) \<Longrightarrow>
    table n (set cs) rel \<Longrightarrow>
    dsim n cs (DRel (dtabc n cs rel)) (mformula.MRel rel)"
| DsPredC: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPred e tms Copy) \<Longrightarrow>
    tms = map Formula.Var [0..<n] \<Longrightarrow> cs = [0..<n] \<Longrightarrow>
    dsim n cs (DPredS e n) (mformula.MPred e tms Copy)"
| DsPredS: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPred e tms Simple) \<Longrightarrow>
    is_simple_pattern tms 0 \<Longrightarrow> cs = smp_cols tms \<Longrightarrow>
    dsim n cs (DPredS e (length tms)) (mformula.MPred e tms Simple)"
| DsPredM: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPred e tms Match) \<Longrightarrow>
    dsim n cs (DPredM e (length tms) tms cs) (mformula.MPred e tms Match)"
| DsAndRel: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MAndRel \<phi> (t1, p, c, t2)) \<Longrightarrow>
    dsim n cs \<phi>d \<phi> \<Longrightarrow>
    Formula.fv_trm t1 \<subseteq> set cs \<Longrightarrow> Formula.fv_trm t2 \<subseteq> set cs \<Longrightarrow>
    dsim n cs (DAndRel \<phi>d (reindex_constraint cs (t1, p, c, t2)))
      (mformula.MAndRel \<phi> (t1, p, c, t2))"
| DsNeg: "produces n {} (mformula.MNeg \<phi>) \<Longrightarrow> dsim n [] \<phi>d \<phi> \<Longrightarrow>
    dsim n [] (DNeg \<phi>d) (mformula.MNeg \<phi>)"
| DsExists: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MExists \<phi>) \<Longrightarrow>
    dsim (Suc n) ccs \<phi>d \<phi> \<Longrightarrow> cs = ex_cols ccs \<Longrightarrow> b = ex_drop0 ccs \<Longrightarrow>
    dsim n cs (DExists \<phi>d b) (mformula.MExists \<phi>)"
| DsOr: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MOr \<phi> \<psi> buf) \<Longrightarrow>
    dsim n cs \<phi>d \<phi> \<Longrightarrow> dsim n cs \<psi>d \<psi> \<Longrightarrow>
    dbuf2 n cs cs buf dbuf \<Longrightarrow>
    dsim n cs (DOr \<phi>d \<psi>d dbuf) (mformula.MOr \<phi> \<psi> buf)"
| DsAnd: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MAnd (set cs1) \<phi> pos (set cs2) \<psi> buf) \<Longrightarrow>
    dsim n cs1 \<phi>d \<phi> \<Longrightarrow> dsim n cs2 \<psi>d \<psi> \<Longrightarrow>
    cs = merge_cols cs1 cs2 \<Longrightarrow> pl = mk_djoin cs1 cs2 \<Longrightarrow>
    (\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1) \<Longrightarrow>
    dbuf2 n cs1 cs2 buf dbuf \<Longrightarrow>
    dsim n cs (DAnd pl \<phi>d pos \<psi>d dbuf) (mformula.MAnd (set cs1) \<phi> pos (set cs2) \<psi> buf)"
| DsPrev: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MPrev I \<phi> first buf nts) \<Longrightarrow>
    dsim n cs \<phi>d \<phi> \<Longrightarrow>
    list_all (ftable n (set cs)) buf \<Longrightarrow> dbuf = map (dtabc n cs) buf \<Longrightarrow>
    dsim n cs (DPrev I \<phi>d first dbuf nts) (mformula.MPrev I \<phi> first buf nts)"
| DsNext: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) (mformula.MNext I \<phi> first nts) \<Longrightarrow>
    dsim n cs \<phi>d \<phi> \<Longrightarrow>
    dsim n cs (DNext I \<phi>d first nts) (mformula.MNext I \<phi> first nts)"
| DsAnds: "wf_cols n cs \<Longrightarrow>
    produces n (set cs)
      (mformula.MAnds (set c0 # map set css) (map set nss) L buf) \<Longrightarrow>
    (\<forall>i < length L. dsim n ((c0 # css @ nss) ! i) (Ld ! i) (L ! i)) \<Longrightarrow>
    length Ld = length L \<Longrightarrow> length (c0 # css @ nss) = length L \<Longrightarrow>
    (\<forall>c \<in> set (c0 # css @ nss). wf_cols n c) \<Longrightarrow>
    (\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)) \<Longrightarrow>
    cs = dands_cols c0 css \<Longrightarrow>
    ps = dands_plans c0 css \<Longrightarrow> ns = dands_plans (dands_cols c0 css) nss \<Longrightarrow>
    dbufn n (c0 # css @ nss) buf dbuf \<Longrightarrow>
    dsim n cs (DAnds ps ns Ld dbuf)
      (mformula.MAnds (set c0 # map set css) (map set nss) L buf)"
| DsAgg: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MAgg args \<phi>) \<Longrightarrow>
    dsim (length (aggargs_tys args) + n) (agg_cols (length (aggargs_tys args)) gcols) \<phi>d \<phi> \<Longrightarrow>
    wf_cols n gcols \<Longrightarrow> aggargs_n args = n \<Longrightarrow> aggargs_y args = y \<Longrightarrow>
    y < n \<Longrightarrow> y \<notin> set gcols \<Longrightarrow>
    (aggargs_g0 args \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f args) \<subseteq> set (agg_cols (length (aggargs_tys args)) gcols) \<Longrightarrow>
    cs = merge_cols gcols [y] \<Longrightarrow>
    dsim n cs (DAgg (aggargs_g0 args) (aggargs_\<omega> args)
        (reindex_trm (agg_cols (length (aggargs_tys args)) gcols) (aggargs_f args))
        (length (aggargs_tys args)) (ins_pos gcols y) \<phi>d) (mformula.MAgg args \<phi>)"

text \<open>The two facts the relation is designed to hand out at every node.\<close>

lemma dsim_wf_cols: "dsim n cs \<phi>d \<phi> \<Longrightarrow> wf_cols n cs"
  by (induct rule: dsim.induct)
    (auto simp: ex_cols_sorted ex_cols_bound sorted_merge_cols set_merge_cols)

lemma dsim_produces: "dsim n cs \<phi>d \<phi> \<Longrightarrow> produces n (set cs) \<phi>"
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
  "(\<forall>i < length L. dsim n (css ! i) (Ld ! i) (L ! i)) \<Longrightarrow>
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
    have h: "dsim n c \<psi>d \<psi>" using la unfolding c d by (auto dest: spec[of _ 0])
    obtain as \<psi>2 where e: "meval j n ts db \<psi> = (as, \<psi>2)" by (cases "meval j n ts db \<psi>")
    have "list_all (ftable n (set c)) as" by (rule produces_tables[OF dsim_produces[OF h] w e])
    then show ?thesis unfolding c 0 using e by simp
  next
    case (Suc i')
    have ta: "\<forall>k < length L'. dsim n (css' ! k) (Ld' ! k) (L' ! k)"
      using la unfolding c d by auto
    show ?thesis using IH[OF ta _ _ w] l1 l2 i unfolding c d Suc by simp
  qed
qed simp

lemma deval_list_rel:
  "length Ld = length L \<Longrightarrow> length css = length L \<Longrightarrow>
   (\<forall>i < length L. dsim n (css ! i) (Ld ! i) (L ! i) \<and>
       (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
          (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (css ! i)) as, \<psi>d')
             \<and> dsim n (css ! i) \<psi>d' \<psi>'))) \<Longrightarrow>
   length (deval_list j ts db Ld) = length L \<and>
   map fst (deval_list j ts db Ld)
       = map2 (\<lambda>c x. map (dtabc n c) x) css (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
   (\<forall>i < length L. dsim n (css ! i) (map snd (deval_list j ts db Ld) ! i)
       (snd (meval j n ts db (L ! i))))"
proof (induct L arbitrary: css Ld)
  case (Cons \<psi> L')
  note l1 = Cons(2) and l2 = Cons(3) and la = Cons(4) and IH = Cons(1)
  obtain c css' where c: "css = c # css'" using l2 by (cases css) auto
  obtain \<psi>d Ld' where d: "Ld = \<psi>d # Ld'" using l1 by (cases Ld) auto
  have h: "dsim n c \<psi>d \<psi> \<and> (\<forall>as \<psi>'. meval j n ts db \<psi> = (as, \<psi>') \<longrightarrow>
      (\<exists>\<psi>d'. deval j ts db \<psi>d = (map (dtabc n c) as, \<psi>d') \<and> dsim n c \<psi>d' \<psi>'))"
    using la unfolding c d by (auto dest: spec[of _ 0])
  have ta: "\<forall>k < length L'. dsim n (css' ! k) (Ld' ! k) (L' ! k) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L' ! k) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld' ! k) = (map (dtabc n (css' ! k)) as, \<psi>d')
            \<and> dsim n (css' ! k) \<psi>d' \<psi>'))"
    using la unfolding c d by auto
  obtain as \<psi>2 where e: "meval j n ts db \<psi> = (as, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain \<psi>d2 where dv: "deval j ts db \<psi>d = (map (dtabc n c) as, \<psi>d2)"
    and sm: "dsim n c \<psi>d2 \<psi>2" using h e by blast
  have rest: "length (deval_list j ts db Ld') = length L' \<and>
      map fst (deval_list j ts db Ld')
        = map2 (\<lambda>c x. map (dtabc n c) x) css'
            (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L') \<and>
      (\<forall>k < length L'. dsim n (css' ! k) (map snd (deval_list j ts db Ld') ! k)
          (snd (meval j n ts db (L' ! k))))"
  proof (rule IH)
    show "length Ld' = length L'" using l1 unfolding d by simp
    show "length css' = length L'" using l2 unfolding c by simp
    show "\<forall>k < length L'. dsim n (css' ! k) (Ld' ! k) (L' ! k) \<and>
        (\<forall>as \<psi>'. meval j n ts db (L' ! k) = (as, \<psi>') \<longrightarrow>
           (\<exists>\<psi>d'. deval j ts db (Ld' ! k) = (map (dtabc n (css' ! k)) as, \<psi>d')
              \<and> dsim n (css' ! k) \<psi>d' \<psi>'))" by (rule ta)
  qed
  show ?case unfolding c d using rest dv sm e by (auto simp: nth_Cons split: nat.splits)
qed simp

text \<open>
  The simulation itself.  Every case is one theorem of @{theory MFODL_Monitor_Imp.Dense}
  applied pointwise to the operand's output list, with @{const produces} supplying the
  operand well-formedness and @{thm produces_next} re-establishing it for the successor.
\<close>

theorem dsim_deval:
  "dsim n cs \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc n cs) xs, \<phi>d') \<and> dsim n cs \<phi>d' \<phi>'"
proof (induct arbitrary: j ts db xs \<phi>' rule: dsim.induct)
  case (DsPure n cs \<phi>)
  note wf = DsPure.hyps(1) and p = DsPure.hyps(2)
    and w = DsPure.prems(1) and m = DsPure.prems(2)
  have t: "list_all (ftable n (set cs)) xs" by (rule produces_tables[OF p w m])
  have "map (dnarrow (wide_mask n cs)) xs = map (dtabc n cs) xs"
    using t by (intro map_cong refl dnarrow_dtabc) (auto simp: list_all_iff)
  then show ?case using m wf produces_next[OF p w m] by (auto intro!: dsim.DsPure)
next
  case (DsRel n cs rel)
  note wf = DsRel.hyps(1) and p = DsRel.hyps(2) and t = DsRel.hyps(3)
    and w = DsRel.prems(1) and m = DsRel.prems(2)
  have x: "xs = replicate (length ts) rel" and f: "\<phi>' = mformula.MRel rel" using m by simp_all
  show ?case using wf p t by (simp add: x f dsim.DsRel)
next
  case (DsPredC n cs e tms)
  note wf = DsPredC.hyps(1) and pr = DsPredC.hyps(2) and tm = DsPredC.hyps(3)
    and cse = DsPredC.hyps(4) and w = DsPredC.prems(1) and m = DsPredC.prems(2)
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
  case (DsPredS n cs e tms)
  note wf = DsPredS.hyps(1) and pr = DsPredS.hyps(2) and sp = DsPredS.hyps(3)
    and cse = DsPredS.hyps(4) and w = DsPredS.prems(1) and m = DsPredS.prems(2)
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
  case (DsPredM n cs e tms)
  note wf = DsPredM.hyps(1) and pr = DsPredM.hyps(2)
    and w = DsPredM.prems(1) and m = DsPredM.prems(2)
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
  case (DsAndRel n cs \<phi> t1 p c t2 \<phi>d)
  note wf = DsAndRel.hyps(1) and pr = DsAndRel.hyps(2) and sim = DsAndRel.hyps(3)
    and IH = DsAndRel.hyps(4) and fv1 = DsAndRel.hyps(5) and fv2 = DsAndRel.hyps(6)
    and w = DsAndRel.prems(1) and m = DsAndRel.prems(2)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (Set.filter (eval_constraint (t1, p, c, t2))) ys"
    and f: "\<phi>' = mformula.MAndRel \<psi>' (t1, p, c, t2)" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs \<psi>d' \<psi>'" using IH[OF w e] by blast
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
  case (DsNeg n \<phi> \<phi>d)
  note pr = DsNeg.hyps(1) and sim = DsNeg.hyps(2) and IH = DsNeg.hyps(3)
    and w = DsNeg.prems(1) and m = DsNeg.prems(2)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. if r = empty_table then unit_table n else empty_table) ys"
    and f: "\<phi>' = mformula.MNeg \<psi>'" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n []) ys, \<psi>d')"
    and sim': "dsim n [] \<psi>d' \<psi>'" using IH[OF w e] by blast
  have "map (\<lambda>r. if r = empty_table then unit_table 0 else empty_table) (map (dtabc n []) ys)
      = map (dtabc n []) xs"
    unfolding x by (simp add: dtabc_neg)
  then show ?case using d sim' produces_next[OF pr w m] f by (auto intro!: dsim.DsNeg)
next
  case (DsExists n cs \<phi> ccs \<phi>d b)
  note wf = DsExists.hyps(1) and pr = DsExists.hyps(2) and sim = DsExists.hyps(3)
    and IH = DsExists.hyps(4) and cse = DsExists.hyps(5) and be = DsExists.hyps(6)
    and w = DsExists.prems(1) and m = DsExists.prems(2)
  obtain ys \<psi>' where e: "meval j (Suc n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (Suc n) ts db \<phi>")
  have x: "xs = map (\<lambda>r. tl ` r) ys" and f: "\<phi>' = mformula.MExists \<psi>'" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (Suc n) ccs) ys, \<psi>d')"
    and sim': "dsim (Suc n) ccs \<psi>d' \<psi>'" using IH[OF w e] by blast
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
  case (DsOr n cs \<phi> \<psi> buf \<phi>d \<psi>d dbuf)
  note wf = DsOr.hyps(1) and pr = DsOr.hyps(2) and sim1 = DsOr.hyps(3) and IH1 = DsOr.hyps(4)
    and sim2 = DsOr.hyps(5) and IH2 = DsOr.hyps(6) and bf = DsOr.hyps(7)
    and w = DsOr.prems(1) and m = DsOr.prems(2)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MOr \<phi>2 \<psi>2 buf2" using m e1 e2 e3 by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs) as, \<phi>d2)"
    and s1: "dsim n cs \<phi>d2 \<phi>2" using IH1[OF w e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs \<psi>d2 \<psi>2" using IH2[OF w e2] by blast
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
  case (DsAnd n cs cs1 \<phi> pos cs2 \<psi> buf \<phi>d \<psi>d pl dbuf)
  note wf = DsAnd.hyps(1) and pr = DsAnd.hyps(2) and sim1 = DsAnd.hyps(3)
    and IH1 = DsAnd.hyps(4) and sim2 = DsAnd.hyps(5) and IH2 = DsAnd.hyps(6)
    and cse = DsAnd.hyps(7) and ple = DsAnd.hyps(8) and neg = DsAnd.hyps(9)
    and bf = DsAnd.hyps(10)
    and w = DsAnd.prems(1) and m = DsAnd.prems(2)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. bin_join n (set cs1) r1 pos (set cs2) r2)
        (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. bin_join n (set cs1) r1 pos (set cs2) r2)
        (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MAnd (set cs1) \<phi>2 pos (set cs2) \<psi>2 buf2"
    using m e1 e2 e3 by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs1) as, \<phi>d2)"
    and s1: "dsim n cs1 \<phi>d2 \<phi>2" using IH1[OF w e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs2) bs, \<psi>d2)"
    and s2: "dsim n cs2 \<psi>d2 \<psi>2" using IH2[OF w e2] by blast
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
  case (DsPrev n cs I \<phi> first buf nts \<phi>d dbuf)
  note wf = DsPrev.hyps(1) and pr = DsPrev.hyps(2) and sim = DsPrev.hyps(3)
    and IH = DsPrev.hyps(4) and lb = DsPrev.hyps(5) and be = DsPrev.hyps(6)
    and w = DsPrev.prems(1) and m = DsPrev.prems(2)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs \<psi>d' \<psi>'" using IH[OF w e] by blast
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
  case (DsNext n cs I \<phi> first nts \<phi>d)
  note wf = DsNext.hyps(1) and pr = DsNext.hyps(2) and sim = DsNext.hyps(3)
    and IH = DsNext.hyps(4) and w = DsNext.prems(1) and m = DsNext.prems(2)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs \<psi>d' \<psi>'" using IH[OF w e] by blast
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
  case (DsAnds n cs c0 css nss L buf Ld ps ns dbuf)
  note wf = DsAnds.hyps(1) and pr = DsAnds.hyps(2) and la = DsAnds.hyps(3)
    and l1 = DsAnds.hyps(4) and l2 = DsAnds.hyps(5) and wc = DsAnds.hyps(6)
    and sb = DsAnds.hyps(7) and cse = DsAnds.hyps(8) and pse = DsAnds.hyps(9)
    and nse = DsAnds.hyps(10) and bf = DsAnds.hyps(11)
    and w = DsAnds.prems(1) and m = DsAnds.prems(2)
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
  have la0: "\<forall>i < length L. dsim n (?cs' ! i) (Ld ! i) (L ! i)" using la by blast
  have tabs: "\<forall>i < length ?cs'. list_all (ftable n (set (?cs' ! i))) (map fst ?R ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length ?cs'"
    then have iL: "i < length L" using l2 by simp
    have "list_all (ftable n (set (?cs' ! i))) (fst (meval j n ts db (L ! i)))"
      by (rule dsims_tables[OF la0 l1 l2 w iL])
    then show "list_all (ftable n (set (?cs' ! i))) (map fst ?R ! i)"
      using iL by simp
  qed
  have la1: "\<forall>i < length L. dsim n (?cs' ! i) (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (?cs' ! i)) as, \<psi>d')
            \<and> dsim n (?cs' ! i) \<psi>d' \<psi>'))"
    using la w by blast
  have dlr: "length (deval_list j ts db Ld) = length L \<and>
      map fst (deval_list j ts db Ld)
        = map2 (\<lambda>c y. map (dtabc n c) y) ?cs'
            (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (?cs' ! i) (map snd (deval_list j ts db Ld) ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF l1 l2 la1])
  have dl0: "length (deval_list j ts db Ld) = length L" using dlr by blast
  have dl: "map fst (deval_list j ts db Ld)
      = map2 (\<lambda>c y. map (dtabc n c) y) ?cs' (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (?cs' ! i) (map snd (deval_list j ts db Ld) ! i)
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
  have s2: "dsim n cs (DAnds ps ns (map snd (deval_list j ts db Ld)) dbuf')
      (mformula.MAnds (set c0 # map set css) (map set nss) (map snd ?R) buf')"
  proof (rule dsim.DsAnds)
    show "wf_cols n cs" by (rule wf)
    show "produces n (set cs)
        (mformula.MAnds (set c0 # map set css) (map set nss) (map snd ?R) buf')"
      using produces_next[OF pr w m] fe by simp
    show "\<forall>i < length (map snd ?R). dsim n (?cs' ! i)
        (map snd (deval_list j ts db Ld) ! i) (map snd ?R ! i)"
    proof (intro allI impI)
      fix i assume "i < length (map snd ?R)"
      then have iL: "i < length L" by simp
      show "dsim n (?cs' ! i) (map snd (deval_list j ts db Ld) ! i) (map snd ?R ! i)"
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
  case (DsAgg n cs args \<phi> gcols \<phi>d y)
  note wf = DsAgg.hyps(1) and pr = DsAgg.hyps(2) and sim = DsAgg.hyps(3) and IH = DsAgg.hyps(4)
    and wg = DsAgg.hyps(5) and ne = DsAgg.hyps(6) and ye = DsAgg.hyps(7) and yn = DsAgg.hyps(8)
    and yg = DsAgg.hyps(9) and g0 = DsAgg.hyps(10) and fv = DsAgg.hyps(11)
    and cse = DsAgg.hyps(12)
    and w = DsAgg.prems(1) and m = DsAgg.prems(2)
  let ?mm = "length (aggargs_tys args)"
  let ?cc = "agg_cols ?mm gcols"
  obtain ys \<psi>' where e: "meval j (?mm + n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (?mm + n) ts db \<phi>")
  have x: "xs = map (eval_aggargs args) ys" and f: "\<phi>' = mformula.MAgg args \<psi>'"
    using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (?mm + n) ?cc) ys, \<psi>d')"
    and sim': "dsim (?mm + n) ?cc \<psi>d' \<psi>'" using IH[OF w e] by blast
  have t: "list_all (ftable (?mm + n) (set ?cc)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w e])
  have "map (dagg (aggargs_g0 args) (aggargs_\<omega> args) (reindex_trm ?cc (aggargs_f args)) ?mm
          (ins_pos gcols y)) (map (dtabc (?mm + n) ?cc) ys) = map (dtabc n cs) xs"
    unfolding x cse using t wg yn yg fv g0 ne ye
    by (intro nth_equalityI)
      (auto simp: list_all_iff eval_aggargs_def dagg_eval_agg)
  then show ?case using d sim' produces_next[OF pr w m] wf wg ne ye yn yg g0 fv cse f
    by (auto intro!: dsim.DsAgg)
qed

(*<*)
end
(*>*)
