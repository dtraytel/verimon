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

coinductive produces :: "nat \<Rightarrow> nat set \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool"
  where produces: "(\<And>j ts db xs \<phi>'. meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable n A) xs \<and> produces n A \<phi>') \<Longrightarrow> produces n A \<phi>"

lemma produces_step:
  "produces n A \<phi> \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
     list_all (ftable n A) xs \<and> produces n A \<phi>'"
  by (erule produces.cases) blast

lemma produces_tables:
  "produces n A \<phi> \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> list_all (ftable n A) xs"
  by (drule produces_step) auto

lemma produces_next:
  "produces n A \<phi> \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> produces n A \<phi>'"
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
  | DAndRel dformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | DNeg dformula
  | DExists dformula bool
  | DAgg bool "ty Formula.agg_op" Formula.trm nat nat dformula
  | DOr dformula dformula "event_data mbuf2"
  | DAnd djoin_plan dformula bool dformula "event_data mbuf2"

fun deval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> dformula \<Rightarrow> event_data table list \<times> dformula" where
  "deval j ts db (DPure \<phi> m msk) =
     (let (xs, \<phi>') = meval j m ts db \<phi> in (map (dnarrow msk) xs, DPure \<phi>' m msk))"
| "deval j ts db (DRel rel) = (replicate (length ts) rel, DRel rel)"
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

inductive dsim :: "nat \<Rightarrow> cols \<Rightarrow> dformula \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  DsPure: "wf_cols n cs \<Longrightarrow> produces n (set cs) \<phi> \<Longrightarrow>
    dsim n cs (DPure \<phi> n (wide_mask n cs)) \<phi>"
| DsRel: "wf_cols n cs \<Longrightarrow> produces n (set cs) (mformula.MRel rel) \<Longrightarrow>
    table n (set cs) rel \<Longrightarrow>
    dsim n cs (DRel (dtabc n cs rel)) (mformula.MRel rel)"
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

text \<open>
  The simulation itself.  Every case is one theorem of @{theory MFODL_Monitor_Imp.Dense}
  applied pointwise to the operand's output list, with @{const produces} supplying the
  operand well-formedness and @{thm produces_next} re-establishing it for the successor.
\<close>

theorem dsim_deval:
  "dsim n cs \<phi>d \<phi> \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc n cs) xs, \<phi>d') \<and> dsim n cs \<phi>d' \<phi>'"
proof (induct arbitrary: j ts db xs \<phi>' rule: dsim.induct)
  case (DsPure n cs \<phi>)
  note wf = DsPure.hyps(1) and p = DsPure.hyps(2) and m = DsPure.prems
  have t: "list_all (ftable n (set cs)) xs" by (rule produces_tables[OF p m])
  have "map (dnarrow (wide_mask n cs)) xs = map (dtabc n cs) xs"
    using t by (intro map_cong refl dnarrow_dtabc) (auto simp: list_all_iff)
  then show ?case using m wf produces_next[OF p m] by (auto intro!: dsim.DsPure)
next
  case (DsRel n cs rel)
  note wf = DsRel.hyps(1) and p = DsRel.hyps(2) and t = DsRel.hyps(3) and m = DsRel.prems
  have x: "xs = replicate (length ts) rel" and f: "\<phi>' = mformula.MRel rel" using m by simp_all
  show ?case using wf p t by (simp add: x f dsim.DsRel)
next
  case (DsAndRel n cs \<phi> t1 p c t2 \<phi>d)
  note wf = DsAndRel.hyps(1) and pr = DsAndRel.hyps(2) and sim = DsAndRel.hyps(3)
    and IH = DsAndRel.hyps(4) and fv1 = DsAndRel.hyps(5) and fv2 = DsAndRel.hyps(6)
    and m = DsAndRel.prems
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (Set.filter (eval_constraint (t1, p, c, t2))) ys"
    and f: "\<phi>' = mformula.MAndRel \<psi>' (t1, p, c, t2)" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs \<psi>d' \<psi>'" using IH[OF e] by blast
  have t: "list_all (ftable n (set cs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] e])
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
  then show ?case using d sim' produces_next[OF pr m] wf fv1 fv2 f
    by (auto intro!: dsim.DsAndRel)
next
  case (DsNeg n \<phi> \<phi>d)
  note pr = DsNeg.hyps(1) and sim = DsNeg.hyps(2) and IH = DsNeg.hyps(3) and m = DsNeg.prems
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. if r = empty_table then unit_table n else empty_table) ys"
    and f: "\<phi>' = mformula.MNeg \<psi>'" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n []) ys, \<psi>d')"
    and sim': "dsim n [] \<psi>d' \<psi>'" using IH[OF e] by blast
  have "map (\<lambda>r. if r = empty_table then unit_table 0 else empty_table) (map (dtabc n []) ys)
      = map (dtabc n []) xs"
    unfolding x by (simp add: dtabc_neg)
  then show ?case using d sim' produces_next[OF pr m] f by (auto intro!: dsim.DsNeg)
next
  case (DsExists n cs \<phi> ccs \<phi>d b)
  note wf = DsExists.hyps(1) and pr = DsExists.hyps(2) and sim = DsExists.hyps(3)
    and IH = DsExists.hyps(4) and cse = DsExists.hyps(5) and be = DsExists.hyps(6)
    and m = DsExists.prems
  obtain ys \<psi>' where e: "meval j (Suc n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (Suc n) ts db \<phi>")
  have x: "xs = map (\<lambda>r. tl ` r) ys" and f: "\<phi>' = mformula.MExists \<psi>'" using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (Suc n) ccs) ys, \<psi>d')"
    and sim': "dsim (Suc n) ccs \<psi>d' \<psi>'" using IH[OF e] by blast
  have wfc: "wf_cols (Suc n) ccs" by (rule dsim_wf_cols[OF sim])
  have t: "list_all (ftable (Suc n) (set ccs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] e])
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
  then show ?case using d sim' produces_next[OF pr m] wf cse be f
    by (auto intro!: dsim.DsExists)
next
  case (DsOr n cs \<phi> \<psi> buf \<phi>d \<psi>d dbuf)
  note wf = DsOr.hyps(1) and pr = DsOr.hyps(2) and sim1 = DsOr.hyps(3) and IH1 = DsOr.hyps(4)
    and sim2 = DsOr.hyps(5) and IH2 = DsOr.hyps(6) and bf = DsOr.hyps(7) and m = DsOr.prems
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MOr \<phi>2 \<psi>2 buf2" using m e1 e2 e3 by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs) as, \<phi>d2)"
    and s1: "dsim n cs \<phi>d2 \<phi>2" using IH1[OF e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs \<psi>d2 \<psi>2" using IH2[OF e2] by blast
  have ta: "list_all (ftable n (set cs)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] e2])
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
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr m] wf x f
    by (auto intro!: dsim.DsOr)
next
  case (DsAnd n cs cs1 \<phi> pos cs2 \<psi> buf \<phi>d \<psi>d pl dbuf)
  note wf = DsAnd.hyps(1) and pr = DsAnd.hyps(2) and sim1 = DsAnd.hyps(3)
    and IH1 = DsAnd.hyps(4) and sim2 = DsAnd.hyps(5) and IH2 = DsAnd.hyps(6)
    and cse = DsAnd.hyps(7) and ple = DsAnd.hyps(8) and neg = DsAnd.hyps(9)
    and bf = DsAnd.hyps(10) and m = DsAnd.prems
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. bin_join n (set cs1) r1 pos (set cs2) r2)
        (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. bin_join n (set cs1) r1 pos (set cs2) r2)
        (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MAnd (set cs1) \<phi>2 pos (set cs2) \<psi>2 buf2"
    using m e1 e2 e3 by simp_all
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs1) as, \<phi>d2)"
    and s1: "dsim n cs1 \<phi>d2 \<phi>2" using IH1[OF e1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs2) bs, \<psi>d2)"
    and s2: "dsim n cs2 \<psi>d2 \<psi>2" using IH2[OF e2] by blast
  have so1: "sorted_wrt (<) cs1" and b1: "\<forall>c \<in> set cs1. c < n"
    using dsim_wf_cols[OF sim1] by (blast dest: conjunct1 conjunct2)+
  have so2: "sorted_wrt (<) cs2" and b2: "\<forall>c \<in> set cs2. c < n"
    using dsim_wf_cols[OF sim2] by (blast dest: conjunct1 conjunct2)+
  have ta: "list_all (ftable n (set cs1)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] e1])
  have tb: "list_all (ftable n (set cs2)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] e2])
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
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr m] wf cse ple neg x f
    by (auto intro!: dsim.DsAnd)
next
  case (DsAgg n cs args \<phi> gcols \<phi>d y)
  note wf = DsAgg.hyps(1) and pr = DsAgg.hyps(2) and sim = DsAgg.hyps(3) and IH = DsAgg.hyps(4)
    and wg = DsAgg.hyps(5) and ne = DsAgg.hyps(6) and ye = DsAgg.hyps(7) and yn = DsAgg.hyps(8)
    and yg = DsAgg.hyps(9) and g0 = DsAgg.hyps(10) and fv = DsAgg.hyps(11)
    and cse = DsAgg.hyps(12) and m = DsAgg.prems
  let ?mm = "length (aggargs_tys args)"
  let ?cc = "agg_cols ?mm gcols"
  obtain ys \<psi>' where e: "meval j (?mm + n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (?mm + n) ts db \<phi>")
  have x: "xs = map (eval_aggargs args) ys" and f: "\<phi>' = mformula.MAgg args \<psi>'"
    using m e by simp_all
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (?mm + n) ?cc) ys, \<psi>d')"
    and sim': "dsim (?mm + n) ?cc \<psi>d' \<psi>'" using IH[OF e] by blast
  have t: "list_all (ftable (?mm + n) (set ?cc)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] e])
  have "map (dagg (aggargs_g0 args) (aggargs_\<omega> args) (reindex_trm ?cc (aggargs_f args)) ?mm
          (ins_pos gcols y)) (map (dtabc (?mm + n) ?cc) ys) = map (dtabc n cs) xs"
    unfolding x cse using t wg yn yg fv g0 ne ye
    by (intro nth_equalityI)
      (auto simp: list_all_iff eval_aggargs_def dagg_eval_agg)
  then show ?case using d sim' produces_next[OF pr m] wf wg ne ye yn yg g0 fv cse f
    by (auto intro!: dsim.DsAgg)
qed

(*<*)
end
(*>*)
