(*<*)
theory Dense_Eval
  imports Dense_Evt_Aux Dense_Trigger_Nar
begin
(*>*)

section \<open>The dense evaluator simulates the kernel's\<close>

text \<open>
  Every theorem of @{theory MFODL_Monitor_Dense.Dense} needs its operand tables to be finite and
  well formed over the node's columns.  That is not a property of a single call but of a
  formula's whole future, so it is stated coinductively: @{term "produces n A tw \<phi>"} says that
  @{const meval} on @{term \<phi>} only ever yields finite tables over @{term A}, and that its
  successors do the same.  The kernel's own well-formedness invariant implies it, which is
  where -- and the only place where -- this development touches the kernel's correctness proof.
\<close>

text \<open>
  A database is well formed when the table stored at a name of arity @{term ar} holds tuples of
  that width with no holes -- which is what the trace's own databases look like.  The dense
  formula's predicate nodes read the database at the width the name was declared with, so this is
  exactly the condition they need.  The tables are also required to be finite: the dense
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

text \<open>A let-bound formula has every column of its own frame live, so the tables it binds into
  the database are exactly what a well-formed database holds -- which is what makes the dense
  let need no conversion at the binding at all.\<close>

lemma wf_db_map_values_empty: "wf_db (Mapping.map_values (\<lambda>_ _. []) db)"
  by (auto simp: wf_db_def Mapping.lookup_map_values split: option.splits)

lemma wf_db_update':
  "wf_db db \<Longrightarrow> list_all (\<lambda>T. table (snd q) {0..<snd q} T \<and> finite T) xs \<Longrightarrow>
     wf_db (Mapping.update q xs db)"
  by (auto simp: wf_db_def lookup_update' split: if_splits)

definition dnext :: "ts \<Rightarrow> ts list \<Rightarrow> ts" where
  "dnext tw ts = (if ts = [] then tw else last ts)"

lemma dnext_ge: "\<forall>t \<in> set ts. tw \<le> t \<Longrightarrow> tw \<le> dnext tw ts"
  by (auto simp: dnext_def)

lemma dnext_bound: "sorted ts \<Longrightarrow> \<forall>t \<in> set ts. t \<le> dnext tw ts"
proof (induct ts rule: rev_induct)
  case (snoc a ts) then show ?case by (auto simp: dnext_def sorted_append)
qed (simp add: dnext_def)

text \<open>
  The invariant also carries a timestamp lower bound: @{term "produces n A tw \<phi>"} may assume
  that every timestamp in the batch is at least @{term tw}, and re-establishes itself at the
  bound @{term "dnext tw ts"} the batch leaves behind.  The temporal nodes need this -- the
  verified Since and Until structures accept a new timestamp only at or after the one they are
  already at -- and the others carry it without using it.
\<close>

coinductive produces :: "nat \<Rightarrow> nat set \<Rightarrow> ts \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool"
  where produces: "(\<And>j ts db xs \<phi>'. wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
      (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable n A) xs \<and> produces n A (dnext tw ts) \<phi>') \<Longrightarrow> produces n A tw \<phi>"

lemma produces_step:
  "produces n A tw \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow>
     meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
     list_all (ftable n A) xs \<and> produces n A (dnext tw ts) \<phi>'"
  by (erule produces.cases) blast

lemma produces_tables:
  "produces n A tw \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow>
     meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> list_all (ftable n A) xs"
  by (drule produces_step) auto

lemma produces_next:
  "produces n A tw \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow>
     meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> produces n A (dnext tw ts) \<phi>'"
  by (drule produces_step) auto

section \<open>The dense formula\<close>

text \<open>
  A dense formula mirrors the kernel's @{typ "('msaux, 'muaux, 'mtaux) mformula"} node by node,
  but every node carries the data the short representation needs instead of the data the wide
  one needs: a join plan instead of two variable sets, a term already reindexed against the
  operand's column list, a mask at the boundary.  @{term DFail} stands for a node the dense
  fragment does not cover: it evaluates to nothing and no simulation rule relates it to a kernel
  formula, so a dense formula containing one proves nothing and the compiler's caller must check
  that it produced none.  Nothing in the type mentions the kernel's formula type, which is what
  makes the dense evaluator exportable on its own.
\<close>

datatype dformula =
    DFail
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
  | DSince args dformula dformula "event_data mbuf2S" dsaux_x
  | DUntil args "bool list" dformula dformula "event_data mbuf2" "ts list" ts
      duaux_x
  | DAndAssign nat Formula.trm dformula
  | DTP mtrm nat
  | DTS mtrm
  | DLet Formula.name nat dformula dformula
  | DFrz Formula.name nat dformula dformula nat nat nat "event_data table list"
  | DLetPast Formula.name nat dformula dformula nat "event_data table option"
  | DTrigger args "nat option list" dformula dformula "event_data mbuf2" "ts list"
      "event_data option gmmtaux"
  | DAndTrigger djoin_plan dformula "event_data table list \<times> event_data table option list"
      args dformula dformula "event_data mbuf2" "ts list" "event_data option gmmtaux"
  | DMatchP nat \<I> mregex "mregex list" "nat option list list" "dformula list"
      "event_data mbufn" "ts list" "event_data mr\<delta>aux"
  | DMatchF nat \<I> mregex "mregex list" "nat option list list" "dformula list"
      "event_data mbufn" "ts list" ts "event_data ml\<delta>aux"

text \<open>The compiler is total on the kernel's formulas, so it answers @{const DFail} at a node it
  does not cover rather than failing.  Its caller checks that the compiled formula has none: this
  counts them.\<close>

fun vdfail_nodes :: "dformula \<Rightarrow> nat" where
  "vdfail_nodes DFail = 1"
| "vdfail_nodes (DAndRel \<phi> conf) = vdfail_nodes \<phi>"
| "vdfail_nodes (DNeg \<phi>) = vdfail_nodes \<phi>"
| "vdfail_nodes (DExists \<phi> b) = vdfail_nodes \<phi>"
| "vdfail_nodes (DAgg g0 \<omega> f k pos \<phi>) = vdfail_nodes \<phi>"
| "vdfail_nodes (DOr \<phi> \<psi> buf) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DAnd pl \<phi> pos \<psi> buf) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DPrev I \<phi> f buf nts) = vdfail_nodes \<phi>"
| "vdfail_nodes (DNext I \<phi> f nts) = vdfail_nodes \<phi>"
| "vdfail_nodes (DAnds ps ns L buf) = sum_list (map vdfail_nodes L)"
| "vdfail_nodes (DSince args \<phi> \<psi> buf aux) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DUntil args msk \<phi> \<psi> buf nts t aux) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DAndAssign p t \<phi>) = vdfail_nodes \<phi>"
| "vdfail_nodes (DLet p m \<phi> \<psi>) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DLetPast p m \<phi> \<psi> i buf) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DTrigger dags pl \<phi> \<psi> dbuf nts daux) = vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> dbuf2 nts daux) =
     vdfail_nodes \<alpha> + vdfail_nodes \<phi> + vdfail_nodes \<psi>"
| "vdfail_nodes (DMatchP m I mr mrs pls L dbuf nts daux) = sum_list (map vdfail_nodes L)"
| "vdfail_nodes (DMatchF m I mr mrs pls L dbuf nts t daux) = sum_list (map vdfail_nodes L)"
| "vdfail_nodes \<phi> = 0"

function (sequential) deval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> dformula \<Rightarrow>
    event_data table list \<times> dformula" where
  "deval j ts db DFail = ([], DFail)"
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
      in (map (Set.filter (deval_constraint conf)) xs, DAndRel \<phi>' conf))"
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
     (let R = map (deval j ts db) Ld;
          (zs, dbuf') = mbufn_take (\<lambda>as zs. zs @ [dmulti_join ps ns as]) []
            (mbufn_add (map fst R) dbuf)
      in (zs, DAnds ps ns (map snd R) dbuf'))"
| "deval j ts db (DSince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          (zs, buf', aux') = dsx_eval_since dags [] (mbuf2S_add xs ys ts buf) aux
      in (zs, DSince dags \<phi>' \<psi>' buf' aux'))"
| "deval j ts db (DUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          (aux', buf', nt, nts') = mbuf2t_take (dux_add_new dags msk) aux
            (mbuf2_add xs ys buf) t (nts @ ts);
          (zs, aux'') = dux_eval dags nt aux'
      in (zs, DUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "deval j ts db (DAndAssign p t \<phi>) =
     (let (xs, \<phi>') = deval j ts db \<phi> in (map (dassign p t) xs, DAndAssign p t \<phi>'))"
| "deval j ts db (DTP mt i) =
     (map (\<lambda>x. dmtrm mt (EInt (integer_of_nat x))) [i..<j], DTP mt j)"
| "deval j ts db (DTS mt) = (map (\<lambda>x. dmtrm mt (EInt (integer_of_nat x))) ts, DTS mt)"
| "deval j ts db (DLet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = deval j ts db \<phi>;
          (ys, \<psi>') = deval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, DLet p m \<phi>' \<psi>'))"
| "deval j ts db (DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) =
     (let (xs, \<phi>) = deval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = deval j ts db0 \<psi>;
          zs0_out = drop (jfrz - jpsi0) zs0;
          jpsi0 = jpsi0 + length zs0;
          \<alpha>s = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs);
          (ys, \<alpha>s') = freeze_meval0 (\<lambda>\<alpha>. deval j []
            (Mapping.update (p, m) (replicate j \<alpha>)
              (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>) (jfrz - jpsi0) \<alpha>s;
          jphi = jphi + length xs;
          jfrz = jfrz + length zs0_out + length ys
      in (zs0_out @ ys, DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s'))"
| "deval j ts db (DLetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
          (ys, \<psi>) = deval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, DLetPast p m \<phi> \<psi> i buf))"
| "deval j ts db (DTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (zs @ [dsan (gresult_mmtaux dags ax)], ax)) ([], daux)
            (mbuf2_add xs ys dbuf) (nts @ ts)
      in (zs, DTrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "deval j ts db (DAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> dbuf2 nts daux) =
     (let (as, \<alpha>') = deval j ts db \<alpha>; (xs, \<phi>') = deval j ts db \<phi>;
          (ys, \<psi>') = deval j ts db \<psi>;
          ((ws, daux'), dbuf2', nts') = mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (ws @ [if gmmtaux_empty ax then None
                      else Some (dsan (gresult_mmtaux dags ax))], ax)) ([], daux)
            (mbuf2_add xs ys dbuf2) (nts @ ts);
          (zs, dbuf1') = mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> dbin_join pl r1 True z) (mbuf2_add as ws dbuf1)
      in (zs, DAndTrigger pl \<alpha>' dbuf1' dags \<phi>' \<psi>' dbuf2' nts' daux'))"
| "deval j ts db (DMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (deval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mbufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = update_matchP m I mr mrs (map2 dembedp pls rels) t ax
             in (zs @ [z], ax)) ([], daux) (mbufn_add (map fst R) dbuf) 0 (nts @ ts)
      in (map dsan zs, DMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "deval j ts db (DMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (deval j ts db) Ld;
          (daux', dbuf', nt, nts') = mbufnt_take
             (\<lambda>rels. update_matchF m I mr mrs (map2 dembedp pls rels))
             daux (mbufn_add (map fst R) dbuf) t (nts @ ts);
          (zs, daux'') = eval_matchF I mr nt daux'
      in (map dsan zs, DMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
  by pat_completeness auto

text \<open>The freeze node re-enters the evaluator on its body's \<^emph>\<open>updated\<close> state, which is
  not a subterm of the node, so the recursion is not structural and termination goes by the
  formula's size -- exactly as the kernel's own evaluator does it.  Evaluation preserves that
  size, which is the fact that makes the measure decrease.\<close>

lemma psize_snd_deval:
  "deval_dom (j, ts, db, \<phi>) \<Longrightarrow> size (snd (deval j ts db \<phi>)) = size \<phi>"
  apply (induct rule: deval.pinduct)
  apply (auto simp only: prod.inject deval.psimps Let_def snd_conv fst_conv
      dformula.size list.map map_map o_apply size_list_map cong: size_list_cong
      split: prod.splits)
   apply simp
  apply (metis snd_conv size_letpast_meval)
  done

lemma total_deval: "All deval_dom"
  by (relation "measure (\<lambda>(j, ts, db, \<phi>). size \<phi>)")
    (auto simp: termination_simp dest!: psize_snd_deval dest: sym)

lemmas size_snd_deval = psize_snd_deval[OF total_deval[THEN spec]]

termination deval by (rule total_deval)

text \<open>The freeze's own recursion is polymorphic in the evaluator and in the state it discards,
  so the dense side reuses @{const freeze_meval0} itself; all that is needed is that the two
  runs take the same branches, which they do because narrowing a list preserves its length.\<close>

lemma freeze_meval0_sub: "freeze_meval0 ev k \<alpha>s = (ys, \<alpha>s') \<Longrightarrow> set \<alpha>s' \<subseteq> set \<alpha>s"
proof (induct ev k \<alpha>s arbitrary: ys \<alpha>s' rule: freeze_meval0.induct)
  case (2 ev k \<alpha> r)
  note IH = 2(1) and E = 2(2)
  obtain zs st where ev: "ev \<alpha> = (zs, st)" by (cases "ev \<alpha>")
  show ?case
  proof (cases "drop k zs")
    case Nil
    then show ?thesis using E ev by simp
  next
    case (Cons y rr)
    obtain ws \<beta>s where e2: "freeze_meval0 ev (Suc k) r = (ws, \<beta>s)"
      by (cases "freeze_meval0 ev (Suc k) r")
    have "set \<beta>s \<subseteq> set r" by (rule IH[OF ev[symmetric] refl Cons e2])
    moreover have "\<alpha>s' = \<beta>s" using E ev Cons e2 by auto
    ultimately show ?thesis by auto
  qed
qed simp

lemma freeze_meval0_rel:
  "freeze_meval0 ev k \<alpha>s = (ys, \<alpha>s') \<Longrightarrow> freeze_meval0 dv k \<alpha>s = (dys, d\<alpha>s') \<Longrightarrow>
   (\<And>\<alpha>. \<alpha> \<in> set \<alpha>s \<Longrightarrow> fst (dv \<alpha>) = map (dtabc n cs) (fst (ev \<alpha>))) \<Longrightarrow>
   dys = map (dtabc n cs) ys \<and> d\<alpha>s' = \<alpha>s'"
proof (induct \<alpha>s arbitrary: k ys \<alpha>s' dys d\<alpha>s')
  case Nil
  then show ?case by simp
next
  case (Cons \<alpha> r)
  note IH = Cons(1) and E = Cons(2) and D = Cons(3) and AG = Cons(4)
  obtain zs st where ev: "ev \<alpha> = (zs, st)" by (cases "ev \<alpha>")
  obtain dzs dst where dv: "dv \<alpha> = (dzs, dst)" by (cases "dv \<alpha>")
  have dz: "dzs = map (dtabc n cs) zs" using AG[of \<alpha>] ev dv by simp
  show ?case
  proof (cases "drop k zs")
    case Nil
    then have dn: "drop k dzs = []" unfolding dz by (simp add: drop_map)
    have "ys = []" and "\<alpha>s' = \<alpha> # r" using E ev Nil by auto
    moreover have "dys = []" and "d\<alpha>s' = \<alpha> # r" using D dv dn by auto
    ultimately show ?thesis by simp
  next
    case (Cons y rr)
    obtain ws \<beta>s where e2: "freeze_meval0 ev (Suc k) r = (ws, \<beta>s)"
      by (cases "freeze_meval0 ev (Suc k) r")
    obtain dws d\<beta>s where d2: "freeze_meval0 dv (Suc k) r = (dws, d\<beta>s)"
      by (cases "freeze_meval0 dv (Suc k) r")
    have rel: "dws = map (dtabc n cs) ws \<and> d\<beta>s = \<beta>s"
      by (rule IH[OF e2 d2]) (use AG in auto)
    have dd: "drop k dzs = dtabc n cs y # map (dtabc n cs) rr"
      unfolding dz using Cons by (simp add: drop_map)
    have y1: "ys = y # ws" and y2: "\<alpha>s' = \<beta>s" using E ev Cons e2 by auto
    have y3: "dys = dtabc n cs y # dws" and y4: "d\<alpha>s' = d\<beta>s"
      using D dv dd d2 by auto
    show ?thesis using rel y1 y2 y3 y4 by simp
  qed
qed

section \<open>The simulation relation\<close>

text \<open>
  @{term "dsim n cs \<phi>d \<phi>"} relates a dense formula to a kernel one at a frame of width
  @{term n} whose live columns are @{term cs}.  Every rule carries the node's own
  @{const produces}, so the relation alone gives the operand well-formedness that the
  @{theory MFODL_Monitor_Dense.Dense} theorems ask for, at every node and after every step.
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

subsection \<open>The aggregation at a structure's output\<close>

text \<open>
  The kernel fuses an aggregation into the Since and the Until: the structure is stepped at the
  operand's frame and the aggregation is applied to whatever it reports.  The dense side runs the
  structure without one -- @{const dargs} clears the field -- and applies the dense aggregation
  afterwards, so the two output lists are not narrowings of each other but two images of one list
  of windows.  That is what the relation below says.  With no aggregation it degenerates to the
  narrowing, which is what the unfused nodes use.
\<close>

definition dsres :: "nat \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> event_data table list \<Rightarrow> event_data table list \<Rightarrow> bool"
  where "dsres n cs args zs dzs \<longleftrightarrow> (\<exists>ws. list_all (table n (set cs)) ws \<and>
     zs = map (eval_args_agg args) ws \<and> dzs = map (dtabc n cs) ws)"

lemma dsres_Nil[simp]: "dsres n cs args [] []"
  unfolding dsres_def by (intro exI[of _ "[]"]) simp

lemma dsres_Cons:
  assumes w: "table n (set cs) w" and r: "dsres n cs args zs dzs"
  shows "dsres n cs args (eval_args_agg args w # zs) (dtabc n cs w # dzs)"
proof -
  obtain ws where ws: "list_all (table n (set cs)) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (dtabc n cs) ws" using r unfolding dsres_def by blast
  show ?thesis unfolding dsres_def by (intro exI[of _ "w # ws"]) (use w ws in simp)
qed

lemma dsres_append:
  assumes a: "dsres n cs args zs dzs" and b: "dsres n cs args us dus"
  shows "dsres n cs args (zs @ us) (dzs @ dus)"
proof -
  obtain ws where ws: "list_all (table n (set cs)) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (dtabc n cs) ws" using a unfolding dsres_def by blast
  obtain vs where vs: "list_all (table n (set cs)) vs" "us = map (eval_args_agg args) vs"
    "dus = map (dtabc n cs) vs" using b unfolding dsres_def by blast
  show ?thesis unfolding dsres_def
    by (intro exI[of _ "ws @ vs"]) (use ws vs in simp)
qed

lemma dsres_rev:
  assumes "dsres n cs args zs dzs"
  shows "dsres n cs args (rev zs) (rev dzs)"
proof -
  obtain ws where ws: "list_all (table n (set cs)) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (dtabc n cs) ws" using assms unfolding dsres_def by blast
  show ?thesis unfolding dsres_def
    by (intro exI[of _ "rev ws"]) (use ws in \<open>simp add: rev_map list_all_iff\<close>)
qed

lemma dsres_rev':
  "rev zs = us \<Longrightarrow> rev dzs = dus \<Longrightarrow> dsres n cs args zs dzs \<Longrightarrow> dsres n cs args us dus"
  using dsres_rev by blast

lemma dsres_none:
  assumes "args_agg args = None" and "dsres n cs args zs dzs"
  shows "dzs = map (dtabc n cs) zs"
  using assms unfolding dsres_def eval_args_agg_def by auto

text \<open>The window a firing reports is a union of the auxiliary list's tables, so it is a table over
  the node's columns; the kernel's structure reports its aggregation and the dense one reports its
  narrowing -- or, for the window with the aggregate fused in, the dense aggregation of its
  narrowing.  The relation below carries that post-function; @{const dsres} is its identity
  instance.\<close>

definition dsresh :: "nat \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> (event_data table \<Rightarrow> event_data table) \<Rightarrow>
    event_data table list \<Rightarrow> event_data table list \<Rightarrow> bool"
  where "dsresh n cs args h zs dzs \<longleftrightarrow> (\<exists>ws. list_all (table n (set cs)) ws \<and>
     zs = map (eval_args_agg args) ws \<and> dzs = map (h \<circ> dtabc n cs) ws)"

lemma dsresh_id: "dsresh n cs args id zs dzs \<longleftrightarrow> dsres n cs args zs dzs"
  unfolding dsresh_def dsres_def by simp

lemma dsresh_Nil[simp]: "dsresh n cs args h [] []"
  unfolding dsresh_def by (intro exI[of _ "[]"]) simp

lemma dsresh_Cons:
  assumes w: "table n (set cs) w" and r: "dsresh n cs args h zs dzs"
  shows "dsresh n cs args h (eval_args_agg args w # zs) (h (dtabc n cs w) # dzs)"
proof -
  obtain ws where ws: "list_all (table n (set cs)) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> dtabc n cs) ws" using r unfolding dsresh_def by blast
  show ?thesis unfolding dsresh_def by (intro exI[of _ "w # ws"]) (use w ws in simp)
qed

lemma dsresh_append:
  assumes a: "dsresh n cs args h zs dzs" and b: "dsresh n cs args h us dus"
  shows "dsresh n cs args h (zs @ us) (dzs @ dus)"
proof -
  obtain ws where ws: "list_all (table n (set cs)) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> dtabc n cs) ws" using a unfolding dsresh_def by blast
  obtain vs where vs: "list_all (table n (set cs)) vs" "us = map (eval_args_agg args) vs"
    "dus = map (h \<circ> dtabc n cs) vs" using b unfolding dsresh_def by blast
  show ?thesis unfolding dsresh_def
    by (intro exI[of _ "ws @ vs"]) (use ws vs in simp)
qed

lemma dsresh_rev:
  assumes "dsresh n cs args h zs dzs"
  shows "dsresh n cs args h (rev zs) (rev dzs)"
proof -
  obtain ws where ws: "list_all (table n (set cs)) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> dtabc n cs) ws" using assms unfolding dsresh_def by blast
  show ?thesis unfolding dsresh_def
    by (intro exI[of _ "rev ws"]) (use ws in \<open>simp add: rev_map\<close>)
qed

lemma dsresh_rev':
  "rev zs = us \<Longrightarrow> rev dzs = dus \<Longrightarrow> dsresh n cs args h zs dzs \<Longrightarrow> dsresh n cs args h us dus"
  using dsresh_rev by blast

lemma table_foldr_Un: "list_all (table n A) ws \<Longrightarrow> table n A (foldr (\<union>) ws {})"
  by (induct ws) (auto simp: table_def)

lemma dsresh_result:
  assumes vd: "dsxaux' n cs_R cs_L args cur da al"
    and vw: "valid_mmasaux args cur wa al"
  shows "dsresh n cs_R args (dsx_post da) [result_mmasaux args wa] [dsx_result (dargs cs_R cs_L args) da]"
proof -
  let ?W = "foldr (\<union>) [rel. (t, rel) \<leftarrow> al, memL (args_ivl args) (cur - t)] {}"
  have tw: "table n (set cs_R) ?W"
    by (rule table_foldr_Un) (use dsxaux'_tables[OF vd] in \<open>auto simp: list_all_iff\<close>)
  have e: "result_mmasaux args wa = eval_args_agg args ?W"
    by (rule default_mmasaux.valid_result_msaux[OF vw])
  have d: "dsx_result (dargs cs_R cs_L args) da = dsx_post da (dtabc n cs_R ?W)"
    by (rule dsxaux'_result[OF vd])
  show ?thesis unfolding e d by (rule dsresh_Cons[OF tw dsresh_Nil])
qed

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
    mmasaux \<Rightarrow> dsaux_x \<Rightarrow> event_data mbuf2S \<Rightarrow> event_data mbuf2S \<Rightarrow> bool" where
  "dsince_rel n cs_R cs_L args tw aux daux buf dbuf \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmasaux args cur aux auxlist \<and>
        dsxaux' n cs_R cs_L args cur daux auxlist \<and> cur \<le> tw \<and>
        (case buf of (xs, ys, tss, sk) \<Rightarrow>
           list_all (ftable n (set cs_L)) xs \<and> list_all (ftable n (set cs_R)) ys \<and>
           sorted tss \<and> (\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw) \<and>
           dbuf = (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys, tss, sk)))"

lemma dsince_relI:
  "valid_mmasaux args cur aux auxlist \<Longrightarrow> dsxaux' n cs_R cs_L args cur daux auxlist \<Longrightarrow>
   cur \<le> tw \<Longrightarrow>
   list_all (ftable n (set cs_L)) xs \<Longrightarrow> list_all (ftable n (set cs_R)) ys \<Longrightarrow>
   sorted tss \<Longrightarrow> \<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw \<Longrightarrow>
   dsince_rel n cs_R cs_L args tw aux daux (xs, ys, tss, sk)
     (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys, tss, sk)"
  unfolding dsince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma dsince_relE:
  assumes "dsince_rel n cs_R cs_L args tw aux daux (xs, ys, tss, sk) dbuf"
  obtains cur auxlist where "valid_mmasaux args cur aux auxlist"
    and "dsxaux' n cs_R cs_L args cur daux auxlist" and "cur \<le> tw"
    and "list_all (ftable n (set cs_L)) xs" and "list_all (ftable n (set cs_R)) ys"
    and "sorted tss" and "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and "dbuf = (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys, tss, sk)"
  using assms unfolding dsince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma dsince_relD_buf:
  "dsince_rel n cs_R cs_L args tw aux daux buf dbuf \<Longrightarrow>
     dbuf = (map (dtabc n cs_L) (fst buf), map (dtabc n cs_R) (fst (snd buf)),
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
     (mbuf2S_add (map (dtabc n cs_L) xs) (map (dtabc n cs_R) ys) ts dbuf)"
proof (cases buf)
  case (fields us vs tss sk)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' n cs_R cs_L args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable n (set cs_L)) us" and lv: "list_all (ftable n (set cs_R)) vs"
    and st: "sorted tss" and ct: "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_L) us, map (dtabc n cs_R) vs, tss, sk)"
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
    muaux_dq \<Rightarrow> duaux_x \<Rightarrow> bool" where
  "duaux_rel n cs_R cs_L args cur aux daux \<longleftrightarrow>
     (\<exists>auxlist. valid_muaux_dq args cur aux auxlist \<and>
        duxaux' n cs_R cs_L args cur daux auxlist)"

lemma duaux_rel_step:
  assumes v: "duaux_rel n cs_R cs_L args u aux daux"
    and sR: "sorted_wrt (<) cs_R" and sL: "sorted_wrt (<) cs_L"
    and bR: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
    and t1: "table n (set cs_L) a" and t2: "table n (set cs_R) b" and f2: "finite b"
    and ut: "u \<le> t"
  shows "duaux_rel n cs_R cs_L args t (add_new_muaux_dq args a b t aux)
     (dux_add_new (dargs cs_R cs_L args) (dmsk cs_R cs_L)
       (dtabc n cs_L a) (dtabc n cs_R b) t daux)"
proof -
  obtain auxlist where vw: "valid_muaux_dq args u aux auxlist"
    and vd: "duxaux' n cs_R cs_L args u daux auxlist"
    using v unfolding duaux_rel_def by blast
  have "valid_muaux_dq args t (add_new_muaux_dq args a b t aux) (update_until args a b t auxlist)"
    by (rule valid_add_new_muaux_dq[OF vw _ _ ut]) (use t1 t2 an aL aR in simp_all)
  moreover have "duxaux' n cs_R cs_L args t
      (dux_add_new (dargs cs_R cs_L args) (dmsk cs_R cs_L)
        (dtabc n cs_L a) (dtabc n cs_R b) t daux)
      (update_until args a b t auxlist)"
    by (rule duxaux'_add_new[OF vd sR sL bR sub t1 t2 f2 ut])
  ultimately show ?thesis unfolding duaux_rel_def by blast
qed

lemma dux_agg_mbuf2t_take:
  "mbuf2t_take (dux_add_new args msk) daux buf t nts = (daux', buf', t', nts') \<Longrightarrow>
   dux_agg daux' = dux_agg daux"
  by (induction "dux_add_new args msk" daux buf t nts arbitrary: daux' buf' t' nts'
      rule: mbuf2t_take.induct) (auto split: if_splits prod.splits)

lemma dux_post_mbuf2t_take:
  "mbuf2t_take (dux_add_new args msk) daux buf t nts = (daux', buf', t', nts') \<Longrightarrow>
   dux_post daux' = dux_post daux"
  using dux_agg_mbuf2t_take by (simp add: dux_post_eq)

lemma duaux_rel_eval:
  assumes v: "duaux_rel n cs_R cs_L args cur aux daux" and nt: "cur \<le> nt"
    and we: "eval_muaux_dq args nt aux = (zs, aux')"
    and de: "dux_eval (dargs cs_R cs_L args) nt daux = (dzs, daux')"
  shows "dsresh n cs_R args (dux_post daux) zs dzs \<and>
    duaux_rel n cs_R cs_L args cur aux' daux'"
proof -
  obtain auxlist where vw: "valid_muaux_dq args cur aux auxlist"
    and vd: "duxaux' n cs_R cs_L args cur daux auxlist"
    using v unfolding duaux_rel_def by blast
  obtain res auxlist' where eu: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
    by (cases "eval_until (args_ivl args) nt auxlist")
  have w: "valid_muaux_dq args cur aux' auxlist' \<and> zs = map (eval_args_agg args) res"
    by (rule valid_eval_muaux_dq[OF vw nt we eu])
  have d: "dzs = map (dux_post daux \<circ> dtabc n cs_R) res \<and>
      duxaux' n cs_R cs_L args cur daux' auxlist'"
    by (rule duxaux'_eval[OF vd nt de eu])
  have tr: "list_all (table n (set cs_R)) res"
  proof (unfold list_all_iff, safe)
    fix x assume "x \<in> set res"
    then obtain t a1 where "(t, a1, x) \<in> set auxlist"
      unfolding eval_until_res[OF eu] by (auto dest!: set_takeWhileD)
    then show "table n (set cs_R) x" using duxaux'_tables[OF vd] by auto
  qed
  show ?thesis using w d tr unfolding duaux_rel_def dsresh_def by blast
qed

text \<open>The node relation.  The stored timestamp is at or after the structure's current one and
  at or before the bound, and so is every timestamp still queued.\<close>

definition duntil_rel :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> duaux_x \<Rightarrow> event_data mbuf2 \<Rightarrow> event_data mbuf2 \<Rightarrow>
    ts list \<Rightarrow> bool" where
  "duntil_rel n cs_R cs_L args tw t aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur. duaux_rel n cs_R cs_L args cur aux daux \<and> cur \<le> t \<and> t \<le> tw \<and>
        list_all (ftable n (set cs_L)) (fst buf) \<and>
        list_all (ftable n (set cs_R)) (snd buf) \<and>
        dbuf = (map (dtabc n cs_L) (fst buf), map (dtabc n cs_R) (snd buf)) \<and>
        sorted nts \<and> (\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw))"

text \<open>
  One firing of the Until node: the buffer traversal steps the two structures in lockstep, and
  then one evaluation at the timestamp the traversal reports yields the narrowing of what the wide
  one yields.
\<close>

lemma until_step_rel:
  assumes sR: "sorted_wrt (<) cs_R" and sL: "sorted_wrt (<) cs_L"
    and bR: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
    and rel: "duntil_rel n cs_R cs_L args tw t aux daux buf dbuf nts"
    and ta: "list_all (ftable n (set cs_L)) as" and tb: "list_all (ftable n (set cs_R)) bs"
    and s: "sorted tss" and bnd: "\<forall>u \<in> set tss. tw \<le> u"
    and we: "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ tss)
      = (aux1, buf1, nt, nts1)"
    and de: "mbuf2t_take (dux_add_new (dargs cs_R cs_L args) (dmsk cs_R cs_L)) daux
      (mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs_R) bs) dbuf) t (nts @ tss)
      = (daux1, dbuf1, dnt, dnts1)"
    and wev: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    and dev: "dux_eval (dargs cs_R cs_L args) dnt daux1 = (dzs, daux2)"
  shows "dsresh n cs_R args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
     dbuf1 = (map (dtabc n cs_L) (fst buf1), map (dtabc n cs_R) (snd buf1)) \<and>
     duntil_rel n cs_R cs_L args (dnext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
proof -
  obtain cur where vr: "duaux_rel n cs_R cs_L args cur aux daux"
    and ct: "cur \<le> t" and ttw: "t \<le> tw"
    and lu: "list_all (ftable n (set cs_L)) (fst buf)"
    and lv: "list_all (ftable n (set cs_R)) (snd buf)"
    and dbe: "dbuf = (map (dtabc n cs_L) (fst buf), map (dtabc n cs_R) (snd buf))"
    and sn: "sorted nts" and cn: "\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw"
    using rel unfolding duntil_rel_def by blast
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mda: "mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs_R) bs) dbuf
      = (map (dtabc n cs_L) us, map (dtabc n cs_R) vs)"
    unfolding dbe us_def vs_def by (cases buf) simp
  have lus: "list_all (ftable n (set cs_L)) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable n (set cs_R)) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a b t' u z z'. a \<in> set us \<Longrightarrow> b \<in> set vs \<Longrightarrow>
      duaux_rel n cs_R cs_L args u z z' \<Longrightarrow> u \<le> t' \<Longrightarrow>
      duaux_rel n cs_R cs_L args t' (add_new_muaux_dq args a b t' z)
        (dux_add_new (dargs cs_R cs_L args) (dmsk cs_R cs_L)
          (dtabc n cs_L a) (dtabc n cs_R b) t' z')"
    using lus lvs by (intro duaux_rel_step[OF _ sR sL bR sub an aL aR]) (auto simp: list_all_iff)
  have sts: "sorted (nts @ tss)"
    using sn s cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>u \<in> set (nts @ tss). cur \<le> u" using cn bnd ct ttw by fastforce
  have tdn: "t \<le> dnext tw tss" using ttw dnext_ge[OF bnd] by simp
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext tw tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF s] by fastforce
  have we': "mbuf2t_take (add_new_muaux_dq args) aux (us, vs) t (nts @ tss)
      = (aux1, (b1, b2), nt, nts1)" using we unfolding ma bfs by simp
  have de': "mbuf2t_take (dux_add_new (dargs cs_R cs_L args) (dmsk cs_R cs_L)) daux
      (map (dtabc n cs_L) us, map (dtabc n cs_R) vs) t (nts @ tss) = (daux1, dbuf1, dnt, dnts1)"
    using de unfolding mda by simp
  have R: "(\<exists>u. duaux_rel n cs_R cs_L args u aux1 daux1 \<and> u \<le> nt \<and>
        (\<forall>v \<in> set nts1. u \<le> v)) \<and> sorted nts1 \<and>
      (nt = t \<or> nt \<in> set (nts @ tss)) \<and> set nts1 \<subseteq> set (nts @ tss) \<and>
      dbuf1 = (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2) \<and> dnt = nt \<and> dnts1 = nts1"
    by (rule mbuf2t_take_rel_ts[OF step vr ct sts cts we' de'])
  obtain u where vu: "duaux_rel n cs_R cs_L args u aux1 daux1" and unt: "u \<le> nt"
    and un: "\<forall>v \<in> set nts1. u \<le> v" using R by blast
  have dn: "dnt = nt" and dns: "dnts1 = nts1" and sn1: "sorted nts1"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf: "dbuf1 = (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2)" using R by blast+
  have ntdn: "nt \<le> dnext tw tss" using R tdn bound by blast
  have pst: "dux_post daux1 = dux_post daux" by (rule dux_post_mbuf2t_take[OF de])
  have ev: "dsresh n cs_R args (dux_post daux) zs dzs \<and>
      duaux_rel n cs_R cs_L args u aux2 daux2"
    using duaux_rel_eval[OF vu unt wev dev[unfolded dn]] pst by simp
  have sb: "set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs" by (rule mbuf2t_take_sub[OF we'])
  have lb1: "list_all (ftable n (set cs_L)) b1" using sb lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable n (set cs_R)) b2" using sb lvs by (auto simp: list_all_iff)
  have "duaux_rel n cs_R cs_L args u aux2 daux2 \<and> u \<le> nt \<and> nt \<le> dnext tw tss \<and>
      list_all (ftable n (set cs_L)) (fst buf1) \<and>
      list_all (ftable n (set cs_R)) (snd buf1) \<and>
      dbuf1 = (map (dtabc n cs_L) (fst buf1), map (dtabc n cs_R) (snd buf1)) \<and>
      sorted nts1 \<and> (\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> dnext tw tss)"
    using ev unt ntdn lb1 lb2 dbf sn1 un sub1 bound bfs by auto
  then have "duntil_rel n cs_R cs_L args (dnext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
    unfolding duntil_rel_def by blast
  then show ?thesis using ev dn dns dbf bfs by simp
qed

subsection \<open>The Trigger structure at the dense frame, and its buffer\<close>

text \<open>
  The trigger node carries the pair of structures, related through the abstract auxiliary list
  they are both valid for, together with the two buffers and the pending timestamps.  Unlike the
  Since and the Until, the structure is stepped and read in the same traversal, so the output
  list is part of what the step relates.  Both operands' tables enter the buffer narrowed at the
  right operand's column list; for the left one that is the embedding, by
  @{thm [source] dembed_dtabc}.
\<close>

definition dtrigger_rel :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    event_data mmtaux \<Rightarrow> event_data option gmmtaux \<Rightarrow> event_data mbuf2 \<Rightarrow>
    event_data mbuf2 \<Rightarrow> ts list \<Rightarrow> bool" where
  "dtrigger_rel n cs_R cs_L args tw aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmtaux args cur aux auxlist \<and>
        (\<forall>(t, l, r) \<in> set auxlist. ftable n (set cs_L) l \<and> ftable n (set cs_R) r) \<and>
        dtaux n cs_R cs_L args cur daux auxlist \<and> cur \<le> tw \<and>
        list_all (ftable n (set cs_L)) (fst buf) \<and>
        list_all (ftable n (set cs_R)) (snd buf) \<and>
        sorted nts \<and> (\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw) \<and>
        dbuf = (map (dtabc n cs_L) (fst buf), map (dtabc n cs_R) (snd buf)))"

lemma dtrigger_relI:
  "valid_mmtaux args cur aux auxlist \<Longrightarrow>
   (\<forall>(t, l, r) \<in> set auxlist. ftable n (set cs_L) l \<and> ftable n (set cs_R) r) \<Longrightarrow>
   dtaux n cs_R cs_L args cur daux auxlist \<Longrightarrow> cur \<le> tw \<Longrightarrow>
   list_all (ftable n (set cs_L)) xs \<Longrightarrow> list_all (ftable n (set cs_R)) ys \<Longrightarrow>
   sorted nts \<Longrightarrow> \<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw \<Longrightarrow>
   dtrigger_rel n cs_R cs_L args tw aux daux (xs, ys)
     (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys) nts"
  unfolding dtrigger_rel_def
  by (intro exI[where x = cur] exI[where x = auxlist] conjI) simp_all

lemma dtrigger_relE:
  assumes "dtrigger_rel n cs_R cs_L args tw aux daux buf dbuf nts"
  obtains cur auxlist where "valid_mmtaux args cur aux auxlist"
    and "\<forall>(t, l, r) \<in> set auxlist. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
    and "dtaux n cs_R cs_L args cur daux auxlist" and "cur \<le> tw"
    and "list_all (ftable n (set cs_L)) (fst buf)"
    and "list_all (ftable n (set cs_R)) (snd buf)"
    and "sorted nts" and "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and "dbuf = (map (dtabc n cs_L) (fst buf), map (dtabc n cs_R) (snd buf))"
  using assms unfolding dtrigger_rel_def by (elim exE conjE) (rule that)

text \<open>One firing of the trigger structure: the buffer traversal that steps it once per pending
  timestamp and collects what it answers.  The two runs stay in step by
  @{thm [source] mbuf2T_take_rel}, and each individual step is @{thm [source] dtaux_update}
  followed by @{thm [source] dtaux_result}.\<close>

lemma dtrigger_step_rel:
  assumes s: "sorted_wrt (<) cs_R" and sL: "sorted_wrt (<) cs_L"
    and b: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
    and m0: "mem (args_ivl args) 0"
    and rel: "dtrigger_rel n cs_R cs_L args tw aux daux buf dbuf nts"
    and ta: "list_all (ftable n (set cs_L)) as" and tb: "list_all (ftable n (set cs_R)) bs"
    and st: "sorted tss" and bnd: "\<forall>v \<in> set tss. tw \<le> v"
    and we: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
        in (zs @ [z], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ tss)
      = ((zs, aux1), buf1, nts1)"
    and de: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = gupdate_mmtaux (dargs cs_R cs_L args) t r1 r2 ax
        in (zs @ [dsan (gresult_mmtaux (dargs cs_R cs_L args) ax)], ax)) ([], daux)
        (mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs_R) bs) dbuf) (nts @ tss)
      = ((dzs, daux1), dbuf1, dnts1)"
  shows "dzs = map (dtabc n cs_R) zs \<and> dnts1 = nts1 \<and>
     dtrigger_rel n cs_R cs_L args (dnext tw tss) aux1 daux1 buf1 dbuf1 nts1"
proof -
  obtain cur auxlist where vw: "valid_mmtaux args cur aux auxlist"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
    and vd: "dtaux n cs_R cs_L args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable n (set cs_L)) (fst buf)"
    and lv: "list_all (ftable n (set cs_R)) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and dbf: "dbuf = (map (dtabc n cs_L) (fst buf), map (dtabc n cs_R) (snd buf))"
    using rel by (rule dtrigger_relE)
  have m0': "mem (args_ivl (dargs cs_R cs_L args)) 0" using m0 by simp
  have tk: "tok cs_R cs_L args" using m0 by (simp add: tok_def)
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  define g where "g = (\<lambda>r1 r2 t (zs :: event_data table list, ax).
    let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
    in (zs @ [z], ax))"
  define gd where "gd = (\<lambda>r1 r2 t (zs :: event_data table list, ax).
    let ax = gupdate_mmtaux (dargs cs_R cs_L args) t r1 r2 ax
    in (zs @ [dsan (gresult_mmtaux (dargs cs_R cs_L args) ax)], ax))"
  define R where "R = (\<lambda>v (pr :: event_data table list \<times> event_data mmtaux)
      (dpr :: event_data table list \<times> event_data option gmmtaux).
    (\<exists>al. valid_mmtaux args v (snd pr) al \<and>
       (\<forall>(t, l, r) \<in> set al. ftable n (set cs_L) l \<and> ftable n (set cs_R) r) \<and>
       dtaux n cs_R cs_L args v (snd dpr) al) \<and>
     fst dpr = map (dtabc n cs_R) (fst pr))"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mad: "mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs_R) bs) dbuf
      = (map (dtabc n cs_L) us, map (dtabc n cs_R) vs)"
    using dbf by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable n (set cs_L)) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable n (set cs_R)) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a c v w z z'. a \<in> set us \<Longrightarrow> c \<in> set vs \<Longrightarrow> R w z z' \<Longrightarrow> w \<le> v \<Longrightarrow>
      R v (g a c v z) (gd (dtabc n cs_L a) (dtabc n cs_R c) v z')"
  proof -
    fix a c v w and z :: "event_data table list \<times> event_data mmtaux"
      and z' :: "event_data table list \<times> event_data option gmmtaux"
    assume au: "a \<in> set us" and cv: "c \<in> set vs" and q: "R w z z'" and wv: "w \<le> v"
    have t1: "ftable n (set cs_L) a" using au lus by (simp add: list_all_iff)
    have t2: "ftable n (set cs_R) c" using cv lvs by (simp add: list_all_iff)
    obtain al where vwz: "valid_mmtaux args w (snd z) al"
      and wfz: "\<forall>(t, l, r) \<in> set al. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
      and vdz: "dtaux n cs_R cs_L args w (snd z') al"
      using q unfolding R_def by blast
    have fz: "fst z' = map (dtabc n cs_R) (fst z)" using q unfolding R_def by blast
    define al' where "al' = filter (\<lambda>(t, _). memR (args_ivl args) (v - t)) al @ [(v, a, c)]"
    have vw': "valid_mmtaux args v (update_mmtaux args v a c (snd z)) al'"
      unfolding al'_def
      by (rule valid_update_mmtaux[OF wv _ _ vwz]) (use t1 t2 an aL aR in simp_all)
    have wf': "\<forall>(t, l, r) \<in> set al'. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
      using wfz t1 t2 unfolding al'_def by auto
    have vd': "dtaux n cs_R cs_L args v
        (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z')) al'"
      unfolding al'_def by (rule dtaux_update[OF vdz wv s sL b sub tk]) (use t1 t2 in simp_all)
    have ne: "\<not> gmmtaux_empty (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a)
        (dtabc n cs_R c) (snd z'))"
      by (rule gupdate_mmtaux_not_empty[OF m0'])
    have res: "result_mmtaux args (update_mmtaux args v a c (snd z))
        = trigger_results args v al'" by (rule valid_result_mmtaux[OF vw'])
    have dres: "gresult_mmtaux (dargs cs_R cs_L args)
          (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z'))
        = dtabc n cs_R (snd (trigger_results args v al'))"
      by (rule dtaux_result[OF vd' ne s b sub an aL aR])
    have dres': "gresult_mmtaux (dargs cs_R cs_L args)
          (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z'))
        = dtabc n cs_R (snd (result_mmtaux args (update_mmtaux args v a c (snd z))))"
      unfolding res by (rule dres)
    have gz: "g a c v z
        = (fst z @ [snd (result_mmtaux args (update_mmtaux args v a c (snd z)))],
           update_mmtaux args v a c (snd z))"
      by (cases z) (simp add: g_def Let_def case_prod_beta)
    have gdz: "gd (dtabc n cs_L a) (dtabc n cs_R c) v z'
        = (fst z' @ [dsan (gresult_mmtaux (dargs cs_R cs_L args)
             (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c)
               (snd z')))],
           gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z'))"
      by (cases z') (simp add: gd_def Let_def case_prod_beta)
    have nz: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (v - t)) al')"
      unfolding al'_def using m0 by simp
    have tr: "table n (set cs_R) (snd (trigger_results args v al'))"
      unfolding trigger_results_snd using nz an aR by (auto simp: table_def)
    have sd: "dsan (gresult_mmtaux (dargs cs_R cs_L args)
          (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z')))
        = gresult_mmtaux (dargs cs_R cs_L args)
          (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z'))"
      unfolding dres' res by (rule dsan_dtabc[OF s b tr])
    show "R v (g a c v z) (gd (dtabc n cs_L a) (dtabc n cs_R c) v z')"
      unfolding R_def gz gdz sd fst_conv snd_conv
      using vw' wf' vd' fz dres' by (intro conjI exI[where x = al']) simp_all
  qed
  have sts: "sorted (nts @ tss)"
    using sn st cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>v \<in> set (nts @ tss). cur \<le> v" using cn bnd ctw by fastforce
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext tw tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF st] by fastforce
  have cdn: "cur \<le> dnext tw tss" using ctw dnext_ge[OF bnd] by simp
  have r0: "R cur ([], aux) ([], daux)" unfolding R_def
    by (intro conjI exI[where x = auxlist]) (use vw wf vd in simp_all)
  have we': "mbuf2T_take g ([], aux) (us, vs) (nts @ tss) = ((zs, aux1), (b1, b2), nts1)"
    using we unfolding ma bfs g_def by simp
  have de': "mbuf2T_take gd ([], daux) (map (dtabc n cs_L) us, map (dtabc n cs_R) vs)
      (nts @ tss) = ((dzs, daux1), dbuf1, dnts1)"
    using de unfolding mad gd_def by simp
  have Rr: "(\<exists>u. R u (zs, aux1) (dzs, daux1) \<and> u \<le> dnext tw tss \<and> (\<forall>t \<in> set nts1. u \<le> t)) \<and>
      sorted nts1 \<and> set nts1 \<subseteq> set (nts @ tss) \<and> set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs \<and>
      dbuf1 = (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2) \<and> dnts1 = nts1"
    by (rule mbuf2T_take_rel[where R = R and f = g and g = gd and h = "dtabc n cs_L"
        and k = "dtabc n cs_R", OF step r0 sts cts bound cdn we' de'])
  obtain u where ru: "R u (zs, aux1) (dzs, daux1)" and ub: "u \<le> dnext tw tss"
    and un: "\<forall>t \<in> set nts1. u \<le> t" using Rr by blast
  have sn1: "sorted nts1" and sb1: "set b1 \<subseteq> set us" and sb2: "set b2 \<subseteq> set vs"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf1: "dbuf1 = (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2)"
    and dn1: "dnts1 = nts1" using Rr by blast+
  have lb1: "list_all (ftable n (set cs_L)) b1" using sb1 lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable n (set cs_R)) b2" using sb2 lvs by (auto simp: list_all_iff)
  obtain al1 where v1: "valid_mmtaux args u aux1 al1"
    and w1: "\<forall>(t, l, r) \<in> set al1. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
    and d1: "dtaux n cs_R cs_L args u daux1 al1" using ru unfolding R_def by auto
  have dz: "dzs = map (dtabc n cs_R) zs" using ru unfolding R_def by simp
  have bnd1: "\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> dnext tw tss" using un sub1 bound by auto
  have "dtrigger_rel n cs_R cs_L args (dnext tw tss) aux1 daux1 (b1, b2)
      (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2) nts1"
    by (rule dtrigger_relI[OF v1 w1 d1 ub lb1 lb2 sn1 bnd1])
  then show ?thesis using dz dn1 bfs dbf1 by simp
qed

subsection \<open>The fused And-Trigger, and its two buffers\<close>

text \<open>
  The kernel's fused node reads the trigger structure as a pair: a set of columns and a table.
  On a non-empty window the set is the trigger's own frame and the table is its answer; on an
  empty one the read is the full table over no columns at all, which the join then lets through
  untouched.  The dense node keeps that distinction as an option -- @{term None} stands for the
  empty window and the join step skips -- so the two reads are related rather than equal.
\<close>

definition dtres :: "nat \<Rightarrow> cols \<Rightarrow> nat set \<times> event_data table \<Rightarrow> event_data table option \<Rightarrow> bool"
  where
  "dtres n cs_R p q \<longleftrightarrow> (case q of
      None \<Rightarrow> p = ({}, unit_table n)
    | Some d \<Rightarrow> fst p = set cs_R \<and> ftable n (set cs_R) (snd p) \<and> d = dtabc n cs_R (snd p))"

lemma dtres_join:
  assumes s: "sorted_wrt (<) cs" and sR: "sorted_wrt (<) cs_R"
    and b: "\<forall>c \<in> set cs. c < n" and sub: "set cs_R \<subseteq> set cs"
    and t: "ftable n (set cs) a" and r: "dtres n cs_R p q"
  shows "(case q of None \<Rightarrow> dtabc n cs a
        | Some z \<Rightarrow> dbin_join (mk_djoin cs cs_R) (dtabc n cs a) True z)
      = dtabc n cs (bin_join n (set cs) a True (fst p) (snd p))"
proof (cases q)
  case None
  then have p: "p = ({}, unit_table n)" using r by (simp add: dtres_def)
  have tu: "table n {} (unit_table n)" by (simp add: unit_table_def table_def wf_tuple_def)
  have "bin_join n (set cs) a True {} (unit_table n) = a"
    using t tu by (simp add: bin_join_table join_no_cols unit_table_def)
  then show ?thesis using None unfolding p by simp
next
  case (Some d)
  then have fp: "fst p = set cs_R" and tp: "ftable n (set cs_R) (snd p)"
    and d: "d = dtabc n cs_R (snd p)" using r by (auto simp: dtres_def)
  have bR: "\<forall>c \<in> set cs_R. c < n" using sub b by auto
  have "dbin_join (mk_djoin cs cs_R) (dtabc n cs a) True (dtabc n cs_R (snd p))
      = dtabc n (merge_cols cs cs_R) (bin_join n (set cs) a True (set cs_R) (snd p))"
    by (rule dbin_join_bin_join[OF s sR b bR _ _ _ _ _]) (use t tp in auto)
  then show ?thesis using Some fp d by (simp add: merge_cols_sub_left[OF s sR sub])
qed

text \<open>The outer buffer's two sides are therefore related rather than mapped, so the traversal
  that drains it needs a relational counterpart of @{thm [source] mbuf2_take_map}.\<close>

lemma mbuf2_take_rel2:
  assumes eq: "\<And>a b db. a \<in> set xs \<Longrightarrow> Q b db \<Longrightarrow> g (h a) db = m (f a b)"
    and q: "list_all2 Q ys dys"
    and t: "mbuf2_take f (xs, ys) = (zs, (xs', ys'))"
  shows "\<exists>dys'. mbuf2_take g (map h xs, dys) = (map m zs, (map h xs', dys')) \<and>
      list_all2 Q ys' dys'"
  using assms
proof (induct xs arbitrary: ys dys zs xs' ys')
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using Cons.prems(2,3) by (cases dys) auto
  next
    case (Cons y ys0)
    then obtain dy dys0 where d: "dys = dy # dys0" and qy: "Q y dy"
      and q0: "list_all2 Q ys0 dys0" using Cons.prems(2) by (cases dys) auto
    obtain ws b1 b2 where w: "mbuf2_take f (xs, ys0) = (ws, (b1, b2))"
      by (cases "mbuf2_take f (xs, ys0)") auto
    have zs: "zs = f x y # ws" and xs': "xs' = b1" and ys': "ys' = b2"
      using Cons.prems(3) w unfolding Cons by (auto simp: Let_def)
    have e0: "\<And>a b db. a \<in> set xs \<Longrightarrow> Q b db \<Longrightarrow> g (h a) db = m (f a b)"
      using Cons.prems(1) by simp
    obtain dys' where r: "mbuf2_take g (map h xs, dys0) = (map m ws, (map h b1, dys'))"
      and q': "list_all2 Q b2 dys'" using Cons.hyps[OF e0 q0 w] by blast
    have hx: "g (h x) dy = m (f x y)" by (rule Cons.prems(1)[OF _ qy]) simp
    show ?thesis using r q' hx unfolding d zs xs' ys' by (auto simp: Let_def)
  qed
qed

text \<open>The node's outer buffer: the left operand's tables at the node's own frame, and the
  trigger's reads as options.\<close>

definition dandbuf :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> event_data mbuft2 \<Rightarrow>
    (event_data table list \<times> event_data table option list) \<Rightarrow> bool" where
  "dandbuf n cs cs_R buf dbuf \<longleftrightarrow>
     list_all (ftable n (set cs)) (fst buf) \<and>
     fst dbuf = map (dtabc n cs) (fst buf) \<and>
     list_all2 (dtres n cs_R) (snd buf) (snd dbuf)"

lemma dandbuf_add:
  assumes b: "dandbuf n cs cs_R buf dbuf" and x: "list_all (ftable n (set cs)) xs"
    and y: "list_all2 (dtres n cs_R) ys dys"
  shows "dandbuf n cs cs_R (mbuf2_add xs ys buf) (mbuf2_add (map (dtabc n cs) xs) dys dbuf)"
  using assms by (cases buf; cases dbuf) (auto simp: dandbuf_def list_all2_appendI)

lemma dandbuf_take:
  assumes s: "sorted_wrt (<) cs" and sR: "sorted_wrt (<) cs_R"
    and b: "\<forall>c \<in> set cs. c < n" and sub: "set cs_R \<subseteq> set cs"
    and bf: "dandbuf n cs cs_R buf dbuf"
    and t: "mbuf2_take (\<lambda>r1 (V, r2). bin_join n (set cs) r1 True V r2) buf = (zs, buf')"
  shows "\<exists>dbuf'. mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> dbin_join (mk_djoin cs cs_R) r1 True z) dbuf
      = (map (dtabc n cs) zs, dbuf') \<and> dandbuf n cs cs_R buf' dbuf'"
proof -
  obtain b1 b2 where bu: "buf = (b1, b2)" by (cases buf)
  obtain c1 c2 where bu': "buf' = (c1, c2)" by (cases buf')
  have l1: "list_all (ftable n (set cs)) b1" and d1: "fst dbuf = map (dtabc n cs) b1"
    and q: "list_all2 (dtres n cs_R) b2 (snd dbuf)"
    using bf bu by (auto simp: dandbuf_def)
  have eq: "\<And>a p q. a \<in> set b1 \<Longrightarrow> dtres n cs_R p q \<Longrightarrow>
      (case q of None \<Rightarrow> dtabc n cs a | Some z \<Rightarrow> dbin_join (mk_djoin cs cs_R) (dtabc n cs a) True z)
        = dtabc n cs ((\<lambda>r1 (V, r2). bin_join n (set cs) r1 True V r2) a p)"
  proof -
    fix a p q assume au: "a \<in> set b1" and dr: "dtres n cs_R p q"
    have ta: "ftable n (set cs) a" using l1 au by (simp add: list_all_iff)
    show "(case q of None \<Rightarrow> dtabc n cs a
          | Some z \<Rightarrow> dbin_join (mk_djoin cs cs_R) (dtabc n cs a) True z)
        = dtabc n cs ((\<lambda>r1 (V, r2). bin_join n (set cs) r1 True V r2) a p)"
      using dtres_join[OF s sR b sub ta dr] by (simp add: case_prod_beta)
  qed
  obtain dys' where r: "mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> dbin_join (mk_djoin cs cs_R) r1 True z) (map (dtabc n cs) b1, snd dbuf)
      = (map (dtabc n cs) zs, (map (dtabc n cs) c1, dys'))"
    and q': "list_all2 (dtres n cs_R) c2 dys'"
    using mbuf2_take_rel2[where h = "dtabc n cs" and m = "dtabc n cs"
        and Q = "dtres n cs_R" and f = "\<lambda>r1 (V, r2). bin_join n (set cs) r1 True V r2"
        and g = "\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> dbin_join (mk_djoin cs cs_R) r1 True z"
        and xs = b1 and ys = b2 and dys = "snd dbuf" and zs = zs and xs' = c1 and ys' = c2,
        OF eq q t[unfolded bu bu']] by blast
  have sc: "set c1 \<subseteq> set b1" using mbuf2_take_sub t bu bu' by blast
  have du: "dbuf = (map (dtabc n cs) b1, snd dbuf)" using d1 by (cases dbuf) simp
  show ?thesis using r q' sc l1 bu'
    by (intro exI[where x = "(map (dtabc n cs) c1, dys')"])
      (subst du, auto simp: dandbuf_def list_all_iff)
qed

text \<open>One firing of the fused node's trigger structure.  It differs from the standalone node's
  only in what each step appends: the kernel keeps the read's column set beside its table, and
  the dense side keeps the empty window as @{term None}.\<close>

lemma dandtrigger_step_rel:
  assumes s: "sorted_wrt (<) cs_R" and sL: "sorted_wrt (<) cs_L"
    and b: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
    and ok: "tok cs_R cs_L args"
    and rel: "dtrigger_rel n cs_R cs_L args tw aux daux buf dbuf nts"
    and ta: "list_all (ftable n (set cs_L)) as" and tb: "list_all (ftable n (set cs_R)) bs"
    and st: "sorted tss" and bnd: "\<forall>v \<in> set tss. tw \<le> v"
    and we: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
        in (zs @ [(fv_z, z)], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ tss)
      = ((zs, aux1), buf1, nts1)"
    and de: "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
        let ax = gupdate_mmtaux (dargs cs_R cs_L args) t r1 r2 ax
        in (ws @ [if gmmtaux_empty ax then None
                  else Some (dsan (gresult_mmtaux (dargs cs_R cs_L args) ax))], ax)) ([], daux)
        (mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs_R) bs) dbuf) (nts @ tss)
      = ((dzs, daux1), dbuf1, dnts1)"
  shows "list_all2 (dtres n cs_R) zs dzs \<and> dnts1 = nts1 \<and>
     dtrigger_rel n cs_R cs_L args (dnext tw tss) aux1 daux1 buf1 dbuf1 nts1"
proof -
  obtain cur auxlist where vw: "valid_mmtaux args cur aux auxlist"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
    and vd: "dtaux n cs_R cs_L args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable n (set cs_L)) (fst buf)"
    and lv: "list_all (ftable n (set cs_R)) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and dbf: "dbuf = (map (dtabc n cs_L) (fst buf), map (dtabc n cs_R) (snd buf))"
    using rel by (rule dtrigger_relE)
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  define g where "g = (\<lambda>r1 r2 t (zs :: (nat set \<times> event_data table) list, ax).
    let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
    in (zs @ [(fv_z, z)], ax))"
  define gd where "gd = (\<lambda>r1 r2 t (ws :: event_data table option list, ax).
    let ax = gupdate_mmtaux (dargs cs_R cs_L args) t r1 r2 ax
    in (ws @ [if gmmtaux_empty ax then None
              else Some (dsan (gresult_mmtaux (dargs cs_R cs_L args) ax))], ax))"
  define R where "R = (\<lambda>v (pr :: (nat set \<times> event_data table) list \<times> event_data mmtaux)
      (dpr :: event_data table option list \<times> event_data option gmmtaux).
    (\<exists>al. valid_mmtaux args v (snd pr) al \<and>
       (\<forall>(t, l, r) \<in> set al. ftable n (set cs_L) l \<and> ftable n (set cs_R) r) \<and>
       dtaux n cs_R cs_L args v (snd dpr) al) \<and>
     list_all2 (dtres n cs_R) (fst pr) (fst dpr))"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mad: "mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs_R) bs) dbuf
      = (map (dtabc n cs_L) us, map (dtabc n cs_R) vs)"
    using dbf by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable n (set cs_L)) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable n (set cs_R)) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a c v w z z'. a \<in> set us \<Longrightarrow> c \<in> set vs \<Longrightarrow> R w z z' \<Longrightarrow> w \<le> v \<Longrightarrow>
      R v (g a c v z) (gd (dtabc n cs_L a) (dtabc n cs_R c) v z')"
  proof -
    fix a c v w and z :: "(nat set \<times> event_data table) list \<times> event_data mmtaux"
      and z' :: "event_data table option list \<times> event_data option gmmtaux"
    assume au: "a \<in> set us" and cv: "c \<in> set vs" and q: "R w z z'" and wv: "w \<le> v"
    have t1: "ftable n (set cs_L) a" using au lus by (simp add: list_all_iff)
    have t2: "ftable n (set cs_R) c" using cv lvs by (simp add: list_all_iff)
    obtain al where vwz: "valid_mmtaux args w (snd z) al"
      and wfz: "\<forall>(t, l, r) \<in> set al. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
      and vdz: "dtaux n cs_R cs_L args w (snd z') al"
      using q unfolding R_def by blast
    have fz: "list_all2 (dtres n cs_R) (fst z) (fst z')" using q unfolding R_def by blast
    define al' where "al' = filter (\<lambda>(t, _). memR (args_ivl args) (v - t)) al @ [(v, a, c)]"
    have vw': "valid_mmtaux args v (update_mmtaux args v a c (snd z)) al'"
      unfolding al'_def
      by (rule valid_update_mmtaux[OF wv _ _ vwz]) (use t1 t2 an aL aR in simp_all)
    have wf': "\<forall>(t, l, r) \<in> set al'. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
      using wfz t1 t2 unfolding al'_def by auto
    have vd': "dtaux n cs_R cs_L args v
        (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z')) al'"
      unfolding al'_def by (rule dtaux_update[OF vdz wv s sL b sub ok]) (use t1 t2 in simp_all)
    have res: "result_mmtaux args (update_mmtaux args v a c (snd z))
        = trigger_results args v al'" by (rule valid_result_mmtaux[OF vw'])
    have dr: "dtres n cs_R (result_mmtaux args (update_mmtaux args v a c (snd z)))
        (if gmmtaux_empty (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a)
             (dtabc n cs_R c) (snd z')) then None
         else Some (dsan (gresult_mmtaux (dargs cs_R cs_L args)
           (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c)
             (snd z')))))"
    proof (cases "gmmtaux_empty (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a)
        (dtabc n cs_R c) (snd z'))")
      case True
      then show ?thesis
        unfolding res using dtaux_result_empty[OF vd' True] an
        by (simp add: dtres_def unit_table_def)
    next
      case False
      have nz: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (v - t)) al')"
        using dtaux_window[OF vd'] False by (simp add: split_def)
      have lst: "fst (last al') = v" unfolding al'_def by simp
      have ft: "ftable n (fst (trigger_results args v al')) (snd (trigger_results args v al'))"
        by (rule conjunct1[OF ftable_trigger_results_weak[OF wf' _ lst an aL aR tok_weak[OF ok]]])
          (simp add: al'_def)
      have fv: "fst (trigger_results args v al') = set cs_R" using nz aR by simp
      have tr: "ftable n (set cs_R) (snd (trigger_results args v al'))" using ft unfolding fv .
      have dres: "gresult_mmtaux (dargs cs_R cs_L args)
            (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z'))
          = dtabc n cs_R (snd (trigger_results args v al'))"
        by (rule dtaux_result[OF vd' False s b sub an aL aR])
      have sd: "dsan (gresult_mmtaux (dargs cs_R cs_L args)
            (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z')))
          = dtabc n cs_R (snd (trigger_results args v al'))"
        unfolding dres by (rule dsan_dtabc[OF s b]) (use tr in simp)
      show ?thesis unfolding res using False fv tr sd by (simp add: dtres_def)
    qed
    have gz: "g a c v z = (fst z @ [result_mmtaux args (update_mmtaux args v a c (snd z))],
           update_mmtaux args v a c (snd z))"
      by (cases z) (simp add: g_def Let_def case_prod_beta)
    have gdz: "gd (dtabc n cs_L a) (dtabc n cs_R c) v z'
        = (fst z' @ [if gmmtaux_empty (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a)
               (dtabc n cs_R c) (snd z')) then None
             else Some (dsan (gresult_mmtaux (dargs cs_R cs_L args)
               (gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c)
                 (snd z'))))],
           gupdate_mmtaux (dargs cs_R cs_L args) v (dtabc n cs_L a) (dtabc n cs_R c) (snd z'))"
      by (cases z') (simp add: gd_def Let_def case_prod_beta)
    show "R v (g a c v z) (gd (dtabc n cs_L a) (dtabc n cs_R c) v z')"
      unfolding R_def gz gdz fst_conv snd_conv
      using vw' wf' vd' fz dr by (intro conjI exI[where x = al']) (simp_all add: list_all2_appendI)
  qed
  have sts: "sorted (nts @ tss)"
    using sn st cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>v \<in> set (nts @ tss). cur \<le> v" using cn bnd ctw by fastforce
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext tw tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF st] by fastforce
  have cdn: "cur \<le> dnext tw tss" using ctw dnext_ge[OF bnd] by simp
  have r0: "R cur ([], aux) ([], daux)" unfolding R_def
    by (intro conjI exI[where x = auxlist]) (use vw wf vd in simp_all)
  have we': "mbuf2T_take g ([], aux) (us, vs) (nts @ tss) = ((zs, aux1), (b1, b2), nts1)"
    using we unfolding ma bfs g_def by simp
  have de': "mbuf2T_take gd ([], daux) (map (dtabc n cs_L) us, map (dtabc n cs_R) vs)
      (nts @ tss) = ((dzs, daux1), dbuf1, dnts1)"
    using de unfolding mad gd_def by simp
  have Rr: "(\<exists>u. R u (zs, aux1) (dzs, daux1) \<and> u \<le> dnext tw tss \<and> (\<forall>t \<in> set nts1. u \<le> t)) \<and>
      sorted nts1 \<and> set nts1 \<subseteq> set (nts @ tss) \<and> set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs \<and>
      dbuf1 = (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2) \<and> dnts1 = nts1"
    by (rule mbuf2T_take_rel[where R = R and f = g and g = gd and h = "dtabc n cs_L"
        and k = "dtabc n cs_R", OF step r0 sts cts bound cdn we' de'])
  obtain u where ru: "R u (zs, aux1) (dzs, daux1)" and ub: "u \<le> dnext tw tss"
    and un: "\<forall>t \<in> set nts1. u \<le> t" using Rr by blast
  have sn1: "sorted nts1" and sb1: "set b1 \<subseteq> set us" and sb2: "set b2 \<subseteq> set vs"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf1: "dbuf1 = (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2)"
    and dn1: "dnts1 = nts1" using Rr by blast+
  have lb1: "list_all (ftable n (set cs_L)) b1" using sb1 lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable n (set cs_R)) b2" using sb2 lvs by (auto simp: list_all_iff)
  obtain al1 where v1: "valid_mmtaux args u aux1 al1"
    and w1: "\<forall>(t, l, r) \<in> set al1. ftable n (set cs_L) l \<and> ftable n (set cs_R) r"
    and d1: "dtaux n cs_R cs_L args u daux1 al1" using ru unfolding R_def by auto
  have dz: "list_all2 (dtres n cs_R) zs dzs" using ru unfolding R_def by simp
  have bnd1: "\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> dnext tw tss" using un sub1 bound by auto
  have "dtrigger_rel n cs_R cs_L args (dnext tw tss) aux1 daux1 (b1, b2)
      (map (dtabc n cs_L) b1, map (dtabc n cs_R) b2) nts1"
    by (rule dtrigger_relI[OF v1 w1 d1 ub lb1 lb2 sn1 bnd1])
  then show ?thesis using dz dn1 bfs dbf1 by simp
qed

subsection \<open>The relation itself\<close>

inductive dsim :: "nat \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> dformula \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  DsRel: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MRel rel) \<Longrightarrow>
    table n (set cs) rel \<Longrightarrow>
    dsim n cs tw (DRel (dtabc n cs rel)) (mformula.MRel rel)"
| DsPredC: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MPred e tms Copy) \<Longrightarrow>
    tms = map Formula.Var [0..<n] \<Longrightarrow> cs = [0..<n] \<Longrightarrow>
    dsim n cs tw (DPredS e n) (mformula.MPred e tms Copy)"
| DsPredS: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MPred e tms Simple) \<Longrightarrow>
    is_simple_pattern tms 0 \<Longrightarrow> cs = smp_cols tms \<Longrightarrow>
    dsim n cs tw (DPredS e (length tms)) (mformula.MPred e tms Simple)"
| DsPredM: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MPred e tms Match) \<Longrightarrow>
    dsim n cs tw (DPredM e (length tms) tms cs) (mformula.MPred e tms Match)"
| DsAndRel: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MAndRel \<phi> (t1, p, c, t2)) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow>
    Formula.fv_trm t1 \<subseteq> set cs \<Longrightarrow> Formula.fv_trm t2 \<subseteq> set cs \<Longrightarrow>
    dsim n cs tw (DAndRel \<phi>d (reindex_constraint cs (t1, p, c, t2)))
      (mformula.MAndRel \<phi> (t1, p, c, t2))"
| DsNeg: "produces n {} tw (mformula.MNeg \<phi>) \<Longrightarrow> dsim n [] tw \<phi>d \<phi> \<Longrightarrow>
    dsim n [] tw (DNeg \<phi>d) (mformula.MNeg \<phi>)"
| DsExists: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MExists \<phi>) \<Longrightarrow>
    dsim (Suc n) ccs tw \<phi>d \<phi> \<Longrightarrow> cs = ex_cols ccs \<Longrightarrow> b = ex_drop0 ccs \<Longrightarrow>
    dsim n cs tw (DExists \<phi>d b) (mformula.MExists \<phi>)"
| DsOr: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MOr \<phi> \<psi> buf) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    dbuf2 n cs cs buf dbuf \<Longrightarrow>
    dsim n cs tw (DOr \<phi>d \<psi>d dbuf) (mformula.MOr \<phi> \<psi> buf)"
| DsAnd: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MAnd (set cs1) \<phi> pos (set cs2) \<psi> buf) \<Longrightarrow>
    dsim n cs1 tw \<phi>d \<phi> \<Longrightarrow> dsim n cs2 tw \<psi>d \<psi> \<Longrightarrow>
    cs = merge_cols cs1 cs2 \<Longrightarrow> pl = mk_djoin cs1 cs2 \<Longrightarrow>
    (\<not> pos \<Longrightarrow> set cs2 \<subseteq> set cs1) \<Longrightarrow>
    dbuf2 n cs1 cs2 buf dbuf \<Longrightarrow>
    dsim n cs tw (DAnd pl \<phi>d pos \<psi>d dbuf) (mformula.MAnd (set cs1) \<phi> pos (set cs2) \<psi> buf)"
| DsPrev: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MPrev I \<phi> first buf nts) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow>
    list_all (ftable n (set cs)) buf \<Longrightarrow> dbuf = map (dtabc n cs) buf \<Longrightarrow>
    dsim n cs tw (DPrev I \<phi>d first dbuf nts) (mformula.MPrev I \<phi> first buf nts)"
| DsNext: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MNext I \<phi> first nts) \<Longrightarrow>
    dsim n cs tw \<phi>d \<phi> \<Longrightarrow>
    dsim n cs tw (DNext I \<phi>d first nts) (mformula.MNext I \<phi> first nts)"
| DsAnds: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw
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
| DsAgg: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MAgg args \<phi>) \<Longrightarrow>
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
    produces n (set cs) tw (mformula.MSince args \<phi> \<psi> buf aux) \<Longrightarrow>
    dsim n cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols n cs_L \<Longrightarrow> set cs_L \<subseteq> set cs \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs \<Longrightarrow>
    dags = dargs cs cs_L args \<Longrightarrow>
    dsince_rel n cs cs_L args tw aux daux buf dbuf \<Longrightarrow>
    dsx_agg daux = None \<Longrightarrow>
    dsim n cs tw (DSince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
| DsUntil: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<Longrightarrow>
    dsim n cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols n cs_L \<Longrightarrow> set cs_L \<subseteq> set cs \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_n args = n \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs \<Longrightarrow>
    dags = dargs cs cs_L args \<Longrightarrow> msk = dmsk cs cs_L \<Longrightarrow>
    duntil_rel n cs cs_L args tw t aux daux buf dbuf nts \<Longrightarrow>
    dux_agg daux = None \<Longrightarrow>
    dsim n cs tw (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| DsSinceAgg: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MSince args \<phi> \<psi> buf aux) \<Longrightarrow>
    dsim nn cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim nn cs_R tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols nn cs_L \<Longrightarrow> set cs_L \<subseteq> set cs_R \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_n args = nn \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs_R \<Longrightarrow>
    dags = dargs cs_R cs_L args \<Longrightarrow>
    dsince_rel nn cs_R cs_L args tw aux daux buf dbuf \<Longrightarrow>
    wf_cols n gcols \<Longrightarrow> aggargs_n ag = n \<Longrightarrow> aggargs_y ag = y \<Longrightarrow>
    y < n \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R \<Longrightarrow>
    nn = length (aggargs_tys ag) + n \<Longrightarrow>
    cs_R = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    cs = merge_cols gcols [y] \<Longrightarrow>
    dsx_agg daux = None \<Longrightarrow>
    dsim n cs tw (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
        (length (aggargs_tys ag)) (ins_pos gcols y) (DSince dags \<phi>d \<psi>d dbuf daux))
      (mformula.MSince args \<phi> \<psi> buf aux)"
| DsSinceFused: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MSince args \<phi> \<psi> buf aux) \<Longrightarrow>
    dsim nn cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim nn cs_R tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols nn cs_L \<Longrightarrow> set cs_L \<subseteq> set cs_R \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_n args = nn \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs_R \<Longrightarrow>
    dags = dargs cs_R cs_L args \<Longrightarrow>
    dsince_rel nn cs_R cs_L args tw aux daux buf dbuf \<Longrightarrow>
    wf_cols n gcols \<Longrightarrow> aggargs_n ag = n \<Longrightarrow> aggargs_y ag = y \<Longrightarrow>
    y < n \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R \<Longrightarrow>
    nn = length (aggargs_tys ag) + n \<Longrightarrow>
    cs_R = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    cs = merge_cols gcols [y] \<Longrightarrow>
    dsx_agg daux = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y) \<Longrightarrow>
    dsim n cs tw (DSince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
| DsUntilAgg: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<Longrightarrow>
    dsim nn cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim nn cs_R tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols nn cs_L \<Longrightarrow> set cs_L \<subseteq> set cs_R \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_n args = nn \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs_R \<Longrightarrow>
    dags = dargs cs_R cs_L args \<Longrightarrow> msk = dmsk cs_R cs_L \<Longrightarrow>
    duntil_rel nn cs_R cs_L args tw t aux daux buf dbuf nts \<Longrightarrow>
    wf_cols n gcols \<Longrightarrow> aggargs_n ag = n \<Longrightarrow> aggargs_y ag = y \<Longrightarrow>
    y < n \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R \<Longrightarrow>
    nn = length (aggargs_tys ag) + n \<Longrightarrow>
    cs_R = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    cs = merge_cols gcols [y] \<Longrightarrow>
    dux_agg daux = None \<Longrightarrow>
    dsim n cs tw (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
        (length (aggargs_tys ag)) (ins_pos gcols y) (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux))
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| DsUntilFused: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<Longrightarrow>
    dsim nn cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim nn cs_R tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols nn cs_L \<Longrightarrow> set cs_L \<subseteq> set cs_R \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_n args = nn \<Longrightarrow>
    args_L args = set cs_L \<Longrightarrow> args_R args = set cs_R \<Longrightarrow>
    dags = dargs cs_R cs_L args \<Longrightarrow> msk = dmsk cs_R cs_L \<Longrightarrow>
    duntil_rel nn cs_R cs_L args tw t aux daux buf dbuf nts \<Longrightarrow>
    wf_cols n gcols \<Longrightarrow> aggargs_n ag = n \<Longrightarrow> aggargs_y ag = y \<Longrightarrow>
    y < n \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set cs_R \<Longrightarrow>
    nn = length (aggargs_tys ag) + n \<Longrightarrow>
    cs_R = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    cs = merge_cols gcols [y] \<Longrightarrow>
    dux_agg daux = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y) \<Longrightarrow>
    dsim n cs tw (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| DsAndAssign: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MAndAssign \<phi> (y, t)) \<Longrightarrow>
    dsim n cs0 tw \<phi>d \<phi> \<Longrightarrow>
    y < n \<Longrightarrow> y \<notin> set cs0 \<Longrightarrow> Formula.fv_trm t \<subseteq> set cs0 \<Longrightarrow>
    cs = merge_cols cs0 [y] \<Longrightarrow>
    dsim n cs tw (DAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) \<phi>d)
      (mformula.MAndAssign \<phi> (y, t))"
| DsTP: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MTP mt i) \<Longrightarrow>
    cs = mtrm_dcols mt \<Longrightarrow>
    dsim n cs tw (DTP mt i) (mformula.MTP mt i)"
| DsTS: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MTS mt) \<Longrightarrow>
    cs = mtrm_dcols mt \<Longrightarrow>
    dsim n cs tw (DTS mt) (mformula.MTS mt)"
| DsLet: "wf_cols n cs \<Longrightarrow> produces n (set cs) tw (mformula.MLet p m \<phi> \<psi>) \<Longrightarrow>
    dsim m [0..<m] tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    dsim n cs tw (DLet p m \<phi>d \<psi>d) (mformula.MLet p m \<phi> \<psi>)"
| DsFrz: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) \<Longrightarrow>
    dsim m [0..<m] tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    list_all (ftable m {0..<m}) \<alpha>s \<Longrightarrow>
    dsim n cs tw (DFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s)
      (mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s)"
| DsLetPast: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MLetPast p m \<phi> \<psi> i buf) \<Longrightarrow>
    dsim m [0..<m] tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    \<forall>y. buf = Some y \<longrightarrow> ftable m {0..<m} y \<Longrightarrow>
    dsim n cs tw (DLetPast p m \<phi>d \<psi>d i buf) (mformula.MLetPast p m \<phi> \<psi> i buf)"
| DsTrigger: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MTrigger args \<phi> \<psi> buf nts aux) \<Longrightarrow>
    dsim n cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim n cs tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols n cs_L \<Longrightarrow> set cs_L \<subseteq> set cs \<Longrightarrow>
    args_n args = n \<Longrightarrow> args_L args = set cs_L \<Longrightarrow> args_R args = set cs \<Longrightarrow>
    mem (args_ivl args) 0 \<Longrightarrow>
    dags = dargs cs cs_L args \<Longrightarrow> pl = emb_plan cs cs_L \<Longrightarrow>
    dtrigger_rel n cs cs_L args tw aux daux buf dbuf nts \<Longrightarrow>
    dsim n cs tw (DTrigger dags pl \<phi>d \<psi>d dbuf nts daux)
      (mformula.MTrigger args \<phi> \<psi> buf nts aux)"
| DsAndTrigger: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MAndTrigger (set cs) \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) \<Longrightarrow>
    dsim n cs tw \<alpha>d \<alpha> \<Longrightarrow> dsim n cs_L tw \<phi>d \<phi> \<Longrightarrow> dsim n cs_R tw \<psi>d \<psi> \<Longrightarrow>
    wf_cols n cs_L \<Longrightarrow> wf_cols n cs_R \<Longrightarrow>
    set cs_L \<subseteq> set cs_R \<Longrightarrow> set cs_R \<subseteq> set cs \<Longrightarrow>
    args_n args = n \<Longrightarrow> args_L args = set cs_L \<Longrightarrow> args_R args = set cs_R \<Longrightarrow>
    tok cs_R cs_L args \<Longrightarrow>
    dags = dargs cs_R cs_L args \<Longrightarrow> pl = mk_djoin cs cs_R \<Longrightarrow>
    dandbuf n cs cs_R buf1 dbf1 \<Longrightarrow>
    dtrigger_rel n cs_R cs_L args tw aux daux buf2 dbf2 nts \<Longrightarrow>
    dsim n cs tw (DAndTrigger pl \<alpha>d dbf1 dags \<phi>d \<psi>d dbf2 nts daux)
      (mformula.MAndTrigger (set cs) \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)"
| DsMatchP: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MMatchP I mr mrs L buf nts aux) \<Longrightarrow>
    Regex.safe_regex fv rgx_safe_pred Past Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set cs = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = RPDs mr \<Longrightarrow>
    length css = length \<psi>s \<Longrightarrow> length L = length \<psi>s \<Longrightarrow> length Ld = length L \<Longrightarrow>
    (\<forall>i < length \<psi>s. set (css ! i) = Formula.fv (\<psi>s ! i)) \<Longrightarrow>
    (\<forall>i < length \<psi>s. set (css ! i) \<subseteq> set cs) \<Longrightarrow>
    (\<forall>c \<in> set css. wf_cols n c) \<Longrightarrow>
    (\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    pls = map (emb_plan cs) css \<Longrightarrow>
    dbufn n css buf dbuf \<Longrightarrow>
    dmrd_rel n cs aux daux \<Longrightarrow>
    dsim n cs tw (DMatchP (length cs) I mr mrs pls Ld dbuf nts daux)
      (mformula.MMatchP I mr mrs L buf nts aux)"
| DsMatchF: "wf_cols n cs \<Longrightarrow>
    produces n (set cs) tw (mformula.MMatchF I mr mrs L buf nts t aux) \<Longrightarrow>
    Regex.safe_regex fv rgx_safe_pred Futu Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set cs = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = LPDs mr \<Longrightarrow>
    length css = length \<psi>s \<Longrightarrow> length L = length \<psi>s \<Longrightarrow> length Ld = length L \<Longrightarrow>
    (\<forall>i < length \<psi>s. set (css ! i) = Formula.fv (\<psi>s ! i)) \<Longrightarrow>
    (\<forall>i < length \<psi>s. set (css ! i) \<subseteq> set cs) \<Longrightarrow>
    (\<forall>c \<in> set css. wf_cols n c) \<Longrightarrow>
    (\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    pls = map (emb_plan cs) css \<Longrightarrow>
    dbufn n css buf dbuf \<Longrightarrow>
    dmld_rel n cs \<psi>s aux daux \<Longrightarrow>
    dsim n cs tw (DMatchF (length cs) I mr mrs pls Ld dbuf nts t daux)
      (mformula.MMatchF I mr mrs L buf nts t aux)"

text \<open>The two facts the relation is designed to hand out at every node.\<close>

lemma dsim_wf_cols: "dsim n cs tw \<phi>d \<phi> \<Longrightarrow> wf_cols n cs"
  by (erule dsim.cases)
    (auto simp: ex_cols_sorted ex_cols_bound sorted_merge_cols set_merge_cols)

lemma dsim_produces: "dsim n cs tw \<phi>d \<phi> \<Longrightarrow> produces n (set cs) tw \<phi>"
  by (erule dsim.cases) auto

text \<open>The unfused Since and Until nodes are related by one rule each, so the relation can be read
  backwards there: the operands are related at the node's own frame.  The compiler uses this to
  reuse an unfused node's simulation for the fused one, whose operands are the very same.\<close>

lemma dsim_DSinceD:
  assumes "dsim n cs tw (DSince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
    and "dsx_agg daux = None"
  obtains cs_L where "dsim n cs_L tw \<phi>d \<phi>" and "dsim n cs tw \<psi>d \<psi>"
    and "wf_cols n cs_L" and "args_L args = set cs_L"
  using assms(1) by (rule dsim.cases) (use assms(2) in auto)

lemma dsim_DUntilD:
  assumes "dsim n cs tw (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts' t' aux)"
    and "dux_agg daux = None"
  obtains cs_L where "dsim n cs_L tw \<phi>d \<phi>" and "dsim n cs tw \<psi>d \<psi>"
    and "wf_cols n cs_L" and "args_L args = set cs_L"
  using assms(1) by (rule dsim.cases) (use assms(2) in auto)

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

text \<open>The timestamped take, which the two match nodes use, keeps the buffers related in the same
  way; the accumulator is a parameter here because the past node threads a pair of the reported
  tables and the structure, and the future node the structure alone.\<close>

lemma dbufn_nt_take:
  assumes b: "dbufn n css buf dbuf"
    and st: "\<And>as u u' t. length as = length css \<Longrightarrow>
        (\<forall>i < length css. ftable n (set (css ! i)) (as ! i)) \<Longrightarrow> R u u' \<Longrightarrow>
        R (f as t u) (g (map2 (dtabc n) css as) t u')"
    and rz: "R z z'"
    and e: "mbufnt_take f z buf t0 tss = (w, buf', t', tss')"
  shows "\<exists>w2 dbuf'. mbufnt_take g z' dbuf t0 tss = (w2, dbuf', t', tss')
      \<and> R w w2 \<and> dbufn n css buf' dbuf'"
proof -
  have lb: "length buf = length css"
    and lt: "\<forall>i < length css. list_all (ftable n (set (css ! i))) (buf ! i)"
    and d: "dbuf = map2 map (map (dtabc n) css) buf"
    using b by (auto simp: dbufn_def)
  define hs :: "(event_data table \<Rightarrow> event_data table) list"
    where "hs = map (dtabc n) css"
  define Ss :: "event_data table set list"
    where "Ss = map (\<lambda>c. {T. ftable n (set c) T}) css"
  obtain w2 buf2 t2 tss2 where e2: "mbufnt_take g z' dbuf t0 tss = (w2, buf2, t2, tss2)"
    by (cases "mbufnt_take g z' dbuf t0 tss") auto
  have sub: "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i"
    using lt lb by (auto simp: Ss_def list_all_iff)
  have step: "\<And>as u u' t. length as = length hs \<Longrightarrow>
      (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> R u u' \<Longrightarrow>
      R (f as t u) (g (map2 (\<lambda>h a. h a) hs as) t u')"
  proof -
    fix as :: "event_data table list" and u u' t
    assume la: "length as = length hs" and ma: "\<forall>i < length as. as ! i \<in> Ss ! i"
      and ru: "R u u'"
    have la': "length as = length css" using la by (simp add: hs_def)
    have ma': "\<forall>i < length css. ftable n (set (css ! i)) (as ! i)"
      using ma la' by (auto simp: Ss_def)
    show "R (f as t u) (g (map2 (\<lambda>h a. h a) hs as) t u')"
      using st[OF la' ma' ru] by (simp add: hs_def map2_apply_map)
  qed
  have r: "R w w2 \<and> buf2 = map2 map hs buf' \<and> t2 = t' \<and> tss2 = tss'"
  proof (rule mbufnt_take_rel[where R = R and Ss = Ss and hs = hs and f = f and g = g
        and z = z and z' = z' and buf = buf and buf' = buf' and w = w])
    show "length hs = length buf" using lb by (simp add: hs_def)
    show "length Ss = length buf" using lb by (simp add: Ss_def)
    show "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i" by (rule sub)
    show "\<And>as t u u'. length as = length hs \<Longrightarrow> (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> R u u' \<Longrightarrow>
        R (f as t u) (g (map2 (\<lambda>h a. h a) hs as) t u')" by (rule step)
    show "R z z'" by (rule rz)
    show "mbufnt_take f z buf t0 tss = (w, buf', t', tss')" by (rule e)
    show "mbufnt_take g z' (map2 map hs buf) t0 tss = (w2, buf2, t2, tss2)"
      using e2 d by (simp add: hs_def)
  qed
  have ls: "length buf' = length buf"
    and ss: "\<forall>i < length buf. set (buf' ! i) \<subseteq> set (buf ! i)"
    using mbufnt_take_sub[OF e] by auto
  have "dbufn n css buf' buf2"
    using lt lb ls ss r by (fastforce simp: dbufn_def hs_def list_all_iff)
  then show ?thesis using e2 r by auto
qed

subsection \<open>Stepping a list of operands\<close>

lemma dsims_tables:
  "(\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
   length Ld = length L \<Longrightarrow> length css = length L \<Longrightarrow> wf_db db \<Longrightarrow>
   sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> i < length L \<Longrightarrow>
     list_all (ftable n (set (css ! i))) (fst (meval j n ts db (L ! i)))"
proof (induct L arbitrary: css Ld i)
  case (Cons \<psi> L')
  note la = Cons(2) and l1 = Cons(3) and l2 = Cons(4) and w = Cons(5)
    and sts = Cons(6) and mts = Cons(7) and i = Cons(8)
    and IH = Cons(1)
  obtain c css' where c: "css = c # css'" using l2 by (cases css) auto
  obtain \<psi>d Ld' where d: "Ld = \<psi>d # Ld'" using l1 by (cases Ld) auto
  show ?case
  proof (cases i)
    case 0
    have h: "dsim n c tw \<psi>d \<psi>" using la unfolding c d by (auto dest: spec[of _ 0])
    obtain as \<psi>2 where e: "meval j n ts db \<psi> = (as, \<psi>2)" by (cases "meval j n ts db \<psi>")
    have "list_all (ftable n (set c)) as" by (rule produces_tables[OF dsim_produces[OF h] w sts mts e])
    then show ?thesis unfolding c 0 using e by simp
  next
    case (Suc i')
    have ta: "\<forall>k < length L'. dsim n (css' ! k) tw (Ld' ! k) (L' ! k)"
      using la unfolding c d by auto
    show ?thesis using IH[OF ta _ _ w sts mts] l1 l2 i unfolding c d Suc by simp
  qed
qed simp

lemma deval_list_rel:
  "length Ld = length L \<Longrightarrow> length css = length L \<Longrightarrow>
   (\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i) \<and>
       (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
          (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (css ! i)) as, \<psi>d')
             \<and> dsim n (css ! i) tw' \<psi>d' \<psi>'))) \<Longrightarrow>
   length (map (deval j ts db) Ld) = length L \<and>
   map fst (map (deval j ts db) Ld)
       = map2 (\<lambda>c x. map (dtabc n c) x) css (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
   (\<forall>i < length L. dsim n (css ! i) tw' (map snd (map (deval j ts db) Ld) ! i)
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
  have rest: "length (map (deval j ts db) Ld') = length L' \<and>
      map fst (map (deval j ts db) Ld')
        = map2 (\<lambda>c x. map (dtabc n c) x) css'
            (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L') \<and>
      (\<forall>k < length L'. dsim n (css' ! k) tw' (map snd (map (deval j ts db) Ld') ! k)
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
  One firing of @{const meval_since} at the dense frame reports the same windows as one firing at
  the wide frame, and the relation is preserved.  The recursion is driven by the buffer alone, so
  the two sides step in lockstep; the induction is over the kernel's own recursion.
\<close>

lemma eval_since_rel:
  fixes cs_R cs_L :: cols and args :: args
  assumes sR: "sorted_wrt (<) cs_R" and sL: "sorted_wrt (<) cs_L"
    and bR: "\<forall>c \<in> set cs_R. c < n"
    and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
  shows "meval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow>
    dsx_eval_since (dargs cs_R cs_L args) drs dbuf daux = (dzs, dbuf', daux') \<Longrightarrow>
    dsince_rel n cs_R cs_L args tw aux daux buf dbuf \<Longrightarrow>
    dsx_post daux = h \<Longrightarrow>
    dsresh n cs_R args h rs drs \<Longrightarrow>
    dsresh n cs_R args h zs dzs \<and> dsince_rel n cs_R cs_L args tw aux' daux' buf' dbuf' \<and>
    dsx_post daux' = h"
proof (induction rs buf aux arbitrary: drs daux dbuf zs buf' aux' dzs dbuf' daux'
    taking: args rule: default_maux.eval_since.induct)
  case (1 rs x xs t tss skew aux)
  note E = 1(1) and D = 1(2) and R = 1(3) and P = 1(4) and S = 1(5)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' n cs_R cs_L args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable n (set cs_L)) (x # xs)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_L) (x # xs), map (dtabc n cs_R) [], t # tss, skew)"
    using R by (rule dsince_relE)
  have tx: "table n (set cs_L) x" using lx by simp
  have ctu: "cur \<le> t" using ct by simp
  show ?case
  proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev rs, (x # xs, [], t # tss, skew), aux)" using True by simp
    have DW: "dsx_eval_since (dargs cs_R cs_L args) drs dbuf daux = (rev drs, dbuf, daux)"
      unfolding dbuf using True by simp
    have EE: "(rev rs, (x # xs, [], t # tss, skew), aux) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev drs, dbuf, daux) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    show ?thesis using EE DD R dsresh_rev[OF S] P by auto
  next
    case False
    let ?wa = "gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)"
    let ?da = "dsx_join (dargs cs_R cs_L args) (dtabc n cs_L x)
        (dsx_add_new_ts (dargs cs_R cs_L args) t daux)"
    let ?al = "map (\<lambda>(u, rel). (u, join rel (args_pos args) x))
        (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
    have vw': "valid_mmasaux args t ?wa ?al"
      by (rule default_mmasaux.valid_join_msaux
          [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
    have vd': "dsxaux' n cs_R cs_L args t ?da ?al"
      by (rule dsxaux'_join[OF dsxaux'_add_new_ts[OF vd ctu] sR sL bR sub tx])
    have res0: "dsresh n cs_R args h [result_mmasaux args ?wa]
        [dsx_result (dargs cs_R cs_L args) ?da]"
      using dsresh_result[OF vd' vw'] by (simp add: P)
    have res: "dsresh n cs_R args h (result_mmasaux args ?wa # rs)
        (dsx_result (dargs cs_R cs_L args) ?da # drs)"
      using dsresh_append[OF res0 S] by simp
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa)"
      using False by (simp add: Let_def)
    have DW: "dsx_eval_since (dargs cs_R cs_L args) drs dbuf daux
        = (rev (dsx_result (dargs cs_R cs_L args) ?da # drs),
           (map (dtabc n cs_L) xs, map (dtabc n cs_R) [], tss, True), ?da)"
      unfolding dbuf using False by (simp add: Let_def)
    have EE: "(rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev (dsx_result (dargs cs_R cs_L args) ?da # drs),
        (map (dtabc n cs_L) xs, map (dtabc n cs_R) [], tss, True), ?da) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    have R': "dsince_rel n cs_R cs_L args tw ?wa ?da (xs, [], tss, True)
        (map (dtabc n cs_L) xs, map (dtabc n cs_R) [], tss, True)"
      by (rule dsince_relI[OF vw' vd']) (use lx st ct in auto)
    show ?thesis using EE DD dsresh_rev[OF res] R' P by auto
  qed
next
  case (2 rs xs y ys tss aux)
  note IH = 2(1) and E = 2(2) and D = 2(3) and R = 2(4) and P = 2(5) and S = 2(6)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' n cs_R cs_L args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable n (set cs_L)) xs"
    and ly: "list_all (ftable n (set cs_R)) (y # ys)"
    and st: "sorted tss" and ct: "\<forall>u \<in> set tss. cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_L) xs, map (dtabc n cs_R) (y # ys), tss, True)"
    using R by (rule dsince_relE)
  have ty: "table n (set cs_R) y" and fy: "finite y" using ly by simp_all
  let ?al = "case auxlist of [] \<Rightarrow> [(cur, y)]
      | ((u, w) # r) \<Rightarrow> if u = cur then (u, w \<union> y) # r else (cur, y) # auxlist"
  have vw': "valid_mmasaux args cur (add_new_table_mmasaux args y aux) ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vw]) (use ty an aR in simp)
  have vd': "dsxaux' n cs_R cs_L args cur
      (dsx_add_new_table (dargs cs_R cs_L args) (dtabc n cs_R y) daux) ?al"
    by (rule dsxaux'_add_new_table[OF vd sR bR ty fy])
  have E': "meval_since args rs (xs, ys, tss, False) (add_new_table_mmasaux args y aux)
      = (zs, buf', aux')" using E by simp
  have D': "dsx_eval_since (dargs cs_R cs_L args) drs
      (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys, tss, False)
      (dsx_add_new_table (dargs cs_R cs_L args) (dtabc n cs_R y) daux)
      = (dzs, dbuf', daux')" using D unfolding dbuf by simp
  have R': "dsince_rel n cs_R cs_L args tw (add_new_table_mmasaux args y aux)
      (dsx_add_new_table (dargs cs_R cs_L args) (dtabc n cs_R y) daux)
      (xs, ys, tss, False) (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys, tss, False)"
    by (rule dsince_relI[OF vw' vd' ctw]) (use lx ly st ct in auto)
  have P': "dsx_post (dsx_add_new_table (dargs cs_R cs_L args) (dtabc n cs_R y) daux) = h"
    using P by simp
  show ?case by (rule IH[OF E' D' R' P' S])
next
  case (3 rs x xs y ys t tss aux)
  note IH = 3(1) and E = 3(2) and D = 3(3) and R = 3(4) and P = 3(5) and S = 3(6)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' n cs_R cs_L args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable n (set cs_L)) (x # xs)"
    and ly: "list_all (ftable n (set cs_R)) (y # ys)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc n cs_L) (x # xs), map (dtabc n cs_R) (y # ys), t # tss, False)"
    using R by (rule dsince_relE)
  have tx: "table n (set cs_L) x" using lx by simp
  have ty: "table n (set cs_R) y" and fy: "finite y" using ly by simp_all
  have ctu: "cur \<le> t" using ct by simp
  let ?jl = "map (\<lambda>(u, rel). (u, join rel (args_pos args) x))
      (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
  let ?al = "case ?jl of [] \<Rightarrow> [(t, y)]
      | ((u, w) # r) \<Rightarrow> if u = t then (u, w \<union> y) # r else (t, y) # ?jl"
  let ?wa = "add_new_table_mmasaux args y
      (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux))"
  let ?da = "dsx_add_new_table (dargs cs_R cs_L args) (dtabc n cs_R y)
      (dsx_join (dargs cs_R cs_L args) (dtabc n cs_L x)
        (dsx_add_new_ts (dargs cs_R cs_L args) t daux))"
  have vwj: "valid_mmasaux args t (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)) ?jl"
    by (rule default_mmasaux.valid_join_msaux
        [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu]]) (use tx an aL in simp)
  have vdj: "dsxaux' n cs_R cs_L args t
      (dsx_join (dargs cs_R cs_L args) (dtabc n cs_L x)
        (dsx_add_new_ts (dargs cs_R cs_L args) t daux)) ?jl"
    by (rule dsxaux'_join[OF dsxaux'_add_new_ts[OF vd ctu] sR sL bR sub tx])
  have vw': "valid_mmasaux args t ?wa ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vwj]) (use ty an aR in simp)
  have vd': "dsxaux' n cs_R cs_L args t ?da ?al"
    by (rule dsxaux'_add_new_table[OF vdj sR bR ty fy])
  have res0: "dsresh n cs_R args h [result_mmasaux args ?wa]
      [dsx_result (dargs cs_R cs_L args) ?da]"
    using dsresh_result[OF vd' vw'] by (simp add: P)
  have res: "dsresh n cs_R args h (result_mmasaux args ?wa # rs)
      (dsx_result (dargs cs_R cs_L args) ?da # drs)"
    using dsresh_append[OF res0 S] by simp
  have P': "dsx_post ?da = h" using P by simp
  have E': "meval_since args (result_mmasaux args ?wa # rs) (xs, ys, tss, False) ?wa
      = (zs, buf', aux')" using E by (simp add: Let_def)
  have D': "dsx_eval_since (dargs cs_R cs_L args)
      (dsx_result (dargs cs_R cs_L args) ?da # drs)
      (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys, tss, False) ?da = (dzs, dbuf', daux')"
    using D unfolding dbuf by (simp add: Let_def)
  have R': "dsince_rel n cs_R cs_L args tw ?wa ?da (xs, ys, tss, False)
      (map (dtabc n cs_L) xs, map (dtabc n cs_R) ys, tss, False)"
    by (rule dsince_relI[OF vw' vd']) (use lx ly st ct in auto)
  show ?case by (rule IH[OF refl E' D' R' P' res])
qed (all \<open>frule dsince_relD_buf, simp add: rev_map,
       (intro conjI)?, (rule dsresh_rev'; assumption)?\<close>)

text \<open>
  The simulation itself.  Every case is one theorem of @{theory MFODL_Monitor_Dense.Dense}
  applied pointwise to the operand's output list, with @{const produces} supplying the
  operand well-formedness and @{thm produces_next} re-establishing it for the successor.
\<close>

text \<open>
  The induction is over the derivation of the simulation, which gives the statement for an
  operand's own derivation.  A node that re-enters the evaluator on an operand's \<^emph>\<open>successor\<close>
  state -- the freeze does -- needs it for a derivation that is not a sub-derivation, so the
  statement carries a bound \<open>NN\<close> on the formula's size and an assumption \<open>Q\<close> giving
  it below that bound.  \<open>dsim_deval_bound\<close> closes the loop by induction on the
  bound, and \<open>dsim_deval\<close> instantiates it.
\<close>

text \<open>
  The recursive let runs its bound formula against databases it builds itself, feeding the
  previous round's output back under the bound predicate.  That operand sits at its own full
  frame, where a dense table \<^emph>\<open>is\<close> the sparse one, so the two runs produce literally the same
  lists and their states stay in step round by round.  The guard that rejects a round in which
  the formula's size changed never fires on either side, because neither evaluator changes its
  formula's size.
\<close>

lemma letpast_meval0_rel:
  assumes Q: "\<And>tw' \<chi>d \<chi> ts' db' zs' \<chi>'. size \<chi> < NN \<Longrightarrow> dsim m [0..<m] tw' \<chi>d \<chi> \<Longrightarrow>
      wf_db db' \<Longrightarrow> sorted ts' \<Longrightarrow> (\<forall>t \<in> set ts'. tw' \<le> t) \<Longrightarrow>
      meval j m ts' db' \<chi> = (zs', \<chi>') \<Longrightarrow>
      \<exists>\<chi>d'. deval j ts' db' \<chi>d = (zs', \<chi>d') \<and> dsim m [0..<m] (dnext tw' ts') \<chi>d' \<chi>'"
  shows "letpast_meval0 (meval j m) J i ys xs q ts db \<phi> = (zs, i', bo, \<phi>') \<Longrightarrow>
    snd q = m \<Longrightarrow> size \<phi> < NN \<Longrightarrow> dsim m [0..<m] tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
    (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> list_all (ftable m {0..<m}) ys \<Longrightarrow>
    list_all (ftable m {0..<m}) xs \<Longrightarrow>
    list_all (ftable m {0..<m}) zs \<and> (\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y) \<and>
      (\<exists>\<phi>d'. letpast_meval0 (deval j) J i ys xs q ts db \<phi>d = (zs, i', bo, \<phi>d')
        \<and> dsim m [0..<m] (dnext tw ts) \<phi>d' \<phi>')"
proof (induct "meval j m" J i ys xs q ts db \<phi> arbitrary: zs i' bo \<phi>' tw \<phi>d
    rule: letpast_meval0.induct)
  case (1 J i ys xs q ts db \<phi>)
  note IH = 1(1) and E = 1(2) and SQ = 1(3) and SZ = 1(4) and SIM = 1(5) and W = 1(6)
    and S = 1(7) and B = 1(8) and LY = 1(9) and LX = 1(10)
  obtain ys' \<phi>2 where ev: "meval j m ts (Mapping.update q xs db) \<phi> = (ys', \<phi>2)"
    by (cases "meval j m ts (Mapping.update q xs db) \<phi>")
  have wu: "wf_db (Mapping.update q xs db)"
    by (rule wf_db_update'[OF W]) (use LX SQ in simp)
  obtain \<phi>d2 where dv: "deval j ts (Mapping.update q xs db) \<phi>d = (ys', \<phi>d2)"
    and s2: "dsim m [0..<m] (dnext tw ts) \<phi>d2 \<phi>2"
    using Q[OF SZ SIM wu S B ev] by blast
  have ty: "list_all (ftable m {0..<m}) ys'"
    using dsim_produces[OF SIM] by (intro produces_tables[OF _ wu S B ev]) simp
  have same: "\<not> size \<phi>2 \<noteq> size \<phi>"
    using default_maux.size_snd_meval[of j m ts "Mapping.update q xs db" \<phi>] ev by simp
  have dsame: "\<not> size \<phi>d2 \<noteq> size \<phi>d"
    using size_snd_deval[of j ts "Mapping.update q xs db" \<phi>d] dv by simp
  have szp: "size \<phi>2 < NN" using same SZ by simp
  show ?case
  proof (cases ys')
    case Nil
    have "zs = ys @ ys' \<and> i' = i + length xs \<and> bo = None \<and> \<phi>' = \<phi>2"
      using E ev same Nil by (simp add: letpast_meval0.simps)
    moreover have "letpast_meval0 (deval j) J i ys xs q ts db \<phi>d
        = (ys @ ys', i + length xs, None, \<phi>d2)"
      using dv dsame Nil by (simp add: letpast_meval0.simps)
    ultimately show ?thesis using s2 LY ty by auto
  next
    case (Cons y r)
    show ?thesis
    proof (cases "J \<le> Suc (i + length xs)")
      case True
      have "zs = ys @ ys' \<and> i' = i + length xs \<and> bo = Some y \<and> \<phi>' = \<phi>2"
        using E ev same Cons True by (simp add: letpast_meval0.simps)
      moreover have "letpast_meval0 (deval j) J i ys xs q ts db \<phi>d
          = (ys @ ys', i + length xs, Some y, \<phi>d2)"
        using dv dsame Cons True by (simp add: letpast_meval0.simps)
      ultimately show ?thesis using s2 LY ty Cons by auto
    next
      case cont: False
      have e': "letpast_meval0 (meval j m) J (i + length xs) (ys @ ys') ys' q []
          (Mapping.map_values (\<lambda>_ _. []) db) \<phi>2 = (zs, i', bo, \<phi>')"
        using E ev same Cons cont by (simp add: letpast_meval0.simps)
      have d': "letpast_meval0 (deval j) J i ys xs q ts db \<phi>d
          = letpast_meval0 (deval j) J (i + length xs) (ys @ ys') ys' q []
              (Mapping.map_values (\<lambda>_ _. []) db) \<phi>d2"
        using dv dsame Cons cont by (simp add: letpast_meval0.simps)
      have "list_all (ftable m {0..<m}) zs \<and> (\<forall>y. bo = Some y \<longrightarrow> ftable m {0..<m} y) \<and>
          (\<exists>\<phi>d''. letpast_meval0 (deval j) J (i + length xs) (ys @ ys') ys' q []
            (Mapping.map_values (\<lambda>_ _. []) db) \<phi>d2 = (zs, i', bo, \<phi>d'')
          \<and> dsim m [0..<m] (dnext (dnext tw ts) []) \<phi>d'' \<phi>')"
        by (rule IH[OF ev[symmetric] refl same Cons cont e' SQ szp s2
              wf_db_map_values_empty]) (use LY ty in auto)
      then show ?thesis using d' by (auto simp: dnext_def)
    qed
  qed
qed

theorem dsim_deval_N:
  assumes Q: "\<And>n' cs' tw' \<phi>d' \<chi> j' ts' db' xs' \<chi>'. size \<chi> < NN \<Longrightarrow> dsim n' cs' tw' \<phi>d' \<chi> \<Longrightarrow>
      wf_db db' \<Longrightarrow> sorted ts' \<Longrightarrow> (\<forall>t \<in> set ts'. tw' \<le> t) \<Longrightarrow>
      meval j' n' ts' db' \<chi> = (xs', \<chi>') \<Longrightarrow>
      \<exists>\<phi>d''. deval j' ts' db' \<phi>d' = (map (dtabc n' cs') xs', \<phi>d'')
        \<and> dsim n' cs' (dnext tw' ts') \<phi>d'' \<chi>'"
  shows "dsim n cs tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> size \<phi> \<le> NN \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc n cs) xs, \<phi>d')
     \<and> dsim n cs (dnext tw ts) \<phi>d' \<phi>'"
proof (induct arbitrary: j ts db xs \<phi>' rule: dsim.induct)
  case (DsRel n cs tw rel)
  note wf = DsRel.hyps(1) and p = DsRel.hyps(2) and t = DsRel.hyps(3)
    and w = DsRel.prems(1) and sts = DsRel.prems(2)
    and mts = DsRel.prems(3) and m = DsRel.prems(4)
  have x: "xs = replicate (length ts) rel" and f: "\<phi>' = mformula.MRel rel" using m by simp_all
  show ?case using wf produces_next[OF p w sts mts m] t f by (simp add: x f dsim.DsRel)
next
  case (DsPredC n cs tw e tms)
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
    show ?thesis using wf pr tm cse produces_next[OF pr w sts mts m] None x f
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
    show ?thesis using wf pr tm cse produces_next[OF pr w sts mts m] Some x f mp
      by (auto intro!: dsim.DsPredC)
  qed
next
  case (DsPredS n cs tw e tms)
  note wf = DsPredS.hyps(1) and pr = DsPredS.hyps(2) and sp = DsPredS.hyps(3)
    and cse = DsPredS.hyps(4) and w = DsPredS.prems(1) and sts = DsPredS.prems(2)
    and mts = DsPredS.prems(3) and m = DsPredS.prems(4)
  have f: "\<phi>' = mformula.MPred e tms Simple" using m by simp
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) empty_table"
      using m None by (simp add: empty_table_def)
    show ?thesis using wf pr sp cse produces_next[OF pr w sts mts m] None x f
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
    show ?thesis using wf pr sp cse produces_next[OF pr w sts mts m] Some x f mp
      by (auto intro!: dsim.DsPredS)
  qed
next
  case (DsPredM n cs tw e tms)
  note wf = DsPredM.hyps(1) and pr = DsPredM.hyps(2)
    and w = DsPredM.prems(1) and sts = DsPredM.prems(2)
    and mts = DsPredM.prems(3) and m = DsPredM.prems(4)
  have f: "\<phi>' = mformula.MPred e tms Match" using m by simp
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) empty_table"
      using m None by (simp add: empty_table_def)
    show ?thesis using wf pr produces_next[OF pr w sts mts m] None x f
      by (auto intro!: dsim.DsPredM)
  next
    case (Some ys)
    have x: "xs = map (\<lambda>T. (\<lambda>g. Table.tabulate g 0 n) ` Option.these (match tms ` T)) ys"
      using m Some by simp
    have t: "list_all (ftable n (set cs)) xs" by (rule produces_tables[OF pr w sts mts m])
    have dt: "\<And>T. T \<in> set ys \<Longrightarrow> dmatch_table tms cs T
        = dtabc n cs ((\<lambda>g. Table.tabulate g 0 n) ` Option.these (match tms ` T))"
    proof (intro dmatch_table_dtabc)
      fix T x assume T: "T \<in> set ys" and x: "x \<in> T"
      have "table (length tms) {0..<length tms} T" by (rule wf_dbD[OF w Some T])
      then show "\<forall>a \<in> set x. a \<noteq> None" using x by (auto simp: table_def wf_tuple_def in_set_conv_nth)
    next
      fix T g assume T: "T \<in> set ys" and g: "g \<in> Option.these (match tms ` T)"
      have "table n (set cs) ((\<lambda>g. Table.tabulate g 0 n) ` Option.these (match tms ` T))"
        using t T unfolding x by (auto simp: list_all_iff)
      then have "wf_tuple n (set cs) (Table.tabulate g 0 n)" using g by (auto simp: table_def)
      then show "\<forall>c \<in> set cs. g c \<noteq> None" using wf by (auto simp: wf_tuple_def)
    qed (use wf in simp_all)
    have mp: "map (dmatch_table tms cs) ys
        = map (dtabc n cs) (map (\<lambda>T. (\<lambda>g. Table.tabulate g 0 n) ` Option.these (match tms ` T)) ys)"
      unfolding map_map by (intro map_cong[OF refl]) (simp add: dt)
    show ?thesis using wf pr produces_next[OF pr w sts mts m] Some x f mp
      by (auto intro!: dsim.DsPredM)
  qed
next
  case (DsAndRel n cs tw \<phi> t1 p c t2 \<phi>d)
  note wf = DsAndRel.hyps(1) and pr = DsAndRel.hyps(2) and sim = DsAndRel.hyps(3)
    and IH = DsAndRel.hyps(4) and fv1 = DsAndRel.hyps(5) and fv2 = DsAndRel.hyps(6)
    and w = DsAndRel.prems(1) and sts = DsAndRel.prems(2)
    and mts = DsAndRel.prems(3) and m = DsAndRel.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (Set.filter (eval_constraint (t1, p, c, t2))) ys"
    and f: "\<phi>' = mformula.MAndRel \<psi>' (t1, p, c, t2)" using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsAndRel.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have t: "list_all (ftable n (set cs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
  have pc: "\<And>r. r \<in> set ys \<Longrightarrow>
      dtabc n cs (Set.filter (eval_constraint (t1, p, c, t2)) r)
        = Set.filter (deval_constraint (reindex_constraint cs (t1, p, c, t2))) (dtabc n cs r)"
    using t wf fv1 fv2 by (intro deval_constraint_reindex) (auto simp: list_all_iff)
  have "map (Set.filter (deval_constraint (reindex_constraint cs (t1, p, c, t2))))
        (map (dtabc n cs) ys) = map (dtabc n cs) xs"
    unfolding x map_map
  proof (intro map_cong refl)
    fix r assume r: "r \<in> set ys"
    show "(Set.filter (deval_constraint (reindex_constraint cs (t1, p, c, t2))) \<circ> dtabc n cs) r
        = (dtabc n cs \<circ> Set.filter (eval_constraint (t1, p, c, t2))) r"
      using pc[OF r] by simp
  qed
  then show ?case using d sim' produces_next[OF pr w sts mts m] wf fv1 fv2 f
    by (auto intro!: dsim.DsAndRel)
next
  case (DsNeg n tw \<phi> \<phi>d)
  note pr = DsNeg.hyps(1) and sim = DsNeg.hyps(2) and IH = DsNeg.hyps(3)
    and w = DsNeg.prems(1) and sts = DsNeg.prems(2)
    and mts = DsNeg.prems(3) and m = DsNeg.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. if r = empty_table then unit_table n else empty_table) ys"
    and f: "\<phi>' = mformula.MNeg \<psi>'" using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsNeg.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n []) ys, \<psi>d')"
    and sim': "dsim n [] (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have "map (\<lambda>r. if r = empty_table then unit_table 0 else empty_table) (map (dtabc n []) ys)
      = map (dtabc n []) xs"
    unfolding x by (simp add: dtabc_neg)
  then show ?case using d sim' produces_next[OF pr w sts mts m] f by (auto intro!: dsim.DsNeg)
next
  case (DsExists n cs tw \<phi> ccs \<phi>d b)
  note wf = DsExists.hyps(1) and pr = DsExists.hyps(2) and sim = DsExists.hyps(3)
    and IH = DsExists.hyps(4) and cse = DsExists.hyps(5) and be = DsExists.hyps(6)
    and w = DsExists.prems(1) and sts = DsExists.prems(2)
    and mts = DsExists.prems(3) and m = DsExists.prems(4)
  obtain ys \<psi>' where e: "meval j (Suc n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (Suc n) ts db \<phi>")
  have x: "xs = map (\<lambda>r. tl ` r) ys" and f: "\<phi>' = mformula.MExists \<psi>'" using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsExists.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (Suc n) ccs) ys, \<psi>d')"
    and sim': "dsim (Suc n) ccs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have wfc: "wf_cols (Suc n) ccs" by (rule dsim_wf_cols[OF sim])
  have t: "list_all (ftable (Suc n) (set ccs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
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
  then show ?case using d sim' produces_next[OF pr w sts mts m] wf cse be f
    by (auto intro!: dsim.DsExists)
next
  case (DsOr n cs tw \<phi> \<psi> buf \<phi>d \<psi>d dbuf)
  note wf = DsOr.hyps(1) and pr = DsOr.hyps(2) and sim1 = DsOr.hyps(3) and IH1 = DsOr.hyps(4)
    and sim2 = DsOr.hyps(5) and IH2 = DsOr.hyps(6) and bf = DsOr.hyps(7)
    and w = DsOr.prems(1) and sts = DsOr.prems(2)
    and mts = DsOr.prems(3) and m = DsOr.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MOr \<phi>2 \<psi>2 buf2" using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsOr.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs) as, \<phi>d2)"
    and s1: "dsim n cs (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable n (set cs)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
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
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr w sts mts m] wf x f
    by (auto intro!: dsim.DsOr)
next
  case (DsAnd n cs tw cs1 \<phi> pos cs2 \<psi> buf \<phi>d \<psi>d pl dbuf)
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
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsAnd.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs1) as, \<phi>d2)"
    and s1: "dsim n cs1 (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs2) bs, \<psi>d2)"
    and s2: "dsim n cs2 (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have so1: "sorted_wrt (<) cs1" and b1: "\<forall>c \<in> set cs1. c < n"
    using dsim_wf_cols[OF sim1] by (blast dest: conjunct1 conjunct2)+
  have so2: "sorted_wrt (<) cs2" and b2: "\<forall>c \<in> set cs2. c < n"
    using dsim_wf_cols[OF sim2] by (blast dest: conjunct1 conjunct2)+
  have ta: "list_all (ftable n (set cs1)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable n (set cs2)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
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
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr w sts mts m] wf cse ple neg x f
    by (auto intro!: dsim.DsAnd)
next
  case (DsPrev n cs tw I \<phi> first buf nts \<phi>d dbuf)
  note wf = DsPrev.hyps(1) and pr = DsPrev.hyps(2) and sim = DsPrev.hyps(3)
    and IH = DsPrev.hyps(4) and lb = DsPrev.hyps(5) and be = DsPrev.hyps(6)
    and w = DsPrev.prems(1) and sts = DsPrev.prems(2)
    and mts = DsPrev.prems(3) and m = DsPrev.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsPrev.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have t: "list_all (ftable n (set cs)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
  have tb: "list_all (ftable n (set cs)) (buf @ ys)" using lb t by simp
  show ?case
  proof (cases "first \<and> ts = []")
    case True
    have x: "xs = []" and f: "\<phi>' = mformula.MPrev I \<psi>' True (buf @ ys) (nts @ ts)"
      using m e True by simp_all
    show ?thesis using d be True x f sim' produces_next[OF pr w sts mts m] wf tb
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
    show ?thesis using d be False x f sim' produces_next[OF pr w sts mts m] wf tb' g'
      by (auto intro!: dsim.DsPrev)
  qed
next
  case (DsNext n cs tw I \<phi> first nts \<phi>d)
  note wf = DsNext.hyps(1) and pr = DsNext.hyps(2) and sim = DsNext.hyps(3)
    and IH = DsNext.hyps(4) and w = DsNext.prems(1) and sts = DsNext.prems(2)
    and mts = DsNext.prems(3) and m = DsNext.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsNext.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs) ys, \<psi>d')"
    and sim': "dsim n cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
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
  show ?case using d c' g' x f sim' produces_next[OF pr w sts mts m] wf
    by (auto intro!: dsim.DsNext)
next
  case (DsAnds n cs tw c0 css nss L buf Ld ps ns dbuf)
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
      by (rule dsims_tables[OF la0 l1 l2 w sts mts iL])
    then show "list_all (ftable n (set (?cs' ! i))) (map fst ?R ! i)"
      using iL by simp
  qed
  have szL: "\<And>i. i < length L \<Longrightarrow> size (L ! i) \<le> NN"
  proof -
    fix i assume i: "i < length L"
    have "size (L ! i) \<le> size_list size L"
      by (rule size_list_estimation'[OF nth_mem[OF i] order.refl])
    also have "size_list size L \<le> NN" by (rule order_trans[OF _ DsAnds.prems(5)]) simp
    finally show "size (L ! i) \<le> NN" .
  qed
  have la1: "\<forall>i < length L. dsim n (?cs' ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (?cs' ! i)) as, \<psi>d')
            \<and> dsim n (?cs' ! i) (dnext tw ts) \<psi>d' \<psi>'))"
    using la w sts mts szL by blast
  have dlr: "length (map (deval j ts db) Ld) = length L \<and>
      map fst (map (deval j ts db) Ld)
        = map2 (\<lambda>c y. map (dtabc n c) y) ?cs'
            (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (?cs' ! i) (dnext tw ts) (map snd (map (deval j ts db) Ld) ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF l1 l2 la1])
  have dl0: "length (map (deval j ts db) Ld) = length L" using dlr by blast
  have dl: "map fst (map (deval j ts db) Ld)
      = map2 (\<lambda>c y. map (dtabc n c) y) ?cs' (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (?cs' ! i) (dnext tw ts) (map snd (map (deval j ts db) Ld) ! i)
      (snd (meval j n ts db (L ! i)))" using dlr by blast
  \<comment> \<open>the buffer\<close>
  have badd: "dbufn n ?cs' (mbufn_add (map fst ?R) buf)
      (mbufn_add (map fst (map (deval j ts db) Ld)) dbuf)"
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
        ([] :: event_data table list) (mbufn_add (map fst (map (deval j ts db) Ld)) dbuf)
      = (map (dtabc n cs) zs, dbuf')"
    and bf': "dbufn n ?cs' buf' dbuf'"
    using dbufn_take[OF badd step g0] by blast
  have dv: "deval j ts db (DAnds ps ns Ld dbuf)
      = (map (dtabc n cs) xs, DAnds ps ns (map snd (map (deval j ts db) Ld)) dbuf')"
    using dt x by (simp add: Let_def del: mbufn_take.simps)
  have s2: "dsim n cs (dnext tw ts) (DAnds ps ns (map snd (map (deval j ts db) Ld)) dbuf')
      (mformula.MAnds (set c0 # map set css) (map set nss) (map snd ?R) buf')"
  proof (rule dsim.DsAnds)
    show "wf_cols n cs" by (rule wf)
    show "produces n (set cs) (dnext tw ts)
        (mformula.MAnds (set c0 # map set css) (map set nss) (map snd ?R) buf')"
      using produces_next[OF pr w sts mts m] fe by simp
    show "\<forall>i < length (map snd ?R). dsim n (?cs' ! i) (dnext tw ts)
        (map snd (map (deval j ts db) Ld) ! i) (map snd ?R ! i)"
    proof (intro allI impI)
      fix i assume "i < length (map snd ?R)"
      then have iL: "i < length L" by simp
      show "dsim n (?cs' ! i) (dnext tw ts) (map snd (map (deval j ts db) Ld) ! i) (map snd ?R ! i)"
        using dl2 iL by simp
    qed
    show "length (map snd (map (deval j ts db) Ld)) = length (map snd ?R)"
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
  case (DsAgg n cs tw args \<phi> gcols \<phi>d y)
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
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsAgg.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc (?mm + n) ?cc) ys, \<psi>d')"
    and sim': "dsim (?mm + n) ?cc (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have t: "list_all (ftable (?mm + n) (set ?cc)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
  have "map (dagg (aggargs_g0 args) (aggargs_\<omega> args) (reindex_trm ?cc (aggargs_f args)) ?mm
          (ins_pos gcols y)) (map (dtabc (?mm + n) ?cc) ys) = map (dtabc n cs) xs"
    unfolding x cse using t wg yn yg fv g0 ne ye
    by (intro nth_equalityI)
      (auto simp: list_all_iff eval_aggargs_def dagg_eval_agg)
  then show ?case using d sim' produces_next[OF pr w sts mts m] wf wg ne ye yn yg g0 fv cse f
    by (auto intro!: dsim.DsAgg)
next
  case (DsSince n cs tw args \<phi> \<psi> buf aux cs_L \<phi>d \<psi>d dags daux dbuf)
  note wf = DsSince.hyps(1) and pr = DsSince.hyps(2)
    and sim1 = DsSince.hyps(3) and IH1 = DsSince.hyps(4)
    and sim2 = DsSince.hyps(5) and IH2 = DsSince.hyps(6)
    and wfL = DsSince.hyps(7) and sub = DsSince.hyps(8) and agg = DsSince.hyps(9)
    and an = DsSince.hyps(10) and aL = DsSince.hyps(11) and aR = DsSince.hyps(12)
    and dag = DsSince.hyps(13) and rel = DsSince.hyps(14) and nag = DsSince.hyps(15)
    and w = DsSince.prems(1) and sts = DsSince.prems(2)
    and mts = DsSince.prems(3) and m = DsSince.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 an by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsSince.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs_L) as, \<phi>d2)"
    and s1: "dsim n cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable n (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs dbuf2 daux2 where d3: "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)"
    by (cases "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) ts dbuf) daux")
  have radd: "dsince_rel n cs cs_L args (dnext tw ts) aux daux (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) ts dbuf)"
    by (rule dsince_rel_add[OF rel ta tb sts mts])
  have d3': "dsx_eval_since (dargs cs cs_L args) (map (dtabc n cs) [])
      (mbuf2S_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)" using d3 unfolding dag by simp
  have post: "dsx_post daux = id" using nag by (simp add: dsx_post_eq)
  have step0: "dsres n cs args zs dzs \<and>
      dsince_rel n cs cs_L args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using eval_since_rel[OF _ _ _ sub an aL aR e3 d3' radd refl] wf wfL
    by (simp add: post dsresh_id)
  have nag2: "dsx_agg daux2 = None" using dsx_agg_eval_since[OF d3] nag by simp
  have step: "dzs = map (dtabc n cs) zs \<and>
      dsince_rel n cs cs_L args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using step0 dsres_none[OF agg] by blast
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DSince dags \<phi>d \<psi>d dbuf daux)
        = (map (dtabc n cs) xs, DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2)"
      using d1 d2 d3 step x by simp
    show "dsim n cs (dnext tw ts) (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsSince[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 wfL sub agg an aL aR
            dag]) (use step nag2 in simp_all)
  qed
next
  case (DsUntil n cs tw args \<phi> \<psi> buf nts t aux cs_L \<phi>d \<psi>d dags msk daux dbuf)
  note wf = DsUntil.hyps(1) and pr = DsUntil.hyps(2)
    and sim1 = DsUntil.hyps(3) and IH1 = DsUntil.hyps(4)
    and sim2 = DsUntil.hyps(5) and IH2 = DsUntil.hyps(6)
    and wfL = DsUntil.hyps(7) and sub = DsUntil.hyps(8) and agg = DsUntil.hyps(9)
    and an = DsUntil.hyps(10) and aL = DsUntil.hyps(11) and aR = DsUntil.hyps(12)
    and dag = DsUntil.hyps(13) and pe = DsUntil.hyps(14) and rel = DsUntil.hyps(15)
    and nag = DsUntil.hyps(16)
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
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsUntil.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs_L) as, \<phi>d2)"
    and s1: "dsim n cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable n (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) dbuf) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) dbuf) t (nts @ ts)")
  obtain dzs daux2 where d4: "dux_eval dags dnt daux1 = (dzs, daux2)"
    by (cases "dux_eval dags dnt daux1")
  have post: "dux_post daux = id" using nag by (simp add: dux_post_eq)
  have step: "dsresh n cs args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (dtabc n cs_L) (fst buf1), map (dtabc n cs) (snd buf1)) \<and>
      duntil_rel n cs cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF _ _ _ sub an aL aR rel ta tb sts mts e3
        d3[unfolded dag pe] e4 d4[unfolded dag]]) (use wf wfL in auto)
  have dres: "dsres n cs args zs dzs"
    using step unfolding post by (simp add: dsresh_def dsres_def)
  have nag2: "dux_agg daux2 = None"
    using dux_agg_mbuf2t_take[OF d3[unfolded dag pe]] dux_agg_eval[of dags dnt daux1]
      d4 nag by simp
  have dz: "dzs = map (dtabc n cs) zs" using dres dsres_none[OF agg] by blast
  have dn: "dnt = nt" and dns: "dnts1 = nts1"
    and rel': "duntil_rel n cs cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
        = (map (dtabc n cs) xs, DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2)"
      using d1 d2 d3 d4 dz dn dns x by simp
    show "dsim n cs (dnext tw ts) (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsUntil[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 wfL sub agg an aL aR
            dag pe rel' nag2])
  qed
next
  case (DsSinceAgg n cs tw args \<phi> \<psi> buf aux nn cs_L \<phi>d cs_R \<psi>d ag dags daux dbuf gcols y)
  note wf = DsSinceAgg.hyps(1) and pr = DsSinceAgg.hyps(2)
    and sim1 = DsSinceAgg.hyps(3) and IH1 = DsSinceAgg.hyps(4)
    and sim2 = DsSinceAgg.hyps(5) and IH2 = DsSinceAgg.hyps(6)
    and wfL = DsSinceAgg.hyps(7) and sub = DsSinceAgg.hyps(8) and agg = DsSinceAgg.hyps(9)
    and an = DsSinceAgg.hyps(10) and aL = DsSinceAgg.hyps(11) and aR = DsSinceAgg.hyps(12)
    and dag = DsSinceAgg.hyps(13) and rel = DsSinceAgg.hyps(14)
    and wg = DsSinceAgg.hyps(15) and agn = DsSinceAgg.hyps(16) and ye = DsSinceAgg.hyps(17)
    and yn = DsSinceAgg.hyps(18) and yg = DsSinceAgg.hyps(19) and g0 = DsSinceAgg.hyps(20)
    and fv = DsSinceAgg.hyps(21) and nne = DsSinceAgg.hyps(22) and cRe = DsSinceAgg.hyps(23)
    and cse = DsSinceAgg.hyps(24) and nag = DsSinceAgg.hyps(25)
    and w = DsSinceAgg.prems(1) and sts = DsSinceAgg.prems(2)
    and mts = DsSinceAgg.prems(3) and m = DsSinceAgg.prems(4)
  let ?ag = "dagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 an by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsSinceAgg.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc nn cs_L) as, \<phi>d2)"
    and s1: "dsim nn cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc nn cs_R) bs, \<psi>d2)"
    and s2: "dsim nn cs_R (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable nn (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable nn (set cs_R)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs dbuf2 daux2 where d3: "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)"
    by (cases "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf) daux")
  have radd: "dsince_rel nn cs_R cs_L args (dnext tw ts) aux daux (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf)"
    by (rule dsince_rel_add[OF rel ta tb sts mts])
  have d3': "dsx_eval_since (dargs cs_R cs_L args) (map (dtabc nn cs_R) [])
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)" using d3 unfolding dag by simp
  have wfR: "wf_cols nn cs_R" by (rule dsim_wf_cols[OF sim2])
  have post: "dsx_post daux = id" using nag by (simp add: dsx_post_eq)
  have step: "dsres nn cs_R args zs dzs \<and>
      dsince_rel nn cs_R cs_L args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using eval_since_rel[OF _ _ _ sub an aL aR e3 d3' radd refl] wfR wfL
    by (simp add: post dsresh_id)
  have nag2: "dsx_agg daux2 = None" using dsx_agg_eval_since[OF d3] nag by simp
  have agc: "map ?ag dzs = map (dtabc n cs) xs"
  proof -
    obtain vs where v: "list_all (table nn (set cs_R)) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (dtabc nn cs_R) vs"
      using step unfolding dsres_def by blast
    show ?thesis unfolding x v(2) v(3)
      using v(1) wg yn yg fv g0 agn ye
      by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg cse cRe nne dagg_eval_agg)
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
          (length (aggargs_tys ag)) (ins_pos gcols y) (DSince dags \<phi>d \<psi>d dbuf daux))
        = (map (dtabc n cs) xs, DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
            (reindex_trm cs_R (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
            (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2))"
      using d1 d2 d3 agc by simp
    show "dsim n cs (dnext tw ts) (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
          (reindex_trm cs_R (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
          (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2)) \<phi>'"
      unfolding f
      by (rule dsim.DsSinceAgg[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 wfL sub
            agg an aL aR dag _ wg agn ye yn yg g0 fv nne cRe cse]) (use step nag2 in simp_all)
  qed
next
  case (DsSinceFused n cs tw args \<phi> \<psi> buf aux nn cs_L \<phi>d cs_R \<psi>d ag dags daux dbuf gcols y)
  note wf = DsSinceFused.hyps(1) and pr = DsSinceFused.hyps(2)
    and sim1 = DsSinceFused.hyps(3) and IH1 = DsSinceFused.hyps(4)
    and sim2 = DsSinceFused.hyps(5) and IH2 = DsSinceFused.hyps(6)
    and wfL = DsSinceFused.hyps(7) and sub = DsSinceFused.hyps(8) and agg = DsSinceFused.hyps(9)
    and an = DsSinceFused.hyps(10) and aL = DsSinceFused.hyps(11) and aR = DsSinceFused.hyps(12)
    and dag = DsSinceFused.hyps(13) and rel = DsSinceFused.hyps(14)
    and wg = DsSinceFused.hyps(15) and agn = DsSinceFused.hyps(16) and ye = DsSinceFused.hyps(17)
    and yn = DsSinceFused.hyps(18) and yg = DsSinceFused.hyps(19) and g0 = DsSinceFused.hyps(20)
    and fv = DsSinceFused.hyps(21) and nne = DsSinceFused.hyps(22) and cRe = DsSinceFused.hyps(23)
    and cse = DsSinceFused.hyps(24) and nag = DsSinceFused.hyps(25)
    and w = DsSinceFused.prems(1) and sts = DsSinceFused.prems(2)
    and mts = DsSinceFused.prems(3) and m = DsSinceFused.prems(4)
  let ?ag = "dagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 an by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsSinceFused.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc nn cs_L) as, \<phi>d2)"
    and s1: "dsim nn cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc nn cs_R) bs, \<psi>d2)"
    and s2: "dsim nn cs_R (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable nn (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable nn (set cs_R)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs dbuf2 daux2 where d3: "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)"
    by (cases "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf) daux")
  have radd: "dsince_rel nn cs_R cs_L args (dnext tw ts) aux daux (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf)"
    by (rule dsince_rel_add[OF rel ta tb sts mts])
  have d3': "dsx_eval_since (dargs cs_R cs_L args) (map (dtabc nn cs_R) [])
      (mbuf2S_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)" using d3 unfolding dag by simp
  have wfR: "wf_cols nn cs_R" by (rule dsim_wf_cols[OF sim2])
  have post: "dsx_post daux = ?ag" using nag by (simp add: dsx_post_eq)
  have step: "dsresh nn cs_R args ?ag zs dzs \<and>
      dsince_rel nn cs_R cs_L args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using eval_since_rel[OF _ _ _ sub an aL aR e3 d3' radd refl] wfR wfL
    by (simp add: post)
  have nag2: "dsx_agg daux2 = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
      length (aggargs_tys ag), ins_pos gcols y)"
    using dsx_agg_eval_since[OF d3] nag by simp
  have agc: "dzs = map (dtabc n cs) xs"
  proof -
    obtain vs where v: "list_all (table nn (set cs_R)) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (?ag \<circ> dtabc nn cs_R) vs"
      using step unfolding dsresh_def by blast
    show ?thesis unfolding x v(2) v(3)
      using v(1) wg yn yg fv g0 agn ye
      by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg cse cRe nne dagg_eval_agg)
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DSince dags \<phi>d \<psi>d dbuf daux)
        = (map (dtabc n cs) xs, DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2)"
      using d1 d2 d3 agc by simp
    show "dsim n cs (dnext tw ts) (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsSinceFused[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 wfL sub
            agg an aL aR dag _ wg agn ye yn yg g0 fv nne cRe cse]) (use step nag2 in simp_all)
  qed
next
  case (DsUntilAgg n cs tw args \<phi> \<psi> buf nts t aux nn cs_L \<phi>d cs_R \<psi>d ag dags msk daux dbuf
      gcols y)
  note wf = DsUntilAgg.hyps(1) and pr = DsUntilAgg.hyps(2)
    and sim1 = DsUntilAgg.hyps(3) and IH1 = DsUntilAgg.hyps(4)
    and sim2 = DsUntilAgg.hyps(5) and IH2 = DsUntilAgg.hyps(6)
    and wfL = DsUntilAgg.hyps(7) and sub = DsUntilAgg.hyps(8) and agg = DsUntilAgg.hyps(9)
    and an = DsUntilAgg.hyps(10) and aL = DsUntilAgg.hyps(11) and aR = DsUntilAgg.hyps(12)
    and dag = DsUntilAgg.hyps(13) and pe = DsUntilAgg.hyps(14) and rel = DsUntilAgg.hyps(15)
    and wg = DsUntilAgg.hyps(16) and agn = DsUntilAgg.hyps(17) and ye = DsUntilAgg.hyps(18)
    and yn = DsUntilAgg.hyps(19) and yg = DsUntilAgg.hyps(20) and g0 = DsUntilAgg.hyps(21)
    and fv = DsUntilAgg.hyps(22) and nne = DsUntilAgg.hyps(23) and cRe = DsUntilAgg.hyps(24)
    and cse = DsUntilAgg.hyps(25) and nag = DsUntilAgg.hyps(26)
    and w = DsUntilAgg.prems(1) and sts = DsUntilAgg.prems(2)
    and mts = DsUntilAgg.prems(3) and m = DsUntilAgg.prems(4)
  let ?ag = "dagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j nn ts db \<psi>")
  obtain aux1 buf1 nt nts1 where e3: "mbuf2t_take (add_new_muaux_dq args) aux
      (mbuf2_add as bs buf) t (nts @ ts) = (aux1, buf1, nt, nts1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ ts)")
  obtain zs aux2 where e4: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    by (cases "eval_muaux_dq args nt aux1")
  have x: "xs = zs"
    and f: "\<phi>' = mformula.MUntil args \<phi>2 \<psi>2 buf1 nts1 nt aux2"
    using m e1 e2 e3 e4 an by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsUntilAgg.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc nn cs_L) as, \<phi>d2)"
    and s1: "dsim nn cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc nn cs_R) bs, \<psi>d2)"
    and s2: "dsim nn cs_R (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable nn (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable nn (set cs_R)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) dbuf) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) dbuf) t (nts @ ts)")
  obtain dzs daux2 where d4: "dux_eval dags dnt daux1 = (dzs, daux2)"
    by (cases "dux_eval dags dnt daux1")
  have wfR: "wf_cols nn cs_R" by (rule dsim_wf_cols[OF sim2])
  have post: "dux_post daux = id" using nag by (simp add: dux_post_eq)
  have step: "dsresh nn cs_R args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (dtabc nn cs_L) (fst buf1), map (dtabc nn cs_R) (snd buf1)) \<and>
      duntil_rel nn cs_R cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF _ _ _ sub an aL aR rel ta tb sts mts e3
        d3[unfolded dag pe] e4 d4[unfolded dag]]) (use wfR wfL in auto)
  have dres: "dsres nn cs_R args zs dzs"
    using step unfolding post by (simp add: dsresh_def dsres_def)
  have nag2: "dux_agg daux2 = None"
    using dux_agg_mbuf2t_take[OF d3[unfolded dag pe]] dux_agg_eval[of dags dnt daux1]
      d4 nag by simp
  have dn: "dnt = nt" and dns: "dnts1 = nts1"
    and rel': "duntil_rel nn cs_R cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  have agc: "map ?ag dzs = map (dtabc n cs) xs"
  proof -
    obtain vs where v: "list_all (table nn (set cs_R)) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (dtabc nn cs_R) vs"
      using dres unfolding dsres_def by blast
    show ?thesis unfolding x v(2) v(3)
      using v(1) wg yn yg fv g0 agn ye
      by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg cse cRe nne dagg_eval_agg)
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
          (length (aggargs_tys ag)) (ins_pos gcols y) (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux))
        = (map (dtabc n cs) xs, DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
            (reindex_trm cs_R (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
            (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2))"
      using d1 d2 d3 d4 agc dn dns by simp
    show "dsim n cs (dnext tw ts) (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
          (reindex_trm cs_R (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
          (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2)) \<phi>'"
      unfolding f
      by (rule dsim.DsUntilAgg[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 wfL sub
            agg an aL aR dag pe rel' wg agn ye yn yg g0 fv nne cRe cse nag2])
  qed
next
  case (DsUntilFused n cs tw args \<phi> \<psi> buf nts t aux nn cs_L \<phi>d cs_R \<psi>d ag dags msk daux dbuf
    gcols y)
  note wf = DsUntilFused.hyps(1) and pr = DsUntilFused.hyps(2)
    and sim1 = DsUntilFused.hyps(3) and IH1 = DsUntilFused.hyps(4)
    and sim2 = DsUntilFused.hyps(5) and IH2 = DsUntilFused.hyps(6)
    and wfL = DsUntilFused.hyps(7) and sub = DsUntilFused.hyps(8) and agg = DsUntilFused.hyps(9)
    and an = DsUntilFused.hyps(10) and aL = DsUntilFused.hyps(11) and aR = DsUntilFused.hyps(12)
    and dag = DsUntilFused.hyps(13) and pe = DsUntilFused.hyps(14) and rel = DsUntilFused.hyps(15)
    and wg = DsUntilFused.hyps(16) and agn = DsUntilFused.hyps(17) and ye = DsUntilFused.hyps(18)
    and yn = DsUntilFused.hyps(19) and yg = DsUntilFused.hyps(20) and g0 = DsUntilFused.hyps(21)
    and fv = DsUntilFused.hyps(22) and nne = DsUntilFused.hyps(23) and cRe = DsUntilFused.hyps(24)
    and cse = DsUntilFused.hyps(25) and nag = DsUntilFused.hyps(26)
    and w = DsUntilFused.prems(1) and sts = DsUntilFused.prems(2)
    and mts = DsUntilFused.prems(3) and m = DsUntilFused.prems(4)
  let ?ag = "dagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cs_R (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j nn ts db \<psi>")
  obtain aux1 buf1 nt nts1 where e3: "mbuf2t_take (add_new_muaux_dq args) aux
      (mbuf2_add as bs buf) t (nts @ ts) = (aux1, buf1, nt, nts1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ ts)")
  obtain zs aux2 where e4: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    by (cases "eval_muaux_dq args nt aux1")
  have x: "xs = zs"
    and f: "\<phi>' = mformula.MUntil args \<phi>2 \<psi>2 buf1 nts1 nt aux2"
    using m e1 e2 e3 e4 an by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsUntilFused.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc nn cs_L) as, \<phi>d2)"
    and s1: "dsim nn cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc nn cs_R) bs, \<psi>d2)"
    and s2: "dsim nn cs_R (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable nn (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable nn (set cs_R)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) dbuf) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc nn cs_L) as) (map (dtabc nn cs_R) bs) dbuf) t (nts @ ts)")
  obtain dzs daux2 where d4: "dux_eval dags dnt daux1 = (dzs, daux2)"
    by (cases "dux_eval dags dnt daux1")
  have wfR: "wf_cols nn cs_R" by (rule dsim_wf_cols[OF sim2])
  have post: "dux_post daux = ?ag" using nag by (simp add: dux_post_eq)
  have step: "dsresh nn cs_R args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (dtabc nn cs_L) (fst buf1), map (dtabc nn cs_R) (snd buf1)) \<and>
      duntil_rel nn cs_R cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF _ _ _ sub an aL aR rel ta tb sts mts e3
        d3[unfolded dag pe] e4 d4[unfolded dag]]) (use wfR wfL in auto)
  have nag2: "dux_agg daux2 = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cs_R (aggargs_f ag),
      length (aggargs_tys ag), ins_pos gcols y)"
    using dux_agg_mbuf2t_take[OF d3[unfolded dag pe]] dux_agg_eval[of dags dnt daux1]
      d4 nag by simp
  have dn: "dnt = nt" and dns: "dnts1 = nts1"
    and rel': "duntil_rel nn cs_R cs_L args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  have agc: "dzs = map (dtabc n cs) xs"
  proof -
    obtain vs where v: "list_all (table nn (set cs_R)) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (?ag \<circ> dtabc nn cs_R) vs"
      using step unfolding dsresh_def post by blast
    show ?thesis unfolding x v(2) v(3)
      using v(1) wg yn yg fv g0 agn ye
      by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg cse cRe nne dagg_eval_agg)
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
        = (map (dtabc n cs) xs, DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2)"
      using d1 d2 d3 d4 agc dn dns by simp
    show "dsim n cs (dnext tw ts) (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsUntilFused[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 wfL sub
            agg an aL aR dag pe rel' wg agn ye yn yg g0 fv nne cRe cse nag2])
  qed
next
  case (DsAndAssign n cs tw \<phi> y t cs0 \<phi>d)
  note wf = DsAndAssign.hyps(1) and pr = DsAndAssign.hyps(2) and sim = DsAndAssign.hyps(3)
    and IH = DsAndAssign.hyps(4) and yb = DsAndAssign.hyps(5)
    and ynn = DsAndAssign.hyps(6) and fv = DsAndAssign.hyps(7)
    and cse = DsAndAssign.hyps(8)
    and w = DsAndAssign.prems(1) and sts = DsAndAssign.prems(2)
    and mts = DsAndAssign.prems(3) and m = DsAndAssign.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. eval_assignment (y, t) ` r) ys"
    and f: "\<phi>' = mformula.MAndAssign \<psi>' (y, t)"
    using m e by (simp_all del: eval_assignment.simps)
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsAndAssign.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc n cs0) ys, \<psi>d')"
    and sim': "dsim n cs0 (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have tb: "list_all (ftable n (set cs0)) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
  have wf0: "wf_cols n cs0" by (rule dsim_wf_cols[OF sim])
  have pc: "\<And>r. r \<in> set ys \<Longrightarrow>
      dassign (ins_pos cs0 y) (reindex_trm cs0 t) (dtabc n cs0 r)
        = dtabc n cs (eval_assignment (y, t) ` r)"
    using tb wf0 yb ynn fv unfolding cse
    by (intro dassign_eval_assignment) (auto simp: list_all_iff)
  have mapeq: "map (dassign (ins_pos cs0 y) (reindex_trm cs0 t)) (map (dtabc n cs0) ys)
      = map (dtabc n cs) xs"
    unfolding x map_map
  proof (intro map_cong refl)
    fix r assume r: "r \<in> set ys"
    show "(dassign (ins_pos cs0 y) (reindex_trm cs0 t) \<circ> dtabc n cs0) r
        = (dtabc n cs \<circ> (\<lambda>r. eval_assignment (y, t) ` r)) r"
      using pc[OF r] by simp
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) \<phi>d)
        = (map (dtabc n cs) xs, DAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) \<psi>d')"
      using d mapeq by simp
    show "dsim n cs (dnext tw ts) (DAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) \<psi>d') \<phi>'"
      unfolding f
      by (rule dsim.DsAndAssign[OF wf produces_next[OF pr w sts mts m, unfolded f]
            sim' yb ynn fv cse])
  qed
next
  case (DsTP n cs tw mt i)
  note wf = DsTP.hyps(1) and pr = DsTP.hyps(2) and cse = DsTP.hyps(3)
    and w = DsTP.prems(1) and sts = DsTP.prems(2)
    and mts = DsTP.prems(3) and m = DsTP.prems(4)
  have x: "xs = map (\<lambda>x. eval_mtrm n mt (EInt (integer_of_nat x))) [i..<j]"
    and f: "\<phi>' = mformula.MTP mt j" using m by simp_all
  have b: "\<forall>c \<in> set (mtrm_dcols mt). c < n" using wf unfolding cse by simp
  have mapeq: "map (dtabc n cs) xs = map (\<lambda>x. dmtrm mt (EInt (integer_of_nat x))) [i..<j]"
    unfolding x map_map cse by (simp add: dtabc_eval_mtrm[OF b])
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DTP mt i) = (map (dtabc n cs) xs, DTP mt j)" using mapeq by simp
    show "dsim n cs (dnext tw ts) (DTP mt j) \<phi>'"
      unfolding f
      by (rule dsim.DsTP[OF wf produces_next[OF pr w sts mts m, unfolded f] cse])
  qed
next
  case (DsTS n cs tw mt)
  note wf = DsTS.hyps(1) and pr = DsTS.hyps(2) and cse = DsTS.hyps(3)
    and w = DsTS.prems(1) and sts = DsTS.prems(2)
    and mts = DsTS.prems(3) and m = DsTS.prems(4)
  have x: "xs = map (\<lambda>x. eval_mtrm n mt (EInt (integer_of_nat x))) ts"
    and f: "\<phi>' = mformula.MTS mt" using m by simp_all
  have b: "\<forall>c \<in> set (mtrm_dcols mt). c < n" using wf unfolding cse by simp
  have mapeq: "map (dtabc n cs) xs = map (\<lambda>x. dmtrm mt (EInt (integer_of_nat x))) ts"
    unfolding x map_map cse by (simp add: dtabc_eval_mtrm[OF b])
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DTS mt) = (map (dtabc n cs) xs, DTS mt)" using mapeq by simp
    show "dsim n cs (dnext tw ts) (DTS mt) \<phi>'"
      unfolding f
      by (rule dsim.DsTS[OF wf produces_next[OF pr w sts mts m, unfolded f] cse])
  qed
next
  case (DsLet n cs tw p m \<phi> \<psi> \<phi>d \<psi>d)
  note wf = DsLet.hyps(1) and pr = DsLet.hyps(2) and sim1 = DsLet.hyps(3)
    and IH1 = DsLet.hyps(4) and sim2 = DsLet.hyps(5) and IH2 = DsLet.hyps(6)
    and w = DsLet.prems(1) and sts = DsLet.prems(2)
    and mts = DsLet.prems(3) and mv = DsLet.prems(4)
  obtain as \<phi>2 where e1: "meval j m ts db \<phi> = (as, \<phi>2)" by (cases "meval j m ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) as db) \<psi> = (bs, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) as db) \<psi>")
  have x: "xs = bs" and f: "\<phi>' = mformula.MLet p m \<phi>2 \<psi>2" using mv e1 e2 by simp_all
  have ta: "list_all (ftable m {0..<m}) as"
    using dsim_produces[OF sim1] by (intro produces_tables[OF _ w sts mts e1]) simp
  have dt: "map (dtabc m [0..<m]) as = as" using ta by (induct as) (auto simp: dtabc_upt)
  have w': "wf_db (Mapping.update (p, m) as db)"
    by (rule wf_db_update'[OF w]) (use ta in simp)
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsLet.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc m [0..<m]) as, \<phi>d2)"
    and s1: "dsim m [0..<m] (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts (Mapping.update (p, m) as db) \<psi>d
        = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w' sts mts e2 sz2] by blast
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DLet p m \<phi>d \<psi>d) = (map (dtabc n cs) xs, DLet p m \<phi>d2 \<psi>d2)"
      using d1 d2 unfolding x dt by simp
    show "dsim n cs (dnext tw ts) (DLet p m \<phi>d2 \<psi>d2) \<phi>'"
      unfolding f
      by (rule dsim.DsLet[OF wf produces_next[OF pr w sts mts mv, unfolded f] s1 s2])
  qed
next
  case (DsFrz n cs tw p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<phi>d \<psi>d)
  note wf = DsFrz.hyps(1) and pr = DsFrz.hyps(2) and sim1 = DsFrz.hyps(3)
    and IH1 = DsFrz.hyps(4) and sim2 = DsFrz.hyps(5) and IH2 = DsFrz.hyps(6)
    and tas = DsFrz.hyps(7)
    and w = DsFrz.prems(1) and sts = DsFrz.prems(2)
    and mts = DsFrz.prems(3) and mv = DsFrz.prems(4) and le = DsFrz.prems(5)
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ le], simp)+
  have szs: "size \<psi> < NN" by (rule order.strict_trans2[OF _ le]) simp
  \<comment> \<open>the left operand: at its own full frame, so its tables are their own dense form\<close>
  obtain as \<phi>2 where e1: "meval j m ts db \<phi> = (as, \<phi>2)" by (cases "meval j m ts db \<phi>")
  have ta: "list_all (ftable m {0..<m}) as"
    using dsim_produces[OF sim1] by (intro produces_tables[OF _ w sts mts e1]) simp
  have dt: "map (dtabc m [0..<m]) as = as" using ta by (induct as) (auto simp: dtabc_upt)
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (as, \<phi>d2)"
    and s1: "dsim m [0..<m] (dnext tw ts) \<phi>d2 \<phi>2"
    using IH1[OF w sts mts e1 sz1] unfolding dt by blast
  \<comment> \<open>the body, against the database in which the bound predicate is empty\<close>
  have w0: "wf_db (Mapping.update (p, m) [] db)" by (rule wf_db_update'[OF w]) simp
  obtain zs0 \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) [] db) \<psi> = (zs0, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<psi>")
  obtain \<psi>d2 where d2: "deval j ts (Mapping.update (p, m) [] db) \<psi>d
        = (map (dtabc n cs) zs0, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2"
    using IH2[OF w0 sts mts e2 sz2] by blast
  have szp: "size \<psi>2 < NN"
    using default_maux.size_snd_meval[of j n ts "Mapping.update (p, m) [] db" \<psi>] e2 szs
    by simp
  \<comment> \<open>the frozen tuples the two runs are handed are the same list\<close>
  let ?as1 = "drop (jfrz - jphi + length (drop (jfrz - jpsi0) zs0)) (\<alpha>s @ as)"
  have tas1: "list_all (ftable m {0..<m}) ?as1"
    using tas ta by (auto simp: list_all_iff dest!: in_set_dropD)
  have agree: "\<And>\<alpha>. \<alpha> \<in> set ?as1 \<Longrightarrow>
      fst (deval j [] (Mapping.update (p, m) (replicate j \<alpha>)
             (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>d2)
        = map (dtabc n cs) (fst (meval j n [] (Mapping.update (p, m) (replicate j \<alpha>)
             (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>2))"
  proof -
    fix \<alpha> assume a: "\<alpha> \<in> set ?as1"
    have wa: "wf_db (Mapping.update (p, m) (replicate j \<alpha>)
        (Mapping.map_values (\<lambda>_ _. []) db))"
      by (rule wf_db_update'[OF wf_db_map_values_empty]) (use tas1 a in \<open>simp add: list_all_iff\<close>)
    obtain us \<chi> where eu: "meval j n [] (Mapping.update (p, m) (replicate j \<alpha>)
        (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>2 = (us, \<chi>)"
      by (cases "meval j n [] (Mapping.update (p, m) (replicate j \<alpha>)
        (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>2")
    obtain dus where du: "deval j [] (Mapping.update (p, m) (replicate j \<alpha>)
          (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>d2 = (map (dtabc n cs) us, dus)"
      using Q[OF szp s2 wa _ _ eu] by auto
    show "fst (deval j [] (Mapping.update (p, m) (replicate j \<alpha>)
             (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>d2)
        = map (dtabc n cs) (fst (meval j n [] (Mapping.update (p, m) (replicate j \<alpha>)
             (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>2))"
      using du eu by simp
  qed
  obtain ys as' where e3: "freeze_meval0 (\<lambda>\<alpha>. meval j n []
        (Mapping.update (p, m) (replicate j \<alpha>) (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>2)
        (jfrz - (jpsi0 + length zs0)) ?as1 = (ys, as')"
    by (cases "freeze_meval0 (\<lambda>\<alpha>. meval j n []
        (Mapping.update (p, m) (replicate j \<alpha>) (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>2)
        (jfrz - (jpsi0 + length zs0)) ?as1")
  obtain dys das' where d3: "freeze_meval0 (\<lambda>\<alpha>. deval j []
        (Mapping.update (p, m) (replicate j \<alpha>) (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>d2)
        (jfrz - (jpsi0 + length zs0)) ?as1 = (dys, das')"
    by (cases "freeze_meval0 (\<lambda>\<alpha>. deval j []
        (Mapping.update (p, m) (replicate j \<alpha>) (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>d2)
        (jfrz - (jpsi0 + length zs0)) ?as1")
  have frel: "dys = map (dtabc n cs) ys \<and> das' = as'"
    by (rule freeze_meval0_rel[OF e3 d3 agree])
  have tas': "list_all (ftable m {0..<m}) as'"
    using freeze_meval0_sub[OF e3] tas1 by (auto simp: list_all_iff)
  \<comment> \<open>the two runs agree, component by component\<close>
  have x: "xs = drop (jfrz - jpsi0) zs0 @ ys"
    and f: "\<phi>' = mformula.MFrz p m \<phi>2 \<psi>2
        (jfrz + length (drop (jfrz - jpsi0) zs0) + length ys)
        (jpsi0 + length zs0) (jphi + length as) as'"
    using mv e1 e2 e3 by (simp_all add: Let_def)
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s)
        = (map (dtabc n cs) xs, DFrz p m \<phi>d2 \<psi>d2
             (jfrz + length (drop (jfrz - jpsi0) zs0) + length ys)
             (jpsi0 + length zs0) (jphi + length as) as')"
      using d1 d2 d3 frel dt unfolding x by (simp add: Let_def drop_map)
    show "dsim n cs (dnext tw ts) (DFrz p m \<phi>d2 \<psi>d2
             (jfrz + length (drop (jfrz - jpsi0) zs0) + length ys)
             (jpsi0 + length zs0) (jphi + length as) as') \<phi>'"
      unfolding f
      by (rule dsim.DsFrz[OF wf produces_next[OF pr w sts mts mv, unfolded f] s1 s2 tas'])
  qed
next
  case (DsLetPast n cs tw p m \<phi> \<psi> i buf \<phi>d \<psi>d)
  note wf = DsLetPast.hyps(1) and pr = DsLetPast.hyps(2) and sim1 = DsLetPast.hyps(3)
    and IH1 = DsLetPast.hyps(4) and sim2 = DsLetPast.hyps(5) and IH2 = DsLetPast.hyps(6)
    and lbo = DsLetPast.hyps(7)
    and w = DsLetPast.prems(1) and sts = DsLetPast.prems(2)
    and mts = DsLetPast.prems(3) and mv = DsLetPast.prems(4) and le = DsLetPast.prems(5)
  have sz2: "size \<psi> \<le> NN" by (rule order_trans[OF _ le]) simp
  have szs: "size \<phi> < NN" by (rule order.strict_trans2[OF _ le]) simp
  have lbl: "list_all (ftable m {0..<m}) (list_of_option buf)" using lbo by (cases buf) auto
  \<comment> \<open>the rounds of the bound formula, which sits at its own full frame\<close>
  obtain as i2 buf2 \<phi>2 where e1: "letpast_meval m j i [] (list_of_option buf) (p, m) ts db \<phi>
      = (as, i2, buf2, \<phi>2)"
    by (cases "letpast_meval m j i [] (list_of_option buf) (p, m) ts db \<phi>") auto
  have e1': "letpast_meval0 (meval j m) j i [] (list_of_option buf) (p, m) ts db \<phi>
      = (as, i2, buf2, \<phi>2)" using e1 by (simp add: default_maux.letpast_meval_def)
  have lnil: "list_all (ftable m {0..<m}) []" by simp
  \<comment> \<open>at that frame a dense table is the sparse one, so the two runs agree literally\<close>
  have Q': "\<And>tw' \<chi>d \<chi> ts' db' zs' \<chi>'. size \<chi> < NN \<Longrightarrow> dsim m [0..<m] tw' \<chi>d \<chi> \<Longrightarrow>
      wf_db db' \<Longrightarrow> sorted ts' \<Longrightarrow> (\<forall>t \<in> set ts'. tw' \<le> t) \<Longrightarrow>
      meval j m ts' db' \<chi> = (zs', \<chi>') \<Longrightarrow>
      \<exists>\<chi>d'. deval j ts' db' \<chi>d = (zs', \<chi>d') \<and> dsim m [0..<m] (dnext tw' ts') \<chi>d' \<chi>'"
  proof -
    fix tw' :: ts and \<chi>d \<chi> ts' db' zs' \<chi>'
    assume a1: "size \<chi> < NN" and a2: "dsim m [0..<m] tw' \<chi>d \<chi>" and a3: "wf_db db'"
      and a4: "sorted ts'" and a5: "\<forall>t \<in> set ts'. tw' \<le> t"
      and a6: "meval j m ts' db' \<chi> = (zs', \<chi>')"
    have t: "list_all (ftable m {0..<m}) zs'"
      using dsim_produces[OF a2] by (intro produces_tables[OF _ a3 a4 a5 a6]) simp
    have dt: "map (dtabc m [0..<m]) zs' = zs'" using t by (induct zs') (auto simp: dtabc_upt)
    show "\<exists>\<chi>d'. deval j ts' db' \<chi>d = (zs', \<chi>d') \<and> dsim m [0..<m] (dnext tw' ts') \<chi>d' \<chi>'"
      using Q[OF a1 a2 a3 a4 a5 a6] unfolding dt by blast
  qed
  have lr: "list_all (ftable m {0..<m}) as \<and> (\<forall>y. buf2 = Some y \<longrightarrow> ftable m {0..<m} y) \<and>
      (\<exists>\<phi>d'. letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi>d
        = (as, i2, buf2, \<phi>d') \<and> dsim m [0..<m] (dnext tw ts) \<phi>d' \<phi>2)"
    by (rule letpast_meval0_rel[OF _ e1' snd_conv szs sim1 w sts mts lnil lbl])
      (blast intro: Q')
  have ta: "list_all (ftable m {0..<m}) as" using lr by simp
  have lbo2: "\<forall>y. buf2 = Some y \<longrightarrow> ftable m {0..<m} y" using lr by simp
  obtain \<phi>d2 where d1: "letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi>d
        = (as, i2, buf2, \<phi>d2)"
    and s1: "dsim m [0..<m] (dnext tw ts) \<phi>d2 \<phi>2" using lr by blast
  \<comment> \<open>the body, against the database in which the bound predicate holds the rounds' output\<close>
  have w2: "wf_db (Mapping.update (p, m) as db)" by (rule wf_db_update'[OF w]) (use ta in simp)
  obtain bs \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) as db) \<psi> = (bs, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) as db) \<psi>")
  obtain \<psi>d2 where d2: "deval j ts (Mapping.update (p, m) as db) \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w2 sts mts e2 sz2] by blast
  have x: "xs = bs" and f: "\<phi>' = mformula.MLetPast p m \<phi>2 \<psi>2 i2 buf2"
    using mv e1 e2 by simp_all
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DLetPast p m \<phi>d \<psi>d i buf)
        = (map (dtabc n cs) xs, DLetPast p m \<phi>d2 \<psi>d2 i2 buf2)"
      using d1 d2 unfolding x by simp
    show "dsim n cs (dnext tw ts) (DLetPast p m \<phi>d2 \<psi>d2 i2 buf2) \<phi>'"
      unfolding f
      by (rule dsim.DsLetPast[OF wf produces_next[OF pr w sts mts mv, unfolded f] s1 s2 lbo2])
  qed
next
  case (DsTrigger n cs tw args \<phi> \<psi> buf nts aux cs_L \<phi>d \<psi>d dags pl daux dbuf)
  note wf = DsTrigger.hyps(1) and pr = DsTrigger.hyps(2)
    and sim1 = DsTrigger.hyps(3) and IH1 = DsTrigger.hyps(4)
    and sim2 = DsTrigger.hyps(5) and IH2 = DsTrigger.hyps(6)
    and wfL = DsTrigger.hyps(7) and sub = DsTrigger.hyps(8)
    and an = DsTrigger.hyps(9) and aL = DsTrigger.hyps(10) and aR = DsTrigger.hyps(11)
    and m0 = DsTrigger.hyps(12) and dag = DsTrigger.hyps(13) and pe = DsTrigger.hyps(14)
    and rel = DsTrigger.hyps(15)
    and w = DsTrigger.prems(1) and sts = DsTrigger.prems(2)
    and mts = DsTrigger.prems(3) and m = DsTrigger.prems(4)
  have cwf: "sorted_wrt (<) cs" and cb: "\<forall>c \<in> set cs. c < n" using wf by auto
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs aux2 buf2 nts2 where e3: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
      in (zs @ [z], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ ts)
      = ((zs, aux2), buf2, nts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
      in (zs @ [z], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ ts)") auto
  have x: "xs = zs" and f: "\<phi>' = mformula.MTrigger args \<phi>2 \<psi>2 buf2 nts2 aux2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsTrigger.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs_L) as, \<phi>d2)"
    and s1: "dsim n cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs) bs, \<psi>d2)"
    and s2: "dsim n cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have ta: "list_all (ftable n (set cs_L)) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable n (set cs)) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs daux2 dbuf2 dnts2 where d3: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [dsan (gresult_mmtaux dags ax)], ax)) ([], daux)
      (mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) dbuf) (nts @ ts)
      = ((dzs, daux2), dbuf2, dnts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [dsan (gresult_mmtaux dags ax)], ax)) ([], daux)
      (mbuf2_add (map (dtabc n cs_L) as) (map (dtabc n cs) bs) dbuf) (nts @ ts)") auto
  have step: "dzs = map (dtabc n cs) zs \<and> dnts2 = nts2 \<and>
      dtrigger_rel n cs cs_L args (dnext tw ts) aux2 daux2 buf2 dbuf2 nts2"
    by (rule dtrigger_step_rel[OF cwf _ cb sub an aL aR m0 rel ta tb sts mts e3
          d3[unfolded dag]]) (use wfL in simp)
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DTrigger dags pl \<phi>d \<psi>d dbuf nts daux)
        = (map (dtabc n cs) xs, DTrigger dags pl \<phi>d2 \<psi>d2 dbuf2 nts2 daux2)"
      using d1 d2 d3 step x by simp
    show "dsim n cs (dnext tw ts) (DTrigger dags pl \<phi>d2 \<psi>d2 dbuf2 nts2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsTrigger[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 wfL sub
            an aL aR m0 dag pe]) (use step in simp)
  qed
next
  case (DsAndTrigger n cs tw \<alpha> buf1 args \<phi> \<psi> buf2 nts aux \<alpha>d cs_L \<phi>d cs_R \<psi>d dags pl dbf1 daux
      dbf2)
  note wf = DsAndTrigger.hyps(1) and pr = DsAndTrigger.hyps(2)
    and sim0 = DsAndTrigger.hyps(3) and IH0 = DsAndTrigger.hyps(4)
    and sim1 = DsAndTrigger.hyps(5) and IH1 = DsAndTrigger.hyps(6)
    and sim2 = DsAndTrigger.hyps(7) and IH2 = DsAndTrigger.hyps(8)
    and wfL = DsAndTrigger.hyps(9) and wfR = DsAndTrigger.hyps(10)
    and subLR = DsAndTrigger.hyps(11) and subR = DsAndTrigger.hyps(12)
    and an = DsAndTrigger.hyps(13) and aL = DsAndTrigger.hyps(14)
    and aR = DsAndTrigger.hyps(15) and ok = DsAndTrigger.hyps(16)
    and dag = DsAndTrigger.hyps(17) and ple = DsAndTrigger.hyps(18)
    and bf1 = DsAndTrigger.hyps(19) and rel = DsAndTrigger.hyps(20)
    and w = DsAndTrigger.prems(1) and sts = DsAndTrigger.prems(2)
    and mts = DsAndTrigger.prems(3) and m = DsAndTrigger.prems(4)
  have cwf: "sorted_wrt (<) cs" and cb: "\<forall>c \<in> set cs. c < n" using wf by auto
  have rwf: "sorted_wrt (<) cs_R" and rb: "\<forall>c \<in> set cs_R. c < n" using wfR by auto
  have lwf: "sorted_wrt (<) cs_L" using wfL by auto
  obtain as \<alpha>2 where e0: "meval j n ts db \<alpha> = (as, \<alpha>2)" by (cases "meval j n ts db \<alpha>")
  obtain xs1 \<phi>2 where e1: "meval j n ts db \<phi> = (xs1, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain ys1 \<psi>2 where e2: "meval j n ts db \<psi> = (ys1, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain ws aux2 buf2' nts2 where e3: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
      in (zs @ [(fv_z, z)], ax)) ([], aux) (mbuf2_add xs1 ys1 buf2) (nts @ ts)
      = ((ws, aux2), buf2', nts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
      in (zs @ [(fv_z, z)], ax)) ([], aux) (mbuf2_add xs1 ys1 buf2) (nts @ ts)") auto
  obtain zs buf1' where e4: "mbuf2_take (\<lambda>r1 (V, r2). bin_join n (set cs) r1 True V r2)
      (mbuf2_add as ws buf1) = (zs, buf1')"
    by (cases "mbuf2_take (\<lambda>r1 (V, r2). bin_join n (set cs) r1 True V r2)
      (mbuf2_add as ws buf1)") auto
  have x: "xs = zs"
    and f: "\<phi>' = mformula.MAndTrigger (set cs) \<alpha>2 buf1' args \<phi>2 \<psi>2 buf2' nts2 aux2"
    using m e0 e1 e2 e3 e4 by (simp_all del: bin_join.simps)
  have sz0: "size \<alpha> \<le> NN" and sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsAndTrigger.prems(5)], simp)+
  obtain \<alpha>d2 where d0: "deval j ts db \<alpha>d = (map (dtabc n cs) as, \<alpha>d2)"
    and s0: "dsim n cs (dnext tw ts) \<alpha>d2 \<alpha>2" using IH0[OF w sts mts e0 sz0] by blast
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc n cs_L) xs1, \<phi>d2)"
    and s1: "dsim n cs_L (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc n cs_R) ys1, \<psi>d2)"
    and s2: "dsim n cs_R (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have t0: "list_all (ftable n (set cs)) as"
    by (rule produces_tables[OF dsim_produces[OF sim0] w sts mts e0])
  have ta: "list_all (ftable n (set cs_L)) xs1"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable n (set cs_R)) ys1"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dws daux2 dbf2' dnts2 where d3: "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (dsan (gresult_mmtaux dags ax))], ax))
      ([], daux) (mbuf2_add (map (dtabc n cs_L) xs1) (map (dtabc n cs_R) ys1) dbf2) (nts @ ts)
      = ((dws, daux2), dbf2', dnts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (dsan (gresult_mmtaux dags ax))], ax))
      ([], daux) (mbuf2_add (map (dtabc n cs_L) xs1) (map (dtabc n cs_R) ys1) dbf2)
      (nts @ ts)") auto
  have step: "list_all2 (dtres n cs_R) ws dws \<and> dnts2 = nts2 \<and>
      dtrigger_rel n cs_R cs_L args (dnext tw ts) aux2 daux2 buf2' dbf2' nts2"
    by (rule dandtrigger_step_rel[OF rwf lwf rb subLR an aL aR ok rel ta tb sts mts e3
          d3[unfolded dag]])
  have badd: "dandbuf n cs cs_R (mbuf2_add as ws buf1)
      (mbuf2_add (map (dtabc n cs) as) dws dbf1)"
    by (rule dandbuf_add[OF bf1 t0]) (use step in simp)
  obtain dbf1' where d4: "mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> dbin_join pl r1 True z) (mbuf2_add (map (dtabc n cs) as) dws dbf1)
      = (map (dtabc n cs) zs, dbf1')"
    and bf1': "dandbuf n cs cs_R buf1' dbf1'"
    using dandbuf_take[OF cwf rwf cb subR badd e4] unfolding ple by blast
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAndTrigger pl \<alpha>d dbf1 dags \<phi>d \<psi>d dbf2 nts daux)
        = (map (dtabc n cs) xs, DAndTrigger pl \<alpha>d2 dbf1' dags \<phi>d2 \<psi>d2 dbf2' nts2 daux2)"
      using d0 d1 d2 d3 d4 step x by simp
    show "dsim n cs (dnext tw ts) (DAndTrigger pl \<alpha>d2 dbf1' dags \<phi>d2 \<psi>d2 dbf2' nts2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsAndTrigger[OF wf produces_next[OF pr w sts mts m, unfolded f] s0 s1 s2
            wfL wfR subLR subR an aL aR ok dag ple bf1']) (use step in simp)
  qed
next
  case (DsMatchP n cs tw I mr mrs L buf nts aux \<psi>s css Ld pls dbuf daux)
  note wf = DsMatchP.hyps(1) and pr = DsMatchP.hyps(2) and sr = DsMatchP.hyps(3)
    and okm = DsMatchP.hyps(4) and fvA = DsMatchP.hyps(5) and dm = DsMatchP.hyps(6)
    and mrsd = DsMatchP.hyps(7) and lc = DsMatchP.hyps(8) and lL = DsMatchP.hyps(9)
    and lLd = DsMatchP.hyps(10) and cfv = DsMatchP.hyps(11) and csub = DsMatchP.hyps(12)
    and wc = DsMatchP.hyps(13) and la = DsMatchP.hyps(14) and pe = DsMatchP.hyps(15)
    and bf = DsMatchP.hyps(16) and rel = DsMatchP.hyps(17)
    and w = DsMatchP.prems(1) and sts = DsMatchP.prems(2)
    and mts = DsMatchP.prems(3) and m = DsMatchP.prems(4)
  let ?R = "map (meval j n ts db) L"
  let ?dR = "map (deval j ts db) Ld"
  let ?F = "\<lambda>rels t (zs, ax).
      let (z, ax) = update_matchP n I mr mrs rels t ax in (zs @ [z], ax)"
  let ?G = "\<lambda>rels t (zs, ax).
      let (z, ax) = update_matchP (length cs) I mr mrs (map2 dembedp pls rels) t ax
      in (zs @ [z], ax)"
  obtain zs aux2 buf2 tt2 nts2 where g0:
    "mbufnt_take ?F ([], aux) (mbufn_add (map fst ?R) buf) 0 (nts @ ts)
       = ((zs, aux2), buf2, tt2, nts2)"
    by (cases "mbufnt_take ?F ([], aux) (mbufn_add (map fst ?R) buf) 0 (nts @ ts)") auto
  have x: "xs = zs" and fe: "\<phi>' = mformula.MMatchP I mr mrs (map snd ?R) buf2 nts2 aux2"
    using m g0 by (simp_all add: Let_def map_split_alt del: mbufnt_take.simps)
  \<comment> \<open>the operands, and their narrowing\<close>
  have la0: "\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i)" using la by blast
  have lcL: "length css = length L" using lc lL by simp
  have tabs: "\<forall>i < length css. list_all (ftable n (set (css ! i))) (map fst ?R ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length css"
    then have iL: "i < length L" using lcL by simp
    have "list_all (ftable n (set (css ! i))) (fst (meval j n ts db (L ! i)))"
      by (rule dsims_tables[OF la0 lLd lcL w sts mts iL])
    then show "list_all (ftable n (set (css ! i))) (map fst ?R ! i)" using iL by simp
  qed
  have szL: "\<And>i. i < length L \<Longrightarrow> size (L ! i) \<le> NN"
  proof -
    fix i assume i: "i < length L"
    have "size (L ! i) \<le> size_list size L"
      by (rule size_list_estimation'[OF nth_mem[OF i] order.refl])
    also have "size_list size L \<le> NN" by (rule order_trans[OF _ DsMatchP.prems(5)]) simp
    finally show "size (L ! i) \<le> NN" .
  qed
  have la1: "\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (css ! i)) as, \<psi>d')
            \<and> dsim n (css ! i) (dnext tw ts) \<psi>d' \<psi>'))"
    using la w sts mts szL by blast
  have dlr: "length ?dR = length L \<and>
      map fst ?dR = map2 (\<lambda>c y. map (dtabc n c) y) css (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (css ! i) (dnext tw ts) (map snd ?dR ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF lLd lcL la1])
  have dl: "map fst ?dR = map2 (\<lambda>c y. map (dtabc n c) y) css (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (css ! i) (dnext tw ts) (map snd ?dR ! i)
      (snd (meval j n ts db (L ! i)))" using dlr by blast
  \<comment> \<open>the buffer\<close>
  have badd: "dbufn n css (mbufn_add (map fst ?R) buf) (mbufn_add (map fst ?dR) dbuf)"
    unfolding dl by (rule dbufn_add[OF bf _ tabs]) (use lcL in simp)
  \<comment> \<open>one firing of the window\<close>
  define Rel where "Rel = (\<lambda>(zs :: event_data table list, ax) (dzs :: event_data table list, dax).
      dzs = map (dtabc n cs) zs \<and> dmrd_rel n cs ax dax)"
  have step: "Rel (?F as t u) (?G (map2 (dtabc n) css as) t u')"
    if las: "length as = length css"
      and mas: "\<forall>i < length css. ftable n (set (css ! i)) (as ! i)"
      and ru: "Rel u u'" for as u u' t
  proof -
    obtain zs0 ax where u: "u = (zs0, ax)" by (cases u)
    obtain dzs0 dax where u': "u' = (dzs0, dax)" by (cases u')
    have dz: "dzs0 = map (dtabc n cs) zs0" and rax: "dmrd_rel n cs ax dax"
      using ru by (simp_all add: Rel_def u u')
    have emb: "map2 dembedp pls (map2 (dtabc n) css as) = map (dtabc n cs) as"
      unfolding list_eq_iff_nth_eq
    proof (intro conjI allI impI)
      show "length (map2 dembedp pls (map2 (dtabc n) css as)) = length (map (dtabc n cs) as)"
        using pe las by simp
    next
      fix i assume i: "i < length (map2 dembedp pls (map2 (dtabc n) css as))"
      then have i': "i < length css" using pe las by simp
      have "dembedp (emb_plan cs (css ! i)) (dtabc n (css ! i) (as ! i)) = dtabc n cs (as ! i)"
        by (rule dembedp_dtabc[OF conjunct1[OF wf] _ conjunct2[OF wf]])
          (use i' wc mas in \<open>fastforce intro: nth_mem\<close>)+
      then show "map2 dembedp pls (map2 (dtabc n) css as) ! i = map (dtabc n cs) as ! i"
        using i' pe las by simp
    qed
    interpret dmatchP_frame n cs \<psi>s as mrs
    proof
      show "sorted_wrt (<) cs" using wf by simp
      show "\<forall>c \<in> set cs. c < n" using wf by simp
      show "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s as"
        using las lc cfv mas by (fastforce simp: list_all2_conv_all_nth)
      show "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set cs" using cfv csub by auto
      show "distinct mrs" by (rule dm)
      show "\<And>ms. ms \<in> set mrs \<Longrightarrow>
          Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<psi>s) \<and>
          ok (length \<psi>s) ms \<and> set cs = fv_regex (from_mregex ms \<psi>s)"
        using mrsd sr okm fvA
        by (auto simp: RPDs_safe RPDs_ok RPDs_safe_fv_regex)
    qed
    have uu: "dtabc n cs (fst (update_matchP n I mr mrs as t ax))
        = fst (update_matchP (length cs) I mr mrs (map (dtabc n cs) as) t dax) \<and>
      dmrd_rel n cs (snd (update_matchP n I mr mrs as t ax))
        (snd (update_matchP (length cs) I mr mrs (map (dtabc n cs) as) t dax))"
      by (rule dtabc_update_matchP[OF rax])
    show ?thesis using dz uu by (simp add: Rel_def u u' emb Let_def split_beta)
  qed
  have rz: "Rel ([], aux) ([], daux)" using rel by (simp add: Rel_def)
  obtain w2 dbuf2 where dt:
    "mbufnt_take ?G ([], daux) (mbufn_add (map fst ?dR) dbuf) 0 (nts @ ts)
       = (w2, dbuf2, tt2, nts2)"
    and rw: "Rel (zs, aux2) w2" and bf2: "dbufn n css buf2 dbuf2"
    using dbufn_nt_take[where R = Rel and f = "?F" and g = "?G", OF badd step rz g0] by blast
  obtain dzs daux2 where w2: "w2 = (dzs, daux2)" by (cases w2)
  have dzs: "dzs = map (dtabc n cs) zs" and rel2: "dmrd_rel n cs aux2 daux2"
    using rw by (simp_all add: Rel_def w2)
  have tx: "list_all (ftable n (set cs)) zs"
    using produces_tables[OF pr w sts mts m] unfolding x .
  have sz: "\<forall>x \<in> set zs. dsan (dtabc n cs x) = dtabc n cs x"
    using tx by (auto simp: list_all_iff dsan_dtabc[OF conjunct1[OF wf] conjunct2[OF wf]])
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DMatchP (length cs) I mr mrs pls Ld dbuf nts daux)
        = (map (dtabc n cs) xs, DMatchP (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 daux2)"
      using dt x dzs sz unfolding w2 by (simp add: Let_def del: mbufnt_take.simps)
    show "dsim n cs (dnext tw ts) (DMatchP (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 daux2)
        \<phi>'"
      unfolding fe
      by (rule dsim.DsMatchP[OF wf produces_next[OF pr w sts mts m, unfolded fe] sr okm fvA dm
            mrsd lc _ _ cfv csub wc _ pe bf2 rel2])
        (use lL lLd dl2 dlr in auto)
  qed
next
  case (DsMatchF n cs tw I mr mrs L buf nts t aux \<psi>s css Ld pls dbuf daux)
  note wf = DsMatchF.hyps(1) and pr = DsMatchF.hyps(2) and sr = DsMatchF.hyps(3)
    and okm = DsMatchF.hyps(4) and fvA = DsMatchF.hyps(5) and dm = DsMatchF.hyps(6)
    and mrsd = DsMatchF.hyps(7) and lc = DsMatchF.hyps(8) and lL = DsMatchF.hyps(9)
    and lLd = DsMatchF.hyps(10) and cfv = DsMatchF.hyps(11) and csub = DsMatchF.hyps(12)
    and wc = DsMatchF.hyps(13) and la = DsMatchF.hyps(14) and pe = DsMatchF.hyps(15)
    and bf = DsMatchF.hyps(16) and rel = DsMatchF.hyps(17)
    and w = DsMatchF.prems(1) and sts = DsMatchF.prems(2)
    and mts = DsMatchF.prems(3) and m = DsMatchF.prems(4)
  let ?R = "map (meval j n ts db) L"
  let ?dR = "map (deval j ts db) Ld"
  let ?F = "update_matchF n I mr mrs"
  let ?G = "\<lambda>rels. update_matchF (length cs) I mr mrs (map2 dembedp pls rels)"
  obtain aux2 buf2 nt2 nts2 where g0:
    "mbufnt_take ?F aux (mbufn_add (map fst ?R) buf) t (nts @ ts) = (aux2, buf2, nt2, nts2)"
    by (cases "mbufnt_take ?F aux (mbufn_add (map fst ?R) buf) t (nts @ ts)") auto
  obtain zs aux3 where g1: "eval_matchF I mr nt2 aux2 = (zs, aux3)"
    by (cases "eval_matchF I mr nt2 aux2") auto
  have x: "xs = zs" and fe: "\<phi>' = mformula.MMatchF I mr mrs (map snd ?R) buf2 nts2 nt2 aux3"
    using m g0 g1 by (simp_all add: Let_def map_split_alt del: mbufnt_take.simps)
  \<comment> \<open>the operands, and their narrowing\<close>
  have la0: "\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i)" using la by blast
  have lcL: "length css = length L" using lc lL by simp
  have tabs: "\<forall>i < length css. list_all (ftable n (set (css ! i))) (map fst ?R ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length css"
    then have iL: "i < length L" using lcL by simp
    have "list_all (ftable n (set (css ! i))) (fst (meval j n ts db (L ! i)))"
      by (rule dsims_tables[OF la0 lLd lcL w sts mts iL])
    then show "list_all (ftable n (set (css ! i))) (map fst ?R ! i)" using iL by simp
  qed
  have szL: "\<And>i. i < length L \<Longrightarrow> size (L ! i) \<le> NN"
  proof -
    fix i assume i: "i < length L"
    have "size (L ! i) \<le> size_list size L"
      by (rule size_list_estimation'[OF nth_mem[OF i] order.refl])
    also have "size_list size L \<le> NN" by (rule order_trans[OF _ DsMatchF.prems(5)]) simp
    finally show "size (L ! i) \<le> NN" .
  qed
  have la1: "\<forall>i < length L. dsim n (css ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc n (css ! i)) as, \<psi>d')
            \<and> dsim n (css ! i) (dnext tw ts) \<psi>d' \<psi>'))"
    using la w sts mts szL by blast
  have dlr: "length ?dR = length L \<and>
      map fst ?dR = map2 (\<lambda>c y. map (dtabc n c) y) css (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (css ! i) (dnext tw ts) (map snd ?dR ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF lLd lcL la1])
  have dl: "map fst ?dR = map2 (\<lambda>c y. map (dtabc n c) y) css (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (css ! i) (dnext tw ts) (map snd ?dR ! i)
      (snd (meval j n ts db (L ! i)))" using dlr by blast
  \<comment> \<open>the buffer\<close>
  have badd: "dbufn n css (mbufn_add (map fst ?R) buf) (mbufn_add (map fst ?dR) dbuf)"
    unfolding dl by (rule dbufn_add[OF bf _ tabs]) (use lcL in simp)
  \<comment> \<open>one firing of the window\<close>
  interpret dmatchF_frame n cs \<psi>s mrs
  proof
    show "sorted_wrt (<) cs" using wf by simp
    show "\<forall>c \<in> set cs. c < n" using wf by simp
    show "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set cs" using cfv csub by auto
    show "distinct mrs" by (rule dm)
    show "\<And>ms. ms \<in> set mrs \<Longrightarrow>
        Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<psi>s) \<and>
        ok (length \<psi>s) ms \<and> set cs = fv_regex (from_mregex ms \<psi>s)"
      using mrsd sr okm fvA by (auto simp: LPDs_safe LPDs_ok LPDs_safe_fv_regex)
  qed
  have step: "dmld_rel n cs \<psi>s (?F as tt u) (?G (map2 (dtabc n) css as) tt u')"
    if las: "length as = length css"
      and mas: "\<forall>i < length css. ftable n (set (css ! i)) (as ! i)"
      and ru: "dmld_rel n cs \<psi>s u u'" for as u u' tt
  proof -
    have emb: "map2 dembedp pls (map2 (dtabc n) css as) = map (dtabc n cs) as"
      unfolding list_eq_iff_nth_eq
    proof (intro conjI allI impI)
      show "length (map2 dembedp pls (map2 (dtabc n) css as)) = length (map (dtabc n cs) as)"
        using pe las by simp
    next
      fix i assume i: "i < length (map2 dembedp pls (map2 (dtabc n) css as))"
      then have i': "i < length css" using pe las by simp
      have "dembedp (emb_plan cs (css ! i)) (dtabc n (css ! i) (as ! i)) = dtabc n cs (as ! i)"
        by (rule dembedp_dtabc[OF conjunct1[OF wf] _ conjunct2[OF wf]])
          (use i' wc mas in \<open>fastforce intro: nth_mem\<close>)+
      then show "map2 dembedp pls (map2 (dtabc n) css as) ! i = map (dtabc n cs) as ! i"
        using i' pe las by simp
    qed
    have wfr: "list_all2 (\<lambda>\<psi> rl. table n (Formula.fv \<psi>) rl) \<psi>s as"
      using las lc cfv mas by (fastforce simp: list_all2_conv_all_nth)
    show ?thesis using dtabc_update_matchF[OF wfr ru] by (simp add: emb)
  qed
  obtain daux2 dbuf2 where dt:
    "mbufnt_take ?G daux (mbufn_add (map fst ?dR) dbuf) t (nts @ ts) = (daux2, dbuf2, nt2, nts2)"
    and rw: "dmld_rel n cs \<psi>s aux2 daux2" and bf2: "dbufn n css buf2 dbuf2"
    using dbufn_nt_take[where R = "dmld_rel n cs \<psi>s" and f = "?F" and g = "?G",
        OF badd step rel g0] by blast
  obtain dzs daux3 where g2: "eval_matchF I mr nt2 daux2 = (dzs, daux3)"
    by (cases "eval_matchF I mr nt2 daux2") auto
  have evb: "fst (eval_matchF I mr nt2 daux2) = map (dtabc n cs) (fst (eval_matchF I mr nt2 aux2))
      \<and> dmld_rel n cs \<psi>s (snd (eval_matchF I mr nt2 aux2)) (snd (eval_matchF I mr nt2 daux2))"
    by (rule dtabc_eval_matchF[OF rw])
  have ev: "dzs = map (dtabc n cs) zs" using evb g1 g2 by simp
  have rel3: "dmld_rel n cs \<psi>s aux3 daux3" using evb g1 g2 by simp
  have tx: "list_all (ftable n (set cs)) zs"
    using produces_tables[OF pr w sts mts m] unfolding x .
  have sz: "\<forall>x \<in> set zs. dsan (dtabc n cs x) = dtabc n cs x"
    using tx by (auto simp: list_all_iff dsan_dtabc[OF conjunct1[OF wf] conjunct2[OF wf]])
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DMatchF (length cs) I mr mrs pls Ld dbuf nts t daux)
        = (map (dtabc n cs) xs,
           DMatchF (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 nt2 daux3)"
      using dt g2 x ev sz by (simp add: Let_def del: mbufnt_take.simps)
    show "dsim n cs (dnext tw ts)
        (DMatchF (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 nt2 daux3) \<phi>'"
      unfolding fe
      by (rule dsim.DsMatchF[OF wf produces_next[OF pr w sts mts m, unfolded fe] sr okm fvA dm
            mrsd lc _ _ cfv csub wc _ pe bf2 rel3])
        (use lL lLd dl2 dlr in auto)
  qed
qed

text \<open>Induction on the bound discharges the assumption the theorem above carries, and
  instantiating it at the formula's own size recovers the statement without it.\<close>

lemma dsim_deval_bound:
  "size \<phi> \<le> NN \<Longrightarrow> dsim n cs tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc n cs) xs, \<phi>d')
     \<and> dsim n cs (dnext tw ts) \<phi>d' \<phi>'"
proof (induct NN arbitrary: n cs tw \<phi>d \<phi> j ts db xs \<phi>' rule: less_induct)
  case (less NN)
  show ?case
    by (rule dsim_deval_N[OF _ less(3) less(4) less(5) less(6) less(7) less(2)])
      (use less(1) in blast)
qed

theorem dsim_deval:
  "dsim n cs tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc n cs) xs, \<phi>d')
     \<and> dsim n cs (dnext tw ts) \<phi>d' \<phi>'"
  by (rule dsim_deval_bound[OF order.refl])

(*<*)
end
(*>*)
