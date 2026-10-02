(*<*)
theory Dense_Eval
  imports Dense_Evt_Aux Dense_Trigger_Nar Dense_Match_Gen
begin
(*>*)

section \<open>The dense evaluator simulates the kernel's\<close>

text \<open>
  Every theorem of @{theory MFODL_Monitor_Dense.Dense} needs its operand tables to be finite and
  well formed over the node's columns.  That is not a property of a single call but of a
  formula's whole future, so it is stated coinductively: @{term "produces n ks tw \<phi>"} says that
  @{const meval} on @{term \<phi>} only ever yields finite tables over the column list @{term ks}, and
  that its successors do the same.  The kernel's own well-formedness invariant implies it, which
  is where -- and the only place where -- this development touches the kernel's correctness
  proof.
\<close>

text \<open>
  A database is well formed when the table stored at a name of arity @{term ar} holds tuples of
  that width -- which is what the trace's own databases look like.  The dense formula's predicate
  nodes read the database at the width the name was declared with, so this is exactly the
  condition they need.  The tables are also required to be finite: the dense multi-way join and
  the dense aggregation need it, and it cannot come from anywhere else -- the kernel's own
  invariant does not carry finiteness (@{term qtable} does not), and the trace does not either.
  It is a property of the input, and a real log has it.
\<close>

definition wf_db :: "database \<Rightarrow> bool" where
  "wf_db db \<longleftrightarrow> (\<forall>e ar X. Mapping.lookup db (e, ar) = Some X \<longrightarrow>
     list_all (\<lambda>T. table [0..<ar] T \<and> finite T) X)"

lemma wf_dbD:
  "wf_db db \<Longrightarrow> Mapping.lookup db (e, ar) = Some X \<Longrightarrow> T \<in> set X \<Longrightarrow> table [0..<ar] T"
  by (auto simp: wf_db_def list_all_iff)

lemma wf_dbD_finite:
  "wf_db db \<Longrightarrow> Mapping.lookup db (e, ar) = Some X \<Longrightarrow> T \<in> set X \<Longrightarrow> finite T"
  by (auto simp: wf_db_def list_all_iff)

text \<open>A let-bound formula's tables are reordered to the positional columns before they are bound
  into the database, so they are exactly what a well-formed database holds.\<close>

lemma wf_db_map_values_empty: "wf_db (Mapping.map_values (\<lambda>_ _. []) db)"
  by (auto simp: wf_db_def Mapping.lookup_map_values split: option.splits)

lemma wf_db_update':
  "wf_db db \<Longrightarrow> list_all (\<lambda>T. table [0..<snd q] T \<and> finite T) xs \<Longrightarrow>
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
  The invariant also carries a timestamp lower bound: @{term "produces n ks tw \<phi>"} may assume
  that every timestamp in the batch is at least @{term tw}, and re-establishes itself at the
  bound @{term "dnext tw ts"} the batch leaves behind.  The temporal nodes need this -- the
  verified Since and Until structures accept a new timestamp only at or after the one they are
  already at -- and the others carry it without using it.
\<close>

coinductive produces :: "nat \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool"
  where produces: "(\<And>j ts db xs \<phi>'. wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
      (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
      list_all (ftable ks) xs \<and> produces n ks (dnext tw ts) \<phi>') \<Longrightarrow> produces n ks tw \<phi>"

lemma produces_step:
  "produces n ks tw \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow>
     meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
     list_all (ftable ks) xs \<and> produces n ks (dnext tw ts) \<phi>'"
  by (erule produces.cases) blast

lemma produces_tables:
  "produces n ks tw \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow>
     meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> list_all (ftable ks) xs"
  by (drule produces_step) auto

lemma produces_next:
  "produces n ks tw \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow>
     meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> produces n ks (dnext tw ts) \<phi>'"
  by (drule produces_step) auto

section \<open>The dense formula\<close>

text \<open>
  A dense formula mirrors the kernel's @{typ "('msaux, 'muaux, 'mtaux) mformula"} node by node,
  but every node carries the data the ascending representation needs instead of the data the
  kernel's needs: a join plan instead of two column lists, a term already reindexed against the
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
      dformula nat nat "ts list" "event_data table list" enat bool bool "nat option" dformula
  | DLetPast Formula.name nat dformula dformula nat "event_data table option"
  | DTrigger args "nat option list" dformula dformula "event_data mbuf2" "ts list"
      "event_data gmmtaux"
  | DAndTrigger djoin_plan dformula "event_data table list \<times> event_data table option list"
      args dformula dformula "event_data mbuf2" "ts list" "event_data gmmtaux"
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
| "vdfail_nodes (DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
    vdfail_nodes \<phi> + vdfail_nodes \<psi> + vdfail_nodes \<rho>"
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
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> xs), DPredS e ar)"
| "deval j ts db (DPredM e ar tms cs) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> map (umatch_table tms cs) xs), DPredM e ar tms cs)"
| "deval j ts db (DAndRel \<phi> conf) =
     (let (xs, \<phi>') = deval j ts db \<phi>
      in (map (Set.filter (ueval_constraint conf)) xs, DAndRel \<phi>' conf))"
| "deval j ts db (DNeg \<phi>) =
     (let (xs, \<phi>') = deval j ts db \<phi>
      in (map (\<lambda>r. if r = {} then {[]} else {}) xs, DNeg \<phi>'))"
| "deval j ts db (DExists \<phi> drop0) =
     (let (xs, \<phi>') = deval j ts db \<phi>
      in (if drop0 then map (\<lambda>r. tl ` r) xs else xs, DExists \<phi>' drop0))"
| "deval j ts db (DAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = deval j ts db \<phi> in (map (uagg g0 \<omega> f k pos) xs, DAgg g0 \<omega> f k pos \<phi>'))"
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
        in (if first then {} # zs else zs, DPrev I \<phi>' False buf' nts'))"
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
     (let (xs, \<phi>') = deval j ts db \<phi> in (map (uassign p t) xs, DAndAssign p t \<phi>'))"
| "deval j ts db (DTP mt i) =
     (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) [i..<j], DTP mt j)"
| "deval j ts db (DTS mt) = (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) ts, DTS mt)"
| "deval j ts db (DLet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = deval j ts db \<phi>;
          (ys, \<psi>') = deval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, DLet p m \<phi>' \<psi>'))"
| "deval j ts db (DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     (let (xs, \<phi>) = deval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = deval j ts db0 \<psi>;
          (rs, \<rho>) = deval j ts db0 \<rho>;
          (zs0_out, jfrz, fl, \<alpha>s, lr) =
            (let zs0_out = drop (jfrz - jpsi0) zs0;
                 \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
             in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
               case lv of None \<Rightarrow> None | Some g \<Rightarrow>
                 if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
                 then Some (g, deval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
                 else None));
          (ys, \<alpha>s', lv, \<rho>, w, pR, tq, rb) = frz_live_loop size (deval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
            fl d po j jfrz \<alpha>s lr (\<rho>, w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
              drop (min jfrz (pR + length rs) - (pR - length rb)) (rb @ rs))
      in (zs0_out @ ys, DFrz p m \<phi> \<psi> (jfrz + length ys) (jpsi0 + length zs0) (jphi + length xs) \<alpha>s' \<rho> w pR tq rb d po ng
        (frz_keep_lv (if po then None else lv) \<rho>L) (frz_keep_st (if po then None else lv) \<rho>L)))"
| "deval j ts db (DLetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
          (ys, \<psi>) = deval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, DLetPast p m \<phi> \<psi> i buf))"
| "deval j ts db (DTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = deval j ts db \<phi>; (ys, \<psi>') = deval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
            (mbuf2_add xs ys dbuf) (nts @ ts)
      in (zs, DTrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "deval j ts db (DAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> dbuf2 nts daux) =
     (let (as, \<alpha>') = deval j ts db \<alpha>; (xs, \<phi>') = deval j ts db \<phi>;
          (ys, \<psi>') = deval j ts db \<psi>;
          ((ws, daux'), dbuf2', nts') = mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (ws @ [if gmmtaux_empty ax then None
                      else Some (gresult_mmtaux dags ax)], ax)) ([], daux)
            (mbuf2_add xs ys dbuf2) (nts @ ts);
          (zs, dbuf1') = mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> dbin_join pl r1 True z) (mbuf2_add as ws dbuf1)
      in (zs, DAndTrigger pl \<alpha>' dbuf1' dags \<phi>' \<psi>' dbuf2' nts' daux'))"
| "deval j ts db (DMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (deval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mbufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @ [z], ax)) ([], daux) (mbufn_add (map fst R) dbuf) 0 (nts @ ts)
      in (zs, DMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "deval j ts db (DMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (deval j ts db) Ld;
          (daux', dbuf', nt, nts') = mbufnt_take
             (\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels)
             daux (mbufn_add (map fst R) dbuf) t (nts @ ts);
          (zs, daux'') = geval_matchF I mr nt daux'
      in (zs, DMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
  by pat_completeness (simp_all only: prod.inject dformula.inject dformula.distinct simp_thms)

text \<open>The freeze node re-enters the evaluator on its body's \<^emph>\<open>updated\<close> state, which is
  not a subterm of the node, so the recursion is not structural and termination goes by the
  formula's size -- exactly as the kernel's own evaluator does it.  Evaluation preserves that
  size, which is the fact that makes the measure decrease.\<close>

lemma size_list_cong:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> size_list f xs = size_list g ys"
  by (induct xs arbitrary: ys) auto

lemma psize_snd_deval:
  "deval_dom (j, ts, db, \<phi>) \<Longrightarrow> size (snd (deval j ts db \<phi>)) = size \<phi>"
proof (induct rule: deval.pinduct)
  case (11 j ts db I \<phi> first buf nts) \<comment> \<open>\<^const>\<open>DPrev\<close>\<close>
  obtain xs \<phi>' where \<phi>': "deval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "mprev_next I (buf @ xs) (nts @ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "size \<phi>' = size \<phi>"
    using 11(2) \<phi>' by simp
  then show ?case
    by (simp add: deval.psimps(11)[OF 11(1)] \<phi>' mp)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) \<comment> \<open>\<^const>\<open>DFrz\<close>\<close>
  let ?db0 = "Mapping.update (p, m) [] db"
  obtain xs \<phi>' where \<phi>': "deval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs0 \<psi>' where \<psi>': "deval j ts ?db0 \<psi> = (zs0, \<psi>')"
    by fastforce
  obtain rs \<rho>' where \<rho>': "deval j ts ?db0 \<rho> = (rs, \<rho>')"
    by fastforce
  have s\<phi>: "size \<phi>' = size \<phi>"
    using 20(2) \<phi>' by simp
  have s\<psi>: "size \<psi>' = size \<psi>"
    using 20(3)[OF \<phi>'[symmetric] refl refl] \<psi>' by simp
  have s\<rho>: "size \<rho>' = size \<rho>"
    using 20(4)[OF \<phi>'[symmetric] refl refl \<psi>'[symmetric] refl] \<rho>' by simp
  obtain zo jf fl as lr where st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, deval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (zo, jf, fl, as, lr)"
    by (rule prod_cases5)
  obtain ys as' lv' s' where lp0: "frz_live_loop size (deval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
      fl d po j jf as lr (\<rho>', w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
        drop (min jf (pR + length rs) - (pR - length rb)) (rb @ rs)) = (ys, as', lv', s')"
    by (metis prod_cases4)
  obtain \<rho>'' w' pR' tq' rb' where s': "s' = (\<rho>'', w', pR', tq', rb')"
    by (metis prod_cases5)
  have s\<rho>'': "size \<rho>'' = size \<rho>"
    using frz_live_loop_size[OF lp0] s\<rho> s' by simp
  have "snd (deval j ts db (DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)) =
    DFrz p m \<phi>' \<psi>' (jf + length ys) (jpsi0 + length zs0) (jphi + length xs) as' \<rho>'' w' pR' tq' rb' d po ng
      (frz_keep_lv (if po then None else lv') \<rho>L) (frz_keep_st (if po then None else lv') \<rho>L)"
    by (simp only: deval.psimps(20)[OF 20(1)] \<phi>' \<psi>' \<rho>' st lp0[unfolded s'] Let_def[where s = ?db0]
        Let_def[where s = "(xs, \<phi>')"] Let_def[where s = "(zs0, \<psi>')"] Let_def[where s = "(rs, \<rho>')"]
        Let_def[where s = "(zo, jf, fl, as, lr)"] Let_def[where s = "(ys, as', lv', \<rho>'', w', pR', tq', rb')"]
        prod.case snd_conv)
  then show ?case
    using s\<phi> s\<psi> s\<rho>'' by simp
next
  case (21 j ts db p m \<phi> \<psi> i buf) \<comment> \<open>\<^const>\<open>DLetPast\<close>\<close>
  obtain xs i' buf' \<phi>' where lp:
    "letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi> = (xs, i', buf', \<phi>')"
    by (metis prod_cases4)
  have "size (snd (snd (snd
      (letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi>)))) = size \<phi>"
    by (rule size_letpast_meval) (simp add: 21(2))
  then have size_\<phi>': "size \<phi>' = size \<phi>"
    by (simp add: lp)
  obtain ys \<psi>' where \<psi>': "deval j ts (Mapping.update (p, m) xs db) \<psi> = (ys, \<psi>')"
    by fastforce
  have size_\<psi>': "size \<psi>' = size \<psi>"
    using 21(3)[OF lp[symmetric] refl refl refl] \<psi>' by simp
  show ?case
    using size_\<phi>' size_\<psi>' by (simp add: deval.psimps(21)[OF 21(1)] lp \<psi>')
  \<comment> \<open>in all other cases, the claim follows directly from the IHs for the subformulas,
    since evaluation keeps the node's constructor and its non-formula arguments do not count\<close>
qed (auto simp only: prod.inject deval.psimps Let_def snd_conv fst_conv
    dformula.size list.map map_map o_apply size_list_map size_frz_keep_st cong: size_list_cong
    split: prod.splits)

lemma total_deval: "All deval_dom"
proof (relation "measure (\<lambda>(j, ts, db, \<phi>). size \<phi>)", goal_cases)
  text \<open>The live copy and the replays of @{const DFrz}, as for @{const meval}.\<close>
  case 23 \<comment> \<open>the live copy, a subterm\<close>
  then show ?case
    by simp
next
  case (24 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L x xa y xb xc xd ya xe xf yb xg xh
    yc xi yd xj yca xk ycb tsa dba \<psi>')
  have "size yb = size \<rho>"
    using psize_snd_deval[of j ts xb \<rho>] 24 by (metis snd_conv)
  then show ?case
    using 24 by simp
qed (auto simp: termination_simp dest!: psize_snd_deval dest: sym)

lemmas size_snd_deval = psize_snd_deval[OF total_deval[THEN spec]]

termination deval by (rule total_deval)

section \<open>The simulation relation\<close>

text \<open>
  @{term "dsim n ks cs tw \<phi>d \<phi>"} relates a dense formula to a kernel one whose tables are over
  the column list @{term ks}, read by the dense one over its ascending order @{term cs}.  Every
  rule carries the node's own @{const produces}, so the relation alone gives the operand
  well-formedness that the @{theory MFODL_Monitor_Dense.Dense} theorems ask for, at every node
  and after every step.
\<close>

definition dbuf2 :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> event_data mbuf2 \<Rightarrow> event_data mbuf2 \<Rightarrow> bool" where
  "dbuf2 k1 c1 k2 c2 buf dbuf \<longleftrightarrow>
     list_all (ftable k1) (fst buf) \<and> list_all (ftable k2) (snd buf) \<and>
     dbuf = (map (dtabc k1 c1) (fst buf), map (dtabc k2 c2) (snd buf))"

definition dbufn :: "cols list \<Rightarrow> cols list \<Rightarrow> event_data mbufn \<Rightarrow> event_data mbufn \<Rightarrow> bool" where
  "dbufn kss css buf dbuf \<longleftrightarrow> length buf = length css \<and> length kss = length css \<and>
     (\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)) \<and>
     dbuf = map2 map (map2 dtabc kss css) buf"

text \<open>
  The relation carries a timestamp bound: @{term "dsim n ks cs tw \<phi>d \<phi>"} is read as \<open>every
  timestamp stored anywhere inside is at most tw\<close>.  Only the temporal nodes look at it -- the
  verified Since structure accepts a new timestamp only at or after the one it is already at, and
  a fresh batch of timestamps arrives at the node from outside, where the relation cannot see it.
  Every other rule carries the bound without using it.  After a step the bound moves to the last
  timestamp of the batch.
\<close>

subsection \<open>The aggregation at a structure's output\<close>

text \<open>
  The kernel fuses an aggregation into the Since and the Until: the structure is stepped at the
  operand's columns and the aggregation is applied to whatever it reports.  The dense side runs
  the structure without one -- @{const dargs} clears the field -- and applies the dense
  aggregation afterwards, so the two output lists are not reorderings of each other but two images
  of one list of windows.  That is what the relation below says.  With no aggregation it
  degenerates to the reordering, which is what the unfused nodes use.
\<close>

definition dsres :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> event_data table list \<Rightarrow> event_data table list \<Rightarrow> bool"
  where "dsres ks cs args zs dzs \<longleftrightarrow> (\<exists>ws. list_all (table ks) ws \<and>
     zs = map (eval_args_agg args) ws \<and> dzs = map (dtabc ks cs) ws)"

lemma dsres_Nil[simp]: "dsres ks cs args [] []"
  unfolding dsres_def by (intro exI[of _ "[]"]) simp

lemma dsres_Cons:
  assumes w: "table ks w" and r: "dsres ks cs args zs dzs"
  shows "dsres ks cs args (eval_args_agg args w # zs) (dtabc ks cs w # dzs)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (dtabc ks cs) ws" using r unfolding dsres_def by blast
  show ?thesis unfolding dsres_def by (intro exI[of _ "w # ws"]) (use w ws in simp)
qed

lemma dsres_append:
  assumes a: "dsres ks cs args zs dzs" and b: "dsres ks cs args us dus"
  shows "dsres ks cs args (zs @ us) (dzs @ dus)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (dtabc ks cs) ws" using a unfolding dsres_def by blast
  obtain vs where vs: "list_all (table ks) vs" "us = map (eval_args_agg args) vs"
    "dus = map (dtabc ks cs) vs" using b unfolding dsres_def by blast
  show ?thesis unfolding dsres_def
    by (intro exI[of _ "ws @ vs"]) (use ws vs in simp)
qed

lemma dsres_rev:
  assumes "dsres ks cs args zs dzs"
  shows "dsres ks cs args (rev zs) (rev dzs)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (dtabc ks cs) ws" using assms unfolding dsres_def by blast
  show ?thesis unfolding dsres_def
    by (intro exI[of _ "rev ws"]) (use ws in \<open>simp add: rev_map list_all_iff\<close>)
qed

lemma dsres_rev':
  "rev zs = us \<Longrightarrow> rev dzs = dus \<Longrightarrow> dsres ks cs args zs dzs \<Longrightarrow> dsres ks cs args us dus"
  using dsres_rev by blast

lemma dsres_none:
  assumes "args_agg args = None" and "dsres ks cs args zs dzs"
  shows "dzs = map (dtabc ks cs) zs"
  using assms unfolding dsres_def eval_args_agg_def by auto

text \<open>The window a firing reports is a union of the auxiliary list's tables, so it is a table over
  the node's columns; the kernel's structure reports its aggregation and the dense one reports its
  reordering -- or, for the window with the aggregate fused in, the dense aggregation of its
  reordering.  The relation below carries that post-function; @{const dsres} is its identity
  instance.\<close>

definition dsresh :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> (event_data table \<Rightarrow> event_data table) \<Rightarrow>
    event_data table list \<Rightarrow> event_data table list \<Rightarrow> bool"
  where "dsresh ks cs args h zs dzs \<longleftrightarrow> (\<exists>ws. list_all (table ks) ws \<and>
     zs = map (eval_args_agg args) ws \<and> dzs = map (h \<circ> dtabc ks cs) ws)"

lemma dsresh_id: "dsresh ks cs args id zs dzs \<longleftrightarrow> dsres ks cs args zs dzs"
  unfolding dsresh_def dsres_def by simp

lemma dsresh_Nil[simp]: "dsresh ks cs args h [] []"
  unfolding dsresh_def by (intro exI[of _ "[]"]) simp

lemma dsresh_Cons:
  assumes w: "table ks w" and r: "dsresh ks cs args h zs dzs"
  shows "dsresh ks cs args h (eval_args_agg args w # zs) (h (dtabc ks cs w) # dzs)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> dtabc ks cs) ws" using r unfolding dsresh_def by blast
  show ?thesis unfolding dsresh_def by (intro exI[of _ "w # ws"]) (use w ws in simp)
qed

lemma dsresh_append:
  assumes a: "dsresh ks cs args h zs dzs" and b: "dsresh ks cs args h us dus"
  shows "dsresh ks cs args h (zs @ us) (dzs @ dus)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> dtabc ks cs) ws" using a unfolding dsresh_def by blast
  obtain vs where vs: "list_all (table ks) vs" "us = map (eval_args_agg args) vs"
    "dus = map (h \<circ> dtabc ks cs) vs" using b unfolding dsresh_def by blast
  show ?thesis unfolding dsresh_def
    by (intro exI[of _ "ws @ vs"]) (use ws vs in simp)
qed

lemma dsresh_rev:
  assumes "dsresh ks cs args h zs dzs"
  shows "dsresh ks cs args h (rev zs) (rev dzs)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> dtabc ks cs) ws" using assms unfolding dsresh_def by blast
  show ?thesis unfolding dsresh_def
    by (intro exI[of _ "rev ws"]) (use ws in \<open>simp add: rev_map\<close>)
qed

lemma dsresh_rev':
  "rev zs = us \<Longrightarrow> rev dzs = dus \<Longrightarrow> dsresh ks cs args h zs dzs \<Longrightarrow> dsresh ks cs args h us dus"
  using dsresh_rev by blast

lemma table_foldr_Un: "list_all (table ks) ws \<Longrightarrow> table ks (foldr (\<union>) ws {})"
  by (induct ws) (auto simp: table_def)

lemma dsresh_result:
  assumes vd: "dsxaux' kR cR cL args cur da al"
    and vw: "valid_mmasaux args cur wa al"
  shows "dsresh kR cR args (dsx_post da) [result_mmasaux args wa] [dsx_result (dargs cR cL args) da]"
proof -
  let ?W = "foldr (\<union>) [rel. (t, rel) \<leftarrow> al, memL (args_ivl args) (cur - t)] {}"
  have tw: "table kR ?W"
    by (rule table_foldr_Un) (use dsxaux'_tables[OF vd] in \<open>auto simp: list_all_iff\<close>)
  have e: "result_mmasaux args wa = eval_args_agg args ?W"
    by (rule default_mmasaux.valid_result_msaux[OF vw])
  have d: "dsx_result (dargs cR cL args) da = dsx_post da (dtabc kR cR ?W)"
    by (rule dsxaux'_result[OF vd])
  show ?thesis unfolding e d by (rule dsresh_Cons[OF tw dsresh_Nil])
qed

subsection \<open>The Since structure at the dense frame, and its buffer\<close>

text \<open>
  The dense Since node runs the verified structure at @{const dargs}.  What the node carries is
  the pair of structures -- the kernel's and the dense one -- related through the abstract
  auxiliary list they are both valid for, together with the two buffers.  The current timestamp
  is shared: the structure's, and the lower bound on the timestamps still in the buffer.  The
  left operand's tables enter the buffer at their own columns.
\<close>

definition dsince_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    mmasaux \<Rightarrow> dsaux_x \<Rightarrow> event_data mbuf2S \<Rightarrow> event_data mbuf2S \<Rightarrow> bool" where
  "dsince_rel kR cR kL cL args tw aux daux buf dbuf \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmasaux args cur aux auxlist \<and>
        dsxaux' kR cR cL args cur daux auxlist \<and> cur \<le> tw \<and>
        (case buf of (xs, ys, tss, sk) \<Rightarrow>
           list_all (ftable kL) xs \<and> list_all (ftable kR) ys \<and>
           sorted tss \<and> (\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw) \<and>
           dbuf = (map (dtabc kL cL) xs, map (dtabc kR cR) ys, tss, sk)))"

lemma dsince_relI:
  "valid_mmasaux args cur aux auxlist \<Longrightarrow> dsxaux' kR cR cL args cur daux auxlist \<Longrightarrow>
   cur \<le> tw \<Longrightarrow>
   list_all (ftable kL) xs \<Longrightarrow> list_all (ftable kR) ys \<Longrightarrow>
   sorted tss \<Longrightarrow> \<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw \<Longrightarrow>
   dsince_rel kR cR kL cL args tw aux daux (xs, ys, tss, sk)
     (map (dtabc kL cL) xs, map (dtabc kR cR) ys, tss, sk)"
  unfolding dsince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma dsince_relE:
  assumes "dsince_rel kR cR kL cL args tw aux daux (xs, ys, tss, sk) dbuf"
  obtains cur auxlist where "valid_mmasaux args cur aux auxlist"
    and "dsxaux' kR cR cL args cur daux auxlist" and "cur \<le> tw"
    and "list_all (ftable kL) xs" and "list_all (ftable kR) ys"
    and "sorted tss" and "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and "dbuf = (map (dtabc kL cL) xs, map (dtabc kR cR) ys, tss, sk)"
  using assms unfolding dsince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma dsince_relD_buf:
  "dsince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow>
     dbuf = (map (dtabc kL cL) (fst buf), map (dtabc kR cR) (fst (snd buf)),
             fst (snd (snd buf)), snd (snd (snd buf)))"
  by (cases buf) (auto elim!: dsince_relE)

text \<open>Widening the bound is harmless, which is what the node needs when a new batch of
  timestamps arrives.\<close>

lemma dsince_rel_mono:
  "dsince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow> tw \<le> tw' \<Longrightarrow>
     dsince_rel kR cR kL cL args tw' aux daux buf dbuf"
  unfolding dsince_rel_def by (fastforce simp del: valid_mmasaux.simps)

text \<open>A fresh batch of operand tables and timestamps enters the buffer at both representations at
  once.  The batch's timestamps are all at or after the old bound, and the buffer's are all at or
  before it, so the concatenation stays sorted and the new bound is the batch's last timestamp.\<close>

lemma dsince_rel_add:
  assumes r: "dsince_rel kR cR kL cL args tw aux daux buf dbuf"
    and lx: "list_all (ftable kL) xs" and ly: "list_all (ftable kR) ys"
    and s: "sorted ts" and b: "\<forall>t \<in> set ts. tw \<le> t"
  shows "dsince_rel kR cR kL cL args (dnext tw ts) aux daux (mbuf2S_add xs ys ts buf)
     (mbuf2S_add (map (dtabc kL cL) xs) (map (dtabc kR cR) ys) ts dbuf)"
proof (cases buf)
  case (fields us vs tss sk)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' kR cR cL args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable kL) us" and lv: "list_all (ftable kR) vs"
    and st: "sorted tss" and ct: "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and dbuf: "dbuf = (map (dtabc kL cL) us, map (dtabc kR cR) vs, tss, sk)"
    using r unfolding fields by (rule dsince_relE)
  have "sorted (tss @ ts)" using st s ct b
    by (fastforce simp: sorted_append intro: order_trans)
  moreover have "\<forall>t \<in> set (tss @ ts). cur \<le> t \<and> t \<le> dnext tw ts"
    using ct b ctw dnext_ge[OF b] dnext_bound[OF s] by fastforce
  ultimately show ?thesis unfolding fields dbuf
    using dsince_relI[OF vw vd order_trans[OF ctw dnext_ge[OF b]],
      where xs = "us @ xs" and ys = "vs @ ys" and tss = "tss @ ts" and sk = sk and kL = kL]
      lu lx lv ly
    by simp
qed

subsection \<open>The Until structure at the dense frame, and its buffer\<close>

text \<open>
  The Until node's state is the pair of verified structures, related through the abstract
  auxiliary list they are both valid for, together with the current timestamp.  Since the
  structure is stepped from inside a buffer traversal, that part is factored out on its own.
\<close>

definition duaux_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> duaux_x \<Rightarrow> bool" where
  "duaux_rel kR cR kL cL args cur aux daux \<longleftrightarrow>
     (\<exists>auxlist. valid_muaux_dq args cur aux auxlist \<and>
        duxaux' kL cL kR cR args cur daux auxlist)"

lemma duaux_rel_step:
  assumes v: "duaux_rel kR cR kL cL args u aux daux"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and t1: "table kL a" and t2: "table kR b" and f2: "finite b"
    and ut: "u \<le> t"
  shows "duaux_rel kR cR kL cL args t (add_new_muaux_dq args a b t aux)
     (dux_add_new (dargs cR cL args) (dmsk cR cL)
       (dtabc kL cL a) (dtabc kR cR b) t daux)"
proof -
  obtain auxlist where vw: "valid_muaux_dq args u aux auxlist"
    and vd: "duxaux' kL cL kR cR args u daux auxlist"
    using v unfolding duaux_rel_def by blast
  have "valid_muaux_dq args t (add_new_muaux_dq args a b t aux) (update_until args a b t auxlist)"
    by (rule valid_add_new_muaux_dq[OF vw _ _ ut]) (use t1 t2 aL aR in simp_all)
  moreover have "duxaux' kL cL kR cR args t
      (dux_add_new (dargs cR cL args) (dmsk cR cL)
        (dtabc kL cL a) (dtabc kR cR b) t daux)
      (update_until args a b t auxlist)"
    by (rule duxaux'_add_new[OF vd fR fL sub aL aR t1 t2 f2 ut])
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
  assumes v: "duaux_rel kR cR kL cL args cur aux daux" and nt: "cur \<le> nt"
    and we: "eval_muaux_dq args nt aux = (zs, aux')"
    and de: "dux_eval (dargs cR cL args) nt daux = (dzs, daux')"
  shows "dsresh kR cR args (dux_post daux) zs dzs \<and>
    duaux_rel kR cR kL cL args cur aux' daux'"
proof -
  obtain auxlist where vw: "valid_muaux_dq args cur aux auxlist"
    and vd: "duxaux' kL cL kR cR args cur daux auxlist"
    using v unfolding duaux_rel_def by blast
  obtain res auxlist' where eu: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
    by (cases "eval_until (args_ivl args) nt auxlist")
  have w: "valid_muaux_dq args cur aux' auxlist' \<and> zs = map (eval_args_agg args) res"
    by (rule valid_eval_muaux_dq[OF vw nt we eu])
  have d: "dzs = map (dux_post daux \<circ> dtabc kR cR) res \<and>
      duxaux' kL cL kR cR args cur daux' auxlist'"
    by (rule duxaux'_eval[OF vd nt de eu])
  have tr: "list_all (table kR) res"
  proof (unfold list_all_iff, safe)
    fix x assume "x \<in> set res"
    then obtain t a1 where "(t, a1, x) \<in> set auxlist"
      unfolding eval_until_res[OF eu] by (auto dest!: set_takeWhileD)
    then show "table kR x" using duxaux'_tables[OF vd] by auto
  qed
  show ?thesis using w d tr unfolding duaux_rel_def dsresh_def by blast
qed

text \<open>The node relation.  The stored timestamp is at or after the structure's current one and
  at or before the bound, and so is every timestamp still queued.\<close>

definition duntil_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> duaux_x \<Rightarrow> event_data mbuf2 \<Rightarrow> event_data mbuf2 \<Rightarrow>
    ts list \<Rightarrow> bool" where
  "duntil_rel kR cR kL cL args tw t aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur. duaux_rel kR cR kL cL args cur aux daux \<and> cur \<le> t \<and> t \<le> tw \<and>
        list_all (ftable kL) (fst buf) \<and>
        list_all (ftable kR) (snd buf) \<and>
        dbuf = (map (dtabc kL cL) (fst buf), map (dtabc kR cR) (snd buf)) \<and>
        sorted nts \<and> (\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw))"

text \<open>
  One firing of the Until node: the buffer traversal steps the two structures in lockstep, and
  then one evaluation at the timestamp the traversal reports yields the reordering of what the
  kernel's one yields.
\<close>

lemma until_step_rel:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and rel: "duntil_rel kR cR kL cL args tw t aux daux buf dbuf nts"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and s: "sorted tss" and bnd: "\<forall>u \<in> set tss. tw \<le> u"
    and we: "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ tss)
      = (aux1, buf1, nt, nts1)"
    and de: "mbuf2t_take (dux_add_new (dargs cR cL args) (dmsk cR cL)) daux
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) t (nts @ tss)
      = (daux1, dbuf1, dnt, dnts1)"
    and wev: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    and dev: "dux_eval (dargs cR cL args) dnt daux1 = (dzs, daux2)"
  shows "dsresh kR cR args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
     dbuf1 = (map (dtabc kL cL) (fst buf1), map (dtabc kR cR) (snd buf1)) \<and>
     duntil_rel kR cR kL cL args (dnext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
proof -
  obtain cur where vr: "duaux_rel kR cR kL cL args cur aux daux"
    and ct: "cur \<le> t" and ttw: "t \<le> tw"
    and lu: "list_all (ftable kL) (fst buf)"
    and lv: "list_all (ftable kR) (snd buf)"
    and dbe: "dbuf = (map (dtabc kL cL) (fst buf), map (dtabc kR cR) (snd buf))"
    and sn: "sorted nts" and cn: "\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw"
    using rel unfolding duntil_rel_def by blast
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mda: "mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf
      = (map (dtabc kL cL) us, map (dtabc kR cR) vs)"
    unfolding dbe us_def vs_def by (cases buf) simp
  have lus: "list_all (ftable kL) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable kR) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a b t' u z z'. a \<in> set us \<Longrightarrow> b \<in> set vs \<Longrightarrow>
      duaux_rel kR cR kL cL args u z z' \<Longrightarrow> u \<le> t' \<Longrightarrow>
      duaux_rel kR cR kL cL args t' (add_new_muaux_dq args a b t' z)
        (dux_add_new (dargs cR cL args) (dmsk cR cL)
          (dtabc kL cL a) (dtabc kR cR b) t' z')"
    using lus lvs by (intro duaux_rel_step[OF _ fR fL sub aL aR]) (auto simp: list_all_iff)
  have sts: "sorted (nts @ tss)"
    using sn s cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>u \<in> set (nts @ tss). cur \<le> u" using cn bnd ct ttw by fastforce
  have tdn: "t \<le> dnext tw tss" using ttw dnext_ge[OF bnd] by simp
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> dnext tw tss"
    using cn dnext_ge[OF bnd] dnext_bound[OF s] by fastforce
  have we': "mbuf2t_take (add_new_muaux_dq args) aux (us, vs) t (nts @ tss)
      = (aux1, (b1, b2), nt, nts1)" using we unfolding ma bfs by simp
  have de': "mbuf2t_take (dux_add_new (dargs cR cL args) (dmsk cR cL)) daux
      (map (dtabc kL cL) us, map (dtabc kR cR) vs) t (nts @ tss) = (daux1, dbuf1, dnt, dnts1)"
    using de unfolding mda by simp
  have R: "(\<exists>u. duaux_rel kR cR kL cL args u aux1 daux1 \<and> u \<le> nt \<and>
        (\<forall>v \<in> set nts1. u \<le> v)) \<and> sorted nts1 \<and>
      (nt = t \<or> nt \<in> set (nts @ tss)) \<and> set nts1 \<subseteq> set (nts @ tss) \<and>
      dbuf1 = (map (dtabc kL cL) b1, map (dtabc kR cR) b2) \<and> dnt = nt \<and> dnts1 = nts1"
    by (rule mbuf2t_take_rel_ts[OF step vr ct sts cts we' de'])
  obtain u where vu: "duaux_rel kR cR kL cL args u aux1 daux1" and unt: "u \<le> nt"
    and un: "\<forall>v \<in> set nts1. u \<le> v" using R by blast
  have dn: "dnt = nt" and dns: "dnts1 = nts1" and sn1: "sorted nts1"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf: "dbuf1 = (map (dtabc kL cL) b1, map (dtabc kR cR) b2)" using R by blast+
  have ntdn: "nt \<le> dnext tw tss" using R tdn bound by blast
  have pst: "dux_post daux1 = dux_post daux" by (rule dux_post_mbuf2t_take[OF de])
  have ev: "dsresh kR cR args (dux_post daux) zs dzs \<and>
      duaux_rel kR cR kL cL args u aux2 daux2"
    using duaux_rel_eval[OF vu unt wev dev[unfolded dn]] pst by simp
  have sb: "set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs" by (rule mbuf2t_take_sub[OF we'])
  have lb1: "list_all (ftable kL) b1" using sb lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable kR) b2" using sb lvs by (auto simp: list_all_iff)
  have "duaux_rel kR cR kL cL args u aux2 daux2 \<and> u \<le> nt \<and> nt \<le> dnext tw tss \<and>
      list_all (ftable kL) (fst buf1) \<and>
      list_all (ftable kR) (snd buf1) \<and>
      dbuf1 = (map (dtabc kL cL) (fst buf1), map (dtabc kR cR) (snd buf1)) \<and>
      sorted nts1 \<and> (\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> dnext tw tss)"
    using ev unt ntdn lb1 lb2 dbf sn1 un sub1 bound bfs by auto
  then have "duntil_rel kR cR kL cL args (dnext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
    unfolding duntil_rel_def by blast
  then show ?thesis using ev dn dns dbf bfs by simp
qed

subsection \<open>The Trigger structure at the dense frame, and its buffer\<close>

text \<open>
  The trigger node carries the pair of structures, related through the abstract auxiliary list
  they are both valid for, together with the two buffers and the pending timestamps.  Unlike the
  Since and the Until, the structure is stepped and read in the same traversal, so the output
  list is part of what the step relates.  Each operand's tables enter the buffer at their own
  columns.
\<close>

definition dtrigger_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    event_data mmtaux \<Rightarrow> event_data gmmtaux \<Rightarrow> event_data mbuf2 \<Rightarrow>
    event_data mbuf2 \<Rightarrow> ts list \<Rightarrow> bool" where
  "dtrigger_rel kR cR kL cL args tw aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmtaux args cur aux auxlist \<and>
        (\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r) \<and>
        dtaux kL cL kR cR args cur daux auxlist \<and> cur \<le> tw \<and>
        list_all (ftable kL) (fst buf) \<and>
        list_all (ftable kR) (snd buf) \<and>
        sorted nts \<and> (\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw) \<and>
        dbuf = (map (dtabc kL cL) (fst buf), map (dtabc kR cR) (snd buf)))"

lemma dtrigger_relI:
  "valid_mmtaux args cur aux auxlist \<Longrightarrow>
   (\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r) \<Longrightarrow>
   dtaux kL cL kR cR args cur daux auxlist \<Longrightarrow> cur \<le> tw \<Longrightarrow>
   list_all (ftable kL) xs \<Longrightarrow> list_all (ftable kR) ys \<Longrightarrow>
   sorted nts \<Longrightarrow> \<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw \<Longrightarrow>
   dtrigger_rel kR cR kL cL args tw aux daux (xs, ys)
     (map (dtabc kL cL) xs, map (dtabc kR cR) ys) nts"
  unfolding dtrigger_rel_def
  by (intro exI[where x = cur] exI[where x = auxlist] conjI) simp_all

lemma dtrigger_relE:
  assumes "dtrigger_rel kR cR kL cL args tw aux daux buf dbuf nts"
  obtains cur auxlist where "valid_mmtaux args cur aux auxlist"
    and "\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r"
    and "dtaux kL cL kR cR args cur daux auxlist" and "cur \<le> tw"
    and "list_all (ftable kL) (fst buf)"
    and "list_all (ftable kR) (snd buf)"
    and "sorted nts" and "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and "dbuf = (map (dtabc kL cL) (fst buf), map (dtabc kR cR) (snd buf))"
  using assms unfolding dtrigger_rel_def by (elim exE conjE) (rule that)

text \<open>One firing of the trigger structure: the buffer traversal that steps it once per pending
  timestamp and collects what it answers.  The two runs stay in step by
  @{thm [source] mbuf2T_take_rel}, and each individual step is @{thm [source] dtaux_update}
  followed by @{thm [source] dtaux_result}.\<close>

lemma dtrigger_step_rel:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and m0: "mem (args_ivl args) 0"
    and rel: "dtrigger_rel kR cR kL cL args tw aux daux buf dbuf nts"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and st: "sorted tss" and bnd: "\<forall>v \<in> set tss. tw \<le> v"
    and we: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
        in (zs @ [z], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ tss)
      = ((zs, aux1), buf1, nts1)"
    and de: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = gupdate_mmtaux (dargs cR cL args) t r1 r2 ax
        in (zs @ [gresult_mmtaux (dargs cR cL args) ax], ax)) ([], daux)
        (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) (nts @ tss)
      = ((dzs, daux1), dbuf1, dnts1)"
  shows "dzs = map (dtabc kR cR) zs \<and> dnts1 = nts1 \<and>
     dtrigger_rel kR cR kL cL args (dnext tw tss) aux1 daux1 buf1 dbuf1 nts1"
proof -
  obtain cur auxlist where vw: "valid_mmtaux args cur aux auxlist"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r"
    and vd: "dtaux kL cL kR cR args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable kL) (fst buf)"
    and lv: "list_all (ftable kR) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and dbf: "dbuf = (map (dtabc kL cL) (fst buf), map (dtabc kR cR) (snd buf))"
    using rel by (rule dtrigger_relE)
  have m0': "mem (args_ivl (dargs cR cL args)) 0" using m0 by simp
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  define g where "g = (\<lambda>r1 r2 t (zs :: event_data table list, ax).
    let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
    in (zs @ [z], ax))"
  define gd where "gd = (\<lambda>r1 r2 t (zs :: event_data table list, ax).
    let ax = gupdate_mmtaux (dargs cR cL args) t r1 r2 ax
    in (zs @ [gresult_mmtaux (dargs cR cL args) ax], ax))"
  define R where "R = (\<lambda>v (pr :: event_data table list \<times> event_data mmtaux)
      (dpr :: event_data table list \<times> event_data gmmtaux).
    (\<exists>al. valid_mmtaux args v (snd pr) al \<and>
       (\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r) \<and>
       dtaux kL cL kR cR args v (snd dpr) al) \<and>
     fst dpr = map (dtabc kR cR) (fst pr))"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mad: "mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf
      = (map (dtabc kL cL) us, map (dtabc kR cR) vs)"
    using dbf by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable kL) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable kR) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a c v w z z'. a \<in> set us \<Longrightarrow> c \<in> set vs \<Longrightarrow> R w z z' \<Longrightarrow> w \<le> v \<Longrightarrow>
      R v (g a c v z) (gd (dtabc kL cL a) (dtabc kR cR c) v z')"
  proof -
    fix a c v w and z :: "event_data table list \<times> event_data mmtaux"
      and z' :: "event_data table list \<times> event_data gmmtaux"
    assume au: "a \<in> set us" and cv: "c \<in> set vs" and q: "R w z z'" and wv: "w \<le> v"
    have t1: "ftable kL a" using au lus by (simp add: list_all_iff)
    have t2: "ftable kR c" using cv lvs by (simp add: list_all_iff)
    obtain al where vwz: "valid_mmtaux args w (snd z) al"
      and wfz: "\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r"
      and vdz: "dtaux kL cL kR cR args w (snd z') al"
      using q unfolding R_def by blast
    have fz: "fst z' = map (dtabc kR cR) (fst z)" using q unfolding R_def by blast
    define al' where "al' = filter (\<lambda>(t, _). memR (args_ivl args) (v - t)) al @ [(v, a, c)]"
    have vw': "valid_mmtaux args v (update_mmtaux args v a c (snd z)) al'"
      unfolding al'_def
      by (rule valid_update_mmtaux[OF wv _ _ vwz]) (use t1 t2 aL aR in simp_all)
    have wf': "\<forall>(t, l, r) \<in> set al'. ftable kL l \<and> ftable kR r"
      using wfz t1 t2 unfolding al'_def by auto
    have vd': "dtaux kL cL kR cR args v
        (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z')) al'"
      unfolding al'_def by (rule dtaux_update[OF vdz wv fR fL sub]) (use t1 t2 in simp_all)
    have ne: "\<not> gmmtaux_empty (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a)
        (dtabc kR cR c) (snd z'))"
      by (rule gupdate_mmtaux_not_empty[OF m0'])
    have res: "result_mmtaux args (update_mmtaux args v a c (snd z))
        = trigger_results args v al'" by (rule valid_result_mmtaux[OF vw'])
    have dres: "gresult_mmtaux (dargs cR cL args)
          (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z'))
        = dtabc kR cR (snd (trigger_results args v al'))"
      by (rule dtaux_result[OF vd' ne fR fL sub aL aR])
    have dres': "gresult_mmtaux (dargs cR cL args)
          (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z'))
        = dtabc kR cR (snd (result_mmtaux args (update_mmtaux args v a c (snd z))))"
      unfolding res by (rule dres)
    have gz: "g a c v z
        = (fst z @ [snd (result_mmtaux args (update_mmtaux args v a c (snd z)))],
           update_mmtaux args v a c (snd z))"
      by (cases z) (simp add: g_def Let_def case_prod_beta)
    have gdz: "gd (dtabc kL cL a) (dtabc kR cR c) v z'
        = (fst z' @ [gresult_mmtaux (dargs cR cL args)
             (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z'))],
           gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z'))"
      by (cases z') (simp add: gd_def Let_def case_prod_beta)
    show "R v (g a c v z) (gd (dtabc kL cL a) (dtabc kR cR c) v z')"
      unfolding R_def gz gdz fst_conv snd_conv
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
  have de': "mbuf2T_take gd ([], daux) (map (dtabc kL cL) us, map (dtabc kR cR) vs)
      (nts @ tss) = ((dzs, daux1), dbuf1, dnts1)"
    using de unfolding mad gd_def by simp
  have Rr: "(\<exists>u. R u (zs, aux1) (dzs, daux1) \<and> u \<le> dnext tw tss \<and> (\<forall>t \<in> set nts1. u \<le> t)) \<and>
      sorted nts1 \<and> set nts1 \<subseteq> set (nts @ tss) \<and> set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs \<and>
      dbuf1 = (map (dtabc kL cL) b1, map (dtabc kR cR) b2) \<and> dnts1 = nts1"
    by (rule mbuf2T_take_rel[where R = R and f = g and g = gd and h = "dtabc kL cL"
        and k = "dtabc kR cR", OF step r0 sts cts bound cdn we' de'])
  obtain u where ru: "R u (zs, aux1) (dzs, daux1)" and ub: "u \<le> dnext tw tss"
    and un: "\<forall>t \<in> set nts1. u \<le> t" using Rr by blast
  have sn1: "sorted nts1" and sb1: "set b1 \<subseteq> set us" and sb2: "set b2 \<subseteq> set vs"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf1: "dbuf1 = (map (dtabc kL cL) b1, map (dtabc kR cR) b2)"
    and dn1: "dnts1 = nts1" using Rr by blast+
  have lb1: "list_all (ftable kL) b1" using sb1 lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable kR) b2" using sb2 lvs by (auto simp: list_all_iff)
  obtain al1 where v1: "valid_mmtaux args u aux1 al1"
    and w1: "\<forall>(t, l, r) \<in> set al1. ftable kL l \<and> ftable kR r"
    and d1: "dtaux kL cL kR cR args u daux1 al1" using ru unfolding R_def by auto
  have dz: "dzs = map (dtabc kR cR) zs" using ru unfolding R_def by simp
  have bnd1: "\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> dnext tw tss" using un sub1 bound by auto
  have "dtrigger_rel kR cR kL cL args (dnext tw tss) aux1 daux1 (b1, b2)
      (map (dtabc kL cL) b1, map (dtabc kR cR) b2) nts1"
    by (rule dtrigger_relI[OF v1 w1 d1 ub lb1 lb2 sn1 bnd1])
  then show ?thesis using dz dn1 bfs dbf1 by simp
qed

subsection \<open>The fused And-Trigger, and its two buffers\<close>

text \<open>
  The kernel's fused node reads the trigger structure as a pair: a column list and a table.  On a
  non-empty window the list is the trigger's own columns and the table is its answer; on an empty
  one the read is the unit table over no columns at all, which the join then lets through
  untouched.  The dense node keeps that distinction as an option -- @{term None} stands for the
  empty window and the join step skips -- so the two reads are related rather than equal.
\<close>

definition dtres :: "cols \<Rightarrow> cols \<Rightarrow> cols \<times> event_data table \<Rightarrow> event_data table option \<Rightarrow> bool"
  where
  "dtres kR cR p q \<longleftrightarrow> (case q of
      None \<Rightarrow> p = ([], unit_table)
    | Some d \<Rightarrow> fst p = kR \<and> ftable kR (snd p) \<and> d = dtabc kR cR (snd p))"

lemma dtres_join:
  assumes fK: "dframe ks cs" and fR: "dframe kR cR" and sub: "set kR \<subseteq> set ks"
    and t: "ftable ks a" and r: "dtres kR cR p q"
  shows "(case q of None \<Rightarrow> dtabc ks cs a
        | Some z \<Rightarrow> dbin_join (mk_djoin cs cR) (dtabc ks cs a) True z)
      = dtabc ks cs (bin_join ks a True (fst p) (snd p))"
proof (cases q)
  case None
  then have p: "p = ([], unit_table)" using r by (simp add: dtres_def)
  have "bin_join ks a True [] unit_table = join ks a True [] unit_table"
    by (rule bin_join_table) (use t dframeD(1)[OF fK] in simp_all)
  then have "bin_join ks a True [] unit_table = a"
    using join_unit_table(1)[OF dframeD(1)[OF fK] conjunct1[OF t]] by simp
  then show ?thesis using None unfolding p by simp
next
  case (Some d)
  then have fp: "fst p = kR" and tp: "ftable kR (snd p)"
    and d: "d = dtabc kR cR (snd p)" using r by (auto simp: dtres_def)
  have sc: "set cR \<subseteq> set cs" using sub dframeD(3)[OF fK] dframeD(3)[OF fR] by simp
  have "dbin_join (mk_djoin cs cR) (dtabc ks cs a) True (dtabc kR cR (snd p))
      = dtabc (cols_union ks kR) (merge_cols cs cR) (join ks a True kR (snd p))"
    by (rule dbin_join_join[OF fK fR _ _ _ _ _]) (use t tp in auto)
  moreover have "bin_join ks a True kR (snd p) = join ks a True kR (snd p)"
    by (rule bin_join_table[OF dframeD(1)[OF fK] dframeD(1)[OF fR] conjunct1[OF t] conjunct1[OF tp]])
  ultimately show ?thesis using Some fp d
    by (simp add: cols_union_subset[OF sub] merge_cols_sub_left[OF dframeD(2)[OF fK] dframeD(2)[OF fR] sc])
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

text \<open>The node's outer buffer: the left operand's tables at the node's own columns, and the
  trigger's reads as options.\<close>

definition dandbuf :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> event_data mbuft2 \<Rightarrow>
    (event_data table list \<times> event_data table option list) \<Rightarrow> bool" where
  "dandbuf ks cs kR cR buf dbuf \<longleftrightarrow>
     list_all (ftable ks) (fst buf) \<and>
     fst dbuf = map (dtabc ks cs) (fst buf) \<and>
     list_all2 (dtres kR cR) (snd buf) (snd dbuf)"

lemma dandbuf_add:
  assumes b: "dandbuf ks cs kR cR buf dbuf" and x: "list_all (ftable ks) xs"
    and y: "list_all2 (dtres kR cR) ys dys"
  shows "dandbuf ks cs kR cR (mbuf2_add xs ys buf) (mbuf2_add (map (dtabc ks cs) xs) dys dbuf)"
  using assms by (cases buf; cases dbuf) (auto simp: dandbuf_def list_all2_appendI)

lemma dandbuf_take:
  assumes fK: "dframe ks cs" and fR: "dframe kR cR" and sub: "set kR \<subseteq> set ks"
    and bf: "dandbuf ks cs kR cR buf dbuf"
    and t: "mbuf2_take (\<lambda>r1 (V, r2). bin_join ks r1 True V r2) buf = (zs, buf')"
  shows "\<exists>dbuf'. mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> dbin_join (mk_djoin cs cR) r1 True z) dbuf
      = (map (dtabc ks cs) zs, dbuf') \<and> dandbuf ks cs kR cR buf' dbuf'"
proof -
  obtain b1 b2 where bu: "buf = (b1, b2)" by (cases buf)
  obtain c1 c2 where bu': "buf' = (c1, c2)" by (cases buf')
  have l1: "list_all (ftable ks) b1" and d1: "fst dbuf = map (dtabc ks cs) b1"
    and q: "list_all2 (dtres kR cR) b2 (snd dbuf)"
    using bf bu by (auto simp: dandbuf_def)
  have eq: "\<And>a p q. a \<in> set b1 \<Longrightarrow> dtres kR cR p q \<Longrightarrow>
      (case q of None \<Rightarrow> dtabc ks cs a | Some z \<Rightarrow> dbin_join (mk_djoin cs cR) (dtabc ks cs a) True z)
        = dtabc ks cs ((\<lambda>r1 (V, r2). bin_join ks r1 True V r2) a p)"
  proof -
    fix a p q assume au: "a \<in> set b1" and dr: "dtres kR cR p q"
    have ta: "ftable ks a" using l1 au by (simp add: list_all_iff)
    show "(case q of None \<Rightarrow> dtabc ks cs a
          | Some z \<Rightarrow> dbin_join (mk_djoin cs cR) (dtabc ks cs a) True z)
        = dtabc ks cs ((\<lambda>r1 (V, r2). bin_join ks r1 True V r2) a p)"
      using dtres_join[OF fK fR sub ta dr] by (simp add: case_prod_beta)
  qed
  obtain dys' where r: "mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> dbin_join (mk_djoin cs cR) r1 True z) (map (dtabc ks cs) b1, snd dbuf)
      = (map (dtabc ks cs) zs, (map (dtabc ks cs) c1, dys'))"
    and q': "list_all2 (dtres kR cR) c2 dys'"
    using mbuf2_take_rel2[where h = "dtabc ks cs" and m = "dtabc ks cs"
        and Q = "dtres kR cR" and f = "\<lambda>r1 (V, r2). bin_join ks r1 True V r2"
        and g = "\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> dbin_join (mk_djoin cs cR) r1 True z"
        and xs = b1 and ys = b2 and dys = "snd dbuf" and zs = zs and xs' = c1 and ys' = c2,
        OF eq q t[unfolded bu bu']] by blast
  have sc: "set c1 \<subseteq> set b1" using mbuf2_take_sub t bu bu' by blast
  have du: "dbuf = (map (dtabc ks cs) b1, snd dbuf)" using d1 by (cases dbuf) simp
  show ?thesis using r q' sc l1 bu'
    by (intro exI[where x = "(map (dtabc ks cs) c1, dys')"])
      (subst du, auto simp: dandbuf_def list_all_iff)
qed

lemma tok_weak:
  "tok cR cL args \<Longrightarrow> dframe kR cR \<Longrightarrow> dframe kL cL \<Longrightarrow>
     mem (args_ivl args) 0 \<or> (args_pos args \<and> set kL = set kR)"
  by (auto simp: tok_def dframe_def)

text \<open>One firing of the fused node's trigger structure.  It differs from the standalone node's
  only in what each step appends: the kernel keeps the read's column list beside its table, and
  the dense side keeps the empty window as @{term None}.\<close>

lemma dandtrigger_step_rel:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and ok: "tok cR cL args"
    and rel: "dtrigger_rel kR cR kL cL args tw aux daux buf dbuf nts"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and st: "sorted tss" and bnd: "\<forall>v \<in> set tss. tw \<le> v"
    and we: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
        in (zs @ [(fv_z, z)], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ tss)
      = ((zs, aux1), buf1, nts1)"
    and de: "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
        let ax = gupdate_mmtaux (dargs cR cL args) t r1 r2 ax
        in (ws @ [if gmmtaux_empty ax then None
                  else Some (gresult_mmtaux (dargs cR cL args) ax)], ax)) ([], daux)
        (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) (nts @ tss)
      = ((dzs, daux1), dbuf1, dnts1)"
  shows "list_all2 (dtres kR cR) zs dzs \<and> dnts1 = nts1 \<and>
     dtrigger_rel kR cR kL cL args (dnext tw tss) aux1 daux1 buf1 dbuf1 nts1"
proof -
  obtain cur auxlist where vw: "valid_mmtaux args cur aux auxlist"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r"
    and vd: "dtaux kL cL kR cR args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable kL) (fst buf)"
    and lv: "list_all (ftable kR) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and dbf: "dbuf = (map (dtabc kL cL) (fst buf), map (dtabc kR cR) (snd buf))"
    using rel by (rule dtrigger_relE)
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  define g where "g = (\<lambda>r1 r2 t (zs :: (cols \<times> event_data table) list, ax).
    let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
    in (zs @ [(fv_z, z)], ax))"
  define gd where "gd = (\<lambda>r1 r2 t (ws :: event_data table option list, ax).
    let ax = gupdate_mmtaux (dargs cR cL args) t r1 r2 ax
    in (ws @ [if gmmtaux_empty ax then None
              else Some (gresult_mmtaux (dargs cR cL args) ax)], ax))"
  define R where "R = (\<lambda>v (pr :: (cols \<times> event_data table) list \<times> event_data mmtaux)
      (dpr :: event_data table option list \<times> event_data gmmtaux).
    (\<exists>al. valid_mmtaux args v (snd pr) al \<and>
       (\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r) \<and>
       dtaux kL cL kR cR args v (snd dpr) al) \<and>
     list_all2 (dtres kR cR) (fst pr) (fst dpr))"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mad: "mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf
      = (map (dtabc kL cL) us, map (dtabc kR cR) vs)"
    using dbf by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable kL) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable kR) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a c v w z z'. a \<in> set us \<Longrightarrow> c \<in> set vs \<Longrightarrow> R w z z' \<Longrightarrow> w \<le> v \<Longrightarrow>
      R v (g a c v z) (gd (dtabc kL cL a) (dtabc kR cR c) v z')"
  proof -
    fix a c v w and z :: "(cols \<times> event_data table) list \<times> event_data mmtaux"
      and z' :: "event_data table option list \<times> event_data gmmtaux"
    assume au: "a \<in> set us" and cv: "c \<in> set vs" and q: "R w z z'" and wv: "w \<le> v"
    have t1: "ftable kL a" using au lus by (simp add: list_all_iff)
    have t2: "ftable kR c" using cv lvs by (simp add: list_all_iff)
    obtain al where vwz: "valid_mmtaux args w (snd z) al"
      and wfz: "\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r"
      and vdz: "dtaux kL cL kR cR args w (snd z') al"
      using q unfolding R_def by blast
    have fz: "list_all2 (dtres kR cR) (fst z) (fst z')" using q unfolding R_def by blast
    define al' where "al' = filter (\<lambda>(t, _). memR (args_ivl args) (v - t)) al @ [(v, a, c)]"
    have vw': "valid_mmtaux args v (update_mmtaux args v a c (snd z)) al'"
      unfolding al'_def
      by (rule valid_update_mmtaux[OF wv _ _ vwz]) (use t1 t2 aL aR in simp_all)
    have wf': "\<forall>(t, l, r) \<in> set al'. ftable kL l \<and> ftable kR r"
      using wfz t1 t2 unfolding al'_def by auto
    have vd': "dtaux kL cL kR cR args v
        (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z')) al'"
      unfolding al'_def by (rule dtaux_update[OF vdz wv fR fL sub]) (use t1 t2 in simp_all)
    have res: "result_mmtaux args (update_mmtaux args v a c (snd z))
        = trigger_results args v al'" by (rule valid_result_mmtaux[OF vw'])
    have dr: "dtres kR cR (result_mmtaux args (update_mmtaux args v a c (snd z)))
        (if gmmtaux_empty (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a)
             (dtabc kR cR c) (snd z')) then None
         else Some (gresult_mmtaux (dargs cR cL args)
           (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c)
             (snd z'))))"
    proof (cases "gmmtaux_empty (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a)
        (dtabc kR cR c) (snd z'))")
      case True
      then show ?thesis
        unfolding res using dtaux_result_empty[OF vd' True]
        by (simp add: dtres_def)
    next
      case False
      have nz: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (v - t)) al')"
        using dtaux_window[OF vd'] False by (simp add: split_def)
      have lst: "fst (last al') = v" unfolding al'_def by simp
      have ft: "ftable (fst (trigger_results args v al')) (snd (trigger_results args v al'))"
        by (rule conjunct1[OF ftable_trigger_results_weak[OF wf' _ lst aL aR
              dframeD(1)[OF fR] tok_weak[OF ok fR fL]]])
          (simp add: al'_def)
      have fv: "fst (trigger_results args v al') = kR" using nz aR by simp
      have tr: "ftable kR (snd (trigger_results args v al'))" using ft unfolding fv .
      have dres: "gresult_mmtaux (dargs cR cL args)
            (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z'))
          = dtabc kR cR (snd (trigger_results args v al'))"
        by (rule dtaux_result[OF vd' False fR fL sub aL aR])
      show ?thesis unfolding res using False fv tr dres by (simp add: dtres_def)
    qed
    have gz: "g a c v z = (fst z @ [result_mmtaux args (update_mmtaux args v a c (snd z))],
           update_mmtaux args v a c (snd z))"
      by (cases z) (simp add: g_def Let_def case_prod_beta)
    have gdz: "gd (dtabc kL cL a) (dtabc kR cR c) v z'
        = (fst z' @ [if gmmtaux_empty (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a)
               (dtabc kR cR c) (snd z')) then None
             else Some (gresult_mmtaux (dargs cR cL args)
               (gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c)
                 (snd z')))],
           gupdate_mmtaux (dargs cR cL args) v (dtabc kL cL a) (dtabc kR cR c) (snd z'))"
      by (cases z') (simp add: gd_def Let_def case_prod_beta)
    show "R v (g a c v z) (gd (dtabc kL cL a) (dtabc kR cR c) v z')"
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
  have de': "mbuf2T_take gd ([], daux) (map (dtabc kL cL) us, map (dtabc kR cR) vs)
      (nts @ tss) = ((dzs, daux1), dbuf1, dnts1)"
    using de unfolding mad gd_def by simp
  have Rr: "(\<exists>u. R u (zs, aux1) (dzs, daux1) \<and> u \<le> dnext tw tss \<and> (\<forall>t \<in> set nts1. u \<le> t)) \<and>
      sorted nts1 \<and> set nts1 \<subseteq> set (nts @ tss) \<and> set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs \<and>
      dbuf1 = (map (dtabc kL cL) b1, map (dtabc kR cR) b2) \<and> dnts1 = nts1"
    by (rule mbuf2T_take_rel[where R = R and f = g and g = gd and h = "dtabc kL cL"
        and k = "dtabc kR cR", OF step r0 sts cts bound cdn we' de'])
  obtain u where ru: "R u (zs, aux1) (dzs, daux1)" and ub: "u \<le> dnext tw tss"
    and un: "\<forall>t \<in> set nts1. u \<le> t" using Rr by blast
  have sn1: "sorted nts1" and sb1: "set b1 \<subseteq> set us" and sb2: "set b2 \<subseteq> set vs"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf1: "dbuf1 = (map (dtabc kL cL) b1, map (dtabc kR cR) b2)"
    and dn1: "dnts1 = nts1" using Rr by blast+
  have lb1: "list_all (ftable kL) b1" using sb1 lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable kR) b2" using sb2 lvs by (auto simp: list_all_iff)
  obtain al1 where v1: "valid_mmtaux args u aux1 al1"
    and w1: "\<forall>(t, l, r) \<in> set al1. ftable kL l \<and> ftable kR r"
    and d1: "dtaux kL cL kR cR args u daux1 al1" using ru unfolding R_def by auto
  have dz: "list_all2 (dtres kR cR) zs dzs" using ru unfolding R_def by simp
  have bnd1: "\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> dnext tw tss" using un sub1 bound by auto
  have "dtrigger_rel kR cR kL cL args (dnext tw tss) aux1 daux1 (b1, b2)
      (map (dtabc kL cL) b1, map (dtabc kR cR) b2) nts1"
    by (rule dtrigger_relI[OF v1 w1 d1 ub lb1 lb2 sn1 bnd1])
  then show ?thesis using dz dn1 bfs dbf1 by simp
qed

subsection \<open>The relation itself\<close>

text \<open>
  A node's kernel tables are over the column list the kernel computes for it -- the free
  variables of its formula, in the order @{const Formula.fv_list} lists them -- and the dense ones
  over the same columns in ascending order.  The kernel's own column lists inside a node (the
  operands' columns of a join, the columns a let-bound formula is reordered from) are therefore the
  operands' kernel columns, and the rules below say so.
\<close>

inductive dsim :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> dformula \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  DsRel: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MRel rel) \<Longrightarrow>
    table ks rel \<Longrightarrow>
    dsim n ks cs tw (DRel (dtabc ks cs rel)) (mformula.MRel rel)"
| DsPredC: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MPred e tms Copy) \<Longrightarrow>
    tms = map Formula.Var [0..<length tms] \<Longrightarrow> ks = [0..<length tms] \<Longrightarrow> cs = ks \<Longrightarrow>
    dsim n ks cs tw (DPredS e (length tms)) (mformula.MPred e tms Copy)"
| DsPredS: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MPred e tms Simple) \<Longrightarrow>
    is_simple_pattern tms 0 \<Longrightarrow> cs = smp_cols tms \<Longrightarrow> ks = cs \<Longrightarrow>
    dsim n ks cs tw (DPredS e (length tms)) (mformula.MPred e tms Simple)"
| DsPredM: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MPred e tms Match) \<Longrightarrow> ks = pred_cols tms \<Longrightarrow>
    dsim n ks cs tw (DPredM e (length tms) tms cs) (mformula.MPred e tms Match)"
| DsAndRel: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MAndRel ks \<phi> (t1, p, c, t2)) \<Longrightarrow>
    dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
    Formula.fv_trm t1 \<subseteq> set cs \<Longrightarrow> Formula.fv_trm t2 \<subseteq> set cs \<Longrightarrow>
    dsim n ks cs tw (DAndRel \<phi>d (reindex_constraint cs (t1, p, c, t2)))
      (mformula.MAndRel ks \<phi> (t1, p, c, t2))"
| DsNeg: "produces n [] tw (mformula.MNeg \<phi>) \<Longrightarrow> dsim n [] [] tw \<phi>d \<phi> \<Longrightarrow>
    dsim n [] [] tw (DNeg \<phi>d) (mformula.MNeg \<phi>)"
| DsExists: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MExists kks \<phi>) \<Longrightarrow>
    dsim (Suc n) kks ccs tw \<phi>d \<phi> \<Longrightarrow> ks = ex_cols kks \<Longrightarrow> cs = dex_cols ccs \<Longrightarrow> b = ex_drop0 ccs \<Longrightarrow>
    dsim n ks cs tw (DExists \<phi>d b) (mformula.MExists kks \<phi>)"
| DsOr: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MOr ks \<phi> k2 \<psi> buf) \<Longrightarrow>
    dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow> dsim n k2 cs tw \<psi>d \<psi> \<Longrightarrow>
    dbuf2 ks cs k2 cs buf dbuf \<Longrightarrow>
    dsim n ks cs tw (DOr \<phi>d \<psi>d dbuf) (mformula.MOr ks \<phi> k2 \<psi> buf)"
| DsAnd: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MAnd k1 \<phi> pos k2 \<psi> buf) \<Longrightarrow>
    dsim n k1 c1 tw \<phi>d \<phi> \<Longrightarrow> dsim n k2 c2 tw \<psi>d \<psi> \<Longrightarrow>
    ks = cols_union k1 k2 \<Longrightarrow> cs = merge_cols c1 c2 \<Longrightarrow> pl = mk_djoin c1 c2 \<Longrightarrow>
    (\<not> pos \<Longrightarrow> set c2 \<subseteq> set c1) \<Longrightarrow>
    dbuf2 k1 c1 k2 c2 buf dbuf \<Longrightarrow>
    dsim n ks cs tw (DAnd pl \<phi>d pos \<psi>d dbuf) (mformula.MAnd k1 \<phi> pos k2 \<psi> buf)"
| DsPrev: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MPrev I \<phi> first buf nts) \<Longrightarrow>
    dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
    list_all (ftable ks) buf \<Longrightarrow> dbuf = map (dtabc ks cs) buf \<Longrightarrow>
    dsim n ks cs tw (DPrev I \<phi>d first dbuf nts) (mformula.MPrev I \<phi> first buf nts)"
| DsNext: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MNext I \<phi> first nts) \<Longrightarrow>
    dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
    dsim n ks cs tw (DNext I \<phi>d first nts) (mformula.MNext I \<phi> first nts)"
| DsAnds: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MAnds ks (k0 # kss) nkss L buf) \<Longrightarrow>
    (\<forall>i < length L. dsim n ((k0 # kss @ nkss) ! i) ((c0 # css @ nss) ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    length Ld = length L \<Longrightarrow> length (c0 # css @ nss) = length L \<Longrightarrow>
    length kss = length css \<Longrightarrow> length nkss = length nss \<Longrightarrow>
    (\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)) \<Longrightarrow>
    cs = dands_cols c0 css \<Longrightarrow>
    ps = dands_plans c0 css \<Longrightarrow> ns = dands_plans (dands_cols c0 css) nss \<Longrightarrow>
    dbufn (k0 # kss @ nkss) (c0 # css @ nss) buf dbuf \<Longrightarrow>
    dsim n ks cs tw (DAnds ps ns Ld dbuf) (mformula.MAnds ks (k0 # kss) nkss L buf)"
| DsAgg: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MAgg args \<phi>) \<Longrightarrow>
    dsim (length (aggargs_tys args) + n) k0 (agg_cols (length (aggargs_tys args)) gcols) tw \<phi>d \<phi> \<Longrightarrow>
    aggargs_cols args = k0 \<Longrightarrow> aggargs_y args = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow>
    (aggargs_g0 args \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f args) \<subseteq> set k0 \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys args)) k0 \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    dsim n ks cs tw (DAgg (aggargs_g0 args) (aggargs_\<omega> args)
        (reindex_trm (agg_cols (length (aggargs_tys args)) gcols) (aggargs_f args))
        (length (aggargs_tys args)) (ins_pos gcols y) \<phi>d) (mformula.MAgg args \<phi>)"
| DsSince: "dframe kR cR \<Longrightarrow>
    produces n kR tw (mformula.MSince args \<phi> \<psi> buf aux) \<Longrightarrow>
    dsim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow>
    dsince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow>
    dsx_agg daux = None \<Longrightarrow>
    dsim n kR cR tw (DSince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
| DsUntil: "dframe kR cR \<Longrightarrow>
    produces n kR tw (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<Longrightarrow>
    dsim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow> msk = dmsk cR cL \<Longrightarrow>
    duntil_rel kR cR kL cL args tw t aux daux buf dbuf nts \<Longrightarrow>
    dux_agg daux = None \<Longrightarrow>
    dsim n kR cR tw (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| DsSinceAgg: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MSince args \<phi> \<psi> buf aux) \<Longrightarrow>
    dsim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow>
    dsince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    dsx_agg daux = None \<Longrightarrow>
    dsim n ks cs tw (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
        (length (aggargs_tys ag)) (ins_pos gcols y) (DSince dags \<phi>d \<psi>d dbuf daux))
      (mformula.MSince args \<phi> \<psi> buf aux)"
| DsSinceFused: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MSince args \<phi> \<psi> buf aux) \<Longrightarrow>
    dsim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow>
    dsince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    dsx_agg daux = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y) \<Longrightarrow>
    dsim n ks cs tw (DSince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
| DsUntilAgg: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<Longrightarrow>
    dsim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow> msk = dmsk cR cL \<Longrightarrow>
    duntil_rel kR cR kL cL args tw t aux daux buf dbuf nts \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    dux_agg daux = None \<Longrightarrow>
    dsim n ks cs tw (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
        (length (aggargs_tys ag)) (ins_pos gcols y) (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux))
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| DsUntilFused: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<Longrightarrow>
    dsim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow> msk = dmsk cR cL \<Longrightarrow>
    duntil_rel kR cR kL cL args tw t aux daux buf dbuf nts \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    dux_agg daux = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y) \<Longrightarrow>
    dsim n ks cs tw (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| DsAndAssign: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MAndAssign k0 \<phi> (y, t)) \<Longrightarrow>
    dsim n k0 c0 tw \<phi>d \<phi> \<Longrightarrow>
    y \<notin> set k0 \<Longrightarrow> Formula.fv_trm t \<subseteq> set c0 \<Longrightarrow>
    ks = k0 @ [y] \<Longrightarrow> cs = merge_cols c0 [y] \<Longrightarrow>
    dsim n ks cs tw (DAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<phi>d)
      (mformula.MAndAssign k0 \<phi> (y, t))"
| DsTP: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MTP mt i) \<Longrightarrow>
    cs = mtrm_dcols mt \<Longrightarrow> ks = cs \<Longrightarrow>
    dsim n ks cs tw (DTP mt i) (mformula.MTP mt i)"
| DsTS: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MTS mt) \<Longrightarrow>
    cs = mtrm_dcols mt \<Longrightarrow> ks = cs \<Longrightarrow>
    dsim n ks cs tw (DTS mt) (mformula.MTS mt)"
| DsLet: "dframe ks cs \<Longrightarrow> produces n ks tw (mformula.MLet p m kks \<phi> \<psi>) \<Longrightarrow>
    dsim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow> dsim n ks cs tw \<psi>d \<psi> \<Longrightarrow>
    dsim n ks cs tw (DLet p m \<phi>d \<psi>d) (mformula.MLet p m kks \<phi> \<psi>)"
| DsFrz: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) \<Longrightarrow>
    dsim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow> dsim n ks cs tw \<psi>d \<psi> \<Longrightarrow>
    list_all (ftable [0..<m]) \<alpha>s \<Longrightarrow> dsim n ks cs tw \<rho>d \<rho> \<Longrightarrow>
    size \<rho>L = size \<rho> \<Longrightarrow> size \<rho>Ld = size \<rho>d \<Longrightarrow> (lv \<noteq> None \<longrightarrow> dsim n ks cs tw \<rho>Ld \<rho>L) \<Longrightarrow>
    dsim n ks cs tw (DFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s \<rho>d w pR tq (map (dtabc ks cs) rb) d po ng lv \<rho>Ld)
      (mformula.MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)"
| DsLetPast: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MLetPast p m kks \<phi> \<psi> i buf) \<Longrightarrow>
    dsim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow> dsim n ks cs tw \<psi>d \<psi> \<Longrightarrow>
    \<forall>y. buf = Some y \<longrightarrow> ftable [0..<m] y \<Longrightarrow>
    dsim n ks cs tw (DLetPast p m \<phi>d \<psi>d i buf) (mformula.MLetPast p m kks \<phi> \<psi> i buf)"
| DsTrigger: "dframe kR cR \<Longrightarrow>
    produces n kR tw (mformula.MTrigger args \<phi> \<psi> buf nts aux) \<Longrightarrow>
    dsim n kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim n kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    mem (args_ivl args) 0 \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow> pl = emb_plan cR cL \<Longrightarrow>
    dtrigger_rel kR cR kL cL args tw aux daux buf dbuf nts \<Longrightarrow>
    dsim n kR cR tw (DTrigger dags pl \<phi>d \<psi>d dbuf nts daux)
      (mformula.MTrigger args \<phi> \<psi> buf nts aux)"
| DsAndTrigger: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MAndTrigger ks \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) \<Longrightarrow>
    dsim n ks cs tw \<alpha>d \<alpha> \<Longrightarrow> dsim n kL cL tw \<phi>d \<phi> \<Longrightarrow> dsim n kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow> set kR \<subseteq> set ks \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    tok cR cL args \<Longrightarrow>
    dags = dargs cR cL args \<Longrightarrow> pl = mk_djoin cs cR \<Longrightarrow>
    dandbuf ks cs kR cR buf1 dbf1 \<Longrightarrow>
    dtrigger_rel kR cR kL cL args tw aux daux buf2 dbf2 nts \<Longrightarrow>
    dsim n ks cs tw (DAndTrigger pl \<alpha>d dbf1 dags \<phi>d \<psi>d dbf2 nts daux)
      (mformula.MAndTrigger ks \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)"
| DsMatchP: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MMatchP I ks dss mr mrs L buf nts aux) \<Longrightarrow>
    Regex.safe_regex fv rgx_safe_pred Past Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = RPDs mr \<Longrightarrow> dss = map Formula.fv_list \<psi>s \<Longrightarrow>
    length css = length \<psi>s \<Longrightarrow> length L = length \<psi>s \<Longrightarrow> length Ld = length L \<Longrightarrow>
    (\<forall>i < length \<psi>s. dframe (dss ! i) (css ! i)) \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks) \<Longrightarrow>
    (\<forall>i < length L. dsim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    pls = map (emb_plan cs) css \<Longrightarrow>
    dbufn dss css buf dbuf \<Longrightarrow>
    dmrd_rel ks cs aux daux \<Longrightarrow>
    dsim n ks cs tw (DMatchP (length cs) I mr mrs pls Ld dbuf nts daux)
      (mformula.MMatchP I ks dss mr mrs L buf nts aux)"
| DsMatchF: "dframe ks cs \<Longrightarrow>
    produces n ks tw (mformula.MMatchF I ks dss mr mrs L buf nts t aux) \<Longrightarrow>
    Regex.safe_regex fv rgx_safe_pred Futu Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = LPDs mr \<Longrightarrow> dss = map Formula.fv_list \<psi>s \<Longrightarrow>
    length css = length \<psi>s \<Longrightarrow> length L = length \<psi>s \<Longrightarrow> length Ld = length L \<Longrightarrow>
    (\<forall>i < length \<psi>s. dframe (dss ! i) (css ! i)) \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks) \<Longrightarrow>
    (\<forall>i < length L. dsim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    pls = map (emb_plan cs) css \<Longrightarrow>
    dbufn dss css buf dbuf \<Longrightarrow>
    dmld_rel ks cs \<psi>s css aux daux \<Longrightarrow>
    dsim n ks cs tw (DMatchF (length cs) I mr mrs pls Ld dbuf nts t daux)
      (mformula.MMatchF I ks dss mr mrs L buf nts t aux)"

(*<*)
end
(*>*)