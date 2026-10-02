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

text \<open>The two facts the relation is designed to hand out at every node.\<close>

lemma dsim_dframe: "dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow> dframe ks cs"
  by (erule dsim.cases) (auto simp: dframe_def)

lemma dsim_produces: "dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow> produces n ks tw \<phi>"
  by (induct rule: dsim.induct) assumption+

text \<open>The unfused Since and Until nodes are related by one rule each, so the relation can be read
  backwards there: the operands are related at the node's own columns.  The compiler uses this to
  reuse an unfused node's simulation for the fused one, whose operands are the very same.\<close>

lemma dsim_DSinceD:
  assumes "dsim n ks cs tw (DSince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
    and "dsx_agg daux = None"
  obtains kL cL where "dsim (args_n args) kL cL tw \<phi>d \<phi>" and "dsim (args_n args) ks cs tw \<psi>d \<psi>"
    and "args_L args = kL"
  using assms(1)
proof (cases rule: dsim.cases)
  case DsSince
  then show ?thesis by (intro that) assumption+
next
  case DsSinceFused
  then show ?thesis using assms(2) by (simp only: option.distinct)
qed

lemma dsim_DUntilD:
  assumes "dsim n ks cs tw (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts' t' aux)"
    and "dux_agg daux = None"
  obtains kL cL where "dsim (args_n args) kL cL tw \<phi>d \<phi>" and "dsim (args_n args) ks cs tw \<psi>d \<psi>"
    and "args_L args = kL"
  using assms(1)
proof (cases rule: dsim.cases)
  case DsUntil
  then show ?thesis by (intro that) assumption+
next
  case DsUntilFused
  then show ?thesis using assms(2) by (simp only: option.distinct)
qed

section \<open>The simulation\<close>

lemma dbuf2_add:
  assumes b: "dbuf2 k1 c1 k2 c2 buf dbuf"
    and x: "list_all (ftable k1) xs" and y: "list_all (ftable k2) ys"
  shows "dbuf2 k1 c1 k2 c2 (mbuf2_add xs ys buf)
      (mbuf2_add (map (dtabc k1 c1) xs) (map (dtabc k2 c2) ys) dbuf)"
  using assms by (cases buf) (auto simp: dbuf2_def)

lemma dbuf2_take:
  assumes b: "dbuf2 k1 c1 k2 c2 buf dbuf"
    and eq: "\<And>a b. ftable k1 a \<Longrightarrow> ftable k2 b \<Longrightarrow> g (dtabc k1 c1 a) (dtabc k2 c2 b) = dtabc ks cs (f a b)"
    and t1: "mbuf2_take f buf = (zs, buf')"
  shows "\<exists>dbuf'. mbuf2_take g dbuf = (map (dtabc ks cs) zs, dbuf') \<and> dbuf2 k1 c1 k2 c2 buf' dbuf'"
proof -
  obtain b1 b2 where buf: "buf = (b1, b2)" by (cases buf)
  obtain d1 d2 where buf': "buf' = (d1, d2)" by (cases buf')
  have l1: "list_all (ftable k1) b1" and l2: "list_all (ftable k2) b2"
    and d: "dbuf = (map (dtabc k1 c1) b1, map (dtabc k2 c2) b2)"
    using b buf by (auto simp: dbuf2_def)
  have "mbuf2_take g (map (dtabc k1 c1) b1, map (dtabc k2 c2) b2)
      = (map (dtabc ks cs) zs, (map (dtabc k1 c1) d1, map (dtabc k2 c2) d2))"
    using t1 buf buf' l1 l2 by (intro mbuf2_take_map) (auto simp: list_all_iff intro!: eq)
  moreover have "set d1 \<subseteq> set b1" "set d2 \<subseteq> set b2"
    using mbuf2_take_sub[of f b1 b2 zs d1 d2] t1 buf buf' by auto
  ultimately show ?thesis using d l1 l2 buf' by (auto simp: dbuf2_def list_all_iff)
qed

subsection \<open>The multi-way buffer of reordered tables\<close>

lemma map2_apply_dtabcs:
  "length kss = length as \<Longrightarrow> length css = length as \<Longrightarrow>
     map2 (\<lambda>h a. h a) (map2 dtabc kss css) as = dtabcs kss css as"
  by (rule nth_equalityI) simp_all

lemma dbufn_add:
  assumes b: "dbufn kss css buf dbuf" and l: "length xss = length css"
    and t: "\<forall>i < length css. list_all (ftable (kss ! i)) (xss ! i)"
  shows "dbufn kss css (mbufn_add xss buf)
      (mbufn_add (map2 map (map2 dtabc kss css) xss) dbuf)"
proof -
  have lb: "length buf = length css" and lk: "length kss = length css"
    and lt: "\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)"
    and d: "dbuf = map2 map (map2 dtabc kss css) buf"
    using b by (auto simp: dbufn_def)
  have "\<forall>i < length css. list_all (ftable (kss ! i)) (mbufn_add xss buf ! i)"
    using lt t lb l by (auto simp: list_all_iff)
  moreover have "mbufn_add (map2 map (map2 dtabc kss css) xss) dbuf
      = map2 map (map2 dtabc kss css) (mbufn_add xss buf)"
    unfolding d by (rule mbufn_add_map2[symmetric]) (use lb l lk in simp_all)
  ultimately show ?thesis using lb l lk by (simp add: dbufn_def)
qed

lemma dbufn_take:
  fixes f g :: "event_data table list \<Rightarrow> event_data table"
    and buf buf' dbuf :: "event_data mbufn" and zs :: "event_data table list"
  assumes b: "dbufn kss css buf dbuf"
    and eq: "\<And>as :: event_data table list. length as = length css \<Longrightarrow>
        (\<forall>i < length css. ftable (kss ! i) (as ! i)) \<Longrightarrow>
        dtabc ks cs (f as) = g (dtabcs kss css as)"
    and t: "mbufn_take (\<lambda>as zs. zs @ [f as]) [] buf = (zs, buf')"
  shows "\<exists>dbuf'. mbufn_take (\<lambda>as zs. zs @ [g as]) [] dbuf = (map (dtabc ks cs) zs, dbuf')
      \<and> dbufn kss css buf' dbuf'"
proof -
  have lb: "length buf = length css" and lk: "length kss = length css"
    and lt: "\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)"
    and d: "dbuf = map2 map (map2 dtabc kss css) buf"
    using b by (auto simp: dbufn_def)
  define hs :: "(event_data table \<Rightarrow> event_data table) list"
    where "hs = map2 dtabc kss css"
  define Ss :: "event_data table set list"
    where "Ss = map (\<lambda>k. {T. ftable k T}) kss"
  obtain w2 buf2 where e2: "mbufn_take (\<lambda>as zs. zs @ [g as])
      ([] :: event_data table list) dbuf = (w2, buf2)"
    by (cases "mbufn_take (\<lambda>as zs. zs @ [g as]) ([] :: event_data table list) dbuf") auto
  have sub: "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i"
    using lt lb lk by (auto simp: Ss_def list_all_iff)
  have step: "\<And>as :: event_data table list. \<And>u u' :: event_data table list.
      length as = length hs \<Longrightarrow>
      (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> u' = map (dtabc ks cs) u \<Longrightarrow>
      u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (dtabc ks cs) (u @ [f as])"
  proof -
    fix as u u' :: "event_data table list"
    assume la: "length as = length hs"
      and ma: "\<forall>i < length as. as ! i \<in> Ss ! i" and mu: "u' = map (dtabc ks cs) u"
    have la': "length as = length css" using la lk by (simp add: hs_def)
    have ma': "\<forall>i < length css. ftable (kss ! i) (as ! i)"
      using ma la' lk by (auto simp: Ss_def)
    show "u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (dtabc ks cs) (u @ [f as])"
      using mu eq[OF la' ma'] la' lk by (simp add: hs_def map2_apply_dtabcs)
  qed
  have r: "(w2 = map (dtabc ks cs) zs) \<and> buf2 = map2 map hs buf'"
  proof (rule mbufn_take_rel[where R = "\<lambda>u u'. u' = map (dtabc ks cs) u" and Ss = Ss
        and hs = hs and f = "\<lambda>as zs. zs @ [f as]" and g = "\<lambda>as zs. zs @ [g as]"
        and z = "[]" and z' = "[]" and buf = buf and buf' = buf' and w = zs])
    show "length hs = length buf" using lb lk by (simp add: hs_def)
    show "length Ss = length buf" using lb lk by (simp add: Ss_def)
    show "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i" by (rule sub)
    show "\<And>as u u'. length as = length hs \<Longrightarrow>
        (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> u' = map (dtabc ks cs) u \<Longrightarrow>
        u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (dtabc ks cs) (u @ [f as])"
      by (rule step)
    show "([] :: event_data table list) = map (dtabc ks cs) []" by simp
    show "mbufn_take (\<lambda>as zs. zs @ [f as]) [] buf = (zs, buf')" by (rule t)
    show "mbufn_take (\<lambda>as zs. zs @ [g as]) [] (map2 map hs buf) = (w2, buf2)"
      using e2 d by (simp add: hs_def)
  qed
  have ls: "length buf' = length buf"
    and ss: "\<forall>i < length buf. set (buf' ! i) \<subseteq> set (buf ! i)"
    using mbufn_take_sub[OF t] by auto
  have "dbufn kss css buf' buf2"
    using lt lb lk ls ss r by (fastforce simp: dbufn_def hs_def list_all_iff)
  then show ?thesis using e2 r by auto
qed

text \<open>The timestamped take, which the two match nodes use, keeps the buffers related in the same
  way; the accumulator is a parameter here because the past node threads a pair of the reported
  tables and the structure, and the future node the structure alone.\<close>

lemma dbufn_nt_take:
  assumes b: "dbufn kss css buf dbuf"
    and st: "\<And>as u u' t. length as = length css \<Longrightarrow>
        (\<forall>i < length css. ftable (kss ! i) (as ! i)) \<Longrightarrow> R u u' \<Longrightarrow>
        R (f as t u) (g (dtabcs kss css as) t u')"
    and rz: "R z z'"
    and e: "mbufnt_take f z buf t0 tss = (w, buf', t', tss')"
  shows "\<exists>w2 dbuf'. mbufnt_take g z' dbuf t0 tss = (w2, dbuf', t', tss')
      \<and> R w w2 \<and> dbufn kss css buf' dbuf'"
proof -
  have lb: "length buf = length css" and lk: "length kss = length css"
    and lt: "\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)"
    and d: "dbuf = map2 map (map2 dtabc kss css) buf"
    using b by (auto simp: dbufn_def)
  define hs :: "(event_data table \<Rightarrow> event_data table) list"
    where "hs = map2 dtabc kss css"
  define Ss :: "event_data table set list"
    where "Ss = map (\<lambda>k. {T. ftable k T}) kss"
  obtain w2 buf2 t2 tss2 where e2: "mbufnt_take g z' dbuf t0 tss = (w2, buf2, t2, tss2)"
    by (cases "mbufnt_take g z' dbuf t0 tss") auto
  have sub: "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i"
    using lt lb lk by (auto simp: Ss_def list_all_iff)
  have step: "\<And>as u u' t. length as = length hs \<Longrightarrow>
      (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> R u u' \<Longrightarrow>
      R (f as t u) (g (map2 (\<lambda>h a. h a) hs as) t u')"
  proof -
    fix as :: "event_data table list" and u u' t
    assume la: "length as = length hs" and ma: "\<forall>i < length as. as ! i \<in> Ss ! i"
      and ru: "R u u'"
    have la': "length as = length css" using la lk by (simp add: hs_def)
    have ma': "\<forall>i < length css. ftable (kss ! i) (as ! i)"
      using ma la' lk by (auto simp: Ss_def)
    show "R (f as t u) (g (map2 (\<lambda>h a. h a) hs as) t u')"
      using st[OF la' ma' ru] la' lk by (simp add: hs_def map2_apply_dtabcs)
  qed
  have r: "R w w2 \<and> buf2 = map2 map hs buf' \<and> t2 = t' \<and> tss2 = tss'"
  proof (rule mbufnt_take_rel[where R = R and Ss = Ss and hs = hs and f = f and g = g
        and z = z and z' = z' and buf = buf and buf' = buf' and w = w])
    show "length hs = length buf" using lb lk by (simp add: hs_def)
    show "length Ss = length buf" using lb lk by (simp add: Ss_def)
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
  have "dbufn kss css buf' buf2"
    using lt lb lk ls ss r by (fastforce simp: dbufn_def hs_def list_all_iff)
  then show ?thesis using e2 r by auto
qed

subsection \<open>Stepping a list of operands\<close>

lemma dsims_tables:
  "(\<forall>i < length L. dsim n (kss ! i) (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
   wf_db db \<Longrightarrow> sorted ts \<Longrightarrow> (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> i < length L \<Longrightarrow>
     list_all (ftable (kss ! i)) (fst (meval j n ts db (L ! i)))"
proof -
  assume la: "\<forall>i < length L. dsim n (kss ! i) (css ! i) tw (Ld ! i) (L ! i)"
    and w: "wf_db db" and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. tw \<le> t" and i: "i < length L"
  obtain as \<psi>2 where e: "meval j n ts db (L ! i) = (as, \<psi>2)" by (cases "meval j n ts db (L ! i)")
  have "list_all (ftable (kss ! i)) as"
    by (rule produces_tables[OF dsim_produces[OF la[rule_format, OF i]] w sts mts e])
  then show ?thesis using e by simp
qed

lemma deval_list_rel:
  assumes l1: "length Ld = length L" and l2: "length css = length L" and l3: "length kss = length L"
    and la: "\<forall>i < length L. dsim n (kss ! i) (css ! i) tw (Ld ! i) (L ! i) \<and>
       (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
          (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc (kss ! i) (css ! i)) as, \<psi>d')
             \<and> dsim n (kss ! i) (css ! i) tw' \<psi>d' \<psi>'))"
  shows "length (map (deval j ts db) Ld) = length L \<and>
   map fst (map (deval j ts db) Ld)
       = map2 map (map2 dtabc kss css) (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
   (\<forall>i < length L. dsim n (kss ! i) (css ! i) tw' (map snd (map (deval j ts db) Ld) ! i)
       (snd (meval j n ts db (L ! i))))"
proof -
  have e: "fst (deval j ts db (Ld ! i)) = map (dtabc (kss ! i) (css ! i)) (fst (meval j n ts db (L ! i)))
      \<and> dsim n (kss ! i) (css ! i) tw' (snd (deval j ts db (Ld ! i))) (snd (meval j n ts db (L ! i)))"
    if i: "i < length L" for i
  proof -
    obtain as \<psi>' where m: "meval j n ts db (L ! i) = (as, \<psi>')" by (cases "meval j n ts db (L ! i)")
    obtain \<psi>d' where "deval j ts db (Ld ! i) = (map (dtabc (kss ! i) (css ! i)) as, \<psi>d')"
      and "dsim n (kss ! i) (css ! i) tw' \<psi>d' \<psi>'" using la[rule_format, OF i] m by blast
    then show ?thesis using m by simp
  qed
  show ?thesis using e l1 l2 l3 by (auto intro!: nth_equalityI)
qed

subsection \<open>One firing of the Since structure\<close>

text \<open>
  One firing of @{const meval_since} on the dense side reports the same windows as one firing on
  the kernel's, and the relation is preserved.  The recursion is driven by the buffer alone, so
  the two sides step in lockstep; the induction is over the kernel's own recursion.
\<close>

lemma eval_since_rel:
  fixes kR cR kL cL :: cols and args :: args
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
  shows "meval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow>
    dsx_eval_since (dargs cR cL args) drs dbuf daux = (dzs, dbuf', daux') \<Longrightarrow>
    dsince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow>
    dsx_post daux = h \<Longrightarrow>
    dsresh kR cR args h rs drs \<Longrightarrow>
    dsresh kR cR args h zs dzs \<and> dsince_rel kR cR kL cL args tw aux' daux' buf' dbuf' \<and>
    dsx_post daux' = h"
proof (induction rs buf aux arbitrary: drs daux dbuf zs buf' aux' dzs dbuf' daux'
    taking: args rule: default_maux.eval_since.induct)
  case (1 rs x xs t tss skew aux)
  note E = 1(1) and D = 1(2) and R = 1(3) and P = 1(4) and S = 1(5)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' kR cR cL args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable kL) (x # xs)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc kL cL) (x # xs), map (dtabc kR cR) [], t # tss, skew)"
    using R by (rule dsince_relE)
  have tx: "table kL x" using lx by simp
  have ctu: "cur \<le> t" using ct by simp
  show ?case
  proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev rs, (x # xs, [], t # tss, skew), aux)" using True by simp
    have DW: "dsx_eval_since (dargs cR cL args) drs dbuf daux = (rev drs, dbuf, daux)"
      unfolding dbuf using True by simp
    have EE: "(rev rs, (x # xs, [], t # tss, skew), aux) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev drs, dbuf, daux) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    show ?thesis using EE DD R dsresh_rev[OF S] P by auto
  next
    case False
    let ?wa = "gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)"
    let ?da = "dsx_join (dargs cR cL args) (dtabc kL cL x)
        (dsx_add_new_ts (dargs cR cL args) t daux)"
    let ?al = "map (\<lambda>(u, rel). (u, join kR rel (args_pos args) kL x))
        (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
    have vw': "valid_mmasaux args t ?wa ?al"
      using default_mmasaux.valid_join_msaux
          [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu], of x] tx aL aR by simp
    have vd': "dsxaux' kR cR cL args t ?da ?al"
      by (rule dsxaux'_join[OF dsxaux'_add_new_ts[OF vd ctu] fR fL sub tx])
    have res0: "dsresh kR cR args h [result_mmasaux args ?wa]
        [dsx_result (dargs cR cL args) ?da]"
      using dsresh_result[OF vd' vw'] by (simp add: P)
    have res: "dsresh kR cR args h (result_mmasaux args ?wa # rs)
        (dsx_result (dargs cR cL args) ?da # drs)"
      using dsresh_append[OF res0 S] by simp
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa)"
      using False by (simp add: Let_def)
    have DW: "dsx_eval_since (dargs cR cL args) drs dbuf daux
        = (rev (dsx_result (dargs cR cL args) ?da # drs),
           (map (dtabc kL cL) xs, map (dtabc kR cR) [], tss, True), ?da)"
      unfolding dbuf using False by (simp add: Let_def)
    have EE: "(rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev (dsx_result (dargs cR cL args) ?da # drs),
        (map (dtabc kL cL) xs, map (dtabc kR cR) [], tss, True), ?da) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    have R': "dsince_rel kR cR kL cL args tw ?wa ?da (xs, [], tss, True)
        (map (dtabc kL cL) xs, map (dtabc kR cR) [], tss, True)"
      by (rule dsince_relI[OF vw' vd']) (use lx st ct in auto)
    show ?thesis using EE DD dsresh_rev[OF res] R' P by auto
  qed
next
  case (2 rs xs y ys tss aux)
  note IH = 2(1) and E = 2(2) and D = 2(3) and R = 2(4) and P = 2(5) and S = 2(6)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' kR cR cL args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable kL) xs"
    and ly: "list_all (ftable kR) (y # ys)"
    and st: "sorted tss" and ct: "\<forall>u \<in> set tss. cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc kL cL) xs, map (dtabc kR cR) (y # ys), tss, True)"
    using R by (rule dsince_relE)
  have ty: "table kR y" and fy: "finite y" using ly by simp_all
  let ?al = "case auxlist of [] \<Rightarrow> [(cur, y)]
      | ((u, w) # r) \<Rightarrow> if u = cur then (u, w \<union> y) # r else (cur, y) # auxlist"
  have vw': "valid_mmasaux args cur (add_new_table_mmasaux args y aux) ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vw]) (use ty aR in simp)
  have vd': "dsxaux' kR cR cL args cur
      (dsx_add_new_table (dargs cR cL args) (dtabc kR cR y) daux) ?al"
    by (rule dsxaux'_add_new_table[OF vd ty fy])
  have E': "meval_since args rs (xs, ys, tss, False) (add_new_table_mmasaux args y aux)
      = (zs, buf', aux')" using E by simp
  have D': "dsx_eval_since (dargs cR cL args) drs
      (map (dtabc kL cL) xs, map (dtabc kR cR) ys, tss, False)
      (dsx_add_new_table (dargs cR cL args) (dtabc kR cR y) daux)
      = (dzs, dbuf', daux')" using D unfolding dbuf by simp
  have R': "dsince_rel kR cR kL cL args tw (add_new_table_mmasaux args y aux)
      (dsx_add_new_table (dargs cR cL args) (dtabc kR cR y) daux)
      (xs, ys, tss, False) (map (dtabc kL cL) xs, map (dtabc kR cR) ys, tss, False)"
    by (rule dsince_relI[OF vw' vd' ctw]) (use lx ly st ct in auto)
  have P': "dsx_post (dsx_add_new_table (dargs cR cL args) (dtabc kR cR y) daux) = h"
    using P by simp
  show ?case by (rule IH[OF E' D' R' P' S])
next
  case (3 rs x xs y ys t tss aux)
  note IH = 3(1) and E = 3(2) and D = 3(3) and R = 3(4) and P = 3(5) and S = 3(6)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "dsxaux' kR cR cL args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable kL) (x # xs)"
    and ly: "list_all (ftable kR) (y # ys)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (dtabc kL cL) (x # xs), map (dtabc kR cR) (y # ys), t # tss, False)"
    using R by (rule dsince_relE)
  have tx: "table kL x" using lx by simp
  have ty: "table kR y" and fy: "finite y" using ly by simp_all
  have ctu: "cur \<le> t" using ct by simp
  let ?jl = "map (\<lambda>(u, rel). (u, join kR rel (args_pos args) kL x))
      (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
  let ?al = "case ?jl of [] \<Rightarrow> [(t, y)]
      | ((u, w) # r) \<Rightarrow> if u = t then (u, w \<union> y) # r else (t, y) # ?jl"
  let ?wa = "add_new_table_mmasaux args y
      (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux))"
  let ?da = "dsx_add_new_table (dargs cR cL args) (dtabc kR cR y)
      (dsx_join (dargs cR cL args) (dtabc kL cL x)
        (dsx_add_new_ts (dargs cR cL args) t daux))"
  have vwj: "valid_mmasaux args t (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)) ?jl"
    using default_mmasaux.valid_join_msaux
        [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu], of x] tx aL aR by simp
  have vdj: "dsxaux' kR cR cL args t
      (dsx_join (dargs cR cL args) (dtabc kL cL x)
        (dsx_add_new_ts (dargs cR cL args) t daux)) ?jl"
    by (rule dsxaux'_join[OF dsxaux'_add_new_ts[OF vd ctu] fR fL sub tx])
  have vw': "valid_mmasaux args t ?wa ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vwj]) (use ty aR in simp)
  have vd': "dsxaux' kR cR cL args t ?da ?al"
    by (rule dsxaux'_add_new_table[OF vdj ty fy])
  have res0: "dsresh kR cR args h [result_mmasaux args ?wa]
      [dsx_result (dargs cR cL args) ?da]"
    using dsresh_result[OF vd' vw'] by (simp add: P)
  have res: "dsresh kR cR args h (result_mmasaux args ?wa # rs)
      (dsx_result (dargs cR cL args) ?da # drs)"
    using dsresh_append[OF res0 S] by simp
  have P': "dsx_post ?da = h" using P by simp
  have E': "meval_since args (result_mmasaux args ?wa # rs) (xs, ys, tss, False) ?wa
      = (zs, buf', aux')" using E by (simp add: Let_def)
  have D': "dsx_eval_since (dargs cR cL args)
      (dsx_result (dargs cR cL args) ?da # drs)
      (map (dtabc kL cL) xs, map (dtabc kR cR) ys, tss, False) ?da = (dzs, dbuf', daux')"
    using D unfolding dbuf by (simp add: Let_def)
  have R': "dsince_rel kR cR kL cL args tw ?wa ?da (xs, ys, tss, False)
      (map (dtabc kL cL) xs, map (dtabc kR cR) ys, tss, False)"
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
  A let-bound formula's tables are reordered by the kernel from the formula's columns to the
  positional ones before they enter the database.  The dense formula's are already over the
  positional columns, which are the ascending order of the same set, so the dense table
  \<^emph>\<open>is\<close> the reordered one and the two databases are literally the same.\<close>

lemma dtabc_reorder_eq: "distinct ks \<Longrightarrow> table ks T \<Longrightarrow> dtabc ks cs T = reorder cs ks T"
  unfolding reorder_def using dtabc_same[of ks T] by (auto simp: dtabc_def)

lemma list_all_ftable_reorder:
  "dframe ks [0..<m] \<Longrightarrow> list_all (ftable ks) xs \<Longrightarrow>
     list_all (ftable [0..<m]) (map (reorder [0..<m] ks) xs)"
  by (auto simp: list_all_iff reorder_def table_def)

text \<open>
  The recursive let runs its bound formula against databases it builds itself, feeding the
  previous round's output back under the bound predicate.  The two runs produce literally the
  same lists, so their states stay in step round by round.  The guard that rejects a round in
  which the formula's size changed never fires on either side, because neither evaluator changes
  its formula's size.
\<close>

lemma letpast_meval0_rel:
  assumes Q: "\<And>tw' \<chi>d \<chi> ts' db' zs' \<chi>'. size \<chi> < NN \<Longrightarrow> dsim m kks [0..<m] tw' \<chi>d \<chi> \<Longrightarrow>
      wf_db db' \<Longrightarrow> sorted ts' \<Longrightarrow> (\<forall>t \<in> set ts'. tw' \<le> t) \<Longrightarrow>
      meval j m ts' db' \<chi> = (zs', \<chi>') \<Longrightarrow>
      \<exists>\<chi>d'. deval j ts' db' \<chi>d = (map (dtabc kks [0..<m]) zs', \<chi>d') \<and>
        dsim m kks [0..<m] (dnext tw' ts') \<chi>d' \<chi>'"
  shows "letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>))
      J i ys xs q ts db \<phi> = (zs, i', bo, \<phi>') \<Longrightarrow>
    snd q = m \<Longrightarrow> size \<phi> < NN \<Longrightarrow> dsim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
    (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> list_all (ftable [0..<m]) ys \<Longrightarrow>
    list_all (ftable [0..<m]) xs \<Longrightarrow>
    list_all (ftable [0..<m]) zs \<and> (\<forall>y. bo = Some y \<longrightarrow> ftable [0..<m] y) \<and>
      (\<exists>\<phi>d'. letpast_meval0 (deval j) J i ys xs q ts db \<phi>d = (zs, i', bo, \<phi>d')
        \<and> dsim m kks [0..<m] (dnext tw ts) \<phi>d' \<phi>')"
proof (induct "\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>)"
    J i ys xs q ts db \<phi> arbitrary: zs i' bo \<phi>' tw \<phi>d rule: letpast_meval0.induct)
  case (1 J i ys xs q ts db \<phi>)
  note IH = 1(1) and E = 1(2) and SQ = 1(3) and SZ = 1(4) and SIM = 1(5) and W = 1(6)
    and S = 1(7) and B = 1(8) and LY = 1(9) and LX = 1(10)
  obtain ys0 \<phi>2 where ev0: "meval j m ts (Mapping.update q xs db) \<phi> = (ys0, \<phi>2)"
    by (cases "meval j m ts (Mapping.update q xs db) \<phi>")
  define ys' where "ys' = map (reorder [0..<m] kks) ys0"
  have ev: "apfst (map (reorder [0..<m] kks)) (meval j m ts (Mapping.update q xs db) \<phi>) = (ys', \<phi>2)"
    using ev0 by (simp add: ys'_def)
  have wu: "wf_db (Mapping.update q xs db)"
    by (rule wf_db_update'[OF W]) (use LX SQ in \<open>simp add: list_all_iff\<close>)
  obtain \<phi>d2 where dv0: "deval j ts (Mapping.update q xs db) \<phi>d = (map (dtabc kks [0..<m]) ys0, \<phi>d2)"
    and s2: "dsim m kks [0..<m] (dnext tw ts) \<phi>d2 \<phi>2"
    using Q[OF SZ SIM wu S B ev0] by blast
  have fk: "dframe kks [0..<m]" by (rule dsim_dframe[OF SIM])
  have ty0: "list_all (ftable kks) ys0"
    by (rule produces_tables[OF dsim_produces[OF SIM] wu S B ev0])
  have dv: "deval j ts (Mapping.update q xs db) \<phi>d = (ys', \<phi>d2)"
    using dv0 ty0 dtabc_reorder_eq[OF dframeD(1)[OF fk]] unfolding ys'_def
    by (auto simp: list_all_iff intro!: map_cong)
  have ty: "list_all (ftable [0..<m]) ys'"
    unfolding ys'_def by (rule list_all_ftable_reorder[OF fk ty0])
  have same: "\<not> size \<phi>2 \<noteq> size \<phi>"
    using default_maux.size_snd_meval[of j m ts "Mapping.update q xs db" \<phi>] ev0 by simp
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
      have e': "letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>))
          J (i + length xs) (ys @ ys') ys' q []
          (Mapping.map_values (\<lambda>_ _. []) db) \<phi>2 = (zs, i', bo, \<phi>')"
        using E ev same Cons cont by (simp add: letpast_meval0.simps)
      have d': "letpast_meval0 (deval j) J i ys xs q ts db \<phi>d
          = letpast_meval0 (deval j) J (i + length xs) (ys @ ys') ys' q []
              (Mapping.map_values (\<lambda>_ _. []) db) \<phi>d2"
        using dv dsame Cons cont by (simp add: letpast_meval0.simps)
      have "list_all (ftable [0..<m]) zs \<and> (\<forall>y. bo = Some y \<longrightarrow> ftable [0..<m] y) \<and>
          (\<exists>\<phi>d''. letpast_meval0 (deval j) J (i + length xs) (ys @ ys') ys' q []
            (Mapping.map_values (\<lambda>_ _. []) db) \<phi>d2 = (zs, i', bo, \<phi>d'')
          \<and> dsim m kks [0..<m] (dnext (dnext tw ts) []) \<phi>d'' \<phi>')"
        by (rule IH[OF ev[symmetric] refl same Cons cont e' SQ szp s2
              wf_db_map_values_empty]) (use LY ty in auto)
      then show ?thesis using d' by (auto simp: dnext_def)
    qed
  qed
qed

text \<open>One firing of the multi-way join: the operands at their own columns, split into the
  positive and the negative ones, as @{thm [source] dmulti_join_eq} takes them.\<close>

lemma map2_zip_dtabcs:
  "length K = length as \<Longrightarrow> length C = length as \<Longrightarrow>
     map2 (\<lambda>(k, c). dtabc k c) (zip K C) as = dtabcs K C as"
  by (rule nth_equalityI) auto

lemma dands_step:
  assumes fs: "\<forall>i < length (c0 # css @ nss). dframe ((k0 # kss @ nkss) ! i) ((c0 # css @ nss) ! i)"
    and lk: "length kss = length css" and lnk: "length nkss = length nss"
    and sb: "\<forall>c \<in> set nss. set c \<subseteq> set (dands_cols c0 css)"
    and fK: "dframe ks (dands_cols c0 css)"
    and las: "length as = length (c0 # css @ nss)"
    and mas: "\<forall>i < length (c0 # css @ nss). ftable ((k0 # kss @ nkss) ! i) (as ! i)"
  shows "dtabc ks (dands_cols c0 css) (mmulti_join ks (k0 # kss) nkss as)
    = dmulti_join (dands_plans c0 css) (dands_plans (dands_cols c0 css) nss)
        (dtabcs (k0 # kss @ nkss) (c0 # css @ nss) as)"
proof -
  obtain T0 r where a0: "as = T0 # r" using las by (cases as) auto
  have lr: "length r = length css + length nss" using las a0 by simp
  define Us where "Us = take (length css) r"
  define Vs where "Vs = drop (length css) r"
  have uv: "r = Us @ Vs" by (simp add: Us_def Vs_def)
  have lu: "length Us = length css" using lr by (simp add: Us_def)
  have lv: "length Vs = length nss" using lr by (simp add: Vs_def)
  have f0: "dframe k0 c0" using fs[rule_format, of 0] by simp
  have t0: "table k0 T0" and fT0: "finite T0" using mas[rule_format, of 0] a0 by auto
  have fp: "i < length css \<Longrightarrow> dframe (kss ! i) (css ! i)" for i
    using fs[rule_format, of "Suc i"] lk by (simp add: nth_append)
  have fn: "i < length nss \<Longrightarrow> dframe (nkss ! i) (nss ! i)" for i
    using fs[rule_format, of "Suc (length css + i)"] lk by (simp add: nth_append)
  have mp: "i < length css \<Longrightarrow> ftable (kss ! i) (Us ! i)" for i
    using mas[rule_format, of "Suc i"] lk lu unfolding a0 uv by (simp add: nth_append)
  have mn: "i < length nss \<Longrightarrow> ftable (nkss ! i) (Vs ! i)" for i
    using mas[rule_format, of "Suc (length css + i)"] lk lu unfolding a0 uv by (simp add: nth_append)
  have pos: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) (zip kss css) Us"
    using lk lu fp mp by (auto simp: list_all2_conv_all_nth wf_operand_def)
  have neg: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) (zip nkss nss) Vs"
    using lnk lv fn mn by (auto simp: list_all2_conv_all_nth wf_operand_def)
  have sub: "\<forall>c \<in> set (map snd (zip nkss nss)). set c \<subseteq> set (dands_cols c0 (map snd (zip kss css)))"
    using sb lk lnk by simp
  have fd: "dframe (kands_cols k0 kss) (dands_cols c0 css)"
    by (rule dframe_dands_cols[OF _ f0]) (use lk fp in \<open>auto simp: list_all2_conv_all_nth\<close>)
  have cs: "distinct ks" "set ks = set (kands_cols k0 (map fst (zip kss css)))"
    using dframeD(1,3)[OF fK] dframeD(3)[OF fd] lk by simp_all
  have DJ: "dmulti_join (dands_plans c0 (map snd (zip kss css)))
        (dands_plans (dands_cols c0 (map snd (zip kss css))) (map snd (zip nkss nss)))
        (map2 (\<lambda>(k, c). dtabc k c) ((k0, c0) # zip kss css @ zip nkss nss) ((T0 # Us) @ Vs))
      = dtabc ks (dands_cols c0 (map snd (zip kss css)))
          (mmulti_join ks (k0 # map fst (zip kss css)) (map fst (zip nkss nss)) ((T0 # Us) @ Vs))"
    by (rule dmulti_join_eq[OF f0 t0 fT0 pos neg sub cs])
  have z: "(k0, c0) # zip kss css @ zip nkss nss = zip (k0 # kss @ nkss) (c0 # css @ nss)"
    using lk by simp
  have "map2 (\<lambda>(k, c). dtabc k c) ((k0, c0) # zip kss css @ zip nkss nss) as
      = dtabcs (k0 # kss @ nkss) (c0 # css @ nss) as"
    unfolding z by (rule map2_zip_dtabcs) (use las lk lnk in simp_all)
  then show ?thesis using DJ lk lnk unfolding a0 uv by simp
qed

lemma dtabc_neg:
  "map (\<lambda>r. if r = {} then {[]} else {}) (map (dtabc [] []) ys)
     = map (dtabc [] []) (map (\<lambda>r. if r = empty_table then unit_table else empty_table) ys)"
  by (auto simp: dtabc_def restrict_def unit_table_def empty_table_def)

theorem dsim_deval_N:
  assumes Q: "\<And>n' ks' cs' tw' \<phi>d' \<chi> j' ts' db' xs' \<chi>'. size \<chi> < NN \<Longrightarrow> dsim n' ks' cs' tw' \<phi>d' \<chi> \<Longrightarrow>
      wf_db db' \<Longrightarrow> sorted ts' \<Longrightarrow> (\<forall>t \<in> set ts'. tw' \<le> t) \<Longrightarrow>
      meval j' n' ts' db' \<chi> = (xs', \<chi>') \<Longrightarrow>
      \<exists>\<phi>d''. deval j' ts' db' \<phi>d' = (map (dtabc ks' cs') xs', \<phi>d'')
        \<and> dsim n' ks' cs' (dnext tw' ts') \<phi>d'' \<chi>'"
  shows "dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> size \<phi> \<le> NN \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc ks cs) xs, \<phi>d')
     \<and> dsim n ks cs (dnext tw ts) \<phi>d' \<phi>'"
proof (induct arbitrary: j ts db xs \<phi>' rule: dsim.induct)
  case (DsRel ks cs n tw rel)
  note wf = DsRel.hyps(1) and p = DsRel.hyps(2) and t = DsRel.hyps(3)
    and w = DsRel.prems(1) and sts = DsRel.prems(2)
    and mts = DsRel.prems(3) and m = DsRel.prems(4)
  have x: "xs = replicate (length ts) rel" and f: "\<phi>' = mformula.MRel rel" using m by simp_all
  show ?case using wf produces_next[OF p w sts mts m] t f by (simp add: x f dsim.DsRel)
next
  case (DsPredC ks cs n tw e tms)
  note wf = DsPredC.hyps(1) and pr = DsPredC.hyps(2) and tm = DsPredC.hyps(3)
    and kse = DsPredC.hyps(4) and cse = DsPredC.hyps(5) and w = DsPredC.prems(1)
    and sts = DsPredC.prems(2) and mts = DsPredC.prems(3) and m = DsPredC.prems(4)
  have f: "\<phi>' = mformula.MPred e tms Copy" using m by simp
  have t: "list_all (ftable ks) xs" by (rule produces_tables[OF pr w sts mts m])
  have mp: "map (dtabc ks cs) xs = xs"
    using t dtabc_same[OF dframeD(1)[OF wf]] unfolding cse by (induct xs) auto
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) {}" using m None by simp
    show ?thesis using wf pr tm kse cse produces_next[OF pr w sts mts m] None x f mp
      by (auto intro!: dsim.DsPredC)
  next
    case (Some ys)
    have x: "xs = ys" using m Some by simp
    show ?thesis using wf pr tm kse cse produces_next[OF pr w sts mts m] Some x f mp
      by (auto intro!: dsim.DsPredC)
  qed
next
  case (DsPredS ks cs n tw e tms)
  note wf = DsPredS.hyps(1) and pr = DsPredS.hyps(2) and sp = DsPredS.hyps(3)
    and cse = DsPredS.hyps(4) and kse = DsPredS.hyps(5) and w = DsPredS.prems(1)
    and sts = DsPredS.prems(2) and mts = DsPredS.prems(3) and m = DsPredS.prems(4)
  have f: "\<phi>' = mformula.MPred e tms Simple" using m by simp
  have t: "list_all (ftable ks) xs" by (rule produces_tables[OF pr w sts mts m])
  have mp: "map (dtabc ks cs) xs = xs"
    using t dtabc_same[OF dframeD(1)[OF wf]] unfolding kse by (induct xs) auto
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) {}" using m None by simp
    show ?thesis using wf pr sp cse kse produces_next[OF pr w sts mts m] None x f mp
      by (auto intro!: dsim.DsPredS)
  next
    case (Some ys)
    have x: "xs = ys" using m Some by simp
    show ?thesis using wf pr sp cse kse produces_next[OF pr w sts mts m] Some x f mp
      by (auto intro!: dsim.DsPredS)
  qed
next
  case (DsPredM ks cs n tw e tms)
  note wf = DsPredM.hyps(1) and pr = DsPredM.hyps(2) and kse = DsPredM.hyps(3)
    and w = DsPredM.prems(1) and sts = DsPredM.prems(2)
    and mts = DsPredM.prems(3) and m = DsPredM.prems(4)
  have f: "\<phi>' = mformula.MPred e tms Match" using m by simp
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) {}" using m None by simp
    show ?thesis using wf pr kse produces_next[OF pr w sts mts m] None x f
      by (auto intro!: dsim.DsPredM)
  next
    case (Some ys)
    have x: "xs = map (\<lambda>X. tabulate_match (pred_cols tms) ` Option.these (match tms ` X)) ys"
      using m Some by simp
    have sc: "set cs \<subseteq> set ks" using dframeD(3)[OF wf] by simp
    have mp: "map (umatch_table tms cs) ys = map (dtabc ks cs) xs"
      unfolding x map_map kse
      by (intro map_cong[OF refl]) (simp add: umatch_table_dtabc[OF sc[unfolded kse]])
    show ?thesis using wf pr kse produces_next[OF pr w sts mts m] Some x f mp
      by (auto intro!: dsim.DsPredM)
  qed
next
  case (DsAndRel ks cs n tw \<phi> t1 p c t2 \<phi>d)
  note wf = DsAndRel.hyps(1) and pr = DsAndRel.hyps(2) and sim = DsAndRel.hyps(3)
    and IH = DsAndRel.hyps(4) and fv1 = DsAndRel.hyps(5) and fv2 = DsAndRel.hyps(6)
    and w = DsAndRel.prems(1) and sts = DsAndRel.prems(2)
    and mts = DsAndRel.prems(3) and m = DsAndRel.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (Set.filter (eval_constraint ks (t1, p, c, t2))) ys"
    and f: "\<phi>' = mformula.MAndRel ks \<psi>' (t1, p, c, t2)" using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsAndRel.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc ks cs) ys, \<psi>d')"
    and sim': "dsim n ks cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have "map (Set.filter (ueval_constraint (reindex_constraint cs (t1, p, c, t2))))
        (map (dtabc ks cs) ys) = map (dtabc ks cs) xs"
    unfolding x by (simp only: map_map comp_def ueval_constraint_reindex[OF fv1 fv2])
  then show ?case using d sim' produces_next[OF pr w sts mts m] wf fv1 fv2 f
    by (auto intro!: dsim.DsAndRel)
next
  case (DsNeg n tw \<phi> \<phi>d)
  note pr = DsNeg.hyps(1) and sim = DsNeg.hyps(2) and IH = DsNeg.hyps(3)
    and w = DsNeg.prems(1) and sts = DsNeg.prems(2)
    and mts = DsNeg.prems(3) and m = DsNeg.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. if r = empty_table then unit_table else empty_table) ys"
    and f: "\<phi>' = mformula.MNeg \<psi>'" using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsNeg.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc [] []) ys, \<psi>d')"
    and sim': "dsim n [] [] (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have "map (\<lambda>r. if r = {} then {[]} else {}) (map (dtabc [] []) ys) = map (dtabc [] []) xs"
    unfolding x by (rule dtabc_neg)
  then show ?case using d sim' produces_next[OF pr w sts mts m] f
    by (auto intro!: dsim.DsNeg)
next
  case (DsExists ks cs n tw kks \<phi> ccs \<phi>d b)
  note wf = DsExists.hyps(1) and pr = DsExists.hyps(2) and sim = DsExists.hyps(3)
    and IH = DsExists.hyps(4) and kse = DsExists.hyps(5) and cse = DsExists.hyps(6)
    and be = DsExists.hyps(7)
    and w = DsExists.prems(1) and sts = DsExists.prems(2)
    and mts = DsExists.prems(3) and m = DsExists.prems(4)
  obtain ys \<psi>' where e: "meval j (Suc n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (Suc n) ts db \<phi>")
  have x: "xs = map (\<lambda>r. ex_proj kks ` r) ys" and f: "\<phi>' = mformula.MExists kks \<psi>'"
    using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsExists.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc kks ccs) ys, \<psi>d')"
    and sim': "dsim (Suc n) kks ccs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have fc: "dframe kks ccs" by (rule dsim_dframe[OF sim])
  have pe1: "ex_drop0 ccs \<Longrightarrow> tl ` dtabc kks ccs r = dtabc ks cs (ex_proj kks ` r)"
    for r :: "event_data table"
    using dtabc_exists[OF fc, of r] unfolding kse cse by simp
  have pe2: "\<not> ex_drop0 ccs \<Longrightarrow> dtabc kks ccs r = dtabc ks cs (ex_proj kks ` r)"
    for r :: "event_data table"
    using dtabc_exists[OF fc, of r] unfolding kse cse by simp
  have "(if b then map (\<lambda>r. tl ` r) (map (dtabc kks ccs) ys) else map (dtabc kks ccs) ys)
      = map (dtabc ks cs) xs"
    unfolding x be by (cases "ex_drop0 ccs") (simp_all add: comp_def pe1 pe2)
  then show ?case using d sim' produces_next[OF pr w sts mts m] wf kse cse be f
    by (auto intro!: dsim.DsExists)
next
  case (DsOr ks cs n tw \<phi> k2 \<psi> buf \<phi>d \<psi>d dbuf)
  note wf = DsOr.hyps(1) and pr = DsOr.hyps(2) and sim1 = DsOr.hyps(3) and IH1 = DsOr.hyps(4)
    and sim2 = DsOr.hyps(5) and IH2 = DsOr.hyps(6) and bf = DsOr.hyps(7)
    and w = DsOr.prems(1) and sts = DsOr.prems(2)
    and mts = DsOr.prems(3) and m = DsOr.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. r1 \<union> reorder ks k2 r2) (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. r1 \<union> reorder ks k2 r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MOr ks \<phi>2 k2 \<psi>2 buf2" using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsOr.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc ks cs) as, \<phi>d2)"
    and s1: "dsim n ks cs (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc k2 cs) bs, \<psi>d2)"
    and s2: "dsim n k2 cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have f2: "dframe k2 cs" by (rule dsim_dframe[OF sim2])
  have ta: "list_all (ftable ks) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable k2) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  have badd: "dbuf2 ks cs k2 cs (mbuf2_add as bs buf)
      (mbuf2_add (map (dtabc ks cs) as) (map (dtabc k2 cs) bs) dbuf)"
    by (rule dbuf2_add[OF bf ta tb])
  have e: "set k2 = set ks" using dframeD(3)[OF wf] dframeD(3)[OF f2] by simp
  have step: "\<And>a b :: event_data table. ftable ks a \<Longrightarrow> ftable k2 b \<Longrightarrow>
      dtabc ks cs a \<union> dtabc k2 cs b = dtabc ks cs (a \<union> reorder ks k2 b)"
  proof -
    fix a b :: "event_data table" assume ta': "ftable ks a" and tb: "ftable k2 b"
    have "dtabc ks cs (reorder ks k2 b) = reorder cs cs (dtabc k2 cs b)"
      by (rule dtabc_reorder[OF wf f2 e conjunct1[OF tb]])
    then show "dtabc ks cs a \<union> dtabc k2 cs b = dtabc ks cs (a \<union> reorder ks k2 b)"
      by (simp add: dtabc_Un_img reorder_def)
  qed
  obtain dbuf2' where dt: "mbuf2_take (\<lambda>r1 r2. r1 \<union> r2)
        (mbuf2_add (map (dtabc ks cs) as) (map (dtabc k2 cs) bs) dbuf)
      = (map (dtabc ks cs) zs, dbuf2')"
    and bf': "dbuf2 ks cs k2 cs buf2 dbuf2'"
    using dbuf2_take[OF badd step e3] by blast
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr w sts mts m] wf x f
    by (auto intro!: dsim.DsOr)
next
  case (DsAnd ks cs n tw k1 \<phi> pos k2 \<psi> buf c1 \<phi>d c2 \<psi>d pl dbuf)
  note wf = DsAnd.hyps(1) and pr = DsAnd.hyps(2) and sim1 = DsAnd.hyps(3)
    and IH1 = DsAnd.hyps(4) and sim2 = DsAnd.hyps(5) and IH2 = DsAnd.hyps(6)
    and kse = DsAnd.hyps(7) and cse = DsAnd.hyps(8) and ple = DsAnd.hyps(9)
    and neg = DsAnd.hyps(10) and bf = DsAnd.hyps(11)
    and w = DsAnd.prems(1) and sts = DsAnd.prems(2)
    and mts = DsAnd.prems(3) and m = DsAnd.prems(4)
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. bin_join k1 r1 pos k2 r2)
        (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. bin_join k1 r1 pos k2 r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MAnd k1 \<phi>2 pos k2 \<psi>2 buf2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsAnd.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc k1 c1) as, \<phi>d2)"
    and s1: "dsim n k1 c1 (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc k2 c2) bs, \<psi>d2)"
    and s2: "dsim n k2 c2 (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have f1: "dframe k1 c1" by (rule dsim_dframe[OF sim1])
  have f2: "dframe k2 c2" by (rule dsim_dframe[OF sim2])
  have ta: "list_all (ftable k1) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable k2) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  have badd: "dbuf2 k1 c1 k2 c2 (mbuf2_add as bs buf)
      (mbuf2_add (map (dtabc k1 c1) as) (map (dtabc k2 c2) bs) dbuf)"
    by (rule dbuf2_add[OF bf ta tb])
  have step: "\<And>a b. ftable k1 a \<Longrightarrow> ftable k2 b \<Longrightarrow>
      dbin_join pl (dtabc k1 c1 a) pos (dtabc k2 c2 b) = dtabc ks cs (bin_join k1 a pos k2 b)"
  proof -
    fix a b :: "event_data table" assume a: "ftable k1 a" and b: "ftable k2 b"
    have "bin_join k1 a pos k2 b = join k1 a pos k2 b"
      by (rule bin_join_table[OF dframeD(1)[OF f1] dframeD(1)[OF f2] conjunct1[OF a] conjunct1[OF b]])
    then show "dbin_join pl (dtabc k1 c1 a) pos (dtabc k2 c2 b) = dtabc ks cs (bin_join k1 a pos k2 b)"
      unfolding ple cse kse using dbin_join_join[OF f1 f2 _ _ neg] a b by simp
  qed
  obtain dbuf2' where dt: "mbuf2_take (\<lambda>r1 r2. dbin_join pl r1 pos r2)
        (mbuf2_add (map (dtabc k1 c1) as) (map (dtabc k2 c2) bs) dbuf)
      = (map (dtabc ks cs) zs, dbuf2')"
    and bf': "dbuf2 k1 c1 k2 c2 buf2 dbuf2'"
    using dbuf2_take[OF badd step e3] by blast
  show ?case using d1 d2 dt bf' s1 s2 produces_next[OF pr w sts mts m] wf kse cse ple neg x f
    by (auto intro!: dsim.DsAnd)
next
  case (DsPrev ks cs n tw I \<phi> first buf nts \<phi>d dbuf)
  note wf = DsPrev.hyps(1) and pr = DsPrev.hyps(2) and sim = DsPrev.hyps(3)
    and IH = DsPrev.hyps(4) and lb = DsPrev.hyps(5) and be = DsPrev.hyps(6)
    and w = DsPrev.prems(1) and sts = DsPrev.prems(2)
    and mts = DsPrev.prems(3) and m = DsPrev.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsPrev.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc ks cs) ys, \<psi>d')"
    and sim': "dsim n ks cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have t: "list_all (ftable ks) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
  have tb: "list_all (ftable ks) (buf @ ys)" using lb t by simp
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
    have g': "mprev_next I (map (dtabc ks cs) (buf @ ys)) (nts @ ts)
        = (map (dtabc ks cs) zs, map (dtabc ks cs) buf', nts')"
      by (rule mprev_next_map[OF _ g]) simp
    have tb': "list_all (ftable ks) buf'"
      using mprev_next_sub[OF g] tb by (auto simp: list_all_iff)
    show ?thesis using d be False x f sim' produces_next[OF pr w sts mts m] wf tb' g'
      by (auto simp: empty_table_def intro!: dsim.DsPrev)
  qed
next
  case (DsNext ks cs n tw I \<phi> first nts \<phi>d)
  note wf = DsNext.hyps(1) and pr = DsNext.hyps(2) and sim = DsNext.hyps(3)
    and IH = DsNext.hyps(4) and w = DsNext.prems(1) and sts = DsNext.prems(2)
    and mts = DsNext.prems(3) and m = DsNext.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsNext.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc ks cs) ys, \<psi>d')"
    and sim': "dsim n ks cs (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  obtain ys0 first0 where c:
      "(case (ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a) = (ys0, first0)"
    by (cases "(case (ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a)") auto
  have c': "(case (map (dtabc ks cs) ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a)
      = (map (dtabc ks cs) ys0, first0)"
    using c by (cases ys; cases first) auto
  obtain zs buf' nts' where g: "mprev_next I ys0 (nts @ ts) = (zs, buf', nts')"
    by (cases "mprev_next I ys0 (nts @ ts)") auto
  have x: "xs = zs" and f: "\<phi>' = mformula.MNext I \<psi>' first0 nts'"
    using m e c g by (simp_all add: Let_def split: prod.splits)
  have g': "mprev_next I (map (dtabc ks cs) ys0) (nts @ ts)
      = (map (dtabc ks cs) zs, map (dtabc ks cs) buf', nts')"
    by (rule mprev_next_map[OF _ g]) simp
  show ?case using d c' g' x f sim' produces_next[OF pr w sts mts m] wf
    by (auto intro!: dsim.DsNext)
next
  case (DsAnds ks cs n tw k0 kss nkss L buf c0 css nss Ld ps ns dbuf)
  note wf = DsAnds.hyps(1) and pr = DsAnds.hyps(2) and la = DsAnds.hyps(3)
    and l1 = DsAnds.hyps(4) and l2 = DsAnds.hyps(5) and lk = DsAnds.hyps(6)
    and lnk = DsAnds.hyps(7) and sb = DsAnds.hyps(8) and cse = DsAnds.hyps(9)
    and pse = DsAnds.hyps(10) and nse = DsAnds.hyps(11) and bf = DsAnds.hyps(12)
    and w = DsAnds.prems(1) and sts = DsAnds.prems(2)
    and mts = DsAnds.prems(3) and m = DsAnds.prems(4)
  let ?ks' = "k0 # kss @ nkss"
  let ?cs' = "c0 # css @ nss"
  let ?R = "map (meval j n ts db) L"
  have l3: "length ?ks' = length L" using l2 lk lnk by simp
  obtain zs buf' where g0: "mbufn_take
      (\<lambda>as zs. zs @ [mmulti_join ks (k0 # kss) nkss as])
      ([] :: event_data table list) (mbufn_add (map fst ?R) buf) = (zs, buf')"
    by (cases "mbufn_take
      (\<lambda>as zs. zs @ [mmulti_join ks (k0 # kss) nkss as])
      ([] :: event_data table list) (mbufn_add (map fst ?R) buf)") auto
  have x: "xs = zs"
    and fe: "\<phi>' = mformula.MAnds ks (k0 # kss) nkss (map snd ?R) buf'"
    using m g0 by (simp_all add: Let_def del: mbufn_take.simps mmulti_join.simps)
  \<comment> \<open>the operands, and their reordering\<close>
  have la0: "\<forall>i < length L. dsim n (?ks' ! i) (?cs' ! i) tw (Ld ! i) (L ! i)" using la by blast
  have tabs: "\<forall>i < length ?cs'. list_all (ftable (?ks' ! i)) (map fst ?R ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length ?cs'"
    then have iL: "i < length L" using l2 by simp
    have "list_all (ftable (?ks' ! i)) (fst (meval j n ts db (L ! i)))"
      by (rule dsims_tables[OF la0 w sts mts iL])
    then show "list_all (ftable (?ks' ! i)) (map fst ?R ! i)"
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
  have la1: "\<forall>i < length L. dsim n (?ks' ! i) (?cs' ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc (?ks' ! i) (?cs' ! i)) as, \<psi>d')
            \<and> dsim n (?ks' ! i) (?cs' ! i) (dnext tw ts) \<psi>d' \<psi>'))"
    using la w sts mts szL by blast
  have dlr: "length (map (deval j ts db) Ld) = length L \<and>
      map fst (map (deval j ts db) Ld)
        = map2 map (map2 dtabc ?ks' ?cs') (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (?ks' ! i) (?cs' ! i) (dnext tw ts) (map snd (map (deval j ts db) Ld) ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF l1 l2 l3 la1])
  have dl0: "length (map (deval j ts db) Ld) = length L" using dlr by blast
  have dl: "map fst (map (deval j ts db) Ld) = map2 map (map2 dtabc ?ks' ?cs') (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (?ks' ! i) (?cs' ! i) (dnext tw ts) (map snd (map (deval j ts db) Ld) ! i)
      (snd (meval j n ts db (L ! i)))" using dlr by blast
  \<comment> \<open>the buffer\<close>
  have badd: "dbufn ?ks' ?cs' (mbufn_add (map fst ?R) buf)
      (mbufn_add (map fst (map (deval j ts db) Ld)) dbuf)"
    unfolding dl by (rule dbufn_add[OF bf _ tabs]) (use l2 in simp)
  \<comment> \<open>the join at each firing\<close>
  have fs: "\<forall>i < length ?cs'. dframe (?ks' ! i) (?cs' ! i)"
    using la0 l2 by (auto dest: dsim_dframe)
  have step: "\<And>as :: event_data table list. length as = length ?cs' \<Longrightarrow>
      (\<forall>i < length ?cs'. ftable (?ks' ! i) (as ! i)) \<Longrightarrow>
      dtabc ks cs (mmulti_join ks (k0 # kss) nkss as) = dmulti_join ps ns (dtabcs ?ks' ?cs' as)"
    unfolding cse pse nse by (rule dands_step[OF fs lk lnk sb wf[unfolded cse]])
  obtain dbuf' where dt: "mbufn_take (\<lambda>as zs. zs @ [dmulti_join ps ns as])
        ([] :: event_data table list) (mbufn_add (map fst (map (deval j ts db) Ld)) dbuf)
      = (map (dtabc ks cs) zs, dbuf')"
    and bf': "dbufn ?ks' ?cs' buf' dbuf'"
    using dbufn_take[OF badd step g0] by blast
  have dv: "deval j ts db (DAnds ps ns Ld dbuf)
      = (map (dtabc ks cs) xs, DAnds ps ns (map snd (map (deval j ts db) Ld)) dbuf')"
    using dt x by (simp add: Let_def del: mbufn_take.simps)
  have s2: "dsim n ks cs (dnext tw ts) (DAnds ps ns (map snd (map (deval j ts db) Ld)) dbuf')
      (mformula.MAnds ks (k0 # kss) nkss (map snd ?R) buf')"
  proof (rule dsim.DsAnds)
    show "dframe ks cs" by (rule wf)
    show "produces n ks (dnext tw ts) (mformula.MAnds ks (k0 # kss) nkss (map snd ?R) buf')"
      using produces_next[OF pr w sts mts m] fe by simp
    show "\<forall>i < length (map snd ?R). dsim n (?ks' ! i) (?cs' ! i) (dnext tw ts)
        (map snd (map (deval j ts db) Ld) ! i) (map snd ?R ! i)"
      using dl2 by simp
    show "length (map snd (map (deval j ts db) Ld)) = length (map snd ?R)"
      using dl0 by simp
    show "length ?cs' = length (map snd ?R)" using l2 by simp
  qed (use lk lnk sb cse pse nse bf' in simp_all)
  show ?case using dv s2 fe by auto
next
  case (DsAgg ks cs n tw args \<phi> k0 gcols \<phi>d y)
  note wf = DsAgg.hyps(1) and pr = DsAgg.hyps(2) and sim = DsAgg.hyps(3) and IH = DsAgg.hyps(4)
    and kc = DsAgg.hyps(5) and ye = DsAgg.hyps(6) and yg = DsAgg.hyps(7)
    and g0 = DsAgg.hyps(8) and fv = DsAgg.hyps(9) and kse = DsAgg.hyps(10) and cse = DsAgg.hyps(11)
    and w = DsAgg.prems(1) and sts = DsAgg.prems(2)
    and mts = DsAgg.prems(3) and m = DsAgg.prems(4)
  let ?mm = "length (aggargs_tys args)"
  let ?cc = "agg_cols ?mm gcols"
  obtain ys \<psi>' where e: "meval j (?mm + n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (?mm + n) ts db \<phi>")
  have x: "xs = map (eval_aggargs args) ys" and f: "\<phi>' = mformula.MAgg args \<psi>'"
    using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsAgg.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc k0 ?cc) ys, \<psi>d')"
    and sim': "dsim (?mm + n) k0 ?cc (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have fc: "dframe k0 ?cc" by (rule dsim_dframe[OF sim])
  have t: "list_all (ftable k0) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
  have "map (uagg (aggargs_g0 args) (aggargs_\<omega> args) (reindex_trm ?cc (aggargs_f args)) ?mm
          (ins_pos gcols y)) (map (dtabc k0 ?cc) ys) = map (dtabc ks cs) xs"
    unfolding x kse cse using t
    by (intro nth_equalityI)
      (auto simp: list_all_iff eval_aggargs_def kc uagg_eval_agg[OF fc _ fv yg g0])
  then show ?case using d sim' produces_next[OF pr w sts mts m] wf kc ye yg g0 fv kse cse f
    by (auto intro!: dsim.DsAgg)
next
  case (DsSince kR cR n tw args \<phi> \<psi> buf aux kL cL \<phi>d \<psi>d dags daux dbuf)
  note wf = DsSince.hyps(1) and pr = DsSince.hyps(2)
    and sim1 = DsSince.hyps(3) and IH1 = DsSince.hyps(4)
    and sim2 = DsSince.hyps(5) and IH2 = DsSince.hyps(6)
    and sub = DsSince.hyps(7) and agg = DsSince.hyps(8)
    and aL = DsSince.hyps(9) and aR = DsSince.hyps(10)
    and dag = DsSince.hyps(11) and rel = DsSince.hyps(12) and nag = DsSince.hyps(13)
    and w = DsSince.prems(1) and sts = DsSince.prems(2)
    and mts = DsSince.prems(3) and m = DsSince.prems(4)
  let ?nn = "args_n args"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsSince.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) as, \<phi>d2)"
    and s1: "dsim ?nn kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) bs, \<psi>d2)"
    and s2: "dsim ?nn kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have ta: "list_all (ftable kL) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs dbuf2 daux2 where d3: "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)"
    by (cases "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux")
  have radd: "dsince_rel kR cR kL cL args (dnext tw ts) aux daux (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf)"
    by (rule dsince_rel_add[OF rel ta tb sts mts])
  have d3': "dsx_eval_since (dargs cR cL args) []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)" using d3 unfolding dag by simp
  have post: "dsx_post daux = id" using nag by (simp add: dsx_post_eq)
  have step0: "dsres kR cR args zs dzs \<and>
      dsince_rel kR cR kL cL args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using eval_since_rel[OF wf fL sub aL aR e3 d3' radd refl] by (simp add: post dsresh_id)
  have nag2: "dsx_agg daux2 = None" using dsx_agg_eval_since[OF d3] nag by simp
  have step: "dzs = map (dtabc kR cR) zs \<and>
      dsince_rel kR cR kL cL args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using step0 dsres_none[OF agg] by blast
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DSince dags \<phi>d \<psi>d dbuf daux)
        = (map (dtabc kR cR) xs, DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2)"
      using d1 d2 d3 step x by simp
    show "dsim n kR cR (dnext tw ts) (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsSince[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 sub agg aL aR
            dag]) (use step nag2 in simp_all)
  qed
next
  case (DsUntil kR cR n tw args \<phi> \<psi> buf nts t aux kL cL \<phi>d \<psi>d dags msk daux dbuf)
  note wf = DsUntil.hyps(1) and pr = DsUntil.hyps(2)
    and sim1 = DsUntil.hyps(3) and IH1 = DsUntil.hyps(4)
    and sim2 = DsUntil.hyps(5) and IH2 = DsUntil.hyps(6)
    and sub = DsUntil.hyps(7) and agg = DsUntil.hyps(8)
    and aL = DsUntil.hyps(9) and aR = DsUntil.hyps(10)
    and dag = DsUntil.hyps(11) and pe = DsUntil.hyps(12) and rel = DsUntil.hyps(13)
    and nag = DsUntil.hyps(14)
    and w = DsUntil.prems(1) and sts = DsUntil.prems(2)
    and mts = DsUntil.prems(3) and m = DsUntil.prems(4)
  let ?nn = "args_n args"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain aux1 buf1 nt nts1 where e3: "mbuf2t_take (add_new_muaux_dq args) aux
      (mbuf2_add as bs buf) t (nts @ ts) = (aux1, buf1, nt, nts1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ ts)")
  obtain zs aux2 where e4: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    by (cases "eval_muaux_dq args nt aux1")
  have x: "xs = zs" and f: "\<phi>' = mformula.MUntil args \<phi>2 \<psi>2 buf1 nts1 nt aux2"
    using m e1 e2 e3 e4 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsUntil.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) as, \<phi>d2)"
    and s1: "dsim ?nn kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) bs, \<psi>d2)"
    and s2: "dsim ?nn kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have ta: "list_all (ftable kL) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) t (nts @ ts)")
  obtain dzs daux2 where d4: "dux_eval dags dnt daux1 = (dzs, daux2)"
    by (cases "dux_eval dags dnt daux1")
  have post: "dux_post daux = id" using nag by (simp add: dux_post_eq)
  have step: "dsresh kR cR args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (dtabc kL cL) (fst buf1), map (dtabc kR cR) (snd buf1)) \<and>
      duntil_rel kR cR kL cL args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF wf fL sub aL aR rel ta tb sts mts e3
        d3[unfolded dag pe] e4 d4[unfolded dag]])
  have dres: "dsres kR cR args zs dzs"
    using step unfolding post by (simp add: dsresh_def dsres_def)
  have nag2: "dux_agg daux2 = None"
    using dux_agg_mbuf2t_take[OF d3[unfolded dag pe]] dux_agg_eval[of dags dnt daux1]
      d4 nag by simp
  have dz: "dzs = map (dtabc kR cR) zs" using dres dsres_none[OF agg] by blast
  have dn: "dnt = nt" and dns: "dnts1 = nts1"
    and rel': "duntil_rel kR cR kL cL args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
        = (map (dtabc kR cR) xs, DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2)"
      using d1 d2 d3 d4 dz dn dns x by simp
    show "dsim n kR cR (dnext tw ts) (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsUntil[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 sub agg aL aR
            dag pe rel' nag2])
  qed
next
  case (DsSinceAgg ks cs n tw args \<phi> \<psi> buf aux kL cL \<phi>d kR cR \<psi>d ag dags daux dbuf y gcols)
  note wf = DsSinceAgg.hyps(1) and pr = DsSinceAgg.hyps(2)
    and sim1 = DsSinceAgg.hyps(3) and IH1 = DsSinceAgg.hyps(4)
    and sim2 = DsSinceAgg.hyps(5) and IH2 = DsSinceAgg.hyps(6)
    and sub = DsSinceAgg.hyps(7) and agg = DsSinceAgg.hyps(8)
    and aL = DsSinceAgg.hyps(9) and aR = DsSinceAgg.hyps(10)
    and dag = DsSinceAgg.hyps(11) and rel = DsSinceAgg.hyps(12)
    and kc = DsSinceAgg.hyps(13) and ye = DsSinceAgg.hyps(14) and yg = DsSinceAgg.hyps(15)
    and g0 = DsSinceAgg.hyps(16) and fv = DsSinceAgg.hyps(17) and cRe = DsSinceAgg.hyps(18)
    and kse = DsSinceAgg.hyps(19) and cse = DsSinceAgg.hyps(20) and nag = DsSinceAgg.hyps(21)
    and w = DsSinceAgg.prems(1) and sts = DsSinceAgg.prems(2)
    and mts = DsSinceAgg.prems(3) and m = DsSinceAgg.prems(4)
  let ?nn = "args_n args"
  let ?ag = "uagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsSinceAgg.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) as, \<phi>d2)"
    and s1: "dsim ?nn kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) bs, \<psi>d2)"
    and s2: "dsim ?nn kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have fR: "dframe kR cR" by (rule dsim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs dbuf2 daux2 where d3: "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)"
    by (cases "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux")
  have radd: "dsince_rel kR cR kL cL args (dnext tw ts) aux daux (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf)"
    by (rule dsince_rel_add[OF rel ta tb sts mts])
  have d3': "dsx_eval_since (dargs cR cL args) []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)" using d3 unfolding dag by simp
  have post: "dsx_post daux = id" using nag by (simp add: dsx_post_eq)
  have step: "dsres kR cR args zs dzs \<and>
      dsince_rel kR cR kL cL args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using eval_since_rel[OF fR fL sub aL aR e3 d3' radd refl] by (simp add: post dsresh_id)
  have nag2: "dsx_agg daux2 = None" using dsx_agg_eval_since[OF d3] nag by simp
  have fc: "dframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "map ?ag dzs = map (dtabc ks cs) xs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (dtabc kR cR) vs"
      using step unfolding dsres_def by blast
    show ?thesis unfolding x v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
          (length (aggargs_tys ag)) (ins_pos gcols y) (DSince dags \<phi>d \<psi>d dbuf daux))
        = (map (dtabc ks cs) xs, DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
            (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
            (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2))"
      using d1 d2 d3 agc by simp
    show "dsim n ks cs (dnext tw ts) (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
          (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
          (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2)) \<phi>'"
      unfolding f
      by (rule dsim.DsSinceAgg[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 sub
            agg aL aR dag _ kc ye yg g0 fv cRe kse cse]) (use step nag2 in simp_all)
  qed
next
  case (DsSinceFused ks cs n tw args \<phi> \<psi> buf aux kL cL \<phi>d kR cR \<psi>d ag dags daux dbuf y gcols)
  note wf = DsSinceFused.hyps(1) and pr = DsSinceFused.hyps(2)
    and sim1 = DsSinceFused.hyps(3) and IH1 = DsSinceFused.hyps(4)
    and sim2 = DsSinceFused.hyps(5) and IH2 = DsSinceFused.hyps(6)
    and sub = DsSinceFused.hyps(7) and agg = DsSinceFused.hyps(8)
    and aL = DsSinceFused.hyps(9) and aR = DsSinceFused.hyps(10)
    and dag = DsSinceFused.hyps(11) and rel = DsSinceFused.hyps(12)
    and kc = DsSinceFused.hyps(13) and ye = DsSinceFused.hyps(14) and yg = DsSinceFused.hyps(15)
    and g0 = DsSinceFused.hyps(16) and fv = DsSinceFused.hyps(17) and cRe = DsSinceFused.hyps(18)
    and kse = DsSinceFused.hyps(19) and cse = DsSinceFused.hyps(20) and nag = DsSinceFused.hyps(21)
    and w = DsSinceFused.prems(1) and sts = DsSinceFused.prems(2)
    and mts = DsSinceFused.prems(3) and m = DsSinceFused.prems(4)
  let ?nn = "args_n args"
  let ?ag = "uagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsSinceFused.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) as, \<phi>d2)"
    and s1: "dsim ?nn kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) bs, \<psi>d2)"
    and s2: "dsim ?nn kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have fR: "dframe kR cR" by (rule dsim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs dbuf2 daux2 where d3: "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)"
    by (cases "dsx_eval_since dags []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux")
  have radd: "dsince_rel kR cR kL cL args (dnext tw ts) aux daux (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf)"
    by (rule dsince_rel_add[OF rel ta tb sts mts])
  have d3': "dsx_eval_since (dargs cR cL args) []
      (mbuf2S_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) ts dbuf) daux
      = (dzs, dbuf2, daux2)" using d3 unfolding dag by simp
  have post: "dsx_post daux = ?ag" using nag by (simp add: dsx_post_eq)
  have step: "dsresh kR cR args ?ag zs dzs \<and>
      dsince_rel kR cR kL cL args (dnext tw ts) aux2 daux2 buf2 dbuf2"
    using eval_since_rel[OF fR fL sub aL aR e3 d3' radd refl] by (simp add: post)
  have nag2: "dsx_agg daux2 = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
      length (aggargs_tys ag), ins_pos gcols y)"
    using dsx_agg_eval_since[OF d3] nag by simp
  have fc: "dframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "dzs = map (dtabc ks cs) xs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (?ag \<circ> dtabc kR cR) vs"
      using step unfolding dsresh_def by blast
    show ?thesis unfolding x v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DSince dags \<phi>d \<psi>d dbuf daux)
        = (map (dtabc ks cs) xs, DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2)"
      using d1 d2 d3 agc by simp
    show "dsim n ks cs (dnext tw ts) (DSince dags \<phi>d2 \<psi>d2 dbuf2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsSinceFused[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 sub
            agg aL aR dag _ kc ye yg g0 fv cRe kse cse]) (use step nag2 in simp_all)
  qed
next
  case (DsUntilAgg ks cs n tw args \<phi> \<psi> buf nts t aux kL cL \<phi>d kR cR \<psi>d ag dags msk daux dbuf
      y gcols)
  note wf = DsUntilAgg.hyps(1) and pr = DsUntilAgg.hyps(2)
    and sim1 = DsUntilAgg.hyps(3) and IH1 = DsUntilAgg.hyps(4)
    and sim2 = DsUntilAgg.hyps(5) and IH2 = DsUntilAgg.hyps(6)
    and sub = DsUntilAgg.hyps(7) and agg = DsUntilAgg.hyps(8)
    and aL = DsUntilAgg.hyps(9) and aR = DsUntilAgg.hyps(10)
    and dag = DsUntilAgg.hyps(11) and pe = DsUntilAgg.hyps(12) and rel = DsUntilAgg.hyps(13)
    and kc = DsUntilAgg.hyps(14) and ye = DsUntilAgg.hyps(15) and yg = DsUntilAgg.hyps(16)
    and g0 = DsUntilAgg.hyps(17) and fv = DsUntilAgg.hyps(18) and cRe = DsUntilAgg.hyps(19)
    and kse = DsUntilAgg.hyps(20) and cse = DsUntilAgg.hyps(21) and nag = DsUntilAgg.hyps(22)
    and w = DsUntilAgg.prems(1) and sts = DsUntilAgg.prems(2)
    and mts = DsUntilAgg.prems(3) and m = DsUntilAgg.prems(4)
  let ?nn = "args_n args"
  let ?ag = "uagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain aux1 buf1 nt nts1 where e3: "mbuf2t_take (add_new_muaux_dq args) aux
      (mbuf2_add as bs buf) t (nts @ ts) = (aux1, buf1, nt, nts1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ ts)")
  obtain zs aux2 where e4: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    by (cases "eval_muaux_dq args nt aux1")
  have x: "xs = zs" and f: "\<phi>' = mformula.MUntil args \<phi>2 \<psi>2 buf1 nts1 nt aux2"
    using m e1 e2 e3 e4 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsUntilAgg.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) as, \<phi>d2)"
    and s1: "dsim ?nn kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) bs, \<psi>d2)"
    and s2: "dsim ?nn kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have fR: "dframe kR cR" by (rule dsim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) t (nts @ ts)")
  obtain dzs daux2 where d4: "dux_eval dags dnt daux1 = (dzs, daux2)"
    by (cases "dux_eval dags dnt daux1")
  have post: "dux_post daux = id" using nag by (simp add: dux_post_eq)
  have step: "dsresh kR cR args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (dtabc kL cL) (fst buf1), map (dtabc kR cR) (snd buf1)) \<and>
      duntil_rel kR cR kL cL args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF fR fL sub aL aR rel ta tb sts mts e3
        d3[unfolded dag pe] e4 d4[unfolded dag]])
  have dres: "dsres kR cR args zs dzs"
    using step unfolding post by (simp add: dsresh_def dsres_def)
  have nag2: "dux_agg daux2 = None"
    using dux_agg_mbuf2t_take[OF d3[unfolded dag pe]] dux_agg_eval[of dags dnt daux1]
      d4 nag by simp
  have dn: "dnt = nt" and dns: "dnts1 = nts1"
    and rel': "duntil_rel kR cR kL cL args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  have fc: "dframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "map ?ag dzs = map (dtabc ks cs) xs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (dtabc kR cR) vs"
      using dres unfolding dsres_def by blast
    show ?thesis unfolding x v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
          (length (aggargs_tys ag)) (ins_pos gcols y) (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux))
        = (map (dtabc ks cs) xs, DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
            (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
            (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2))"
      using d1 d2 d3 d4 agc dn dns by simp
    show "dsim n ks cs (dnext tw ts) (DAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
          (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
          (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2)) \<phi>'"
      unfolding f
      by (rule dsim.DsUntilAgg[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 sub
            agg aL aR dag pe rel' kc ye yg g0 fv cRe kse cse nag2])
  qed
next
  case (DsUntilFused ks cs n tw args \<phi> \<psi> buf nts t aux kL cL \<phi>d kR cR \<psi>d ag dags msk daux dbuf
      y gcols)
  note wf = DsUntilFused.hyps(1) and pr = DsUntilFused.hyps(2)
    and sim1 = DsUntilFused.hyps(3) and IH1 = DsUntilFused.hyps(4)
    and sim2 = DsUntilFused.hyps(5) and IH2 = DsUntilFused.hyps(6)
    and sub = DsUntilFused.hyps(7) and agg = DsUntilFused.hyps(8)
    and aL = DsUntilFused.hyps(9) and aR = DsUntilFused.hyps(10)
    and dag = DsUntilFused.hyps(11) and pe = DsUntilFused.hyps(12) and rel = DsUntilFused.hyps(13)
    and kc = DsUntilFused.hyps(14) and ye = DsUntilFused.hyps(15) and yg = DsUntilFused.hyps(16)
    and g0 = DsUntilFused.hyps(17) and fv = DsUntilFused.hyps(18) and cRe = DsUntilFused.hyps(19)
    and kse = DsUntilFused.hyps(20) and cse = DsUntilFused.hyps(21) and nag = DsUntilFused.hyps(22)
    and w = DsUntilFused.prems(1) and sts = DsUntilFused.prems(2)
    and mts = DsUntilFused.prems(3) and m = DsUntilFused.prems(4)
  let ?nn = "args_n args"
  let ?ag = "uagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain aux1 buf1 nt nts1 where e3: "mbuf2t_take (add_new_muaux_dq args) aux
      (mbuf2_add as bs buf) t (nts @ ts) = (aux1, buf1, nt, nts1)"
    by (cases "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ ts)")
  obtain zs aux2 where e4: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    by (cases "eval_muaux_dq args nt aux1")
  have x: "xs = zs" and f: "\<phi>' = mformula.MUntil args \<phi>2 \<psi>2 buf1 nts1 nt aux2"
    using m e1 e2 e3 e4 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsUntilFused.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) as, \<phi>d2)"
    and s1: "dsim ?nn kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) bs, \<psi>d2)"
    and s2: "dsim ?nn kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have fR: "dframe kR cR" by (rule dsim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (dux_add_new dags msk) daux
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) t (nts @ ts)")
  obtain dzs daux2 where d4: "dux_eval dags dnt daux1 = (dzs, daux2)"
    by (cases "dux_eval dags dnt daux1")
  have post: "dux_post daux = ?ag" using nag by (simp add: dux_post_eq)
  have step: "dsresh kR cR args (dux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (dtabc kL cL) (fst buf1), map (dtabc kR cR) (snd buf1)) \<and>
      duntil_rel kR cR kL cL args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF fR fL sub aL aR rel ta tb sts mts e3
        d3[unfolded dag pe] e4 d4[unfolded dag]])
  have nag2: "dux_agg daux2 = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
      length (aggargs_tys ag), ins_pos gcols y)"
    using dux_agg_mbuf2t_take[OF d3[unfolded dag pe]] dux_agg_eval[of dags dnt daux1]
      d4 nag by simp
  have dn: "dnt = nt" and dns: "dnts1 = nts1"
    and rel': "duntil_rel kR cR kL cL args (dnext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  have fc: "dframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "dzs = map (dtabc ks cs) xs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (?ag \<circ> dtabc kR cR) vs"
      using step unfolding dsresh_def post by blast
    show ?thesis unfolding x v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DUntil dags msk \<phi>d \<psi>d dbuf nts t daux)
        = (map (dtabc ks cs) xs, DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2)"
      using d1 d2 d3 d4 agc dn dns by simp
    show "dsim n ks cs (dnext tw ts) (DUntil dags msk \<phi>d2 \<psi>d2 dbuf1 nts1 nt daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsUntilFused[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 sub
            agg aL aR dag pe rel' kc ye yg g0 fv cRe kse cse nag2])
  qed
next
  case (DsAndAssign ks cs n tw k0 \<phi> y t c0 \<phi>d)
  note wf = DsAndAssign.hyps(1) and pr = DsAndAssign.hyps(2) and sim = DsAndAssign.hyps(3)
    and IH = DsAndAssign.hyps(4) and yk = DsAndAssign.hyps(5) and fv = DsAndAssign.hyps(6)
    and kse = DsAndAssign.hyps(7) and cse = DsAndAssign.hyps(8)
    and w = DsAndAssign.prems(1) and sts = DsAndAssign.prems(2)
    and mts = DsAndAssign.prems(3) and m = DsAndAssign.prems(4)
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. eval_assignment k0 (y, t) ` r) ys"
    and f: "\<phi>' = mformula.MAndAssign k0 \<psi>' (y, t)"
    using m e by (simp_all del: eval_assignment.simps)
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ DsAndAssign.prems(5)]) simp
  obtain \<psi>d' where d: "deval j ts db \<phi>d = (map (dtabc k0 c0) ys, \<psi>d')"
    and sim': "dsim n k0 c0 (dnext tw ts) \<psi>d' \<psi>'" using IH[OF w sts mts e sz] by blast
  have tb: "list_all (ftable k0) ys"
    by (rule produces_tables[OF dsim_produces[OF sim] w sts mts e])
  have f0: "dframe k0 c0" by (rule dsim_dframe[OF sim])
  have mapeq: "map (uassign (ins_pos c0 y) (reindex_trm c0 t)) (map (dtabc k0 c0) ys)
      = map (dtabc ks cs) xs"
    unfolding x map_map kse cse using tb
    by (intro map_cong refl) (simp add: list_all_iff uassign_eval_assignment[OF f0 yk fv])
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<phi>d)
        = (map (dtabc ks cs) xs, DAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<psi>d')"
      using d mapeq by simp
    show "dsim n ks cs (dnext tw ts) (DAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<psi>d') \<phi>'"
      unfolding f
      by (rule dsim.DsAndAssign[OF wf produces_next[OF pr w sts mts m, unfolded f]
            sim' yk fv kse cse])
  qed
next
  case (DsTP ks cs n tw mt i)
  note wf = DsTP.hyps(1) and pr = DsTP.hyps(2) and cse = DsTP.hyps(3) and kse = DsTP.hyps(4)
    and w = DsTP.prems(1) and sts = DsTP.prems(2)
    and mts = DsTP.prems(3) and m = DsTP.prems(4)
  have x: "xs = map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) [i..<j]"
    and f: "\<phi>' = mformula.MTP mt j" using m by simp_all
  have t: "list_all (ftable ks) xs" by (rule produces_tables[OF pr w sts mts m])
  have mapeq: "map (dtabc ks cs) xs = map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) [i..<j]"
    using t dtabc_same[OF dframeD(1)[OF wf]] unfolding kse
    by (auto simp: x umtrm_eval_mtrm list_all_iff)
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DTP mt i) = (map (dtabc ks cs) xs, DTP mt j)" using mapeq by simp
    show "dsim n ks cs (dnext tw ts) (DTP mt j) \<phi>'"
      unfolding f
      by (rule dsim.DsTP[OF wf produces_next[OF pr w sts mts m, unfolded f] cse kse])
  qed
next
  case (DsTS ks cs n tw mt)
  note wf = DsTS.hyps(1) and pr = DsTS.hyps(2) and cse = DsTS.hyps(3) and kse = DsTS.hyps(4)
    and w = DsTS.prems(1) and sts = DsTS.prems(2)
    and mts = DsTS.prems(3) and m = DsTS.prems(4)
  have x: "xs = map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) ts"
    and f: "\<phi>' = mformula.MTS mt" using m by simp_all
  have t: "list_all (ftable ks) xs" by (rule produces_tables[OF pr w sts mts m])
  have mapeq: "map (dtabc ks cs) xs = map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) ts"
    using t dtabc_same[OF dframeD(1)[OF wf]] unfolding kse
    by (auto simp: x umtrm_eval_mtrm list_all_iff)
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DTS mt) = (map (dtabc ks cs) xs, DTS mt)" using mapeq by simp
    show "dsim n ks cs (dnext tw ts) (DTS mt) \<phi>'"
      unfolding f
      by (rule dsim.DsTS[OF wf produces_next[OF pr w sts mts m, unfolded f] cse kse])
  qed
next
  case (DsLet ks cs n tw p m kks \<phi> \<psi> \<phi>d \<psi>d)
  note wf = DsLet.hyps(1) and pr = DsLet.hyps(2) and sim1 = DsLet.hyps(3)
    and IH1 = DsLet.hyps(4) and sim2 = DsLet.hyps(5) and IH2 = DsLet.hyps(6)
    and w = DsLet.prems(1) and sts = DsLet.prems(2)
    and mts = DsLet.prems(3) and mv = DsLet.prems(4)
  obtain as \<phi>2 where e1: "meval j m ts db \<phi> = (as, \<phi>2)" by (cases "meval j m ts db \<phi>")
  let ?as = "map (reorder [0..<m] kks) as"
  obtain bs \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) ?as db) \<psi> = (bs, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) ?as db) \<psi>")
  have x: "xs = bs" and f: "\<phi>' = mformula.MLet p m kks \<phi>2 \<psi>2" using mv e1 e2 by simp_all
  have fk: "dframe kks [0..<m]" by (rule dsim_dframe[OF sim1])
  have ta: "list_all (ftable kks) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have dt: "map (dtabc kks [0..<m]) as = ?as"
    using ta dtabc_reorder_eq[OF dframeD(1)[OF fk]] by (auto simp: list_all_iff)
  have w': "wf_db (Mapping.update (p, m) ?as db)"
    by (rule wf_db_update'[OF w]) (use list_all_ftable_reorder[OF fk ta] in \<open>simp add: list_all_iff\<close>)
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsLet.prems(5)], simp)+
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kks [0..<m]) as, \<phi>d2)"
    and s1: "dsim m kks [0..<m] (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts (Mapping.update (p, m) ?as db) \<psi>d
        = (map (dtabc ks cs) bs, \<psi>d2)"
    and s2: "dsim n ks cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w' sts mts e2 sz2] by blast
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DLet p m \<phi>d \<psi>d) = (map (dtabc ks cs) xs, DLet p m \<phi>d2 \<psi>d2)"
      using d1 d2 unfolding x dt by simp
    show "dsim n ks cs (dnext tw ts) (DLet p m \<phi>d2 \<psi>d2) \<phi>'"
      unfolding f
      by (rule dsim.DsLet[OF wf produces_next[OF pr w sts mts mv, unfolded f] s1 s2])
  qed
next
  case (DsFrz ks cs n tw p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> wv pR tq rb d po ng lv \<rho>L \<phi>d \<psi>d \<rho>d \<rho>Ld)
  note wf = DsFrz.hyps(1) and pr = DsFrz.hyps(2) and sim1 = DsFrz.hyps(3)
    and IH1 = DsFrz.hyps(4) and sim2 = DsFrz.hyps(5) and IH2 = DsFrz.hyps(6)
    and tas = DsFrz.hyps(7) and sim3 = DsFrz.hyps(8) and IH3 = DsFrz.hyps(9)
    and szL = DsFrz.hyps(10) and szLd = DsFrz.hyps(11)
    and w = DsFrz.prems(1) and sts = DsFrz.prems(2)
    and mts = DsFrz.prems(3) and mv = DsFrz.prems(4) and le = DsFrz.prems(5)
  let ?dbe = "Mapping.map_values (\<lambda>_ _. []) db"
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN" and sz3: "size \<rho> \<le> NN"
    by (rule order_trans[OF _ le], simp)+
  have szr: "size \<rho> < NN" by (rule order.strict_trans2[OF _ le]) simp
  \<comment> \<open>the bound formula: its tables, reordered to the positional columns, are its dense ones\<close>
  obtain as0 \<phi>2 where e1: "meval j m ts db \<phi> = (as0, \<phi>2)" by (cases "meval j m ts db \<phi>")
  let ?as = "map (reorder [0..<m] kks) as0"
  have fk: "dframe kks [0..<m]" by (rule dsim_dframe[OF sim1])
  have ta0: "list_all (ftable kks) as0"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have ta: "list_all (ftable [0..<m]) ?as" by (rule list_all_ftable_reorder[OF fk ta0])
  have dt: "map (dtabc kks [0..<m]) as0 = ?as"
    using ta0 dtabc_reorder_eq[OF dframeD(1)[OF fk]] by (auto simp: list_all_iff)
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (?as, \<phi>d2)"
    and s1: "dsim m kks [0..<m] (dnext tw ts) \<phi>d2 \<phi>2"
    using IH1[OF w sts mts e1 sz1] unfolding dt by blast
  \<comment> \<open>the body and the replay base, against the database in which the bound predicate is empty\<close>
  have w0: "wf_db (Mapping.update (p, m) [] db)" by (rule wf_db_update'[OF w]) simp
  obtain zs0 \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) [] db) \<psi> = (zs0, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<psi>")
  obtain \<psi>d2 where d2: "deval j ts (Mapping.update (p, m) [] db) \<psi>d
        = (map (dtabc ks cs) zs0, \<psi>d2)"
    and s2: "dsim n ks cs (dnext tw ts) \<psi>d2 \<psi>2"
    using IH2[OF w0 sts mts e2 sz2] by blast
  obtain rs \<rho>2 where e4: "meval j n ts (Mapping.update (p, m) [] db) \<rho> = (rs, \<rho>2)"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<rho>")
  obtain \<rho>d2 where d4: "deval j ts (Mapping.update (p, m) [] db) \<rho>d
        = (map (dtabc ks cs) rs, \<rho>d2)"
    and s4: "dsim n ks cs (dnext tw ts) \<rho>d2 \<rho>2"
    using IH3[OF w0 sts mts e4 sz3] by blast
  \<comment> \<open>the frozen tuples the two runs are handed are the same list\<close>
  let ?zout = "drop (jfrz - jpsi0) zs0"
  let ?as1 = "drop (jfrz - jphi + length ?zout) (\<alpha>s @ ?as)"
  let ?F = "frz_fill ng (\<alpha>s @ ?as)"
  have tas1: "list_all (ftable [0..<m]) ?as1"
    using tas ta by (auto simp: list_all_iff dest!: in_set_dropD)
  have tF: "ftable [0..<m] ?F"
    using frz_fill_cases[of ng "\<alpha>s @ ?as"] tas ta by (auto simp: list_all_iff table_def)
  have wa: "wf_db (Mapping.update (p, m) (replicate k \<alpha>) ?dbe)" if "ftable [0..<m] \<alpha>" for k \<alpha>
    by (rule wf_db_update'[OF wf_db_map_values_empty]) (use that in \<open>simp add: list_all_iff\<close>)
  have sz\<rho>2: "size \<rho>2 = size \<rho>"
    using default_maux.size_snd_meval[of j n ts "Mapping.update (p, m) [] db" \<rho>] e4 by simp
  have sz\<rho>d2: "size \<rho>d2 = size \<rho>d"
    using size_snd_deval[of j ts "Mapping.update (p, m) [] db" \<rho>d] d4 by simp
  \<comment> \<open>the copies and the window's moves: the two runs evaluate related states on the same tables\<close>
  define R where "R st dst \<longleftrightarrow> dsim n ks cs (dnext tw ts) dst st \<and> size st = size \<rho> \<and> size dst = size \<rho>d"
    for st dst
  have agree: "fst (deval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>d) =
      map (dtabc ks cs) (fst (meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>)) \<and>
      R (snd (meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>))
        (snd (deval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>d))"
    if r: "R \<chi> \<chi>d" and X: "X \<in> Set.insert ?F (set ?as1)" for \<chi> \<chi>d c X
  proof -
    have tX: "ftable [0..<m] X"
      using X tas1 tF by (auto simp: list_all_iff)
    obtain us \<chi>' where eu: "meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi> = (us, \<chi>')"
      by (cases "meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>")
    have sz\<chi>: "size \<chi> < NN"
      using r szr by (simp add: R_def)
    obtain dus where du: "deval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>d
        = (map (dtabc ks cs) us, dus)" and sdu: "dsim n ks cs (dnext (dnext tw ts) []) dus \<chi>'"
      using Q[OF sz\<chi> conjunct1[OF r[unfolded R_def]] wa[OF tX] _ _ eu] by auto
    have "size \<chi>' = size \<rho>"
      using default_maux.size_snd_meval[of j n "[]" "Mapping.update (p, m) (replicate c X) ?dbe" \<chi>]
        eu r by (simp add: R_def)
    moreover have "size dus = size \<rho>d"
      using size_snd_deval[of j "[]" "Mapping.update (p, m) (replicate c X) ?dbe" \<chi>d] du r
      by (simp add: R_def)
    ultimately show ?thesis
      using du eu sdu by (simp add: R_def dnext_def)
  qed
  \<comment> \<open>the live copy, fed the new time points\<close>
  let ?dbL = "Mapping.update (p, m) (replicate (length ts) (hd ?as1)) db"
  define lrk where "lrk = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if ?zout = [] \<and> ?as1 \<noteq> [] then Some (g, meval j n ts ?dbL \<rho>L) else None)"
  define lrd where "lrd = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if ?zout = [] \<and> ?as1 \<noteq> [] then Some (g, deval j ts ?dbL \<rho>Ld) else None)"
  have lrel: "rel_option (\<lambda>(k, us, \<sigma>) (k', us', \<sigma>'). k' = k \<and> us' = map (dtabc ks cs) us \<and> R \<sigma> \<sigma>')
      lrk lrd"
  proof (cases "lv \<noteq> None \<and> ?zout = [] \<and> ?as1 \<noteq> []")
    case True
    then obtain g where lv: "lv = Some g"
      by auto
    have simL: "dsim n ks cs tw \<rho>Ld \<rho>L"
      using DsFrz.hyps(12) True by blast
    have szl: "size \<rho>L < NN"
      by (rule order.strict_trans2[OF _ le]) simp
    have hin: "hd ?as1 \<in> set ?as1"
      by (rule hd_in_set) (use True in blast)
    have hdt: "ftable [0..<m] (hd ?as1)"
      using tas1 hin unfolding list_all_iff by blast
    have wL: "wf_db ?dbL"
      by (rule wf_db_update'[OF w]) (use hdt in \<open>simp add: list_all_iff\<close>)
    obtain us \<chi> where eL: "meval j n ts ?dbL \<rho>L = (us, \<chi>)"
      by (cases "meval j n ts ?dbL \<rho>L")
    obtain dus where dL: "deval j ts ?dbL \<rho>Ld = (map (dtabc ks cs) us, dus)"
      and sL: "dsim n ks cs (dnext tw ts) dus \<chi>"
      using Q[OF szl simL wL sts mts eL] by blast
    have "size \<chi> = size \<rho>"
      using default_maux.size_snd_meval[of j n ts ?dbL \<rho>L] eL szL by simp
    moreover have "size dus = size \<rho>d"
      using size_snd_deval[of j ts ?dbL \<rho>Ld] dL szLd by simp
    ultimately show ?thesis
      using True lv eL dL sL by (simp add: lrk_def lrd_def R_def)
  next
    case False
    then show ?thesis
      by (auto simp: lrk_def lrd_def split: option.splits)
  qed
  let ?k = "min (jfrz + length ?zout) (pR + length rs) - (pR - length rb)"
  let ?tq1 = "if d = \<infinity> then [] else tq @ ts"
  let ?s = "(\<rho>2, wv, pR + length rs, ?tq1, drop ?k (rb @ rs))"
  let ?sd = "(\<rho>d2, wv, pR + length rs, ?tq1, drop ?k (map (dtabc ks cs) rb @ map (dtabc ks cs) rs))"
  obtain ys as' lvk \<rho>3 w3 pR3 tq3 rb3 where e3: "frz_live_loop size (meval j n) (p, m) ?dbe ?F d po j
      (jfrz + length ?zout) ?as1 lrk ?s = (ys, as', lvk, \<rho>3, w3, pR3, tq3, rb3)"
    by (metis prod_cases4 prod_cases5)
  obtain dys das' lvd sd3 where d3: "frz_live_loop size (deval j) (p, m) ?dbe ?F d po j
      (jfrz + length ?zout) ?as1 lrd ?sd = (dys, das', lvd, sd3)"
    by (metis prod_cases4)
  have d3': "frz_live_loop size (deval j) (p, m) ?dbe (id ?F) d po j
      (jfrz + length ?zout) (map id ?as1) lrd ?sd = (dys, das', lvd, sd3)"
    using d3 by simp
  have st0: "frz_st_rel R (dtabc ks cs) ?s ?sd"
    using s4 sz\<rho>2 sz\<rho>d2 by (simp add: R_def drop_map flip: map_append)
  have frel: "dys = map (dtabc ks cs) ys \<and> das' = map id as' \<and>
      rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lvk lvd \<and>
      frz_st_rel R (dtabc ks cs) (\<rho>3, w3, pR3, tq3, rb3) sd3"
    by (rule frz_live_loop_rel[OF _ _ st0 lrel e3 d3']) (simp add: agree, simp add: R_def)
  have sub: "set as' \<subseteq> set ?as1"
    using frz_live_loop_inv[where P = "\<lambda>_. True" and T = "\<lambda>_. True", OF _ _ _ e3] by (simp add: list_all_iff)
  have tas': "list_all (ftable [0..<m]) as'"
    using sub tas1 by (auto simp: list_all_iff)
  obtain \<rho>d3 where sd3: "sd3 = (\<rho>d3, w3, pR3, tq3, map (dtabc ks cs) rb3)" and R3: "R \<rho>3 \<rho>d3"
    using frel by (cases sd3) auto
  let ?lvk = "if po then None else lvk"
  let ?lvd = "if po then None else lvd"
  have keep: "frz_keep_lv ?lvd \<rho>Ld = frz_keep_lv ?lvk \<rho>L"
    "frz_keep_lv ?lvk \<rho>L \<noteq> None \<longrightarrow> dsim n ks cs (dnext tw ts) (frz_keep_st ?lvd \<rho>Ld) (frz_keep_st ?lvk \<rho>L)"
    using frel szL szLd
    by (cases po; cases lvk; cases lvd; auto simp: frz_keep_lv_def frz_keep_st_def R_def)+
  \<comment> \<open>the two runs agree, component by component\<close>
  let ?jfrz1 = "jfrz + length ?zout + length ys"
  have stk: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s0 = \<alpha>s @ map (reorder [0..<m] kks) as0;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) \<alpha>s0
     in (zs0_out, jfrz + length zs0_out, frz_fill ng \<alpha>s0, \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, meval j n ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (?zout, jfrz + length ?zout, ?F, ?as1, lrk)"
    by (simp only: Let_def lrk_def)
  have std: "(let zs0_out = drop (jfrz - jpsi0) (map (dtabc ks cs) zs0);
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ ?as)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ ?as), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, deval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>Ld)
         else None)) = (map (dtabc ks cs) ?zout, jfrz + length ?zout, ?F, ?as1, lrd)"
    by (simp only: Let_def lrd_def drop_map length_map map_is_Nil_conv)
  have mq: "meval j n ts db (mformula.MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> wv pR tq rb d po ng lv \<rho>L) =
      (?zout @ ys, mformula.MFrz p m kks \<phi>2 \<psi>2 (jfrz + length ?zout + length ys) (jpsi0 + length zs0)
        (jphi + length as0) as' \<rho>3 w3 pR3 tq3 rb3 d po ng (frz_keep_lv ?lvk \<rho>L) (frz_keep_st ?lvk \<rho>L))"
    by (simp only: default_maux.meval.simps e1 e2 e4 stk e3 Let_def[where s = "Mapping.update (p, m) [] db"]
        Let_def[where s = "(as0, \<phi>2)"] Let_def[where s = "(zs0, \<psi>2)"] Let_def[where s = "(rs, \<rho>2)"]
        Let_def[where s = "(?zout, jfrz + length ?zout, ?F, ?as1, lrk)"]
        Let_def[where s = "(ys, as', lvk, \<rho>3, w3, pR3, tq3, rb3)"] prod.case)
  have x: "xs = ?zout @ ys"
    and f: "\<phi>' = mformula.MFrz p m kks \<phi>2 \<psi>2 ?jfrz1 (jpsi0 + length zs0) (jphi + length as0) as'
        \<rho>3 w3 pR3 tq3 rb3 d po ng (frz_keep_lv ?lvk \<rho>L) (frz_keep_st ?lvk \<rho>L)"
    using mv unfolding mq by simp_all
  have dq: "deval j ts db (DFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s \<rho>d wv pR tq (map (dtabc ks cs) rb) d po ng lv \<rho>Ld) =
      (map (dtabc ks cs) ?zout @ dys, DFrz p m \<phi>d2 \<psi>d2 (jfrz + length ?zout + length dys) (jpsi0 + length zs0)
        (jphi + length as0) das' \<rho>d3 w3 pR3 tq3 (map (dtabc ks cs) rb3) d po ng
        (frz_keep_lv ?lvd \<rho>Ld) (frz_keep_st ?lvd \<rho>Ld))"
    by (simp only: deval.simps d1 d2 d4 std length_map d3[unfolded sd3]
        Let_def[where s = "Mapping.update (p, m) [] db"]
        Let_def[where s = "(?as, \<phi>d2)"] Let_def[where s = "(map (dtabc ks cs) zs0, \<psi>d2)"]
        Let_def[where s = "(map (dtabc ks cs) rs, \<rho>d2)"]
        Let_def[where s = "(map (dtabc ks cs) ?zout, jfrz + length ?zout, ?F, ?as1, lrd)"]
        Let_def[where s = "(dys, das', lvd, \<rho>d3, w3, pR3, tq3, map (dtabc ks cs) rb3)"] prod.case)
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s \<rho>d wv pR tq (map (dtabc ks cs) rb) d po ng lv \<rho>Ld)
        = (map (dtabc ks cs) xs, DFrz p m \<phi>d2 \<psi>d2 ?jfrz1 (jpsi0 + length zs0) (jphi + length as0) as'
            \<rho>d3 w3 pR3 tq3 (map (dtabc ks cs) rb3) d po ng (frz_keep_lv ?lvk \<rho>L) (frz_keep_st ?lvd \<rho>Ld))"
      unfolding dq x using frel keep(1) by simp
    show "dsim n ks cs (dnext tw ts) (DFrz p m \<phi>d2 \<psi>d2 ?jfrz1 (jpsi0 + length zs0) (jphi + length as0) as'
            \<rho>d3 w3 pR3 tq3 (map (dtabc ks cs) rb3) d po ng (frz_keep_lv ?lvk \<rho>L) (frz_keep_st ?lvd \<rho>Ld)) \<phi>'"
      unfolding f
      by (rule dsim.DsFrz[OF wf produces_next[OF pr w sts mts mv, unfolded f] s1 s2 tas'])
        (use R3 szL szLd keep(2) in \<open>simp_all add: R_def\<close>)
  qed
next
  case (DsLetPast ks cs n tw p m kks \<phi> \<psi> i buf \<phi>d \<psi>d)
  note wf = DsLetPast.hyps(1) and pr = DsLetPast.hyps(2) and sim1 = DsLetPast.hyps(3)
    and IH1 = DsLetPast.hyps(4) and sim2 = DsLetPast.hyps(5) and IH2 = DsLetPast.hyps(6)
    and lbo = DsLetPast.hyps(7)
    and w = DsLetPast.prems(1) and sts = DsLetPast.prems(2)
    and mts = DsLetPast.prems(3) and mv = DsLetPast.prems(4) and le = DsLetPast.prems(5)
  have sz2: "size \<psi> \<le> NN" by (rule order_trans[OF _ le]) simp
  have szs: "size \<phi> < NN" by (rule order.strict_trans2[OF _ le]) simp
  have lbl: "list_all (ftable [0..<m]) (list_of_option buf)" using lbo by (cases buf) auto
  \<comment> \<open>the rounds of the bound formula\<close>
  obtain as i2 buf2 \<phi>2 where e1: "letpast_meval m kks j i [] (list_of_option buf) (p, m) ts db \<phi>
      = (as, i2, buf2, \<phi>2)"
    by (cases "letpast_meval m kks j i [] (list_of_option buf) (p, m) ts db \<phi>") auto
  have e1': "letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>))
      j i [] (list_of_option buf) (p, m) ts db \<phi> = (as, i2, buf2, \<phi>2)"
    using e1 by (simp add: default_maux.letpast_meval_def)
  have lnil: "list_all (ftable [0..<m]) []" by simp
  have lr: "list_all (ftable [0..<m]) as \<and> (\<forall>y. buf2 = Some y \<longrightarrow> ftable [0..<m] y) \<and>
      (\<exists>\<phi>d'. letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi>d
        = (as, i2, buf2, \<phi>d') \<and> dsim m kks [0..<m] (dnext tw ts) \<phi>d' \<phi>2)"
    by (rule letpast_meval0_rel[OF _ e1' snd_conv szs sim1 w sts mts lnil lbl]) (rule Q)
  have ta: "list_all (ftable [0..<m]) as" using lr by simp
  have lbo2: "\<forall>y. buf2 = Some y \<longrightarrow> ftable [0..<m] y" using lr by simp
  obtain \<phi>d2 where d1: "letpast_meval0 (deval j) j i [] (list_of_option buf) (p, m) ts db \<phi>d
        = (as, i2, buf2, \<phi>d2)"
    and s1: "dsim m kks [0..<m] (dnext tw ts) \<phi>d2 \<phi>2" using lr by blast
  \<comment> \<open>the body, against the database in which the bound predicate holds the rounds' output\<close>
  have w2: "wf_db (Mapping.update (p, m) as db)"
    by (rule wf_db_update'[OF w]) (use ta in \<open>simp add: list_all_iff\<close>)
  obtain bs \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) as db) \<psi> = (bs, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) as db) \<psi>")
  obtain \<psi>d2 where d2: "deval j ts (Mapping.update (p, m) as db) \<psi>d = (map (dtabc ks cs) bs, \<psi>d2)"
    and s2: "dsim n ks cs (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w2 sts mts e2 sz2] by blast
  have x: "xs = bs" and f: "\<phi>' = mformula.MLetPast p m kks \<phi>2 \<psi>2 i2 buf2"
    using mv e1 e2 by simp_all
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DLetPast p m \<phi>d \<psi>d i buf)
        = (map (dtabc ks cs) xs, DLetPast p m \<phi>d2 \<psi>d2 i2 buf2)"
      using d1 d2 unfolding x by simp
    show "dsim n ks cs (dnext tw ts) (DLetPast p m \<phi>d2 \<psi>d2 i2 buf2) \<phi>'"
      unfolding f
      by (rule dsim.DsLetPast[OF wf produces_next[OF pr w sts mts mv, unfolded f] s1 s2 lbo2])
  qed
next
  case (DsTrigger kR cR n tw args \<phi> \<psi> buf nts aux kL cL \<phi>d \<psi>d dags pl daux dbuf)
  note wf = DsTrigger.hyps(1) and pr = DsTrigger.hyps(2)
    and sim1 = DsTrigger.hyps(3) and IH1 = DsTrigger.hyps(4)
    and sim2 = DsTrigger.hyps(5) and IH2 = DsTrigger.hyps(6)
    and sub = DsTrigger.hyps(7) and aL = DsTrigger.hyps(8) and aR = DsTrigger.hyps(9)
    and m0 = DsTrigger.hyps(10) and dag = DsTrigger.hyps(11) and pe = DsTrigger.hyps(12)
    and rel = DsTrigger.hyps(13)
    and w = DsTrigger.prems(1) and sts = DsTrigger.prems(2)
    and mts = DsTrigger.prems(3) and m = DsTrigger.prems(4)
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
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) as, \<phi>d2)"
    and s1: "dsim n kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) bs, \<psi>d2)"
    and s2: "dsim n kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have ta: "list_all (ftable kL) as"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) bs"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dzs daux2 dbuf2 dnts2 where d3: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) (nts @ ts)
      = ((dzs, daux2), dbuf2, dnts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
      (mbuf2_add (map (dtabc kL cL) as) (map (dtabc kR cR) bs) dbuf) (nts @ ts)") auto
  have step: "dzs = map (dtabc kR cR) zs \<and> dnts2 = nts2 \<and>
      dtrigger_rel kR cR kL cL args (dnext tw ts) aux2 daux2 buf2 dbuf2 nts2"
    by (rule dtrigger_step_rel[OF wf fL sub aL aR m0 rel ta tb sts mts e3 d3[unfolded dag]])
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DTrigger dags pl \<phi>d \<psi>d dbuf nts daux)
        = (map (dtabc kR cR) xs, DTrigger dags pl \<phi>d2 \<psi>d2 dbuf2 nts2 daux2)"
      using d1 d2 d3 step x by simp
    show "dsim n kR cR (dnext tw ts) (DTrigger dags pl \<phi>d2 \<psi>d2 dbuf2 nts2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsTrigger[OF wf produces_next[OF pr w sts mts m, unfolded f] s1 s2 sub
            aL aR m0 dag pe]) (use step in simp)
  qed
next
  case (DsAndTrigger ks cs n tw \<alpha> buf1 args \<phi> \<psi> buf2 nts aux \<alpha>d kL cL \<phi>d kR cR \<psi>d dags pl dbf1
      daux dbf2)
  note wf = DsAndTrigger.hyps(1) and pr = DsAndTrigger.hyps(2)
    and sim0 = DsAndTrigger.hyps(3) and IH0 = DsAndTrigger.hyps(4)
    and sim1 = DsAndTrigger.hyps(5) and IH1 = DsAndTrigger.hyps(6)
    and sim2 = DsAndTrigger.hyps(7) and IH2 = DsAndTrigger.hyps(8)
    and subLR = DsAndTrigger.hyps(9) and subR = DsAndTrigger.hyps(10)
    and aL = DsAndTrigger.hyps(11) and aR = DsAndTrigger.hyps(12) and ok = DsAndTrigger.hyps(13)
    and dag = DsAndTrigger.hyps(14) and ple = DsAndTrigger.hyps(15)
    and bf1 = DsAndTrigger.hyps(16) and rel = DsAndTrigger.hyps(17)
    and w = DsAndTrigger.prems(1) and sts = DsAndTrigger.prems(2)
    and mts = DsAndTrigger.prems(3) and m = DsAndTrigger.prems(4)
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
  obtain zs buf1' where e4: "mbuf2_take (\<lambda>r1 (V, r2). bin_join ks r1 True V r2)
      (mbuf2_add as ws buf1) = (zs, buf1')"
    by (cases "mbuf2_take (\<lambda>r1 (V, r2). bin_join ks r1 True V r2)
      (mbuf2_add as ws buf1)") auto
  have x: "xs = zs"
    and f: "\<phi>' = mformula.MAndTrigger ks \<alpha>2 buf1' args \<phi>2 \<psi>2 buf2' nts2 aux2"
    using m e0 e1 e2 e3 e4 by (simp_all del: bin_join.simps)
  have sz0: "size \<alpha> \<le> NN" and sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ DsAndTrigger.prems(5)], simp)+
  obtain \<alpha>d2 where d0: "deval j ts db \<alpha>d = (map (dtabc ks cs) as, \<alpha>d2)"
    and s0: "dsim n ks cs (dnext tw ts) \<alpha>d2 \<alpha>2" using IH0[OF w sts mts e0 sz0] by blast
  obtain \<phi>d2 where d1: "deval j ts db \<phi>d = (map (dtabc kL cL) xs1, \<phi>d2)"
    and s1: "dsim n kL cL (dnext tw ts) \<phi>d2 \<phi>2" using IH1[OF w sts mts e1 sz1] by blast
  obtain \<psi>d2 where d2: "deval j ts db \<psi>d = (map (dtabc kR cR) ys1, \<psi>d2)"
    and s2: "dsim n kR cR (dnext tw ts) \<psi>d2 \<psi>2" using IH2[OF w sts mts e2 sz2] by blast
  have fL: "dframe kL cL" by (rule dsim_dframe[OF sim1])
  have fR: "dframe kR cR" by (rule dsim_dframe[OF sim2])
  have t0: "list_all (ftable ks) as"
    by (rule produces_tables[OF dsim_produces[OF sim0] w sts mts e0])
  have ta: "list_all (ftable kL) xs1"
    by (rule produces_tables[OF dsim_produces[OF sim1] w sts mts e1])
  have tb: "list_all (ftable kR) ys1"
    by (rule produces_tables[OF dsim_produces[OF sim2] w sts mts e2])
  obtain dws daux2 dbf2' dnts2 where d3: "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
      ([], daux) (mbuf2_add (map (dtabc kL cL) xs1) (map (dtabc kR cR) ys1) dbf2) (nts @ ts)
      = ((dws, daux2), dbf2', dnts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
      ([], daux) (mbuf2_add (map (dtabc kL cL) xs1) (map (dtabc kR cR) ys1) dbf2)
      (nts @ ts)") auto
  have step: "list_all2 (dtres kR cR) ws dws \<and> dnts2 = nts2 \<and>
      dtrigger_rel kR cR kL cL args (dnext tw ts) aux2 daux2 buf2' dbf2' nts2"
    by (rule dandtrigger_step_rel[OF fR fL subLR aL aR ok rel ta tb sts mts e3 d3[unfolded dag]])
  have badd: "dandbuf ks cs kR cR (mbuf2_add as ws buf1)
      (mbuf2_add (map (dtabc ks cs) as) dws dbf1)"
    by (rule dandbuf_add[OF bf1 t0]) (use step in simp)
  obtain dbf1' where d4: "mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> dbin_join pl r1 True z) (mbuf2_add (map (dtabc ks cs) as) dws dbf1)
      = (map (dtabc ks cs) zs, dbf1')"
    and bf1': "dandbuf ks cs kR cR buf1' dbf1'"
    using dandbuf_take[OF wf fR subR badd e4] unfolding ple by blast
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DAndTrigger pl \<alpha>d dbf1 dags \<phi>d \<psi>d dbf2 nts daux)
        = (map (dtabc ks cs) xs, DAndTrigger pl \<alpha>d2 dbf1' dags \<phi>d2 \<psi>d2 dbf2' nts2 daux2)"
      using d0 d1 d2 d3 d4 step x by simp
    show "dsim n ks cs (dnext tw ts) (DAndTrigger pl \<alpha>d2 dbf1' dags \<phi>d2 \<psi>d2 dbf2' nts2 daux2) \<phi>'"
      unfolding f
      by (rule dsim.DsAndTrigger[OF wf produces_next[OF pr w sts mts m, unfolded f] s0 s1 s2
            subLR subR aL aR ok dag ple bf1']) (use step in simp)
  qed
next
  case (DsMatchP ks cs n tw I dss mr mrs L buf nts aux \<psi>s css Ld pls dbuf daux)
  note wf = DsMatchP.hyps(1) and pr = DsMatchP.hyps(2) and sr = DsMatchP.hyps(3)
    and okm = DsMatchP.hyps(4) and fvA = DsMatchP.hyps(5) and dm = DsMatchP.hyps(6)
    and mrsd = DsMatchP.hyps(7) and dsse = DsMatchP.hyps(8) and lcs = DsMatchP.hyps(9)
    and lL = DsMatchP.hyps(10) and lLd = DsMatchP.hyps(11) and fas = DsMatchP.hyps(12)
    and csub = DsMatchP.hyps(13) and la = DsMatchP.hyps(14) and pe = DsMatchP.hyps(15)
    and bf = DsMatchP.hyps(16) and rel = DsMatchP.hyps(17)
    and w = DsMatchP.prems(1) and sts = DsMatchP.prems(2)
    and mts = DsMatchP.prems(3) and m = DsMatchP.prems(4)
  let ?R = "map (meval j n ts db) L"
  let ?dR = "map (deval j ts db) Ld"
  let ?F = "\<lambda>rels t (zs, ax).
      let (z, ax) = update_matchP ks dss I mr mrs rels t ax in (zs @ [z], ax)"
  let ?G = "\<lambda>rels t (zs, ax).
      let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
      in (zs @ [z], ax)"
  obtain zs aux2 buf2 tt2 nts2 where g0:
    "mbufnt_take ?F ([], aux) (mbufn_add (map fst ?R) buf) 0 (nts @ ts)
       = ((zs, aux2), buf2, tt2, nts2)"
    by (cases "mbufnt_take ?F ([], aux) (mbufn_add (map fst ?R) buf) 0 (nts @ ts)") auto
  have x: "xs = zs" and fe: "\<phi>' = mformula.MMatchP I ks dss mr mrs (map snd ?R) buf2 nts2 aux2"
    using m g0 by (simp_all add: Let_def map_split_alt del: mbufnt_take.simps)
  \<comment> \<open>the operands, and their reordering\<close>
  have la0: "\<forall>i < length L. dsim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i)" using la by blast
  have lcL: "length css = length L" using lcs lL by simp
  have ldL: "length dss = length L" using dsse lL by simp
  have tabs: "\<forall>i < length css. list_all (ftable (dss ! i)) (map fst ?R ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length css"
    then have iL: "i < length L" using lcL by simp
    have "list_all (ftable (dss ! i)) (fst (meval j n ts db (L ! i)))"
      by (rule dsims_tables[OF la0 w sts mts iL])
    then show "list_all (ftable (dss ! i)) (map fst ?R ! i)" using iL by simp
  qed
  have szL: "\<And>i. i < length L \<Longrightarrow> size (L ! i) \<le> NN"
  proof -
    fix i assume i: "i < length L"
    have "size (L ! i) \<le> size_list size L"
      by (rule size_list_estimation'[OF nth_mem[OF i] order.refl])
    also have "size_list size L \<le> NN" by (rule order_trans[OF _ DsMatchP.prems(5)]) simp
    finally show "size (L ! i) \<le> NN" .
  qed
  have la1: "\<forall>i < length L. dsim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc (dss ! i) (css ! i)) as, \<psi>d')
            \<and> dsim n (dss ! i) (css ! i) (dnext tw ts) \<psi>d' \<psi>'))"
    using la w sts mts szL by blast
  have dlr: "length ?dR = length L \<and>
      map fst ?dR = map2 map (map2 dtabc dss css) (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (dss ! i) (css ! i) (dnext tw ts) (map snd ?dR ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF lLd lcL ldL la1])
  have dl: "map fst ?dR = map2 map (map2 dtabc dss css) (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (dss ! i) (css ! i) (dnext tw ts) (map snd ?dR ! i)
      (snd (meval j n ts db (L ! i)))" using dlr by blast
  \<comment> \<open>the buffer\<close>
  have badd: "dbufn dss css (mbufn_add (map fst ?R) buf) (mbufn_add (map fst ?dR) dbuf)"
    unfolding dl by (rule dbufn_add[OF bf _ tabs]) (use lcL in simp)
  \<comment> \<open>the masks the window probes with\<close>
  have msk: "map emb_msk pls = map (dmsk cs) css"
    unfolding pe map_map o_def
  proof (rule map_cong[OF refl])
    fix c assume c: "c \<in> set css"
    then obtain i where i: "i < length css" and ci: "c = css ! i" by (auto simp: in_set_conv_nth)
    have fi: "dframe (dss ! i) (css ! i)" using fas i lcs by simp
    show "emb_msk (emb_plan cs c) = dmsk cs c"
    proof (rule emb_msk_emb_plan)
      show "sorted_wrt (<) cs" by (rule dframeD(2)[OF wf])
      show "sorted_wrt (<) c" using dframeD(2)[OF fi] ci by simp
      show "set c \<subseteq> set cs" using csub i ci lcs dframeD(3)[OF fi] dframeD(3)[OF wf] dsse
        by simp
    qed
  qed
  \<comment> \<open>one firing of the window\<close>
  define Rel where "Rel = (\<lambda>(zs :: event_data table list, ax) (dzs :: event_data table list, dax).
      dzs = map (dtabc ks cs) zs \<and> dmrd_rel ks cs ax dax)"
  have step: "Rel (?F as t u) (?G (dtabcs dss css as) t u')"
    if las: "length as = length css"
      and mas: "\<forall>i < length css. ftable (dss ! i) (as ! i)"
      and ru: "Rel u u'" for as u u' t
  proof -
    obtain zs0 ax where u: "u = (zs0, ax)" by (cases u)
    obtain dzs0 dax where u': "u' = (dzs0, dax)" by (cases u')
    have dz: "dzs0 = map (dtabc ks cs) zs0" and rax: "dmrd_rel ks cs ax dax"
      using ru by (simp_all add: Rel_def u u')
    interpret dmatchP_frame ks cs \<psi>s css as mrs
    proof
      show "dframe ks cs" by (rule wf)
      show "length css = length \<psi>s" by (rule lcs)
      show "\<And>i. i < length \<psi>s \<Longrightarrow> dframe (Formula.fv_list (\<psi>s ! i)) (css ! i)"
        using fas dsse by simp
      show "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set ks" using csub by simp
      show "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel) \<psi>s as"
        using las lcs dsse mas by (fastforce simp: list_all2_conv_all_nth)
      show "distinct mrs" by (rule dm)
      show "\<And>ms. ms \<in> set mrs \<Longrightarrow>
          Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<psi>s) \<and>
          ok (length \<psi>s) ms \<and> set ks = fv_regex (from_mregex ms \<psi>s)"
        using mrsd sr okm fvA
        by (auto simp: RPDs_safe RPDs_ok RPDs_safe_fv_regex)
    qed
    have uu: "dtabc ks cs (fst (update_matchP ks dss I mr mrs as t ax))
        = fst (gupdate_matchP (map (dmsk cs) css) I mr mrs (dtabcs dss css as) t dax) \<and>
      dmrd_rel ks cs (snd (update_matchP ks dss I mr mrs as t ax))
        (snd (gupdate_matchP (map (dmsk cs) css) I mr mrs (dtabcs dss css as) t dax))"
      using dtabc_gupdate_matchP[OF rax] unfolding dsse .
    show ?thesis using dz uu by (simp add: Rel_def u u' msk Let_def split_beta)
  qed
  have rz: "Rel ([], aux) ([], daux)" using rel by (simp add: Rel_def)
  obtain w2 dbuf2 where dt:
    "mbufnt_take ?G ([], daux) (mbufn_add (map fst ?dR) dbuf) 0 (nts @ ts)
       = (w2, dbuf2, tt2, nts2)"
    and rw: "Rel (zs, aux2) w2" and bf2: "dbufn dss css buf2 dbuf2"
    using dbufn_nt_take[where R = Rel and f = "?F" and g = "?G", OF badd step rz g0] by blast
  obtain dzs daux2 where w2: "w2 = (dzs, daux2)" by (cases w2)
  have dzs: "dzs = map (dtabc ks cs) zs" and rel2: "dmrd_rel ks cs aux2 daux2"
    using rw by (simp_all add: Rel_def w2)
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DMatchP (length cs) I mr mrs pls Ld dbuf nts daux)
        = (map (dtabc ks cs) xs, DMatchP (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 daux2)"
      using dt x dzs unfolding w2 by (simp add: Let_def del: mbufnt_take.simps)
    show "dsim n ks cs (dnext tw ts) (DMatchP (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 daux2)
        \<phi>'"
      unfolding fe
      by (rule dsim.DsMatchP[OF wf produces_next[OF pr w sts mts m, unfolded fe] sr okm fvA dm
            mrsd dsse lcs _ _ fas csub _ pe bf2 rel2])
        (use lL lLd dl2 dlr in auto)
  qed
next
  case (DsMatchF ks cs n tw I dss mr mrs L buf nts t aux \<psi>s css Ld pls dbuf daux)
  note wf = DsMatchF.hyps(1) and pr = DsMatchF.hyps(2) and sr = DsMatchF.hyps(3)
    and okm = DsMatchF.hyps(4) and fvA = DsMatchF.hyps(5) and dm = DsMatchF.hyps(6)
    and mrsd = DsMatchF.hyps(7) and dsse = DsMatchF.hyps(8) and lcs = DsMatchF.hyps(9)
    and lL = DsMatchF.hyps(10) and lLd = DsMatchF.hyps(11) and fas = DsMatchF.hyps(12)
    and csub = DsMatchF.hyps(13) and la = DsMatchF.hyps(14) and pe = DsMatchF.hyps(15)
    and bf = DsMatchF.hyps(16) and rel = DsMatchF.hyps(17)
    and w = DsMatchF.prems(1) and sts = DsMatchF.prems(2)
    and mts = DsMatchF.prems(3) and m = DsMatchF.prems(4)
  let ?R = "map (meval j n ts db) L"
  let ?dR = "map (deval j ts db) Ld"
  let ?F = "update_matchF ks dss I mr mrs"
  let ?G = "\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels"
  obtain aux2 buf2 nt2 nts2 where g0:
    "mbufnt_take ?F aux (mbufn_add (map fst ?R) buf) t (nts @ ts) = (aux2, buf2, nt2, nts2)"
    by (cases "mbufnt_take ?F aux (mbufn_add (map fst ?R) buf) t (nts @ ts)") auto
  obtain zs aux3 where g1: "eval_matchF I mr nt2 aux2 = (zs, aux3)"
    by (cases "eval_matchF I mr nt2 aux2") auto
  have x: "xs = zs" and fe: "\<phi>' = mformula.MMatchF I ks dss mr mrs (map snd ?R) buf2 nts2 nt2 aux3"
    using m g0 g1 by (simp_all add: Let_def map_split_alt del: mbufnt_take.simps)
  \<comment> \<open>the operands, and their reordering\<close>
  have la0: "\<forall>i < length L. dsim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i)" using la by blast
  have lcL: "length css = length L" using lcs lL by simp
  have ldL: "length dss = length L" using dsse lL by simp
  have tabs: "\<forall>i < length css. list_all (ftable (dss ! i)) (map fst ?R ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length css"
    then have iL: "i < length L" using lcL by simp
    have "list_all (ftable (dss ! i)) (fst (meval j n ts db (L ! i)))"
      by (rule dsims_tables[OF la0 w sts mts iL])
    then show "list_all (ftable (dss ! i)) (map fst ?R ! i)" using iL by simp
  qed
  have szL: "\<And>i. i < length L \<Longrightarrow> size (L ! i) \<le> NN"
  proof -
    fix i assume i: "i < length L"
    have "size (L ! i) \<le> size_list size L"
      by (rule size_list_estimation'[OF nth_mem[OF i] order.refl])
    also have "size_list size L \<le> NN" by (rule order_trans[OF _ DsMatchF.prems(5)]) simp
    finally show "size (L ! i) \<le> NN" .
  qed
  have la1: "\<forall>i < length L. dsim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. deval j ts db (Ld ! i) = (map (dtabc (dss ! i) (css ! i)) as, \<psi>d')
            \<and> dsim n (dss ! i) (css ! i) (dnext tw ts) \<psi>d' \<psi>'))"
    using la w sts mts szL by blast
  have dlr: "length ?dR = length L \<and>
      map fst ?dR = map2 map (map2 dtabc dss css) (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. dsim n (dss ! i) (css ! i) (dnext tw ts) (map snd ?dR ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule deval_list_rel[OF lLd lcL ldL la1])
  have dl: "map fst ?dR = map2 map (map2 dtabc dss css) (map fst ?R)"
    using dlr by (simp add: comp_def)
  have dl2: "\<forall>i < length L. dsim n (dss ! i) (css ! i) (dnext tw ts) (map snd ?dR ! i)
      (snd (meval j n ts db (L ! i)))" using dlr by blast
  \<comment> \<open>the buffer\<close>
  have badd: "dbufn dss css (mbufn_add (map fst ?R) buf) (mbufn_add (map fst ?dR) dbuf)"
    unfolding dl by (rule dbufn_add[OF bf _ tabs]) (use lcL in simp)
  \<comment> \<open>one firing of the window\<close>
  interpret dmatchF_frame ks cs \<psi>s css mrs
  proof
    show "dframe ks cs" by (rule wf)
    show "length css = length \<psi>s" by (rule lcs)
    show "\<And>i. i < length \<psi>s \<Longrightarrow> dframe (Formula.fv_list (\<psi>s ! i)) (css ! i)"
      using fas dsse by simp
    show "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set ks" using csub by simp
    show "distinct mrs" by (rule dm)
    show "\<And>ms. ms \<in> set mrs \<Longrightarrow>
        Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<psi>s) \<and>
        ok (length \<psi>s) ms \<and> set ks = fv_regex (from_mregex ms \<psi>s)"
      using mrsd sr okm fvA by (auto simp: LPDs_safe LPDs_ok LPDs_safe_fv_regex)
  qed
  have msk: "map emb_msk pls = map (dmsk cs) css"
    unfolding pe map_map o_def
  proof (rule map_cong[OF refl])
    fix c assume c: "c \<in> set css"
    then obtain i where i: "i < length css" and ci: "c = css ! i" by (auto simp: in_set_conv_nth)
    have fi: "dframe (dss ! i) (css ! i)" using fas i lcs by simp
    show "emb_msk (emb_plan cs c) = dmsk cs c"
    proof (rule emb_msk_emb_plan)
      show "sorted_wrt (<) cs" by (rule dframeD(2)[OF wf])
      show "sorted_wrt (<) c" using dframeD(2)[OF fi] ci by simp
      show "set c \<subseteq> set cs" using csub i ci lcs dframeD(3)[OF fi] dframeD(3)[OF wf] dsse
        by simp
    qed
  qed
  have step: "dmld_rel ks cs \<psi>s css (?F as tt u) (?G (dtabcs dss css as) tt u')"
    if las: "length as = length css"
      and mas: "\<forall>i < length css. ftable (dss ! i) (as ! i)"
      and ru: "dmld_rel ks cs \<psi>s css u u'" for as u u' tt
  proof -
    have wfr: "list_all2 (\<lambda>\<psi> rl. table (Formula.fv_list \<psi>) rl) \<psi>s as"
      using las lcs dsse mas by (fastforce simp: list_all2_conv_all_nth)
    show ?thesis using dtabc_gupdate_matchF[OF wfr ru] unfolding dsse by (simp add: msk)
  qed
  obtain daux2 dbuf2 where dt:
    "mbufnt_take ?G daux (mbufn_add (map fst ?dR) dbuf) t (nts @ ts) = (daux2, dbuf2, nt2, nts2)"
    and rw: "dmld_rel ks cs \<psi>s css aux2 daux2" and bf2: "dbufn dss css buf2 dbuf2"
    using dbufn_nt_take[where R = "dmld_rel ks cs \<psi>s css" and f = "?F" and g = "?G",
        OF badd step rel g0] by blast
  obtain dzs daux3 where g2: "geval_matchF I mr nt2 daux2 = (dzs, daux3)"
    by (cases "geval_matchF I mr nt2 daux2") auto
  have evb: "fst (geval_matchF I mr nt2 daux2) = map (dtabc ks cs) (fst (eval_matchF I mr nt2 aux2))
      \<and> dmld_rel ks cs \<psi>s css (snd (eval_matchF I mr nt2 aux2)) (snd (geval_matchF I mr nt2 daux2))"
    by (rule dtabc_geval_matchF[OF rw])
  have ev: "dzs = map (dtabc ks cs) zs" using evb g1 g2 by simp
  have rel3: "dmld_rel ks cs \<psi>s css aux3 daux3" using evb g1 g2 by simp
  show ?case
  proof (intro exI conjI)
    show "deval j ts db (DMatchF (length cs) I mr mrs pls Ld dbuf nts t daux)
        = (map (dtabc ks cs) xs,
           DMatchF (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 nt2 daux3)"
      using dt g2 x ev by (simp add: Let_def del: mbufnt_take.simps)
    show "dsim n ks cs (dnext tw ts)
        (DMatchF (length cs) I mr mrs pls (map snd ?dR) dbuf2 nts2 nt2 daux3) \<phi>'"
      unfolding fe
      by (rule dsim.DsMatchF[OF wf produces_next[OF pr w sts mts m, unfolded fe] sr okm fvA dm
            mrsd dsse lcs _ _ fas csub _ pe bf2 rel3])
        (use lL lLd dl2 dlr in auto)
  qed
qed

text \<open>Induction on the bound discharges the assumption the theorem above carries, and
  instantiating it at the formula's own size recovers the statement without it.\<close>

lemma dsim_deval_bound:
  "size \<phi> \<le> NN \<Longrightarrow> dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc ks cs) xs, \<phi>d')
     \<and> dsim n ks cs (dnext tw ts) \<phi>d' \<phi>'"
proof (induct NN arbitrary: n ks cs tw \<phi>d \<phi> j ts db xs \<phi>' rule: less_induct)
  case (less NN)
  show ?case
    by (rule dsim_deval_N[OF _ less(3) less(4) less(5) less(6) less(7) less(2)])
      (use less(1) in blast)
qed

theorem dsim_deval:
  "dsim n ks cs tw \<phi>d \<phi> \<Longrightarrow> wf_db db \<Longrightarrow> sorted ts \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow>
   \<exists>\<phi>d'. deval j ts db \<phi>d = (map (dtabc ks cs) xs, \<phi>d')
     \<and> dsim n ks cs (dnext tw ts) \<phi>d' \<phi>'"
  by (rule dsim_deval_bound[OF order.refl])

(*<*)
end
(*>*)