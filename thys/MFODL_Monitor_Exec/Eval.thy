(*<*)
theory Eval
  imports Window_Dispatch Trigger_Window Kernel_Call
begin
(*>*)

section \<open>The executable evaluator simulates the kernel's\<close>

text \<open>
  Every theorem of @{theory MFODL_Monitor_Exec.Frame} needs its operand tables to be finite and
  well formed over the node's columns.  The simulation below takes that from the kernel: it is
  stated for the calls of @{const meval} that @{const kgood} covers, whose tables the kernel's
  correctness theorem describes (@{thm [source] kgood_tables}).
\<close>

definition enext :: "ts \<Rightarrow> ts list \<Rightarrow> ts" where
  "enext tw ts = (if ts = [] then tw else last ts)"

lemma enext_ge: "\<forall>t \<in> set ts. tw \<le> t \<Longrightarrow> tw \<le> enext tw ts"
  by (auto simp: enext_def)

lemma enext_bound: "sorted ts \<Longrightarrow> \<forall>t \<in> set ts. t \<le> enext tw ts"
proof (induct ts rule: rev_induct)
  case (snoc a ts) then show ?case by (auto simp: enext_def sorted_append)
qed (simp add: enext_def)

text \<open>
  The simulation also carries a timestamp lower bound @{term tw}: every timestamp in a batch is
  at least @{term tw}, and the relation is re-established at the bound @{term "enext tw ts"} the
  batch leaves behind.  The temporal nodes need this -- the verified Since and Until structures
  accept a new timestamp only at or after the one they are already at -- and the others carry
  it without using it.
\<close>

section \<open>The executable formula\<close>

text \<open>
  A executable formula mirrors the kernel's @{typ "('msaux, 'muaux, 'mtaux) mformula"} node by node,
  but every node carries the data the ascending representation needs instead of the data the
  kernel's needs: a join plan instead of two column lists, a term already reindexed against the
  operand's column list, a mask at the boundary.  @{term EFail} stands for a node the executable
  fragment does not cover: it evaluates to nothing and no simulation rule relates it to a kernel
  formula, so a executable formula containing one proves nothing and the compiler's caller must check
  that it produced none.  Nothing in the type mentions the kernel's formula type, which is what
  makes the executable evaluator exportable on its own.
\<close>

datatype eformula =
    EFail
  | ERel "event_data table"
  | EPredS Formula.name nat
  | EPredM Formula.name nat "Formula.trm list" cols
  | EAndRel eformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | ENeg eformula
  | EExists eformula bool
  | EAgg bool "ty Formula.agg_op" Formula.trm nat nat eformula
  | EOr eformula eformula uebuf2
  | EAnd ejoin_plan eformula bool eformula uebuf2
  | EPrev \<I> eformula bool "event_data table mbuf_t" "ts mbuf_t"
  | ENext \<I> eformula bool "ts mbuf_t"
  | EAnds "ejoin_plan list" "ejoin_plan list" "eformula list" uebufn
  | ESince args eformula eformula uebuf2S udsaux_x
  | EUntil args "bool list" eformula eformula uebuf2 "ts mbuf_t" ts uduaux_x
  | EAndAssign nat Formula.trm eformula
  | ETP mtrm nat
  | ETS mtrm
  | ELet Formula.name nat eformula eformula
  | EFrz Formula.name nat eformula eformula nat nat nat "event_data table list"
      eformula nat nat "ts list" "event_data table list" enat bool bool "nat option" eformula
  | ELetPast Formula.name nat eformula eformula nat "event_data table option"
  | ETrigger args "nat option list" eformula eformula uebuf2 "ts mbuf_t" "event_data gmmtaux"
  | EAndTrigger ejoin_plan eformula "event_data table mbuf_t \<times> event_data table option mbuf_t"
      args eformula eformula uebuf2 "ts mbuf_t" "event_data gmmtaux"
  | EMatchP nat \<I> mregex "mregex list" "nat option list list" "eformula list"
      uebufn "ts mbuf_t" "event_data mr\<delta>aux"
  | EMatchF nat \<I> mregex "mregex list" "nat option list list" "eformula list"
      uebufn "ts mbuf_t" ts "event_data ml\<delta>aux"

text \<open>The compiler is total on the kernel's formulas, so it answers @{const EFail} at a node it
  does not cover rather than failing.  Its caller checks that the compiled formula has none: this
  counts them.\<close>

fun efail_nodes :: "eformula \<Rightarrow> nat" where
  "efail_nodes EFail = 1"
| "efail_nodes (EAndRel \<phi> conf) = efail_nodes \<phi>"
| "efail_nodes (ENeg \<phi>) = efail_nodes \<phi>"
| "efail_nodes (EExists \<phi> b) = efail_nodes \<phi>"
| "efail_nodes (EAgg g0 \<omega> f k pos \<phi>) = efail_nodes \<phi>"
| "efail_nodes (EOr \<phi> \<psi> buf) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (EAnd pl \<phi> pos \<psi> buf) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (EPrev I \<phi> f buf nts) = efail_nodes \<phi>"
| "efail_nodes (ENext I \<phi> f nts) = efail_nodes \<phi>"
| "efail_nodes (EAnds ps ns L buf) = sum_list (map efail_nodes L)"
| "efail_nodes (ESince args \<phi> \<psi> buf aux) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (EUntil args msk \<phi> \<psi> buf nts t aux) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (EAndAssign p t \<phi>) = efail_nodes \<phi>"
| "efail_nodes (ELet p m \<phi> \<psi>) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
    efail_nodes \<phi> + efail_nodes \<psi> + efail_nodes \<rho>"
| "efail_nodes (ELetPast p m \<phi> \<psi> i buf) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (ETrigger dags pl \<phi> \<psi> dbuf nts daux) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (EAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> ebuf2 nts daux) =
     efail_nodes \<alpha> + efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (EMatchP m I mr mrs pls L dbuf nts daux) = sum_list (map efail_nodes L)"
| "efail_nodes (EMatchF m I mr mrs pls L dbuf nts t daux) = sum_list (map efail_nodes L)"
| "efail_nodes \<phi> = 0"

function (sequential) eeval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> eformula \<Rightarrow>
    event_data table list \<times> eformula" where
  "eeval j ts db EFail = ([], EFail)"
| "eeval j ts db (ERel rel) = (replicate (length ts) rel, ERel rel)"
| "eeval j ts db (EPredS e ar) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> xs), EPredS e ar)"
| "eeval j ts db (EPredM e ar tms cs) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> map (umatch_table tms cs) xs), EPredM e ar tms cs)"
| "eeval j ts db (EAndRel \<phi> conf) =
     (let (xs, \<phi>') = eeval j ts db \<phi>
      in (map (Set.filter (ueval_constraint conf)) xs, EAndRel \<phi>' conf))"
| "eeval j ts db (ENeg \<phi>) =
     (let (xs, \<phi>') = eeval j ts db \<phi>
      in (map (\<lambda>r. if r = {} then {[]} else {}) xs, ENeg \<phi>'))"
| "eeval j ts db (EExists \<phi> drop0) =
     (let (xs, \<phi>') = eeval j ts db \<phi>
      in (if drop0 then map (\<lambda>r. tl ` r) xs else xs, EExists \<phi>' drop0))"
| "eeval j ts db (EAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = eeval j ts db \<phi> in (map (uagg g0 \<omega> f k pos) xs, EAgg g0 \<omega> f k pos \<phi>'))"
| "eeval j ts db (EOr \<phi> \<psi> buf) =
     (let (xs, \<phi>') = eeval j ts db \<phi>; (ys, \<psi>') = eeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
      in (zs, EOr \<phi>' \<psi>' buf'))"
| "eeval j ts db (EAnd pl \<phi> pos \<psi> buf) =
     (let (xs, \<phi>') = eeval j ts db \<phi>; (ys, \<psi>') = eeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2) (mebuf2_add xs ys buf)
      in (zs, EAnd pl \<phi>' pos \<psi>' buf'))"
| "eeval j ts db (EPrev I \<phi> first buf nts) =
     (let (xs, \<phi>') = eeval j ts db \<phi>
      in if first \<and> ts = [] then ([], EPrev I \<phi>' True (buf @@ xs) (nts @@ ts))
      else let (zs, buf', nts') = meprev_next I (buf @@ xs) (nts @@ ts)
        in (if first then {} # zs else zs, EPrev I \<phi>' False buf' nts'))"
| "eeval j ts db (ENext I \<phi> first nts) =
     (let (xs, \<phi>') = eeval j ts db \<phi>;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
      in (zs, ENext I \<phi>' first' nts'))"
| "eeval j ts db (EAnds ps ns Ld dbuf) =
     (let R = map (eeval j ts db) Ld;
          (zs, dbuf') = mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty
            (mebufn_add (map fst R) dbuf)
      in (Rep_mbuf_t zs, EAnds ps ns (map snd R) dbuf'))"
| "eeval j ts db (ESince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = eeval j ts db \<phi>; (ys, \<psi>') = eeval j ts db \<psi>;
          (zs, buf', aux') = uedsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux
      in (zs, ESince dags \<phi>' \<psi>' buf' aux'))"
| "eeval j ts db (EUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = eeval j ts db \<phi>; (ys, \<psi>') = eeval j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (udux_add_new dags msk) aux
            (mebuf2_add xs ys buf) t (nts @@ ts);
          (zs, aux'') = udux_eval dags nt aux'
      in (zs, EUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "eeval j ts db (EAndAssign p t \<phi>) =
     (let (xs, \<phi>') = eeval j ts db \<phi> in (map (uassign p t) xs, EAndAssign p t \<phi>'))"
| "eeval j ts db (ETP mt i) =
     (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) [i..<j], ETP mt j)"
| "eeval j ts db (ETS mt) = (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) ts, ETS mt)"
| "eeval j ts db (ELet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = eeval j ts db \<phi>;
          (ys, \<psi>') = eeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, ELet p m \<phi>' \<psi>'))"
| "eeval j ts db (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) =
     (let (xs, \<phi>) = eeval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = eeval j ts db0 \<psi>;
          (rs, \<rho>) = eeval j ts db0 \<rho>;
          (zs0_out, jfrz, fl, \<alpha>s, lr) =
            (let zs0_out = drop (jfrz - jpsi0) zs0;
                 \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
             in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
               case lv of None \<Rightarrow> None | Some g \<Rightarrow>
                 if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
                 then Some (g, eeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
                 else None));
          (ys, \<alpha>s', lv, \<rho>, w, pR, tq, rb) = frz_live_loop size (eeval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
            fl d po j jfrz \<alpha>s lr (\<rho>, w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
              drop (min jfrz (pR + length rs) - (pR - length rb)) (rb @ rs))
      in (zs0_out @ ys, EFrz p m \<phi> \<psi> (jfrz + length ys) (jpsi0 + length zs0) (jphi + length xs) \<alpha>s' \<rho> w pR tq rb d po ng
        (frz_keep_lv (if po then None else lv) \<rho>L) (frz_keep_st (if po then None else lv) \<rho>L)))"
| "eeval j ts db (ELetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            letpast_meval0 (eeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
          (ys, \<psi>) = eeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, ELetPast p m \<phi> \<psi> i buf))"
| "eeval j ts db (ETrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = eeval j ts db \<phi>; (ys, \<psi>') = eeval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
            (mebuf2_add xs ys dbuf) (nts @@ ts)
      in (zs, ETrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "eeval j ts db (EAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> ebuf2 nts daux) =
     (let (as, \<alpha>') = eeval j ts db \<alpha>; (xs, \<phi>') = eeval j ts db \<phi>;
          (ys, \<psi>') = eeval j ts db \<psi>;
          ((ws, daux'), dbuf2', nts') = mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (ws @ [if gmmtaux_empty ax then None
                      else Some (gresult_mmtaux dags ax)], ax)) ([], daux)
            (mebuf2_add xs ys ebuf2) (nts @@ ts);
          (zs, dbuf1') = mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> gbin_join pl r1 True z) (mebuf2_add as ws dbuf1)
      in (zs, EAndTrigger pl \<alpha>' dbuf1' dags \<phi>' \<psi>' dbuf2' nts' daux'))"
| "eeval j ts db (EMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (eeval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mebufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @@ [z], ax)) (mbuf_t_empty, daux)
             (mebufn_add (map fst R) dbuf) 0 (nts @@ ts)
      in (Rep_mbuf_t zs, EMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "eeval j ts db (EMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (eeval j ts db) Ld;
          (daux', dbuf', nt, nts') = mebufnt_take
             (\<lambda>rels. gupdate_matchF (map emb_msk pls) I mr mrs rels)
             daux (mebufn_add (map fst R) dbuf) t (nts @@ ts);
          (zs, daux'') = geval_matchF I mr nt daux'
      in (zs, EMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
  by pat_completeness (simp_all only: prod.inject eformula.inject eformula.distinct simp_thms)

text \<open>The freeze node re-enters the evaluator on its body's \<^emph>\<open>updated\<close> state, which is
  not a subterm of the node, so the recursion is not structural and termination goes by the
  formula's size -- exactly as the kernel's own evaluator does it.  Evaluation preserves that
  size, which is the fact that makes the measure decrease.\<close>

lemma size_list_cong:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> size_list f xs = size_list g ys"
  by (induct xs arbitrary: ys) auto

lemma psize_snd_eeval:
  "eeval_dom (j, ts, db, \<phi>) \<Longrightarrow> size (snd (eeval j ts db \<phi>)) = size \<phi>"
proof (induct rule: eeval.pinduct)
  case (11 j ts db I \<phi> first buf nts) \<comment> \<open>\<^const>\<open>EPrev\<close>\<close>
  obtain xs \<phi>' where \<phi>': "eeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs buf' nts' where mp: "meprev_next I (buf @@ xs) (nts @@ ts) = (zs, buf', nts')"
    by (metis prod_cases3)
  have "size \<phi>' = size \<phi>"
    using 11(2) \<phi>' by simp
  then show ?case
    by (simp add: eeval.psimps(11)[OF 11(1)] \<phi>' mp del: meprev_next.simps)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L) \<comment> \<open>\<^const>\<open>EFrz\<close>\<close>
  let ?db0 = "Mapping.update (p, m) [] db"
  obtain xs \<phi>' where \<phi>': "eeval j ts db \<phi> = (xs, \<phi>')"
    by fastforce
  obtain zs0 \<psi>' where \<psi>': "eeval j ts ?db0 \<psi> = (zs0, \<psi>')"
    by fastforce
  obtain rs \<rho>' where \<rho>': "eeval j ts ?db0 \<rho> = (rs, \<rho>')"
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
         then Some (g, eeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None)) = (zo, jf, fl, as, lr)"
    by (rule prod_cases5)
  obtain ys as' lv' s' where lp0: "frz_live_loop size (eeval j) (p, m) (Mapping.map_values (\<lambda>_ _. []) db)
      fl d po j jf as lr (\<rho>', w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
        drop (min jf (pR + length rs) - (pR - length rb)) (rb @ rs)) = (ys, as', lv', s')"
    by (metis prod_cases4)
  obtain \<rho>'' w' pR' tq' rb' where s': "s' = (\<rho>'', w', pR', tq', rb')"
    by (metis prod_cases5)
  have s\<rho>'': "size \<rho>'' = size \<rho>"
    using frz_live_loop_size[OF lp0] s\<rho> s' by simp
  have "snd (eeval j ts db (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)) =
    EFrz p m \<phi>' \<psi>' (jf + length ys) (jpsi0 + length zs0) (jphi + length xs) as' \<rho>'' w' pR' tq' rb' d po ng
      (frz_keep_lv (if po then None else lv') \<rho>L) (frz_keep_st (if po then None else lv') \<rho>L)"
    by (simp only: eeval.psimps(20)[OF 20(1)] \<phi>' \<psi>' \<rho>' st lp0[unfolded s'] Let_def[where s = ?db0]
        Let_def[where s = "(xs, \<phi>')"] Let_def[where s = "(zs0, \<psi>')"] Let_def[where s = "(rs, \<rho>')"]
        Let_def[where s = "(zo, jf, fl, as, lr)"] Let_def[where s = "(ys, as', lv', \<rho>'', w', pR', tq', rb')"]
        prod.case snd_conv)
  then show ?case
    using s\<phi> s\<psi> s\<rho>'' by simp
next
  case (21 j ts db p m \<phi> \<psi> i buf) \<comment> \<open>\<^const>\<open>ELetPast\<close>\<close>
  obtain xs i' buf' \<phi>' where lp:
    "letpast_meval0 (eeval j) j i [] (list_of_option buf) (p, m) ts db \<phi> = (xs, i', buf', \<phi>')"
    by (metis prod_cases4)
  have "size (snd (snd (snd
      (letpast_meval0 (eeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>)))) = size \<phi>"
    by (rule size_letpast_meval) (simp add: 21(2))
  then have size_\<phi>': "size \<phi>' = size \<phi>"
    by (simp add: lp)
  obtain ys \<psi>' where \<psi>': "eeval j ts (Mapping.update (p, m) xs db) \<psi> = (ys, \<psi>')"
    by fastforce
  have size_\<psi>': "size \<psi>' = size \<psi>"
    using 21(3)[OF lp[symmetric] refl refl refl] \<psi>' by simp
  show ?case
    using size_\<phi>' size_\<psi>' by (simp add: eeval.psimps(21)[OF 21(1)] lp \<psi>')
  \<comment> \<open>in all other cases, the claim follows directly from the IHs for the subformulas,
    since evaluation keeps the node's constructor and its non-formula arguments do not count\<close>
qed (auto simp only: prod.inject eeval.psimps Let_def snd_conv fst_conv
    eformula.size list.map map_map o_apply size_list_map size_frz_keep_st cong: size_list_cong
    split: prod.splits)

lemma total_eeval: "All eeval_dom"
proof (relation "measure (\<lambda>(j, ts, db, \<phi>). size \<phi>)", goal_cases)
  text \<open>The live copy and the replays of @{const EFrz}, as for @{const meval}.\<close>
  case 23 \<comment> \<open>the live copy, a subterm\<close>
  then show ?case
    by simp
next
  case (24 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L x xa y xb xc xd ya xe xf yb xg xh
    yc xi yd xj yca xk ycb tsa dba \<psi>')
  have "size yb = size \<rho>"
    using psize_snd_eeval[of j ts xb \<rho>] 24 by (metis snd_conv)
  then show ?case
    using 24 by simp
qed (auto simp: termination_simp dest!: psize_snd_eeval dest: sym)

lemmas size_snd_eeval = psize_snd_eeval[OF total_eeval[THEN spec]]

termination eeval by (rule total_eeval)

section \<open>The simulation relation\<close>

text \<open>
  @{term "esim n ks cs tw \<phi>d \<phi>"} relates a executable formula to a kernel one whose tables are over
  the column list @{term ks}, read by the executable one over its ascending order @{term cs}.  The
  relation is about the state alone; the operand well-formedness that the
  @{theory MFODL_Monitor_Exec.Frame} theorems ask for comes from the call (@{const kgood}).
\<close>

definition ebuf2 :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> event_data mbuf2 \<Rightarrow> event_data mbuf2 \<Rightarrow> bool" where
  "ebuf2 k1 c1 k2 c2 buf dbuf \<longleftrightarrow>
     list_all (ftable k1) (fst buf) \<and> list_all (ftable k2) (snd buf) \<and>
     dbuf = (map (etabc k1 c1) (fst buf), map (etabc k2 c2) (snd buf))"

definition ebufn :: "cols list \<Rightarrow> cols list \<Rightarrow> event_data mbufn \<Rightarrow> event_data mbufn \<Rightarrow> bool" where
  "ebufn kss css buf dbuf \<longleftrightarrow> length buf = length css \<and> length kss = length css \<and>
     (\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)) \<and>
     dbuf = map2 map (map2 etabc kss css) buf"

text \<open>
  The relation carries a timestamp bound: @{term "esim n ks cs tw \<phi>d \<phi>"} is read as \<open>every
  timestamp stored anywhere inside is at most tw\<close>.  Only the temporal nodes look at it -- the
  verified Since structure accepts a new timestamp only at or after the one it is already at, and
  a fresh batch of timestamps arrives at the node from outside, where the relation cannot see it.
  Every other rule carries the bound without using it.  After a step the bound moves to the last
  timestamp of the batch.
\<close>

subsection \<open>The aggregation at a structure's output\<close>

text \<open>
  The kernel fuses an aggregation into the Since and the Until: the structure is stepped at the
  operand's columns and the aggregation is applied to whatever it reports.  The executable side runs
  the structure without one -- @{const eargs} clears the field -- and applies the executable
  aggregation afterwards, so the two output lists are not reorderings of each other but two images
  of one list of windows.  That is what the relation below says.  With no aggregation it
  degenerates to the reordering, which is what the unfused nodes use.
\<close>

definition esres :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> event_data table list \<Rightarrow> event_data table list \<Rightarrow> bool"
  where "esres ks cs args zs dzs \<longleftrightarrow> (\<exists>ws. list_all (table ks) ws \<and>
     zs = map (eval_args_agg args) ws \<and> dzs = map (etabc ks cs) ws)"

lemma esres_Nil[simp]: "esres ks cs args [] []"
  unfolding esres_def by (intro exI[of _ "[]"]) simp

lemma esres_none:
  assumes "args_agg args = None" and "esres ks cs args zs dzs"
  shows "dzs = map (etabc ks cs) zs"
  using assms unfolding esres_def eval_args_agg_def by auto

text \<open>The window a firing reports is a union of the auxiliary list's tables, so it is a table over
  the node's columns; the kernel's structure reports its aggregation and the executable one reports its
  reordering -- or, for the window with the aggregate fused in, the executable aggregation of its
  reordering.  The relation below carries that post-function; @{const esres} is its identity
  instance.\<close>

definition esresh :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> (event_data table \<Rightarrow> event_data table) \<Rightarrow>
    event_data table list \<Rightarrow> event_data table list \<Rightarrow> bool"
  where "esresh ks cs args h zs dzs \<longleftrightarrow> (\<exists>ws. list_all (table ks) ws \<and>
     zs = map (eval_args_agg args) ws \<and> dzs = map (h \<circ> etabc ks cs) ws)"

lemma esresh_id: "esresh ks cs args id zs dzs \<longleftrightarrow> esres ks cs args zs dzs"
  unfolding esresh_def esres_def by simp

lemma esresh_Nil[simp]: "esresh ks cs args h [] []"
  unfolding esresh_def by (intro exI[of _ "[]"]) simp

lemma esresh_Cons:
  assumes w: "table ks w" and r: "esresh ks cs args h zs dzs"
  shows "esresh ks cs args h (eval_args_agg args w # zs) (h (etabc ks cs w) # dzs)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> etabc ks cs) ws" using r unfolding esresh_def by blast
  show ?thesis unfolding esresh_def by (intro exI[of _ "w # ws"]) (use w ws in simp)
qed

lemma esresh_append:
  assumes a: "esresh ks cs args h zs dzs" and b: "esresh ks cs args h us dus"
  shows "esresh ks cs args h (zs @ us) (dzs @ dus)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> etabc ks cs) ws" using a unfolding esresh_def by blast
  obtain vs where vs: "list_all (table ks) vs" "us = map (eval_args_agg args) vs"
    "dus = map (h \<circ> etabc ks cs) vs" using b unfolding esresh_def by blast
  show ?thesis unfolding esresh_def
    by (intro exI[of _ "ws @ vs"]) (use ws vs in simp)
qed

lemma esresh_rev:
  assumes "esresh ks cs args h zs dzs"
  shows "esresh ks cs args h (rev zs) (rev dzs)"
proof -
  obtain ws where ws: "list_all (table ks) ws" "zs = map (eval_args_agg args) ws"
    "dzs = map (h \<circ> etabc ks cs) ws" using assms unfolding esresh_def by blast
  show ?thesis unfolding esresh_def
    by (intro exI[of _ "rev ws"]) (use ws in \<open>simp add: rev_map\<close>)
qed

lemma esresh_rev':
  "rev zs = us \<Longrightarrow> rev dzs = dus \<Longrightarrow> esresh ks cs args h zs dzs \<Longrightarrow> esresh ks cs args h us dus"
  using esresh_rev by blast

lemma table_foldr_Un: "list_all (table ks) ws \<Longrightarrow> table ks (foldr (\<union>) ws {})"
  by (induct ws) (auto simp: table_def)

lemma esresh_result:
  assumes vd: "esxaux' kR cR cL args cur da al"
    and vw: "valid_mmasaux args cur wa al"
  shows "esresh kR cR args (esx_post da) [result_mmasaux args wa] [esx_result (eargs cR cL args) da]"
proof -
  let ?W = "foldr (\<union>) [rel. (t, rel) \<leftarrow> al, memL (args_ivl args) (cur - t)] {}"
  have tw: "table kR ?W"
    by (rule table_foldr_Un) (use esxaux'_tables[OF vd] in \<open>auto simp: list_all_iff\<close>)
  have e: "result_mmasaux args wa = eval_args_agg args ?W"
    by (rule default_mmasaux.valid_result_msaux[OF vw])
  have d: "esx_result (eargs cR cL args) da = esx_post da (etabc kR cR ?W)"
    by (rule esxaux'_result[OF vd])
  show ?thesis unfolding e d by (rule esresh_Cons[OF tw esresh_Nil])
qed

subsection \<open>The Since structure at the ascending frame, and its buffer\<close>

text \<open>
  The executable Since node runs the verified structure at @{const eargs}.  What the node carries is
  the pair of structures -- the kernel's and the executable one -- related through the abstract
  auxiliary list they are both valid for, together with the two buffers.  The current timestamp
  is shared: the structure's, and the lower bound on the timestamps still in the buffer.  The
  left operand's tables enter the buffer at their own columns.
\<close>

definition esince_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    mmasaux \<Rightarrow> esaux_x \<Rightarrow> event_data mbuf2S \<Rightarrow> event_data mbuf2S \<Rightarrow> bool" where
  "esince_rel kR cR kL cL args tw aux daux buf dbuf \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmasaux args cur aux auxlist \<and>
        esxaux' kR cR cL args cur daux auxlist \<and> cur \<le> tw \<and>
        (case buf of (xs, ys, tss, sk) \<Rightarrow>
           list_all (ftable kL) xs \<and> list_all (ftable kR) ys \<and>
           sorted tss \<and> (\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw) \<and>
           dbuf = (map (etabc kL cL) xs, map (etabc kR cR) ys, tss, sk)))"

lemma esince_relI:
  "valid_mmasaux args cur aux auxlist \<Longrightarrow> esxaux' kR cR cL args cur daux auxlist \<Longrightarrow>
   cur \<le> tw \<Longrightarrow>
   list_all (ftable kL) xs \<Longrightarrow> list_all (ftable kR) ys \<Longrightarrow>
   sorted tss \<Longrightarrow> \<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw \<Longrightarrow>
   esince_rel kR cR kL cL args tw aux daux (xs, ys, tss, sk)
     (map (etabc kL cL) xs, map (etabc kR cR) ys, tss, sk)"
  unfolding esince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma esince_relE:
  assumes "esince_rel kR cR kL cL args tw aux daux (xs, ys, tss, sk) dbuf"
  obtains cur auxlist where "valid_mmasaux args cur aux auxlist"
    and "esxaux' kR cR cL args cur daux auxlist" and "cur \<le> tw"
    and "list_all (ftable kL) xs" and "list_all (ftable kR) ys"
    and "sorted tss" and "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and "dbuf = (map (etabc kL cL) xs, map (etabc kR cR) ys, tss, sk)"
  using assms unfolding esince_rel_def by (auto simp del: valid_mmasaux.simps)

lemma esince_relD_buf:
  "esince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow>
     dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (fst (snd buf)),
             fst (snd (snd buf)), snd (snd (snd buf)))"
  by (cases buf) (auto elim!: esince_relE)

text \<open>Widening the bound is harmless, which is what the node needs when a new batch of
  timestamps arrives.\<close>

text \<open>A fresh batch of operand tables and timestamps enters the buffer at both representations at
  once.  The batch's timestamps are all at or after the old bound, and the buffer's are all at or
  before it, so the concatenation stays sorted and the new bound is the batch's last timestamp.\<close>

lemma esince_rel_add:
  assumes r: "esince_rel kR cR kL cL args tw aux daux buf dbuf"
    and lx: "list_all (ftable kL) xs" and ly: "list_all (ftable kR) ys"
    and s: "sorted ts" and b: "\<forall>t \<in> set ts. tw \<le> t"
  shows "esince_rel kR cR kL cL args (enext tw ts) aux daux (mbuf2S_add xs ys ts buf)
     (mbuf2S_add (map (etabc kL cL) xs) (map (etabc kR cR) ys) ts dbuf)"
proof (cases buf)
  case (fields us vs tss sk)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "esxaux' kR cR cL args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable kL) us" and lv: "list_all (ftable kR) vs"
    and st: "sorted tss" and ct: "\<forall>t \<in> set tss. cur \<le> t \<and> t \<le> tw"
    and dbuf: "dbuf = (map (etabc kL cL) us, map (etabc kR cR) vs, tss, sk)"
    using r unfolding fields by (rule esince_relE)
  have "sorted (tss @ ts)" using st s ct b
    by (fastforce simp: sorted_append intro: order_trans)
  moreover have "\<forall>t \<in> set (tss @ ts). cur \<le> t \<and> t \<le> enext tw ts"
    using ct b ctw enext_ge[OF b] enext_bound[OF s] by fastforce
  ultimately show ?thesis unfolding fields dbuf
    using esince_relI[OF vw vd order_trans[OF ctw enext_ge[OF b]],
      where xs = "us @ xs" and ys = "vs @ ys" and tss = "tss @ ts" and sk = sk and kL = kL]
      lu lx lv ly
    by simp
qed

subsection \<open>The Until structure at the ascending frame, and its buffer\<close>

text \<open>
  The Until node's state is the pair of verified structures, related through the abstract
  auxiliary list they are both valid for, together with the current timestamp.  Since the
  structure is stepped from inside a buffer traversal, that part is factored out on its own.
\<close>

definition euaux_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> euaux_x \<Rightarrow> bool" where
  "euaux_rel kR cR kL cL args cur aux daux \<longleftrightarrow>
     (\<exists>auxlist. valid_muaux_dq args cur aux auxlist \<and>
        euxaux' kL cL kR cR args cur daux auxlist)"

lemma euaux_rel_step:
  assumes v: "euaux_rel kR cR kL cL args u aux daux"
    and fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and t1: "table kL a" and t2: "table kR b" and f2: "finite b"
    and ut: "u \<le> t"
  shows "euaux_rel kR cR kL cL args t (add_new_muaux_dq args a b t aux)
     (eux_add_new (eargs cR cL args) (emsk cR cL)
       (etabc kL cL a) (etabc kR cR b) t daux)"
proof -
  obtain auxlist where vw: "valid_muaux_dq args u aux auxlist"
    and vd: "euxaux' kL cL kR cR args u daux auxlist"
    using v unfolding euaux_rel_def by blast
  have "valid_muaux_dq args t (add_new_muaux_dq args a b t aux) (update_until args a b t auxlist)"
    by (rule valid_add_new_muaux_dq[OF vw _ _ ut]) (use t1 t2 aL aR in simp_all)
  moreover have "euxaux' kL cL kR cR args t
      (eux_add_new (eargs cR cL args) (emsk cR cL)
        (etabc kL cL a) (etabc kR cR b) t daux)
      (update_until args a b t auxlist)"
    by (rule euxaux'_add_new[OF vd fR fL sub aL aR t1 t2 f2 ut])
  ultimately show ?thesis unfolding euaux_rel_def by blast
qed

lemma eux_agg_mbuf2t_take:
  "mbuf2t_take (eux_add_new args msk) daux buf t nts = (daux', buf', t', nts') \<Longrightarrow>
   eux_agg daux' = eux_agg daux"
  by (induction "eux_add_new args msk" daux buf t nts arbitrary: daux' buf' t' nts'
      rule: mbuf2t_take.induct) (auto split: if_splits prod.splits)

lemma eux_post_mbuf2t_take:
  "mbuf2t_take (eux_add_new args msk) daux buf t nts = (daux', buf', t', nts') \<Longrightarrow>
   eux_post daux' = eux_post daux"
  using eux_agg_mbuf2t_take by (simp add: eux_post_eq)

lemma euaux_rel_eval:
  assumes v: "euaux_rel kR cR kL cL args cur aux daux" and nt: "cur \<le> nt"
    and we: "eval_muaux_dq args nt aux = (zs, aux')"
    and de: "eux_eval (eargs cR cL args) nt daux = (dzs, daux')"
  shows "esresh kR cR args (eux_post daux) zs dzs \<and>
    euaux_rel kR cR kL cL args cur aux' daux'"
proof -
  obtain auxlist where vw: "valid_muaux_dq args cur aux auxlist"
    and vd: "euxaux' kL cL kR cR args cur daux auxlist"
    using v unfolding euaux_rel_def by blast
  obtain res auxlist' where eu: "eval_until (args_ivl args) nt auxlist = (res, auxlist')"
    by (cases "eval_until (args_ivl args) nt auxlist")
  have w: "valid_muaux_dq args cur aux' auxlist' \<and> zs = map (eval_args_agg args) res"
    by (rule valid_eval_muaux_dq[OF vw nt we eu])
  have d: "dzs = map (eux_post daux \<circ> etabc kR cR) res \<and>
      euxaux' kL cL kR cR args cur daux' auxlist'"
    by (rule euxaux'_eval[OF vd nt de eu])
  have tr: "list_all (table kR) res"
  proof (unfold list_all_iff, safe)
    fix x assume "x \<in> set res"
    then obtain t a1 where "(t, a1, x) \<in> set auxlist"
      unfolding eval_until_res[OF eu] by (auto dest!: set_takeWhileD)
    then show "table kR x" using euxaux'_tables[OF vd] by auto
  qed
  show ?thesis using w d tr unfolding euaux_rel_def esresh_def by blast
qed

text \<open>The node relation.  The stored timestamp is at or after the structure's current one and
  at or before the bound, and so is every timestamp still queued.\<close>

definition euntil_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow>
    muaux_dq \<Rightarrow> euaux_x \<Rightarrow> event_data mbuf2 \<Rightarrow> event_data mbuf2 \<Rightarrow>
    ts list \<Rightarrow> bool" where
  "euntil_rel kR cR kL cL args tw t aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur. euaux_rel kR cR kL cL args cur aux daux \<and> cur \<le> t \<and> t \<le> tw \<and>
        list_all (ftable kL) (fst buf) \<and>
        list_all (ftable kR) (snd buf) \<and>
        dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (snd buf)) \<and>
        sorted nts \<and> (\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw))"

text \<open>
  One firing of the Until node: the buffer traversal steps the two structures in lockstep, and
  then one evaluation at the timestamp the traversal reports yields the reordering of what the
  kernel's one yields.
\<close>

lemma until_step_rel:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and rel: "euntil_rel kR cR kL cL args tw t aux daux buf dbuf nts"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and s: "sorted tss" and bnd: "\<forall>u \<in> set tss. tw \<le> u"
    and we: "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ tss)
      = (aux1, buf1, nt, nts1)"
    and de: "mbuf2t_take (eux_add_new (eargs cR cL args) (emsk cR cL)) daux
      (mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) t (nts @ tss)
      = (daux1, dbuf1, dnt, dnts1)"
    and wev: "eval_muaux_dq args nt aux1 = (zs, aux2)"
    and dev: "eux_eval (eargs cR cL args) dnt daux1 = (dzs, daux2)"
  shows "esresh kR cR args (eux_post daux) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
     dbuf1 = (map (etabc kL cL) (fst buf1), map (etabc kR cR) (snd buf1)) \<and>
     euntil_rel kR cR kL cL args (enext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
proof -
  obtain cur where vr: "euaux_rel kR cR kL cL args cur aux daux"
    and ct: "cur \<le> t" and ttw: "t \<le> tw"
    and lu: "list_all (ftable kL) (fst buf)"
    and lv: "list_all (ftable kR) (snd buf)"
    and dbe: "dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (snd buf))"
    and sn: "sorted nts" and cn: "\<forall>u \<in> set nts. cur \<le> u \<and> u \<le> tw"
    using rel unfolding euntil_rel_def by blast
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mda: "mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf
      = (map (etabc kL cL) us, map (etabc kR cR) vs)"
    unfolding dbe us_def vs_def by (cases buf) simp
  have lus: "list_all (ftable kL) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable kR) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a b t' u z z'. a \<in> set us \<Longrightarrow> b \<in> set vs \<Longrightarrow>
      euaux_rel kR cR kL cL args u z z' \<Longrightarrow> u \<le> t' \<Longrightarrow>
      euaux_rel kR cR kL cL args t' (add_new_muaux_dq args a b t' z)
        (eux_add_new (eargs cR cL args) (emsk cR cL)
          (etabc kL cL a) (etabc kR cR b) t' z')"
    using lus lvs by (intro euaux_rel_step[OF _ fR fL sub aL aR]) (auto simp: list_all_iff)
  have sts: "sorted (nts @ tss)"
    using sn s cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>u \<in> set (nts @ tss). cur \<le> u" using cn bnd ct ttw by fastforce
  have tdn: "t \<le> enext tw tss" using ttw enext_ge[OF bnd] by simp
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> enext tw tss"
    using cn enext_ge[OF bnd] enext_bound[OF s] by fastforce
  have we': "mbuf2t_take (add_new_muaux_dq args) aux (us, vs) t (nts @ tss)
      = (aux1, (b1, b2), nt, nts1)" using we unfolding ma bfs by simp
  have de': "mbuf2t_take (eux_add_new (eargs cR cL args) (emsk cR cL)) daux
      (map (etabc kL cL) us, map (etabc kR cR) vs) t (nts @ tss) = (daux1, dbuf1, dnt, dnts1)"
    using de unfolding mda by simp
  have R: "(\<exists>u. euaux_rel kR cR kL cL args u aux1 daux1 \<and> u \<le> nt \<and>
        (\<forall>v \<in> set nts1. u \<le> v)) \<and> sorted nts1 \<and>
      (nt = t \<or> nt \<in> set (nts @ tss)) \<and> set nts1 \<subseteq> set (nts @ tss) \<and>
      dbuf1 = (map (etabc kL cL) b1, map (etabc kR cR) b2) \<and> dnt = nt \<and> dnts1 = nts1"
    by (rule mbuf2t_take_rel_ts[OF step vr ct sts cts we' de'])
  obtain u where vu: "euaux_rel kR cR kL cL args u aux1 daux1" and unt: "u \<le> nt"
    and un: "\<forall>v \<in> set nts1. u \<le> v" using R by blast
  have dn: "dnt = nt" and dns: "dnts1 = nts1" and sn1: "sorted nts1"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf: "dbuf1 = (map (etabc kL cL) b1, map (etabc kR cR) b2)" using R by blast+
  have ntdn: "nt \<le> enext tw tss" using R tdn bound by blast
  have pst: "eux_post daux1 = eux_post daux" by (rule eux_post_mbuf2t_take[OF de])
  have ev: "esresh kR cR args (eux_post daux) zs dzs \<and>
      euaux_rel kR cR kL cL args u aux2 daux2"
    using euaux_rel_eval[OF vu unt wev dev[unfolded dn]] pst by simp
  have sb: "set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs" by (rule mbuf2t_take_sub[OF we'])
  have lb1: "list_all (ftable kL) b1" using sb lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable kR) b2" using sb lvs by (auto simp: list_all_iff)
  have "euaux_rel kR cR kL cL args u aux2 daux2 \<and> u \<le> nt \<and> nt \<le> enext tw tss \<and>
      list_all (ftable kL) (fst buf1) \<and>
      list_all (ftable kR) (snd buf1) \<and>
      dbuf1 = (map (etabc kL cL) (fst buf1), map (etabc kR cR) (snd buf1)) \<and>
      sorted nts1 \<and> (\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> enext tw tss)"
    using ev unt ntdn lb1 lb2 dbf sn1 un sub1 bound bfs by auto
  then have "euntil_rel kR cR kL cL args (enext tw tss) nt aux2 daux2 buf1 dbuf1 nts1"
    unfolding euntil_rel_def by blast
  then show ?thesis using ev dn dns dbf bfs by simp
qed

subsection \<open>The Trigger structure at the ascending frame, and its buffer\<close>

text \<open>
  The trigger node carries the pair of structures, related through the abstract auxiliary list
  they are both valid for, together with the two buffers and the pending timestamps.  Unlike the
  Since and the Until, the structure is stepped and read in the same traversal, so the output
  list is part of what the step relates.  Each operand's tables enter the buffer at their own
  columns.
\<close>

definition etrigger_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    event_data mmtaux \<Rightarrow> event_data gmmtaux \<Rightarrow> event_data mbuf2 \<Rightarrow>
    event_data mbuf2 \<Rightarrow> ts list \<Rightarrow> bool" where
  "etrigger_rel kR cR kL cL args tw aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmtaux args cur aux auxlist \<and>
        (\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r) \<and>
        etaux kL cL kR cR args cur daux auxlist \<and> cur \<le> tw \<and>
        list_all (ftable kL) (fst buf) \<and>
        list_all (ftable kR) (snd buf) \<and>
        sorted nts \<and> (\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw) \<and>
        dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (snd buf)))"

lemma etrigger_relI:
  "valid_mmtaux args cur aux auxlist \<Longrightarrow>
   (\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r) \<Longrightarrow>
   etaux kL cL kR cR args cur daux auxlist \<Longrightarrow> cur \<le> tw \<Longrightarrow>
   list_all (ftable kL) xs \<Longrightarrow> list_all (ftable kR) ys \<Longrightarrow>
   sorted nts \<Longrightarrow> \<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw \<Longrightarrow>
   etrigger_rel kR cR kL cL args tw aux daux (xs, ys)
     (map (etabc kL cL) xs, map (etabc kR cR) ys) nts"
  unfolding etrigger_rel_def
  by (intro exI[where x = cur] exI[where x = auxlist] conjI) simp_all

lemma etrigger_relE:
  assumes "etrigger_rel kR cR kL cL args tw aux daux buf dbuf nts"
  obtains cur auxlist where "valid_mmtaux args cur aux auxlist"
    and "\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r"
    and "etaux kL cL kR cR args cur daux auxlist" and "cur \<le> tw"
    and "list_all (ftable kL) (fst buf)"
    and "list_all (ftable kR) (snd buf)"
    and "sorted nts" and "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and "dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (snd buf))"
  using assms unfolding etrigger_rel_def by (elim exE conjE) (rule that)

text \<open>One firing of the trigger structure: the buffer traversal that steps it once per pending
  timestamp and collects what it answers.  The two runs stay in step by
  @{thm [source] mbuf2T_take_rel}, and each individual step is @{thm [source] etaux_update}
  followed by @{thm [source] etaux_result}.\<close>

lemma etrigger_step_rel:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and m0: "mem (args_ivl args) 0"
    and rel: "etrigger_rel kR cR kL cL args tw aux daux buf dbuf nts"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and st: "sorted tss" and bnd: "\<forall>v \<in> set tss. tw \<le> v"
    and we: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
        in (zs @ [z], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ tss)
      = ((zs, aux1), buf1, nts1)"
    and de: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = gupdate_mmtaux (eargs cR cL args) t r1 r2 ax
        in (zs @ [gresult_mmtaux (eargs cR cL args) ax], ax)) ([], daux)
        (mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) (nts @ tss)
      = ((dzs, daux1), dbuf1, dnts1)"
  shows "dzs = map (etabc kR cR) zs \<and> dnts1 = nts1 \<and>
     etrigger_rel kR cR kL cL args (enext tw tss) aux1 daux1 buf1 dbuf1 nts1"
proof -
  obtain cur auxlist where vw: "valid_mmtaux args cur aux auxlist"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r"
    and vd: "etaux kL cL kR cR args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable kL) (fst buf)"
    and lv: "list_all (ftable kR) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and dbf: "dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (snd buf))"
    using rel by (rule etrigger_relE)
  have m0': "mem (args_ivl (eargs cR cL args)) 0" using m0 by simp
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  define g where "g = (\<lambda>r1 r2 t (zs :: event_data table list, ax).
    let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
    in (zs @ [z], ax))"
  define gd where "gd = (\<lambda>r1 r2 t (zs :: event_data table list, ax).
    let ax = gupdate_mmtaux (eargs cR cL args) t r1 r2 ax
    in (zs @ [gresult_mmtaux (eargs cR cL args) ax], ax))"
  define R where "R = (\<lambda>v (pr :: event_data table list \<times> event_data mmtaux)
      (dpr :: event_data table list \<times> event_data gmmtaux).
    (\<exists>al. valid_mmtaux args v (snd pr) al \<and>
       (\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r) \<and>
       etaux kL cL kR cR args v (snd dpr) al) \<and>
     fst dpr = map (etabc kR cR) (fst pr))"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mad: "mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf
      = (map (etabc kL cL) us, map (etabc kR cR) vs)"
    using dbf by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable kL) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable kR) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a c v w z z'. a \<in> set us \<Longrightarrow> c \<in> set vs \<Longrightarrow> R w z z' \<Longrightarrow> w \<le> v \<Longrightarrow>
      R v (g a c v z) (gd (etabc kL cL a) (etabc kR cR c) v z')"
  proof -
    fix a c v w and z :: "event_data table list \<times> event_data mmtaux"
      and z' :: "event_data table list \<times> event_data gmmtaux"
    assume au: "a \<in> set us" and cv: "c \<in> set vs" and q: "R w z z'" and wv: "w \<le> v"
    have t1: "ftable kL a" using au lus by (simp add: list_all_iff)
    have t2: "ftable kR c" using cv lvs by (simp add: list_all_iff)
    obtain al where vwz: "valid_mmtaux args w (snd z) al"
      and wfz: "\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r"
      and vdz: "etaux kL cL kR cR args w (snd z') al"
      using q unfolding R_def by blast
    have fz: "fst z' = map (etabc kR cR) (fst z)" using q unfolding R_def by blast
    define al' where "al' = filter (\<lambda>(t, _). memR (args_ivl args) (v - t)) al @ [(v, a, c)]"
    have vw': "valid_mmtaux args v (update_mmtaux args v a c (snd z)) al'"
      unfolding al'_def
      by (rule valid_update_mmtaux[OF wv _ _ vwz]) (use t1 t2 aL aR in simp_all)
    have wf': "\<forall>(t, l, r) \<in> set al'. ftable kL l \<and> ftable kR r"
      using wfz t1 t2 unfolding al'_def by auto
    have vd': "etaux kL cL kR cR args v
        (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z')) al'"
      unfolding al'_def by (rule etaux_update[OF vdz wv fR fL sub]) (use t1 t2 in simp_all)
    have ne: "\<not> gmmtaux_empty (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a)
        (etabc kR cR c) (snd z'))"
      by (rule gupdate_mmtaux_not_empty[OF m0'])
    have res: "result_mmtaux args (update_mmtaux args v a c (snd z))
        = trigger_results args v al'" by (rule valid_result_mmtaux[OF vw'])
    have dres: "gresult_mmtaux (eargs cR cL args)
          (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z'))
        = etabc kR cR (snd (trigger_results args v al'))"
      by (rule etaux_result[OF vd' ne fR fL sub aL aR])
    have dres': "gresult_mmtaux (eargs cR cL args)
          (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z'))
        = etabc kR cR (snd (result_mmtaux args (update_mmtaux args v a c (snd z))))"
      unfolding res by (rule dres)
    have gz: "g a c v z
        = (fst z @ [snd (result_mmtaux args (update_mmtaux args v a c (snd z)))],
           update_mmtaux args v a c (snd z))"
      by (cases z) (simp add: g_def Let_def case_prod_beta)
    have gdz: "gd (etabc kL cL a) (etabc kR cR c) v z'
        = (fst z' @ [gresult_mmtaux (eargs cR cL args)
             (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z'))],
           gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z'))"
      by (cases z') (simp add: gd_def Let_def case_prod_beta)
    show "R v (g a c v z) (gd (etabc kL cL a) (etabc kR cR c) v z')"
      unfolding R_def gz gdz fst_conv snd_conv
      using vw' wf' vd' fz dres' by (intro conjI exI[where x = al']) simp_all
  qed
  have sts: "sorted (nts @ tss)"
    using sn st cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>v \<in> set (nts @ tss). cur \<le> v" using cn bnd ctw by fastforce
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> enext tw tss"
    using cn enext_ge[OF bnd] enext_bound[OF st] by fastforce
  have cdn: "cur \<le> enext tw tss" using ctw enext_ge[OF bnd] by simp
  have r0: "R cur ([], aux) ([], daux)" unfolding R_def
    by (intro conjI exI[where x = auxlist]) (use vw wf vd in simp_all)
  have we': "mbuf2T_take g ([], aux) (us, vs) (nts @ tss) = ((zs, aux1), (b1, b2), nts1)"
    using we unfolding ma bfs g_def by simp
  have de': "mbuf2T_take gd ([], daux) (map (etabc kL cL) us, map (etabc kR cR) vs)
      (nts @ tss) = ((dzs, daux1), dbuf1, dnts1)"
    using de unfolding mad gd_def by simp
  have Rr: "(\<exists>u. R u (zs, aux1) (dzs, daux1) \<and> u \<le> enext tw tss \<and> (\<forall>t \<in> set nts1. u \<le> t)) \<and>
      sorted nts1 \<and> set nts1 \<subseteq> set (nts @ tss) \<and> set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs \<and>
      dbuf1 = (map (etabc kL cL) b1, map (etabc kR cR) b2) \<and> dnts1 = nts1"
    by (rule mbuf2T_take_rel[where R = R and f = g and g = gd and h = "etabc kL cL"
        and k = "etabc kR cR", OF step r0 sts cts bound cdn we' de'])
  obtain u where ru: "R u (zs, aux1) (dzs, daux1)" and ub: "u \<le> enext tw tss"
    and un: "\<forall>t \<in> set nts1. u \<le> t" using Rr by blast
  have sn1: "sorted nts1" and sb1: "set b1 \<subseteq> set us" and sb2: "set b2 \<subseteq> set vs"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf1: "dbuf1 = (map (etabc kL cL) b1, map (etabc kR cR) b2)"
    and dn1: "dnts1 = nts1" using Rr by blast+
  have lb1: "list_all (ftable kL) b1" using sb1 lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable kR) b2" using sb2 lvs by (auto simp: list_all_iff)
  obtain al1 where v1: "valid_mmtaux args u aux1 al1"
    and w1: "\<forall>(t, l, r) \<in> set al1. ftable kL l \<and> ftable kR r"
    and d1: "etaux kL cL kR cR args u daux1 al1" using ru unfolding R_def by auto
  have dz: "dzs = map (etabc kR cR) zs" using ru unfolding R_def by simp
  have bnd1: "\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> enext tw tss" using un sub1 bound by auto
  have "etrigger_rel kR cR kL cL args (enext tw tss) aux1 daux1 (b1, b2)
      (map (etabc kL cL) b1, map (etabc kR cR) b2) nts1"
    by (rule etrigger_relI[OF v1 w1 d1 ub lb1 lb2 sn1 bnd1])
  then show ?thesis using dz dn1 bfs dbf1 by simp
qed

subsection \<open>The fused And-Trigger, and its two buffers\<close>

text \<open>
  The kernel's fused node reads the trigger structure as a pair: a column list and a table.  On a
  non-empty window the list is the trigger's own columns and the table is its answer; on an empty
  one the read is the unit table over no columns at all, which the join then lets through
  untouched.  The executable node keeps that distinction as an option -- @{term None} stands for the
  empty window and the join step skips -- so the two reads are related rather than equal.
\<close>

definition etres :: "cols \<Rightarrow> cols \<Rightarrow> cols \<times> event_data table \<Rightarrow> event_data table option \<Rightarrow> bool"
  where
  "etres kR cR p q \<longleftrightarrow> (case q of
      None \<Rightarrow> p = ([], unit_table)
    | Some d \<Rightarrow> fst p = kR \<and> ftable kR (snd p) \<and> d = etabc kR cR (snd p))"

lemma etres_join:
  assumes fK: "eframe ks cs" and fR: "eframe kR cR" and sub: "set kR \<subseteq> set ks"
    and t: "ftable ks a" and r: "etres kR cR p q"
  shows "(case q of None \<Rightarrow> etabc ks cs a
        | Some z \<Rightarrow> gbin_join (mk_djoin cs cR) (etabc ks cs a) True z)
      = etabc ks cs (bin_join ks a True (fst p) (snd p))"
proof (cases q)
  case None
  then have p: "p = ([], unit_table)" using r by (simp add: etres_def)
  have "bin_join ks a True [] unit_table = join ks a True [] unit_table"
    by (rule bin_join_table) (use t eframeD(1)[OF fK] in simp_all)
  then have "bin_join ks a True [] unit_table = a"
    using join_unit_table(1)[OF eframeD(1)[OF fK] conjunct1[OF t]] by simp
  then show ?thesis using None unfolding p by simp
next
  case (Some d)
  then have fp: "fst p = kR" and tp: "ftable kR (snd p)"
    and d: "d = etabc kR cR (snd p)" using r by (auto simp: etres_def)
  have sc: "set cR \<subseteq> set cs" using sub eframeD(3)[OF fK] eframeD(3)[OF fR] by simp
  have "gbin_join (mk_djoin cs cR) (etabc ks cs a) True (etabc kR cR (snd p))
      = etabc (cols_union ks kR) (merge_cols cs cR) (join ks a True kR (snd p))"
    by (rule gbin_join_join[OF fK fR _ _ _ _ _]) (use t tp in auto)
  moreover have "bin_join ks a True kR (snd p) = join ks a True kR (snd p)"
    by (rule bin_join_table[OF eframeD(1)[OF fK] eframeD(1)[OF fR] conjunct1[OF t] conjunct1[OF tp]])
  ultimately show ?thesis using Some fp d
    by (simp add: cols_union_subset[OF sub] merge_cols_sub_left[OF eframeD(2)[OF fK] eframeD(2)[OF fR] sc])
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

definition eandbuf :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> event_data mbuft2 \<Rightarrow>
    (event_data table list \<times> event_data table option list) \<Rightarrow> bool" where
  "eandbuf ks cs kR cR buf dbuf \<longleftrightarrow>
     list_all (ftable ks) (fst buf) \<and>
     fst dbuf = map (etabc ks cs) (fst buf) \<and>
     list_all2 (etres kR cR) (snd buf) (snd dbuf)"

lemma eandbuf_add:
  assumes b: "eandbuf ks cs kR cR buf dbuf" and x: "list_all (ftable ks) xs"
    and y: "list_all2 (etres kR cR) ys dys"
  shows "eandbuf ks cs kR cR (mbuf2_add xs ys buf) (mbuf2_add (map (etabc ks cs) xs) dys dbuf)"
  using assms by (cases buf; cases dbuf) (auto simp: eandbuf_def list_all2_appendI)

lemma eandbuf_take:
  assumes fK: "eframe ks cs" and fR: "eframe kR cR" and sub: "set kR \<subseteq> set ks"
    and bf: "eandbuf ks cs kR cR buf dbuf"
    and t: "mbuf2_take (\<lambda>r1 (V, r2). bin_join ks r1 True V r2) buf = (zs, buf')"
  shows "\<exists>dbuf'. mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> gbin_join (mk_djoin cs cR) r1 True z) dbuf
      = (map (etabc ks cs) zs, dbuf') \<and> eandbuf ks cs kR cR buf' dbuf'"
proof -
  obtain b1 b2 where bu: "buf = (b1, b2)" by (cases buf)
  obtain c1 c2 where bu': "buf' = (c1, c2)" by (cases buf')
  have l1: "list_all (ftable ks) b1" and d1: "fst dbuf = map (etabc ks cs) b1"
    and q: "list_all2 (etres kR cR) b2 (snd dbuf)"
    using bf bu by (auto simp: eandbuf_def)
  have eq: "\<And>a p q. a \<in> set b1 \<Longrightarrow> etres kR cR p q \<Longrightarrow>
      (case q of None \<Rightarrow> etabc ks cs a | Some z \<Rightarrow> gbin_join (mk_djoin cs cR) (etabc ks cs a) True z)
        = etabc ks cs ((\<lambda>r1 (V, r2). bin_join ks r1 True V r2) a p)"
  proof -
    fix a p q assume au: "a \<in> set b1" and dr: "etres kR cR p q"
    have ta: "ftable ks a" using l1 au by (simp add: list_all_iff)
    show "(case q of None \<Rightarrow> etabc ks cs a
          | Some z \<Rightarrow> gbin_join (mk_djoin cs cR) (etabc ks cs a) True z)
        = etabc ks cs ((\<lambda>r1 (V, r2). bin_join ks r1 True V r2) a p)"
      using etres_join[OF fK fR sub ta dr] by (simp add: case_prod_beta)
  qed
  obtain dys' where r: "mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> gbin_join (mk_djoin cs cR) r1 True z) (map (etabc ks cs) b1, snd dbuf)
      = (map (etabc ks cs) zs, (map (etabc ks cs) c1, dys'))"
    and q': "list_all2 (etres kR cR) c2 dys'"
    using mbuf2_take_rel2[where h = "etabc ks cs" and m = "etabc ks cs"
        and Q = "etres kR cR" and f = "\<lambda>r1 (V, r2). bin_join ks r1 True V r2"
        and g = "\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> gbin_join (mk_djoin cs cR) r1 True z"
        and xs = b1 and ys = b2 and dys = "snd dbuf" and zs = zs and xs' = c1 and ys' = c2,
        OF eq q t[unfolded bu bu']] by blast
  have sc: "set c1 \<subseteq> set b1" using mbuf2_take_sub t bu bu' by blast
  have du: "dbuf = (map (etabc ks cs) b1, snd dbuf)" using d1 by (cases dbuf) simp
  show ?thesis using r q' sc l1 bu'
    by (intro exI[where x = "(map (etabc ks cs) c1, dys')"])
      (subst du, auto simp: eandbuf_def list_all_iff)
qed

lemma tok_weak:
  "tok cR cL args \<Longrightarrow> eframe kR cR \<Longrightarrow> eframe kL cL \<Longrightarrow>
     mem (args_ivl args) 0 \<or> (args_pos args \<and> set kL = set kR)"
  by (auto simp: tok_def eframe_def)

text \<open>One firing of the fused node's trigger structure.  It differs from the standalone node's
  only in what each step appends: the kernel keeps the read's column list beside its table, and
  the executable side keeps the empty window as @{term None}.\<close>

lemma eandtrigger_step_rel:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and ok: "tok cR cL args"
    and rel: "etrigger_rel kR cR kL cL args tw aux daux buf dbuf nts"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and st: "sorted tss" and bnd: "\<forall>v \<in> set tss. tw \<le> v"
    and we: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
        let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
        in (zs @ [(fv_z, z)], ax)) ([], aux) (mbuf2_add as bs buf) (nts @ tss)
      = ((zs, aux1), buf1, nts1)"
    and de: "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
        let ax = gupdate_mmtaux (eargs cR cL args) t r1 r2 ax
        in (ws @ [if gmmtaux_empty ax then None
                  else Some (gresult_mmtaux (eargs cR cL args) ax)], ax)) ([], daux)
        (mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) (nts @ tss)
      = ((dzs, daux1), dbuf1, dnts1)"
  shows "list_all2 (etres kR cR) zs dzs \<and> dnts1 = nts1 \<and>
     etrigger_rel kR cR kL cL args (enext tw tss) aux1 daux1 buf1 dbuf1 nts1"
proof -
  obtain cur auxlist where vw: "valid_mmtaux args cur aux auxlist"
    and wf: "\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r"
    and vd: "etaux kL cL kR cR args cur daux auxlist" and ctw: "cur \<le> tw"
    and lu: "list_all (ftable kL) (fst buf)"
    and lv: "list_all (ftable kR) (snd buf)"
    and sn: "sorted nts" and cn: "\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw"
    and dbf: "dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (snd buf))"
    using rel by (rule etrigger_relE)
  obtain b1 b2 where bfs: "buf1 = (b1, b2)" by (cases buf1)
  define us where "us = fst buf @ as"
  define vs where "vs = snd buf @ bs"
  define g where "g = (\<lambda>r1 r2 t (zs :: (cols \<times> event_data table) list, ax).
    let ax = update_mmtaux args t r1 r2 ax; (fv_z, z) = result_mmtaux args ax
    in (zs @ [(fv_z, z)], ax))"
  define gd where "gd = (\<lambda>r1 r2 t (ws :: event_data table option list, ax).
    let ax = gupdate_mmtaux (eargs cR cL args) t r1 r2 ax
    in (ws @ [if gmmtaux_empty ax then None
              else Some (gresult_mmtaux (eargs cR cL args) ax)], ax))"
  define R where "R = (\<lambda>v (pr :: (cols \<times> event_data table) list \<times> event_data mmtaux)
      (dpr :: event_data table option list \<times> event_data gmmtaux).
    (\<exists>al. valid_mmtaux args v (snd pr) al \<and>
       (\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r) \<and>
       etaux kL cL kR cR args v (snd dpr) al) \<and>
     list_all2 (etres kR cR) (fst pr) (fst dpr))"
  have ma: "mbuf2_add as bs buf = (us, vs)" by (cases buf) (simp add: us_def vs_def)
  have mad: "mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf
      = (map (etabc kL cL) us, map (etabc kR cR) vs)"
    using dbf by (cases buf) (simp add: us_def vs_def)
  have lus: "list_all (ftable kL) us" using lu ta by (simp add: us_def)
  have lvs: "list_all (ftable kR) vs" using lv tb by (simp add: vs_def)
  have step: "\<And>a c v w z z'. a \<in> set us \<Longrightarrow> c \<in> set vs \<Longrightarrow> R w z z' \<Longrightarrow> w \<le> v \<Longrightarrow>
      R v (g a c v z) (gd (etabc kL cL a) (etabc kR cR c) v z')"
  proof -
    fix a c v w and z :: "(cols \<times> event_data table) list \<times> event_data mmtaux"
      and z' :: "event_data table option list \<times> event_data gmmtaux"
    assume au: "a \<in> set us" and cv: "c \<in> set vs" and q: "R w z z'" and wv: "w \<le> v"
    have t1: "ftable kL a" using au lus by (simp add: list_all_iff)
    have t2: "ftable kR c" using cv lvs by (simp add: list_all_iff)
    obtain al where vwz: "valid_mmtaux args w (snd z) al"
      and wfz: "\<forall>(t, l, r) \<in> set al. ftable kL l \<and> ftable kR r"
      and vdz: "etaux kL cL kR cR args w (snd z') al"
      using q unfolding R_def by blast
    have fz: "list_all2 (etres kR cR) (fst z) (fst z')" using q unfolding R_def by blast
    define al' where "al' = filter (\<lambda>(t, _). memR (args_ivl args) (v - t)) al @ [(v, a, c)]"
    have vw': "valid_mmtaux args v (update_mmtaux args v a c (snd z)) al'"
      unfolding al'_def
      by (rule valid_update_mmtaux[OF wv _ _ vwz]) (use t1 t2 aL aR in simp_all)
    have wf': "\<forall>(t, l, r) \<in> set al'. ftable kL l \<and> ftable kR r"
      using wfz t1 t2 unfolding al'_def by auto
    have vd': "etaux kL cL kR cR args v
        (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z')) al'"
      unfolding al'_def by (rule etaux_update[OF vdz wv fR fL sub]) (use t1 t2 in simp_all)
    have res: "result_mmtaux args (update_mmtaux args v a c (snd z))
        = trigger_results args v al'" by (rule valid_result_mmtaux[OF vw'])
    have dr: "etres kR cR (result_mmtaux args (update_mmtaux args v a c (snd z)))
        (if gmmtaux_empty (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a)
             (etabc kR cR c) (snd z')) then None
         else Some (gresult_mmtaux (eargs cR cL args)
           (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c)
             (snd z'))))"
    proof (cases "gmmtaux_empty (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a)
        (etabc kR cR c) (snd z'))")
      case True
      then show ?thesis
        unfolding res using etaux_result_empty[OF vd' True]
        by (simp add: etres_def)
    next
      case False
      have nz: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (v - t)) al')"
        using etaux_window[OF vd'] False by (simp add: split_def)
      have lst: "fst (last al') = v" unfolding al'_def by simp
      have ft: "ftable (fst (trigger_results args v al')) (snd (trigger_results args v al'))"
        by (rule conjunct1[OF ftable_trigger_results_weak[OF wf' _ lst aL aR
              eframeD(1)[OF fR] tok_weak[OF ok fR fL]]])
          (simp add: al'_def)
      have fv: "fst (trigger_results args v al') = kR" using nz aR by simp
      have tr: "ftable kR (snd (trigger_results args v al'))" using ft unfolding fv .
      have dres: "gresult_mmtaux (eargs cR cL args)
            (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z'))
          = etabc kR cR (snd (trigger_results args v al'))"
        by (rule etaux_result[OF vd' False fR fL sub aL aR])
      show ?thesis unfolding res using False fv tr dres by (simp add: etres_def)
    qed
    have gz: "g a c v z = (fst z @ [result_mmtaux args (update_mmtaux args v a c (snd z))],
           update_mmtaux args v a c (snd z))"
      by (cases z) (simp add: g_def Let_def case_prod_beta)
    have gdz: "gd (etabc kL cL a) (etabc kR cR c) v z'
        = (fst z' @ [if gmmtaux_empty (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a)
               (etabc kR cR c) (snd z')) then None
             else Some (gresult_mmtaux (eargs cR cL args)
               (gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c)
                 (snd z')))],
           gupdate_mmtaux (eargs cR cL args) v (etabc kL cL a) (etabc kR cR c) (snd z'))"
      by (cases z') (simp add: gd_def Let_def case_prod_beta)
    show "R v (g a c v z) (gd (etabc kL cL a) (etabc kR cR c) v z')"
      unfolding R_def gz gdz fst_conv snd_conv
      using vw' wf' vd' fz dr by (intro conjI exI[where x = al']) (simp_all add: list_all2_appendI)
  qed
  have sts: "sorted (nts @ tss)"
    using sn st cn bnd by (fastforce simp: sorted_append intro: order_trans)
  have cts: "\<forall>v \<in> set (nts @ tss). cur \<le> v" using cn bnd ctw by fastforce
  have bound: "\<forall>v \<in> set (nts @ tss). v \<le> enext tw tss"
    using cn enext_ge[OF bnd] enext_bound[OF st] by fastforce
  have cdn: "cur \<le> enext tw tss" using ctw enext_ge[OF bnd] by simp
  have r0: "R cur ([], aux) ([], daux)" unfolding R_def
    by (intro conjI exI[where x = auxlist]) (use vw wf vd in simp_all)
  have we': "mbuf2T_take g ([], aux) (us, vs) (nts @ tss) = ((zs, aux1), (b1, b2), nts1)"
    using we unfolding ma bfs g_def by simp
  have de': "mbuf2T_take gd ([], daux) (map (etabc kL cL) us, map (etabc kR cR) vs)
      (nts @ tss) = ((dzs, daux1), dbuf1, dnts1)"
    using de unfolding mad gd_def by simp
  have Rr: "(\<exists>u. R u (zs, aux1) (dzs, daux1) \<and> u \<le> enext tw tss \<and> (\<forall>t \<in> set nts1. u \<le> t)) \<and>
      sorted nts1 \<and> set nts1 \<subseteq> set (nts @ tss) \<and> set b1 \<subseteq> set us \<and> set b2 \<subseteq> set vs \<and>
      dbuf1 = (map (etabc kL cL) b1, map (etabc kR cR) b2) \<and> dnts1 = nts1"
    by (rule mbuf2T_take_rel[where R = R and f = g and g = gd and h = "etabc kL cL"
        and k = "etabc kR cR", OF step r0 sts cts bound cdn we' de'])
  obtain u where ru: "R u (zs, aux1) (dzs, daux1)" and ub: "u \<le> enext tw tss"
    and un: "\<forall>t \<in> set nts1. u \<le> t" using Rr by blast
  have sn1: "sorted nts1" and sb1: "set b1 \<subseteq> set us" and sb2: "set b2 \<subseteq> set vs"
    and sub1: "set nts1 \<subseteq> set (nts @ tss)"
    and dbf1: "dbuf1 = (map (etabc kL cL) b1, map (etabc kR cR) b2)"
    and dn1: "dnts1 = nts1" using Rr by blast+
  have lb1: "list_all (ftable kL) b1" using sb1 lus by (auto simp: list_all_iff)
  have lb2: "list_all (ftable kR) b2" using sb2 lvs by (auto simp: list_all_iff)
  obtain al1 where v1: "valid_mmtaux args u aux1 al1"
    and w1: "\<forall>(t, l, r) \<in> set al1. ftable kL l \<and> ftable kR r"
    and d1: "etaux kL cL kR cR args u daux1 al1" using ru unfolding R_def by auto
  have dz: "list_all2 (etres kR cR) zs dzs" using ru unfolding R_def by simp
  have bnd1: "\<forall>v \<in> set nts1. u \<le> v \<and> v \<le> enext tw tss" using un sub1 bound by auto
  have "etrigger_rel kR cR kL cL args (enext tw tss) aux1 daux1 (b1, b2)
      (map (etabc kL cL) b1, map (etabc kR cR) b2) nts1"
    by (rule etrigger_relI[OF v1 w1 d1 ub lb1 lb2 sn1 bnd1])
  then show ?thesis using dz dn1 bfs dbf1 by simp
qed

subsection \<open>The relation itself\<close>

text \<open>
  A node's kernel tables are over the column list the kernel computes for it -- the free
  variables of its formula, in the order @{const Formula.fv_list} lists them -- and the executable ones
  over the same columns in ascending order.  The kernel's own column lists inside a node (the
  operands' columns of a join, the columns a let-bound formula is reordered from) are therefore the
  operands' kernel columns, and the rules below say so.
\<close>

inductive esim :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> ts \<Rightarrow> eformula \<Rightarrow>
    (mmasaux, muaux_dq, event_data mmtaux) mformula \<Rightarrow> bool" where
  EsRel: "eframe ks cs \<Longrightarrow>
    table ks rel \<Longrightarrow>
    esim n ks cs tw (ERel (etabc ks cs rel)) (mformula.MRel rel)"
| EsPredC: "eframe ks cs \<Longrightarrow>
    tms = map Formula.Var [0..<length tms] \<Longrightarrow> ks = [0..<length tms] \<Longrightarrow> cs = ks \<Longrightarrow>
    esim n ks cs tw (EPredS e (length tms)) (mformula.MPred e tms Copy)"
| EsPredS: "eframe ks cs \<Longrightarrow>
    is_simple_pattern tms 0 \<Longrightarrow> cs = smp_cols tms \<Longrightarrow> ks = cs \<Longrightarrow>
    esim n ks cs tw (EPredS e (length tms)) (mformula.MPred e tms Simple)"
| EsPredM: "eframe ks cs \<Longrightarrow>
    ks = pred_cols tms \<Longrightarrow>
    esim n ks cs tw (EPredM e (length tms) tms cs) (mformula.MPred e tms Match)"
| EsAndRel: "eframe ks cs \<Longrightarrow>
    esim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
    Formula.fv_trm t1 \<subseteq> set cs \<Longrightarrow> Formula.fv_trm t2 \<subseteq> set cs \<Longrightarrow>
    esim n ks cs tw (EAndRel \<phi>d (reindex_constraint cs (t1, p, c, t2)))
      (mformula.MAndRel ks \<phi> (t1, p, c, t2))"
| EsNeg: "esim n [] [] tw \<phi>d \<phi> \<Longrightarrow>
    esim n [] [] tw (ENeg \<phi>d) (mformula.MNeg \<phi>)"
| EsExists: "eframe ks cs \<Longrightarrow>
    esim (Suc n) kks ccs tw \<phi>d \<phi> \<Longrightarrow> ks = ex_cols kks \<Longrightarrow> cs = eex_cols ccs \<Longrightarrow> b = ex_drop0 ccs \<Longrightarrow>
    esim n ks cs tw (EExists \<phi>d b) (mformula.MExists kks \<phi>)"
| EsOr: "eframe ks cs \<Longrightarrow>
    esim n ks cs tw \<phi>d \<phi> \<Longrightarrow> esim n k2 cs tw \<psi>d \<psi> \<Longrightarrow>
    ebuf2 ks cs k2 cs buf (rbuf2 dbuf) \<Longrightarrow>
    esim n ks cs tw (EOr \<phi>d \<psi>d dbuf) (mformula.MOr ks \<phi> k2 \<psi> buf)"
| EsAnd: "eframe ks cs \<Longrightarrow>
    esim n k1 c1 tw \<phi>d \<phi> \<Longrightarrow> esim n k2 c2 tw \<psi>d \<psi> \<Longrightarrow>
    ks = cols_union k1 k2 \<Longrightarrow> cs = merge_cols c1 c2 \<Longrightarrow> pl = mk_djoin c1 c2 \<Longrightarrow>
    (\<not> pos \<Longrightarrow> set c2 \<subseteq> set c1) \<Longrightarrow>
    ebuf2 k1 c1 k2 c2 buf (rbuf2 dbuf) \<Longrightarrow>
    esim n ks cs tw (EAnd pl \<phi>d pos \<psi>d dbuf) (mformula.MAnd k1 \<phi> pos k2 \<psi> buf)"
| EsPrev: "eframe ks cs \<Longrightarrow>
    esim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
    Rep_mbuf_t dbuf = map (etabc ks cs) buf \<Longrightarrow>
    Rep_mbuf_t dnts = nts \<Longrightarrow>
    esim n ks cs tw (EPrev I \<phi>d first dbuf dnts) (mformula.MPrev I \<phi> first buf nts)"
| EsNext: "eframe ks cs \<Longrightarrow>
    esim n ks cs tw \<phi>d \<phi> \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    esim n ks cs tw (ENext I \<phi>d first dnts) (mformula.MNext I \<phi> first nts)"
| EsAnds: "eframe ks cs \<Longrightarrow>
    (\<forall>i < length L. esim n ((k0 # kss @ nkss) ! i) ((c0 # css @ nss) ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    length Ld = length L \<Longrightarrow> length (c0 # css @ nss) = length L \<Longrightarrow>
    length kss = length css \<Longrightarrow> length nkss = length nss \<Longrightarrow>
    (\<forall>c \<in> set nss. set c \<subseteq> set (eands_cols c0 css)) \<Longrightarrow>
    cs = eands_cols c0 css \<Longrightarrow>
    ps = eands_plans c0 css \<Longrightarrow> ns = eands_plans (eands_cols c0 css) nss \<Longrightarrow>
    ebufn (k0 # kss @ nkss) (c0 # css @ nss) buf (map Rep_mbuf_t dbuf) \<Longrightarrow>
    esim n ks cs tw (EAnds ps ns Ld dbuf) (mformula.MAnds ks (k0 # kss) nkss L buf)"
| EsAgg: "eframe ks cs \<Longrightarrow>
    esim (length (aggargs_tys args) + n) k0 (agg_cols (length (aggargs_tys args)) gcols) tw \<phi>d \<phi> \<Longrightarrow>
    aggargs_cols args = k0 \<Longrightarrow> aggargs_y args = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow>
    (aggargs_g0 args \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f args) \<subseteq> set k0 \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys args)) k0 \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    esim n ks cs tw (EAgg (aggargs_g0 args) (aggargs_\<omega> args)
        (reindex_trm (agg_cols (length (aggargs_tys args)) gcols) (aggargs_f args))
        (length (aggargs_tys args)) (ins_pos gcols y) \<phi>d) (mformula.MAgg args \<phi>)"
| EsSince: "eframe kR cR \<Longrightarrow>
    esim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> esim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow>
    esince_rel kR cR kL cL args tw aux (rdsx daux) buf (rbufS dbuf) \<Longrightarrow>
    esx_agg (rdsx daux) = None \<Longrightarrow>
    esim n kR cR tw (ESince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
| EsUntil: "eframe kR cR \<Longrightarrow>
    esim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> esim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = None \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow> msk = emsk cR cL \<Longrightarrow>
    euntil_rel kR cR kL cL args tw t aux (rdux daux) buf (rbuf2 dbuf) nts \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    eux_agg (rdux daux) = None \<Longrightarrow>
    esim n kR cR tw (EUntil dags msk \<phi>d \<psi>d dbuf dnts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| EsSinceAgg: "eframe ks cs \<Longrightarrow>
    esim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> esim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow>
    esince_rel kR cR kL cL args tw aux (rdsx daux) buf (rbufS dbuf) \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    esx_agg (rdsx daux) = None \<Longrightarrow>
    esim n ks cs tw (EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
        (length (aggargs_tys ag)) (ins_pos gcols y) (ESince dags \<phi>d \<psi>d dbuf daux))
      (mformula.MSince args \<phi> \<psi> buf aux)"
| EsSinceFused: "eframe ks cs \<Longrightarrow>
    esim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> esim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow>
    esince_rel kR cR kL cL args tw aux (rdsx daux) buf (rbufS dbuf) \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    esx_agg (rdsx daux) = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y) \<Longrightarrow>
    usx_q daux = None \<Longrightarrow>
    esim n ks cs tw (ESince dags \<phi>d \<psi>d dbuf daux) (mformula.MSince args \<phi> \<psi> buf aux)"
| EsSinceGuard: "eframe ks cs \<Longrightarrow>

    esim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> esim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow>
    esince_rel kR cR kL cL args tw aux (rdsx daux) buf (rbufS dbuf) \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    esx_agg (rdsx daux) = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y) \<Longrightarrow>
    Formula.fv_trm t1 \<subseteq> set cs \<Longrightarrow> Formula.fv_trm t2 \<subseteq> set cs \<Longrightarrow>
    usx_q daux = Some (reindex_constraint cs (t1, p, c, t2)) \<Longrightarrow>
    esim n ks cs tw (ESince dags \<phi>d \<psi>d dbuf daux)
      (mformula.MAndRel ks (mformula.MSince args \<phi> \<psi> buf aux) (t1, p, c, t2))"
| EsUntilAgg: "eframe ks cs \<Longrightarrow>
    esim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> esim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow> msk = emsk cR cL \<Longrightarrow>
    euntil_rel kR cR kL cL args tw t aux (rdux daux) buf (rbuf2 dbuf) nts \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    eux_agg (rdux daux) = None \<Longrightarrow>
    esim n ks cs tw (EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
        (length (aggargs_tys ag)) (ins_pos gcols y) (EUntil dags msk \<phi>d \<psi>d dbuf dnts t daux))
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| EsUntilFused: "eframe ks cs \<Longrightarrow>
    esim (args_n args) kL cL tw \<phi>d \<phi> \<Longrightarrow> esim (args_n args) kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow>
    args_agg args = Some ag \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow> msk = emsk cR cL \<Longrightarrow>
    euntil_rel kR cR kL cL args tw t aux (rdux daux) buf (rbuf2 dbuf) nts \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    aggargs_cols ag = kR \<Longrightarrow> aggargs_y ag = y \<Longrightarrow> y \<notin> set gcols \<Longrightarrow> (aggargs_g0 ag \<Longrightarrow> gcols = []) \<Longrightarrow>
    Formula.fv_trm (aggargs_f ag) \<subseteq> set kR \<Longrightarrow>
    cR = agg_cols (length (aggargs_tys ag)) gcols \<Longrightarrow>
    ks = y # shift_cols (length (aggargs_tys ag)) kR \<Longrightarrow> cs = merge_cols gcols [y] \<Longrightarrow>
    eux_agg (rdux daux) = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y) \<Longrightarrow>
    esim n ks cs tw (EUntil dags msk \<phi>d \<psi>d dbuf dnts t daux)
      (mformula.MUntil args \<phi> \<psi> buf nts t aux)"
| EsAndAssign: "eframe ks cs \<Longrightarrow>
    esim n k0 c0 tw \<phi>d \<phi> \<Longrightarrow>
    y \<notin> set k0 \<Longrightarrow> Formula.fv_trm t \<subseteq> set c0 \<Longrightarrow>
    ks = k0 @ [y] \<Longrightarrow> cs = merge_cols c0 [y] \<Longrightarrow>
    esim n ks cs tw (EAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<phi>d)
      (mformula.MAndAssign k0 \<phi> (y, t))"
| EsTP: "eframe ks cs \<Longrightarrow>
    cs = mtrm_ecols mt \<Longrightarrow> ks = cs \<Longrightarrow>
    esim n ks cs tw (ETP mt i) (mformula.MTP mt i)"
| EsTS: "eframe ks cs \<Longrightarrow>
    cs = mtrm_ecols mt \<Longrightarrow> ks = cs \<Longrightarrow>
    esim n ks cs tw (ETS mt) (mformula.MTS mt)"
| EsLet: "eframe ks cs \<Longrightarrow>
    esim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow> esim n ks cs tw \<psi>d \<psi> \<Longrightarrow>
    esim n ks cs tw (ELet p m \<phi>d \<psi>d) (mformula.MLet p m kks \<phi> \<psi>)"
| EsFrz: "eframe ks cs \<Longrightarrow>
    esim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow> esim n ks cs tw \<psi>d \<psi> \<Longrightarrow>
    esim n ks cs tw \<rho>d \<rho> \<Longrightarrow>
    size \<rho>L = size \<rho> \<Longrightarrow> size \<rho>Ld = size \<rho>d \<Longrightarrow> (lv \<noteq> None \<longrightarrow> esim n ks cs tw \<rho>Ld \<rho>L) \<Longrightarrow>
    esim n ks cs tw (EFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s \<rho>d w pR tq (map (etabc ks cs) rb) d po ng lv \<rho>Ld)
      (mformula.MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L)"
| EsLetPast: "eframe ks cs \<Longrightarrow>
    esim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow> esim n ks cs tw \<psi>d \<psi> \<Longrightarrow>
    esim n ks cs tw (ELetPast p m \<phi>d \<psi>d i buf) (mformula.MLetPast p m kks \<phi> \<psi> i buf)"
| EsTrigger: "eframe kR cR \<Longrightarrow>
    esim n kL cL tw \<phi>d \<phi> \<Longrightarrow> esim n kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    mem (args_ivl args) 0 \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow> pl = emb_plan cR cL \<Longrightarrow>
    etrigger_rel kR cR kL cL args tw aux daux buf (rbuf2 dbuf) nts \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    esim n kR cR tw (ETrigger dags pl \<phi>d \<psi>d dbuf dnts daux)
      (mformula.MTrigger args \<phi> \<psi> buf nts aux)"
| EsAndTrigger: "eframe ks cs \<Longrightarrow>
    esim n ks cs tw \<alpha>d \<alpha> \<Longrightarrow> esim n kL cL tw \<phi>d \<phi> \<Longrightarrow> esim n kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow> set kR \<subseteq> set ks \<Longrightarrow>
    args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    tok cR cL args \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow> pl = mk_djoin cs cR \<Longrightarrow>
    eandbuf ks cs kR cR buf1 (rbufo dbf1) \<Longrightarrow>
    etrigger_rel kR cR kL cL args tw aux daux buf2 (rbuf2 dbf2) nts \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    esim n ks cs tw (EAndTrigger pl \<alpha>d dbf1 dags \<phi>d \<psi>d dbf2 dnts daux)
      (mformula.MAndTrigger ks \<alpha> buf1 args \<phi> \<psi> buf2 nts aux)"
| EsMatchP: "eframe ks cs \<Longrightarrow>
    Regex.safe_regex fv rgx_safe_pred Past Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = RPDs mr \<Longrightarrow> dss = map Formula.fv_list \<psi>s \<Longrightarrow>
    length css = length \<psi>s \<Longrightarrow> length L = length \<psi>s \<Longrightarrow> length Ld = length L \<Longrightarrow>
    (\<forall>i < length \<psi>s. eframe (dss ! i) (css ! i)) \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks) \<Longrightarrow>
    (\<forall>i < length L. esim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    pls = map (emb_plan cs) css \<Longrightarrow>
    ebufn dss css buf (map Rep_mbuf_t dbuf) \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    emrd_rel ks cs aux daux \<Longrightarrow>
    esim n ks cs tw (EMatchP (length cs) I mr mrs pls Ld dbuf dnts daux)
      (mformula.MMatchP I ks dss mr mrs L buf nts aux)"
| EsMatchF: "eframe ks cs \<Longrightarrow>
    Regex.safe_regex fv rgx_safe_pred Futu Strict
      (from_mregex mr (\<psi>s :: ty Formula.formula list)) \<Longrightarrow>
    ok (length \<psi>s) mr \<Longrightarrow> set ks = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
    distinct mrs \<Longrightarrow> set mrs = LPDs mr \<Longrightarrow> dss = map Formula.fv_list \<psi>s \<Longrightarrow>
    length css = length \<psi>s \<Longrightarrow> length L = length \<psi>s \<Longrightarrow> length Ld = length L \<Longrightarrow>
    (\<forall>i < length \<psi>s. eframe (dss ! i) (css ! i)) \<Longrightarrow>
    (\<forall>i < length \<psi>s. Formula.fv (\<psi>s ! i) \<subseteq> set ks) \<Longrightarrow>
    (\<forall>i < length L. esim n (dss ! i) (css ! i) tw (Ld ! i) (L ! i)) \<Longrightarrow>
    pls = map (emb_plan cs) css \<Longrightarrow>
    ebufn dss css buf (map Rep_mbuf_t dbuf) \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    emld_rel ks cs \<psi>s css aux daux \<Longrightarrow>
    esim n ks cs tw (EMatchF (length cs) I mr mrs pls Ld dbuf dnts t daux)
      (mformula.MMatchF I ks dss mr mrs L buf nts t aux)"

text \<open>The fact the relation is designed to hand out at every node.\<close>

lemma esim_dframe: "esim n ks cs tw \<phi>d \<phi> \<Longrightarrow> eframe ks cs"
  by (erule esim.cases) (auto simp: eframe_def)

section \<open>The simulation\<close>

lemma ebuf2_add:
  assumes b: "ebuf2 k1 c1 k2 c2 buf dbuf"
    and x: "list_all (ftable k1) xs" and y: "list_all (ftable k2) ys"
  shows "ebuf2 k1 c1 k2 c2 (mbuf2_add xs ys buf)
      (mbuf2_add (map (etabc k1 c1) xs) (map (etabc k2 c2) ys) dbuf)"
  using assms by (cases buf) (auto simp: ebuf2_def)

lemma ebuf2_take:
  assumes b: "ebuf2 k1 c1 k2 c2 buf dbuf"
    and eq: "\<And>a b. ftable k1 a \<Longrightarrow> ftable k2 b \<Longrightarrow> g (etabc k1 c1 a) (etabc k2 c2 b) = etabc ks cs (f a b)"
    and t1: "mbuf2_take f buf = (zs, buf')"
  shows "\<exists>dbuf'. mbuf2_take g dbuf = (map (etabc ks cs) zs, dbuf') \<and> ebuf2 k1 c1 k2 c2 buf' dbuf'"
proof -
  obtain b1 b2 where buf: "buf = (b1, b2)" by (cases buf)
  obtain d1 d2 where buf': "buf' = (d1, d2)" by (cases buf')
  have l1: "list_all (ftable k1) b1" and l2: "list_all (ftable k2) b2"
    and d: "dbuf = (map (etabc k1 c1) b1, map (etabc k2 c2) b2)"
    using b buf by (auto simp: ebuf2_def)
  have "mbuf2_take g (map (etabc k1 c1) b1, map (etabc k2 c2) b2)
      = (map (etabc ks cs) zs, (map (etabc k1 c1) d1, map (etabc k2 c2) d2))"
    using t1 buf buf' l1 l2 by (intro mbuf2_take_map) (auto simp: list_all_iff intro!: eq)
  moreover have "set d1 \<subseteq> set b1" "set d2 \<subseteq> set b2"
    using mbuf2_take_sub[of f b1 b2 zs d1 d2] t1 buf buf' by auto
  ultimately show ?thesis using d l1 l2 buf' by (auto simp: ebuf2_def list_all_iff)
qed

subsection \<open>The multi-way buffer of reordered tables\<close>

lemma map2_apply_etabcs:
  "length kss = length as \<Longrightarrow> length css = length as \<Longrightarrow>
     map2 (\<lambda>h a. h a) (map2 etabc kss css) as = etabcs kss css as"
  by (rule nth_equalityI) simp_all

lemma ebufn_add:
  assumes b: "ebufn kss css buf dbuf" and l: "length xss = length css"
    and t: "\<forall>i < length css. list_all (ftable (kss ! i)) (xss ! i)"
  shows "ebufn kss css (mbufn_add xss buf)
      (mbufn_add (map2 map (map2 etabc kss css) xss) dbuf)"
proof -
  have lb: "length buf = length css" and lk: "length kss = length css"
    and lt: "\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)"
    and d: "dbuf = map2 map (map2 etabc kss css) buf"
    using b by (auto simp: ebufn_def)
  have "\<forall>i < length css. list_all (ftable (kss ! i)) (mbufn_add xss buf ! i)"
    using lt t lb l by (auto simp: list_all_iff)
  moreover have "mbufn_add (map2 map (map2 etabc kss css) xss) dbuf
      = map2 map (map2 etabc kss css) (mbufn_add xss buf)"
    unfolding d by (rule mbufn_add_map2[symmetric]) (use lb l lk in simp_all)
  ultimately show ?thesis using lb l lk by (simp add: ebufn_def)
qed

lemma ebufn_take:
  fixes f g :: "event_data table list \<Rightarrow> event_data table"
    and buf buf' dbuf :: "event_data mbufn" and zs :: "event_data table list"
  assumes b: "ebufn kss css buf dbuf"
    and eq: "\<And>as :: event_data table list. length as = length css \<Longrightarrow>
        (\<forall>i < length css. ftable (kss ! i) (as ! i)) \<Longrightarrow>
        etabc ks cs (f as) = g (etabcs kss css as)"
    and t: "mbufn_take (\<lambda>as zs. zs @ [f as]) [] buf = (zs, buf')"
  shows "\<exists>dbuf'. mbufn_take (\<lambda>as zs. zs @ [g as]) [] dbuf = (map (etabc ks cs) zs, dbuf')
      \<and> ebufn kss css buf' dbuf'"
proof -
  have lb: "length buf = length css" and lk: "length kss = length css"
    and lt: "\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)"
    and d: "dbuf = map2 map (map2 etabc kss css) buf"
    using b by (auto simp: ebufn_def)
  define hs :: "(event_data table \<Rightarrow> event_data table) list"
    where "hs = map2 etabc kss css"
  define Ss :: "event_data table set list"
    where "Ss = map (\<lambda>k. {T. ftable k T}) kss"
  obtain w2 buf2 where e2: "mbufn_take (\<lambda>as zs. zs @ [g as])
      ([] :: event_data table list) dbuf = (w2, buf2)"
    by (cases "mbufn_take (\<lambda>as zs. zs @ [g as]) ([] :: event_data table list) dbuf") auto
  have sub: "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i"
    using lt lb lk by (auto simp: Ss_def list_all_iff)
  have step: "\<And>as :: event_data table list. \<And>u u' :: event_data table list.
      length as = length hs \<Longrightarrow>
      (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> u' = map (etabc ks cs) u \<Longrightarrow>
      u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (etabc ks cs) (u @ [f as])"
  proof -
    fix as u u' :: "event_data table list"
    assume la: "length as = length hs"
      and ma: "\<forall>i < length as. as ! i \<in> Ss ! i" and mu: "u' = map (etabc ks cs) u"
    have la': "length as = length css" using la lk by (simp add: hs_def)
    have ma': "\<forall>i < length css. ftable (kss ! i) (as ! i)"
      using ma la' lk by (auto simp: Ss_def)
    show "u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (etabc ks cs) (u @ [f as])"
      using mu eq[OF la' ma'] la' lk by (simp add: hs_def map2_apply_etabcs)
  qed
  have r: "(w2 = map (etabc ks cs) zs) \<and> buf2 = map2 map hs buf'"
  proof (rule mbufn_take_rel[where R = "\<lambda>u u'. u' = map (etabc ks cs) u" and Ss = Ss
        and hs = hs and f = "\<lambda>as zs. zs @ [f as]" and g = "\<lambda>as zs. zs @ [g as]"
        and z = "[]" and z' = "[]" and buf = buf and buf' = buf' and w = zs])
    show "length hs = length buf" using lb lk by (simp add: hs_def)
    show "length Ss = length buf" using lb lk by (simp add: Ss_def)
    show "\<forall>i < length buf. set (buf ! i) \<subseteq> Ss ! i" by (rule sub)
    show "\<And>as u u'. length as = length hs \<Longrightarrow>
        (\<forall>i < length as. as ! i \<in> Ss ! i) \<Longrightarrow> u' = map (etabc ks cs) u \<Longrightarrow>
        u' @ [g (map2 (\<lambda>h a. h a) hs as)] = map (etabc ks cs) (u @ [f as])"
      by (rule step)
    show "([] :: event_data table list) = map (etabc ks cs) []" by simp
    show "mbufn_take (\<lambda>as zs. zs @ [f as]) [] buf = (zs, buf')" by (rule t)
    show "mbufn_take (\<lambda>as zs. zs @ [g as]) [] (map2 map hs buf) = (w2, buf2)"
      using e2 d by (simp add: hs_def)
  qed
  have ls: "length buf' = length buf"
    and ss: "\<forall>i < length buf. set (buf' ! i) \<subseteq> set (buf ! i)"
    using mbufn_take_sub[OF t] by auto
  have "ebufn kss css buf' buf2"
    using lt lb lk ls ss r by (fastforce simp: ebufn_def hs_def list_all_iff)
  then show ?thesis using e2 r by auto
qed

text \<open>The timestamped take, which the two match nodes use, keeps the buffers related in the same
  way; the accumulator is a parameter here because the past node threads a pair of the reported
  tables and the structure, and the future node the structure alone.\<close>

lemma ebufn_nt_take:
  assumes b: "ebufn kss css buf dbuf"
    and st: "\<And>as u u' t. length as = length css \<Longrightarrow>
        (\<forall>i < length css. ftable (kss ! i) (as ! i)) \<Longrightarrow> R u u' \<Longrightarrow>
        R (f as t u) (g (etabcs kss css as) t u')"
    and rz: "R z z'"
    and e: "mbufnt_take f z buf t0 tss = (w, buf', t', tss')"
  shows "\<exists>w2 dbuf'. mbufnt_take g z' dbuf t0 tss = (w2, dbuf', t', tss')
      \<and> R w w2 \<and> ebufn kss css buf' dbuf'"
proof -
  have lb: "length buf = length css" and lk: "length kss = length css"
    and lt: "\<forall>i < length css. list_all (ftable (kss ! i)) (buf ! i)"
    and d: "dbuf = map2 map (map2 etabc kss css) buf"
    using b by (auto simp: ebufn_def)
  define hs :: "(event_data table \<Rightarrow> event_data table) list"
    where "hs = map2 etabc kss css"
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
      using st[OF la' ma' ru] la' lk by (simp add: hs_def map2_apply_etabcs)
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
  have "ebufn kss css buf' buf2"
    using lt lb lk ls ss r by (fastforce simp: ebufn_def hs_def list_all_iff)
  then show ?thesis using e2 r by auto
qed

subsection \<open>The queues the nodes keep\<close>

text \<open>A node keeps its buffers in queues, and the relation is stated on the lists they represent.
  Each queue operation commutes with the representation, so a step of a queue is a step of the
  list it represents.\<close>

lemma ebuf2_estep:
  assumes b: "ebuf2 k1 c1 k2 c2 buf (rbuf2 dbuf)"
    and x: "list_all (ftable k1) xs" and y: "list_all (ftable k2) ys"
    and eq: "\<And>a b. ftable k1 a \<Longrightarrow> ftable k2 b \<Longrightarrow> g (etabc k1 c1 a) (etabc k2 c2 b) = etabc ks cs (f a b)"
    and t1: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
  shows "\<exists>dbuf'. mebuf2_take g (mebuf2_add (map (etabc k1 c1) xs) (map (etabc k2 c2) ys) dbuf)
      = (map (etabc ks cs) zs, dbuf') \<and> ebuf2 k1 c1 k2 c2 buf' (rbuf2 dbuf')"
proof -
  let ?B = "mebuf2_add (map (etabc k1 c1) xs) (map (etabc k2 c2) ys) dbuf"
  have a: "ebuf2 k1 c1 k2 c2 (mbuf2_add xs ys buf) (rbuf2 ?B)"
    using ebuf2_add[OF b x y] by (simp only: mbuf2_add_rbuf2)
  obtain dbuf'' where t: "mbuf2_take g (rbuf2 ?B) = (map (etabc ks cs) zs, dbuf'')"
    and r: "ebuf2 k1 c1 k2 c2 buf' dbuf''"
    using ebuf2_take[OF a eq t1] by blast
  obtain zs' dbuf' where e: "mebuf2_take g ?B = (zs', dbuf')"
    by (metis surj_pair)
  have "(zs', rbuf2 dbuf') = (map (etabc ks cs) zs, dbuf'')"
    using t e by (simp only: mbuf2_take_rbuf2 prod.case)
  then show ?thesis
    using r e by auto
qed

lemma ebufn_eadd:
  assumes "ebufn kss css buf (map Rep_mbuf_t dbuf)" and "length xss = length css"
    and "\<forall>i < length css. list_all (ftable (kss ! i)) (xss ! i)"
  shows "ebufn kss css (mbufn_add xss buf)
      (map Rep_mbuf_t (mebufn_add (map2 map (map2 etabc kss css) xss) dbuf))"
  using ebufn_add[OF assms] by (simp only: mbufn_add_rbl)

lemma uedsx_eval_since_rel:
  assumes "esx_eval_since dags [] (mbuf2S_add Xs Ys ts (rbufS dbuf)) (rdsx daux) = (dzs, dbf2, daux2)"
  obtains ub ua where
    "uedsx_eval_since dags [] (mebuf2S_add Xs Ys ts dbuf) daux = (map (ufilt (usx_q daux)) dzs, ub, ua)"
    and "rbufS ub = dbf2" and "rdsx ua = daux2" and "usx_q ua = usx_q daux"
proof -
  obtain zs ub ua where e: "uedsx_eval_since dags [] (mebuf2S_add Xs Ys ts dbuf) daux = (zs, ub, ua)"
    by (metis prod_cases3)
  have a: "esx_eval_since dags [] (rbufS (mebuf2S_add Xs Ys ts dbuf)) (rdsx daux) = (dzs, dbf2, daux2)"
    using assms by (simp only: mbuf2S_add_rbufS)
  have "(map (ufilt (usx_q daux)) dzs, dbf2, daux2) = (zs, rbufS ub, rdsx ua)"
    using esx_eval_since_rdsx0[where args = dags and buf = "mebuf2S_add Xs Ys ts dbuf" and aux = daux] a e
    by simp
  then show ?thesis
    using that e usx_q_uedsx_eval_since'[OF e] by simp
qed

lemma mebufnt_take_obtain:
  assumes "mbufnt_take f z (map Rep_mbuf_t B) t0 (Rep_mbuf_t Q @ ts) = (z', b', t', n')"
  obtains ub un where "mebufnt_take f z B t0 (Q @@ ts) = (z', ub, t', un)"
    and "map Rep_mbuf_t ub = b'" and "Rep_mbuf_t un = n'"
proof -
  obtain z'' ub t'' un where e: "mebufnt_take f z B t0 (Q @@ ts) = (z'', ub, t'', un)"
    by (metis prod_cases4)
  show ?thesis
    using assms e that by (simp add: mbufnt_take_rbl del: mbufnt_take.simps mebufnt_take.simps)
qed

lemma mebufnt_take_matchP_obtain:
  assumes "mbufnt_take (\<lambda>rels t (zs, ax). let (z, ax) = gupdate_matchP msks I mr mrs rels t ax
      in (zs @ [z], ax)) ([], a0) (map Rep_mbuf_t B) t0 (Rep_mbuf_t Q @ ts) = (w, b', t', n')"
  obtains uzs a' ub un where "mebufnt_take (\<lambda>rels t (zs, ax).
      let (z, ax) = gupdate_matchP msks I mr mrs rels t ax in (zs @@ [z], ax))
      (mbuf_t_empty, a0) B t0 (Q @@ ts) = ((uzs, a'), ub, t', un)"
    and "w = (Rep_mbuf_t uzs, a')" and "map Rep_mbuf_t ub = b'" and "Rep_mbuf_t un = n'"
proof -
  obtain uzs a' ub t'' un where e: "mebufnt_take (\<lambda>rels t (zs, ax).
      let (z, ax) = gupdate_matchP msks I mr mrs rels t ax in (zs @@ [z], ax))
      (mbuf_t_empty, a0) B t0 (Q @@ ts) = ((uzs, a'), ub, t'', un)"
    by (metis prod_cases4 surj_pair)
  show ?thesis
    using assms e that mbufnt_take_matchP[of msks I mr mrs a0 B t0 Q ts]
    by (simp add: Let_def del: mbufnt_take.simps mebufnt_take.simps)
qed

lemma mebuf2T_take_obtain:
  assumes "mbuf2T_take f z (rbuf2 B) (Rep_mbuf_t Q @ ts) = (z', b', n')"
  obtains ub un where "mebuf2T_take f z B (Q @@ ts) = (z', ub, un)"
    and "rbuf2 ub = b'" and "Rep_mbuf_t un = n'"
proof -
  obtain z'' ub un where e: "mebuf2T_take f z B (Q @@ ts) = (z'', ub, un)"
    by (metis prod_cases3)
  show ?thesis
    using assms e that by (simp add: mbuf2T_take_rbuf2 del: mbuf2T_take.simps mebuf2T_take.simps)
qed

lemma mebuf2t_take_until_obtain:
  assumes "mbuf2t_take (eux_add_new dags msk) (rdux A) (rbuf2 B) t (Rep_mbuf_t Q @ ts) = (a', b', t', n')"
  obtains ua ub un where "mebuf2t_take (udux_add_new dags msk) A B t (Q @@ ts) = (ua, ub, t', un)"
    and "rdux ua = a'" and "rbuf2 ub = b'" and "Rep_mbuf_t un = n'"
proof -
  obtain ua ub t'' un where e: "mebuf2t_take (udux_add_new dags msk) A B t (Q @@ ts) = (ua, ub, t'', un)"
    by (metis prod_cases4)
  show ?thesis
    using assms e that by (simp add: mbuf2t_take_until del: mbuf2t_take.simps mebuf2t_take.simps)
qed

subsection \<open>Stepping a list of operands\<close>

lemma esims_tables:
  "(\<forall>i < length L. kgood n (kss ! i) j ts db (L ! i)) \<Longrightarrow> i < length L \<Longrightarrow>
     list_all (ftable (kss ! i)) (fst (meval j n ts db (L ! i)))"
  by (cases "meval j n ts db (L ! i)") (auto intro: kgood_tables)

lemma eeval_list_rel:
  assumes l1: "length Ld = length L" and l2: "length css = length L" and l3: "length kss = length L"
    and la: "\<forall>i < length L. esim n (kss ! i) (css ! i) tw (Ld ! i) (L ! i) \<and>
       (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
          (\<exists>\<psi>d'. eeval j ts db (Ld ! i) = (map (etabc (kss ! i) (css ! i)) as, \<psi>d')
             \<and> esim n (kss ! i) (css ! i) tw' \<psi>d' \<psi>'))"
  shows "length (map (eeval j ts db) Ld) = length L \<and>
   map fst (map (eeval j ts db) Ld)
       = map2 map (map2 etabc kss css) (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
   (\<forall>i < length L. esim n (kss ! i) (css ! i) tw' (map snd (map (eeval j ts db) Ld) ! i)
       (snd (meval j n ts db (L ! i))))"
proof -
  have e: "fst (eeval j ts db (Ld ! i)) = map (etabc (kss ! i) (css ! i)) (fst (meval j n ts db (L ! i)))
      \<and> esim n (kss ! i) (css ! i) tw' (snd (eeval j ts db (Ld ! i))) (snd (meval j n ts db (L ! i)))"
    if i: "i < length L" for i
  proof -
    obtain as \<psi>' where m: "meval j n ts db (L ! i) = (as, \<psi>')" by (cases "meval j n ts db (L ! i)")
    obtain \<psi>d' where "eeval j ts db (Ld ! i) = (map (etabc (kss ! i) (css ! i)) as, \<psi>d')"
      and "esim n (kss ! i) (css ! i) tw' \<psi>d' \<psi>'" using la[rule_format, OF i] m by blast
    then show ?thesis using m by simp
  qed
  show ?thesis using e l1 l2 l3 by (auto intro!: nth_equalityI)
qed

text \<open>
  The operand block shared by the multi-operand nodes: given the induction hypotheses for the
  operands, their executable steps report the reordered tables, stay related, and the buffer
  stays related after adding their results.
\<close>

lemma eeval_operands:
  assumes la: "\<forall>i < length L. esim n (kss ! i) (css ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>j ts. (\<forall>t \<in> set ts. tw \<le> t) \<longrightarrow> (\<forall>db xs \<phi>'.
        meval j n ts db (L ! i) = (xs, \<phi>') \<longrightarrow> size (L ! i) \<le> NN \<longrightarrow>
        kgood n (kss ! i) j ts db (L ! i) \<longrightarrow>
        (\<exists>\<phi>d'. eeval j ts db (Ld ! i) = (map (etabc (kss ! i) (css ! i)) xs, \<phi>d') \<and>
          esim n (kss ! i) (css ! i) (enext tw ts) \<phi>d' \<phi>')))"
    and l1: "length Ld = length L" and l2: "length css = length L" and l3: "length kss = length L"
    and mts: "\<forall>t \<in> set ts. tw \<le> t" and sz: "size_list size L \<le> NN"
    and kgL: "\<forall>i < length L. kgood n (kss ! i) j ts db (L ! i)"
    and bf: "ebufn kss css buf (map Rep_mbuf_t dbuf)"
  shows "length (map (eeval j ts db) Ld) = length L"
    and "map fst (map (eeval j ts db) Ld) = map2 map (map2 etabc kss css) (map fst (map (meval j n ts db) L))"
    and "\<forall>i < length L. esim n (kss ! i) (css ! i) (enext tw ts) (map snd (map (eeval j ts db) Ld) ! i)
      (snd (meval j n ts db (L ! i)))"
    and "ebufn kss css (mbufn_add (map fst (map (meval j n ts db) L)) buf)
      (map Rep_mbuf_t (mebufn_add (map fst (map (eeval j ts db) Ld)) dbuf))"
proof -
  have szL: "size (L ! i) \<le> NN" if i: "i < length L" for i
    by (rule order_trans[OF size_list_estimation'[OF nth_mem[OF i] order.refl, where f = size] sz])
  have la1: "\<forall>i < length L. esim n (kss ! i) (css ! i) tw (Ld ! i) (L ! i) \<and>
      (\<forall>as \<psi>'. meval j n ts db (L ! i) = (as, \<psi>') \<longrightarrow>
         (\<exists>\<psi>d'. eeval j ts db (Ld ! i) = (map (etabc (kss ! i) (css ! i)) as, \<psi>d')
            \<and> esim n (kss ! i) (css ! i) (enext tw ts) \<psi>d' \<psi>'))"
    using la mts szL kgL by blast
  have dlr: "length (map (eeval j ts db) Ld) = length L \<and>
      map fst (map (eeval j ts db) Ld) = map2 map (map2 etabc kss css) (map (\<lambda>\<psi>. fst (meval j n ts db \<psi>)) L) \<and>
      (\<forall>i < length L. esim n (kss ! i) (css ! i) (enext tw ts) (map snd (map (eeval j ts db) Ld) ! i)
          (snd (meval j n ts db (L ! i))))"
    by (rule eeval_list_rel[OF l1 l2 l3 la1])
  then show "length (map (eeval j ts db) Ld) = length L"
    and dl: "map fst (map (eeval j ts db) Ld) = map2 map (map2 etabc kss css) (map fst (map (meval j n ts db) L))"
    and "\<forall>i < length L. esim n (kss ! i) (css ! i) (enext tw ts) (map snd (map (eeval j ts db) Ld) ! i)
      (snd (meval j n ts db (L ! i)))"
    using l1 by (auto simp: comp_def)
  have tabs: "\<forall>i < length css. list_all (ftable (kss ! i)) (map fst (map (meval j n ts db) L) ! i)"
    using esims_tables[OF kgL] l2 by simp
  show "ebufn kss css (mbufn_add (map fst (map (meval j n ts db) L)) buf)
      (map Rep_mbuf_t (mebufn_add (map fst (map (eeval j ts db) Ld)) dbuf))"
    unfolding dl by (rule ebufn_eadd[OF bf _ tabs]) (use l2 in simp)
qed

subsection \<open>One firing of the Since structure\<close>

text \<open>
  One firing of @{const meval_since} on the executable side reports the same windows as one firing on
  the kernel's, and the relation is preserved.  The recursion is driven by the buffer alone, so
  the two sides step in lockstep; the induction is over the kernel's own recursion.
\<close>

lemma eval_since_rel:
  fixes kR cR kL cL :: cols and args :: args
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
  shows "meval_since args rs buf aux = (zs, buf', aux') \<Longrightarrow>
    esx_eval_since (eargs cR cL args) drs dbuf daux = (dzs, dbuf', daux') \<Longrightarrow>
    esince_rel kR cR kL cL args tw aux daux buf dbuf \<Longrightarrow>
    esx_post daux = h \<Longrightarrow>
    esresh kR cR args h rs drs \<Longrightarrow>
    esresh kR cR args h zs dzs \<and> esince_rel kR cR kL cL args tw aux' daux' buf' dbuf' \<and>
    esx_post daux' = h"
proof (induction rs buf aux arbitrary: drs daux dbuf zs buf' aux' dzs dbuf' daux'
    taking: args rule: default_maux.eval_since.induct)
  case (1 rs x xs t tss skew aux)
  note E = 1(1) and D = 1(2) and R = 1(3) and P = 1(4) and S = 1(5)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "esxaux' kR cR cL args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable kL) (x # xs)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (etabc kL cL) (x # xs), map (etabc kR cR) [], t # tss, skew)"
    using R by (rule esince_relE)
  have tx: "table kL x" using lx by simp
  have ctu: "cur \<le> t" using ct by simp
  show ?case
  proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev rs, (x # xs, [], t # tss, skew), aux)" using True by simp
    have DW: "esx_eval_since (eargs cR cL args) drs dbuf daux = (rev drs, dbuf, daux)"
      unfolding dbuf using True by simp
    have EE: "(rev rs, (x # xs, [], t # tss, skew), aux) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev drs, dbuf, daux) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    show ?thesis using EE DD R esresh_rev[OF S] P by auto
  next
    case False
    let ?wa = "gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)"
    let ?da = "esx_join (eargs cR cL args) (etabc kL cL x)
        (esx_add_new_ts (eargs cR cL args) t daux)"
    let ?al = "map (\<lambda>(u, rel). (u, join kR rel (args_pos args) kL x))
        (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
    have vw': "valid_mmasaux args t ?wa ?al"
      using default_mmasaux.valid_join_msaux
          [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu], of x] tx aL aR by simp
    have vd': "esxaux' kR cR cL args t ?da ?al"
      by (rule esxaux'_join[OF esxaux'_add_new_ts[OF vd ctu] fR fL sub tx])
    have res0: "esresh kR cR args h [result_mmasaux args ?wa]
        [esx_result (eargs cR cL args) ?da]"
      using esresh_result[OF vd' vw'] by (simp add: P)
    have res: "esresh kR cR args h (result_mmasaux args ?wa # rs)
        (esx_result (eargs cR cL args) ?da # drs)"
      using esresh_append[OF res0 S] by simp
    have EW: "meval_since args rs (x # xs, [], t # tss, skew) aux
        = (rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa)"
      using False by (simp add: Let_def)
    have DW: "esx_eval_since (eargs cR cL args) drs dbuf daux
        = (rev (esx_result (eargs cR cL args) ?da # drs),
           (map (etabc kL cL) xs, map (etabc kR cR) [], tss, True), ?da)"
      unfolding dbuf using False by (simp add: Let_def)
    have EE: "(rev (result_mmasaux args ?wa # rs), (xs, [], tss, True), ?wa) = (zs, buf', aux')"
      by (rule trans[OF EW[symmetric] E])
    have DD: "(rev (esx_result (eargs cR cL args) ?da # drs),
        (map (etabc kL cL) xs, map (etabc kR cR) [], tss, True), ?da) = (dzs, dbuf', daux')"
      by (rule trans[OF DW[symmetric] D])
    have R': "esince_rel kR cR kL cL args tw ?wa ?da (xs, [], tss, True)
        (map (etabc kL cL) xs, map (etabc kR cR) [], tss, True)"
      by (rule esince_relI[OF vw' vd']) (use lx st ct in auto)
    show ?thesis using EE DD esresh_rev[OF res] R' P by auto
  qed
next
  case (2 rs xs y ys tss aux)
  note IH = 2(1) and E = 2(2) and D = 2(3) and R = 2(4) and P = 2(5) and S = 2(6)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "esxaux' kR cR cL args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable kL) xs"
    and ly: "list_all (ftable kR) (y # ys)"
    and st: "sorted tss" and ct: "\<forall>u \<in> set tss. cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (etabc kL cL) xs, map (etabc kR cR) (y # ys), tss, True)"
    using R by (rule esince_relE)
  have ty: "table kR y" and fy: "finite y" using ly by simp_all
  let ?al = "case auxlist of [] \<Rightarrow> [(cur, y)]
      | ((u, w) # r) \<Rightarrow> if u = cur then (u, w \<union> y) # r else (cur, y) # auxlist"
  have vw': "valid_mmasaux args cur (add_new_table_mmasaux args y aux) ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vw]) (use ty aR in simp)
  have vd': "esxaux' kR cR cL args cur
      (esx_add_new_table (eargs cR cL args) (etabc kR cR y) daux) ?al"
    by (rule esxaux'_add_new_table[OF vd ty fy])
  have E': "meval_since args rs (xs, ys, tss, False) (add_new_table_mmasaux args y aux)
      = (zs, buf', aux')" using E by simp
  have D': "esx_eval_since (eargs cR cL args) drs
      (map (etabc kL cL) xs, map (etabc kR cR) ys, tss, False)
      (esx_add_new_table (eargs cR cL args) (etabc kR cR y) daux)
      = (dzs, dbuf', daux')" using D unfolding dbuf by simp
  have R': "esince_rel kR cR kL cL args tw (add_new_table_mmasaux args y aux)
      (esx_add_new_table (eargs cR cL args) (etabc kR cR y) daux)
      (xs, ys, tss, False) (map (etabc kL cL) xs, map (etabc kR cR) ys, tss, False)"
    by (rule esince_relI[OF vw' vd' ctw]) (use lx ly st ct in auto)
  have P': "esx_post (esx_add_new_table (eargs cR cL args) (etabc kR cR y) daux) = h"
    using P by simp
  show ?case by (rule IH[OF E' D' R' P' S])
next
  case (3 rs x xs y ys t tss aux)
  note IH = 3(1) and E = 3(2) and D = 3(3) and R = 3(4) and P = 3(5) and S = 3(6)
  obtain cur auxlist where vw: "valid_mmasaux args cur aux auxlist"
    and vd: "esxaux' kR cR cL args cur daux auxlist"
    and ctw: "cur \<le> tw"
    and lx: "list_all (ftable kL) (x # xs)"
    and ly: "list_all (ftable kR) (y # ys)"
    and st: "sorted (t # tss)"
    and ct: "\<forall>u \<in> set (t # tss). cur \<le> u \<and> u \<le> tw"
    and dbuf: "dbuf = (map (etabc kL cL) (x # xs), map (etabc kR cR) (y # ys), t # tss, False)"
    using R by (rule esince_relE)
  have tx: "table kL x" using lx by simp
  have ty: "table kR y" and fy: "finite y" using ly by simp_all
  have ctu: "cur \<le> t" using ct by simp
  let ?jl = "map (\<lambda>(u, rel). (u, join kR rel (args_pos args) kL x))
      (filter (\<lambda>(u, rel). memR (args_ivl args) (t - u)) auxlist)"
  let ?al = "case ?jl of [] \<Rightarrow> [(t, y)]
      | ((u, w) # r) \<Rightarrow> if u = t then (u, w \<union> y) # r else (t, y) # ?jl"
  let ?wa = "add_new_table_mmasaux args y
      (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux))"
  let ?da = "esx_add_new_table (eargs cR cL args) (etabc kR cR y)
      (esx_join (eargs cR cL args) (etabc kL cL x)
        (esx_add_new_ts (eargs cR cL args) t daux))"
  have vwj: "valid_mmasaux args t (gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)) ?jl"
    using default_mmasaux.valid_join_msaux
        [OF default_mmasaux.valid_add_new_ts_msaux[OF vw ctu], of x] tx aL aR by simp
  have vdj: "esxaux' kR cR cL args t
      (esx_join (eargs cR cL args) (etabc kL cL x)
        (esx_add_new_ts (eargs cR cL args) t daux)) ?jl"
    by (rule esxaux'_join[OF esxaux'_add_new_ts[OF vd ctu] fR fL sub tx])
  have vw': "valid_mmasaux args t ?wa ?al"
    by (rule default_mmasaux.valid_add_new_table_msaux[OF vwj]) (use ty aR in simp)
  have vd': "esxaux' kR cR cL args t ?da ?al"
    by (rule esxaux'_add_new_table[OF vdj ty fy])
  have res0: "esresh kR cR args h [result_mmasaux args ?wa]
      [esx_result (eargs cR cL args) ?da]"
    using esresh_result[OF vd' vw'] by (simp add: P)
  have res: "esresh kR cR args h (result_mmasaux args ?wa # rs)
      (esx_result (eargs cR cL args) ?da # drs)"
    using esresh_append[OF res0 S] by simp
  have P': "esx_post ?da = h" using P by simp
  have E': "meval_since args (result_mmasaux args ?wa # rs) (xs, ys, tss, False) ?wa
      = (zs, buf', aux')" using E by (simp add: Let_def)
  have D': "esx_eval_since (eargs cR cL args)
      (esx_result (eargs cR cL args) ?da # drs)
      (map (etabc kL cL) xs, map (etabc kR cR) ys, tss, False) ?da = (dzs, dbuf', daux')"
    using D unfolding dbuf by (simp add: Let_def)
  have R': "esince_rel kR cR kL cL args tw ?wa ?da (xs, ys, tss, False)
      (map (etabc kL cL) xs, map (etabc kR cR) ys, tss, False)"
    by (rule esince_relI[OF vw' vd']) (use lx ly st ct in auto)
  show ?case by (rule IH[OF refl E' D' R' P' res])
qed (all \<open>frule esince_relD_buf, simp add: rev_map,
       (intro conjI)?, (rule esresh_rev'; assumption)?\<close>)

text \<open>
  The simulation itself.  Every case is one theorem of @{theory MFODL_Monitor_Exec.Frame}
  applied pointwise to the operand's output list, with @{thm [source] kgood_tables} supplying
  the operand well-formedness: the operands' calls are good when the node's is.
\<close>

text \<open>
  The induction is over the derivation of the simulation, which gives the statement for an
  operand's own derivation.  A node that re-enters the evaluator on an operand's \<^emph>\<open>successor\<close>
  state -- the freeze does -- needs it for a derivation that is not a sub-derivation, so the
  statement carries a bound \<open>NN\<close> on the formula's size and an assumption \<open>Q\<close> giving
  it below that bound.  \<open>esim_deval_bound\<close> closes the loop by induction on the
  bound, and \<open>esim_deval\<close> instantiates it.
\<close>

text \<open>
  A let-bound formula's tables are reordered by the kernel from the formula's columns to the
  positional ones before they enter the database.  The executable formula's are already over the
  positional columns, which are the ascending order of the same set, so the executable table
  \<^emph>\<open>is\<close> the reordered one and the two databases are literally the same.\<close>

lemma etabc_reorder_eq: "distinct ks \<Longrightarrow> table ks T \<Longrightarrow> etabc ks cs T = reorder cs ks T"
  unfolding reorder_def using etabc_same[of ks T] by (auto simp: etabc_def)

text \<open>
  The recursive let runs its bound formula against databases it builds itself, feeding the
  previous round's output back under the bound predicate.  The two runs produce literally the
  same lists, so their states stay in step round by round.  The guard that rejects a round in
  which the formula's size changed never fires on either side, because neither evaluator changes
  its formula's size.
\<close>

lemma letpast_meval0_rel:
  assumes Q: "\<And>tw' \<chi>d \<chi> ts' db' zs' \<chi>'. size \<chi> < NN \<Longrightarrow> esim m kks [0..<m] tw' \<chi>d \<chi> \<Longrightarrow>
      (\<forall>t \<in> set ts'. tw' \<le> t) \<Longrightarrow>
      meval j m ts' db' \<chi> = (zs', \<chi>') \<Longrightarrow> kgood m kks j ts' db' \<chi> \<Longrightarrow>
      \<exists>\<chi>d'. eeval j ts' db' \<chi>d = (map (etabc kks [0..<m]) zs', \<chi>d') \<and>
        esim m kks [0..<m] (enext tw' ts') \<chi>d' \<chi>'"
  shows "letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>))
      J i ys xs q ts db \<phi> = (zs, i', bo, \<phi>') \<Longrightarrow>
    snd q = m \<Longrightarrow> size \<phi> < NN \<Longrightarrow> esim m kks [0..<m] tw \<phi>d \<phi> \<Longrightarrow>
    (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> J = j \<Longrightarrow> lpgood m kks j i ys xs q ts db \<phi> \<Longrightarrow>
    \<exists>\<phi>d'. letpast_meval0 (eeval j) J i ys xs q ts db \<phi>d = (zs, i', bo, \<phi>d')
      \<and> esim m kks [0..<m] (enext tw ts) \<phi>d' \<phi>'"
proof (induct "\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>)"
    J i ys xs q ts db \<phi> arbitrary: zs i' bo \<phi>' tw \<phi>d rule: letpast_meval0.induct)
  case (1 J i ys xs q ts db \<phi>)
  note IH = 1(1) and E = 1(2) and SQ = 1(3) and SZ = 1(4) and SIM = 1(5)
    and B = 1(6) and JJ = 1(7) and LP = 1(8)
  obtain p where q: "q = (p, m)" using SQ by (cases q) auto
  have kgc: "kgood m kks j ts (Mapping.update q xs db) \<phi>"
    using lpgood_call[OF LP[unfolded q]] q by simp
  obtain ys0 \<phi>2 where ev0: "meval j m ts (Mapping.update q xs db) \<phi> = (ys0, \<phi>2)"
    by (cases "meval j m ts (Mapping.update q xs db) \<phi>")
  define ys' where "ys' = map (reorder [0..<m] kks) ys0"
  have ev: "apfst (map (reorder [0..<m] kks)) (meval j m ts (Mapping.update q xs db) \<phi>) = (ys', \<phi>2)"
    using ev0 by (simp add: ys'_def)
  obtain \<phi>d2 where dv0: "eeval j ts (Mapping.update q xs db) \<phi>d = (map (etabc kks [0..<m]) ys0, \<phi>d2)"
    and s2: "esim m kks [0..<m] (enext tw ts) \<phi>d2 \<phi>2"
    using Q[OF SZ SIM B ev0 kgc] by blast
  have fk: "eframe kks [0..<m]" by (rule esim_dframe[OF SIM])
  have ty0: "list_all (ftable kks) ys0"
    by (rule kgood_tables[OF kgc ev0])
  have dv: "eeval j ts (Mapping.update q xs db) \<phi>d = (ys', \<phi>d2)"
    using dv0 ty0 etabc_reorder_eq[OF eframeD(1)[OF fk]] unfolding ys'_def
    by (auto simp: list_all_iff intro!: map_cong)
  have same: "\<not> size \<phi>2 \<noteq> size \<phi>"
    using default_maux.size_snd_meval[of j m ts "Mapping.update q xs db" \<phi>] ev0 by simp
  have dsame: "\<not> size \<phi>d2 \<noteq> size \<phi>d"
    using size_snd_eeval[of j ts "Mapping.update q xs db" \<phi>d] dv by simp
  have szp: "size \<phi>2 < NN" using same SZ by simp
  show ?case
  proof (cases ys')
    case Nil
    have "zs = ys @ ys' \<and> i' = i + length xs \<and> bo = None \<and> \<phi>' = \<phi>2"
      using E ev same Nil by (simp add: letpast_meval0.simps)
    moreover have "letpast_meval0 (eeval j) J i ys xs q ts db \<phi>d
        = (ys @ ys', i + length xs, None, \<phi>d2)"
      using dv dsame Nil by (simp add: letpast_meval0.simps)
    ultimately show ?thesis using s2 by auto
  next
    case (Cons y r)
    show ?thesis
    proof (cases "J \<le> Suc (i + length xs)")
      case True
      have "zs = ys @ ys' \<and> i' = i + length xs \<and> bo = Some y \<and> \<phi>' = \<phi>2"
        using E ev same Cons True by (simp add: letpast_meval0.simps)
      moreover have "letpast_meval0 (eeval j) J i ys xs q ts db \<phi>d
          = (ys @ ys', i + length xs, Some y, \<phi>d2)"
        using dv dsame Cons True by (simp add: letpast_meval0.simps)
      ultimately show ?thesis using s2 by auto
    next
      case cont: False
      have e': "letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>))
          J (i + length xs) (ys @ ys') ys' q []
          (Mapping.map_values (\<lambda>_ _. []) db) \<phi>2 = (zs, i', bo, \<phi>')"
        using E ev same Cons cont by (simp add: letpast_meval0.simps)
      have LP': "lpgood m kks j (i + length xs) (ys @ ys') ys' q [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>2"
        using lpgood_step[OF LP[unfolded q] ev[unfolded q]] Cons cont JJ q by simp
      have d': "letpast_meval0 (eeval j) J i ys xs q ts db \<phi>d
          = letpast_meval0 (eeval j) J (i + length xs) (ys @ ys') ys' q []
              (Mapping.map_values (\<lambda>_ _. []) db) \<phi>d2"
        using dv dsame Cons cont by (simp add: letpast_meval0.simps)
      have "\<exists>\<phi>d''. letpast_meval0 (eeval j) J (i + length xs) (ys @ ys') ys' q []
            (Mapping.map_values (\<lambda>_ _. []) db) \<phi>d2 = (zs, i', bo, \<phi>d'')
          \<and> esim m kks [0..<m] (enext (enext tw ts) []) \<phi>d'' \<phi>'"
        by (rule IH[OF ev[symmetric] refl same Cons cont e' SQ szp s2]) (use JJ LP' in auto)
      then show ?thesis using d' by (auto simp: enext_def)
    qed
  qed
qed

text \<open>One firing of the multi-way join: the operands at their own columns, split into the
  positive and the negative ones, as @{thm [source] gmulti_join_eq} takes them.\<close>

lemma map2_zip_etabcs:
  "length K = length as \<Longrightarrow> length C = length as \<Longrightarrow>
     map2 (\<lambda>(k, c). etabc k c) (zip K C) as = etabcs K C as"
  by (rule nth_equalityI) auto

lemma eands_step:
  assumes fs: "\<forall>i < length (c0 # css @ nss). eframe ((k0 # kss @ nkss) ! i) ((c0 # css @ nss) ! i)"
    and lk: "length kss = length css" and lnk: "length nkss = length nss"
    and sb: "\<forall>c \<in> set nss. set c \<subseteq> set (eands_cols c0 css)"
    and fK: "eframe ks (eands_cols c0 css)"
    and las: "length (as :: event_data table list) = length (c0 # css @ nss)"
    and mas: "\<forall>i < length (c0 # css @ nss). ftable ((k0 # kss @ nkss) ! i) (as ! i)"
  shows "etabc ks (eands_cols c0 css) (mmulti_join ks (k0 # kss) nkss as)
    = gmulti_join (eands_plans c0 css) (eands_plans (eands_cols c0 css) nss)
        (etabcs (k0 # kss @ nkss) (c0 # css @ nss) as)"
proof -
  obtain T0 r where a0: "as = T0 # r" using las by (cases as) auto
  have lr: "length r = length css + length nss" using las a0 by simp
  define Us where "Us = take (length css) r"
  define Vs where "Vs = drop (length css) r"
  have uv: "r = Us @ Vs" by (simp add: Us_def Vs_def)
  have lu: "length Us = length css" using lr by (simp add: Us_def)
  have lv: "length Vs = length nss" using lr by (simp add: Vs_def)
  have f0: "eframe k0 c0" using fs[rule_format, of 0] by simp
  have t0: "table k0 T0" and fT0: "finite T0" using mas[rule_format, of 0] a0 by auto
  have fp: "i < length css \<Longrightarrow> eframe (kss ! i) (css ! i)" for i
    using fs[rule_format, of "Suc i"] lk by (simp add: nth_append)
  have fn: "i < length nss \<Longrightarrow> eframe (nkss ! i) (nss ! i)" for i
    using fs[rule_format, of "Suc (length css + i)"] lk by (simp add: nth_append)
  have mp: "i < length css \<Longrightarrow> ftable (kss ! i) (Us ! i)" for i
    using mas[rule_format, of "Suc i"] lk lu unfolding a0 uv by (simp add: nth_append)
  have mn: "i < length nss \<Longrightarrow> ftable (nkss ! i) (Vs ! i)" for i
    using mas[rule_format, of "Suc (length css + i)"] lk lu unfolding a0 uv by (simp add: nth_append)
  have pos: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) (zip kss css) Us"
    using lk lu fp mp by (auto simp: list_all2_conv_all_nth wf_operand_def)
  have neg: "list_all2 (\<lambda>(k, c) U. wf_operand k c U) (zip nkss nss) Vs"
    using lnk lv fn mn by (auto simp: list_all2_conv_all_nth wf_operand_def)
  have sub: "\<forall>c \<in> set (map snd (zip nkss nss)). set c \<subseteq> set (eands_cols c0 (map snd (zip kss css)))"
    using sb lk lnk by simp
  have fd: "eframe (kands_cols k0 kss) (eands_cols c0 css)"
    by (rule eframe_eands_cols[OF _ f0]) (use lk fp in \<open>auto simp: list_all2_conv_all_nth\<close>)
  have cs: "distinct ks" "set ks = set (kands_cols k0 (map fst (zip kss css)))"
    using eframeD(1,3)[OF fK] eframeD(3)[OF fd] lk by simp_all
  have DJ: "gmulti_join (eands_plans c0 (map snd (zip kss css)))
        (eands_plans (eands_cols c0 (map snd (zip kss css))) (map snd (zip nkss nss)))
        (map2 (\<lambda>(k, c). etabc k c) ((k0, c0) # zip kss css @ zip nkss nss) ((T0 # Us) @ Vs))
      = etabc ks (eands_cols c0 (map snd (zip kss css)))
          (mmulti_join ks (k0 # map fst (zip kss css)) (map fst (zip nkss nss)) ((T0 # Us) @ Vs))"
    by (rule gmulti_join_eq[OF f0 t0 fT0 pos neg sub cs])
  have z: "(k0, c0) # zip kss css @ zip nkss nss = zip (k0 # kss @ nkss) (c0 # css @ nss)"
    using lk by simp
  have "map2 (\<lambda>(k, c). etabc k c) ((k0, c0) # zip kss css @ zip nkss nss) as
      = etabcs (k0 # kss @ nkss) (c0 # css @ nss) as"
    unfolding z by (rule map2_zip_etabcs) (use las lk lnk in simp_all)
  then show ?thesis using DJ lk lnk unfolding a0 uv by simp
qed

lemma etabc_neg:
  "map (\<lambda>r. if r = {} then {[]} else {}) (map (etabc [] []) ys)
     = map (etabc [] []) (map (\<lambda>r. if r = empty_table then unit_table else empty_table) ys)"
  by (auto simp: etabc_def restrict_def unit_table_def empty_table_def)

text \<open>One firing of a fused aggregating Since node.  The node reports the aggregated windows,
  read through its guard; the kernel's node reports the windows, which its aggregation then
  aggregates.\<close>

text \<open>One firing of a Since node, whatever the post-processing of its window: the executable
  node's results are the kernel's under the window's post-processing, and the relation carries
  over to the successor states.\<close>

lemma esince_node_rel:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and dag: "dags = eargs cR cL args"
    and rel: "esince_rel kR cR kL cL args tw aux (rdsx daux) buf (rbufS dbuf)"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. tw \<le> t"
    and e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux = (zs, buf2, aux2)"
  obtains dzs ub ua where "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) dzs, ub, ua)"
    and "esresh kR cR args (esx_post (rdsx daux)) zs dzs"
    and "esince_rel kR cR kL cL args (enext tw ts) aux2 (rdsx ua) buf2 (rbufS ub)"
    and "esx_agg (rdsx ua) = esx_agg (rdsx daux)" and "usx_q ua = usx_q daux"
proof -
  obtain dzs dbf2 daux2 where d3: "esx_eval_since dags []
      (mbuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts (rbufS dbuf)) (rdsx daux)
      = (dzs, dbf2, daux2)"
    by (cases "esx_eval_since dags []
      (mbuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts (rbufS dbuf)) (rdsx daux)")
  have radd: "esince_rel kR cR kL cL args (enext tw ts) aux (rdsx daux) (mbuf2S_add as bs ts buf)
      (mbuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts (rbufS dbuf))"
    by (rule esince_rel_add[OF rel ta tb sts mts])
  have step: "esresh kR cR args (esx_post (rdsx daux)) zs dzs \<and>
      esince_rel kR cR kL cL args (enext tw ts) aux2 daux2 buf2 dbf2"
    using eval_since_rel[OF fR fL sub aL aR e3 d3[unfolded dag] radd refl] by (simp add: esresh_def)
  have nag2: "esx_agg daux2 = esx_agg (rdsx daux)"
    using esx_agg_eval_since[OF d3] by simp
  obtain ub ua where "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) dzs, ub, ua)"
    and "rbufS ub = dbf2" and "rdsx ua = daux2" and "usx_q ua = usx_q daux"
    by (rule uedsx_eval_since_rel[OF d3])
  then show ?thesis
    using that step nag2 by simp
qed

text \<open>One firing of an Until node, likewise.\<close>

lemma euntil_node_rel:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
    and dag: "dags = eargs cR cL args" and pe: "msk = emsk cR cL"
    and rel: "euntil_rel kR cR kL cL args tw t aux (rdux daux) buf (rbuf2 dbuf) nts"
    and ne: "Rep_mbuf_t dnts = nts"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and sts: "sorted ts" and mts: "\<forall>u \<in> set ts. tw \<le> u"
    and e3: "mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add as bs buf) t (nts @ ts)
      = (aux1, buf1, nt, nts1)"
    and e4: "eval_muaux_dq args nt aux1 = (zs, aux2)"
  obtains dzs ua ub un ua2 where
    "mebuf2t_take (udux_add_new dags msk) daux
      (mebuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) t (dnts @@ ts) = (ua, ub, nt, un)"
    and "udux_eval dags nt ua = (dzs, ua2)"
    and "esresh kR cR args (eux_post (rdux daux)) zs dzs"
    and "euntil_rel kR cR kL cL args (enext tw ts) nt aux2 (rdux ua2) buf1 (rbuf2 ub) nts1"
    and "Rep_mbuf_t un = nts1" and "eux_agg (rdux ua2) = eux_agg (rdux daux)"
proof -
  obtain daux1 dbuf1 dnt dnts1 where d3: "mbuf2t_take (eux_add_new dags msk) (rdux daux)
      (mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) (rbuf2 dbuf)) t (nts @ ts)
      = (daux1, dbuf1, dnt, dnts1)"
    by (cases "mbuf2t_take (eux_add_new dags msk) (rdux daux)
      (mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) (rbuf2 dbuf)) t (nts @ ts)")
  obtain dzs daux2 where d4: "eux_eval dags dnt daux1 = (dzs, daux2)"
    by (cases "eux_eval dags dnt daux1")
  have step: "esresh kR cR args (eux_post (rdux daux)) zs dzs \<and> dnt = nt \<and> dnts1 = nts1 \<and>
      dbuf1 = (map (etabc kL cL) (fst buf1), map (etabc kR cR) (snd buf1)) \<and>
      euntil_rel kR cR kL cL args (enext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    by (rule until_step_rel[OF fR fL sub aL aR rel ta tb sts mts e3
        d3[unfolded dag pe] e4 d4[unfolded dag]])
  have nag2: "eux_agg daux2 = eux_agg (rdux daux)"
    using eux_agg_mbuf2t_take[OF d3] eux_agg_eval[of dags dnt daux1] d4 by simp
  obtain ua ub un where eu: "mebuf2t_take (udux_add_new dags msk) daux
      (mebuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) t (dnts @@ ts) = (ua, ub, dnt, un)"
    and ua: "rdux ua = daux1" and ub: "rbuf2 ub = dbuf1" and un: "Rep_mbuf_t un = dnts1"
    by (rule mebuf2t_take_until_obtain[OF d3[unfolded mbuf2_add_rbuf2 ne[symmetric]]])
  obtain uzs ua2 where eu2: "udux_eval dags dnt ua = (uzs, ua2)"
    by (cases "udux_eval dags dnt ua")
  have uz: "uzs = dzs" and ua2: "rdux ua2 = daux2"
    using d4 eu2 eux_eval_rdux[of dags dnt ua] unfolding ua by simp_all
  have dnt: "dnt = nt" and dn1: "dnts1 = nts1"
    and db1: "dbuf1 = (map (etabc kL cL) (fst buf1), map (etabc kR cR) (snd buf1))"
    and r: "euntil_rel kR cR kL cL args (enext tw ts) nt aux2 daux2 buf1 dbuf1 nts1"
    using step by blast+
  show ?thesis
    by (rule that[of ua ub un uzs ua2]) (use eu eu2 uz ua2 ub un step nag2 r dnt dn1 in simp_all)
qed

lemma esince_fused_rel:
  assumes fR: "eframe kR cR" and fL: "eframe kL cL" and sub: "set kL \<subseteq> set kR"
    and agg: "args_agg args = Some ag" and aL: "args_L args = kL" and aR: "args_R args = kR"
    and dag: "dags = eargs cR cL args"
    and rel: "esince_rel kR cR kL cL args tw aux (rdsx daux) buf (rbufS dbuf)"
    and kc: "aggargs_cols ag = kR" and ye: "aggargs_y ag = y" and yg: "y \<notin> set gcols"
    and g0: "aggargs_g0 ag \<Longrightarrow> gcols = []" and fv: "Formula.fv_trm (aggargs_f ag) \<subseteq> set kR"
    and cRe: "cR = agg_cols (length (aggargs_tys ag)) gcols"
    and kse: "ks = y # shift_cols (length (aggargs_tys ag)) kR" and cse: "cs = merge_cols gcols [y]"
    and nag: "esx_agg (rdsx daux) = Some (aggargs_g0 ag, aggargs_\<omega> ag, reindex_trm cR (aggargs_f ag),
        length (aggargs_tys ag), ins_pos gcols y)"
    and ta: "list_all (ftable kL) as" and tb: "list_all (ftable kR) bs"
    and sts: "sorted ts" and mts: "\<forall>t \<in> set ts. tw \<le> t"
    and e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux = (zs, buf2, aux2)"
  obtains ub ua where "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) (map (etabc ks cs) zs), ub, ua)"
    and "esince_rel kR cR kL cL args (enext tw ts) aux2 (rdsx ua) buf2 (rbufS ub)"
    and "esx_agg (rdsx ua) = esx_agg (rdsx daux)" and "usx_q ua = usx_q daux"
proof -
  let ?ag = "uagg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
      (length (aggargs_tys ag)) (ins_pos gcols y)"
  obtain dzs ub ua where eu: "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) dzs, ub, ua)"
    and step: "esresh kR cR args (esx_post (rdsx daux)) zs dzs"
    and rel': "esince_rel kR cR kL cL args (enext tw ts) aux2 (rdsx ua) buf2 (rbufS ub)"
    and nag2: "esx_agg (rdsx ua) = esx_agg (rdsx daux)" and uq: "usx_q ua = usx_q daux"
    by (rule esince_node_rel[OF fR fL sub aL aR dag rel ta tb sts mts e3])
  have post: "esx_post (rdsx daux) = ?ag" using nag by (simp add: esx_post_eq)
  have fc: "eframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "dzs = map (etabc ks cs) zs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (?ag \<circ> etabc kR cR) vs"
      using step unfolding post esresh_def by blast
    show ?thesis unfolding v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  show ?thesis
    by (rule that[OF eu[unfolded agc] rel' nag2 uq])
qed

theorem esim_deval_N:
  assumes Q: "\<And>n' ks' cs' tw' \<phi>d' \<chi> j' ts' db' xs' \<chi>'. size \<chi> < NN \<Longrightarrow> esim n' ks' cs' tw' \<phi>d' \<chi> \<Longrightarrow>
      (\<forall>t \<in> set ts'. tw' \<le> t) \<Longrightarrow>
      meval j' n' ts' db' \<chi> = (xs', \<chi>') \<Longrightarrow> kgood n' ks' j' ts' db' \<chi> \<Longrightarrow>
      \<exists>\<phi>d''. eeval j' ts' db' \<phi>d' = (map (etabc ks' cs') xs', \<phi>d'')
        \<and> esim n' ks' cs' (enext tw' ts') \<phi>d'' \<chi>'"
  shows "esim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> size \<phi> \<le> NN \<Longrightarrow>
   kgood n ks j ts db \<phi> \<Longrightarrow>
   \<exists>\<phi>d'. eeval j ts db \<phi>d = (map (etabc ks cs) xs, \<phi>d')
     \<and> esim n ks cs (enext tw ts) \<phi>d' \<phi>'"
proof (induct arbitrary: j ts db xs \<phi>' rule: esim.induct)
  case (EsRel ks cs rel n tw)
  note wf = EsRel.hyps(1) and t = EsRel.hyps(2)
    and kg = EsRel.prems(4) and sts = kgood_sorted[OF EsRel.prems(4)]
    and mts = EsRel.prems(1) and m = EsRel.prems(2)
  have x: "xs = replicate (length ts) rel" and f: "\<phi>' = mformula.MRel rel" using m by simp_all
  show ?case using wf t f by (simp add: x f esim.EsRel)
next
  case (EsPredC ks cs tms n tw e)
  note wf = EsPredC.hyps(1) and tm = EsPredC.hyps(2)
    and kse = EsPredC.hyps(3) and cse = EsPredC.hyps(4) and kg = EsPredC.prems(4)
    and sts = kgood_sorted[OF EsPredC.prems(4)] and mts = EsPredC.prems(1) and m = EsPredC.prems(2)
  have f: "\<phi>' = mformula.MPred e tms Copy" using m by simp
  have t: "list_all (ftable ks) xs" by (rule kgood_tables[OF kg m])
  have mp: "map (etabc ks cs) xs = xs"
    using t etabc_same[OF eframeD(1)[OF wf]] unfolding cse by (induct xs) auto
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) {}" using m None by simp
    show ?thesis using wf tm kse cse None x f mp
      by (auto intro!: esim.EsPredC)
  next
    case (Some ys)
    have x: "xs = ys" using m Some by simp
    show ?thesis using wf tm kse cse Some x f mp
      by (auto intro!: esim.EsPredC)
  qed
next
  case (EsPredS ks cs tms n tw e)
  note wf = EsPredS.hyps(1) and sp = EsPredS.hyps(2)
    and cse = EsPredS.hyps(3) and kse = EsPredS.hyps(4) and kg = EsPredS.prems(4)
    and sts = kgood_sorted[OF EsPredS.prems(4)] and mts = EsPredS.prems(1) and m = EsPredS.prems(2)
  have f: "\<phi>' = mformula.MPred e tms Simple" using m by simp
  have t: "list_all (ftable ks) xs" by (rule kgood_tables[OF kg m])
  have mp: "map (etabc ks cs) xs = xs"
    using t etabc_same[OF eframeD(1)[OF wf]] unfolding kse by (induct xs) auto
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) {}" using m None by simp
    show ?thesis using wf sp cse kse None x f mp
      by (auto intro!: esim.EsPredS)
  next
    case (Some ys)
    have x: "xs = ys" using m Some by simp
    show ?thesis using wf sp cse kse Some x f mp
      by (auto intro!: esim.EsPredS)
  qed
next
  case (EsPredM ks cs tms n tw e)
  note wf = EsPredM.hyps(1) and kse = EsPredM.hyps(2)
    and kg = EsPredM.prems(4) and sts = kgood_sorted[OF EsPredM.prems(4)]
    and mts = EsPredM.prems(1) and m = EsPredM.prems(2)
  have f: "\<phi>' = mformula.MPred e tms Match" using m by simp
  show ?case
  proof (cases "Mapping.lookup db (e, length tms)")
    case None
    have x: "xs = replicate (length ts) {}" using m None by simp
    show ?thesis using wf kse None x f
      by (auto intro!: esim.EsPredM)
  next
    case (Some ys)
    have x: "xs = map (\<lambda>X. tabulate_match (pred_cols tms) ` Option.these (match tms ` X)) ys"
      using m Some by simp
    have sc: "set cs \<subseteq> set ks" using eframeD(3)[OF wf] by simp
    have mp: "map (umatch_table tms cs) ys = map (etabc ks cs) xs"
      unfolding x map_map kse
      by (intro map_cong[OF refl]) (simp add: umatch_table_etabc[OF sc[unfolded kse]])
    show ?thesis using wf kse Some x f mp
      by (auto intro!: esim.EsPredM)
  qed
next
  case (EsAndRel ks cs n tw \<phi>d \<phi> t1 t2 p c)
  note wf = EsAndRel.hyps(1) and sim = EsAndRel.hyps(2)
    and IH = EsAndRel.hyps(3) and fv1 = EsAndRel.hyps(4) and fv2 = EsAndRel.hyps(5)
    and kg = EsAndRel.prems(4) and sts = kgood_sorted[OF EsAndRel.prems(4)]
    and mts = EsAndRel.prems(1) and m = EsAndRel.prems(2)
  have kgc: "kgood n ks j ts db \<phi>" by (rule kgood_MAndRel[OF kg])
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (Set.filter (eval_constraint ks (t1, p, c, t2))) ys"
    and f: "\<phi>' = mformula.MAndRel ks \<psi>' (t1, p, c, t2)" using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ EsAndRel.prems(3)]) simp
  obtain \<psi>d' where d: "eeval j ts db \<phi>d = (map (etabc ks cs) ys, \<psi>d')"
    and sim': "esim n ks cs (enext tw ts) \<psi>d' \<psi>'" using IH[OF mts e sz kgc] by blast
  have "map (Set.filter (ueval_constraint (reindex_constraint cs (t1, p, c, t2))))
        (map (etabc ks cs) ys) = map (etabc ks cs) xs"
    unfolding x by (simp only: map_map comp_def ueval_constraint_reindex[OF fv1 fv2])
  then show ?case using d sim' wf fv1 fv2 f
    by (auto intro!: esim.EsAndRel)
next
  case (EsNeg n tw \<phi>d \<phi>)
  note sim = EsNeg.hyps(1) and IH = EsNeg.hyps(2)
    and kg = EsNeg.prems(4) and sts = kgood_sorted[OF EsNeg.prems(4)]
    and mts = EsNeg.prems(1) and m = EsNeg.prems(2)
  have kgc: "kgood n [] j ts db \<phi>" by (rule kgood_MNeg[OF kg])
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. if r = empty_table then unit_table else empty_table) ys"
    and f: "\<phi>' = mformula.MNeg \<psi>'" using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ EsNeg.prems(3)]) simp
  obtain \<psi>d' where d: "eeval j ts db \<phi>d = (map (etabc [] []) ys, \<psi>d')"
    and sim': "esim n [] [] (enext tw ts) \<psi>d' \<psi>'" using IH[OF mts e sz kgc] by blast
  have "map (\<lambda>r. if r = {} then {[]} else {}) (map (etabc [] []) ys) = map (etabc [] []) xs"
    unfolding x by (rule etabc_neg)
  then show ?case using d sim' f
    by (auto intro!: esim.EsNeg)
next
  case (EsExists ks cs n kks ccs tw \<phi>d \<phi> b)
  note wf = EsExists.hyps(1) and sim = EsExists.hyps(2)
    and IH = EsExists.hyps(3) and kse = EsExists.hyps(4) and cse = EsExists.hyps(5)
    and be = EsExists.hyps(6)
    and kg = EsExists.prems(4) and sts = kgood_sorted[OF EsExists.prems(4)]
    and mts = EsExists.prems(1) and m = EsExists.prems(2)
  have kgc: "kgood (Suc n) kks j ts db \<phi>" by (rule kgood_MExists[OF kg])
  obtain ys \<psi>' where e: "meval j (Suc n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (Suc n) ts db \<phi>")
  have x: "xs = map (\<lambda>r. ex_proj kks ` r) ys" and f: "\<phi>' = mformula.MExists kks \<psi>'"
    using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ EsExists.prems(3)]) simp
  obtain \<psi>d' where d: "eeval j ts db \<phi>d = (map (etabc kks ccs) ys, \<psi>d')"
    and sim': "esim (Suc n) kks ccs (enext tw ts) \<psi>d' \<psi>'" using IH[OF mts e sz kgc] by blast
  have fc: "eframe kks ccs" by (rule esim_dframe[OF sim])
  have pe1: "ex_drop0 ccs \<Longrightarrow> tl ` etabc kks ccs r = etabc ks cs (ex_proj kks ` r)"
    for r :: "event_data table"
    using etabc_exists[OF fc, of r] unfolding kse cse by simp
  have pe2: "\<not> ex_drop0 ccs \<Longrightarrow> etabc kks ccs r = etabc ks cs (ex_proj kks ` r)"
    for r :: "event_data table"
    using etabc_exists[OF fc, of r] unfolding kse cse by simp
  have "(if b then map (\<lambda>r. tl ` r) (map (etabc kks ccs) ys) else map (etabc kks ccs) ys)
      = map (etabc ks cs) xs"
    unfolding x be by (cases "ex_drop0 ccs") (simp_all add: comp_def pe1 pe2)
  then show ?case using d sim' wf kse cse be f
    by (auto intro!: esim.EsExists)
next
  case (EsOr ks cs n tw \<phi>d \<phi> k2 \<psi>d \<psi> buf dbuf)
  note wf = EsOr.hyps(1) and sim1 = EsOr.hyps(2) and IH1 = EsOr.hyps(3)
    and sim2 = EsOr.hyps(4) and IH2 = EsOr.hyps(5) and bf = EsOr.hyps(6)
    and kg = EsOr.prems(4) and sts = kgood_sorted[OF EsOr.prems(4)]
    and mts = EsOr.prems(1) and m = EsOr.prems(2)
  have kg1: "kgood n ks j ts db \<phi>" and kg2: "kgood n k2 j ts db \<psi>" by (rule kgood_MOr[OF kg])+
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. r1 \<union> reorder ks k2 r2) (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. r1 \<union> reorder ks k2 r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MOr ks \<phi>2 k2 \<psi>2 buf2" using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ EsOr.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc ks cs) as, \<phi>d2)"
    and s1: "esim n ks cs (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc k2 cs) bs, \<psi>d2)"
    and s2: "esim n k2 cs (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have f2: "eframe k2 cs" by (rule esim_dframe[OF sim2])
  have ta: "list_all (ftable ks) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable k2) bs"
    by (rule kgood_tables[OF kg2 e2])
  have e: "set k2 = set ks" using eframeD(3)[OF wf] eframeD(3)[OF f2] by simp
  have step: "\<And>a b :: event_data table. ftable ks a \<Longrightarrow> ftable k2 b \<Longrightarrow>
      etabc ks cs a \<union> etabc k2 cs b = etabc ks cs (a \<union> reorder ks k2 b)"
  proof -
    fix a b :: "event_data table" assume ta': "ftable ks a" and tb: "ftable k2 b"
    have "etabc ks cs (reorder ks k2 b) = reorder cs cs (etabc k2 cs b)"
      by (rule etabc_reorder[OF wf f2 e conjunct1[OF tb]])
    then show "etabc ks cs a \<union> etabc k2 cs b = etabc ks cs (a \<union> reorder ks k2 b)"
      by (simp add: etabc_Un_img reorder_def)
  qed
  obtain dbuf2' where dt: "mebuf2_take (\<lambda>r1 r2. r1 \<union> r2)
        (mebuf2_add (map (etabc ks cs) as) (map (etabc k2 cs) bs) dbuf)
      = (map (etabc ks cs) zs, dbuf2')"
    and bf': "ebuf2 ks cs k2 cs buf2 (rbuf2 dbuf2')"
    using ebuf2_estep[OF bf ta tb step e3] by blast
  show ?case using d1 d2 dt bf' s1 s2 wf x f
    by (auto intro!: esim.EsOr simp del: mebuf2_take.simps)
next
  case (EsAnd ks cs n k1 c1 tw \<phi>d \<phi> k2 c2 \<psi>d \<psi> pl pos buf dbuf)
  note wf = EsAnd.hyps(1) and sim1 = EsAnd.hyps(2)
    and IH1 = EsAnd.hyps(3) and sim2 = EsAnd.hyps(4) and IH2 = EsAnd.hyps(5)
    and kse = EsAnd.hyps(6) and cse = EsAnd.hyps(7) and ple = EsAnd.hyps(8)
    and neg = EsAnd.hyps(9) and bf = EsAnd.hyps(10)
    and kg = EsAnd.prems(4) and sts = kgood_sorted[OF EsAnd.prems(4)]
    and mts = EsAnd.prems(1) and m = EsAnd.prems(2)
  have kg1: "kgood n k1 j ts db \<phi>" and kg2: "kgood n k2 j ts db \<psi>" by (rule kgood_MAnd[OF kg])+
  obtain as \<phi>2 where e1: "meval j n ts db \<phi> = (as, \<phi>2)" by (cases "meval j n ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j n ts db \<psi> = (bs, \<psi>2)" by (cases "meval j n ts db \<psi>")
  obtain zs buf2 where e3: "mbuf2_take (\<lambda>r1 r2. bin_join k1 r1 pos k2 r2)
        (mbuf2_add as bs buf) = (zs, buf2)"
    by (cases "mbuf2_take (\<lambda>r1 r2. bin_join k1 r1 pos k2 r2) (mbuf2_add as bs buf)")
  have x: "xs = zs" and f: "\<phi>' = mformula.MAnd k1 \<phi>2 pos k2 \<psi>2 buf2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ EsAnd.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc k1 c1) as, \<phi>d2)"
    and s1: "esim n k1 c1 (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc k2 c2) bs, \<psi>d2)"
    and s2: "esim n k2 c2 (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have f1: "eframe k1 c1" by (rule esim_dframe[OF sim1])
  have f2: "eframe k2 c2" by (rule esim_dframe[OF sim2])
  have ta: "list_all (ftable k1) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable k2) bs"
    by (rule kgood_tables[OF kg2 e2])
  have step: "\<And>a b. ftable k1 (a :: event_data table) \<Longrightarrow> ftable k2 b \<Longrightarrow>
      gbin_join pl (etabc k1 c1 a) pos (etabc k2 c2 b) = etabc ks cs (bin_join k1 a pos k2 b)"
  proof -
    fix a b :: "event_data table" assume a: "ftable k1 a" and b: "ftable k2 b"
    have "bin_join k1 a pos k2 b = join k1 a pos k2 b"
      by (rule bin_join_table[OF eframeD(1)[OF f1] eframeD(1)[OF f2] conjunct1[OF a] conjunct1[OF b]])
    then show "gbin_join pl (etabc k1 c1 a) pos (etabc k2 c2 b) = etabc ks cs (bin_join k1 a pos k2 b)"
      unfolding ple cse kse using gbin_join_join[OF f1 f2 _ _ neg] a b by simp
  qed
  obtain dbuf2' where dt: "mebuf2_take (\<lambda>r1 r2. gbin_join pl r1 pos r2)
        (mebuf2_add (map (etabc k1 c1) as) (map (etabc k2 c2) bs) dbuf)
      = (map (etabc ks cs) zs, dbuf2')"
    and bf': "ebuf2 k1 c1 k2 c2 buf2 (rbuf2 dbuf2')"
    using ebuf2_estep[OF bf ta tb step e3] by blast
  show ?case using d1 d2 dt bf' s1 s2 wf kse cse ple neg x f
    by (auto intro!: esim.EsAnd simp del: mebuf2_take.simps)
next
  case (EsPrev ks cs n tw \<phi>d \<phi> dbuf buf dnts nts I first)
  note wf = EsPrev.hyps(1) and sim = EsPrev.hyps(2)
    and IH = EsPrev.hyps(3) and be = EsPrev.hyps(4) and ne = EsPrev.hyps(5)
    and kg = EsPrev.prems(4) and sts = kgood_sorted[OF EsPrev.prems(4)]
    and mts = EsPrev.prems(1) and m = EsPrev.prems(2)
  have kgc: "kgood n ks j ts db \<phi>" by (rule kgood_MPrev[OF kg])
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ EsPrev.prems(3)]) simp
  obtain \<psi>d' where d: "eeval j ts db \<phi>d = (map (etabc ks cs) ys, \<psi>d')"
    and sim': "esim n ks cs (enext tw ts) \<psi>d' \<psi>'" using IH[OF mts e sz kgc] by blast
  have t: "list_all (ftable ks) ys"
    by (rule kgood_tables[OF kgc e])
  show ?case
  proof (cases "first \<and> ts = []")
    case True
    have x: "xs = []" and f: "\<phi>' = mformula.MPrev I \<psi>' True (buf @ ys) (nts @ ts)"
      using m e True by simp_all
    have b2: "Rep_mbuf_t (dbuf @@ map (etabc ks cs) ys) = map (etabc ks cs) (buf @ ys)"
      and n2: "Rep_mbuf_t (dnts @@ ts) = nts @ ts"
      using be ne by (simp_all add: mbuf_t_append.rep_eq)
    show ?thesis using d True x f sim' wf b2 n2
      by (auto intro!: esim.EsPrev)
  next
    case False
    obtain zs buf' nts' where g: "mprev_next I (buf @ ys) (nts @ ts) = (zs, buf', nts')"
      by (cases "mprev_next I (buf @ ys) (nts @ ts)") auto
    have x: "xs = (if first then empty_table # zs else zs)"
      and f: "\<phi>' = mformula.MPrev I \<psi>' False buf' nts'"
      using m e g False by (simp_all add: Let_def)
    have g': "mprev_next I (map (etabc ks cs) (buf @ ys)) (nts @ ts)
        = (map (etabc ks cs) zs, map (etabc ks cs) buf', nts')"
      by (rule mprev_next_map[OF _ g]) simp
    obtain zs'' ub un where eu:
        "meprev_next I (dbuf @@ map (etabc ks cs) ys) (dnts @@ ts) = (zs'', ub, un)"
      by (metis prod_cases3)
    have r: "(zs'', Rep_mbuf_t ub, Rep_mbuf_t un) = (map (etabc ks cs) zs, map (etabc ks cs) buf', nts')"
      using mprev_next_prev[of I dbuf "map (etabc ks cs) ys" dnts ts] g' eu be ne
      by (simp del: mprev_next.simps meprev_next.simps)
    show ?thesis using d False x f sim' wf eu r
      by (auto simp: empty_table_def intro!: esim.EsPrev simp del: meprev_next.simps)
  qed
next
  case (EsNext ks cs n tw \<phi>d \<phi> dnts nts I first)
  note wf = EsNext.hyps(1) and sim = EsNext.hyps(2)
    and IH = EsNext.hyps(3) and ne = EsNext.hyps(4) and kg = EsNext.prems(4) and sts = kgood_sorted[OF EsNext.prems(4)]
    and mts = EsNext.prems(1) and m = EsNext.prems(2)
  have kgc: "kgood n ks j ts db \<phi>" by (rule kgood_MNext[OF kg])
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ EsNext.prems(3)]) simp
  obtain \<psi>d' where d: "eeval j ts db \<phi>d = (map (etabc ks cs) ys, \<psi>d')"
    and sim': "esim n ks cs (enext tw ts) \<psi>d' \<psi>'" using IH[OF mts e sz kgc] by blast
  obtain ys0 first0 where c:
      "(case (ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a) = (ys0, first0)"
    by (cases "(case (ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a)") auto
  have c': "(case (map (etabc ks cs) ys, first) of (_ # r, True) \<Rightarrow> (r, False) | a \<Rightarrow> a)
      = (map (etabc ks cs) ys0, first0)"
    using c by (cases ys; cases first) auto
  obtain zs buf' nts' where g: "mprev_next I ys0 (nts @ ts) = (zs, buf', nts')"
    by (cases "mprev_next I ys0 (nts @ ts)") auto
  have x: "xs = zs" and f: "\<phi>' = mformula.MNext I \<psi>' first0 nts'"
    using m e c g by (simp_all add: Let_def split: prod.splits)
  have g': "mprev_next I (map (etabc ks cs) ys0) (nts @ ts)
      = (map (etabc ks cs) zs, map (etabc ks cs) buf', nts')"
    by (rule mprev_next_map[OF _ g]) simp
  obtain zs'' ub un where eu:
      "meprev_next I (mbuf_t_empty @@ map (etabc ks cs) ys0) (dnts @@ ts) = (zs'', ub, un)"
    by (metis prod_cases3)
  have "(zs'', Rep_mbuf_t ub, Rep_mbuf_t un) = (map (etabc ks cs) zs, map (etabc ks cs) buf', nts')"
    using mprev_next_next[of I "map (etabc ks cs) ys0" dnts ts] g' eu ne
    by (simp del: mprev_next.simps meprev_next.simps)
  then show ?case using d c' eu x f sim' wf
    by (auto intro!: esim.EsNext simp del: meprev_next.simps)
next
  case (EsAnds ks cs L n k0 kss nkss c0 css nss tw Ld ps ns buf dbuf)
  note wf = EsAnds.hyps(1) and la = EsAnds.hyps(2)
    and l1 = EsAnds.hyps(3) and l2 = EsAnds.hyps(4) and lk = EsAnds.hyps(5)
    and lnk = EsAnds.hyps(6) and sb = EsAnds.hyps(7) and cse = EsAnds.hyps(8)
    and pse = EsAnds.hyps(9) and nse = EsAnds.hyps(10) and bf = EsAnds.hyps(11)
    and kg = EsAnds.prems(4) and sts = kgood_sorted[OF EsAnds.prems(4)]
    and mts = EsAnds.prems(1) and m = EsAnds.prems(2)
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
  have la0: "\<forall>i < length L. esim n (?ks' ! i) (?cs' ! i) tw (Ld ! i) (L ! i)" using la by blast
  have kgL: "\<forall>i < length L. kgood n (?ks' ! i) j ts db (L ! i)"
    using kgood_MAnds[OF kg] by simp
  have sz: "size_list size L \<le> NN" using EsAnds.prems(3) by simp
  note ops = eeval_operands[OF la l1 l2 l3 mts sz kgL bf]
  note dl0 = ops(1) and dl = ops(2) and dl2 = ops(3) and badd = ops(4)
  \<comment> \<open>the join at each firing\<close>
  have fs: "\<forall>i < length ?cs'. eframe (?ks' ! i) (?cs' ! i)"
    using la0 l2 by (auto dest: esim_dframe)
  have step: "\<And>as :: event_data table list. length as = length ?cs' \<Longrightarrow>
      (\<forall>i < length ?cs'. ftable (?ks' ! i) (as ! i)) \<Longrightarrow>
      etabc ks cs (mmulti_join ks (k0 # kss) nkss as) = gmulti_join ps ns (etabcs ?ks' ?cs' as)"
    unfolding cse pse nse by (rule eands_step[OF fs lk lnk sb wf[unfolded cse]])
  obtain dbuf' where dt: "mbufn_take (\<lambda>as zs. zs @ [gmulti_join ps ns as])
        ([] :: event_data table list)
        (map Rep_mbuf_t (mebufn_add (map fst (map (eeval j ts db) Ld)) dbuf))
      = (map (etabc ks cs) zs, dbuf')"
    and bf': "ebufn ?ks' ?cs' buf' dbuf'"
    using ebufn_take[OF badd step g0] by blast
  obtain uzs ub where eu: "mebufn_take (\<lambda>as zs. zs @@ [gmulti_join ps ns as]) mbuf_t_empty
      (mebufn_add (map fst (map (eeval j ts db) Ld)) dbuf) = (uzs, ub)"
    by (metis surj_pair)
  have r: "Rep_mbuf_t uzs = map (etabc ks cs) zs \<and> map Rep_mbuf_t ub = dbuf'"
    using dt eu mbufn_take_ands[of ps ns "mebufn_add (map fst (map (eeval j ts db) Ld)) dbuf"]
    by (simp del: mbufn_take.simps mebufn_take.simps)
  have dv: "eeval j ts db (EAnds ps ns Ld dbuf)
      = (map (etabc ks cs) xs, EAnds ps ns (map snd (map (eeval j ts db) Ld)) ub)"
    using eu r x by (simp add: Let_def del: mebufn_take.simps)
  have s2: "esim n ks cs (enext tw ts) (EAnds ps ns (map snd (map (eeval j ts db) Ld)) ub)
      (mformula.MAnds ks (k0 # kss) nkss (map snd ?R) buf')"
  proof (rule esim.EsAnds)
    show "eframe ks cs" by (rule wf)
    show "\<forall>i < length (map snd ?R). esim n (?ks' ! i) (?cs' ! i) (enext tw ts)
        (map snd (map (eeval j ts db) Ld) ! i) (map snd ?R ! i)"
      using dl2 by simp
    show "length (map snd (map (eeval j ts db) Ld)) = length (map snd ?R)"
      using dl0 by simp
    show "length ?cs' = length (map snd ?R)" using l2 by simp
  qed (use lk lnk sb cse pse nse bf' r in simp_all)
  show ?case using dv s2 fe by auto
next
  case (EsAgg ks cs args n k0 gcols tw \<phi>d \<phi> y)
  note wf = EsAgg.hyps(1) and sim = EsAgg.hyps(2) and IH = EsAgg.hyps(3)
    and kc = EsAgg.hyps(4) and ye = EsAgg.hyps(5) and yg = EsAgg.hyps(6)
    and g0 = EsAgg.hyps(7) and fv = EsAgg.hyps(8) and kse = EsAgg.hyps(9) and cse = EsAgg.hyps(10)
    and kg = EsAgg.prems(4) and sts = kgood_sorted[OF EsAgg.prems(4)]
    and mts = EsAgg.prems(1) and m = EsAgg.prems(2)
  have kgc: "kgood (length (aggargs_tys args) + n) k0 j ts db \<phi>" using kgood_MAgg[OF kg] kc by simp
  let ?mm = "length (aggargs_tys args)"
  let ?cc = "agg_cols ?mm gcols"
  obtain ys \<psi>' where e: "meval j (?mm + n) ts db \<phi> = (ys, \<psi>')"
    by (cases "meval j (?mm + n) ts db \<phi>")
  have x: "xs = map (eval_aggargs args) ys" and f: "\<phi>' = mformula.MAgg args \<psi>'"
    using m e by simp_all
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ EsAgg.prems(3)]) simp
  obtain \<psi>d' where d: "eeval j ts db \<phi>d = (map (etabc k0 ?cc) ys, \<psi>d')"
    and sim': "esim (?mm + n) k0 ?cc (enext tw ts) \<psi>d' \<psi>'" using IH[OF mts e sz kgc] by blast
  have fc: "eframe k0 ?cc" by (rule esim_dframe[OF sim])
  have t: "list_all (ftable k0) ys"
    by (rule kgood_tables[OF kgc e])
  have "map (uagg (aggargs_g0 args) (aggargs_\<omega> args) (reindex_trm ?cc (aggargs_f args)) ?mm
          (ins_pos gcols y)) (map (etabc k0 ?cc) ys) = map (etabc ks cs) xs"
    unfolding x kse cse using t
    by (intro nth_equalityI)
      (auto simp: list_all_iff eval_aggargs_def kc uagg_eval_agg[OF fc _ fv yg g0])
  then show ?case using d sim' wf kc ye yg g0 fv kse cse f
    by (auto intro!: esim.EsAgg)
next
  case (EsSince kR cR args kL cL tw \<phi>d \<phi> \<psi>d \<psi> dags aux daux buf dbuf n)
  note wf = EsSince.hyps(1)
    and sim1 = EsSince.hyps(2) and IH1 = EsSince.hyps(3)
    and sim2 = EsSince.hyps(4) and IH2 = EsSince.hyps(5)
    and sub = EsSince.hyps(6) and agg = EsSince.hyps(7)
    and aL = EsSince.hyps(8) and aR = EsSince.hyps(9)
    and dag = EsSince.hyps(10) and rel = EsSince.hyps(11) and nag = EsSince.hyps(12)
    and kg = EsSince.prems(4) and sts = kgood_sorted[OF EsSince.prems(4)]
    and mts = EsSince.prems(1) and m = EsSince.prems(2)
  have kg1: "kgood (args_n args) kL j ts db \<phi>" and kg2: "kgood (args_n args) kR j ts db \<psi>"
    using kgood_MSince[OF kg] aL aR by simp_all
  let ?nn = "args_n args"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ EsSince.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim ?nn kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim ?nn kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain dzs ub ua where eu: "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) dzs, ub, ua)"
    and step: "esresh kR cR args (esx_post (rdsx daux)) zs dzs"
    and rel': "esince_rel kR cR kL cL args (enext tw ts) aux2 (rdsx ua) buf2 (rbufS ub)"
    and nag2: "esx_agg (rdsx ua) = esx_agg (rdsx daux)"
    by (rule esince_node_rel[OF wf fL sub aL aR dag rel ta tb sts mts e3])
  have post: "esx_post (rdsx daux) = id" using nag by (simp add: esx_post_eq)
  have dz: "dzs = map (etabc kR cR) zs"
    using step esres_none[OF agg] by (simp add: post esresh_id)
  have q: "usx_q daux = None" using nag by (cases daux) simp_all
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ESince dags \<phi>d \<psi>d dbuf daux)
        = (map (etabc kR cR) xs, ESince dags \<phi>d2 \<psi>d2 ub ua)"
      using d1 d2 eu dz x q by simp
    show "esim n kR cR (enext tw ts) (ESince dags \<phi>d2 \<psi>d2 ub ua) \<phi>'"
      unfolding f
      by (rule esim.EsSince[OF wf s1 s2 sub agg aL aR
            dag]) (use rel' nag2 nag in simp_all)
  qed
next
  case (EsUntil kR cR args kL cL tw \<phi>d \<phi> \<psi>d \<psi> dags msk t aux daux buf dbuf nts dnts n)
  note wf = EsUntil.hyps(1)
    and sim1 = EsUntil.hyps(2) and IH1 = EsUntil.hyps(3)
    and sim2 = EsUntil.hyps(4) and IH2 = EsUntil.hyps(5)
    and sub = EsUntil.hyps(6) and agg = EsUntil.hyps(7)
    and aL = EsUntil.hyps(8) and aR = EsUntil.hyps(9)
    and dag = EsUntil.hyps(10) and pe = EsUntil.hyps(11) and rel = EsUntil.hyps(12)
    and ne = EsUntil.hyps(13) and nag = EsUntil.hyps(14)
    and kg = EsUntil.prems(4) and sts = kgood_sorted[OF EsUntil.prems(4)]
    and mts = EsUntil.prems(1) and m = EsUntil.prems(2)
  have kg1: "kgood (args_n args) kL j ts db \<phi>" and kg2: "kgood (args_n args) kR j ts db \<psi>"
    using kgood_MUntil[OF kg] aL aR by simp_all
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
    by (rule order_trans[OF _ EsUntil.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim ?nn kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim ?nn kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain dzs ua ub un ua2 where eu: "mebuf2t_take (udux_add_new dags msk) daux
      (mebuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) t (dnts @@ ts) = (ua, ub, nt, un)"
    and eu2: "udux_eval dags nt ua = (dzs, ua2)"
    and step: "esresh kR cR args (eux_post (rdux daux)) zs dzs"
    and rel': "euntil_rel kR cR kL cL args (enext tw ts) nt aux2 (rdux ua2) buf1 (rbuf2 ub) nts1"
    and un: "Rep_mbuf_t un = nts1" and nag2: "eux_agg (rdux ua2) = eux_agg (rdux daux)"
    by (rule euntil_node_rel[OF wf fL sub aL aR dag pe rel ne ta tb sts mts e3 e4])
  have post: "eux_post (rdux daux) = id" using nag by (simp add: eux_post_eq)
  have dz: "dzs = map (etabc kR cR) zs"
    using step esres_none[OF agg] by (simp add: post esresh_id)
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EUntil dags msk \<phi>d \<psi>d dbuf dnts t daux)
        = (map (etabc kR cR) xs, EUntil dags msk \<phi>d2 \<psi>d2 ub un nt ua2)"
      using d1 d2 eu eu2 dz x by simp
    show "esim n kR cR (enext tw ts) (EUntil dags msk \<phi>d2 \<psi>d2 ub un nt ua2) \<phi>'"
      unfolding f
      by (rule esim.EsUntil[OF wf s1 s2 sub agg aL aR
            dag pe]) (use rel' nag2 nag un in simp_all)
  qed
next
  case (EsSinceAgg ks cs args kL cL tw \<phi>d \<phi> kR cR \<psi>d \<psi> ag dags aux daux buf dbuf y gcols n)
  note wf = EsSinceAgg.hyps(1)
    and sim1 = EsSinceAgg.hyps(2) and IH1 = EsSinceAgg.hyps(3)
    and sim2 = EsSinceAgg.hyps(4) and IH2 = EsSinceAgg.hyps(5)
    and sub = EsSinceAgg.hyps(6) and agg = EsSinceAgg.hyps(7)
    and aL = EsSinceAgg.hyps(8) and aR = EsSinceAgg.hyps(9)
    and dag = EsSinceAgg.hyps(10) and rel = EsSinceAgg.hyps(11)
    and kc = EsSinceAgg.hyps(12) and ye = EsSinceAgg.hyps(13) and yg = EsSinceAgg.hyps(14)
    and g0 = EsSinceAgg.hyps(15) and fv = EsSinceAgg.hyps(16) and cRe = EsSinceAgg.hyps(17)
    and kse = EsSinceAgg.hyps(18) and cse = EsSinceAgg.hyps(19) and nag = EsSinceAgg.hyps(20)
    and kg = EsSinceAgg.prems(4) and sts = kgood_sorted[OF EsSinceAgg.prems(4)]
    and mts = EsSinceAgg.prems(1) and m = EsSinceAgg.prems(2)
  have kg1: "kgood (args_n args) kL j ts db \<phi>" and kg2: "kgood (args_n args) kR j ts db \<psi>"
    using kgood_MSince[OF kg] aL aR by simp_all
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
    by (rule order_trans[OF _ EsSinceAgg.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim ?nn kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim ?nn kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have fR: "eframe kR cR" by (rule esim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain dzs ub ua where eu: "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) dzs, ub, ua)"
    and step: "esresh kR cR args (esx_post (rdsx daux)) zs dzs"
    and rel': "esince_rel kR cR kL cL args (enext tw ts) aux2 (rdsx ua) buf2 (rbufS ub)"
    and nag2: "esx_agg (rdsx ua) = esx_agg (rdsx daux)"
    by (rule esince_node_rel[OF fR fL sub aL aR dag rel ta tb sts mts e3])
  have post: "esx_post (rdsx daux) = id" using nag by (simp add: esx_post_eq)
  have fc: "eframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "map ?ag dzs = map (etabc ks cs) xs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (etabc kR cR) vs"
      using step unfolding post esresh_id esres_def by blast
    show ?thesis unfolding x v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  have q: "usx_q daux = None" using nag by (cases daux) simp_all
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
          (length (aggargs_tys ag)) (ins_pos gcols y) (ESince dags \<phi>d \<psi>d dbuf daux))
        = (map (etabc ks cs) xs, EAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
            (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
            (ESince dags \<phi>d2 \<psi>d2 ub ua))"
      using d1 d2 eu q agc by simp
    show "esim n ks cs (enext tw ts) (EAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
          (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
          (ESince dags \<phi>d2 \<psi>d2 ub ua)) \<phi>'"
      unfolding f
      by (rule esim.EsSinceAgg[OF wf s1 s2 sub
            agg aL aR dag _ kc ye yg g0 fv cRe kse cse]) (use rel' nag2 nag in simp_all)
  qed
next
  case (EsSinceFused ks cs args kL cL tw \<phi>d \<phi> kR cR \<psi>d \<psi> ag dags aux daux buf dbuf y gcols n)
  note wf = EsSinceFused.hyps(1)
    and sim1 = EsSinceFused.hyps(2) and IH1 = EsSinceFused.hyps(3)
    and sim2 = EsSinceFused.hyps(4) and IH2 = EsSinceFused.hyps(5)
    and sub = EsSinceFused.hyps(6) and agg = EsSinceFused.hyps(7)
    and aL = EsSinceFused.hyps(8) and aR = EsSinceFused.hyps(9)
    and dag = EsSinceFused.hyps(10) and rel = EsSinceFused.hyps(11)
    and kc = EsSinceFused.hyps(12) and ye = EsSinceFused.hyps(13) and yg = EsSinceFused.hyps(14)
    and g0 = EsSinceFused.hyps(15) and fv = EsSinceFused.hyps(16) and cRe = EsSinceFused.hyps(17)
    and kse = EsSinceFused.hyps(18) and cse = EsSinceFused.hyps(19) and nag = EsSinceFused.hyps(20)
    and nq = EsSinceFused.hyps(21)
    and kg = EsSinceFused.prems(4) and sts = kgood_sorted[OF EsSinceFused.prems(4)]
    and mts = EsSinceFused.prems(1) and m = EsSinceFused.prems(2)
  have kg1: "kgood (args_n args) kL j ts db \<phi>" and kg2: "kgood (args_n args) kR j ts db \<psi>"
    using kgood_MSince[OF kg] aL aR by simp_all
  let ?nn = "args_n args"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have x: "xs = zs" and f: "\<phi>' = mformula.MSince args \<phi>2 \<psi>2 buf2 aux2"
    using m e1 e2 e3 by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ EsSinceFused.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim ?nn kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim ?nn kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have fR: "eframe kR cR" by (rule esim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain ub ua where eu: "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) (map (etabc ks cs) zs), ub, ua)"
    and rel2: "esince_rel kR cR kL cL args (enext tw ts) aux2 (rdsx ua) buf2 (rbufS ub)"
    and nag2: "esx_agg (rdsx ua) = esx_agg (rdsx daux)" and q2: "usx_q ua = usx_q daux"
    by (rule esince_fused_rel[OF fR fL sub agg aL aR dag rel kc ye yg g0 fv cRe kse cse nag
          ta tb sts mts e3])
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ESince dags \<phi>d \<psi>d dbuf daux)
        = (map (etabc ks cs) xs, ESince dags \<phi>d2 \<psi>d2 ub ua)"
      using d1 d2 eu nq x by simp
    show "esim n ks cs (enext tw ts) (ESince dags \<phi>d2 \<psi>d2 ub ua) \<phi>'"
      unfolding f
      by (rule esim.EsSinceFused[OF wf s1 s2 sub
            agg aL aR dag rel2 kc ye yg g0 fv cRe kse cse]) (use nag nag2 q2 nq in simp_all)
  qed
next
  case (EsSinceGuard ks cs args kL cL tw \<phi>d \<phi> kR cR \<psi>d \<psi> ag dags aux daux buf dbuf y gcols t1 t2 p c n)
  note wf = EsSinceGuard.hyps(1)
    and sim1 = EsSinceGuard.hyps(2) and IH1 = EsSinceGuard.hyps(3)
    and sim2 = EsSinceGuard.hyps(4) and IH2 = EsSinceGuard.hyps(5)
    and sub = EsSinceGuard.hyps(6) and agg = EsSinceGuard.hyps(7)
    and aL = EsSinceGuard.hyps(8) and aR = EsSinceGuard.hyps(9)
    and dag = EsSinceGuard.hyps(10) and rel = EsSinceGuard.hyps(11)
    and kc = EsSinceGuard.hyps(12) and ye = EsSinceGuard.hyps(13) and yg = EsSinceGuard.hyps(14)
    and g0 = EsSinceGuard.hyps(15) and fv = EsSinceGuard.hyps(16) and cRe = EsSinceGuard.hyps(17)
    and kse = EsSinceGuard.hyps(18) and cse = EsSinceGuard.hyps(19) and nag = EsSinceGuard.hyps(20)
    and fv1 = EsSinceGuard.hyps(21) and fv2 = EsSinceGuard.hyps(22) and gq = EsSinceGuard.hyps(23)
    and kg = EsSinceGuard.prems(4) and sts = kgood_sorted[OF EsSinceGuard.prems(4)]
    and mts = EsSinceGuard.prems(1) and m = EsSinceGuard.prems(2)
  have kg1: "kgood (args_n args) kL j ts db \<phi>" and kg2: "kgood (args_n args) kR j ts db \<psi>"
    using kgood_MSince[OF kgood_MAndRel[OF kg]] aL aR by simp_all
  let ?nn = "args_n args"
  obtain as \<phi>2 where e1: "meval j ?nn ts db \<phi> = (as, \<phi>2)" by (cases "meval j ?nn ts db \<phi>")
  obtain bs \<psi>2 where e2: "meval j ?nn ts db \<psi> = (bs, \<psi>2)" by (cases "meval j ?nn ts db \<psi>")
  obtain zs buf2 aux2 where e3: "meval_since args [] (mbuf2S_add as bs ts buf) aux
      = (zs, buf2, aux2)" by (cases "meval_since args [] (mbuf2S_add as bs ts buf) aux")
  have mS: "meval j n ts db (mformula.MSince args \<phi> \<psi> buf aux)
      = (zs, mformula.MSince args \<phi>2 \<psi>2 buf2 aux2)"
    using e1 e2 e3 by simp
  have x: "xs = map (Set.filter (eval_constraint ks (t1, p, c, t2))) zs"
    and f: "\<phi>' = mformula.MAndRel ks (mformula.MSince args \<phi>2 \<psi>2 buf2 aux2) (t1, p, c, t2)"
    using m mS by simp_all
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ EsSinceGuard.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim ?nn kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim ?nn kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have fR: "eframe kR cR" by (rule esim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain ub ua where eu: "uedsx_eval_since dags []
      (mebuf2S_add (map (etabc kL cL) as) (map (etabc kR cR) bs) ts dbuf) daux
      = (map (ufilt (usx_q daux)) (map (etabc ks cs) zs), ub, ua)"
    and rel2: "esince_rel kR cR kL cL args (enext tw ts) aux2 (rdsx ua) buf2 (rbufS ub)"
    and nag2: "esx_agg (rdsx ua) = esx_agg (rdsx daux)" and q2: "usx_q ua = usx_q daux"
    by (rule esince_fused_rel[OF fR fL sub agg aL aR dag rel kc ye yg g0 fv cRe kse cse nag
          ta tb sts mts e3])
  have filt: "map (ufilt (usx_q daux)) (map (etabc ks cs) zs) = map (etabc ks cs) xs"
    unfolding gq x by (simp only: map_map comp_def ufilt_Some ueval_constraint_reindex[OF fv1 fv2])
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ESince dags \<phi>d \<psi>d dbuf daux)
        = (map (etabc ks cs) xs, ESince dags \<phi>d2 \<psi>d2 ub ua)"
      using d1 d2 eu filt by simp
    show "esim n ks cs (enext tw ts) (ESince dags \<phi>d2 \<psi>d2 ub ua) \<phi>'"
      unfolding f
      by (rule esim.EsSinceGuard[OF wf s1 s2 sub agg aL aR dag rel2 kc ye yg g0 fv cRe
            kse cse _ fv1 fv2]) (use nag nag2 q2 gq in simp_all)
  qed
next
  case (EsUntilAgg ks cs args kL cL tw \<phi>d \<phi> kR cR \<psi>d \<psi> ag dags msk t aux daux buf dbuf nts dnts y gcols n)
  note wf = EsUntilAgg.hyps(1)
    and sim1 = EsUntilAgg.hyps(2) and IH1 = EsUntilAgg.hyps(3)
    and sim2 = EsUntilAgg.hyps(4) and IH2 = EsUntilAgg.hyps(5)
    and sub = EsUntilAgg.hyps(6) and agg = EsUntilAgg.hyps(7)
    and aL = EsUntilAgg.hyps(8) and aR = EsUntilAgg.hyps(9)
    and dag = EsUntilAgg.hyps(10) and pe = EsUntilAgg.hyps(11) and rel = EsUntilAgg.hyps(12)
    and ne = EsUntilAgg.hyps(13)
    and kc = EsUntilAgg.hyps(14) and ye = EsUntilAgg.hyps(15) and yg = EsUntilAgg.hyps(16)
    and g0 = EsUntilAgg.hyps(17) and fv = EsUntilAgg.hyps(18) and cRe = EsUntilAgg.hyps(19)
    and kse = EsUntilAgg.hyps(20) and cse = EsUntilAgg.hyps(21) and nag = EsUntilAgg.hyps(22)
    and kg = EsUntilAgg.prems(4) and sts = kgood_sorted[OF EsUntilAgg.prems(4)]
    and mts = EsUntilAgg.prems(1) and m = EsUntilAgg.prems(2)
  have kg1: "kgood (args_n args) kL j ts db \<phi>" and kg2: "kgood (args_n args) kR j ts db \<psi>"
    using kgood_MUntil[OF kg] aL aR by simp_all
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
    by (rule order_trans[OF _ EsUntilAgg.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim ?nn kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim ?nn kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have fR: "eframe kR cR" by (rule esim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain dzs ua ub un ua2 where eu: "mebuf2t_take (udux_add_new dags msk) daux
      (mebuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) t (dnts @@ ts) = (ua, ub, nt, un)"
    and eu2: "udux_eval dags nt ua = (dzs, ua2)"
    and step: "esresh kR cR args (eux_post (rdux daux)) zs dzs"
    and rel': "euntil_rel kR cR kL cL args (enext tw ts) nt aux2 (rdux ua2) buf1 (rbuf2 ub) nts1"
    and un: "Rep_mbuf_t un = nts1" and nag2: "eux_agg (rdux ua2) = eux_agg (rdux daux)"
    by (rule euntil_node_rel[OF fR fL sub aL aR dag pe rel ne ta tb sts mts e3 e4])
  have post: "eux_post (rdux daux) = id" using nag by (simp add: eux_post_eq)
  have fc: "eframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "map ?ag dzs = map (etabc ks cs) xs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (etabc kR cR) vs"
      using step unfolding post esresh_id esres_def by blast
    show ?thesis unfolding x v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EAgg (aggargs_g0 ag) (aggargs_\<omega> ag) (reindex_trm cR (aggargs_f ag))
          (length (aggargs_tys ag)) (ins_pos gcols y) (EUntil dags msk \<phi>d \<psi>d dbuf dnts t daux))
        = (map (etabc ks cs) xs, EAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
            (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
            (EUntil dags msk \<phi>d2 \<psi>d2 ub un nt ua2))"
      using d1 d2 eu eu2 agc by simp
    show "esim n ks cs (enext tw ts) (EAgg (aggargs_g0 ag) (aggargs_\<omega> ag)
          (reindex_trm cR (aggargs_f ag)) (length (aggargs_tys ag)) (ins_pos gcols y)
          (EUntil dags msk \<phi>d2 \<psi>d2 ub un nt ua2)) \<phi>'"
      unfolding f
      by (rule esim.EsUntilAgg[OF wf s1 s2 sub
            agg aL aR dag pe _ _ kc ye yg g0 fv cRe kse cse]) (use rel' nag2 nag un in simp_all)
  qed
next
  case (EsUntilFused ks cs args kL cL tw \<phi>d \<phi> kR cR \<psi>d \<psi> ag dags msk t aux daux buf dbuf nts dnts y gcols n)
  note wf = EsUntilFused.hyps(1)
    and sim1 = EsUntilFused.hyps(2) and IH1 = EsUntilFused.hyps(3)
    and sim2 = EsUntilFused.hyps(4) and IH2 = EsUntilFused.hyps(5)
    and sub = EsUntilFused.hyps(6) and agg = EsUntilFused.hyps(7)
    and aL = EsUntilFused.hyps(8) and aR = EsUntilFused.hyps(9)
    and dag = EsUntilFused.hyps(10) and pe = EsUntilFused.hyps(11) and rel = EsUntilFused.hyps(12)
    and ne = EsUntilFused.hyps(13)
    and kc = EsUntilFused.hyps(14) and ye = EsUntilFused.hyps(15) and yg = EsUntilFused.hyps(16)
    and g0 = EsUntilFused.hyps(17) and fv = EsUntilFused.hyps(18) and cRe = EsUntilFused.hyps(19)
    and kse = EsUntilFused.hyps(20) and cse = EsUntilFused.hyps(21) and nag = EsUntilFused.hyps(22)
    and kg = EsUntilFused.prems(4) and sts = kgood_sorted[OF EsUntilFused.prems(4)]
    and mts = EsUntilFused.prems(1) and m = EsUntilFused.prems(2)
  have kg1: "kgood (args_n args) kL j ts db \<phi>" and kg2: "kgood (args_n args) kR j ts db \<psi>"
    using kgood_MUntil[OF kg] aL aR by simp_all
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
    by (rule order_trans[OF _ EsUntilFused.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim ?nn kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim ?nn kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have fR: "eframe kR cR" by (rule esim_dframe[OF sim2])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain dzs ua ub un ua2 where eu: "mebuf2t_take (udux_add_new dags msk) daux
      (mebuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) t (dnts @@ ts) = (ua, ub, nt, un)"
    and eu2: "udux_eval dags nt ua = (dzs, ua2)"
    and step: "esresh kR cR args (eux_post (rdux daux)) zs dzs"
    and rel': "euntil_rel kR cR kL cL args (enext tw ts) nt aux2 (rdux ua2) buf1 (rbuf2 ub) nts1"
    and un: "Rep_mbuf_t un = nts1" and nag2: "eux_agg (rdux ua2) = eux_agg (rdux daux)"
    by (rule euntil_node_rel[OF fR fL sub aL aR dag pe rel ne ta tb sts mts e3 e4])
  have post: "eux_post (rdux daux) = ?ag" using nag by (simp add: eux_post_eq)
  have fc: "eframe kR (agg_cols (length (aggargs_tys ag)) gcols)" using fR cRe by simp
  have agc: "dzs = map (etabc ks cs) xs"
  proof -
    obtain vs where v: "list_all (table kR) vs"
      "zs = map (eval_args_agg args) vs" "dzs = map (?ag \<circ> etabc kR cR) vs"
      using step unfolding esresh_def post by blast
    show ?thesis unfolding x v(2) v(3) kse cse cRe
      using v(1) by (intro nth_equalityI)
        (auto simp: list_all_iff eval_args_agg_def eval_aggargs_def agg kc uagg_eval_agg[OF fc _ fv yg g0])
  qed
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EUntil dags msk \<phi>d \<psi>d dbuf dnts t daux)
        = (map (etabc ks cs) xs, EUntil dags msk \<phi>d2 \<psi>d2 ub un nt ua2)"
      using d1 d2 eu eu2 agc by simp
    show "esim n ks cs (enext tw ts) (EUntil dags msk \<phi>d2 \<psi>d2 ub un nt ua2) \<phi>'"
      unfolding f
      by (rule esim.EsUntilFused[OF wf s1 s2 sub
            agg aL aR dag pe _ _ kc ye yg g0 fv cRe kse cse]) (use rel' nag2 nag un in simp_all)
  qed
next
  case (EsAndAssign ks cs n k0 c0 tw \<phi>d \<phi> y t)
  note wf = EsAndAssign.hyps(1) and sim = EsAndAssign.hyps(2)
    and IH = EsAndAssign.hyps(3) and yk = EsAndAssign.hyps(4) and fv = EsAndAssign.hyps(5)
    and kse = EsAndAssign.hyps(6) and cse = EsAndAssign.hyps(7)
    and kg = EsAndAssign.prems(4) and sts = kgood_sorted[OF EsAndAssign.prems(4)]
    and mts = EsAndAssign.prems(1) and m = EsAndAssign.prems(2)
  have kgc: "kgood n k0 j ts db \<phi>" by (rule kgood_MAndAssign[OF kg])
  obtain ys \<psi>' where e: "meval j n ts db \<phi> = (ys, \<psi>')" by (cases "meval j n ts db \<phi>")
  have x: "xs = map (\<lambda>r. eval_assignment k0 (y, t) ` r) ys"
    and f: "\<phi>' = mformula.MAndAssign k0 \<psi>' (y, t)"
    using m e by (simp_all del: eval_assignment.simps)
  have sz: "size \<phi> \<le> NN" by (rule order_trans[OF _ EsAndAssign.prems(3)]) simp
  obtain \<psi>d' where d: "eeval j ts db \<phi>d = (map (etabc k0 c0) ys, \<psi>d')"
    and sim': "esim n k0 c0 (enext tw ts) \<psi>d' \<psi>'" using IH[OF mts e sz kgc] by blast
  have tb: "list_all (ftable k0) ys"
    by (rule kgood_tables[OF kgc e])
  have f0: "eframe k0 c0" by (rule esim_dframe[OF sim])
  have mapeq: "map (uassign (ins_pos c0 y) (reindex_trm c0 t)) (map (etabc k0 c0) ys)
      = map (etabc ks cs) xs"
    unfolding x map_map kse cse using tb
    by (intro map_cong refl) (simp add: list_all_iff uassign_eval_assignment[OF f0 yk fv])
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<phi>d)
        = (map (etabc ks cs) xs, EAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<psi>d')"
      using d mapeq by simp
    show "esim n ks cs (enext tw ts) (EAndAssign (ins_pos c0 y) (reindex_trm c0 t) \<psi>d') \<phi>'"
      unfolding f
      by (rule esim.EsAndAssign[OF wf sim' yk fv kse cse])
  qed
next
  case (EsTP ks cs mt n tw i)
  note wf = EsTP.hyps(1) and cse = EsTP.hyps(2) and kse = EsTP.hyps(3)
    and kg = EsTP.prems(4) and sts = kgood_sorted[OF EsTP.prems(4)]
    and mts = EsTP.prems(1) and m = EsTP.prems(2)
  have x: "xs = map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) [i..<j]"
    and f: "\<phi>' = mformula.MTP mt j" using m by simp_all
  have t: "list_all (ftable ks) xs" by (rule kgood_tables[OF kg m])
  have mapeq: "map (etabc ks cs) xs = map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) [i..<j]"
    using t etabc_same[OF eframeD(1)[OF wf]] unfolding kse
    by (auto simp: x umtrm_eval_mtrm list_all_iff)
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ETP mt i) = (map (etabc ks cs) xs, ETP mt j)" using mapeq by simp
    show "esim n ks cs (enext tw ts) (ETP mt j) \<phi>'"
      unfolding f
      by (rule esim.EsTP[OF wf cse kse])
  qed
next
  case (EsTS ks cs mt n tw)
  note wf = EsTS.hyps(1) and cse = EsTS.hyps(2) and kse = EsTS.hyps(3)
    and kg = EsTS.prems(4) and sts = kgood_sorted[OF EsTS.prems(4)]
    and mts = EsTS.prems(1) and m = EsTS.prems(2)
  have x: "xs = map (\<lambda>x. eval_mtrm mt (EInt (integer_of_nat x))) ts"
    and f: "\<phi>' = mformula.MTS mt" using m by simp_all
  have t: "list_all (ftable ks) xs" by (rule kgood_tables[OF kg m])
  have mapeq: "map (etabc ks cs) xs = map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) ts"
    using t etabc_same[OF eframeD(1)[OF wf]] unfolding kse
    by (auto simp: x umtrm_eval_mtrm list_all_iff)
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ETS mt) = (map (etabc ks cs) xs, ETS mt)" using mapeq by simp
    show "esim n ks cs (enext tw ts) (ETS mt) \<phi>'"
      unfolding f
      by (rule esim.EsTS[OF wf cse kse])
  qed
next
  case (EsLet ks cs m kks tw \<phi>d \<phi> n \<psi>d \<psi> p)
  note wf = EsLet.hyps(1) and sim1 = EsLet.hyps(2)
    and IH1 = EsLet.hyps(3) and sim2 = EsLet.hyps(4) and IH2 = EsLet.hyps(5)
    and kg = EsLet.prems(4) and sts = kgood_sorted[OF EsLet.prems(4)]
    and mts = EsLet.prems(1) and mv = EsLet.prems(2)
  obtain as \<phi>2 where e1: "meval j m ts db \<phi> = (as, \<phi>2)" by (cases "meval j m ts db \<phi>")
  let ?as = "map (reorder [0..<m] kks) as"
  obtain bs \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) ?as db) \<psi> = (bs, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) ?as db) \<psi>")
  have x: "xs = bs" and f: "\<phi>' = mformula.MLet p m kks \<phi>2 \<psi>2" using mv e1 e2 by simp_all
  have kg1: "kgood m kks j ts db \<phi>" by (rule kgood_MLet(1)[OF kg])
  have kg2: "kgood n ks j ts (Mapping.update (p, m) ?as db) \<psi>" by (rule kgood_MLet(2)[OF kg e1])
  have fk: "eframe kks [0..<m]" by (rule esim_dframe[OF sim1])
  have ta: "list_all (ftable kks) as"
    by (rule kgood_tables[OF kg1 e1])
  have dt: "map (etabc kks [0..<m]) as = ?as"
    using ta etabc_reorder_eq[OF eframeD(1)[OF fk]] by (auto simp: list_all_iff)
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN"
    by (rule order_trans[OF _ EsLet.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kks [0..<m]) as, \<phi>d2)"
    and s1: "esim m kks [0..<m] (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts (Mapping.update (p, m) ?as db) \<psi>d
        = (map (etabc ks cs) bs, \<psi>d2)"
    and s2: "esim n ks cs (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ELet p m \<phi>d \<psi>d) = (map (etabc ks cs) xs, ELet p m \<phi>d2 \<psi>d2)"
      using d1 d2 unfolding x dt by simp
    show "esim n ks cs (enext tw ts) (ELet p m \<phi>d2 \<psi>d2) \<phi>'"
      unfolding f
      by (rule esim.EsLet[OF wf s1 s2])
  qed
next
  case (EsFrz ks cs m kks tw \<phi>d \<phi> n \<psi>d \<psi> \<rho>d \<rho> \<rho>L \<rho>Ld lv p jfrz jpsi0 jphi \<alpha>s wv pR tq rb d po ng)
  note wf = EsFrz.hyps(1) and sim1 = EsFrz.hyps(2)
    and IH1 = EsFrz.hyps(3) and sim2 = EsFrz.hyps(4) and IH2 = EsFrz.hyps(5)
    and sim3 = EsFrz.hyps(6) and IH3 = EsFrz.hyps(7)
    and szL = EsFrz.hyps(8) and szLd = EsFrz.hyps(9)
    and kg = EsFrz.prems(4) and sts = kgood_sorted[OF EsFrz.prems(4)]
    and mts = EsFrz.prems(1) and mv = EsFrz.prems(2) and le = EsFrz.prems(3)
  have kg1: "kgood m kks j ts db \<phi>" by (rule kgood_MFrz_phi[OF kg])
  have kg2: "kgood n ks j ts (Mapping.update (p, m) [] db) \<psi>" by (rule kgood_MFrz_psi[OF kg])
  have kg3: "kgood n ks j ts (Mapping.update (p, m) [] db) \<rho>" by (rule kgood_MFrz_rho[OF kg])
  let ?dbe = "Mapping.map_values (\<lambda>_ _. []) db"
  have sz1: "size \<phi> \<le> NN" and sz2: "size \<psi> \<le> NN" and sz3: "size \<rho> \<le> NN"
    by (rule order_trans[OF _ le], simp)+
  have szr: "size \<rho> < NN" by (rule order.strict_trans2[OF _ le]) simp
  \<comment> \<open>the bound formula: its tables, reordered to the positional columns, are its executable ones\<close>
  obtain as0 \<phi>2 where e1: "meval j m ts db \<phi> = (as0, \<phi>2)" by (cases "meval j m ts db \<phi>")
  let ?as = "map (reorder [0..<m] kks) as0"
  have fk: "eframe kks [0..<m]" by (rule esim_dframe[OF sim1])
  have ta0: "list_all (ftable kks) as0"
    by (rule kgood_tables[OF kg1 e1])
  have dt: "map (etabc kks [0..<m]) as0 = ?as"
    using ta0 etabc_reorder_eq[OF eframeD(1)[OF fk]] by (auto simp: list_all_iff)
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (?as, \<phi>d2)"
    and s1: "esim m kks [0..<m] (enext tw ts) \<phi>d2 \<phi>2"
    using IH1[OF mts e1 sz1 kg1] unfolding dt by blast
  \<comment> \<open>the body and the replay base, against the database in which the bound predicate is empty\<close>
  obtain zs0 \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) [] db) \<psi> = (zs0, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<psi>")
  obtain \<psi>d2 where d2: "eeval j ts (Mapping.update (p, m) [] db) \<psi>d
        = (map (etabc ks cs) zs0, \<psi>d2)"
    and s2: "esim n ks cs (enext tw ts) \<psi>d2 \<psi>2"
    using IH2[OF mts e2 sz2 kg2] by blast
  obtain rs \<rho>2 where e4: "meval j n ts (Mapping.update (p, m) [] db) \<rho> = (rs, \<rho>2)"
    by (cases "meval j n ts (Mapping.update (p, m) [] db) \<rho>")
  obtain \<rho>d2 where d4: "eeval j ts (Mapping.update (p, m) [] db) \<rho>d
        = (map (etabc ks cs) rs, \<rho>d2)"
    and s4: "esim n ks cs (enext tw ts) \<rho>d2 \<rho>2"
    using IH3[OF mts e4 sz3 kg3] by blast
  \<comment> \<open>the frozen tuples the two runs are handed are the same list\<close>
  let ?zout = "drop (jfrz - jpsi0) zs0"
  let ?as1 = "drop (jfrz - jphi + length ?zout) (\<alpha>s @ ?as)"
  let ?F = "frz_fill ng (\<alpha>s @ ?as)"
  let ?A = "Set.insert ?F (set (\<alpha>s @ ?as))"
  have subA: "set ?as1 \<subseteq> ?A"
    by (auto dest: in_set_dropD)
  have sz\<rho>2: "size \<rho>2 = size \<rho>"
    using default_maux.size_snd_meval[of j n ts "Mapping.update (p, m) [] db" \<rho>] e4 by simp
  have sz\<rho>d2: "size \<rho>d2 = size \<rho>d"
    using size_snd_eeval[of j ts "Mapping.update (p, m) [] db" \<rho>d] d4 by simp
  \<comment> \<open>the copies and the window's moves: the two runs evaluate related states on the same tables\<close>
  define R where "R st dst \<longleftrightarrow> esim n ks cs (enext tw ts) dst st \<and> size st = size \<rho> \<and> size dst = size \<rho>d"
    for st dst
  have agree: "fst (eeval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>d) =
      map (etabc ks cs) (fst (meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>)) \<and>
      R (snd (meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>))
        (snd (eeval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>d))"
    if r: "R \<chi> \<chi>d" and X: "X \<in> ?A"
      and kgc: "kgood n ks j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>" for \<chi> \<chi>d c X
  proof -
    obtain us \<chi>' where eu: "meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi> = (us, \<chi>')"
      by (cases "meval j n [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>")
    have sz\<chi>: "size \<chi> < NN"
      using r szr by (simp add: R_def)
    obtain dus where du: "eeval j [] (Mapping.update (p, m) (replicate c X) ?dbe) \<chi>d
        = (map (etabc ks cs) us, dus)" and sdu: "esim n ks cs (enext (enext tw ts) []) dus \<chi>'"
      using Q[OF sz\<chi> conjunct1[OF r[unfolded R_def]] _ eu kgc] by auto
    have "size \<chi>' = size \<rho>"
      using default_maux.size_snd_meval[of j n "[]" "Mapping.update (p, m) (replicate c X) ?dbe" \<chi>]
        eu r by (simp add: R_def)
    moreover have "size dus = size \<rho>d"
      using size_snd_eeval[of j "[]" "Mapping.update (p, m) (replicate c X) ?dbe" \<chi>d] du r
      by (simp add: R_def)
    ultimately show ?thesis
      using du eu sdu by (simp add: R_def enext_def)
  qed
  \<comment> \<open>the live copy, fed the new time points\<close>
  let ?dbL = "Mapping.update (p, m) (replicate (length ts) (hd ?as1)) db"
  define lrk where "lrk = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if ?zout = [] \<and> ?as1 \<noteq> [] then Some (g, meval j n ts ?dbL \<rho>L) else None)"
  define lrd where "lrd = (case lv of None \<Rightarrow> None | Some g \<Rightarrow>
    if ?zout = [] \<and> ?as1 \<noteq> [] then Some (g, eeval j ts ?dbL \<rho>Ld) else None)"
  have lrel: "rel_option (\<lambda>(k, us, \<sigma>) (k', us', \<sigma>'). k' = k \<and> us' = map (etabc ks cs) us \<and> R \<sigma> \<sigma>')
      lrk lrd"
  proof (cases "lv \<noteq> None \<and> ?zout = [] \<and> ?as1 \<noteq> []")
    case True
    then obtain g where lv: "lv = Some g"
      by auto
    have simL: "esim n ks cs tw \<rho>Ld \<rho>L"
      using EsFrz.hyps(10) True by blast
    have szl: "size \<rho>L < NN"
      by (rule order.strict_trans2[OF _ le]) simp
    have hin: "hd ?as1 \<in> set ?as1"
      by (rule hd_in_set) (use True in blast)
    have as1: "?as1 = drop (jfrz - jphi) (\<alpha>s @ ?as)"
      using True by simp
    have kgL: "kgood n ks j ts ?dbL \<rho>L"
      using kgood_MFrz_live[OF kg e1 lv, folded as1] True by blast
    obtain us \<chi> where eL: "meval j n ts ?dbL \<rho>L = (us, \<chi>)"
      by (cases "meval j n ts ?dbL \<rho>L")
    obtain dus where dL: "eeval j ts ?dbL \<rho>Ld = (map (etabc ks cs) us, dus)"
      and sL: "esim n ks cs (enext tw ts) dus \<chi>"
      using Q[OF szl simL mts eL kgL] by blast
    have "size \<chi> = size \<rho>"
      using default_maux.size_snd_meval[of j n ts ?dbL \<rho>L] eL szL by simp
    moreover have "size dus = size \<rho>d"
      using size_snd_eeval[of j ts ?dbL \<rho>Ld] dL szLd by simp
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
  let ?sd = "(\<rho>d2, wv, pR + length rs, ?tq1, drop ?k (map (etabc ks cs) rb @ map (etabc ks cs) rs))"
  obtain ys as' lvk \<rho>3 w3 pR3 tq3 rb3 where e3: "frz_live_loop size (meval j n) (p, m) ?dbe ?F d po j
      (jfrz + length ?zout) ?as1 lrk ?s = (ys, as', lvk, \<rho>3, w3, pR3, tq3, rb3)"
    by (metis prod_cases4 prod_cases5)
  obtain dys das' lvd sd3 where d3: "frz_live_loop size (eeval j) (p, m) ?dbe ?F d po j
      (jfrz + length ?zout) ?as1 lrd ?sd = (dys, das', lvd, sd3)"
    by (metis prod_cases4)
  have d3': "frz_live_loop size (eeval j) (p, m) ?dbe (id ?F) d po j
      (jfrz + length ?zout) (map id ?as1) lrd ?sd = (dys, das', lvd, sd3)"
    using d3 by simp
  have st0: "frz_st_rel R (etabc ks cs) ?s ?sd"
    using s4 sz\<rho>2 sz\<rho>d2 by (simp add: R_def drop_map flip: map_append)
  have frel: "dys = map (etabc ks cs) ys \<and> das' = map id as' \<and>
      rel_option (\<lambda>(k, \<sigma>) (k', \<sigma>'). k' = k \<and> R \<sigma> \<sigma>') lvk lvd \<and>
      frz_st_rel R (etabc ks cs) (\<rho>3, w3, pR3, tq3, rb3) sd3"
  proof (rule frz_live_loop_rel_inv[where K = "frz_kinv n ks j (p, m) d ?dbe ?A" and A = ?A,
        OF _ _ subA st0 _ lrel e3 d3'])
    \<comment> \<open>the window's move\<close>
    fix s s' i
    assume st: "frz_st_rel R (etabc ks cs) s s'" and K: "frz_kinv n ks j (p, m) d ?dbe ?A s"
    obtain \<rho>' w' pR' tq' rb' where s: "s = (\<rho>', w', pR', tq', rb')"
      by (metis prod_cases5)
    with st obtain \<rho>d' where s': "s' = (\<rho>d', w', pR', tq', map (etabc ks cs) rb')" and R: "R \<rho>' \<rho>d'"
      by (cases s') auto
    let ?a = "frz_adv d w' i j tq'"
    have a: "?a \<le> j - w'"
      by (rule frz_adv_le) (use K in \<open>auto simp: s frz_kinv_def\<close>)
    have Fa: "?F \<in> ?A" by simp
    obtain rs2 \<sigma>2 where e: "meval j n [] (Mapping.update (p, m) (replicate ?a ?F) ?dbe) \<rho>' = (rs2, \<sigma>2)"
      by fastforce
    obtain rs2' \<sigma>2' where e': "eeval j [] (Mapping.update (p, m) (replicate ?a (id ?F)) ?dbe) \<rho>d' = (rs2', \<sigma>2')"
      by fastforce
    have ag: "rs2' = map (etabc ks cs) rs2 \<and> R \<sigma>2 \<sigma>2'"
      using agree[OF R Fa frz_kinv_call[OF K[unfolded s] Fa a]] e e' by simp
    have sz: "size \<sigma>2 = size \<rho>'" "size \<sigma>2' = size \<rho>d'"
      using ag R by (simp_all add: R_def)
    show "frz_st_rel R (etabc ks cs) (frz_adv_st size (meval j n) (p, m) ?dbe ?F d j i s)
        (frz_adv_st size (eeval j) (p, m) ?dbe (id ?F) d j i s') \<and>
      frz_kinv n ks j (p, m) d ?dbe ?A (frz_adv_st size (meval j n) (p, m) ?dbe ?F d j i s)"
      using frz_kinv_adv[OF K Fa, of i] s s' e e' ag sz
      by (auto simp: frz_adv_st_def Let_def drop_map[symmetric])
  next
    \<comment> \<open>a copy\<close>
    fix \<rho>' w' pR' tq' rb' \<rho>d' X i
    assume R: "R \<rho>' \<rho>d'" and K: "frz_kinv n ks j (p, m) d ?dbe ?A (\<rho>', w', pR', tq', rb')" and X: "X \<in> ?A"
    show "fst (eeval j [] (Mapping.update (p, m) (replicate (frz_cut po w' i j) (id X)) ?dbe) \<rho>d') =
        map (etabc ks cs) (fst (meval j n [] (Mapping.update (p, m) (replicate (frz_cut po w' i j) X) ?dbe) \<rho>')) \<and>
      R (snd (meval j n [] (Mapping.update (p, m) (replicate (frz_cut po w' i j) X) ?dbe) \<rho>'))
        (snd (eeval j [] (Mapping.update (p, m) (replicate (frz_cut po w' i j) (id X)) ?dbe) \<rho>d'))"
      using agree[OF R X frz_kinv_call[OF K X frz_cut_le]] by simp
  next
    show "frz_kinv n ks j (p, m) d ?dbe ?A ?s"
      by (rule kgood_MFrz_kinv[OF kg e1 e4])
  qed
  have sub: "set as' \<subseteq> set ?as1"
    using frz_live_loop_inv[where P = "\<lambda>_. True" and T = "\<lambda>_. True", OF _ _ _ e3] by (simp add: list_all_iff)
  obtain \<rho>d3 where sd3: "sd3 = (\<rho>d3, w3, pR3, tq3, map (etabc ks cs) rb3)" and R3: "R \<rho>3 \<rho>d3"
    using frel by (cases sd3) auto
  let ?lvk = "if po then None else lvk"
  let ?lvd = "if po then None else lvd"
  have keep: "frz_keep_lv ?lvd \<rho>Ld = frz_keep_lv ?lvk \<rho>L"
    "frz_keep_lv ?lvk \<rho>L \<noteq> None \<longrightarrow> esim n ks cs (enext tw ts) (frz_keep_st ?lvd \<rho>Ld) (frz_keep_st ?lvk \<rho>L)"
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
  have std: "(let zs0_out = drop (jfrz - jpsi0) (map (etabc ks cs) zs0);
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ ?as)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ ?as), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, eeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>Ld)
         else None)) = (map (etabc ks cs) ?zout, jfrz + length ?zout, ?F, ?as1, lrd)"
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
  have dq: "eeval j ts db (EFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s \<rho>d wv pR tq (map (etabc ks cs) rb) d po ng lv \<rho>Ld) =
      (map (etabc ks cs) ?zout @ dys, EFrz p m \<phi>d2 \<psi>d2 (jfrz + length ?zout + length dys) (jpsi0 + length zs0)
        (jphi + length as0) das' \<rho>d3 w3 pR3 tq3 (map (etabc ks cs) rb3) d po ng
        (frz_keep_lv ?lvd \<rho>Ld) (frz_keep_st ?lvd \<rho>Ld))"
    by (simp only: eeval.simps d1 d2 d4 std length_map d3[unfolded sd3]
        Let_def[where s = "Mapping.update (p, m) [] db"]
        Let_def[where s = "(?as, \<phi>d2)"] Let_def[where s = "(map (etabc ks cs) zs0, \<psi>d2)"]
        Let_def[where s = "(map (etabc ks cs) rs, \<rho>d2)"]
        Let_def[where s = "(map (etabc ks cs) ?zout, jfrz + length ?zout, ?F, ?as1, lrd)"]
        Let_def[where s = "(dys, das', lvd, \<rho>d3, w3, pR3, tq3, map (etabc ks cs) rb3)"] prod.case)
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s \<rho>d wv pR tq (map (etabc ks cs) rb) d po ng lv \<rho>Ld)
        = (map (etabc ks cs) xs, EFrz p m \<phi>d2 \<psi>d2 ?jfrz1 (jpsi0 + length zs0) (jphi + length as0) as'
            \<rho>d3 w3 pR3 tq3 (map (etabc ks cs) rb3) d po ng (frz_keep_lv ?lvk \<rho>L) (frz_keep_st ?lvd \<rho>Ld))"
      unfolding dq x using frel keep(1) by simp
    show "esim n ks cs (enext tw ts) (EFrz p m \<phi>d2 \<psi>d2 ?jfrz1 (jpsi0 + length zs0) (jphi + length as0) as'
            \<rho>d3 w3 pR3 tq3 (map (etabc ks cs) rb3) d po ng (frz_keep_lv ?lvk \<rho>L) (frz_keep_st ?lvd \<rho>Ld)) \<phi>'"
      unfolding f
      by (rule esim.EsFrz[OF wf s1 s2])
        (use R3 szL szLd keep(2) in \<open>simp_all add: R_def\<close>)
  qed
next
  case (EsLetPast ks cs m kks tw \<phi>d \<phi> n \<psi>d \<psi> p i buf)
  note wf = EsLetPast.hyps(1) and sim1 = EsLetPast.hyps(2)
    and IH1 = EsLetPast.hyps(3) and sim2 = EsLetPast.hyps(4) and IH2 = EsLetPast.hyps(5)
    and kg = EsLetPast.prems(4) and sts = kgood_sorted[OF EsLetPast.prems(4)]
    and mts = EsLetPast.prems(1) and mv = EsLetPast.prems(2) and le = EsLetPast.prems(3)
  have sz2: "size \<psi> \<le> NN" by (rule order_trans[OF _ le]) simp
  have szs: "size \<phi> < NN" by (rule order.strict_trans2[OF _ le]) simp
  \<comment> \<open>the rounds of the bound formula\<close>
  obtain as i2 buf2 \<phi>2 where e1: "letpast_meval m kks j i [] (list_of_option buf) (p, m) ts db \<phi>
      = (as, i2, buf2, \<phi>2)"
    by (cases "letpast_meval m kks j i [] (list_of_option buf) (p, m) ts db \<phi>") auto
  have e1': "letpast_meval0 (\<lambda>ts db \<phi>. apfst (map (reorder [0..<m] kks)) (meval j m ts db \<phi>))
      j i [] (list_of_option buf) (p, m) ts db \<phi> = (as, i2, buf2, \<phi>2)"
    using e1 by (simp add: default_maux.letpast_meval_def)
  have lr: "\<exists>\<phi>d'. letpast_meval0 (eeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>d
        = (as, i2, buf2, \<phi>d') \<and> esim m kks [0..<m] (enext tw ts) \<phi>d' \<phi>2"
    by (rule letpast_meval0_rel[OF _ e1' snd_conv szs sim1 mts refl
        kgood_MLetPast_init[OF kg]]) (rule Q)
  obtain \<phi>d2 where d1: "letpast_meval0 (eeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>d
        = (as, i2, buf2, \<phi>d2)"
    and s1: "esim m kks [0..<m] (enext tw ts) \<phi>d2 \<phi>2" using lr by blast
  \<comment> \<open>the body, against the database in which the bound predicate holds the rounds' output\<close>
  have kg2: "kgood n ks j ts (Mapping.update (p, m) as db) \<psi>"
    by (rule kgood_MLetPast_body[OF kg e1])
  obtain bs \<psi>2 where e2: "meval j n ts (Mapping.update (p, m) as db) \<psi> = (bs, \<psi>2)"
    by (cases "meval j n ts (Mapping.update (p, m) as db) \<psi>")
  obtain \<psi>d2 where d2: "eeval j ts (Mapping.update (p, m) as db) \<psi>d = (map (etabc ks cs) bs, \<psi>d2)"
    and s2: "esim n ks cs (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have x: "xs = bs" and f: "\<phi>' = mformula.MLetPast p m kks \<phi>2 \<psi>2 i2 buf2"
    using mv e1 e2 by simp_all
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ELetPast p m \<phi>d \<psi>d i buf)
        = (map (etabc ks cs) xs, ELetPast p m \<phi>d2 \<psi>d2 i2 buf2)"
      using d1 d2 unfolding x by simp
    show "esim n ks cs (enext tw ts) (ELetPast p m \<phi>d2 \<psi>d2 i2 buf2) \<phi>'"
      unfolding f
      by (rule esim.EsLetPast[OF wf s1 s2])
  qed
next
  case (EsTrigger kR cR n kL cL tw \<phi>d \<phi> \<psi>d \<psi> args dags pl aux daux buf dbuf nts dnts)
  note wf = EsTrigger.hyps(1)
    and sim1 = EsTrigger.hyps(2) and IH1 = EsTrigger.hyps(3)
    and sim2 = EsTrigger.hyps(4) and IH2 = EsTrigger.hyps(5)
    and sub = EsTrigger.hyps(6) and aL = EsTrigger.hyps(7) and aR = EsTrigger.hyps(8)
    and m0 = EsTrigger.hyps(9) and dag = EsTrigger.hyps(10) and pe = EsTrigger.hyps(11)
    and rel = EsTrigger.hyps(12) and ne = EsTrigger.hyps(13)
    and kg = EsTrigger.prems(4) and sts = kgood_sorted[OF EsTrigger.prems(4)]
    and mts = EsTrigger.prems(1) and m = EsTrigger.prems(2)
  have kg1: "kgood n kL j ts db \<phi>" and kg2: "kgood n kR j ts db \<psi>"
    using kgood_MTrigger[OF kg] aL aR by simp_all
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
    by (rule order_trans[OF _ EsTrigger.prems(3)], simp)+
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) as, \<phi>d2)"
    and s1: "esim n kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) bs, \<psi>d2)"
    and s2: "esim n kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have ta: "list_all (ftable kL) as"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) bs"
    by (rule kgood_tables[OF kg2 e2])
  obtain dzs daux2 ebuf2 dnts2 where d3: "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
      (mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) (rbuf2 dbuf)) (nts @ ts)
      = ((dzs, daux2), ebuf2, dnts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
      (mbuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) (rbuf2 dbuf)) (nts @ ts)") auto
  have step: "dzs = map (etabc kR cR) zs \<and> dnts2 = nts2 \<and>
      etrigger_rel kR cR kL cL args (enext tw ts) aux2 daux2 buf2 ebuf2 nts2"
    by (rule etrigger_step_rel[OF wf fL sub aL aR m0 rel ta tb sts mts e3 d3[unfolded dag]])
  obtain ub un where eu: "mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux)
      (mebuf2_add (map (etabc kL cL) as) (map (etabc kR cR) bs) dbuf) (dnts @@ ts)
      = ((dzs, daux2), ub, un)" and ub: "rbuf2 ub = ebuf2" and un: "Rep_mbuf_t un = dnts2"
    by (rule mebuf2T_take_obtain[OF d3[unfolded mbuf2_add_rbuf2 ne[symmetric]]])
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (ETrigger dags pl \<phi>d \<psi>d dbuf dnts daux)
        = (map (etabc kR cR) xs, ETrigger dags pl \<phi>d2 \<psi>d2 ub un daux2)"
      using d1 d2 eu step x by simp
    show "esim n kR cR (enext tw ts) (ETrigger dags pl \<phi>d2 \<psi>d2 ub un daux2) \<phi>'"
      unfolding f
      by (rule esim.EsTrigger[OF wf s1 s2 sub
            aL aR m0 dag pe]) (use step ub un in simp_all)
  qed
next
  case (EsAndTrigger ks cs n tw \<alpha>d \<alpha> kL cL \<phi>d \<phi> kR cR \<psi>d \<psi> args dags pl buf1 dbf1 aux daux buf2 dbf2 nts dnts)
  note wf = EsAndTrigger.hyps(1)
    and sim0 = EsAndTrigger.hyps(2) and IH0 = EsAndTrigger.hyps(3)
    and sim1 = EsAndTrigger.hyps(4) and IH1 = EsAndTrigger.hyps(5)
    and sim2 = EsAndTrigger.hyps(6) and IH2 = EsAndTrigger.hyps(7)
    and subLR = EsAndTrigger.hyps(8) and subR = EsAndTrigger.hyps(9)
    and aL = EsAndTrigger.hyps(10) and aR = EsAndTrigger.hyps(11) and ok = EsAndTrigger.hyps(12)
    and dag = EsAndTrigger.hyps(13) and ple = EsAndTrigger.hyps(14)
    and bf1 = EsAndTrigger.hyps(15) and rel = EsAndTrigger.hyps(16) and ne = EsAndTrigger.hyps(17)
    and kg = EsAndTrigger.prems(4) and sts = kgood_sorted[OF EsAndTrigger.prems(4)]
    and mts = EsAndTrigger.prems(1) and m = EsAndTrigger.prems(2)
  have kg0: "kgood n ks j ts db \<alpha>" and kg1: "kgood n kL j ts db \<phi>" and kg2: "kgood n kR j ts db \<psi>"
    using kgood_MAndTrigger[OF kg] aL aR by simp_all
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
    by (rule order_trans[OF _ EsAndTrigger.prems(3)], simp)+
  obtain \<alpha>d2 where d0: "eeval j ts db \<alpha>d = (map (etabc ks cs) as, \<alpha>d2)"
    and s0: "esim n ks cs (enext tw ts) \<alpha>d2 \<alpha>2" using IH0[OF mts e0 sz0 kg0] by blast
  obtain \<phi>d2 where d1: "eeval j ts db \<phi>d = (map (etabc kL cL) xs1, \<phi>d2)"
    and s1: "esim n kL cL (enext tw ts) \<phi>d2 \<phi>2" using IH1[OF mts e1 sz1 kg1] by blast
  obtain \<psi>d2 where d2: "eeval j ts db \<psi>d = (map (etabc kR cR) ys1, \<psi>d2)"
    and s2: "esim n kR cR (enext tw ts) \<psi>d2 \<psi>2" using IH2[OF mts e2 sz2 kg2] by blast
  have fL: "eframe kL cL" by (rule esim_dframe[OF sim1])
  have fR: "eframe kR cR" by (rule esim_dframe[OF sim2])
  have t0: "list_all (ftable ks) as"
    by (rule kgood_tables[OF kg0 e0])
  have ta: "list_all (ftable kL) xs1"
    by (rule kgood_tables[OF kg1 e1])
  have tb: "list_all (ftable kR) ys1"
    by (rule kgood_tables[OF kg2 e2])
  obtain dws daux2 dbf2' dnts2 where d3: "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
      ([], daux) (mbuf2_add (map (etabc kL cL) xs1) (map (etabc kR cR) ys1) (rbuf2 dbf2)) (nts @ ts)
      = ((dws, daux2), dbf2', dnts2)"
    by (cases "mbuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
      ([], daux) (mbuf2_add (map (etabc kL cL) xs1) (map (etabc kR cR) ys1) (rbuf2 dbf2))
      (nts @ ts)") auto
  have step: "list_all2 (etres kR cR) ws dws \<and> dnts2 = nts2 \<and>
      etrigger_rel kR cR kL cL args (enext tw ts) aux2 daux2 buf2' dbf2' nts2"
    by (rule eandtrigger_step_rel[OF fR fL subLR aL aR ok rel ta tb sts mts e3 d3[unfolded dag]])
  obtain ub2 un where eu: "mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
      let ax = gupdate_mmtaux dags t r1 r2 ax
      in (ws @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
      ([], daux) (mebuf2_add (map (etabc kL cL) xs1) (map (etabc kR cR) ys1) dbf2) (dnts @@ ts)
      = ((dws, daux2), ub2, un)" and ub2: "rbuf2 ub2 = dbf2'" and un: "Rep_mbuf_t un = dnts2"
    by (rule mebuf2T_take_obtain[OF d3[unfolded mbuf2_add_rbuf2 ne[symmetric]]])
  have badd0: "eandbuf ks cs kR cR (mbuf2_add as ws buf1)
      (mbuf2_add (map (etabc ks cs) as) dws (rbufo dbf1))"
    by (rule eandbuf_add[OF bf1 t0]) (use step in simp)
  have badd: "eandbuf ks cs kR cR (mbuf2_add as ws buf1)
      (rbufo (mebuf2_add (map (etabc ks cs) as) dws dbf1))"
    using badd0 by (simp only: mbuf2_add_rbufo)
  obtain dbf1' where d4: "mbuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> gbin_join pl r1 True z) (rbufo (mebuf2_add (map (etabc ks cs) as) dws dbf1))
      = (map (etabc ks cs) zs, dbf1')"
    and bf1': "eandbuf ks cs kR cR buf1' dbf1'"
    using eandbuf_take[OF wf fR subR badd e4] unfolding ple by blast
  obtain zs' ub1 where eu1: "mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
        | Some z \<Rightarrow> gbin_join pl r1 True z) (mebuf2_add (map (etabc ks cs) as) dws dbf1) = (zs', ub1)"
    by (metis surj_pair)
  have r1: "zs' = map (etabc ks cs) zs \<and> rbufo ub1 = dbf1'"
    using eu1 d4 mbuf2_take_rbufo[of
        "\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> gbin_join pl r1 True z"
        "mebuf2_add (map (etabc ks cs) as) dws dbf1"]
    by (simp del: mbuf2_take.simps mebuf2_take.simps)
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EAndTrigger pl \<alpha>d dbf1 dags \<phi>d \<psi>d dbf2 dnts daux)
        = (map (etabc ks cs) xs, EAndTrigger pl \<alpha>d2 ub1 dags \<phi>d2 \<psi>d2 ub2 un daux2)"
      using d0 d1 d2 eu eu1 r1 step x by simp
    show "esim n ks cs (enext tw ts) (EAndTrigger pl \<alpha>d2 ub1 dags \<phi>d2 \<psi>d2 ub2 un daux2) \<phi>'"
      unfolding f
      by (rule esim.EsAndTrigger[OF wf s0 s1 s2
            subLR subR aL aR ok dag ple]) (use bf1' r1 step ub2 un in simp_all)
  qed
next
  case (EsMatchP ks cs mr \<psi>s mrs dss css L Ld n tw pls buf dbuf dnts nts aux daux I)
  note wf = EsMatchP.hyps(1) and sr = EsMatchP.hyps(2)
    and okm = EsMatchP.hyps(3) and fvA = EsMatchP.hyps(4) and dm = EsMatchP.hyps(5)
    and mrsd = EsMatchP.hyps(6) and dsse = EsMatchP.hyps(7) and lcs = EsMatchP.hyps(8)
    and lL = EsMatchP.hyps(9) and lLd = EsMatchP.hyps(10) and fas = EsMatchP.hyps(11)
    and csub = EsMatchP.hyps(12) and la = EsMatchP.hyps(13) and pe = EsMatchP.hyps(14)
    and bf = EsMatchP.hyps(15) and ne = EsMatchP.hyps(16) and rel = EsMatchP.hyps(17)
    and kg = EsMatchP.prems(4) and sts = kgood_sorted[OF EsMatchP.prems(4)]
    and mts = EsMatchP.prems(1) and m = EsMatchP.prems(2)
  let ?R = "map (meval j n ts db) L"
  let ?dR = "map (eeval j ts db) Ld"
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
  have kgL: "\<forall>i < length L. kgood n (dss ! i) j ts db (L ! i)"
    using kgood_MMatchP[OF kg] by blast
  have lcL: "length css = length L" using lcs lL by simp
  have ldL: "length dss = length L" using dsse lL by simp
  have sz: "size_list size L \<le> NN" using EsMatchP.prems(3) by simp
  note ops = eeval_operands[OF la lLd lcL ldL mts sz kgL bf]
  note dl0 = ops(1) and dl = ops(2) and dl2 = ops(3) and badd = ops(4)
  \<comment> \<open>the masks the window probes with\<close>
  have msk: "map emb_msk pls = map (emsk cs) css"
    unfolding pe map_map o_def
  proof (rule map_cong[OF refl])
    fix c assume c: "c \<in> set css"
    then obtain i where i: "i < length css" and ci: "c = css ! i" by (auto simp: in_set_conv_nth)
    have fi: "eframe (dss ! i) (css ! i)" using fas i lcs by simp
    show "emb_msk (emb_plan cs c) = emsk cs c"
    proof (rule emb_msk_emb_plan)
      show "sorted_wrt (<) cs" by (rule eframeD(2)[OF wf])
      show "sorted_wrt (<) c" using eframeD(2)[OF fi] ci by simp
      show "set c \<subseteq> set cs" using csub i ci lcs eframeD(3)[OF fi] eframeD(3)[OF wf] dsse
        by simp
    qed
  qed
  \<comment> \<open>one firing of the window\<close>
  define Rel where "Rel = (\<lambda>(zs :: event_data table list, ax) (dzs :: event_data table list, dax).
      dzs = map (etabc ks cs) zs \<and> emrd_rel ks cs ax dax)"
  have step: "Rel (?F as t u) (?G (etabcs dss css as) t u')"
    if las: "length as = length css"
      and mas: "\<forall>i < length css. ftable (dss ! i) (as ! i)"
      and ru: "Rel u u'" for as u u' t
  proof -
    obtain zs0 ax where u: "u = (zs0, ax)" by (cases u)
    obtain dzs0 dax where u': "u' = (dzs0, dax)" by (cases u')
    have dz: "dzs0 = map (etabc ks cs) zs0" and rax: "emrd_rel ks cs ax dax"
      using ru by (simp_all add: Rel_def u u')
    interpret ematchP_frame ks cs \<psi>s css as mrs
    proof
      show "eframe ks cs" by (rule wf)
      show "length css = length \<psi>s" by (rule lcs)
      show "\<And>i. i < length \<psi>s \<Longrightarrow> eframe (Formula.fv_list (\<psi>s ! i)) (css ! i)"
        using fas dsse by simp
      show "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set ks" using csub by simp
      show "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel \<and> finite rel) \<psi>s as"
        using las lcs dsse mas by (fastforce simp: list_all2_conv_all_nth)
      show "distinct mrs" by (rule dm)
      show "\<And>ms. ms \<in> set mrs \<Longrightarrow>
          Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<psi>s) \<and>
          ok (length \<psi>s) ms \<and> set ks = fv_regex (from_mregex ms \<psi>s)"
        using mrsd sr okm fvA
        by (auto simp: RPDs_safe RPDs_ok RPDs_safe_fv_regex)
    qed
    have uu: "etabc ks cs (fst (update_matchP ks dss I mr mrs as t ax))
        = fst (gupdate_matchP (map (emsk cs) css) I mr mrs (etabcs dss css as) t dax) \<and>
      emrd_rel ks cs (snd (update_matchP ks dss I mr mrs as t ax))
        (snd (gupdate_matchP (map (emsk cs) css) I mr mrs (etabcs dss css as) t dax))"
      using etabc_gupdate_matchP[OF rax] unfolding dsse .
    show ?thesis using dz uu by (simp add: Rel_def u u' msk Let_def split_beta)
  qed
  have rz: "Rel ([], aux) ([], daux)" using rel by (simp add: Rel_def)
  obtain w2 ebuf2 where dt:
    "mbufnt_take ?G ([], daux) (map Rep_mbuf_t (mebufn_add (map fst ?dR) dbuf)) 0 (nts @ ts)
       = (w2, ebuf2, tt2, nts2)"
    and rw: "Rel (zs, aux2) w2" and bf2: "ebufn dss css buf2 ebuf2"
    using ebufn_nt_take[where R = Rel and f = "?F" and g = "?G", OF badd step rz g0] by blast
  obtain uzs daux2 ub un where dte: "mebufnt_take (\<lambda>rels t (zs, ax).
      let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax in (zs @@ [z], ax))
      (mbuf_t_empty, daux) (mebufn_add (map fst ?dR) dbuf) 0 (dnts @@ ts) = ((uzs, daux2), ub, tt2, un)"
    and w2: "w2 = (Rep_mbuf_t uzs, daux2)" and ub: "map Rep_mbuf_t ub = ebuf2"
    and un: "Rep_mbuf_t un = nts2"
    by (rule mebufnt_take_matchP_obtain[OF dt[unfolded ne[symmetric]]])
  have dzs: "Rep_mbuf_t uzs = map (etabc ks cs) zs" and rel2: "emrd_rel ks cs aux2 daux2"
    using rw by (simp_all add: Rel_def w2)
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EMatchP (length cs) I mr mrs pls Ld dbuf dnts daux)
        = (map (etabc ks cs) xs, EMatchP (length cs) I mr mrs pls (map snd ?dR) ub un daux2)"
      using dte x dzs by (simp add: Let_def del: mebufnt_take.simps)
    show "esim n ks cs (enext tw ts) (EMatchP (length cs) I mr mrs pls (map snd ?dR) ub un daux2)
        \<phi>'"
      unfolding fe
      by (rule esim.EsMatchP[OF wf sr okm fvA dm
            mrsd dsse lcs _ _ fas csub _ pe _ un rel2])
        (use lL lLd dl2 dl0 bf2 ub in auto)
  qed
next
  case (EsMatchF ks cs mr \<psi>s mrs dss css L Ld n tw pls buf dbuf dnts nts aux daux I t)
  note wf = EsMatchF.hyps(1) and sr = EsMatchF.hyps(2)
    and okm = EsMatchF.hyps(3) and fvA = EsMatchF.hyps(4) and dm = EsMatchF.hyps(5)
    and mrsd = EsMatchF.hyps(6) and dsse = EsMatchF.hyps(7) and lcs = EsMatchF.hyps(8)
    and lL = EsMatchF.hyps(9) and lLd = EsMatchF.hyps(10) and fas = EsMatchF.hyps(11)
    and csub = EsMatchF.hyps(12) and la = EsMatchF.hyps(13) and pe = EsMatchF.hyps(14)
    and bf = EsMatchF.hyps(15) and ne = EsMatchF.hyps(16) and rel = EsMatchF.hyps(17)
    and kg = EsMatchF.prems(4) and sts = kgood_sorted[OF EsMatchF.prems(4)]
    and mts = EsMatchF.prems(1) and m = EsMatchF.prems(2)
  let ?R = "map (meval j n ts db) L"
  let ?dR = "map (eeval j ts db) Ld"
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
  have kgL: "\<forall>i < length L. kgood n (dss ! i) j ts db (L ! i)"
    using kgood_MMatchF[OF kg] by blast
  have lcL: "length css = length L" using lcs lL by simp
  have ldL: "length dss = length L" using dsse lL by simp
  have sz: "size_list size L \<le> NN" using EsMatchF.prems(3) by simp
  note ops = eeval_operands[OF la lLd lcL ldL mts sz kgL bf]
  note dl0 = ops(1) and dl = ops(2) and dl2 = ops(3) and badd = ops(4)
  \<comment> \<open>one firing of the window\<close>
  interpret ematchF_frame ks cs \<psi>s css mrs
  proof
    show "eframe ks cs" by (rule wf)
    show "length css = length \<psi>s" by (rule lcs)
    show "\<And>i. i < length \<psi>s \<Longrightarrow> eframe (Formula.fv_list (\<psi>s ! i)) (css ! i)"
      using fas dsse by simp
    show "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set ks" using csub by simp
    show "distinct mrs" by (rule dm)
    show "\<And>ms. ms \<in> set mrs \<Longrightarrow>
        Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<psi>s) \<and>
        ok (length \<psi>s) ms \<and> set ks = fv_regex (from_mregex ms \<psi>s)"
      using mrsd sr okm fvA by (auto simp: LPDs_safe LPDs_ok LPDs_safe_fv_regex)
  qed
  have msk: "map emb_msk pls = map (emsk cs) css"
    unfolding pe map_map o_def
  proof (rule map_cong[OF refl])
    fix c assume c: "c \<in> set css"
    then obtain i where i: "i < length css" and ci: "c = css ! i" by (auto simp: in_set_conv_nth)
    have fi: "eframe (dss ! i) (css ! i)" using fas i lcs by simp
    show "emb_msk (emb_plan cs c) = emsk cs c"
    proof (rule emb_msk_emb_plan)
      show "sorted_wrt (<) cs" by (rule eframeD(2)[OF wf])
      show "sorted_wrt (<) c" using eframeD(2)[OF fi] ci by simp
      show "set c \<subseteq> set cs" using csub i ci lcs eframeD(3)[OF fi] eframeD(3)[OF wf] dsse
        by simp
    qed
  qed
  have step: "emld_rel ks cs \<psi>s css (?F as tt u) (?G (etabcs dss css as) tt u')"
    if las: "length as = length css"
      and mas: "\<forall>i < length css. ftable (dss ! i) (as ! i)"
      and ru: "emld_rel ks cs \<psi>s css u u'" for as u u' tt
  proof -
    have wfr: "list_all2 (\<lambda>\<psi> rl. table (Formula.fv_list \<psi>) rl \<and> finite rl) \<psi>s as"
      using las lcs dsse mas by (fastforce simp: list_all2_conv_all_nth)
    show ?thesis using etabc_gupdate_matchF[OF wfr ru] unfolding dsse by (simp add: msk)
  qed
  obtain daux2 ebuf2 where dt:
    "mbufnt_take ?G daux (map Rep_mbuf_t (mebufn_add (map fst ?dR) dbuf)) t (nts @ ts)
      = (daux2, ebuf2, nt2, nts2)"
    and rw: "emld_rel ks cs \<psi>s css aux2 daux2" and bf2: "ebufn dss css buf2 ebuf2"
    using ebufn_nt_take[where R = "emld_rel ks cs \<psi>s css" and f = "?F" and g = "?G",
        OF badd step rel g0] by blast
  obtain ub un where dte: "mebufnt_take ?G daux (mebufn_add (map fst ?dR) dbuf) t (dnts @@ ts)
      = (daux2, ub, nt2, un)" and ub: "map Rep_mbuf_t ub = ebuf2" and un: "Rep_mbuf_t un = nts2"
    by (rule mebufnt_take_obtain[OF dt[unfolded ne[symmetric]]])
  obtain dzs daux3 where g2: "geval_matchF I mr nt2 daux2 = (dzs, daux3)"
    by (cases "geval_matchF I mr nt2 daux2") auto
  have evb: "fst (geval_matchF I mr nt2 daux2) = map (etabc ks cs) (fst (eval_matchF I mr nt2 aux2))
      \<and> emld_rel ks cs \<psi>s css (snd (eval_matchF I mr nt2 aux2)) (snd (geval_matchF I mr nt2 daux2))"
    by (rule etabc_geval_matchF[OF rw])
  have ev: "dzs = map (etabc ks cs) zs" using evb g1 g2 by simp
  have rel3: "emld_rel ks cs \<psi>s css aux3 daux3" using evb g1 g2 by simp
  show ?case
  proof (intro exI conjI)
    show "eeval j ts db (EMatchF (length cs) I mr mrs pls Ld dbuf dnts t daux)
        = (map (etabc ks cs) xs,
           EMatchF (length cs) I mr mrs pls (map snd ?dR) ub un nt2 daux3)"
      using dte g2 x ev by (simp add: Let_def del: mebufnt_take.simps)
    show "esim n ks cs (enext tw ts)
        (EMatchF (length cs) I mr mrs pls (map snd ?dR) ub un nt2 daux3) \<phi>'"
      unfolding fe
      by (rule esim.EsMatchF[OF wf sr okm fvA dm
            mrsd dsse lcs _ _ fas csub _ pe _ un rel3])
        (use lL lLd dl2 dl0 bf2 ub in auto)
  qed
qed

text \<open>Induction on the bound discharges the assumption the theorem above carries, and
  instantiating it at the formula's own size recovers the statement without it.\<close>

lemma esim_deval_bound:
  "size \<phi> \<le> NN \<Longrightarrow> esim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> kgood n ks j ts db \<phi> \<Longrightarrow>
   \<exists>\<phi>d'. eeval j ts db \<phi>d = (map (etabc ks cs) xs, \<phi>d')
     \<and> esim n ks cs (enext tw ts) \<phi>d' \<phi>'"
proof (induct NN arbitrary: n ks cs tw \<phi>d \<phi> j ts db xs \<phi>' rule: less_induct)
  case (less NN)
  show ?case
    by (rule esim_deval_N[OF _ less(3) less(4) less(5) less(2) less(6)])
      (use less(1) in blast)
qed

theorem esim_deval:
  "esim n ks cs tw \<phi>d \<phi> \<Longrightarrow>
   (\<forall>t \<in> set ts. tw \<le> t) \<Longrightarrow> meval j n ts db \<phi> = (xs, \<phi>') \<Longrightarrow> kgood n ks j ts db \<phi> \<Longrightarrow>
   \<exists>\<phi>d'. eeval j ts db \<phi>d = (map (etabc ks cs) xs, \<phi>d')
     \<and> esim n ks cs (enext tw ts) \<phi>d' \<phi>'"
  by (rule esim_deval_bound[OF order.refl])

(*<*)
end
(*>*)