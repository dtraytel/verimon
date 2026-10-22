(*<*)
theory Eval
  imports Window_Dispatch Release_Window Trigger_Window
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

datatype ('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula =
    EFail
  | ERel "event_data table"
  | EPredS Formula.name nat
  | EPredM Formula.name nat "Formula.trm list" cols
  | EAndRel "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | ENeg "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula"
  | EExists "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" bool
  | EAgg bool "ty Formula.agg_op" Formula.trm nat nat "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula"
  | EOr "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" 'b2
  | EAnd ejoin_plan "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" bool "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" 'b2
  | EPrev \<I> "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" bool "event_data table mbuf_t" "ts mbuf_t"
  | ENext \<I> "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" bool "ts mbuf_t"
  | EAnds "ejoin_plan list" "ejoin_plan list" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula list" 'bn
  | ESince args "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" uebuf2S 'bs
  | EUntil args "bool list" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" uebuf2 "ts mbuf_t" ts 'bu
  | EAndAssign nat Formula.trm "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula"
  | ETP mtrm nat
  | ETS mtrm
  | ELet Formula.name nat "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula"
  | EFrz Formula.name nat "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" nat nat nat "event_data table list"
      "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" nat nat "ts list" "event_data table list" enat bool bool "nat option" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula"
      "(event_data list set, event_data table) frz_sep" "nat list" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula"
  | ELetPast Formula.name nat "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" nat "event_data table option"
  | ETrigger args "nat option list" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" uebuf2 "ts mbuf_t" "event_data twaux"
  | ERelease args "bool list" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" uebuf2 "ts mbuf_t" ts "event_data eraux"
  | EAndTrigger ejoin_plan "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" 'ba
      args "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula" uebuf2 "ts mbuf_t" "event_data twaux"
  | EMatchP nat \<I> mregex "mregex list" "nat option list list" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula list"
      uebufn "ts mbuf_t" "event_data mr\<delta>aux"
  | EMatchF nat \<I> mregex "mregex list" "nat option list list" "('b2, 'bn, 'ba, 'bs, 'bu, 'p) geformula list"
      uebufn "ts mbuf_t" ts "event_data ml\<delta>aux"
  | EPlain 'p

text \<open>The executable formula over plain tables.  The buffers of the unions and the joins, whose
  tables a consumer may want with indices, have the types @{typ 'b2}, @{typ 'bn} and @{typ 'ba};
  as type variables they do not count towards the size of a formula, which the evaluation of
  @{text "LET PAST"} compares before and after a step.\<close>

type_synonym eformula = "(uebuf2, uebufn, event_data table mbuf_t \<times> event_data table option mbuf_t, udsaux_x, uduaux_x, unit) geformula"

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
| "efail_nodes (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) =
    efail_nodes \<phi> + efail_nodes \<psi> + efail_nodes \<rho>"
| "efail_nodes (ELetPast p m \<phi> \<psi> i buf) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (ETrigger dags pl \<phi> \<psi> dbuf nts daux) = efail_nodes \<phi> + efail_nodes \<psi>"
| "efail_nodes (ERelease dags msk \<phi> \<psi> dbuf nts t daux) = efail_nodes \<phi> + efail_nodes \<psi>"
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
| "eeval j ts db (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) =
     (let (xs, \<phi>) = eeval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = eeval j ts db0 \<psi>;
          (rs, \<rho>) = eeval j ts db0 \<rho>;
          (zs0_out, jfrz, fl, \<alpha>s, lr, fd) =
            (let zs0_out = drop (jfrz - jpsi0) zs0;
                 \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
             in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
               case lv of None \<Rightarrow> None | Some g \<Rightarrow>
                 if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
                 then Some (g, eeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
                 else None,
               case sx of FSSep L _ _ _ _ _ _ _ \<Rightarrow>
                 Some (eeval j ts (Mapping.update (p, m) (replicate (length ts) L) db) \<rho>S,
                   eeval j ts (Mapping.update (p, m) (replicate (length ts) {}) db) \<rho>E)
               | _ \<Rightarrow> None));
          (ys, \<alpha>s', lv, (\<rho>, w, pR, tq, rb), sx, \<rho>S, \<rho>E) = frz_step size (eeval j) (frz_kops m cS) (p, m)
            (Mapping.map_values (\<lambda>_ _. []) db) fl d po j jfrz \<alpha>s xs lr fd sx \<rho>S \<rho>E
            (\<rho>, w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
              drop (min jfrz (pR + length rs) - (pR - length rb)) (rb @ rs))
      in (zs0_out @ ys, EFrz p m \<phi> \<psi> (jfrz + length ys) (jpsi0 + length zs0) (jphi + length xs) \<alpha>s' \<rho> w pR tq rb d po ng
        (frz_keep_lv (if po then None else lv) \<rho>L) (frz_keep_st (if po then None else lv) \<rho>L) sx cS \<rho>S \<rho>E))"
| "eeval j ts db (ELetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            letpast_meval0 (eeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
          (ys, \<psi>) = eeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, ELetPast p m \<phi> \<psi> i buf))"
| "eeval j ts db (ETrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = eeval j ts db \<phi>; (ys, \<psi>') = eeval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = tw_update dags t r1 r2 ax
            in (zs @ [tw_result ax], ax)) ([], daux)
            (mebuf2_add xs ys dbuf) (nts @@ ts)
      in (zs, ETrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "eeval j ts db (EAndTrigger pl \<alpha> dbuf1 dags \<phi> \<psi> ebuf2 nts daux) =
     (let (as, \<alpha>') = eeval j ts db \<alpha>; (xs, \<phi>') = eeval j ts db \<phi>;
          (ys, \<psi>') = eeval j ts db \<psi>;
          ((ws, daux'), dbuf2', nts') = mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = tw_update dags t r1 r2 ax
            in (ws @ [if tw_empty ax then None
                      else Some (tw_result ax)], ax)) ([], daux)
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
| "eeval j ts db (ERelease dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = eeval j ts db \<phi>; (ys, \<psi>') = eeval j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (eraux_update dags msk) aux
            (mebuf2_add xs ys buf) t (nts @@ ts);
          (zs, aux'') = eraux_eval (args_ivl dags) nt aux'
      in (zs, ERelease dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "eeval j ts db (EPlain x) = ([], EPlain x)"
  by pat_completeness (simp_all only: prod.inject geformula.inject geformula.distinct simp_thms)

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
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E) \<comment> \<open>\<^const>\<open>EFrz\<close>\<close>
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
  obtain zo jf fl as lr fd where st: "(let zs0_out = drop (jfrz - jpsi0) zs0;
       \<alpha>s1 = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs)
     in (zs0_out, jfrz + length zs0_out, frz_fill ng (\<alpha>s @ xs), \<alpha>s1,
       case lv of None \<Rightarrow> None | Some g \<Rightarrow>
         if zs0_out = [] \<and> \<alpha>s1 \<noteq> []
         then Some (g, eeval j ts (Mapping.update (p, m) (replicate (length ts) (hd \<alpha>s1)) db) \<rho>L)
         else None,
       case sx of FSSep L _ _ _ _ _ _ _ \<Rightarrow>
         Some (eeval j ts (Mapping.update (p, m) (replicate (length ts) L) db) \<rho>S,
           eeval j ts (Mapping.update (p, m) (replicate (length ts) {}) db) \<rho>E)
       | _ \<Rightarrow> None)) = (zo, jf, fl, as, lr, fd)"
    by (metis prod_cases6)
  obtain ys as' lv' s' sx' \<rho>S' \<rho>E' where lp0: "frz_step size (eeval j) (frz_kops m cS) (p, m)
      (Mapping.map_values (\<lambda>_ _. []) db) fl d po j jf as xs lr fd sx \<rho>S \<rho>E
      (\<rho>', w, pR + length rs, if d = \<infinity> then [] else tq @ ts,
        drop (min jf (pR + length rs) - (pR - length rb)) (rb @ rs)) = (ys, as', lv', s', sx', \<rho>S', \<rho>E')"
    by (metis prod_cases7)
  obtain \<rho>'' w' pR' tq' rb' where s': "s' = (\<rho>'', w', pR', tq', rb')"
    by (metis prod_cases5)
  have s\<rho>'': "size \<rho>'' = size \<rho>" and sS: "size \<rho>S' = size \<rho>S" and sE: "size \<rho>E' = size \<rho>E"
    using frz_step_size[OF lp0] s\<rho> s' by simp_all
  have "snd (eeval j ts db (EFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)) =
    EFrz p m \<phi>' \<psi>' (jf + length ys) (jpsi0 + length zs0) (jphi + length xs) as' \<rho>'' w' pR' tq' rb' d po ng
      (frz_keep_lv (if po then None else lv') \<rho>L) (frz_keep_st (if po then None else lv') \<rho>L) sx' cS \<rho>S' \<rho>E'"
    by (simp only: eeval.psimps(20)[OF 20(1)] \<phi>' \<psi>' \<rho>' st lp0[unfolded s'] Let_def[where s = ?db0]
        Let_def[where s = "(xs, \<phi>')"] Let_def[where s = "(zs0, \<psi>')"] Let_def[where s = "(rs, \<rho>')"]
        Let_def[where s = "(zo, jf, fl, as, lr, fd)"]
        Let_def[where s = "(ys, as', lv', (\<rho>'', w', pR', tq', rb'), sx', \<rho>S', \<rho>E')"]
        prod.case snd_conv)
  then show ?case
    using s\<phi> s\<psi> s\<rho>'' sS sE by simp
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
    geformula.size list.map map_map o_apply size_list_map size_frz_keep_st cong: size_list_cong
    split: prod.splits)

lemma total_eeval: "All eeval_dom"
proof (relation "measure (\<lambda>(j, ts, db, \<phi>). size \<phi>)", goal_cases)
  text \<open>The live copy and the replays of @{const EFrz}, as for @{const meval}.\<close>
  case 23 \<comment> \<open>the live copy, a subterm\<close>
  then show ?case
    by simp
next
  case 24 \<comment> \<open>the copy of the separable mode with the frozen table, a subterm\<close>
  then show ?case
    by simp
next
  case 25 \<comment> \<open>the copy of the separable mode with the empty table, a subterm\<close>
  then show ?case
    by simp
next
  case (26 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E x xa y xb xc xd ya xe
    xf yb xg xh yc xi yd xj yca xk ycb xl ycc tsa dba \<psi>')
  have "size yb = size \<rho>"
    using psize_snd_eeval[of j ts xb \<rho>] 26 by (metis snd_conv)
  then show ?case
    using 26 by simp
qed (auto simp: termination_simp dest!: psize_snd_eeval dest: sym)

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

text \<open>The window a firing reports is a union of the auxiliary list's tables, so it is a table over
  the node's columns; the kernel's structure reports its aggregation and the executable one reports its
  reordering -- or, for the window with the aggregate fused in, the executable aggregation of its
  reordering.  The relation below carries that post-function; @{const esres} is its identity
  instance.\<close>

definition esresh :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> (event_data table \<Rightarrow> event_data table) \<Rightarrow>
    event_data table list \<Rightarrow> event_data table list \<Rightarrow> bool"
  where "esresh ks cs args h zs dzs \<longleftrightarrow> (\<exists>ws. list_all (table ks) ws \<and>
     zs = map (eval_args_agg args) ws \<and> dzs = map (h \<circ> etabc ks cs) ws)"

lemma esresh_Nil[simp]: "esresh ks cs args h [] []"
  unfolding esresh_def by (intro exI[of _ "[]"]) simp

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

subsection \<open>The Trigger structure at the ascending frame, and its buffer\<close>

text \<open>
  The trigger node carries the pair of structures, related through the abstract auxiliary list
  they are both valid for, together with the two buffers and the pending timestamps.  Unlike the
  Since and the Until, the structure is stepped and read in the same traversal, so the output
  list is part of what the step relates.  Each operand's tables enter the buffer at their own
  columns.
\<close>

definition etrigger_rel :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow>
    event_data mmtaux \<Rightarrow> event_data twaux \<Rightarrow> event_data mbuf2 \<Rightarrow>
    event_data mbuf2 \<Rightarrow> ts list \<Rightarrow> bool" where
  "etrigger_rel kR cR kL cL args tw aux daux buf dbuf nts \<longleftrightarrow>
     (\<exists>cur auxlist. valid_mmtaux args cur aux auxlist \<and>
        (\<forall>(t, l, r) \<in> set auxlist. ftable kL l \<and> ftable kR r) \<and>
        etw kL cL kR cR args cur daux auxlist \<and> cur \<le> tw \<and>
        list_all (ftable kL) (fst buf) \<and>
        list_all (ftable kR) (snd buf) \<and>
        sorted nts \<and> (\<forall>v \<in> set nts. cur \<le> v \<and> v \<le> tw) \<and>
        dbuf = (map (etabc kL cL) (fst buf), map (etabc kR cR) (snd buf)))"

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

text \<open>The node's outer buffer: the left operand's tables at the node's own columns, and the
  trigger's reads as options.\<close>

definition eandbuf :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> event_data mbuft2 \<Rightarrow>
    (event_data table list \<times> event_data table option list) \<Rightarrow> bool" where
  "eandbuf ks cs kR cR buf dbuf \<longleftrightarrow>
     list_all (ftable ks) (fst buf) \<and>
     fst dbuf = map (etabc ks cs) (fst buf) \<and>
     list_all2 (etres kR cR) (snd buf) (snd dbuf)"

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
    size \<rho>S = size \<rho> \<Longrightarrow> size \<rho>Sd = size \<rho>d \<Longrightarrow> size \<rho>E = size \<rho> \<Longrightarrow> size \<rho>Ed = size \<rho>d \<Longrightarrow>
    (\<forall>L nL pX buf rg bo tk Lr. sx = FSSep L nL pX buf rg bo tk Lr \<longrightarrow>
      esim n ks cs tw \<rho>Sd \<rho>S \<and> esim n ks cs tw \<rho>Ed \<rho>E) \<Longrightarrow> cS = ks \<Longrightarrow>
    esim n ks cs tw (EFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi \<alpha>s \<rho>d w pR tq (map (etabc ks cs) rb) d po ng lv \<rho>Ld
        (map_frz_sep id (etabc ks cs) sx) cs \<rho>Sd \<rho>Ed)
      (mformula.MFrz p m kks \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s \<rho> w pR tq rb d po ng lv \<rho>L sx cS \<rho>S \<rho>E)"
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
| EsRelease: "eframe kR cR \<Longrightarrow>
    esim n kL cL tw \<phi>d \<phi> \<Longrightarrow> esim n kR cR tw \<psi>d \<psi> \<Longrightarrow>
    set kL \<subseteq> set kR \<Longrightarrow> args_L args = kL \<Longrightarrow> args_R args = kR \<Longrightarrow>
    dags = eargs cR cL args \<Longrightarrow> msk = emsk cR cL \<Longrightarrow>
    ebuf2 kL cL kR cR buf (rbuf2 dbuf) \<Longrightarrow> Rep_mbuf_t dnts = nts \<Longrightarrow>
    erelease_rel kR cR (args_ivl args) tw t aux daux nts \<Longrightarrow>
    esim n kR cR tw (ERelease dags msk \<phi>d \<psi>d dbuf dnts t daux)
      (mformula.MRelease args \<phi> \<psi> buf nts t aux)"
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

end
(*>*)
