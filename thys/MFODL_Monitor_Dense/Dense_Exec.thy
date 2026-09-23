(*<*)
theory Dense_Exec
  imports Dense_Descend
begin
(*>*)

section \<open>The verified dense evaluator over queue buffers\<close>

text \<open>
  @{const deval} buffers the tables of a node's operands in lists, as the kernel's @{const meval}
  does: a batch is appended with @{term "(@)"}, one step of the traversal takes the head.  That
  is the specification's shape, and it is quadratic in the number of tables a buffer holds --
  which is the number of time points by which one operand runs ahead of the other, and on a log
  with thousands of time points per timestamp an @{text EVENTUALLY} under a conjunction holds
  thousands of them.  The kernel's executable layer (@{theory MFODL_Monitor_Devel.Monitor_Impl})
  keeps the same buffers in @{typ "'a mbuf_t"}, a copy of the list type whose code
  representation is a queue, and proves its evaluator to be @{const meval} up to the
  representation.  This theory does the same for the dense evaluator: @{text edformula} is
  @{typ dformula} with its buffers in @{typ "'a mbuf_t"}, @{text edeval} is @{const deval}
  with the queue operations put in, and the lemma @{text edeval_Rep} at the end says the two
  agree.  Nothing else changes: the simulation of @{theory MFODL_Monitor_Dense.Dense_Eval} is
  about @{const deval}, and @{const deval} on a represented formula is, by that theorem, what
  the generated code runs.
\<close>
datatype edformula =
    EDFail
  | EDRel "event_data table"
  | EDPredS Formula.name nat
  | EDPredM Formula.name nat "Formula.trm list" cols
  | EDAndRel edformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | EDNeg edformula
  | EDExists edformula bool
  | EDAgg bool "ty Formula.agg_op" Formula.trm nat nat edformula
  | EDOr edformula edformula "event_data mebuf2"
  | EDAnd djoin_plan edformula bool edformula "event_data mebuf2"
  | EDPrev \<I> edformula bool "event_data table mbuf_t" "ts mbuf_t"
  | EDNext \<I> edformula bool "ts mbuf_t"
  | EDAnds "djoin_plan list" "djoin_plan list" "edformula list" "event_data mebufn"
  | EDSince args edformula edformula "event_data mebuf2S" dsaux_x
  | EDUntil args "bool list" edformula edformula "event_data mebuf2" "ts mbuf_t" ts duaux_x
  | EDAndAssign nat Formula.trm edformula
  | EDTP mtrm nat
  | EDTS mtrm
  | EDLet Formula.name nat edformula edformula
  | EDFrz Formula.name nat edformula edformula nat nat nat "event_data table list"
  | EDLetPast Formula.name nat edformula edformula nat "event_data table option"
  | EDTrigger args "nat option list" edformula edformula "event_data mebuf2" "ts mbuf_t"
      "event_data option gmmtaux"
  | EDAndTrigger djoin_plan edformula
      "event_data table mbuf_t \<times> event_data table option mbuf_t" args edformula edformula
      "event_data mebuf2" "ts mbuf_t" "event_data option gmmtaux"
  | EDMatchP nat \<I> mregex "mregex list" "nat option list list" "edformula list"
      "event_data mebufn" "ts mbuf_t" "event_data mr\<delta>aux"
  | EDMatchF nat \<I> mregex "mregex list" "nat option list list" "edformula list"
      "event_data mebufn" "ts mbuf_t" ts "event_data ml\<delta>aux"

fun Rep_edformula :: "edformula \<Rightarrow> dformula" where
  "Rep_edformula EDFail = DFail"
| "Rep_edformula (EDRel rel) = DRel rel"
| "Rep_edformula (EDPredS e ar) = DPredS e ar"
| "Rep_edformula (EDPredM e ar tms cs) = DPredM e ar tms cs"
| "Rep_edformula (EDAndRel \<phi> conf) = DAndRel (Rep_edformula \<phi>) conf"
| "Rep_edformula (EDNeg \<phi>) = DNeg (Rep_edformula \<phi>)"
| "Rep_edformula (EDExists \<phi> b) = DExists (Rep_edformula \<phi>) b"
| "Rep_edformula (EDAgg g0 \<omega> f k pos \<phi>) = DAgg g0 \<omega> f k pos (Rep_edformula \<phi>)"
| "Rep_edformula (EDOr \<phi> \<psi> buf) =
     DOr (Rep_edformula \<phi>) (Rep_edformula \<psi>) (map_prod Rep_mbuf_t Rep_mbuf_t buf)"
| "Rep_edformula (EDAnd pl \<phi> pos \<psi> buf) =
     DAnd pl (Rep_edformula \<phi>) pos (Rep_edformula \<psi>) (map_prod Rep_mbuf_t Rep_mbuf_t buf)"
| "Rep_edformula (EDPrev I \<phi> first buf nts) =
     DPrev I (Rep_edformula \<phi>) first (Rep_mbuf_t buf) (Rep_mbuf_t nts)"
| "Rep_edformula (EDNext I \<phi> first nts) = DNext I (Rep_edformula \<phi>) first (Rep_mbuf_t nts)"
| "Rep_edformula (EDAnds ps ns L buf) =
     DAnds ps ns (map Rep_edformula L) (map Rep_mbuf_t buf)"
| "Rep_edformula (EDSince args \<phi> \<psi> buf aux) =
     DSince args (Rep_edformula \<phi>) (Rep_edformula \<psi>)
       (case buf of (a, b, c, d) \<Rightarrow> (Rep_mbuf_t a, Rep_mbuf_t b, Rep_mbuf_t c, d)) aux"
| "Rep_edformula (EDUntil args msk \<phi> \<psi> buf nts t aux) =
     DUntil args msk (Rep_edformula \<phi>) (Rep_edformula \<psi>) (map_prod Rep_mbuf_t Rep_mbuf_t buf)
       (Rep_mbuf_t nts) t aux"
| "Rep_edformula (EDAndAssign p t \<phi>) = DAndAssign p t (Rep_edformula \<phi>)"
| "Rep_edformula (EDTP mt i) = DTP mt i"
| "Rep_edformula (EDTS mt) = DTS mt"
| "Rep_edformula (EDLet p m \<phi> \<psi>) = DLet p m (Rep_edformula \<phi>) (Rep_edformula \<psi>)"
| "Rep_edformula (EDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) =
     DFrz p m (Rep_edformula \<phi>) (Rep_edformula \<psi>) jfrz jpsi0 jphi \<alpha>s"
| "Rep_edformula (EDLetPast p m \<phi> \<psi> i buf) =
     DLetPast p m (Rep_edformula \<phi>) (Rep_edformula \<psi>) i buf"
| "Rep_edformula (EDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     DTrigger dags pl (Rep_edformula \<phi>) (Rep_edformula \<psi>) (map_prod Rep_mbuf_t Rep_mbuf_t dbuf)
       (Rep_mbuf_t nts) daux"
| "Rep_edformula (EDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     DAndTrigger pl (Rep_edformula \<alpha>) (map_prod Rep_mbuf_t Rep_mbuf_t dbf1) dags
       (Rep_edformula \<phi>) (Rep_edformula \<psi>) (map_prod Rep_mbuf_t Rep_mbuf_t dbf2)
       (Rep_mbuf_t nts) daux"
| "Rep_edformula (EDMatchP m I mr mrs pls Ld dbuf nts daux) =
     DMatchP m I mr mrs pls (map Rep_edformula Ld) (map Rep_mbuf_t dbuf) (Rep_mbuf_t nts) daux"
| "Rep_edformula (EDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     DMatchF m I mr mrs pls (map Rep_edformula Ld) (map Rep_mbuf_t dbuf) (Rep_mbuf_t nts) t daux"

lemma size_Rep_edformula[simp]: "size (Rep_edformula \<phi>) = size \<phi>"
  by (induct \<phi>) (auto simp: comp_def size_list_map cong: size_list_cong)

fun evdfail_nodes :: "edformula \<Rightarrow> nat" where
  "evdfail_nodes EDFail = 1"
| "evdfail_nodes (EDAndRel \<phi> conf) = evdfail_nodes \<phi>"
| "evdfail_nodes (EDNeg \<phi>) = evdfail_nodes \<phi>"
| "evdfail_nodes (EDExists \<phi> b) = evdfail_nodes \<phi>"
| "evdfail_nodes (EDAgg g0 \<omega> f k pos \<phi>) = evdfail_nodes \<phi>"
| "evdfail_nodes (EDOr \<phi> \<psi> buf) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDAnd pl \<phi> pos \<psi> buf) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDPrev I \<phi> f buf nts) = evdfail_nodes \<phi>"
| "evdfail_nodes (EDNext I \<phi> f nts) = evdfail_nodes \<phi>"
| "evdfail_nodes (EDAnds ps ns L buf) = sum_list (map evdfail_nodes L)"
| "evdfail_nodes (EDSince args \<phi> \<psi> buf aux) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDUntil args msk \<phi> \<psi> buf nts t aux) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDAndAssign p t \<phi>) = evdfail_nodes \<phi>"
| "evdfail_nodes (EDLet p m \<phi> \<psi>) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDLetPast p m \<phi> \<psi> i buf) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDTrigger dags pl \<phi> \<psi> dbuf nts daux) = evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     evdfail_nodes \<alpha> + evdfail_nodes \<phi> + evdfail_nodes \<psi>"
| "evdfail_nodes (EDMatchP m I mr mrs pls L dbuf nts daux) = sum_list (map evdfail_nodes L)"
| "evdfail_nodes (EDMatchF m I mr mrs pls L dbuf nts t daux) = sum_list (map evdfail_nodes L)"
| "evdfail_nodes \<phi> = 0"

lemma vdfail_nodes_Rep: "vdfail_nodes (Rep_edformula \<phi>) = evdfail_nodes \<phi>"
  by (induct \<phi>) (auto simp: comp_def intro: arg_cong[of _ _ sum_list])

subsection \<open>The Since buffer\<close>

text \<open>The kernel's @{text eeval_since} with the dispatching operations put in.\<close>

fun edsx_eval_since :: "args \<Rightarrow> event_data table list \<Rightarrow> event_data mebuf2S \<Rightarrow> dsaux_x \<Rightarrow>
    event_data table list \<times> event_data mebuf2S \<times> dsaux_x" where
  "edsx_eval_since args rs (xs, ys, ts, skew) aux =
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow>
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          (if skew \<or> memL (args_ivl args) 0
           then (rev rs, (x ## xs', mbuf_t_empty, t ## ts', skew), aux)
           else (let aux' = dsx_join args x (dsx_add_new_ts args t aux)
             in (rev (dsx_result args aux' # rs), (xs', mbuf_t_empty, ts', True), aux')))
        | (None, ts') \<Rightarrow> (rev rs, (x ## xs', mbuf_t_empty, mbuf_t_empty, skew), aux))
      | (None, xs') \<Rightarrow> (rev rs, (mbuf_t_empty, mbuf_t_empty, ts, skew), aux))
    | (Some y, ys') \<Rightarrow>
      if skew then edsx_eval_since args rs (xs, ys', ts, False) (dsx_add_new_table args y aux)
      else
      (case mbuf_t_cases xs of (Some x1, xs1) \<Rightarrow>
        (case mbuf_t_cases ts of (Some t1, ts1) \<Rightarrow>
          (let aux1 = dsx_add_new_table args y (dsx_join args x1 (dsx_add_new_ts args t1 aux))
           in edsx_eval_since args (dsx_result args aux1 # rs) (xs1, ys', ts1, False) aux1)
        | (None, ts1) \<Rightarrow> (rev rs, (x1 ## xs1, y ## ys', ts1, skew), aux))
      | (None, xs1) \<Rightarrow> (rev rs, (mbuf_t_empty, y ## ys', ts, skew), aux)))"

lemma edsx_eval_since:
  "edsx_eval_since args rs (xs, ys, ts, skew) aux = (res, (xs', ys', ts', skew'), aux') \<Longrightarrow>
   dsx_eval_since args rs (Rep_mbuf_t xs, Rep_mbuf_t ys, Rep_mbuf_t ts, skew) aux
   = (res, (Rep_mbuf_t xs', Rep_mbuf_t ys', Rep_mbuf_t ts', skew'), aux')"
proof (induction args rs "(xs, ys, ts, skew)" aux arbitrary: xs ys ts skew res xs' ys' ts' skew' aux'
    rule: edsx_eval_since.induct)
  case (1 args rs xs ys ts skew aux)
  note IH1 = 1(1) and IH2 = 1(2) and E = 1(3)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')" by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')" by fastforce
  obtain t ts'' where ts_def: "mbuf_t_cases ts = (t, ts'')" by fastforce
  show ?case
  proof (cases "y = None \<or> \<not> skew")
    case True
    then show ?thesis using IH2 E xs_def ys_def ts_def
      by (cases x; cases y; cases t)
        (auto simp: mbuf_t_empty.rep_eq mbuf_t_Cons.rep_eq Let_def split: if_splits)
  next
    case False
    then obtain y2 where y: "y = Some y2" and sk: skew by (cases y) auto
    have D: "edsx_eval_since args rs (xs, ys'', ts, False) (dsx_add_new_table args y2 aux)
        = (res, (xs', ys', ts', skew'), aux')"
      using E by (subst (asm) edsx_eval_since.simps) (simp add: ys_def y sk)
    have "dsx_eval_since args rs (Rep_mbuf_t xs, Rep_mbuf_t ys'', Rep_mbuf_t ts, False)
        (dsx_add_new_table args y2 aux)
        = (res, (Rep_mbuf_t xs', Rep_mbuf_t ys', Rep_mbuf_t ts', skew'), aux')"
      by (rule IH1[OF ys_def[symmetric] y sk D])
    then show ?thesis using ys_def[unfolded y] sk by simp
  qed
qed

subsection \<open>The evaluator\<close>

function (sequential) edeval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> edformula \<Rightarrow>
    event_data table list \<times> edformula" where
  "edeval j ts db EDFail = ([], EDFail)"
| "edeval j ts db (EDRel rel) = (replicate (length ts) rel, EDRel rel)"
| "edeval j ts db (EDPredS e ar) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) empty_table
       | Some xs \<Rightarrow> xs), EDPredS e ar)"
| "edeval j ts db (EDPredM e ar tms cs) =
     ((case Mapping.lookup db (e, ar) of
         None \<Rightarrow> replicate (length ts) empty_table
       | Some xs \<Rightarrow> map (dmatch_table tms cs) xs), EDPredM e ar tms cs)"
| "edeval j ts db (EDAndRel \<phi> conf) =
     (let (xs, \<phi>') = edeval j ts db \<phi>
      in (map (Set.filter (deval_constraint conf)) xs, EDAndRel \<phi>' conf))"
| "edeval j ts db (EDNeg \<phi>) =
     (let (xs, \<phi>') = edeval j ts db \<phi>
      in (map (\<lambda>r. if r = empty_table then unit_table 0 else empty_table) xs, EDNeg \<phi>'))"
| "edeval j ts db (EDExists \<phi> drop0) =
     (let (xs, \<phi>') = edeval j ts db \<phi>
      in (if drop0 then map (\<lambda>r. tl ` r) xs else xs, EDExists \<phi>' drop0))"
| "edeval j ts db (EDAgg g0 \<omega> f k pos \<phi>) =
     (let (xs, \<phi>') = edeval j ts db \<phi> in (map (dagg g0 \<omega> f k pos) xs, EDAgg g0 \<omega> f k pos \<phi>'))"
| "edeval j ts db (EDOr \<phi> \<psi> buf) =
     (let (xs, \<phi>') = edeval j ts db \<phi>; (ys, \<psi>') = edeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
      in (zs, EDOr \<phi>' \<psi>' buf'))"
| "edeval j ts db (EDAnd pl \<phi> pos \<psi> buf) =
     (let (xs, \<phi>') = edeval j ts db \<phi>; (ys, \<psi>') = edeval j ts db \<psi>;
          (zs, buf') = mebuf2_take (\<lambda>r1 r2. dbin_join pl r1 pos r2) (mebuf2_add xs ys buf)
      in (zs, EDAnd pl \<phi>' pos \<psi>' buf'))"
| "edeval j ts db (EDPrev I \<phi> first buf nts) =
     (let (xs, \<phi>') = edeval j ts db \<phi>
      in if first \<and> ts = [] then ([], EDPrev I \<phi>' True (buf @@ xs) (nts @@ ts))
      else let (zs, buf', nts') = meprev_next I (buf @@ xs) (nts @@ ts)
        in (if first then empty_table # zs else zs, EDPrev I \<phi>' False buf' nts'))"
| "edeval j ts db (EDNext I \<phi> first nts) =
     (let (xs, \<phi>') = edeval j ts db \<phi>;
          (xs, first') = (case (xs, first) of (_ # xs', True) \<Rightarrow> (xs', False) | a \<Rightarrow> a);
          (zs, _, nts') = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
      in (zs, EDNext I \<phi>' first' nts'))"
| "edeval j ts db (EDAnds ps ns Ld dbuf) =
     (let R = map (edeval j ts db) Ld;
          (zs, dbuf') = mebufn_take (\<lambda>as zs. zs @@ [dmulti_join ps ns as]) mbuf_t_empty
            (mebufn_add (map fst R) dbuf)
      in (Rep_mbuf_t zs, EDAnds ps ns (map snd R) dbuf'))"
| "edeval j ts db (EDSince dags \<phi> \<psi> buf aux) =
     (let (xs, \<phi>') = edeval j ts db \<phi>; (ys, \<psi>') = edeval j ts db \<psi>;
          (zs, buf', aux') = edsx_eval_since dags [] (mebuf2S_add xs ys ts buf) aux
      in (zs, EDSince dags \<phi>' \<psi>' buf' aux'))"
| "edeval j ts db (EDUntil dags msk \<phi> \<psi> buf nts t aux) =
     (let (xs, \<phi>') = edeval j ts db \<phi>; (ys, \<psi>') = edeval j ts db \<psi>;
          (aux', buf', nt, nts') = mebuf2t_take (dux_add_new dags msk) aux
            (mebuf2_add xs ys buf) t (nts @@ ts);
          (zs, aux'') = dux_eval dags nt aux'
      in (zs, EDUntil dags msk \<phi>' \<psi>' buf' nts' nt aux''))"
| "edeval j ts db (EDAndAssign p t \<phi>) =
     (let (xs, \<phi>') = edeval j ts db \<phi> in (map (dassign p t) xs, EDAndAssign p t \<phi>'))"
| "edeval j ts db (EDTP mt i) =
     (map (\<lambda>x. dmtrm mt (EInt (integer_of_nat x))) [i..<j], EDTP mt j)"
| "edeval j ts db (EDTS mt) = (map (\<lambda>x. dmtrm mt (EInt (integer_of_nat x))) ts, EDTS mt)"
| "edeval j ts db (EDLet p m \<phi> \<psi>) =
     (let (xs, \<phi>') = edeval j ts db \<phi>;
          (ys, \<psi>') = edeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, EDLet p m \<phi>' \<psi>'))"
| "edeval j ts db (EDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) =
     (let (xs, \<phi>) = edeval j ts db \<phi>;
          db0 = Mapping.update (p, m) [] db;
          (zs0, \<psi>) = edeval j ts db0 \<psi>;
          zs0_out = drop (jfrz - jpsi0) zs0;
          jpsi0 = jpsi0 + length zs0;
          \<alpha>s = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs);
          (ys, \<alpha>s') = freeze_meval0 (\<lambda>\<alpha>. edeval j []
            (Mapping.update (p, m) (replicate j \<alpha>)
              (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>) (jfrz - jpsi0) \<alpha>s;
          jphi = jphi + length xs;
          jfrz = jfrz + length zs0_out + length ys
      in (zs0_out @ ys, EDFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s'))"
| "edeval j ts db (EDLetPast p m \<phi> \<psi> i buf) =
     (let (xs, i, buf, \<phi>) =
            letpast_meval0 (edeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>;
          (ys, \<psi>) = edeval j ts (Mapping.update (p, m) xs db) \<psi>
      in (ys, EDLetPast p m \<phi> \<psi> i buf))"
| "edeval j ts db (EDTrigger dags pl \<phi> \<psi> dbuf nts daux) =
     (let (xs, \<phi>') = edeval j ts db \<phi>; (ys, \<psi>') = edeval j ts db \<psi>;
          ((zs, daux'), dbuf', nts') = mebuf2T_take (\<lambda>r1 r2 t (zs, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (zs @ [dsan (gresult_mmtaux dags ax)], ax)) ([], daux)
            (mebuf2_add xs ys dbuf) (nts @@ ts)
      in (zs, EDTrigger dags pl \<phi>' \<psi>' dbuf' nts' daux'))"
| "edeval j ts db (EDMatchP m I mr mrs pls Ld dbuf nts daux) =
     (let R = map (edeval j ts db) Ld;
          ((zs, daux'), dbuf', _, nts') = mebufnt_take (\<lambda>rels t (zs, ax).
             let (z, ax) = gupdate_matchP (map emb_msk pls) I mr mrs rels t ax
             in (zs @@ [z], ax)) (mbuf_t_empty, daux) (mebufn_add (map fst R) dbuf) 0 (nts @@ ts)
      in (map dsan (Rep_mbuf_t zs), EDMatchP m I mr mrs pls (map snd R) dbuf' nts' daux'))"
| "edeval j ts db (EDMatchF m I mr mrs pls Ld dbuf nts t daux) =
     (let R = map (edeval j ts db) Ld;
          (daux', dbuf', nt, nts') = mebufnt_take
             (\<lambda>rels. update_matchF m I mr mrs (map2 dembedp pls rels))
             daux (mebufn_add (map fst R) dbuf) t (nts @@ ts);
          (zs, daux'') = eval_matchF I mr nt daux'
      in (map dsan zs, EDMatchF m I mr mrs pls (map snd R) dbuf' nts' nt daux''))"
| "edeval j ts db (EDAndTrigger pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux) =
     (let (as, \<alpha>') = edeval j ts db \<alpha>; (xs, \<phi>') = edeval j ts db \<phi>;
          (ys, \<psi>') = edeval j ts db \<psi>;
          ((ws, daux'), dbf2', nts') = mebuf2T_take (\<lambda>r1 r2 t (ws, ax).
            let ax = gupdate_mmtaux dags t r1 r2 ax
            in (ws @ [if gmmtaux_empty ax then None
                      else Some (dsan (gresult_mmtaux dags ax))], ax)) ([], daux)
            (mebuf2_add xs ys dbf2) (nts @@ ts);
          (zs, dbf1') = mebuf2_take (\<lambda>r1 r2. case r2 of None \<Rightarrow> r1
            | Some z \<Rightarrow> dbin_join pl r1 True z) (mebuf2_add as ws dbf1)
      in (zs, EDAndTrigger pl \<alpha>' dbf1' dags \<phi>' \<psi>' dbf2' nts' daux'))"
  by pat_completeness auto

lemma psize_snd_edeval:
  "edeval_dom (j, ts, db, \<phi>) \<Longrightarrow> size (snd (edeval j ts db \<phi>)) = size \<phi>"
  apply (induct rule: edeval.pinduct)
  apply (auto simp only: prod.inject edeval.psimps Let_def snd_conv fst_conv
      edformula.size list.map map_map o_apply size_list_map cong: size_list_cong
      split: prod.splits)
   apply simp
  apply (metis snd_conv size_letpast_meval)
  done

lemma total_edeval: "All edeval_dom"
  by (relation "measure (\<lambda>(j, ts, db, \<phi>). size \<phi>)")
    (auto simp: termination_simp dest!: psize_snd_edeval dest: sym)

termination edeval by (rule total_edeval)

lemma size_snd_edeval[simp]: "size (snd (edeval j ts db \<phi>)) = size \<phi>"
  by (rule psize_snd_edeval[OF total_edeval[THEN spec]])

subsection \<open>The two evaluators agree\<close>

lemma edeval_Rep:
  "deval j ts db (Rep_edformula \<phi>) = (let (zs, \<phi>') = edeval j ts db \<phi> in (zs, Rep_edformula \<phi>'))"
proof (induction j ts db \<phi> rule: edeval.induct)
  case (13 j ts db ps ns L buf)
  have "map fst (map (edeval j ts db) L) = map fst (map (deval j ts db) (map Rep_edformula L))"
    "map snd (map (deval j ts db) (map Rep_edformula L))
      = map Rep_edformula (map snd (map (edeval j ts db) L))"
    by (auto dest: 13 split: prod.splits)
  then show ?case
    using 13
    by (auto simp only: Let_def deval.simps edeval.simps mbufn_add Rep_edformula.simps
        mbuf_t_empty.rep_eq split: prod.splits dest!: mebufn_take mbufn_take_app)
next
  case (20 j ts db p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s)
  obtain xs \<phi>' where \<phi>: "edeval j ts db \<phi> = (xs, \<phi>')"
    by (cases "edeval j ts db \<phi>")
  obtain zs0 \<psi>' where \<psi>: "edeval j ts (Mapping.update (p, m) [] db) \<psi> = (zs0, \<psi>')"
    by (cases "edeval j ts (Mapping.update (p, m) [] db) \<psi>")
  { fix \<alpha>
    have "\<exists>ys \<psi>''. edeval j []
     (Mapping.update (p, m) (replicate j \<alpha>) (Mapping.map_values (\<lambda>_ _. []) db))
     \<psi>' = (ys, \<psi>'')"
    by (cases "edeval j []
     (Mapping.update (p, m) (replicate j \<alpha>) (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>'") simp
  }
  from allI[OF this, of "\<lambda>x. x"] obtain ys \<psi>'' where \<psi>': "edeval j []
     (Mapping.update (p, m) (replicate j \<alpha>) (Mapping.map_values (\<lambda>_ _. []) db))
     \<psi>' = (ys \<alpha>, \<psi>'' \<alpha>)" for \<alpha>
    by atomize_elim (unfold choice_iff)
  show ?case
    using 20(1)[unfolded \<phi> Let_def prod.case] 20(2)[OF refl \<phi>[symmetric] refl, unfolded \<psi> Let_def prod.case]
      20(3)[OF \<phi>[symmetric] refl refl \<psi>[symmetric] refl refl refl refl, unfolded \<psi>' Let_def prod.case]
    by (auto simp: Let_def \<phi> \<psi> \<psi>' split_beta intro!: arg_cong[OF default_maux.freeze_meval0_cong_fst])
next
  case (21 j ts db p m \<phi> \<psi> i buf)
  have IH: "size \<psi> = size \<phi> \<Longrightarrow> deval j ts db (Rep_edformula \<psi>) =
    (case edeval j ts db \<psi> of (zs, \<psi>') \<Rightarrow> (zs, Rep_edformula \<psi>'))" for ts db \<psi>
    using 21 by auto
  show ?case
    using 21(2)[OF refl _ refl refl]
    by (cases "letpast_meval0 (edeval j) j i [] (list_of_option buf) (p, m) ts db \<phi>")
       (auto split: prod.splits
        dest!: letpast_meval0_cong_f[where ?eval="deval j" and ?eval'="edeval j" and \<phi>=\<phi>,
          OF IH size_Rep_edformula, simplified])
next
  case (23 j ts db m I mr mrs pls Ld dbuf nts daux)
  have "map fst (map (edeval j ts db) Ld) = map fst (map (deval j ts db) (map Rep_edformula Ld))"
    "map snd (map (deval j ts db) (map Rep_edformula Ld))
      = map Rep_edformula (map snd (map (edeval j ts db) Ld))"
    by (auto dest: 23 split: prod.splits)
  then show ?case
    using 23
    by (auto simp only: Let_def deval.simps edeval.simps mbufn_add Rep_edformula.simps
        mbuf_t_empty.rep_eq mbuf_t_append.rep_eq
        split: prod.splits dest!: mebufnt_take dest: mbufnt_take_app)
next
  case (24 j ts db m I mr mrs pls Ld dbuf nts t daux)
  have "map fst (map (edeval j ts db) Ld) = map fst (map (deval j ts db) (map Rep_edformula Ld))"
    "map snd (map (deval j ts db) (map Rep_edformula Ld))
      = map Rep_edformula (map snd (map (edeval j ts db) Ld))"
    by (auto dest: 24 split: prod.splits)
  then show ?case
    using 24
    by (auto simp only: Let_def deval.simps edeval.simps mbufn_add Rep_edformula.simps
        mbuf_t_append.rep_eq
        split: prod.splits dest!: mebufnt_take)
next
  case (25 j ts db pl \<alpha> dbf1 dags \<phi> \<psi> dbf2 nts daux)
  obtain as \<alpha>' where a: "edeval j ts db \<alpha> = (as, \<alpha>')" by (cases "edeval j ts db \<alpha>")
  obtain xs \<phi>' where x: "edeval j ts db \<phi> = (xs, \<phi>')" by (cases "edeval j ts db \<phi>")
  obtain ys \<psi>' where y: "edeval j ts db \<psi> = (ys, \<psi>')" by (cases "edeval j ts db \<psi>")
  let ?f = "\<lambda>r1 r2 t (ws, ax). let ax = gupdate_mmtaux dags t r1 r2 ax
    in (ws @ [if gmmtaux_empty ax then None else Some (dsan (gresult_mmtaux dags ax))], ax)"
  obtain ws daux' b2 nts' where t:
    "mebuf2T_take ?f ([], daux) (mebuf2_add xs ys dbf2) (nts @@ ts) = ((ws, daux'), b2, nts')"
    by (cases "mebuf2T_take ?f ([], daux) (mebuf2_add xs ys dbf2) (nts @@ ts)") auto
  let ?g = "\<lambda>r1 r2. case r2 of None \<Rightarrow> r1 | Some z \<Rightarrow> dbin_join pl r1 True z"
  obtain zs b1 where u: "mebuf2_take ?g (mebuf2_add as ws dbf1) = (zs, b1)"
    by (cases "mebuf2_take ?g (mebuf2_add as ws dbf1)")
  have ia: "deval j ts db (Rep_edformula \<alpha>) = (as, Rep_edformula \<alpha>')" using 25(1) a by simp
  have ix: "deval j ts db (Rep_edformula \<phi>) = (xs, Rep_edformula \<phi>')" using 25(2) a x by simp
  have iy: "deval j ts db (Rep_edformula \<psi>) = (ys, Rep_edformula \<psi>')" using 25(3) a x y by simp
  have t': "mbuf2T_take ?f ([], daux) (mbuf2_add xs ys (map_prod Rep_mbuf_t Rep_mbuf_t dbf2))
      (Rep_mbuf_t nts @ ts) = ((ws, daux'), map_prod Rep_mbuf_t Rep_mbuf_t b2, Rep_mbuf_t nts')"
    using mebuf2T_take[OF t] by (simp add: mbuf2_add mbuf_t_append.rep_eq)
  have u': "mbuf2_take ?g (mbuf2_add as ws (map_prod Rep_mbuf_t Rep_mbuf_t dbf1))
      = (zs, map_prod Rep_mbuf_t Rep_mbuf_t b1)"
    using mebuf2_take[OF u] by (simp add: mbuf2_add)
  show ?case
    by (simp only: Rep_edformula.simps deval.simps edeval.simps Let_def ia ix iy a x y
        t[unfolded Let_def] t'[unfolded Let_def] u u' prod.case)
qed (auto simp: mbuf2_add mbuf_t_empty.rep_eq mbuf_t_append.rep_eq
    simp del: mprev_next.simps meprev_next.simps dsx_eval_since.simps edsx_eval_since.simps
    split: prod.splits dest!: mebuf2_take mebuf2t_take mebuf2T_take meprev_next edsx_eval_since)

subsection \<open>The code setup\<close>

text \<open>
  As for the kernel: the specification type keeps its name and its theorems, and the generated
  code represents it by the type with the queue buffers.  Everything the code calls on it goes
  through the two equations below; the compiler's own equation is in the next theory,
  @{text Dense_Descend_Code}.
\<close>

code_datatype Rep_edformula

declare [[code drop: deval vdfail_nodes]]

lemma deval_code[code]:
  "deval j ts db (Rep_edformula \<phi>) = (let (zs, \<phi>') = edeval j ts db \<phi> in (zs, Rep_edformula \<phi>'))"
  by (rule edeval_Rep)

lemma vdfail_nodes_code[code]: "vdfail_nodes (Rep_edformula \<phi>) = evdfail_nodes \<phi>"
  by (rule vdfail_nodes_Rep)

(*<*)
end
(*>*)
