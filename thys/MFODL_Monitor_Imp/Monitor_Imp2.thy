(*<*)
theory Monitor_Imp2
  imports Since_Imp2 Until_Imp2 Join_Imp2
begin
(*>*)

section \<open>A monitor over the heap-resident Since structure\<close>

text \<open>
  A clone of the monadic evaluation function over the structure of
  @{theory MFODL_Monitor_Imp.Since_Imp2}. Definitions only; the verdicts are checked against
  the verified kernel by differential testing.
\<close>

type_synonym mformula_p = "(mmasaux, muaux_dq, event_data mmtaux) meformula"
type_synonym mformula_j = "(msaux_j, muaux_j, event_data mmtaux) meformula"
type_synonym mstate_j = "nat \<times> nat \<times> mformula_j \<times> nat \<times> ts queue"

fun embed :: "mformula_p \<Rightarrow> mformula_j" where
  "embed (MRel rel) = MRel rel"
| "embed (MPred e tms mode) = MPred e tms mode"
| "embed (MLet p m \<phi> \<psi>) = MLet p m (embed \<phi>) (embed \<psi>)"
| "embed (MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = MFrz p m (embed \<phi>) (embed \<psi>) jfrz jpsi0 jphi \<alpha>s"
| "embed (MLetPast p m \<phi> \<psi> i buf) = MLetPast p m (embed \<phi>) (embed \<psi>) i buf"
| "embed (MAnd A \<phi> pos B \<psi> buf) = MAnd A (embed \<phi>) pos B (embed \<psi>) buf"
| "embed (MAndAssign \<phi> conf) = MAndAssign (embed \<phi>) conf"
| "embed (MAndRel \<phi> conf) = MAndRel (embed \<phi>) conf"
| "embed (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
    MAndTrigger V (embed \<phi>) buf1 args (embed \<phi>') (embed \<psi>') buf2 nts aux"
| "embed (MAnds A_pos A_neg L buf) = MAnds A_pos A_neg (map embed L) buf"
| "embed (MOr \<phi> \<psi> buf) = MOr (embed \<phi>) (embed \<psi>) buf"
| "embed (MNeg \<phi>) = MNeg (embed \<phi>)"
| "embed (MExists \<phi>) = MExists (embed \<phi>)"
| "embed (MAgg args \<phi>) = MAgg args (embed \<phi>)"
| "embed (MPrev I \<phi> first buf nts) = MPrev I (embed \<phi>) first buf nts"
| "embed (MNext I \<phi> first nts) = MNext I (embed \<phi>) first nts"
| "embed (MSince args \<phi> \<psi> buf aux) = MSince args (embed \<phi>) (embed \<psi>) buf (MSJ_pure aux)"
| "embed (MUntil args \<phi> \<psi> buf nts t aux) = MUntil args (embed \<phi>) (embed \<psi>) buf nts t (MUJ_pure aux)"
| "embed (MTrigger args \<phi> \<psi> buf nts aux) = MTrigger args (embed \<phi>) (embed \<psi>) buf nts aux"
| "embed (MMatchP I mr mrs \<phi>s buf nts aux) = MMatchP I mr mrs (map embed \<phi>s) buf nts aux"
| "embed (MMatchF I mr mrs \<phi>s buf nts t aux) = MMatchF I mr mrs (map embed \<phi>s) buf nts t aux"
| "embed (MTP mt i) = MTP mt i"
| "embed (MTS mt) = MTS mt"

fun purify :: "mformula_j \<Rightarrow> mformula_p" where
  "purify (MRel rel) = MRel rel"
| "purify (MPred e tms mode) = MPred e tms mode"
| "purify (MLet p m \<phi> \<psi>) = MLet p m (purify \<phi>) (purify \<psi>)"
| "purify (MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = MFrz p m (purify \<phi>) (purify \<psi>) jfrz jpsi0 jphi \<alpha>s"
| "purify (MLetPast p m \<phi> \<psi> i buf) = MLetPast p m (purify \<phi>) (purify \<psi>) i buf"
| "purify (MAnd A \<phi> pos B \<psi> buf) = MAnd A (purify \<phi>) pos B (purify \<psi>) buf"
| "purify (MAndAssign \<phi> conf) = MAndAssign (purify \<phi>) conf"
| "purify (MAndRel \<phi> conf) = MAndRel (purify \<phi>) conf"
| "purify (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
    MAndTrigger V (purify \<phi>) buf1 args (purify \<phi>') (purify \<psi>') buf2 nts aux"
| "purify (MAnds A_pos A_neg L buf) = MAnds A_pos A_neg (map purify L) buf"
| "purify (MOr \<phi> \<psi> buf) = MOr (purify \<phi>) (purify \<psi>) buf"
| "purify (MNeg \<phi>) = MNeg (purify \<phi>)"
| "purify (MExists \<phi>) = MExists (purify \<phi>)"
| "purify (MAgg args \<phi>) = MAgg args (purify \<phi>)"
| "purify (MPrev I \<phi> first buf nts) = MPrev I (purify \<phi>) first buf nts"
| "purify (MNext I \<phi> first nts) = MNext I (purify \<phi>) first nts"
| "purify (MSince args \<phi> \<psi> buf (MSJ_pure s)) = MSince args (purify \<phi>) (purify \<psi>) buf s"
| "purify (MSince args \<phi> \<psi> buf (MSJ_imp q)) = MSince args (purify \<phi>) (purify \<psi>) buf (init_mmasaux args)"
| "purify (MUntil args \<phi> \<psi> buf nts t (MUJ_pure a)) = MUntil args (purify \<phi>) (purify \<psi>) buf nts t a"
| "purify (MUntil args \<phi> \<psi> buf nts t (MUJ_imp d)) = MUntil args (purify \<phi>) (purify \<psi>) buf nts t (init_muaux_dq args)"
| "purify (MTrigger args \<phi> \<psi> buf nts aux) = MTrigger args (purify \<phi>) (purify \<psi>) buf nts aux"
| "purify (MMatchP I mr mrs \<phi>s buf nts aux) = MMatchP I mr mrs (map purify \<phi>s) buf nts aux"
| "purify (MMatchF I mr mrs \<phi>s buf nts t aux) = MMatchF I mr mrs (map purify \<phi>s) buf nts t aux"
| "purify (MTP mt i) = MTP mt i"
| "purify (MTS mt) = MTS mt"

partial_function (heap) eval_since_j :: "args \<Rightarrow> event_data table list \<Rightarrow> event_data mebuf2S \<Rightarrow> msaux_j \<Rightarrow>
    (event_data table list \<times> event_data mebuf2S \<times> msaux_j) Heap" where
  [code]:
  "eval_since_j args rs buf aux = (case buf of (xs, ys, ts, skew) \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow>
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          (if skew \<or> memL (args_ivl args) 0
           then return (rev rs, (x ## xs', mbuf_t_empty, t ## ts', skew), aux)
           else do { aux \<leftarrow> add_new_ts_j args t aux; aux' \<leftarrow> join_j args x aux; r \<leftarrow> result_j args aux';
                     return (rev (r # rs), (xs', mbuf_t_empty, ts', True), aux') })
        | (None, ts') \<Rightarrow> return (rev rs, (x ## xs', mbuf_t_empty, mbuf_t_empty, skew), aux))
      | (None, xs') \<Rightarrow> return (rev rs, (mbuf_t_empty, mbuf_t_empty, ts, skew), aux))
    | (Some y, ys') \<Rightarrow>
      if skew then do { aux \<leftarrow> add_new_table_j args y aux; eval_since_j args rs (xs, ys', ts, False) aux }
      else
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          do { aux \<leftarrow> add_new_ts_j args t aux; aux \<leftarrow> join_j args x aux; aux' \<leftarrow> add_new_table_j args y aux;
               r \<leftarrow> result_j args aux'; eval_since_j args (r # rs) (xs', ys', ts', False) aux' }
        | (None, ts') \<Rightarrow> return (rev rs, (x ## xs', y ## ys', ts', skew), aux))
      | (None, xs') \<Rightarrow> return (rev rs, (mbuf_t_empty, y ## ys', ts, skew), aux))))"

partial_function (heap) mebuf2t_take_j :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> 'b \<Rightarrow>
    event_data mebuf2 \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> ('b \<times> event_data mebuf2 \<times> ts \<times> ts mbuf_t) Heap" where
  [code]:
  "mebuf2t_take_j f z buf t0 ts = (case buf of (xs, ys) \<Rightarrow>
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> return (z, (xs, ys), t0, ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> return (z, (xs', ys), t, t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> return (z, (x ## xs', ys'), t, t ## ts') | (Some y, ys') \<Rightarrow>
    do { z \<leftarrow> f x y t z; mebuf2t_take_j f z (xs', ys') t ts' }))))"

fun meval_j :: "nat \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> mformula_j \<Rightarrow> (event_data table list \<times> mformula_j) Heap"
  and meval_j_list :: "nat \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> mformula_j list \<Rightarrow>
    ((event_data table list \<times> mformula_j) list) Heap" where
  "meval_j_list j n ts db [] = return []"
| "meval_j_list j n ts db (\<phi> # r) = do {
     x \<leftarrow> meval_j j n ts db \<phi>;
     xs \<leftarrow> meval_j_list j n ts db r;
     return (x # xs) }"
| "meval_j j n ts db (MAnds A_pos A_neg L buf) = do {
     R \<leftarrow> meval_j_list j n ts db L;
     return (let buf = mebufn_add (map fst R) buf;
                 (zs, buf) = mebufn_take (\<lambda>xs zs. zs @@ [mmulti_join n A_pos A_neg xs]) mbuf_t_empty buf
             in (Rep_mbuf_t zs, MAnds A_pos A_neg (map snd R) buf)) }"
| "meval_j j n ts db (MAnd A \<phi> pos B \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_j j n ts db \<psi>;
     r \<leftarrow> mebuf2_take_j (\<lambda>r1 r2. bin_join_j n A r1 pos B r2) (mebuf2_add xs ys buf);
     return (fst r, MAnd A \<phi> pos B \<psi> (snd r)) }"
| "meval_j j n ts db (MAndAssign \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     return (map (\<lambda>r. eval_assignment conf ` r) xs, MAndAssign \<phi> conf) }"
| "meval_j j n ts db (MAndRel \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     return (map (Set.filter (eval_constraint conf)) xs, MAndRel \<phi> conf) }"
| "meval_j j n ts db (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = do {
     (as, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     (xs, \<phi>') \<leftarrow> meval_j j n ts db \<phi>';
     (ys, \<psi>') \<leftarrow> meval_j j n ts db \<psi>';
     return (let ((zs_trigger, aux), buf2, nts) = mebuf2T_take (\<lambda>r1 r2 t (zs, aux).
         let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
         in (zs @ [(fv_z, z)], aux)) ([], aux) (mebuf2_add xs ys buf2) (nts @@ ts);
       (zs, buf1) = mebuf2_take (\<lambda>r1 (V_trigger, r2). bin_join n V r1 True V_trigger r2) (mebuf2_add as zs_trigger buf1)
       in (zs, MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux)) }"
| "meval_j j n ts db (MOr \<phi> \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_j j n ts db \<psi>;
     return (let (zs, buf) = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
       in (zs, MOr \<phi> \<psi> buf)) }"
| "meval_j j n ts db (MNeg \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     return (map (\<lambda>r. if r = empty_table then unit_table n else empty_table) xs, MNeg \<phi>) }"
| "meval_j j n ts db (MExists \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_j j (Suc n) ts db \<phi>;
     return (map (\<lambda>r. tl ` r) xs, MExists \<phi>) }"
| "meval_j j n ts db (MAgg args \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_j j (length (aggargs_tys args) + n) ts db \<phi>;
     return (map (eval_aggargs args) xs, MAgg args \<phi>) }"
| "meval_j j n ts db (MPrev I \<phi> first buf nts) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     return (if first \<and> ts = [] then ([], MPrev I \<phi> True (buf @@ xs) (nts @@ ts))
       else let (zs, buf, nts) = meprev_next I (buf @@ xs) (nts @@ ts)
         in (if first then empty_table # zs else zs, MPrev I \<phi> False buf nts)) }"
| "meval_j j n ts db (MNext I \<phi> first nts) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     return (let (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
       (zs, buf, nts) = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
       in (zs, MNext I \<phi> first nts)) }"
| "meval_j j n ts db (MSince args \<phi> \<psi> buf aux) = do {
     (xs, \<phi>) \<leftarrow> meval_j j (args_n args) ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_j j (args_n args) ts db \<psi>;
     (zs, buf, aux) \<leftarrow> eval_since_j args [] (mebuf2S_add xs ys ts buf) aux;
     return (zs, MSince args \<phi> \<psi> buf aux) }"
| "meval_j j n ts db (MUntil args \<phi> \<psi> buf nts t aux) = do {
     (xs, \<phi>) \<leftarrow> meval_j j (args_n args) ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_j j (args_n args) ts db \<psi>;
     r \<leftarrow> mebuf2t_take_j (add_new_u_j args) aux (mebuf2_add xs ys buf) t (nts @@ ts);
     (case r of (aux, buf, nt, nts') \<Rightarrow>
      do { z \<leftarrow> eval_u_j args nt aux;
           return (fst z, MUntil args \<phi> \<psi> buf nts' nt (snd z)) }) }"
| "meval_j j n ts db (MTrigger args \<phi> \<psi> buf nts aux) = do {
     (xs, \<phi>) \<leftarrow> meval_j j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_j j n ts db \<psi>;
     return (let ((zs, aux), buf, nts) = mebuf2T_take (\<lambda>r1 r2 t (zs, aux).
         let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
         in (zs @ [z], aux)) ([], aux) (mebuf2_add xs ys buf) (nts @@ ts)
       in (zs, MTrigger args \<phi> \<psi> buf nts aux)) }"
| "meval_j j n ts db \<phi>i = return (let (xs, \<phi>) = meeval j n ts db (purify \<phi>i) in (xs, embed \<phi>))"

fun reset :: "mformula_p \<Rightarrow> mformula_p" where
  "reset (MAnd A \<phi> pos B \<psi> buf) = MAnd A (reset \<phi>) pos B (reset \<psi>) buf"
| "reset (MAndAssign \<phi> conf) = MAndAssign (reset \<phi>) conf"
| "reset (MAndRel \<phi> conf) = MAndRel (reset \<phi>) conf"
| "reset (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
    MAndTrigger V (reset \<phi>) buf1 args (reset \<phi>') (reset \<psi>') buf2 nts aux"
| "reset (MOr \<phi> \<psi> buf) = MOr (reset \<phi>) (reset \<psi>) buf"
| "reset (MNeg \<phi>) = MNeg (reset \<phi>)"
| "reset (MExists \<phi>) = MExists (reset \<phi>)"
| "reset (MAgg args \<phi>) = MAgg args (reset \<phi>)"
| "reset (MPrev I \<phi> first buf nts) = MPrev I (reset \<phi>) first buf nts"
| "reset (MNext I \<phi> first nts) = MNext I (reset \<phi>) first nts"
| "reset (MSince args \<phi> \<psi> buf aux) = MSince args (reset \<phi>) (reset \<psi>) buf (init_mmasaux args)"
| "reset (MUntil args \<phi> \<psi> buf nts t aux) = MUntil args (reset \<phi>) (reset \<psi>) buf nts t aux"
| "reset (MTrigger args \<phi> \<psi> buf nts aux) = MTrigger args (reset \<phi>) (reset \<psi>) buf nts aux"
| "reset \<phi> = \<phi>"

fun mformula_j_of :: "mformula_p \<Rightarrow> mformula_j Heap"
  and mformula_j_of_list :: "mformula_p list \<Rightarrow> mformula_j list Heap" where
  "mformula_j_of_list [] = return []"
| "mformula_j_of_list (\<phi> # r) = do {
     \<phi>i \<leftarrow> mformula_j_of \<phi>; \<phi>s \<leftarrow> mformula_j_of_list r; return (\<phi>i # \<phi>s) }"
| "mformula_j_of (MAnds A_pos A_neg L buf) = do {
     Li \<leftarrow> mformula_j_of_list L; return (MAnds A_pos A_neg Li buf) }"
| "mformula_j_of (MAnd A \<phi> pos B \<psi> buf) = do {
     \<phi>i \<leftarrow> mformula_j_of \<phi>; \<psi>i \<leftarrow> mformula_j_of \<psi>; return (MAnd A \<phi>i pos B \<psi>i buf) }"
| "mformula_j_of (MAndAssign \<phi> conf) = do { \<phi>i \<leftarrow> mformula_j_of \<phi>; return (MAndAssign \<phi>i conf) }"
| "mformula_j_of (MAndRel \<phi> conf) = do { \<phi>i \<leftarrow> mformula_j_of \<phi>; return (MAndRel \<phi>i conf) }"
| "mformula_j_of (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = do {
     \<phi>i \<leftarrow> mformula_j_of \<phi>; \<phi>i' \<leftarrow> mformula_j_of \<phi>'; \<psi>i' \<leftarrow> mformula_j_of \<psi>';
     return (MAndTrigger V \<phi>i buf1 args \<phi>i' \<psi>i' buf2 nts aux) }"
| "mformula_j_of (MOr \<phi> \<psi> buf) = do {
     \<phi>i \<leftarrow> mformula_j_of \<phi>; \<psi>i \<leftarrow> mformula_j_of \<psi>; return (MOr \<phi>i \<psi>i buf) }"
| "mformula_j_of (MNeg \<phi>) = do { \<phi>i \<leftarrow> mformula_j_of \<phi>; return (MNeg \<phi>i) }"
| "mformula_j_of (MExists \<phi>) = do { \<phi>i \<leftarrow> mformula_j_of \<phi>; return (MExists \<phi>i) }"
| "mformula_j_of (MAgg args \<phi>) = do { \<phi>i \<leftarrow> mformula_j_of \<phi>; return (MAgg args \<phi>i) }"
| "mformula_j_of (MPrev I \<phi> first buf nts) = do { \<phi>i \<leftarrow> mformula_j_of \<phi>; return (MPrev I \<phi>i first buf nts) }"
| "mformula_j_of (MNext I \<phi> first nts) = do { \<phi>i \<leftarrow> mformula_j_of \<phi>; return (MNext I \<phi>i first nts) }"
| "mformula_j_of (MSince args \<phi> \<psi> buf aux) = do {
     \<phi>i \<leftarrow> mformula_j_of \<phi>; \<psi>i \<leftarrow> mformula_j_of \<psi>; q \<leftarrow> init_j args;
     return (MSince args \<phi>i \<psi>i buf q) }"
| "mformula_j_of (MUntil args \<phi> \<psi> buf nts t aux) = do {
     \<phi>i \<leftarrow> mformula_j_of \<phi>; \<psi>i \<leftarrow> mformula_j_of \<psi>; d \<leftarrow> init_u_j args;
     return (MUntil args \<phi>i \<psi>i buf nts t d) }"
| "mformula_j_of (MTrigger args \<phi> \<psi> buf nts aux) = do {
     \<phi>i \<leftarrow> mformula_j_of \<phi>; \<psi>i \<leftarrow> mformula_j_of \<psi>; return (MTrigger args \<phi>i \<psi>i buf nts aux) }"
| "mformula_j_of \<phi> = return (embed \<phi>)"

fun annotate_verdicts_j :: "nat \<Rightarrow> ts queue \<Rightarrow> event_data table list \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list \<Rightarrow> nat \<times> ts queue \<times> (nat \<times> ts \<times> event_data table) list" where
  "annotate_verdicts_j i tq [] acc = (i, tq, rev acc)"
| "annotate_verdicts_j i tq (v # vs) acc = (case pop tq of
      (None, tq') \<Rightarrow> (i + 1 + length vs, (tl_queue ^^ (1 + length vs)) tq', rev acc)
    | (Some t, tq') \<Rightarrow> annotate_verdicts_j (i + 1) tq' vs ((i, t, v) # acc))"

definition mstep_j :: "database \<times> ts \<Rightarrow> mstate_j \<Rightarrow> ((nat \<times> ts \<times> event_data table) list \<times> mstate_j) Heap" where
  "mstep_j tdb sti = (case sti of (i, j, m, n, tq) \<Rightarrow> do {
     (vs, m') \<leftarrow> meval_j (j + 1) n [snd tdb] (fst tdb) m;
     return (case annotate_verdicts_j i (append_queue (snd tdb) tq) vs [] of
       (i', tq', vs') \<Rightarrow> (vs', (i', j + 1, m', n, tq'))) })"

definition minit_safe_j :: "ty Formula.formula \<Rightarrow> mstate_j Heap" where
  "minit_safe_j \<phi> = do {
     m \<leftarrow> mformula_j_of (meinit0 (Formula.nfv \<phi>) \<phi>);
     return (0, 0, m, Formula.nfv \<phi>, empty_queue) }"

(*<*)
end
(*>*)
