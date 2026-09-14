(*<*)
theory Monitor_Imp
  imports Optimized_Since_Imp
begin
(*>*)

section \<open>A monitor with heap-resident Since structures\<close>

text \<open>
  The auxiliary structures are threaded through @{const meval} as pure values, so a structure
  that lives on the heap forces the evaluation function to be monadic. We clone @{const meval}
  in the heap monad for the fragment of formulas in which a Since operator can profit from the
  imperative structure of @{theory MFODL_Monitor_Devel.Optimized_Since_Imp}: the Boolean
  connectives, quantification, aggregation, the temporal operators and Since itself. Under the
  remaining constructors (@{text LET}, @{text LETPAST}, @{text FRZ}, @{text ANDS}, the regular
  expression operators), whose evaluation functions call the evaluation of their subformulas in
  loops, the subformulas keep the pure structure and are evaluated by the pure @{const meval};
  this costs nothing but the acceleration. Since the fragment is closed under the operators
  that a monitored formula is usually built from, the Since operators of a typical formula are
  all in it.
\<close>

type_synonym mformula_p = "(mmasaux, muaux_dq, event_data mmtaux) mformula"
type_synonym mformula_h = "(msaux_h, muaux_dq, event_data mmtaux) mformula"
type_synonym mstate_p = "(mmasaux, muaux_dq, event_data mmtaux) mstate"
type_synonym mstate_h = "(msaux_h, muaux_dq, event_data mmtaux) mstate"

subsection \<open>Formulas with pure structures, and back\<close>

fun embed :: "mformula_p \<Rightarrow> mformula_h" where
  "embed (mformula.MRel rel) = mformula.MRel rel"
| "embed (mformula.MPred e tms mode) = mformula.MPred e tms mode"
| "embed (mformula.MLet p m \<phi> \<psi>) = mformula.MLet p m (embed \<phi>) (embed \<psi>)"
| "embed (mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = mformula.MFrz p m (embed \<phi>) (embed \<psi>) jfrz jpsi0 jphi \<alpha>s"
| "embed (mformula.MLetPast p m \<phi> \<psi> i buf) = mformula.MLetPast p m (embed \<phi>) (embed \<psi>) i buf"
| "embed (mformula.MAnd A \<phi> pos B \<psi> buf) = mformula.MAnd A (embed \<phi>) pos B (embed \<psi>) buf"
| "embed (mformula.MAndAssign \<phi> conf) = mformula.MAndAssign (embed \<phi>) conf"
| "embed (mformula.MAndRel \<phi> conf) = mformula.MAndRel (embed \<phi>) conf"
| "embed (mformula.MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
    mformula.MAndTrigger V (embed \<phi>) buf1 args (embed \<phi>') (embed \<psi>') buf2 nts aux"
| "embed (mformula.MAnds A_pos A_neg L buf) = mformula.MAnds A_pos A_neg (map embed L) buf"
| "embed (mformula.MOr \<phi> \<psi> buf) = mformula.MOr (embed \<phi>) (embed \<psi>) buf"
| "embed (mformula.MNeg \<phi>) = mformula.MNeg (embed \<phi>)"
| "embed (mformula.MExists \<phi>) = mformula.MExists (embed \<phi>)"
| "embed (mformula.MAgg args \<phi>) = mformula.MAgg args (embed \<phi>)"
| "embed (mformula.MPrev I \<phi> first buf nts) = mformula.MPrev I (embed \<phi>) first buf nts"
| "embed (mformula.MNext I \<phi> first nts) = mformula.MNext I (embed \<phi>) first nts"
| "embed (mformula.MSince args \<phi> \<psi> buf aux) = mformula.MSince args (embed \<phi>) (embed \<psi>) buf (MSH_pure aux)"
| "embed (mformula.MUntil args \<phi> \<psi> buf nts t aux) = mformula.MUntil args (embed \<phi>) (embed \<psi>) buf nts t aux"
| "embed (mformula.MTrigger args \<phi> \<psi> buf nts aux) = mformula.MTrigger args (embed \<phi>) (embed \<psi>) buf nts aux"
| "embed (mformula.MMatchP I mr mrs \<phi>s buf nts aux) = mformula.MMatchP I mr mrs (map embed \<phi>s) buf nts aux"
| "embed (mformula.MMatchF I mr mrs \<phi>s buf nts t aux) = mformula.MMatchF I mr mrs (map embed \<phi>s) buf nts t aux"
| "embed (mformula.MTP mt i) = mformula.MTP mt i"
| "embed (mformula.MTS mt) = mformula.MTS mt"

fun purify :: "mformula_h \<Rightarrow> mformula_p" where
  "purify (mformula.MRel rel) = mformula.MRel rel"
| "purify (mformula.MPred e tms mode) = mformula.MPred e tms mode"
| "purify (mformula.MLet p m \<phi> \<psi>) = mformula.MLet p m (purify \<phi>) (purify \<psi>)"
| "purify (mformula.MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = mformula.MFrz p m (purify \<phi>) (purify \<psi>) jfrz jpsi0 jphi \<alpha>s"
| "purify (mformula.MLetPast p m \<phi> \<psi> i buf) = mformula.MLetPast p m (purify \<phi>) (purify \<psi>) i buf"
| "purify (mformula.MAnd A \<phi> pos B \<psi> buf) = mformula.MAnd A (purify \<phi>) pos B (purify \<psi>) buf"
| "purify (mformula.MAndAssign \<phi> conf) = mformula.MAndAssign (purify \<phi>) conf"
| "purify (mformula.MAndRel \<phi> conf) = mformula.MAndRel (purify \<phi>) conf"
| "purify (mformula.MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
    mformula.MAndTrigger V (purify \<phi>) buf1 args (purify \<phi>') (purify \<psi>') buf2 nts aux"
| "purify (mformula.MAnds A_pos A_neg L buf) = mformula.MAnds A_pos A_neg (map purify L) buf"
| "purify (mformula.MOr \<phi> \<psi> buf) = mformula.MOr (purify \<phi>) (purify \<psi>) buf"
| "purify (mformula.MNeg \<phi>) = mformula.MNeg (purify \<phi>)"
| "purify (mformula.MExists \<phi>) = mformula.MExists (purify \<phi>)"
| "purify (mformula.MAgg args \<phi>) = mformula.MAgg args (purify \<phi>)"
| "purify (mformula.MPrev I \<phi> first buf nts) = mformula.MPrev I (purify \<phi>) first buf nts"
| "purify (mformula.MNext I \<phi> first nts) = mformula.MNext I (purify \<phi>) first nts"
| "purify (mformula.MSince args \<phi> \<psi> buf (MSH_pure s)) = mformula.MSince args (purify \<phi>) (purify \<psi>) buf s"
| "purify (mformula.MSince args \<phi> \<psi> buf (MSH_imp q)) = mformula.MSince args (purify \<phi>) (purify \<psi>) buf (init_mmasaux args)"
| "purify (mformula.MUntil args \<phi> \<psi> buf nts t aux) = mformula.MUntil args (purify \<phi>) (purify \<psi>) buf nts t aux"
| "purify (mformula.MTrigger args \<phi> \<psi> buf nts aux) = mformula.MTrigger args (purify \<phi>) (purify \<psi>) buf nts aux"
| "purify (mformula.MMatchP I mr mrs \<phi>s buf nts aux) = mformula.MMatchP I mr mrs (map purify \<phi>s) buf nts aux"
| "purify (mformula.MMatchF I mr mrs \<phi>s buf nts t aux) = mformula.MMatchF I mr mrs (map purify \<phi>s) buf nts t aux"
| "purify (mformula.MTP mt i) = mformula.MTP mt i"
| "purify (mformula.MTS mt) = mformula.MTS mt"

lemma purify_embed[simp]: "purify (embed \<phi>) = \<phi>"
  by (induction \<phi> rule: embed.induct) (auto simp: comp_def intro!: map_idI)

lemma comp_purify_embed[simp]: "purify \<circ> embed = id"
  by (auto simp: fun_eq_iff)

lemma map_purify_embed[simp]: "map purify (map embed \<phi>s) = \<phi>s"
  by (induction \<phi>s) auto

subsection \<open>The relation between pure and heap formulas\<close>

text \<open>
  In the fragment the two formulas agree except for the Since structures, which are related by
  @{const is_msaux_h}; elsewhere the heap formula is the embedding of the pure one and carries
  no heap structure at all.
\<close>

fun is_mformula :: "mformula_p \<Rightarrow> mformula_h \<Rightarrow> assn" where
  "is_mformula (mformula.MAnd A \<phi> pos B \<psi> buf) \<chi> =
    (case \<chi> of mformula.MAnd A' \<phi>i pos' B' \<psi>i buf' \<Rightarrow>
      \<up>(A' = A \<and> pos' = pos \<and> B' = B \<and> buf' = buf) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MAndAssign \<phi> conf) \<chi> =
    (case \<chi> of mformula.MAndAssign \<phi>i conf' \<Rightarrow> \<up>(conf' = conf) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MAndRel \<phi> conf) \<chi> =
    (case \<chi> of mformula.MAndRel \<phi>i conf' \<Rightarrow> \<up>(conf' = conf) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) \<chi> =
    (case \<chi> of mformula.MAndTrigger V' \<phi>i buf1' args' \<phi>i' \<psi>i' buf2' nts' aux' \<Rightarrow>
      \<up>(V' = V \<and> buf1' = buf1 \<and> args' = args \<and> buf2' = buf2 \<and> nts' = nts \<and> aux' = aux) *
      is_mformula \<phi> \<phi>i * is_mformula \<phi>' \<phi>i' * is_mformula \<psi>' \<psi>i' | _ \<Rightarrow> false)"
| "is_mformula (mformula.MOr \<phi> \<psi> buf) \<chi> =
    (case \<chi> of mformula.MOr \<phi>i \<psi>i buf' \<Rightarrow> \<up>(buf' = buf) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MNeg \<phi>) \<chi> = (case \<chi> of mformula.MNeg \<phi>i \<Rightarrow> is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MExists \<phi>) \<chi> = (case \<chi> of mformula.MExists \<phi>i \<Rightarrow> is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MAgg args \<phi>) \<chi> =
    (case \<chi> of mformula.MAgg args' \<phi>i \<Rightarrow> \<up>(args' = args) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MPrev I \<phi> first buf nts) \<chi> =
    (case \<chi> of mformula.MPrev I' \<phi>i first' buf' nts' \<Rightarrow>
      \<up>(I' = I \<and> first' = first \<and> buf' = buf \<and> nts' = nts) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MNext I \<phi> first nts) \<chi> =
    (case \<chi> of mformula.MNext I' \<phi>i first' nts' \<Rightarrow>
      \<up>(I' = I \<and> first' = first \<and> nts' = nts) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (mformula.MSince args \<phi> \<psi> buf aux) \<chi> =
    (case \<chi> of mformula.MSince args' \<phi>i \<psi>i buf' auxi \<Rightarrow>
      \<up>(args' = args \<and> buf' = buf) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i * is_msaux_h args aux auxi | _ \<Rightarrow> false)"
| "is_mformula (mformula.MUntil args \<phi> \<psi> buf nts t aux) \<chi> =
    (case \<chi> of mformula.MUntil args' \<phi>i \<psi>i buf' nts' t' aux' \<Rightarrow>
      \<up>(args' = args \<and> buf' = buf \<and> nts' = nts \<and> t' = t \<and> aux' = aux) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i
    | _ \<Rightarrow> false)"
| "is_mformula (mformula.MTrigger args \<phi> \<psi> buf nts aux) \<chi> =
    (case \<chi> of mformula.MTrigger args' \<phi>i \<psi>i buf' nts' aux' \<Rightarrow>
      \<up>(args' = args \<and> buf' = buf \<and> nts' = nts \<and> aux' = aux) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i | _ \<Rightarrow> false)"
| "is_mformula \<phi> \<chi> = \<up>(\<chi> = embed \<phi>)"

lemma is_mformula_embed: "is_mformula \<phi> (embed \<phi>) = emp"
  by (induction \<phi>) simp_all

subsection \<open>Evaluation of the Since buffer\<close>

fun eval_since_imp :: "args \<Rightarrow> event_data table list \<Rightarrow> event_data mbuf2S \<Rightarrow> msaux_h \<Rightarrow>
    (event_data table list \<times> event_data mbuf2S \<times> msaux_h) Heap" where
  "eval_since_imp args rs (x # xs, [], t # ts, skew) aux =
    (if skew \<or> memL (args_ivl args) 0 then return (rev rs, (x # xs, [], t # ts, skew), aux)
     else do { aux \<leftarrow> add_new_ts_h args t aux; aux' \<leftarrow> join_h args x aux; r \<leftarrow> result_h args aux';
               return (rev (r # rs), (xs, [], ts, True), aux') })"
| "eval_since_imp args rs (xs, y # ys, ts, True) aux =
    do { aux \<leftarrow> add_new_table_h args y aux; eval_since_imp args rs (xs, ys, ts, False) aux }"
| "eval_since_imp args rs (x # xs, y # ys, t # ts, False) aux =
    do { aux \<leftarrow> add_new_ts_h args t aux; aux \<leftarrow> join_h args x aux; aux' \<leftarrow> add_new_table_h args y aux;
         r \<leftarrow> result_h args aux'; eval_since_imp args (r # rs) (xs, ys, ts, False) aux' }"
| "eval_since_imp args rs buf aux = return (rev rs, buf, aux)"

lemma eval_since_imp_rule:
  "<is_msaux_h args s q> eval_since_imp args rs buf q
   <\<lambda>r. \<up>(fst r = fst (meval_since args rs buf s) \<and> fst (snd r) = fst (snd (meval_since args rs buf s))) *
      is_msaux_h args (snd (snd (meval_since args rs buf s))) (snd (snd r))>\<^sub>t"
proof (induction rs buf s arbitrary: q rule: default_maux.eval_since.induct[where args = args])
  case (1 rs x xs t ts skew aux)
  show ?case
    by (sep_auto heap: add_new_ts_h_rule join_h_rule result_h_rule simp: Let_def)
next
  case (2 rs xs y ys ts aux)
  show ?case
    by (sep_auto heap: add_new_table_h_rule "2.IH")
next
  case (3 rs x xs y ys t ts aux)
  show ?case
    by (sep_auto heap: add_new_ts_h_rule join_h_rule add_new_table_h_rule result_h_rule "3.IH" simp: Let_def)
qed sep_auto+

subsection \<open>Evaluation of a formula\<close>

fun meval_imp :: "nat \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> mformula_h \<Rightarrow> (event_data table list \<times> mformula_h) Heap" where
  "meval_imp j n ts db (mformula.MAnd A \<phi> pos B \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j n ts db \<psi>;
     return (let (zs, buf) = mbuf2_take (\<lambda>r1 r2. bin_join n A r1 pos B r2) (mbuf2_add xs ys buf)
       in (zs, mformula.MAnd A \<phi> pos B \<psi> buf)) }"
| "meval_imp j n ts db (mformula.MAndAssign \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (map (\<lambda>r. eval_assignment conf ` r) xs, mformula.MAndAssign \<phi> conf) }"
| "meval_imp j n ts db (mformula.MAndRel \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (map (\<lambda>r. Set.filter (eval_constraint conf) r) xs, mformula.MAndRel \<phi> conf) }"
| "meval_imp j n ts db (mformula.MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = do {
     (as, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (xs, \<phi>') \<leftarrow> meval_imp j n ts db \<phi>';
     (ys, \<psi>') \<leftarrow> meval_imp j n ts db \<psi>';
     return (let ((zs_trigger, aux), buf2, nts) = mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
         let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
         in (zs @ [(fv_z, z)], aux)) ([], aux) (mbuf2_add xs ys buf2) (nts @ ts);
       (zs, buf1) = mbuf2_take (\<lambda>r1 (V_trigger, r2). bin_join n V r1 True V_trigger r2) (mbuf2_add as zs_trigger buf1)
       in (zs, mformula.MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux)) }"
| "meval_imp j n ts db (mformula.MOr \<phi> \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j n ts db \<psi>;
     return (let (zs, buf) = mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add xs ys buf)
       in (zs, mformula.MOr \<phi> \<psi> buf)) }"
| "meval_imp j n ts db (mformula.MNeg \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (map (\<lambda>r. if r = empty_table then unit_table n else empty_table) xs, mformula.MNeg \<phi>) }"
| "meval_imp j n ts db (mformula.MExists \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (Suc n) ts db \<phi>;
     return (map (\<lambda>r. tl ` r) xs, mformula.MExists \<phi>) }"
| "meval_imp j n ts db (mformula.MAgg args \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (length (aggargs_tys args) + n) ts db \<phi>;
     return (map (eval_aggargs args) xs, mformula.MAgg args \<phi>) }"
| "meval_imp j n ts db (mformula.MPrev I \<phi> first buf nts) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (if first \<and> ts = [] then ([], mformula.MPrev I \<phi> True (buf @ xs) (nts @ ts))
       else let (zs, buf, nts) = mprev_next I (buf @ xs) (nts @ ts)
         in (if first then empty_table # zs else zs, mformula.MPrev I \<phi> False buf nts)) }"
| "meval_imp j n ts db (mformula.MNext I \<phi> first nts) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (let (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
       (zs, buf, nts) = mprev_next I xs (nts @ ts)
       in (zs, mformula.MNext I \<phi> first nts)) }"
| "meval_imp j n ts db (mformula.MSince args \<phi> \<psi> buf aux) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (args_n args) ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j (args_n args) ts db \<psi>;
     (zs, buf, aux) \<leftarrow> eval_since_imp args [] (mbuf2S_add xs ys ts buf) aux;
     return (zs, mformula.MSince args \<phi> \<psi> buf aux) }"
| "meval_imp j n ts db (mformula.MUntil args \<phi> \<psi> buf nts t aux) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (args_n args) ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j (args_n args) ts db \<psi>;
     return (let (aux, buf, nt, nts') = mbuf2t_take (add_new_muaux_dq args) aux (mbuf2_add xs ys buf) t (nts @ ts);
       (zs, aux) = eval_muaux_dq args nt aux
       in (zs, mformula.MUntil args \<phi> \<psi> buf nts' nt aux)) }"
| "meval_imp j n ts db (mformula.MTrigger args \<phi> \<psi> buf nts aux) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j n ts db \<psi>;
     return (let ((zs, aux), buf, nts) = mbuf2T_take (\<lambda>r1 r2 t (zs, aux).
         let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
         in (zs @ [z], aux)) ([], aux) (mbuf2_add xs ys buf) (nts @ ts)
       in (zs, mformula.MTrigger args \<phi> \<psi> buf nts aux)) }"
| "meval_imp j n ts db \<phi>i = return (let (xs, \<phi>) = meval j n ts db (purify \<phi>i) in (xs, embed \<phi>))"

lemma meval_imp_rule:
  "<is_mformula \<phi> \<phi>i> meval_imp j n ts db \<phi>i
   <\<lambda>r. \<up>(fst r = fst (meval j n ts db \<phi>)) * is_mformula (snd (meval j n ts db \<phi>)) (snd r)>\<^sub>t"
proof (induction \<phi> arbitrary: \<phi>i n ts db)
  case (MRel x1)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MPred x1 x2 x3)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MLet x1 x2 x3 x4)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MFrz x1 x2 x3 x4 x5 x6 x7 x8)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MLetPast x1 x2 x3 x4 x5 x6)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MAnd x1 x2 x3 x4 x5 x6)
  show ?case by (cases \<phi>i) (sep_auto heap: MAnd.IH simp: split_beta)+
next
  case (MAndAssign x1 x2)
  show ?case by (cases \<phi>i) (sep_auto heap: MAndAssign.IH simp: split_beta)+
next
  case (MAndRel x1 x2)
  show ?case by (cases \<phi>i) (sep_auto heap: MAndRel.IH simp: split_beta)+
next
  case (MAndTrigger x1 x2 x3 x4 x5 x6 x7 x8 x9)
  show ?case by (cases \<phi>i) (sep_auto heap: MAndTrigger.IH simp: split_beta)+
next
  case (MAnds x1 x2 x3 x4)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MOr x1 x2 x3)
  show ?case by (cases \<phi>i) (sep_auto heap: MOr.IH simp: split_beta)+
next
  case (MNeg x1)
  show ?case by (cases \<phi>i) (sep_auto heap: MNeg.IH simp: split_beta)+
next
  case (MExists x1)
  show ?case by (cases \<phi>i) (sep_auto heap: MExists.IH simp: split_beta)+
next
  case (MAgg x1 x2)
  show ?case by (cases \<phi>i) (sep_auto heap: MAgg.IH simp: split_beta)+
next
  case (MPrev x1 x2 x3 x4 x5)
  show ?case by (cases \<phi>i) (sep_auto heap: MPrev.IH simp: split_beta)+
next
  case (MNext x1 x2 x3 x4)
  show ?case by (cases \<phi>i) (sep_auto heap: MNext.IH simp: split_beta)+
next
  case (MSince x1 x2 x3 x4 x5)
  show ?case by (cases \<phi>i) (sep_auto heap: MSince.IH eval_since_imp_rule simp: split_beta)+
next
  case (MUntil x1 x2 x3 x4 x5 x6 x7)
  show ?case by (cases \<phi>i) (sep_auto heap: MUntil.IH simp: split_beta)+
next
  case (MTrigger x1 x2 x3 x4 x5 x6)
  show ?case by (cases \<phi>i) (sep_auto heap: MTrigger.IH simp: split_beta)+
next
  case (MMatchP x1 x2 x3 x4 x5 x6 x7)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MMatchF x1 x2 x3 x4 x5 x6 x7 x8)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MTP x1 x2)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
next
  case (MTS x1)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meval_simps)
qed

subsection \<open>Building the initial formula on the heap\<close>

fun reset :: "mformula_p \<Rightarrow> mformula_p" where
  "reset (mformula.MAnd A \<phi> pos B \<psi> buf) = mformula.MAnd A (reset \<phi>) pos B (reset \<psi>) buf"
| "reset (mformula.MAndAssign \<phi> conf) = mformula.MAndAssign (reset \<phi>) conf"
| "reset (mformula.MAndRel \<phi> conf) = mformula.MAndRel (reset \<phi>) conf"
| "reset (mformula.MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
    mformula.MAndTrigger V (reset \<phi>) buf1 args (reset \<phi>') (reset \<psi>') buf2 nts aux"
| "reset (mformula.MOr \<phi> \<psi> buf) = mformula.MOr (reset \<phi>) (reset \<psi>) buf"
| "reset (mformula.MNeg \<phi>) = mformula.MNeg (reset \<phi>)"
| "reset (mformula.MExists \<phi>) = mformula.MExists (reset \<phi>)"
| "reset (mformula.MAgg args \<phi>) = mformula.MAgg args (reset \<phi>)"
| "reset (mformula.MPrev I \<phi> first buf nts) = mformula.MPrev I (reset \<phi>) first buf nts"
| "reset (mformula.MNext I \<phi> first nts) = mformula.MNext I (reset \<phi>) first nts"
| "reset (mformula.MSince args \<phi> \<psi> buf aux) = mformula.MSince args (reset \<phi>) (reset \<psi>) buf (init_mmasaux args)"
| "reset (mformula.MUntil args \<phi> \<psi> buf nts t aux) = mformula.MUntil args (reset \<phi>) (reset \<psi>) buf nts t aux"
| "reset (mformula.MTrigger args \<phi> \<psi> buf nts aux) = mformula.MTrigger args (reset \<phi>) (reset \<psi>) buf nts aux"
| "reset \<phi> = \<phi>"

fun mformula_imp :: "mformula_p \<Rightarrow> mformula_h Heap" where
  "mformula_imp (mformula.MAnd A \<phi> pos B \<psi> buf) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (mformula.MAnd A \<phi>i pos B \<psi>i buf) }"
| "mformula_imp (mformula.MAndAssign \<phi> conf) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (mformula.MAndAssign \<phi>i conf) }"
| "mformula_imp (mformula.MAndRel \<phi> conf) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (mformula.MAndRel \<phi>i conf) }"
| "mformula_imp (mformula.MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<phi>i' \<leftarrow> mformula_imp \<phi>'; \<psi>i' \<leftarrow> mformula_imp \<psi>';
     return (mformula.MAndTrigger V \<phi>i buf1 args \<phi>i' \<psi>i' buf2 nts aux) }"
| "mformula_imp (mformula.MOr \<phi> \<psi> buf) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (mformula.MOr \<phi>i \<psi>i buf) }"
| "mformula_imp (mformula.MNeg \<phi>) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (mformula.MNeg \<phi>i) }"
| "mformula_imp (mformula.MExists \<phi>) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (mformula.MExists \<phi>i) }"
| "mformula_imp (mformula.MAgg args \<phi>) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (mformula.MAgg args \<phi>i) }"
| "mformula_imp (mformula.MPrev I \<phi> first buf nts) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (mformula.MPrev I \<phi>i first buf nts) }"
| "mformula_imp (mformula.MNext I \<phi> first nts) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (mformula.MNext I \<phi>i first nts) }"
| "mformula_imp (mformula.MSince args \<phi> \<psi> buf aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; q \<leftarrow> init_h args;
     return (mformula.MSince args \<phi>i \<psi>i buf q) }"
| "mformula_imp (mformula.MUntil args \<phi> \<psi> buf nts t aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (mformula.MUntil args \<phi>i \<psi>i buf nts t aux) }"
| "mformula_imp (mformula.MTrigger args \<phi> \<psi> buf nts aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (mformula.MTrigger args \<phi>i \<psi>i buf nts aux) }"
| "mformula_imp \<phi> = return (embed \<phi>)"

lemma mformula_imp_rule: "<emp> mformula_imp \<phi> <is_mformula (reset \<phi>)>\<^sub>t"
proof (induction \<phi>)
  case (MRel x1)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MPred x1 x2 x3)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MLet x1 x2 x3 x4)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MFrz x1 x2 x3 x4 x5 x6 x7 x8)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MLetPast x1 x2 x3 x4 x5 x6)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MAnd x1 x2 x3 x4 x5 x6)
  show ?case by (sep_auto heap: MAnd.IH)
next
  case (MAndAssign x1 x2)
  show ?case by (sep_auto heap: MAndAssign.IH)
next
  case (MAndRel x1 x2)
  show ?case by (sep_auto heap: MAndRel.IH)
next
  case (MAndTrigger x1 x2 x3 x4 x5 x6 x7 x8 x9)
  show ?case by (sep_auto heap: MAndTrigger.IH)
next
  case (MAnds x1 x2 x3 x4)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MOr x1 x2 x3)
  show ?case by (sep_auto heap: MOr.IH)
next
  case (MNeg x1)
  show ?case by (sep_auto heap: MNeg.IH)
next
  case (MExists x1)
  show ?case by (sep_auto heap: MExists.IH)
next
  case (MAgg x1 x2)
  show ?case by (sep_auto heap: MAgg.IH)
next
  case (MPrev x1 x2 x3 x4 x5)
  show ?case by (sep_auto heap: MPrev.IH)
next
  case (MNext x1 x2 x3 x4)
  show ?case by (sep_auto heap: MNext.IH)
next
  case (MSince x1 x2 x3 x4 x5)
  show ?case by (sep_auto heap: MSince.IH init_h_rule)
next
  case (MUntil x1 x2 x3 x4 x5 x6 x7)
  show ?case by (sep_auto heap: MUntil.IH)
next
  case (MTrigger x1 x2 x3 x4 x5 x6)
  show ?case by (sep_auto heap: MTrigger.IH)
next
  case (MMatchP x1 x2 x3 x4 x5 x6 x7)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MMatchF x1 x2 x3 x4 x5 x6 x7 x8)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MTP x1 x2)
  show ?case by (sep_auto simp: is_mformula_embed)
next
  case (MTS x1)
  show ?case by (sep_auto simp: is_mformula_embed)
qed

subsection \<open>The monitor\<close>

definition is_mstate :: "mstate_p \<Rightarrow> mstate_h \<Rightarrow> assn" where
  "is_mstate st sti = \<up>(mstate_i sti = mstate_i st \<and> mstate_j sti = mstate_j st \<and>
     mstate_n sti = mstate_n st \<and> mstate_t sti = mstate_t st) * is_mformula (mstate_m st) (mstate_m sti)"

definition mstep_imp :: "database \<times> ts \<Rightarrow> mstate_h \<Rightarrow> ((nat \<times> ts \<times> event_data table) list \<times> mstate_h) Heap" where
  "mstep_imp tdb st = do {
     (xs, m) \<leftarrow> meval_imp (mstate_j st + 1) (mstate_n st) [snd tdb] (fst tdb) (mstate_m st);
     return (List.enumerate (mstate_i st) (zip (mstate_t st @ [snd tdb]) xs),
       \<lparr> mstate_i = mstate_i st + length xs, mstate_j = mstate_j st + 1, mstate_m = m,
         mstate_n = mstate_n st, mstate_t = drop (length xs) (mstate_t st @ [snd tdb]) \<rparr>) }"

lemma mstep_imp_rule:
  "<is_mstate st sti> mstep_imp tdb sti
   <\<lambda>r. \<up>(fst r = fst (mstep tdb st)) * is_mstate (snd (mstep tdb st)) (snd r)>\<^sub>t"
  unfolding mstep_imp_def default_maux.mstep_def is_mstate_def
  by (sep_auto heap: meval_imp_rule simp: split_beta)

definition minit_safe_imp :: "ty Formula.formula \<Rightarrow> mstate_h Heap" where
  "minit_safe_imp \<phi> = do {
     m \<leftarrow> mformula_imp (mstate_m (minit_safe \<phi>));
     return \<lparr> mstate_i = mstate_i (minit_safe \<phi>), mstate_j = mstate_j (minit_safe \<phi>), mstate_m = m,
       mstate_n = mstate_n (minit_safe \<phi>), mstate_t = mstate_t (minit_safe \<phi>) \<rparr> }"

lemma minit_safe_imp_rule:
  assumes "reset (mstate_m (minit_safe \<phi>)) = mstate_m (minit_safe \<phi>)"
  shows "<emp> minit_safe_imp \<phi> <is_mstate (minit_safe \<phi>)>\<^sub>t"
  unfolding minit_safe_imp_def is_mstate_def
  by (sep_auto heap: mformula_imp_rule simp: assms)

lemmas init_defs = default_mmasaux.init_since_def dq_muaux.init_until_def
  verimon_maux.init_and_trigger_def verimon_maux.init_trigger_def

lemma reset_minit0: "reset (minit0 n \<phi>) = minit0 n \<phi>"
  apply (induction n \<phi> rule: default_maux.minit0.induct)
  apply (simp_all add: init_defs Let_def)
  apply (simp_all add: init_defs Let_def split: formula.split del: default_maux.minit0.simps)
  apply (auto simp: init_defs Let_def split: formula.split prod.split
      simp del: default_maux.minit0.simps)
  done

lemma reset_minit_safe:
  assumes "mmonitorable_exec \<phi>"
  shows "reset (mstate_m (minit_safe \<phi>)) = mstate_m (minit_safe \<phi>)"
  using assms by (simp add: default_maux.minit_safe_def default_maux.minit_def Let_def reset_minit0)

lemma minit_safe_imp_rule':
  assumes "mmonitorable_exec \<phi>"
  shows "<emp> minit_safe_imp \<phi> <is_mstate (minit_safe \<phi>)>\<^sub>t"
  by (rule minit_safe_imp_rule[OF reset_minit_safe[OF assms]])

subsection \<open>Running a whole prefix in one heap computation\<close>

text \<open>
  The composition of the steps is a single heap computation, whose result is a pure value: the
  verdicts of the pure monitor. The streaming front end performs the same composition, one step
  per call.
\<close>

primrec msteps0_imp :: "((Formula.name \<times> event_data list) set \<times> ts) list \<Rightarrow> mstate_h \<Rightarrow>
    ((nat \<times> ts \<times> event_data table) list \<times> mstate_h) Heap" where
  "msteps0_imp [] st = return ([], st)"
| "msteps0_imp (tdb # \<pi>) st = do {
     (V', st') \<leftarrow> mstep_imp (apfst mk_db tdb) st;
     (V'', st'') \<leftarrow> msteps0_imp \<pi> st';
     return (V' @ V'', st'') }"

lemma msteps0_imp_rule:
  "<is_mstate st sti> msteps0_imp \<pi> sti
   <\<lambda>r. \<up>(fst r = fst (default_maux.msteps0 \<pi> st)) * is_mstate (snd (default_maux.msteps0 \<pi> st)) (snd r)>\<^sub>t"
proof (induction \<pi> arbitrary: st sti)
  case Nil
  show ?case by sep_auto
next
  case (Cons tdb \<pi>)
  show ?case by (sep_auto heap: mstep_imp_rule Cons.IH simp: split_beta)
qed

definition monitor_imp :: "ty Formula.formula \<Rightarrow> ((Formula.name \<times> event_data list) set \<times> ts) list \<Rightarrow>
    (nat \<times> ts \<times> event_data table) list Heap" where
  "monitor_imp \<phi> \<pi> = do { st \<leftarrow> minit_safe_imp \<phi>; r \<leftarrow> msteps0_imp \<pi> st; return (fst r) }"

lemma monitor_imp_rule:
  assumes "mmonitorable_exec \<phi>"
  shows "<emp> monitor_imp \<phi> \<pi> <\<lambda>r. \<up>(r = msteps0_stateless \<pi> (minit_safe \<phi>))>\<^sub>t"
  unfolding monitor_imp_def
  by (sep_auto heap: minit_safe_imp_rule'[OF assms] msteps0_imp_rule
      simp: default_maux.msteps0_msteps0_stateless[symmetric])

theorem run_monitor_imp:
  assumes "mmonitorable_exec \<phi>"
  shows "run (monitor_imp \<phi> \<pi>) = msteps0_stateless \<pi> (minit_safe \<phi>)"
  by (rule run_hoare[OF monitor_imp_rule[OF assms]])

(*<*)
end
(*>*)
