(*<*)
theory Monitor_Imp
  imports Optimized_Since_Imp
begin
(*>*)

section \<open>A monitor with heap-resident Since structures\<close>

text \<open>
  The auxiliary structures are threaded through the evaluation function as pure values, so a
  heap-resident structure forces that function to be monadic. We clone @{const meeval}, the
  evaluation function used by the generated code, in the heap monad for the fragment of
  formulas in which a Since operator can profit from the imperative structure of
  @{theory MFODL_Monitor_Imp.Optimized_Since_Imp}: the Boolean connectives, assignments and
  constraints, quantification, aggregation, the temporal operators and Since itself. Under the
  remaining constructors (@{text LET}, @{text LETPAST}, @{text FRZ}, @{text ANDS}, the regular
  expression operators), whose evaluation calls the evaluation of their subformulas in loops,
  the subformulas keep the pure structure and are evaluated by the pure @{const meeval}; this
  costs nothing but the acceleration. Since the fragment is closed under the operators a
  monitored formula is usually built from, the Since operators of a typical formula are all in
  it.
\<close>

type_synonym mformula_p = "(mmasaux, muaux_dq, event_data mmtaux) meformula"
type_synonym mformula_h = "(msaux_h, muaux_dq, event_data mmtaux) meformula"
type_synonym mstate_p = "(mmasaux, muaux_dq, event_data mmtaux) mstate"
type_synonym mstate_h = "nat \<times> nat \<times> mformula_h \<times> nat \<times> ts queue"

subsection \<open>Formulas with pure structures, and back\<close>

fun embed :: "mformula_p \<Rightarrow> mformula_h" where
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
| "embed (MSince args \<phi> \<psi> buf aux) = MSince args (embed \<phi>) (embed \<psi>) buf (MSH_pure aux)"
| "embed (MUntil args \<phi> \<psi> buf nts t aux) = MUntil args (embed \<phi>) (embed \<psi>) buf nts t aux"
| "embed (MTrigger args \<phi> \<psi> buf nts aux) = MTrigger args (embed \<phi>) (embed \<psi>) buf nts aux"
| "embed (MMatchP I mr mrs \<phi>s buf nts aux) = MMatchP I mr mrs (map embed \<phi>s) buf nts aux"
| "embed (MMatchF I mr mrs \<phi>s buf nts t aux) = MMatchF I mr mrs (map embed \<phi>s) buf nts t aux"
| "embed (MTP mt i) = MTP mt i"
| "embed (MTS mt) = MTS mt"

fun purify :: "mformula_h \<Rightarrow> mformula_p" where
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
| "purify (MSince args \<phi> \<psi> buf (MSH_pure s)) = MSince args (purify \<phi>) (purify \<psi>) buf s"
| "purify (MSince args \<phi> \<psi> buf (MSH_imp q)) = MSince args (purify \<phi>) (purify \<psi>) buf (init_mmasaux args)"
| "purify (MUntil args \<phi> \<psi> buf nts t aux) = MUntil args (purify \<phi>) (purify \<psi>) buf nts t aux"
| "purify (MTrigger args \<phi> \<psi> buf nts aux) = MTrigger args (purify \<phi>) (purify \<psi>) buf nts aux"
| "purify (MMatchP I mr mrs \<phi>s buf nts aux) = MMatchP I mr mrs (map purify \<phi>s) buf nts aux"
| "purify (MMatchF I mr mrs \<phi>s buf nts t aux) = MMatchF I mr mrs (map purify \<phi>s) buf nts t aux"
| "purify (MTP mt i) = MTP mt i"
| "purify (MTS mt) = MTS mt"

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
  "is_mformula (MAnd A \<phi> pos B \<psi> buf) \<chi> =
    (case \<chi> of MAnd A' \<phi>i pos' B' \<psi>i buf' \<Rightarrow>
      \<up>(A' = A \<and> pos' = pos \<and> B' = B \<and> buf' = buf) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i | _ \<Rightarrow> false)"
| "is_mformula (MAndAssign \<phi> conf) \<chi> =
    (case \<chi> of MAndAssign \<phi>i conf' \<Rightarrow> \<up>(conf' = conf) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (MAndRel \<phi> conf) \<chi> =
    (case \<chi> of MAndRel \<phi>i conf' \<Rightarrow> \<up>(conf' = conf) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) \<chi> =
    (case \<chi> of MAndTrigger V' \<phi>i buf1' args' \<phi>i' \<psi>i' buf2' nts' aux' \<Rightarrow>
      \<up>(V' = V \<and> buf1' = buf1 \<and> args' = args \<and> buf2' = buf2 \<and> nts' = nts \<and> aux' = aux) *
      is_mformula \<phi> \<phi>i * is_mformula \<phi>' \<phi>i' * is_mformula \<psi>' \<psi>i' | _ \<Rightarrow> false)"
| "is_mformula (MOr \<phi> \<psi> buf) \<chi> =
    (case \<chi> of MOr \<phi>i \<psi>i buf' \<Rightarrow> \<up>(buf' = buf) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i | _ \<Rightarrow> false)"
| "is_mformula (MNeg \<phi>) \<chi> = (case \<chi> of MNeg \<phi>i \<Rightarrow> is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (MExists \<phi>) \<chi> = (case \<chi> of MExists \<phi>i \<Rightarrow> is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (MAgg args \<phi>) \<chi> =
    (case \<chi> of MAgg args' \<phi>i \<Rightarrow> \<up>(args' = args) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (MPrev I \<phi> first buf nts) \<chi> =
    (case \<chi> of MPrev I' \<phi>i first' buf' nts' \<Rightarrow>
      \<up>(I' = I \<and> first' = first \<and> buf' = buf \<and> nts' = nts) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (MNext I \<phi> first nts) \<chi> =
    (case \<chi> of MNext I' \<phi>i first' nts' \<Rightarrow>
      \<up>(I' = I \<and> first' = first \<and> nts' = nts) * is_mformula \<phi> \<phi>i | _ \<Rightarrow> false)"
| "is_mformula (MSince args \<phi> \<psi> buf aux) \<chi> =
    (case \<chi> of MSince args' \<phi>i \<psi>i buf' auxi \<Rightarrow>
      \<up>(args' = args \<and> buf' = buf) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i * is_msaux_h args aux auxi | _ \<Rightarrow> false)"
| "is_mformula (MUntil args \<phi> \<psi> buf nts t aux) \<chi> =
    (case \<chi> of MUntil args' \<phi>i \<psi>i buf' nts' t' aux' \<Rightarrow>
      \<up>(args' = args \<and> buf' = buf \<and> nts' = nts \<and> t' = t \<and> aux' = aux) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i
    | _ \<Rightarrow> false)"
| "is_mformula (MTrigger args \<phi> \<psi> buf nts aux) \<chi> =
    (case \<chi> of MTrigger args' \<phi>i \<psi>i buf' nts' aux' \<Rightarrow>
      \<up>(args' = args \<and> buf' = buf \<and> nts' = nts \<and> aux' = aux) * is_mformula \<phi> \<phi>i * is_mformula \<psi> \<psi>i | _ \<Rightarrow> false)"
| "is_mformula \<phi> \<chi> = \<up>(\<chi> = embed \<phi>)"

lemma is_mformula_embed: "is_mformula \<phi> (embed \<phi>) = emp"
  by (induction \<phi>) simp_all

subsection \<open>Evaluation of the Since buffer\<close>

fun eval_since_imp :: "args \<Rightarrow> event_data table list \<Rightarrow> event_data mebuf2S \<Rightarrow> msaux_h \<Rightarrow>
    (event_data table list \<times> event_data mebuf2S \<times> msaux_h) Heap" where
  "eval_since_imp args rs (xs, ys, ts, skew) aux =
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow>
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          (if skew \<or> memL (args_ivl args) 0
           then return (rev rs, (x ## xs', mbuf_t_empty, t ## ts', skew), aux)
           else do { aux \<leftarrow> add_new_ts_h args t aux; aux' \<leftarrow> join_h args x aux; r \<leftarrow> result_h args aux';
                     return (rev (r # rs), (xs', mbuf_t_empty, ts', True), aux') })
        | (None, ts') \<Rightarrow> return (rev rs, (x ## xs', mbuf_t_empty, mbuf_t_empty, skew), aux))
      | (None, xs') \<Rightarrow> return (rev rs, (mbuf_t_empty, mbuf_t_empty, ts, skew), aux))
    | (Some y, ys') \<Rightarrow>
      if skew then do { aux \<leftarrow> add_new_table_h args y aux; eval_since_imp args rs (xs, ys', ts, False) aux }
      else
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          do { aux \<leftarrow> add_new_ts_h args t aux; aux \<leftarrow> join_h args x aux; aux' \<leftarrow> add_new_table_h args y aux;
               r \<leftarrow> result_h args aux'; eval_since_imp args (r # rs) (xs', ys', ts', False) aux' }
        | (None, ts') \<Rightarrow> return (rev rs, (x ## xs', y ## ys', ts', skew), aux))
      | (None, xs') \<Rightarrow> return (rev rs, (mbuf_t_empty, y ## ys', ts, skew), aux)))"

lemma eval_since_imp_rule:
  "<is_msaux_h args s q> eval_since_imp args rs buf q
   <\<lambda>r. \<up>(fst r = fst (eeval_since args rs buf s) \<and> fst (snd r) = fst (snd (eeval_since args rs buf s))) *
      is_msaux_h args (snd (snd (eeval_since args rs buf s))) (snd (snd r))>\<^sub>t"
proof (induction rs buf s arbitrary: q rule: default_maux.eeval_since.induct[where args = args])
  case (1 rs xs ys ts skew aux)
  show ?case
    by (sep_auto heap: add_new_ts_h_rule join_h_rule result_h_rule add_new_table_h_rule "1.IH"
        simp: Let_def split: option.splits prod.splits)
qed

subsection \<open>Evaluation of a formula\<close>

fun meval_imp :: "nat \<Rightarrow> nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> mformula_h \<Rightarrow> (event_data table list \<times> mformula_h) Heap" where
  "meval_imp j n ts db (MAnd A \<phi> pos B \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j n ts db \<psi>;
     return (let (zs, buf) = mebuf2_take (\<lambda>r1 r2. bin_join n A r1 pos B r2) (mebuf2_add xs ys buf)
       in (zs, MAnd A \<phi> pos B \<psi> buf)) }"
| "meval_imp j n ts db (MAndAssign \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (map (\<lambda>r. eval_assignment conf ` r) xs, MAndAssign \<phi> conf) }"
| "meval_imp j n ts db (MAndRel \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (map (Set.filter (eval_constraint conf)) xs, MAndRel \<phi> conf) }"
| "meval_imp j n ts db (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = do {
     (as, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (xs, \<phi>') \<leftarrow> meval_imp j n ts db \<phi>';
     (ys, \<psi>') \<leftarrow> meval_imp j n ts db \<psi>';
     return (let ((zs_trigger, aux), buf2, nts) = mebuf2T_take (\<lambda>r1 r2 t (zs, aux).
         let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
         in (zs @ [(fv_z, z)], aux)) ([], aux) (mebuf2_add xs ys buf2) (nts @@ ts);
       (zs, buf1) = mebuf2_take (\<lambda>r1 (V_trigger, r2). bin_join n V r1 True V_trigger r2) (mebuf2_add as zs_trigger buf1)
       in (zs, MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux)) }"
| "meval_imp j n ts db (MOr \<phi> \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j n ts db \<psi>;
     return (let (zs, buf) = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
       in (zs, MOr \<phi> \<psi> buf)) }"
| "meval_imp j n ts db (MNeg \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (map (\<lambda>r. if r = empty_table then unit_table n else empty_table) xs, MNeg \<phi>) }"
| "meval_imp j n ts db (MExists \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (Suc n) ts db \<phi>;
     return (map (\<lambda>r. tl ` r) xs, MExists \<phi>) }"
| "meval_imp j n ts db (MAgg args \<phi>) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (length (aggargs_tys args) + n) ts db \<phi>;
     return (map (eval_aggargs args) xs, MAgg args \<phi>) }"
| "meval_imp j n ts db (MPrev I \<phi> first buf nts) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (if first \<and> ts = [] then ([], MPrev I \<phi> True (buf @@ xs) (nts @@ ts))
       else let (zs, buf, nts) = meprev_next I (buf @@ xs) (nts @@ ts)
         in (if first then empty_table # zs else zs, MPrev I \<phi> False buf nts)) }"
| "meval_imp j n ts db (MNext I \<phi> first nts) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     return (let (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
       (zs, buf, nts) = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
       in (zs, MNext I \<phi> first nts)) }"
| "meval_imp j n ts db (MSince args \<phi> \<psi> buf aux) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (args_n args) ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j (args_n args) ts db \<psi>;
     (zs, buf, aux) \<leftarrow> eval_since_imp args [] (mebuf2S_add xs ys ts buf) aux;
     return (zs, MSince args \<phi> \<psi> buf aux) }"
| "meval_imp j n ts db (MUntil args \<phi> \<psi> buf nts t aux) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j (args_n args) ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j (args_n args) ts db \<psi>;
     return (let (aux, buf, nt, nts') = mebuf2t_take (add_new_muaux_dq args) aux (mebuf2_add xs ys buf) t (nts @@ ts);
       (zs, aux) = eval_muaux_dq args nt aux
       in (zs, MUntil args \<phi> \<psi> buf nts' nt aux)) }"
| "meval_imp j n ts db (MTrigger args \<phi> \<psi> buf nts aux) = do {
     (xs, \<phi>) \<leftarrow> meval_imp j n ts db \<phi>;
     (ys, \<psi>) \<leftarrow> meval_imp j n ts db \<psi>;
     return (let ((zs, aux), buf, nts) = mebuf2T_take (\<lambda>r1 r2 t (zs, aux).
         let aux = update_mmtaux args t r1 r2 aux; (fv_z, z) = result_mmtaux args aux
         in (zs @ [z], aux)) ([], aux) (mebuf2_add xs ys buf) (nts @@ ts)
       in (zs, MTrigger args \<phi> \<psi> buf nts aux)) }"
| "meval_imp j n ts db \<phi>i = return (let (xs, \<phi>) = meeval j n ts db (purify \<phi>i) in (xs, embed \<phi>))"

lemma meval_imp_rule:
  "<is_mformula \<phi> \<phi>i> meval_imp j n ts db \<phi>i
   <\<lambda>r. \<up>(fst r = fst (meeval j n ts db \<phi>)) * is_mformula (snd (meeval j n ts db \<phi>)) (snd r)>\<^sub>t"
proof (induction \<phi> arbitrary: \<phi>i n ts db)
  case (MRel x1)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
next
  case (MPred x1 x2 x3)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
next
  case (MLet x1 x2 x3 x4)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
next
  case (MFrz x1 x2 x3 x4 x5 x6 x7 x8)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
next
  case (MLetPast x1 x2 x3 x4 x5 x6)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
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
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
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
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
next
  case (MMatchF x1 x2 x3 x4 x5 x6 x7 x8)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
next
  case (MTP x1 x2)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
next
  case (MTS x1)
  show ?case by (sep_auto simp: is_mformula_embed split_beta simp del: default_maux.meeval.simps)
qed

subsection \<open>Building the initial formula on the heap\<close>

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

fun mformula_imp :: "mformula_p \<Rightarrow> mformula_h Heap" where
  "mformula_imp (MAnd A \<phi> pos B \<psi> buf) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (MAnd A \<phi>i pos B \<psi>i buf) }"
| "mformula_imp (MAndAssign \<phi> conf) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (MAndAssign \<phi>i conf) }"
| "mformula_imp (MAndRel \<phi> conf) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (MAndRel \<phi>i conf) }"
| "mformula_imp (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<phi>i' \<leftarrow> mformula_imp \<phi>'; \<psi>i' \<leftarrow> mformula_imp \<psi>';
     return (MAndTrigger V \<phi>i buf1 args \<phi>i' \<psi>i' buf2 nts aux) }"
| "mformula_imp (MOr \<phi> \<psi> buf) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (MOr \<phi>i \<psi>i buf) }"
| "mformula_imp (MNeg \<phi>) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (MNeg \<phi>i) }"
| "mformula_imp (MExists \<phi>) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (MExists \<phi>i) }"
| "mformula_imp (MAgg args \<phi>) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (MAgg args \<phi>i) }"
| "mformula_imp (MPrev I \<phi> first buf nts) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (MPrev I \<phi>i first buf nts) }"
| "mformula_imp (MNext I \<phi> first nts) = do { \<phi>i \<leftarrow> mformula_imp \<phi>; return (MNext I \<phi>i first nts) }"
| "mformula_imp (MSince args \<phi> \<psi> buf aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; q \<leftarrow> init_h args;
     return (MSince args \<phi>i \<psi>i buf q) }"
| "mformula_imp (MUntil args \<phi> \<psi> buf nts t aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (MUntil args \<phi>i \<psi>i buf nts t aux) }"
| "mformula_imp (MTrigger args \<phi> \<psi> buf nts aux) = do {
     \<phi>i \<leftarrow> mformula_imp \<phi>; \<psi>i \<leftarrow> mformula_imp \<psi>; return (MTrigger args \<phi>i \<psi>i buf nts aux) }"
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

text \<open>
  The state of the imperative monitor keeps the same data as @{typ mstate_p}, with the formula
  on the heap and the time stamps in a queue, as the code representation @{const mestate} of the
  pure state does.
\<close>

definition is_mstate :: "mstate_p \<Rightarrow> mstate_h \<Rightarrow> assn" where
  "is_mstate st sti = (case sti of (i, j, m, n, tq) \<Rightarrow>
     (\<exists>\<^sub>Ae. \<up>(i = mstate_i st \<and> j = mstate_j st \<and> n = mstate_n st \<and>
        linearize tq = mstate_t st \<and> mstate_m st = Rep_meformula e) * is_mformula e m))"

definition mstep_imp :: "database \<times> ts \<Rightarrow> mstate_h \<Rightarrow> ((nat \<times> ts \<times> event_data table) list \<times> mstate_h) Heap" where
  "mstep_imp tdb sti = (case sti of (i, j, m, n, tq) \<Rightarrow> do {
     (vs, m') \<leftarrow> meval_imp (j + 1) n [snd tdb] (fst tdb) m;
     return (let tq' = append_queue (snd tdb) tq in
       (List.enumerate i (zip (linearize tq') vs),
        (i + length vs, j + 1, m', n, (tl_queue ^^ length vs) tq'))) })"

lemma linearize_funpow_tl: "linearize ((tl_queue ^^ k) q) = drop k (linearize q)"
  by (induction k) (auto simp: tl_queue_rep drop_Suc tl_drop)

lemma mstep_imp_rule:
  "<is_mstate st sti> mstep_imp tdb sti
   <\<lambda>r. \<up>(fst r = fst (mstep tdb st)) * is_mstate (snd (mstep tdb st)) (snd r)>\<^sub>t"
  unfolding is_mstate_def mstep_imp_def default_maux.mstep_def
  by (sep_auto heap: meval_imp_rule
      simp: default_maux.meval_code linearize_funpow_tl append_queue_rep split_beta)

lemmas init_defs = default_mmasaux.init_since'_def dq_muaux.init_until'_def
  verimon_maux.init_and_trigger'_def verimon_maux.init_trigger'_def

lemma reset_meinit0: "reset (meinit0 n \<phi>) = meinit0 n \<phi>"
  apply (induction n \<phi> rule: default_maux.meinit0.induct)
  apply (simp_all add: init_defs Let_def)
  apply (simp_all add: init_defs Let_def split: formula.split del: default_maux.meinit0.simps)
  apply (auto simp: init_defs Let_def split: formula.split prod.split
      simp del: default_maux.meinit0.simps)
  done

definition minit_safe_imp :: "ty Formula.formula \<Rightarrow> mstate_h Heap" where
  "minit_safe_imp \<phi> = do {
     m \<leftarrow> mformula_imp (meinit0 (Formula.nfv \<phi>) \<phi>);
     return (0, 0, m, Formula.nfv \<phi>, empty_queue) }"

lemma minit_safe_imp_rule:
  assumes "mmonitorable_exec \<phi>"
  shows "<emp> minit_safe_imp \<phi> <is_mstate (minit_safe \<phi>)>\<^sub>t"
  unfolding minit_safe_imp_def is_mstate_def
  using assms
  by (sep_auto heap: mformula_imp_rule
      simp: default_maux.minit_safe_def default_maux.minit_def default_maux.minit0_code
      mestate_def Let_def reset_meinit0 empty_queue_rep)

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
  by (sep_auto heap: minit_safe_imp_rule[OF assms] msteps0_imp_rule
      simp: default_maux.msteps0_msteps0_stateless[symmetric])

theorem run_monitor_imp:
  assumes "mmonitorable_exec \<phi>"
  shows "run (monitor_imp \<phi> \<pi>) = msteps0_stateless \<pi> (minit_safe \<phi>)"
  by (rule run_hoare[OF monitor_imp_rule[OF assms]])

(*<*)
end
(*>*)
