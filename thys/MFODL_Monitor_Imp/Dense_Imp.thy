(*<*)
theory Dense_Imp
  imports Monitor_Imp2 Dense_Unbox
begin
(*>*)

section \<open>Tuples without their empty columns\<close>

text \<open>
  The short-tuple representation, its operations and their agreement with the kernel's live in
  @{theory MFODL_Monitor_Imp.Dense}.  What is left here is the part that is not a pure
  refinement: the heap-resident join index, the monadic evaluation function, and the
  compilation of an @{type mformula_j} into the dense fragment.
\<close>

subsection \<open>Indexing a join on the heap\<close>

text \<open>
  The same index as @{theory MFODL_Monitor_Imp.Join_Imp2}, over the short tuples.  Two things
  the sparse version has to worry about go away.  Its guard requires both operands to be
  complete on the common columns, because a tuple with a hole there means ``any value'' and a
  hash index would miss the matches; a short tuple has no holes at all, so the guard is
  vacuous and the index applies wherever the shape is right.  And the key is the projection
  onto the shared columns, which here is as short as the shared columns rather than as long as
  the formula is wide, so it is cheaper both to build and to hash.
\<close>

type_synonym udatabase = "(Formula.name \<times> nat, utable list) mapping"

type_synonym djidx = "(event_data list, event_data list list) imap"

partial_function (heap) didx_ins :: "bool list \<Rightarrow> event_data list list \<Rightarrow> djidx \<Rightarrow>
    djidx Heap" where
  [code]:
  "didx_ins msk xs q = (case xs of [] \<Rightarrow> return q
     | x # r \<Rightarrow> (let k = dproj msk x; h = uihash k in
         do { v \<leftarrow> im_lookup_h ueq q h k;
              q \<leftarrow> im_update_h ueq q h k (case v of None \<Rightarrow> [x] | Some l \<Rightarrow> x # l);
              didx_ins msk r q }))"

text \<open>The index holds the right operand and the left probes it.\<close>

partial_function (heap) dprobe_r :: "mrg list \<Rightarrow> bool list \<Rightarrow> djidx \<Rightarrow>
    event_data list list \<Rightarrow> utable \<Rightarrow> utable Heap" where
  [code]:
  "dprobe_r p lk q xs acc = (case xs of [] \<Rightarrow> return acc
     | x # r \<Rightarrow> (let k = dproj lk x in
         do { v \<leftarrow> im_lookup_h ueq q (uihash k) k;
              dprobe_r p lk q r (case v of None \<Rightarrow> acc
                | Some l \<Rightarrow> fold (\<lambda>y acc. Set.insert (dmerge p x y) acc) l acc) }))"

text \<open>The index holds the left operand and the right probes it; the merge keeps its sides.\<close>

partial_function (heap) dprobe_l :: "mrg list \<Rightarrow> bool list \<Rightarrow> djidx \<Rightarrow>
    event_data list list \<Rightarrow> utable \<Rightarrow> utable Heap" where
  [code]:
  "dprobe_l p rk q ys acc = (case ys of [] \<Rightarrow> return acc
     | y # r \<Rightarrow> (let k = dproj rk y in
         do { v \<leftarrow> im_lookup_h ueq q (uihash k) k;
              dprobe_l p rk q r (case v of None \<Rightarrow> acc
                | Some l \<Rightarrow> fold (\<lambda>x acc. Set.insert (dmerge p x y) acc) l acc) }))"

text \<open>As in the sparse code, the smaller side is indexed and the larger probes it, and only the
  case in which neither operand's columns contain the other's is taken away from the tree.\<close>

fun dbin_join_h :: "djoin_plan \<Rightarrow> utable \<Rightarrow> bool \<Rightarrow> utable \<Rightarrow> utable Heap" where
  "dbin_join_h (DJGen p lk rk) A pos B =
     (if \<not> dense_heap_join \<or> \<not> pos \<or> Set.is_empty A \<or> Set.is_empty B
      then return (gbin_join (DJGen p lk rk) A pos B)
      else (let xs = csorted_list_of_set A; ys = csorted_list_of_set B in
        if length ys \<le> length xs
        then (if \<not> heap_join_ok ys then return (gbin_join (DJGen p lk rk) A pos B)
              else do { q \<leftarrow> im_new (2 * integer_of_nat (length ys));
                        q \<leftarrow> didx_ins rk ys q;
                        dprobe_r p lk q xs {} })
        else (if \<not> heap_join_ok xs then return (gbin_join (DJGen p lk rk) A pos B)
              else do { q \<leftarrow> im_new (2 * integer_of_nat (length xs));
                        q \<leftarrow> didx_ins lk xs q;
                        dprobe_l p rk q ys {} })))"
| "dbin_join_h pl A pos B = return (gbin_join pl A pos B)"

subsection \<open>The multi-way conjunction\<close>

text \<open>
  A conjunction of more than two conjuncts -- and in practice nearly every conjunction, see
  @{theory MFODL_Monitor_Imp.Join_Imp2} -- is compiled to @{term MAnds}, so without this case
  the short tuples would never reach a join at all.  The positive conjuncts are joined
  left-deep and the negative ones subtracted afterwards, as in the sparse code; the columns of
  every intermediate result are known at build time, so all the plans are made once.
\<close>

fun dands_pos_h :: "djoin_plan list \<Rightarrow> utable \<Rightarrow> utable list \<Rightarrow> utable Heap" where
  "dands_pos_h [] t us = return t"
| "dands_pos_h (p # ps) t [] = return t"
| "dands_pos_h (p # ps) t (u # us) = do { t \<leftarrow> dbin_join_h p t True u; dands_pos_h ps t us }"

fun dands_neg_h :: "djoin_plan list \<Rightarrow> utable \<Rightarrow> utable list \<Rightarrow> utable Heap" where
  "dands_neg_h [] t us = return t"
| "dands_neg_h (p # ps) t [] = return t"
| "dands_neg_h (p # ps) t (u # us) = do { t \<leftarrow> dbin_join_h p t False u; dands_neg_h ps t us }"

definition dmulti_join :: "djoin_plan list \<Rightarrow> djoin_plan list \<Rightarrow> utable list \<Rightarrow>
    utable Heap" where
  "dmulti_join ps ns us = (case us of [] \<Rightarrow> return {}
     | t # r \<Rightarrow> do { t \<leftarrow> dands_pos_h ps t (take (length ps) r);
                     dands_neg_h ns t (drop (length ps) r) })"

text \<open>The columns of the operand, of the groups, and of the result.\<close>

definition dagg_child_cols :: "aggargs \<Rightarrow> cols" where
  "dagg_child_cols args = set_cols (aggargs_cols args)"

definition dagg_group_cols :: "aggargs \<Rightarrow> cols" where
  "dagg_group_cols args = map (\<lambda>c. c - length (aggargs_tys args))
     (drop (length (aggargs_tys args)) (dagg_child_cols args))"

definition dagg_cols :: "aggargs \<Rightarrow> cols" where
  "dagg_cols args = merge_cols (dagg_group_cols args) [aggargs_y args]"

definition dagg_pos :: "aggargs \<Rightarrow> nat" where
  "dagg_pos args = length (filter (\<lambda>c. c < aggargs_y args) (dagg_group_cols args))"

text \<open>The five numbers the aggregation needs at the dense frame: whether it groups by nothing,
  the operation, the term reindexed to the operand's columns, how many columns the operand has
  in front of the groups, and where the result variable sits among the node's columns.  They are
  what the aggregation node below carries, and what the structure of
  @{theory MFODL_Monitor_Imp.Dense_Unbox} maintains the aggregate by.\<close>

definition dagg_of :: "aggargs \<Rightarrow> daggargs" where
  "dagg_of ag = \<lparr>dgg_g0 = aggargs_g0 ag, dgg_op = aggargs_\<omega> ag,
     dgg_trm = reindex_trm (dagg_child_cols ag) (aggargs_f ag),
     dgg_k = length (aggargs_tys ag), dgg_p = dagg_pos ag\<rparr>"

text \<open>
  An aggregation over a Since or an Until is fused into the temporal operator's own arguments,
  so that its structure can keep the aggregate up to date instead of recomputing it from the
  window at every time point.  The dense operators keep that fusion.  What the compiler does
  take apart is the frame: the structure runs at the operand's columns, so the arguments it is
  given are the operator's with the aggregation removed and narrowed to those columns, and the
  aggregation travels separately, as the five numbers of @{const dagg_of}, to the structure that
  maintains it.  The shape the compiler recognises is the one below: the node produces the
  aggregation's columns, its right operand produces the aggregation's operand's, and the widths
  agree.
\<close>

definition dunfuse :: "args \<Rightarrow> args" where
  "dunfuse args = init_args (args_ivl args) (args_n args) (args_L args) (args_R args)
     (args_pos args) None"

definition dagg_fused :: "nat \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> bool" where
  "dagg_fused n cs args = (case args_agg args of None \<Rightarrow> False | Some ag \<Rightarrow>
     cs = dagg_cols ag \<and> set_cols (args_R args) = dagg_child_cols ag \<and>
     set (set_cols (args_L args)) \<subseteq> set (dagg_child_cols ag) \<and> n = aggargs_n ag \<and>
     args_n args = length (aggargs_tys ag) + aggargs_n ag)"


subsection \<open>Buffers over the short tables\<close>

text \<open>
  The buffer operations of @{theory MFODL_Monitor_Devel.Monitor_Impl} that are stated at
  @{typ "event_data table"} rather than at a table type of their own, in the one form the
  evaluation function below needs.  Only the type changes; @{const empty_table} becomes the
  empty set of the short tables.
\<close>

type_synonym umebuf2 = "utable mbuf_t \<times> utable mbuf_t"

text \<open>One buffer holds tables that may stand for "every valuation": the one between a
  conjunction and the trigger below it, whose window can be empty.  Both sides carry the option
  so that the buffer stays homogeneous and @{const mebuf2_take_j} can be used unchanged; the
  left side is always @{term Some}.\<close>

type_synonym umebuf2O = "utable option mbuf_t \<times> utable option mbuf_t"

type_synonym umebufn = "utable mbuf_t list"

type_synonym umebuf2S = "utable mbuf_t \<times> utable mbuf_t \<times> ts mbuf_t \<times> bool"

fun umebufn_add :: "utable list list \<Rightarrow> umebufn \<Rightarrow> umebufn" where
  "umebufn_add xs' xs = List.map2 (@@) xs xs'"

fun umebuf2S_add :: "utable list \<Rightarrow> utable list \<Rightarrow> ts list \<Rightarrow> umebuf2S \<Rightarrow> umebuf2S" where
  "umebuf2S_add xs' ys' ts' (xs, ys, ts, skew) = (xs @@ xs', ys @@ ys', ts @@ ts', skew)"

fun umeprev_next :: "\<I> \<Rightarrow> utable mbuf_t \<Rightarrow> ts mbuf_t
  \<Rightarrow> utable list \<times> utable mbuf_t \<times> ts mbuf_t"
  where "umeprev_next I xs ts = (case mbuf_t_cases xs of (None, xs') \<Rightarrow> ([], mbuf_t_empty, ts)
  | (Some x, xs') \<Rightarrow> (case mbuf_t_cases ts of (None, ts') \<Rightarrow> ([], x ## xs', mbuf_t_empty)
  | (Some t, ts') \<Rightarrow> (case mbuf_t_cases ts' of (None, ts'') \<Rightarrow> ([], x ## xs', t ## mbuf_t_empty)
  | (Some t', ts'') \<Rightarrow> (let (ys, zs) = umeprev_next I xs' (t' ## ts'')
    in ((if mem I ((t' - t)) then x else {}) # ys, zs)))))"

fun umebuf2T_take :: "(utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    umebuf2 \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> umebuf2 \<times> ts mbuf_t" where
  "umebuf2T_take f z (xs, ys) ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t ## ts') | (Some y, ys') \<Rightarrow>
    umebuf2T_take f (f x y t z) (xs', ys') ts')))"

fun umebufnt_take :: "(utable list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> umebufn \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow>
    'b \<times> umebufn \<times> ts \<times> ts mbuf_t" where
  "umebufnt_take f z buf t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, buf, t0, ts) | (Some t, ts') \<Rightarrow>
    (if (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf, t, t ## ts')
     else umebufnt_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) t z)
       (map (snd \<circ> mbuf_t_cases) buf) t ts'))"

section \<open>A monitor over the short tuples\<close>

text \<open>
  The formula carries, at every node, the columns of the table the node produces.  Every
  constructor of the sparse formula has a dense counterpart; what the compiler cannot place --
  a node whose stored frame disagrees with the columns its parent asks for -- becomes
  a failure node.  Building the state counts those nodes and refuses the formula when there is
  one, so the monitor never mixes the two representations: there is no wide evaluation left to
  fall back to.  At the root the columns are all of them, so the verdicts have the width the
  printer expects and nothing is converted there.
\<close>

fun trm_vars :: "Formula.trm \<Rightarrow> nat list" where
  "trm_vars (Formula.Var x) = [x]"
| "trm_vars (Formula.Const c) = []"
| "trm_vars (Formula.Plus a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.Minus a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.UMinus a) = trm_vars a"
| "trm_vars (Formula.Mult a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.Div a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.Mod a b) = trm_vars a @ trm_vars b"
| "trm_vars (Formula.F2i a) = trm_vars a"
| "trm_vars (Formula.I2f a) = trm_vars a"

definition tms_cols :: "Formula.trm list \<Rightarrow> cols" where
  "tms_cols tms = csorted_list_of_set (set (concat (map trm_vars tms)))"

text \<open>The columns a subformula produces, where they can be read off it.\<close>

fun mcols :: "nat \<Rightarrow> mformula_j \<Rightarrow> cols option" where
  "mcols n (MPred e tms mode) = Some (tms_cols tms)"
| "mcols n (MAnd A \<phi> pos B \<psi> buf) =
    Some (if pos then merge_cols (set_cols A) (set_cols B) else set_cols A)"
| "mcols n (MAnds A_pos A_neg L buf) =
    (case A_pos of [] \<Rightarrow> None
     | A # As \<Rightarrow> Some (dands_cols (set_cols A) (map set_cols As)))"
| "mcols n (MAgg args \<phi>) = Some (dagg_cols args)"
| "mcols n (MAndRel \<phi> conf) = mcols n \<phi>"
| "mcols n (MOr \<phi> \<psi> buf) = mcols n \<phi>"
| "mcols n (MNeg \<phi>) = Some []"
| "mcols n (MExists \<phi>) = (case mcols (Suc n) \<phi> of None \<Rightarrow> None
    | Some cs \<Rightarrow> Some (map (\<lambda>x. x - 1) (filter (\<lambda>x. x \<noteq> 0) cs)))"
| "mcols n (MPrev I \<phi> first buf nts) = mcols n \<phi>"
| "mcols n (MNext I \<phi> first nts) = mcols n \<phi>"
| "mcols n (MSince args \<phi> \<psi> buf aux) =
    (case args_agg args of None \<Rightarrow> Some (set_cols (args_R args))
     | Some aggargs \<Rightarrow> Some (dagg_cols aggargs))"
| "mcols n (MUntil args \<phi> \<psi> buf nts t aux) =
    (case args_agg args of None \<Rightarrow> Some (set_cols (args_R args))
     | Some aggargs \<Rightarrow> Some (dagg_cols aggargs))"
| "mcols n (MTrigger args \<phi> \<psi> buf nts aux) = Some (set_cols (args_R args))"
| "mcols n (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
    Some (merge_cols (set_cols V) (set_cols (args_R args)))"
| "mcols n (MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = mcols n \<psi>"
| "mcols n (MLetPast p m \<phi> \<psi> i buf) = mcols n \<psi>"
| "mcols n (MMatchP I mr mrs \<phi>s buf nts aux) =
    map_option (\<lambda>css. fold merge_cols css []) (those (map (mcols n) \<phi>s))"
| "mcols n (MMatchF I mr mrs \<phi>s buf nts t aux) =
    map_option (\<lambda>css. fold merge_cols css []) (those (map (mcols n) \<phi>s))"
| "mcols n (MAndAssign \<phi> conf) = (case mcols n \<phi> of None \<Rightarrow> None
    | Some cs \<Rightarrow> (if fst conf \<in> set cs \<or> \<not> Formula.fv_trm (snd conf) \<subseteq> set cs then None
                 else Some (merge_cols cs [fst conf])))"
| "mcols n (MLet p m \<phi> \<psi>) = mcols n \<psi>"
| "mcols n (MTP mt i) = Some (mtrm_dcols mt)"
| "mcols n (MTS mt) = Some (mtrm_dcols mt)"
| "mcols n \<phi> = None"

subsection \<open>The temporal structures at the dense frame\<close>

text \<open>
  The Since and the Until of @{theory MFODL_Monitor_Imp.Since_Imp2} and
  @{theory MFODL_Monitor_Imp.Until_Imp2} take the left operand's table at the right operand's
  frame, which is why the node had to embed it first.  The structures of
  @{theory MFODL_Monitor_Imp.Dense_Aux} take it at the left operand's own frame, so the
  embedding disappears.

  They replace exactly one branch each.  Where @{const init_j} picks @{const MSJ_pure} it is
  because @{const special_args} fails, that is, because the join columns are a proper nonempty
  subset -- and that is precisely the case in which the embedding was not a no-op.  The other
  two branches, the heap-resident structure and the closed-left-operand one, are reached only
  when the two frames coincide or the left one is empty, where there was nothing to embed.  So
  the dense node keeps them unchanged and swaps the pure structure for the dense one.
\<close>

datatype msaux_d = MSD_imp "event_data list msaux2" | MSD_dns "event_data gmsaux"
  | MSD_evt "event_data gsevtaux" | MSD_agg daggargs dmasaux

text \<open>Of the three representations only @{const MSD_imp} lives on the heap.  The freeze node
  replays its body from a fixed state, which a heap-resident structure cannot do, so the
  compiler has to be able to rule that representation out for the subtree it replays.  It says
  so through the flag below, which it reads off the representation the sparse monitor picked
  for the same node -- the two conditions are the same one, so nothing changes for a node
  outside a freeze.\<close>

fun msj_heap :: "msaux_j \<Rightarrow> bool" where
  "msj_heap (MSJ_imp q) = True"
| "msj_heap _ = False"

text \<open>A node whose aggregation is fused into it takes the fourth representation, which is the
  window of the second with the aggregate maintained alongside.  It is not a choice between
  representations: the other three produce the window itself, and only this one produces the
  aggregate of it, so the compiler picks it exactly when the node carries an aggregation.\<close>

definition init_d :: "bool \<Rightarrow> daggargs option \<Rightarrow> args \<Rightarrow> bool list \<Rightarrow> msaux_d Heap" where
  "init_d hp ago args msk = (case ago of Some ag \<Rightarrow>
       return (MSD_agg ag (dainit_msaux args ag msk))
     | None \<Rightarrow>
       (if sevt_applies args then return (MSD_evt (ginit_sevt args))
        else if hp \<and> args_agg args = None \<and> special_args args
        then do { q \<leftarrow> init2 args; return (MSD_imp q) }
        else return (MSD_dns (ginit_msaux args msk))))"

fun add_new_ts_d :: "args \<Rightarrow> ts \<Rightarrow> msaux_d \<Rightarrow> msaux_d Heap" where
  "add_new_ts_d args nt (MSD_imp q) =
     do { q \<leftarrow> add_new_ts2 uihash ueq args nt q; return (MSD_imp q) }"
| "add_new_ts_d args nt (MSD_dns s) = return (MSD_dns (gadd_new_ts_msaux args nt s))"
| "add_new_ts_d args nt (MSD_evt a) = return (MSD_evt (gadd_new_ts_sevt args nt a))"
| "add_new_ts_d args nt (MSD_agg ag s) =
     return (MSD_agg ag (daadd_new_ts_msaux args ag nt s))"

text \<open>The table this takes is the left operand's, at the left operand's frame in the dense
  branch and at the common frame in the other two.\<close>

fun join_d :: "args \<Rightarrow> utable \<Rightarrow> msaux_d \<Rightarrow> msaux_d Heap" where
  "join_d args X (MSD_imp q) =
     do { q \<leftarrow> gc_join2 uihash ueq [] args X q; return (MSD_imp q) }"
| "join_d args X (MSD_dns s) = return (MSD_dns (ggc_join_msaux args X s))"
| "join_d args X (MSD_evt a) = return (MSD_evt (gjoin_sevt args X a))"
| "join_d args X (MSD_agg ag s) = return (MSD_agg ag (dajoin_msaux args ag X s))"

fun add_new_table_d :: "args \<Rightarrow> utable \<Rightarrow> msaux_d \<Rightarrow> msaux_d Heap" where
  "add_new_table_d args X (MSD_imp q) =
     do { q \<leftarrow> add_new_table2 uihash ueq args X q; return (MSD_imp q) }"
| "add_new_table_d args X (MSD_dns s) = return (MSD_dns (gadd_new_table_msaux args X s))"
| "add_new_table_d args X (MSD_evt a) = return (MSD_evt (gadd_new_table_sevt args X a))"
| "add_new_table_d args X (MSD_agg ag s) =
     return (MSD_agg ag (daadd_new_table_msaux args ag X s))"

fun result_d :: "args \<Rightarrow> msaux_d \<Rightarrow> utable Heap" where
  "result_d args (MSD_imp q) = result2 q"
| "result_d args (MSD_dns s) = return (gresult_msaux args s)"
| "result_d args (MSD_evt a) = return (gresult_sevt args a)"
| "result_d args (MSD_agg ag s) = return (daresult_msaux ag s)"

partial_function (heap) eval_since_d :: "args \<Rightarrow> utable list \<Rightarrow> umebuf2S \<Rightarrow>
    msaux_d \<Rightarrow> (utable list \<times> umebuf2S \<times> msaux_d) Heap" where
  [code]:
  "eval_since_d args rs buf aux = (case buf of (xs, ys, ts, skew) \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow>
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          (if skew \<or> memL (args_ivl args) 0
           then return (rev rs, (x ## xs', mbuf_t_empty, t ## ts', skew), aux)
           else do { aux \<leftarrow> add_new_ts_d args t aux; aux' \<leftarrow> join_d args x aux;
                     r \<leftarrow> result_d args aux';
                     return (rev (r # rs), (xs', mbuf_t_empty, ts', True), aux') })
        | (None, ts') \<Rightarrow> return (rev rs, (x ## xs', mbuf_t_empty, mbuf_t_empty, skew), aux))
      | (None, xs') \<Rightarrow> return (rev rs, (mbuf_t_empty, mbuf_t_empty, ts, skew), aux))
    | (Some y, ys') \<Rightarrow>
      if skew then do { aux \<leftarrow> add_new_table_d args y aux;
                        eval_since_d args rs (xs, ys', ts, False) aux }
      else
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          do { aux \<leftarrow> add_new_ts_d args t aux; aux \<leftarrow> join_d args x aux;
               aux' \<leftarrow> add_new_table_d args y aux; r \<leftarrow> result_d args aux';
               eval_since_d args (r # rs) (xs', ys', ts', False) aux' }
        | (None, ts') \<Rightarrow> return (rev rs, (x ## xs', y ## ys', ts', skew), aux))
      | (None, xs') \<Rightarrow> return (rev rs, (mbuf_t_empty, y ## ys', ts, skew), aux))))"

text \<open>
  The Until is the same story.  Only @{const add_new_dq} reads the left operand, and the dense
  @{const dadd_new_dq} reads it at the left operand's frame, keyed by the mask the node carries.
\<close>

datatype muaux_d = MUD_dns "event_data gmuaux" | MUD_evt "event_data gevtaux"
  | MUD_agg daggargs dmauaux

definition init_u_d :: "daggargs option \<Rightarrow> args \<Rightarrow> bool list \<Rightarrow> muaux_d Heap" where
  "init_u_d ago args msk = (case ago of Some ag \<Rightarrow> return (MUD_agg ag (gainit_dq args ag))
     | None \<Rightarrow> (if evt_applies args then return (MUD_evt (ginit_evt args))
        else return (MUD_dns (ginit_dq args))))"

fun add_new_u_d :: "args \<Rightarrow> bool list \<Rightarrow> utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow>
    muaux_d \<Rightarrow> muaux_d Heap" where
  "add_new_u_d args msk rel1 rel2 nt (MUD_dns a) =
     return (MUD_dns (gadd_new_dq args msk rel1 rel2 nt a))"
| "add_new_u_d args msk rel1 rel2 nt (MUD_evt a) =
     return (MUD_evt (gadd_new_evt args rel1 rel2 nt a))"
| "add_new_u_d args msk rel1 rel2 nt (MUD_agg ag a) =
     return (MUD_agg ag (gaadd_new_dq args ag msk rel1 rel2 nt a))"

fun eval_u_d :: "args \<Rightarrow> ts \<Rightarrow> muaux_d \<Rightarrow> (utable list \<times> muaux_d) Heap" where
  "eval_u_d args nt (MUD_dns a) = return (case geval_dq args nt a of (zs, a') \<Rightarrow> (zs, MUD_dns a'))"
| "eval_u_d args nt (MUD_evt a) = return (case geval_evt args nt a of (zs, a') \<Rightarrow> (zs, MUD_evt a'))"
| "eval_u_d args nt (MUD_agg ag a) =
     return (case gaeval_dq args ag nt a of (zs, a') \<Rightarrow> (zs, MUD_agg ag a'))"

datatype dformula =
    DFail
  | DRel utable
  | DPredS Formula.name nat
  | DPredM Formula.name nat "Formula.trm list" cols
  | DAnd djoin_plan dformula bool dformula umebuf2
  | DAnds "djoin_plan list" "djoin_plan list" "dformula list" umebufn
  | DAndRel dformula "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | DOr dformula dformula umebuf2
  | DNeg dformula
  | DExists dformula bool
  | DAgg bool "ty Formula.agg_op" Formula.trm nat nat dformula
  | DPrev \<I> dformula bool "utable mbuf_t" "ts mbuf_t"
  | DNext \<I> dformula bool "ts mbuf_t"
  | DSince args dformula dformula umebuf2S msaux_d
  | DUntil args "bool list" dformula dformula umebuf2 "ts mbuf_t" ts muaux_d
  | DAndAssign nat Formula.trm dformula
  | DTP mtrm nat
  | DTS mtrm
  | DLet Formula.name nat dformula dformula
  | DFrz Formula.name nat dformula dformula nat nat nat "utable list"
  | DLetPast Formula.name nat dformula dformula nat "utable option"
  | DTrigger args dformula dformula umebuf2 "ts mbuf_t" "event_data gmmtaux"
  | DAndTrigger djoin_plan dformula umebuf2O args dformula dformula umebuf2 "ts mbuf_t"
      "event_data gmmtaux"
  | DMatchP \<I> mregex "mregex list" "bool list list" "dformula list" umebufn "ts mbuf_t"
      "event_data gmrdaux"
  | DMatchF \<I> mregex "mregex list" "bool list list" "dformula list" umebufn "ts mbuf_t" ts
      "event_data gmldaux"

subsection \<open>Building it\<close>

text \<open>The buffers of the node being compiled hold the wide tables, so they are not carried
  over; they are empty, because this runs on the freshly built formula and nothing has been
  evaluated yet.\<close>

text \<open>
  The freeze node's body is replayed from a fixed state, so nothing below it may keep anything
  on the heap.  It does not: the only heap-resident representation is @{const MSD_imp}, which
  @{const init_d} picks only where the sparse monitor picked @{const MSJ_imp} for the same node,
  and @{const mformula_j_of} leaves the freeze node to @{const embed}, which puts every Since
  and Until structure below it into its pure representation.  That is the same invariant the
  sparse monitor relies on, which evaluates a freeze node by purifying it.
\<close>

function (sequential) dformula_of :: "nat \<Rightarrow> cols \<Rightarrow> mformula_j \<Rightarrow> dformula Heap"
  and dformula_of_list :: "nat \<Rightarrow> cols list \<Rightarrow> mformula_j list \<Rightarrow> dformula list Heap" where
  "dformula_of_list n cs [] = return []"
| "dformula_of_list n cs (\<phi> # r) = do {
     \<phi>d \<leftarrow> dformula_of n (case cs of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) \<phi>;
     \<phi>s \<leftarrow> dformula_of_list n (case cs of [] \<Rightarrow> [] | _ # r' \<Rightarrow> r') r;
     return (\<phi>d # \<phi>s) }"
| "dformula_of n cs (MAnds A_pos A_neg L buf) =
     (case A_pos of [] \<Rightarrow> return DFail
      | A # As \<Rightarrow>
        (let cs_pos = set_cols A # map set_cols As;
             fin = dands_cols (set_cols A) (map set_cols As);
             cs_neg = map set_cols A_neg in
         if length L \<noteq> length A_pos + length A_neg
         then return DFail
         else do {
           Ld \<leftarrow> dformula_of_list n (cs_pos @ cs_neg) L;
           return (DAnds (dands_plans (set_cols A) (map set_cols As))
                     (map (mk_djoin fin) cs_neg) Ld (map (\<lambda>_. mbuf_t_empty) Ld)) }))"
| "dformula_of n cs (MPred e tms mode) =
     return (if mode \<noteq> Match \<and> cs = tms_cols tms then DPredS e (length tms)
             else DPredM e (length tms) tms cs)"
| "dformula_of n cs (MRel rel) = return (DRel (deopt_table (dnarrow (wide_mask n cs) rel)))"
| "dformula_of n cs (MAnd A \<phi> pos B \<psi> buf) = do {
     \<phi>d \<leftarrow> dformula_of n (set_cols A) \<phi>;
     \<psi>d \<leftarrow> dformula_of n (set_cols B) \<psi>;
     return (DAnd (mk_djoin (set_cols A) (set_cols B)) \<phi>d pos \<psi>d
                (mbuf_t_empty, mbuf_t_empty)) }"
| "dformula_of n cs (MAndRel \<phi> conf) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>;
     return (DAndRel \<phi>d (reindex_constraint cs conf)) }"
| "dformula_of n cs (MOr \<phi> \<psi> buf) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>; \<psi>d \<leftarrow> dformula_of n cs \<psi>;
     return (DOr \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty)) }"
| "dformula_of n cs (MNeg \<phi>) = do {
     \<phi>d \<leftarrow> dformula_of n [] \<phi>; return (DNeg \<phi>d) }"
| "dformula_of n cs (MExists \<phi>) = (case mcols (Suc n) \<phi> of
     None \<Rightarrow> return DFail
   | Some ccs \<Rightarrow> do {
       \<phi>d \<leftarrow> dformula_of (Suc n) ccs \<phi>;
       return (DExists \<phi>d (case ccs of [] \<Rightarrow> False | c # _ \<Rightarrow> c = 0)) })"
| "dformula_of n cs (MAgg args \<phi>) = do {
     \<phi>d \<leftarrow> dformula_of (length (aggargs_tys args) + n) (dagg_child_cols args) \<phi>;
     return (DAgg (aggargs_g0 args) (aggargs_\<omega> args)
               (reindex_trm (dagg_child_cols args) (aggargs_f args))
               (length (aggargs_tys args)) (dagg_pos args) \<phi>d) }"
| "dformula_of n cs (MPrev I \<phi> first buf nts) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>; return (DPrev I \<phi>d first mbuf_t_empty nts) }"
| "dformula_of n cs (MNext I \<phi> first nts) = do {
     \<phi>d \<leftarrow> dformula_of n cs \<phi>; return (DNext I \<phi>d first nts) }"
| "dformula_of n cs (MSince args \<phi> \<psi> buf aux) =
     (let cs_L = set_cols (args_L args) in
      if sevt_applies args then do {
        \<phi>d \<leftarrow> dformula_of n cs_L \<phi>;
        \<psi>d \<leftarrow> dformula_of n (set_cols (args_R args)) \<psi>;
        q \<leftarrow> init_d (msj_heap aux) None args (dmsk (set_cols (args_R args)) cs_L);
        return (DSince args \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty, mbuf_t_empty, False) q) }
      else if args_agg args = None \<and> args_n args = n \<and> args_R args = set cs \<and>
              set cs_L \<subseteq> set cs
      then (let dags = dargs cs cs_L args in do {
        \<phi>d \<leftarrow> dformula_of n cs_L \<phi>;
        \<psi>d \<leftarrow> dformula_of n cs \<psi>;
        q \<leftarrow> init_d (msj_heap aux) None dags (dmsk cs cs_L);
        return (DSince dags \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty, mbuf_t_empty, False) q) })
      else if dagg_fused n cs args
      then (let ag = the (args_agg args);
                ccs = dagg_child_cols ag;
                dags = dargs ccs cs_L (dunfuse args) in do {
        \<phi>d \<leftarrow> dformula_of (args_n args) cs_L \<phi>;
        \<psi>d \<leftarrow> dformula_of (args_n args) ccs \<psi>;
        q \<leftarrow> init_d (msj_heap aux) (Some (dagg_of ag)) dags (dmsk ccs cs_L);
        return (DSince dags \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty, mbuf_t_empty, False) q) })
      else return DFail)"
| "dformula_of n cs (MUntil args \<phi> \<psi> buf nts t aux) =
     (let cs_L = set_cols (args_L args) in
      if evt_applies args then do {
        \<phi>d \<leftarrow> dformula_of n cs_L \<phi>;
        \<psi>d \<leftarrow> dformula_of n (set_cols (args_R args)) \<psi>;
        d \<leftarrow> init_u_d None args (dmsk (set_cols (args_R args)) cs_L);
        return (DUntil args (dmsk (set_cols (args_R args)) cs_L) \<phi>d \<psi>d
                   (mbuf_t_empty, mbuf_t_empty) nts t d) }
      else if args_agg args = None \<and> args_n args = n \<and> args_R args = set cs \<and>
              set cs_L \<subseteq> set cs
      then (let dags = dargs cs cs_L args in do {
        \<phi>d \<leftarrow> dformula_of n cs_L \<phi>;
        \<psi>d \<leftarrow> dformula_of n cs \<psi>;
        d \<leftarrow> init_u_d None dags (dmsk cs cs_L);
        return (DUntil dags (dmsk cs cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) nts t d) })
      else if dagg_fused n cs args
      then (let ag = the (args_agg args);
                ccs = dagg_child_cols ag;
                dags = dargs ccs cs_L (dunfuse args) in do {
        \<phi>d \<leftarrow> dformula_of (args_n args) cs_L \<phi>;
        \<psi>d \<leftarrow> dformula_of (args_n args) ccs \<psi>;
        d \<leftarrow> init_u_d (Some (dagg_of ag)) dags (dmsk ccs cs_L);
        return (DUntil dags (dmsk ccs cs_L) \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) nts t d) })
      else return DFail)"
| "dformula_of n cs (MAndAssign \<phi> conf) =
     (let y = fst conf; t = snd conf; cs0 = rem_col cs y in
      if y \<in> set cs \<and> Formula.fv_trm t \<subseteq> set cs0
      then do {
        \<phi>d \<leftarrow> dformula_of n cs0 \<phi>;
        return (DAndAssign (ins_pos cs0 y) (reindex_trm cs0 t) \<phi>d) }
      else return DFail)"
| "dformula_of n cs (MLet p m \<phi> \<psi>) = do {
     \<phi>d \<leftarrow> dformula_of m [0..<m] \<phi>;
     \<psi>d \<leftarrow> dformula_of n cs \<psi>;
     return (DLet p m \<phi>d \<psi>d) }"
| "dformula_of n cs (MTP mt i) =
     return (if cs = mtrm_dcols mt then DTP mt i else DFail)"
| "dformula_of n cs (MTS mt) =
     return (if cs = mtrm_dcols mt then DTS mt else DFail)"
| "dformula_of n cs (MMatchP I mr mrs \<phi>s buf nts aux) =
     (case those (map (mcols n) \<phi>s) of
        None \<Rightarrow> return DFail
      | Some css \<Rightarrow>
        (if cs = fold merge_cols css [] then do {
           Ld \<leftarrow> dformula_of_list n css \<phi>s;
           return (DMatchP I mr mrs (map (dmsk cs) css) Ld
                     (map (\<lambda>_. mbuf_t_empty) Ld) mbuf_t_empty []) }
         else return DFail))"
| "dformula_of n cs (MMatchF I mr mrs \<phi>s buf nts t aux) =
     (case those (map (mcols n) \<phi>s) of
        None \<Rightarrow> return DFail
      | Some css \<Rightarrow>
        (if cs = fold merge_cols css [] then do {
           Ld \<leftarrow> dformula_of_list n css \<phi>s;
           return (DMatchF I mr mrs (map (dmsk cs) css) Ld
                     (map (\<lambda>_. mbuf_t_empty) Ld) mbuf_t_empty t []) }
         else return DFail))"
| "dformula_of n cs (MTrigger args \<phi> \<psi> buf nts aux) =
     (let cs_L = set_cols (args_L args) in
      if args_n args = n \<and> args_R args = set cs \<and> set cs_L \<subseteq> set cs \<and> mem (args_ivl args) 0
      then (let dags = dargs cs cs_L args in do {
        \<phi>d \<leftarrow> dformula_of n cs_L \<phi>;
        \<psi>d \<leftarrow> dformula_of n cs \<psi>;
        return (DTrigger dags \<phi>d \<psi>d (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
                  (ginit_mmtaux dags (dmsk cs cs_L))) })
      else return DFail)"
| "dformula_of n cs (MAndTrigger V \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) =
     (let cs_V = set_cols V; cs_R = set_cols (args_R args); cs_L = set_cols (args_L args) in
      if args_n args = n \<and> cs = merge_cols cs_V cs_R \<and> set cs_R \<subseteq> set cs_V \<and> set cs_L \<subseteq> set cs_R
      then (let dags = dargs cs_R cs_L args in do {
        \<phi>d \<leftarrow> dformula_of n cs_V \<phi>;
        \<phi>d' \<leftarrow> dformula_of n cs_L \<phi>';
        \<psi>d' \<leftarrow> dformula_of n cs_R \<psi>';
        return (DAndTrigger (mk_djoin cs_V cs_R) \<phi>d (mbuf_t_empty, mbuf_t_empty) dags \<phi>d' \<psi>d'
                  (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty
                  (ginit_mmtaux dags (dmsk cs_R cs_L))) })
      else return DFail)"
| "dformula_of n cs (MLetPast p m \<phi> \<psi> i buf) = do {
     \<phi>d \<leftarrow> dformula_of m [0..<m] \<phi>;
     \<psi>d \<leftarrow> dformula_of n cs \<psi>;
     return (DLetPast p m \<phi>d \<psi>d i
               (map_option (deopt_table \<circ> dnarrow (wide_mask m [0..<m])) buf)) }"
| "dformula_of n cs (MFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = do {
     \<phi>d \<leftarrow> dformula_of m [0..<m] \<phi>;
     \<psi>d \<leftarrow> dformula_of n cs \<psi>;
     return (DFrz p m \<phi>d \<psi>d jfrz jpsi0 jphi
               (map (deopt_table \<circ> dnarrow (wide_mask m [0..<m])) \<alpha>s)) }"
  by pat_completeness auto

text \<open>Every recursive call descends into a subformula; the compiler's own arguments -- the frame
  and the column list -- move in both directions, so the measure names the subformula outright
  rather than leaving it to be searched for.\<close>

termination
  by (relation "measure (case_sum (\<lambda>(n, cs, \<phi>). size \<phi>) (\<lambda>(n, cs, L). size_list size L))") auto

subsection \<open>Evaluating it\<close>

text \<open>
  The freeze node re-enters the evaluator on its body's \<^emph>\<open>updated\<close> state, which is not a
  subterm of the node.  The pure evaluator settles that with a termination proof over the
  formula's size; here the result sits inside the heap monad, where the size of the updated
  state is not a term a termination prover can reach.  So the evaluator below is a least fixed
  point in the heap monad's own partial order, which asks for no termination argument at all.
  What it asks for instead is that the body be monotone in the recursive call, and the two
  combinators the body passes that call to carry the obligation themselves.
\<close>

fun hmap :: "('a \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b list Heap" where
  "hmap f [] = return []"
| "hmap f (x # xs) = do { y \<leftarrow> f x; ys \<leftarrow> hmap f xs; return (y # ys) }"

lemma hmap_mono[partial_function_mono]:
  assumes "\<And>x. mono_Heap (F x)"
  shows "mono_Heap (\<lambda>f. hmap (\<lambda>x. F x f) xs)"
  using assms by (induct xs) (auto intro!: partial_function_mono)

text \<open>
  The freeze node's replay loop, the heap counterpart of the kernel's @{const freeze_meval0}.
  Each round evaluates the body from the state the loop began in -- the round's own updated
  state is discarded -- so nothing below the body may be heap-resident, which is what the
  compiler arranges.
\<close>

fun freeze_meval0_h :: "(utable \<Rightarrow> (utable list \<times> 'a) Heap) \<Rightarrow> nat \<Rightarrow> utable list \<Rightarrow>
    (utable list \<times> utable list) Heap" where
  "freeze_meval0_h eval k [] = return ([], [])"
| "freeze_meval0_h eval k (\<alpha> # \<alpha>s) = do {
     r \<leftarrow> eval \<alpha>;
     (case drop k (fst r) of [] \<Rightarrow> return ([], \<alpha> # \<alpha>s)
      | y # _ \<Rightarrow> do { z \<leftarrow> freeze_meval0_h eval (Suc k) \<alpha>s;
                     return (y # fst z, snd z) }) }"

text \<open>
  The recursive let's loop, the heap counterpart of the kernel's @{const letpast_meval0}.  It
  carries the body's state from round to round, so unlike the freeze node's loop it puts no
  demand on the body.  Its own recursion is bounded by the number of time points whatever the
  body does, which is why it is a total function of its own rather than part of the fixed
  point; only the evaluator it is handed is one.
\<close>

function letpast_meval0_h ::
  "(ts list \<Rightarrow> udatabase \<Rightarrow> dformula \<Rightarrow> (utable list \<times> dformula) Heap) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   utable list \<Rightarrow> utable list \<Rightarrow> Formula.name \<times> nat \<Rightarrow> ts list \<Rightarrow> udatabase \<Rightarrow> dformula \<Rightarrow>
   (utable list \<times> nat \<times> utable option \<times> dformula) Heap" where
  "letpast_meval0_h eval j i ys xs p ts db \<phi> = do {
     r \<leftarrow> eval ts (Mapping.update p xs db) \<phi>;
     (if size (snd r) \<noteq> size \<phi> then return ([], 0, None, \<phi>)
      else case fst r of
        [] \<Rightarrow> return (ys @ fst r, i + length xs, None, snd r)
      | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j
          then return (ys @ fst r, i + length xs, Some y, snd r)
          else letpast_meval0_h eval j (i + length xs) (ys @ fst r) (fst r) p []
                 (Mapping.map_values (\<lambda>_ _. []) db) (snd r))) }"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, j, i, _, xs, _). j - (i + length xs))")
     (auto simp: not_le min_def diff_less_mono2)

declare letpast_meval0_h.simps[simp del]

lemma letpast_meval0_h_mono_aux:
  assumes E: "\<And>ts db \<chi>. mono_Heap (\<lambda>f. E ts db \<chi> f)"
  shows "j - (i + length xs) \<le> n \<Longrightarrow>
    mono_Heap (\<lambda>f. letpast_meval0_h (\<lambda>ts db \<chi>. E ts db \<chi> f) j i ys xs p ts0 db0 \<phi>)"
proof (induct n arbitrary: i ys xs ts0 db0 \<phi>)
  case (0 i ys xs ts0 db0 \<phi>)
  have "mono_Heap (\<lambda>f. E ts0 (Mapping.update p xs db0) \<phi> f \<bind>
    (\<lambda>r. if size (snd r) \<noteq> size \<phi> then return ([], 0, None, \<phi>)
         else case fst r of
           [] \<Rightarrow> return (ys @ fst r, i + length xs, None, snd r)
         | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j
             then return (ys @ fst r, i + length xs, Some y, snd r)
             else letpast_meval0_h (\<lambda>ts db \<chi>. E ts db \<chi> f) j (i + length xs) (ys @ fst r)
                    (fst r) p [] (Mapping.map_values (\<lambda>_ _. []) db0) (snd r))))"
  proof (rule bind_mono[OF E], goal_cases)
    case (1 r)
    have "Suc (i + length xs) \<ge> j" using "0.prems" by arith
    then show ?case by (cases "fst r") (auto intro!: partial_function_mono)
  qed
  then show ?case by (subst letpast_meval0_h.simps) simp
next
  case (Suc n i ys xs ts0 db0 \<phi>)
  have "mono_Heap (\<lambda>f. E ts0 (Mapping.update p xs db0) \<phi> f \<bind>
    (\<lambda>r. if size (snd r) \<noteq> size \<phi> then return ([], 0, None, \<phi>)
         else case fst r of
           [] \<Rightarrow> return (ys @ fst r, i + length xs, None, snd r)
         | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j
             then return (ys @ fst r, i + length xs, Some y, snd r)
             else letpast_meval0_h (\<lambda>ts db \<chi>. E ts db \<chi> f) j (i + length xs) (ys @ fst r)
                    (fst r) p [] (Mapping.map_values (\<lambda>_ _. []) db0) (snd r))))"
  proof (rule bind_mono[OF E], goal_cases)
    case (1 r)
    show ?case
    proof (cases "fst r")
      case Nil
      then show ?thesis by (auto intro!: partial_function_mono)
    next
      case (Cons y r')
      show ?thesis
      proof (cases "Suc (i + length xs) \<ge> j")
        case True
        with Cons show ?thesis by (auto intro!: partial_function_mono)
      next
        case False
        have "1 \<le> length (fst r)" using Cons by simp
        then have le: "j - (i + length xs + length (fst r)) \<le> n"
          using False Suc.prems by arith
        have IH: "mono_Heap (\<lambda>f. letpast_meval0_h (\<lambda>ts db \<chi>. E ts db \<chi> f) j (i + length xs)
                    (ys @ fst r) (fst r) p [] (Mapping.map_values (\<lambda>_ _. []) db0) (snd r))"
          by (rule Suc.hyps[OF le])
        from Cons False IH show ?thesis by (auto intro!: partial_function_mono)
      qed
    qed
  qed
  then show ?case by (subst letpast_meval0_h.simps) simp
qed

lemma letpast_meval0_h_mono[partial_function_mono]:
  assumes "\<And>ts db \<chi>. mono_Heap (\<lambda>f. E ts db \<chi> f)"
  shows "mono_Heap (\<lambda>f. letpast_meval0_h (\<lambda>ts db \<chi>. E ts db \<chi> f) j i ys xs p ts0 db0 \<phi>)"
  by (rule letpast_meval0_h_mono_aux[OF assms le_refl])

lemma freeze_meval0_h_mono[partial_function_mono]:
  assumes E: "\<And>x. mono_Heap (E x)"
  shows "mono_Heap (\<lambda>f. freeze_meval0_h (\<lambda>x. E x f) k \<alpha>s)"
proof (induct \<alpha>s arbitrary: k)
  case Nil
  show ?case by (auto intro!: partial_function_mono)
next
  case (Cons \<alpha> \<alpha>s)
  have "mono_Heap (\<lambda>f. E \<alpha> f \<bind>
      (\<lambda>r. case drop k (fst r) of [] \<Rightarrow> return ([], \<alpha> # \<alpha>s)
           | y # _ \<Rightarrow> freeze_meval0_h (\<lambda>x. E x f) (Suc k) \<alpha>s \<bind>
                     (\<lambda>z. return (y # fst z, snd z))))"
  proof (rule bind_mono[OF E], goal_cases)
    case (1 r)
    show ?case
      by (cases "drop k (fst r)") (auto intro!: partial_function_mono Cons.hyps)
  qed
  then show ?case by simp
qed

text \<open>
  One step of the evaluator, with the recursive call left open as the parameter @{term rc}.
  Writing it this way keeps the node-by-node reading of the equations and turns the fixed
  point's monotonicity obligation into a lemma that can be proved node by node.
\<close>

fun deval_step :: "(nat \<Rightarrow> ts list \<Rightarrow> udatabase \<Rightarrow> dformula \<Rightarrow> (utable list \<times> dformula) Heap) \<Rightarrow>
    nat \<Rightarrow> ts list \<Rightarrow> udatabase \<Rightarrow> dformula \<Rightarrow> (utable list \<times> dformula) Heap" where
  "deval_step rc j ts db (DAnds ps ns L buf) = do {
     R \<leftarrow> hmap (\<lambda>\<phi>. rc j ts db \<phi>) L;
     p \<leftarrow> mebufn_take_j (dmulti_join ps ns) mbuf_t_empty (umebufn_add (map fst R) buf);
     return (Rep_mbuf_t (fst p), DAnds ps ns (map snd R) (snd p)) }"
| "deval_step rc j ts db DFail =
     raise (STR ''deval: the formula is outside the dense fragment'')"
| "deval_step rc j ts db (DRel rel) = return (replicate (length ts) rel, DRel rel)"
| "deval_step rc j ts db (DPredS e ar) = return
     ((case Mapping.lookup db (e, ar) of None \<Rightarrow> replicate (length ts) {} | Some xs \<Rightarrow> xs),
      DPredS e ar)"
| "deval_step rc j ts db (DPredM e ar tms cs) = return
     ((case Mapping.lookup db (e, ar) of None \<Rightarrow> replicate (length ts) {}
       | Some xs \<Rightarrow> map (umatch_table tms cs) xs),
      DPredM e ar tms cs)"
| "deval_step rc j ts db (DAnd pl \<phi> pos \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> rc j ts db \<psi>;
     r \<leftarrow> mebuf2_take_j (\<lambda>r1 r2. dbin_join_h pl r1 pos r2) (mebuf2_add xs ys buf);
     return (fst r, DAnd pl \<phi> pos \<psi> (snd r)) }"
| "deval_step rc j ts db (DAndRel \<phi> conf) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     return (map (Set.filter (ueval_constraint conf)) xs, DAndRel \<phi> conf) }"
| "deval_step rc j ts db (DOr \<phi> \<psi> buf) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> rc j ts db \<psi>;
     return (let (zs, buf) = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
       in (zs, DOr \<phi> \<psi> buf)) }"
| "deval_step rc j ts db (DNeg \<phi>) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     return (map (\<lambda>r. if r = {} then {[]} else {}) xs, DNeg \<phi>) }"
| "deval_step rc j ts db (DExists \<phi> drop0) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     return (if drop0 then map (\<lambda>r. tl ` r) xs else xs, DExists \<phi> drop0) }"
| "deval_step rc j ts db (DAgg g0 \<omega> f k pos \<phi>) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     return (map (uagg g0 \<omega> f k pos) xs, DAgg g0 \<omega> f k pos \<phi>) }"
| "deval_step rc j ts db (DPrev I \<phi> first buf nts) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     return (if first \<and> ts = [] then ([], DPrev I \<phi> True (buf @@ xs) (nts @@ ts))
       else let (zs, buf, nts) = umeprev_next I (buf @@ xs) (nts @@ ts)
         in (if first then {} # zs else zs, DPrev I \<phi> False buf nts)) }"
| "deval_step rc j ts db (DNext I \<phi> first nts) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     return (let (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
       (zs, buf, nts) = umeprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
       in (zs, DNext I \<phi> first nts)) }"
| "deval_step rc j ts db (DSince args \<phi> \<psi> buf aux) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> rc j ts db \<psi>;
     (zs, buf, aux) \<leftarrow> eval_since_d args [] (umebuf2S_add xs ys ts buf) aux;
     return (zs, DSince args \<phi> \<psi> buf aux) }"
| "deval_step rc j ts db (DUntil args msk \<phi> \<psi> buf nts t aux) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> rc j ts db \<psi>;
     r \<leftarrow> mebuf2t_take_j (add_new_u_d args msk) aux (mebuf2_add xs ys buf) t (nts @@ ts);
     (case r of (aux, buf, nt, nts') \<Rightarrow>
      do { z \<leftarrow> eval_u_d args nt aux;
           return (fst z, DUntil args msk \<phi> \<psi> buf nts' nt (snd z)) }) }"
| "deval_step rc j ts db (DAndAssign p t \<phi>) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     return (map (uassign p t) xs, DAndAssign p t \<phi>) }"
| "deval_step rc j ts db (DTP mt i) =
     return (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) [i..<j], DTP mt j)"
| "deval_step rc j ts db (DTS mt) =
     return (map (\<lambda>x. umtrm mt (EInt (integer_of_nat x))) ts, DTS mt)"
| "deval_step rc j ts db (DLet p m \<phi> \<psi>) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> rc j ts (Mapping.update (p, m) xs db) \<psi>;
     return (ys, DLet p m \<phi> \<psi>) }"
| "deval_step rc j ts db (DMatchP I mr mrs msks \<phi>s buf nts aux) = do {
     R \<leftarrow> hmap (\<lambda>\<phi>. rc j ts db \<phi>) \<phi>s;
     return (let ((zs, aux), buf, _, nts) = umebufnt_take (\<lambda>rels t (zs, ax).
          let (z, ax) = gupdate_matchP msks I mr mrs rels t ax in (zs @@ [z], ax))
          (mbuf_t_empty, aux) (umebufn_add (map fst R) buf) 0 (nts @@ ts)
       in (Rep_mbuf_t zs, DMatchP I mr mrs msks (map snd R) buf nts aux)) }"
| "deval_step rc j ts db (DMatchF I mr mrs msks \<phi>s buf nts t aux) = do {
     R \<leftarrow> hmap (\<lambda>\<phi>. rc j ts db \<phi>) \<phi>s;
     return (let (aux, buf, nt, nts) = umebufnt_take (gupdate_matchF msks I mr mrs) aux
             (umebufn_add (map fst R) buf) t (nts @@ ts);
          (zs, aux) = geval_matchF I mr nt aux
       in (zs, DMatchF I mr mrs msks (map snd R) buf nts nt aux)) }"
| "deval_step rc j ts db (DTrigger dags \<phi> \<psi> dbuf nts daux) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (ys, \<psi>) \<leftarrow> rc j ts db \<psi>;
     return (let ((zs, daux), dbuf, nts) = umebuf2T_take (\<lambda>r1 r2 t (zs, ax).
         let ax = gupdate_mmtaux dags t r1 r2 ax
         in (zs @ [gresult_mmtaux dags ax], ax)) ([], daux) (mebuf2_add xs ys dbuf) (nts @@ ts)
       in (zs, DTrigger dags \<phi> \<psi> dbuf nts daux)) }"
| "deval_step rc j ts db (DAndTrigger pl \<phi> buf1 dags \<phi>' \<psi>' buf2 nts daux) = do {
     (as, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (xs, \<phi>') \<leftarrow> rc j ts db \<phi>';
     (ys, \<psi>') \<leftarrow> rc j ts db \<psi>';
     ((zs_trigger, daux), buf2, nts) \<leftarrow> return (umebuf2T_take (\<lambda>r1 r2 t (zs, ax).
         let ax = gupdate_mmtaux dags t r1 r2 ax
         in (zs @ [if gmmtaux_empty ax then None else Some (gresult_mmtaux dags ax)], ax))
         ([], daux) (mebuf2_add xs ys buf2) (nts @@ ts));
     r \<leftarrow> mebuf2_take_j (\<lambda>r1 r2. case r2 of None \<Rightarrow> return r1
           | Some z \<Rightarrow> (case r1 of None \<Rightarrow> return None
              | Some a \<Rightarrow> do { c \<leftarrow> dbin_join_h pl a True z; return (Some c) }))
           (mebuf2_add (map Some as) zs_trigger buf1);
     return (map the (fst r), DAndTrigger pl \<phi> (snd r) dags \<phi>' \<psi>' buf2 nts daux) }"
| "deval_step rc j ts db (DLetPast p m \<phi> \<psi> i buf) = do {
     r \<leftarrow> letpast_meval0_h (\<lambda>ts' db' \<chi>. rc j ts' db' \<chi>) j i [] (list_of_option buf) (p, m) ts db \<phi>;
     (case r of (xs, i, buf, \<phi>) \<Rightarrow> do {
        (ys, \<psi>) \<leftarrow> rc j ts (Mapping.update (p, m) xs db) \<psi>;
        return (ys, DLetPast p m \<phi> \<psi> i buf) }) }"
| "deval_step rc j ts db (DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = do {
     (xs, \<phi>) \<leftarrow> rc j ts db \<phi>;
     (zs0, \<psi>) \<leftarrow> rc j ts (Mapping.update (p, m) [] db) \<psi>;
     (let zs0_out = drop (jfrz - jpsi0) zs0;
          jpsi0' = jpsi0 + length zs0;
          \<alpha>s' = drop (jfrz - jphi + length zs0_out) (\<alpha>s @ xs) in
      do { r \<leftarrow> freeze_meval0_h (\<lambda>\<alpha>. rc j []
                 (Mapping.update (p, m) (replicate j \<alpha>)
                   (Mapping.map_values (\<lambda>_ _. []) db)) \<psi>) (jfrz - jpsi0') \<alpha>s';
           return (zs0_out @ fst r,
             DFrz p m \<phi> \<psi> (jfrz + length zs0_out + length (fst r)) jpsi0'
               (jphi + length xs) (snd r)) }) }"

lemma deval_step_mono[partial_function_mono]:
  assumes rc: "\<And>j ts db \<phi>. mono_Heap (\<lambda>f. RC f j ts db \<phi>)"
  shows "mono_Heap (\<lambda>f. deval_step (RC f) j ts db \<phi>0)"
  by (cases \<phi>0) (auto intro!: partial_function_mono rc)

partial_function (heap) deval :: "nat \<Rightarrow> ts list \<Rightarrow> udatabase \<Rightarrow> dformula \<Rightarrow>
    (utable list \<times> dformula) Heap" where
  [code]: "deval j ts db \<phi>0 = deval_step deval j ts db \<phi>0"

subsection \<open>The state\<close>

fun dfail_nodes :: "dformula \<Rightarrow> nat" and dfail_nodes_list :: "dformula list \<Rightarrow> nat" where
  "dfail_nodes_list [] = 0"
| "dfail_nodes_list (\<phi> # r) = dfail_nodes \<phi> + dfail_nodes_list r"
| "dfail_nodes DFail = 1"
| "dfail_nodes (DAnds ps ns L buf) = dfail_nodes_list L"
| "dfail_nodes (DAnd pl \<phi> pos \<psi> buf) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DAndRel \<phi> conf) = dfail_nodes \<phi>"
| "dfail_nodes (DOr \<phi> \<psi> buf) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DNeg \<phi>) = dfail_nodes \<phi>"
| "dfail_nodes (DExists \<phi> b) = dfail_nodes \<phi>"
| "dfail_nodes (DAgg g0 \<omega> f k pos \<phi>) = dfail_nodes \<phi>"
| "dfail_nodes (DPrev I \<phi> f buf nts) = dfail_nodes \<phi>"
| "dfail_nodes (DNext I \<phi> f nts) = dfail_nodes \<phi>"
| "dfail_nodes (DSince args \<phi> \<psi> buf aux) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DUntil args msk \<phi> \<psi> buf nts t aux) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DAndAssign p t \<phi>) = dfail_nodes \<phi>"
| "dfail_nodes (DLet p m \<phi> \<psi>) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DFrz p m \<phi> \<psi> jfrz jpsi0 jphi \<alpha>s) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DLetPast p m \<phi> \<psi> i buf) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DTrigger dags \<phi> \<psi> dbuf nts daux) = dfail_nodes \<phi> + dfail_nodes \<psi>"
| "dfail_nodes (DAndTrigger pl \<phi> buf1 dags \<phi>' \<psi>' buf2 nts daux) =
    dfail_nodes \<phi> + dfail_nodes \<phi>' + dfail_nodes \<psi>'"
| "dfail_nodes (DMatchP I mr mrs msks \<phi>s buf nts aux) = dfail_nodes_list \<phi>s"
| "dfail_nodes (DMatchF I mr mrs msks \<phi>s buf nts t aux) = dfail_nodes_list \<phi>s"
| "dfail_nodes \<phi> = 0"

type_synonym dstate = "nat \<times> nat \<times> dformula \<times> nat \<times> ts queue"

definition mstep_d :: "udatabase \<times> ts \<Rightarrow> dstate \<Rightarrow>
    ((nat \<times> ts \<times> utable) list \<times> dstate) Heap" where
  "mstep_d tdb sti = (case sti of (i, j, m, n, tq) \<Rightarrow> do {
     (vs, m') \<leftarrow> deval (j + 1) [snd tdb] (fst tdb) m;
     return (case annotate_verdicts_j i (append_queue (snd tdb) tq) vs [] of
       (i', tq', vs') \<Rightarrow> (vs', (i', j + 1, m', n, tq'))) })"

definition minit_safe_d :: "ty Formula.formula \<Rightarrow> dstate Heap" where
  "minit_safe_d \<phi> = do {
     m \<leftarrow> mformula_j_of (meinit0 (Formula.nfv \<phi>) \<phi>);
     d \<leftarrow> dformula_of (Formula.nfv \<phi>) [0..<Formula.nfv \<phi>] m;
     if dfail_nodes d = 0 then return (0, 0, d, Formula.nfv \<phi>, empty_queue)
     else raise (STR ''minit_safe_d: the formula is outside the dense fragment'') }"

(*<*)
end
(*>*)