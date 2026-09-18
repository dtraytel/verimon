(*<*)
theory Dense_Unbox
  imports Dense_Aux
begin
(*>*)

section \<open>Tuples without the option\<close>

text \<open>
  A dense tuple has no holes: @{const dwf_tuple} says so, and after 20.32--20.33 no dense
  operation constructs one -- @{const dwiden}, the only one that ever did, does not occur in the
  generated code any more.  So the @{typ "'a option"} around every field pays for a possibility
  that cannot arise: one indirection on every read, two pattern tests per field in the
  monomorphic tuple comparator, and two words of every field's footprint.

  This theory removes it.  The dense operations are restated over a bare element type \<open>'b\<close>,
  where the existing ones are over @{typ "'a option"}; each generic operation is then proved
  equal to the one it generalises at the option instance, so every theorem of
  @{theory MFODL_Monitor_Imp.Dense} and @{theory MFODL_Monitor_Imp.Dense_Aux} continues to say
  what it said, and the executable evaluator instantiates the same definitions at
  @{typ event_data} instead.

  The operations that read a field rather than move it -- the assignment, the time-point and
  time-stamp terms, the match, the constraint and the aggregation -- cannot be generalised,
  because they go through @{const meval_trm}, which reads @{term "the (v ! x)"}.  They get
  unboxed twins here, each proved to agree with the original on hole-free tuples.
\<close>

subsection \<open>The join, over a bare element type\<close>

definition gindex_step :: "bool list \<Rightarrow> 'b list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> ('b list, 'b list list) mapping" where
  "gindex_step msk b m = (let k = dproj msk b in
     (case Mapping.lookup m k of None \<Rightarrow> Mapping.update k [b] m
      | Some l \<Rightarrow> Mapping.update k (b # l) m))"

definition gindex :: "bool list \<Rightarrow> 'b :: ccompare list set \<Rightarrow>
    ('b list, 'b list list) mapping" where
  "gindex msk B = fold (gindex_step msk) (csorted_list_of_set B) Mapping.empty"

definition gprobe_step :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gprobe_step p msk m a acc = (case Mapping.lookup m (dproj msk a) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>b acc. Set.insert (dmerge p a b) acc) l acc)"

definition gprobe_step_l :: "mrg list \<Rightarrow> bool list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gprobe_step_l p rk m y acc = (case Mapping.lookup m (dproj rk y) of
      None \<Rightarrow> acc
    | Some l \<Rightarrow> fold (\<lambda>x acc. Set.insert (dmerge p x y) acc) l acc)"

definition ggen_join :: "mrg list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow>
    'b :: ccompare list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "ggen_join p lk rk A B =
     (if card A \<le> card B
      then (let m = gindex lk A in fold (gprobe_step_l p rk m) (csorted_list_of_set B) {})
      else (let m = gindex rk B in fold (gprobe_step p lk m) (csorted_list_of_set A) {}))"

fun gbin_join0 :: "djoin_plan \<Rightarrow> 'b :: ccompare list set \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gbin_join0 DJEq A pos B = (if pos then A \<inter> B else A - B)"
| "gbin_join0 DJEmp A pos B = (if pos = ([] \<in> B) then A else {})"
| "gbin_join0 (DJSub msk) A pos B = dsemi msk pos A B"
| "gbin_join0 (DJSup msk) A pos B = (if pos then Set.filter (\<lambda>b. dproj msk b \<in> A) B else A)"
| "gbin_join0 (DJGen p lk rk) A pos B = (if pos then ggen_join p lk rk A B else A)"

definition gbin_join :: "djoin_plan \<Rightarrow> 'b :: ccompare list set \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow>
    'b list set" where
  "gbin_join pl A pos B = (if Set.is_empty A then {}
     else if Set.is_empty B then (if pos then {} else A)
     else gbin_join0 pl A pos B)"

fun gands_pos :: "djoin_plan list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set list \<Rightarrow>
    'b list set" where
  "gands_pos [] t us = t"
| "gands_pos (p # ps) t [] = t"
| "gands_pos (p # ps) t (u # us) = gands_pos ps (gbin_join p t True u) us"

fun gands_neg :: "djoin_plan list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set list \<Rightarrow>
    'b list set" where
  "gands_neg [] t us = t"
| "gands_neg (p # ps) t [] = t"
| "gands_neg (p # ps) t (u # us) = gands_neg ps (gbin_join p t False u) us"

text \<open>At the option instance these are the operations of
  @{theory MFODL_Monitor_Imp.Dense}, so the join's correctness theorems there are theorems
  about these.\<close>

lemma gindex_step_eq: "gindex_step msk = (dindex_step msk :: event_data tuple \<Rightarrow> _)"
  by (intro ext) (simp add: gindex_step_def dindex_step_def)

lemma gindex_eq: "gindex msk (B :: event_data table) = dindex msk B"
  by (simp add: gindex_def dindex_def gindex_step_eq)

lemma gprobe_step_eq: "gprobe_step p msk m (a :: event_data tuple) acc = dprobe_step p msk m a acc"
  by (simp add: gprobe_step_def dprobe_step_def)

lemma gprobe_step_l_eq:
  "gprobe_step_l p rk m (y :: event_data tuple) acc = dprobe_step_l p rk m y acc"
  by (simp add: gprobe_step_l_def dprobe_step_l_def)

lemma ggen_join_eq: "ggen_join p lk rk (A :: event_data table) B = dgen_join p lk rk A B"
  by (simp add: ggen_join_def dgen_join_def gindex_eq empty_table_def
      gprobe_step_eq[abs_def] gprobe_step_l_eq[abs_def])

lemma gbin_join0_eq: "gbin_join0 pl (A :: event_data table) pos B = dbin_join0 pl A pos B"
  by (cases pl) (simp_all add: ggen_join_eq empty_table_def)

lemma gbin_join_eq: "gbin_join pl (A :: event_data table) pos B = dbin_join pl A pos B"
  by (simp add: gbin_join_def dbin_join_def gbin_join0_eq empty_table_def)

lemma gands_pos_eq: "gands_pos ps (t :: event_data table) us = dands_pos ps t us"
  by (induct ps t us rule: gands_pos.induct) (simp_all add: gbin_join_eq)

lemma gands_neg_eq: "gands_neg ps (t :: event_data table) us = dands_neg ps t us"
  by (induct ps t us rule: gands_neg.induct) (simp_all add: gbin_join_eq)

subsection \<open>The Since structure, over a bare element type\<close>

text \<open>
  The index algebra of @{theory MFODL_Monitor_Imp.Dense_Aux} -- @{const didx}, @{const didx_union},
  @{const didx_minus}, @{const dsemi_idx} -- is already stated over @{typ "'b list"}; only the
  state itself, the operation that consults the arguments to decide whether the index is live,
  and @{const valid_tuple} carry the option, and only in their signatures.  They are restated here
  and the six operations with them.
\<close>

type_synonym 'b gmsaux = "ts \<times> ts \<times> bool list \<times>
  (ts \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times> 'b list set \<times>
  ('b list, 'b list set) mapping \<times> ('b list, ts) mapping \<times>
  ('b list, 'b list set) mapping \<times> ('b list, ts) mapping"

definition gvalid_tuple :: "('b list, ts) mapping \<Rightarrow> ts \<times> 'b list \<Rightarrow> bool" where
  "gvalid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
     | Some t' \<Rightarrow> t \<ge> t')"

definition gidx_upd :: "args \<Rightarrow> (unit \<Rightarrow> ('b list, 'b list set) mapping) \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "gidx_upd args w = (if didx_live args then w () else Mapping.empty)"

definition ginit_msaux :: "args \<Rightarrow> bool list \<Rightarrow> 'b gmsaux" where
  "ginit_msaux args msk = (0, 0, msk, empty_queue, empty_queue, {},
     Mapping.empty, Mapping.empty, Mapping.empty, Mapping.empty)"

fun gshift_end :: "args \<Rightarrow> ts \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux" where
  "gshift_end args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
     (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
     (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
     (t, gc, msk, data_prev', data_in, table_in - del,
      gidx_upd args (\<lambda>_. didx_minus idx_in (didx msk del)), tuple_in, idx_since, tuple_since))"

fun gadd_new_ts_msaux' :: "args \<Rightarrow> ts \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux" where
  "gadd_new_ts_msaux' args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
     data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
     (tuple_in, add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple tuple_since (t, as)}))
        move (tuple_in, {}) in
     (nt, gc, msk, data_prev, data_in, table_in \<union> add,
      gidx_upd args (\<lambda>_. didx_union idx_in (didx msk add)), tuple_in, idx_since, tuple_since))"

definition gadd_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux" where
  "gadd_new_ts_msaux args nt daux = gadd_new_ts_msaux' args nt (gshift_end args nt daux)"

fun ggc_msaux :: "args \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux" where
  "ggc_msaux args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
     tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
     (nt, nt, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      gidx_upd args (\<lambda>_. didx msk (Mapping.keys tuple_since')), tuple_since'))"

fun gadd_new_table_msaux :: "args \<Rightarrow> 'b list set \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux" where
  "gadd_new_table_msaux args X (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let X' = minus_keys X tuple_since;
     tuple_since' = upd_set tuple_since (\<lambda>_. t) X';
     idx_since' = gidx_upd args (\<lambda>_. didx_union idx_since (didx msk X')) in
     (if memL (args_ivl args) 0 then
        (t, gc, msk, data_prev, append_queue (t, X) data_in, table_in \<union> X,
         gidx_upd args (\<lambda>_. didx_union idx_in (didx msk X)), upd_set tuple_in (\<lambda>_. t) X,
         idx_since', tuple_since')
      else (t, gc, msk, append_queue (t, X) data_prev, data_in, table_in, idx_in, tuple_in,
         idx_since', tuple_since')))"

fun gresult_msaux :: "args \<Rightarrow> 'b gmsaux \<Rightarrow> 'b list set" where
  "gresult_msaux args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) = table_in"

fun gjoin_msaux :: "args \<Rightarrow> 'b list set \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux" where
  "gjoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let pos = args_pos args in
     (if \<forall>i \<in> set msk. \<not> i then
        (let take_all = (([] \<in> Y) = pos) in
         (t, gc, msk, data_prev, data_in,
          if take_all then table_in else {},
          if take_all then idx_in else Mapping.empty,
          if take_all then tuple_in else Mapping.empty,
          if take_all then idx_since else Mapping.empty,
          if take_all then tuple_since else Mapping.empty))
      else if \<forall>i \<in> set msk. i then
        (let in_del = (if pos then table_in - Y else table_in \<inter> Y);
         tuple_in' = mapping_delete_set tuple_in in_del;
         tuple_since' = Mapping.filter (\<lambda>as _. (as \<in> Y) = pos) tuple_since in
         (t, gc, msk, data_prev, data_in, table_in - in_del, Mapping.empty, tuple_in',
          Mapping.empty, tuple_since'))
      else
        (let in_del = dsemi_idx msk (\<not> pos) idx_in Y;
         since_del = dsemi_idx msk (\<not> pos) idx_since Y in
         (t, gc, msk, data_prev, data_in, table_in - in_del,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_in, mapping_delete_set tuple_in in_del,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_since,
          mapping_delete_set tuple_since since_del))))"

fun ggc_join_msaux :: "args \<Rightarrow> 'b list set \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux" where
  "ggc_join_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc)
     then gjoin_msaux args Y (ggc_msaux args (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))
     else gjoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
       idx_since, tuple_since))"

text \<open>At the option instance, the six operations are the ones whose validity
  @{theory MFODL_Monitor_Imp.Dense_Aux} establishes.\<close>

lemma gvalid_tuple_eq: "gvalid_tuple (m :: (event_data tuple, ts) mapping) = valid_tuple m"
  by (intro ext) (simp add: gvalid_tuple_def valid_tuple_def)

lemma gidx_upd_eq:
  "gidx_upd args (w :: unit \<Rightarrow> (event_data tuple, event_data table) mapping) = didx_upd args w"
  by (simp add: gidx_upd_def didx_upd_def)

lemma ginit_msaux_eq: "ginit_msaux args msk = (dinit_msaux args msk :: event_data dmsaux)"
  by (simp add: ginit_msaux_def dinit_msaux_def)

lemma gshift_end_eq: "gshift_end args nt (d :: event_data dmsaux) = dshift_end args nt d"
  by (cases d rule: dmsaux_cases) (simp add: Let_def gidx_upd_eq split: prod.splits)

lemma gadd_new_ts_msaux'_eq:
  "gadd_new_ts_msaux' args nt (d :: event_data dmsaux) = dadd_new_ts_msaux' args nt d"
  by (cases d rule: dmsaux_cases)
    (simp add: Let_def gidx_upd_eq gvalid_tuple_eq split: prod.splits)

lemma gadd_new_ts_msaux_eq:
  "gadd_new_ts_msaux args nt (d :: event_data dmsaux) = dadd_new_ts_msaux args nt d"
  by (simp add: gadd_new_ts_msaux_def dadd_new_ts_msaux_def gshift_end_eq gadd_new_ts_msaux'_eq)

lemma ggc_msaux_eq: "ggc_msaux args (d :: event_data dmsaux) = dgc_msaux args d"
  by (cases d rule: dmsaux_cases) (simp add: Let_def gidx_upd_eq)

lemma gadd_new_table_msaux_eq:
  "gadd_new_table_msaux args X (d :: event_data dmsaux) = dadd_new_table_msaux args X d"
  by (cases d rule: dmsaux_cases) (simp add: Let_def gidx_upd_eq)

lemma gresult_msaux_eq: "gresult_msaux args (d :: event_data dmsaux) = dresult_msaux args d"
  by (cases d rule: dmsaux_cases) simp

lemma gjoin_msaux_eq: "gjoin_msaux args Y (d :: event_data dmsaux) = djoin_msaux args Y d"
  by (cases d rule: dmsaux_cases) (simp add: Let_def)

lemma ggc_join_msaux_eq: "ggc_join_msaux args Y (d :: event_data dmsaux) = dgc_join_msaux args Y d"
  by (cases d rule: dmsaux_cases) (simp add: gjoin_msaux_eq ggc_msaux_eq)

subsection \<open>The Until structure, over a bare element type\<close>

text \<open>
  The deque structure of @{theory MFODL_Monitor_Devel.Optimized_Until_Deque} was monomorphised at
  @{typ event_data} for code generation (7), so it is restated here rather than instantiated.
  One thing genuinely changes: @{const eval_step_dq} passes the finished table through
  @{const eval_args_agg}, which is an aggregation over @{typ event_data} and cannot be generic.
  The dense fragment only ever builds an Until node when @{term "args_agg args = None"}, where
  that call is the identity, so the generic step omits it and the agreement lemmas below assume
  it.
\<close>

type_synonym 'b gmuaux = "tp \<times> ts queue \<times> ('b list set \<times> (ts + tp)) queue \<times> nat \<times>
  bool list \<times> bool list \<times> 'b list set \<times> ('b list, tp) mapping \<times>
  ('b list, ts + tp) mapping dq \<times> ts dq \<times> 'b list set list"

type_synonym 'b guntil_acc = "'b list set \<times> ('b list, ts + tp) mapping dq \<times> 'b list set"

definition ginit_dq :: "args \<Rightarrow> 'b gmuaux" where
  "ginit_dq args = (0, empty_queue, empty_queue, 0,
     join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
     {}, Mapping.empty, dq_push Mapping.empty dq_empty, dq_empty, [])"

fun geval_step_dq :: "args \<Rightarrow> 'b gmuaux \<Rightarrow> 'b gmuaux" where
  "geval_step_dq args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_nth a2_dq 0;
        I = args_ivl args;
        T = result;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue
           (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = \<Union>(set (map fst taken));
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of
              Some tstp \<Rightarrow> (\<not> ts_tp_lt I ts' (tp - len + 1) tstp) | None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        a2_dq' = dq_tl a2_dq;
        m' = dq_nth a2_dq' 0;
        result' = if len = 1 then {} else (result - to_del) \<union> Mapping.keys m';
        a2_dq = dq_upd a2_dq' 0 (if len = 1 then Mapping.empty
          else Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m');
        tstp_dq = dq_tl tstp_dq in
        (tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, T # dn)))"

fun gshift_dq :: "args \<Rightarrow> ts \<Rightarrow> 'b gmuaux \<Rightarrow> 'b gmuaux" where
  "gshift_dq args nt (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. geval_step_dq args aux) (tp, tss', tables, len, maskL, maskR,
      result, a1_map, a2_dq, tstp_dq, dn) (linearize tss_queue))"

fun geval_dq :: "args \<Rightarrow> ts \<Rightarrow> 'b gmuaux \<Rightarrow> 'b list set list \<times> 'b gmuaux" where
  "geval_dq args nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
       gshift_dq args nt aux in
    (rev dn, (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, [])))"

definition guntil_step_dq :: "(nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> nat \<Rightarrow> nat \<times> 'b list \<Rightarrow>
    'b guntil_acc \<Rightarrow> 'b guntil_acc" where
  "guntil_step_dq P d t0 p acc = (case acc of (tbl, a2, res) \<Rightarrow> if P (fst p) then
     (Set.insert (snd p) tbl, upd_nested_step_dq t0 d (max_tstp d) p a2,
      if fst p = t0 then Set.insert (snd p) res else res)
   else acc)"

definition guntil_elem_step_dq :: "('b list, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    bool \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'b list \<Rightarrow> 'b guntil_acc \<Rightarrow> 'b guntil_acc" where
  "guntil_elem_step_dq a1_map msk pos tp len inz P d as acc =
    (let acc' = (if inz then guntil_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (dproj msk as) of
        None \<Rightarrow> (if \<not>pos then guntil_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> guntil_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as)
          else (max (tp - len) (tp' + 1), as)) acc')"

definition gadd_new_dq :: "args \<Rightarrow> bool list \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    'b gmuaux \<Rightarrow> 'b gmuaux" where
  "gadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn) =
       gshift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (\<lambda>t. memL I (nt - dq_nth tstp_dq (t - (tp - len))));
     (tbl, a2_dq', result') = fold (guntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csorted_list_of_set rel2) ({}, a2_dq, result);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
       (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, dn))"

text \<open>At the option instance, and where the node has no aggregation, these are the operations of
  the verified structure.\<close>

lemma ginit_dq_eq: "ginit_dq args = (init_dq args :: event_data mmuaux_dq)"
  by (simp add: ginit_dq_def init_dq_def)

lemma geval_step_dq_eq:
  assumes "args_agg args = None"
  shows "geval_step_dq args (d :: event_data mmuaux_dq) = eval_step_dq args d"
  by (cases d rule: mmuaux_dq_cases)
    (simp add: Let_def eval_args_agg_def assms split: prod.splits option.splits)

lemma gshift_dq_eq:
  assumes "args_agg args = None"
  shows "gshift_dq args nt (d :: event_data mmuaux_dq) = shift_dq args nt d"
proof (cases d rule: mmuaux_dq_cases)
  case (1 tp tss tables len maskL maskR result a1_map a2_dq tstp_dq dn)
  have "foldl (\<lambda>aux _. geval_step_dq args aux) z xs = foldl (\<lambda>aux _. eval_step_dq args aux) z xs"
    for z :: "event_data mmuaux_dq" and xs :: "ts list"
    by (induct xs arbitrary: z) (simp_all add: geval_step_dq_eq[OF assms])
  then show ?thesis unfolding 1 by (simp add: Let_def split: prod.splits)
qed

lemma geval_dq_eq:
  assumes "args_agg args = None"
  shows "geval_dq args nt (d :: event_data mmuaux_dq) = eval_dq args nt d"
  by (simp add: gshift_dq_eq[OF assms] split: prod.splits)

lemma guntil_step_dq_eq:
  "guntil_step_dq P d t0 (p :: nat \<times> event_data tuple) acc = until_step_dq P d t0 p acc"
  by (simp add: guntil_step_dq_def until_step_dq_def)

lemma guntil_elem_step_dq_eq:
  "guntil_elem_step_dq a1_map msk pos tp len inz P d (as :: event_data tuple) acc
   = duntil_elem_step_dq a1_map msk pos tp len inz P d as acc"
  by (simp add: guntil_elem_step_dq_def duntil_elem_step_dq_def guntil_step_dq_eq
      split: option.splits)

lemma gadd_new_dq_eq:
  assumes "args_agg args = None"
  shows "gadd_new_dq args msk rel1 rel2 nt (d :: event_data mmuaux_dq)
       = dadd_new_dq args msk rel1 rel2 nt d"
  by (simp add: gadd_new_dq_def dadd_new_dq_def gshift_dq_eq[OF assms]
      guntil_elem_step_dq_eq[abs_def] split: prod.splits)

subsection \<open>The operations that read a field\<close>

text \<open>
  These cannot be generalised, because they look inside a field.  Each gets a twin that reads the
  field directly, and a lemma saying the twin agrees with the original.  \<open>deopt\<close> strips the option
  and \<open>reopt\<close> puts it back; on hole-free tuples they are inverse, which is what the agreement
  lemmas are stated against.
\<close>

definition deopt :: "'a tuple \<Rightarrow> 'a list" where
  "deopt = map the"

definition reopt :: "'a list \<Rightarrow> 'a tuple" where
  "reopt = map Some"

definition deopt_table :: "'a table \<Rightarrow> 'a list set" where
  "deopt_table X = deopt ` X"

definition reopt_table :: "'a list set \<Rightarrow> 'a table" where
  "reopt_table X = reopt ` X"

lemma deopt_simps[simp]:
  "deopt [] = []" "deopt (a # x) = the a # deopt x"
  "deopt (xs @ ys) = deopt xs @ deopt ys"
  "deopt (take p x) = take p (deopt x)" "deopt (drop p x) = drop p (deopt x)"
  by (simp_all add: deopt_def drop_map take_map)

lemma reopt_simps[simp]: "reopt [] = []" "reopt (a # x) = Some a # reopt x"
  by (simp_all add: reopt_def)

lemma deopt_reopt[simp]: "deopt (reopt xs) = xs"
  by (simp add: deopt_def reopt_def comp_def)

lemma reopt_deopt: "dwf_tuple n x \<Longrightarrow> reopt (deopt x) = x"
  by (auto simp: deopt_def reopt_def dwf_tuple_def list_eq_iff_nth_eq)

lemma deopt_table_reopt_table[simp]: "deopt_table (reopt_table X) = X"
  by (force simp: deopt_table_def reopt_table_def)

lemma length_deopt[simp]: "length (deopt x) = length x"
  by (simp add: deopt_def)

lemma length_reopt[simp]: "length (reopt xs) = length xs"
  by (simp add: reopt_def)

lemma nth_deopt: "i < length x \<Longrightarrow> deopt x ! i = the (x ! i)"
  by (simp add: deopt_def)

fun umeval_trm :: "Formula.trm \<Rightarrow> event_data list \<Rightarrow> event_data" where
  "umeval_trm (Formula.Var x) v = v ! x"
| "umeval_trm (Formula.Const x) v = x"
| "umeval_trm (Formula.Plus x y) v = umeval_trm x v + umeval_trm y v"
| "umeval_trm (Formula.Minus x y) v = umeval_trm x v - umeval_trm y v"
| "umeval_trm (Formula.UMinus x) v = - umeval_trm x v"
| "umeval_trm (Formula.Mult x y) v = umeval_trm x v * umeval_trm y v"
| "umeval_trm (Formula.Div x y) v = umeval_trm x v div umeval_trm y v"
| "umeval_trm (Formula.Mod x y) v = umeval_trm x v mod umeval_trm y v"
| "umeval_trm (Formula.F2i x) v = EInt (integer_of_event_data (umeval_trm x v))"
| "umeval_trm (Formula.I2f x) v = EFloat (double_of_event_data (umeval_trm x v))"

lemma umeval_trm_deopt:
  "Formula.fv_trm t \<subseteq> {i. i < length x} \<Longrightarrow> umeval_trm t (deopt x) = meval_trm t x"
  by (induct t) (simp_all add: nth_deopt)

definition uassign1 :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data list \<Rightarrow> event_data list" where
  "uassign1 p t d = take p d @ umeval_trm t d # drop p d"

definition uassign :: "nat \<Rightarrow> Formula.trm \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "uassign p t D = uassign1 p t ` D"

lemma uassign1_deopt:
  "Formula.fv_trm t \<subseteq> {i. i < length x} \<Longrightarrow> uassign1 p t (deopt x) = deopt (dassign1 p t x)"
  by (simp add: uassign1_def dassign1_def umeval_trm_deopt)

fun umtrm :: "mtrm \<Rightarrow> event_data \<Rightarrow> event_data list set" where
  "umtrm (MVar v) x = {[x]}"
| "umtrm (MConst c) x = (if c = x then {[]} else {})"

lemma umtrm_deopt: "umtrm mt x = deopt_table (dmtrm mt x)"
  by (cases mt) (simp_all add: deopt_table_def deopt_def unit_table_def empty_table_def)

fun umatch :: "Formula.trm list \<Rightarrow> event_data list \<Rightarrow> (nat \<rightharpoonup> event_data) option" where
  "umatch [] [] = Some Map.empty"
| "umatch (Formula.Const x # ts) (y # ys) = (if x = y then umatch ts ys else None)"
| "umatch (Formula.Var x # ts) (y # ys) = (case umatch ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "umatch _ _ = None"

lemma umatch_reopt: "umatch tms xs = match tms (reopt xs)"
  by (induct tms xs rule: umatch.induct) auto

lemma umatch_deopt: "dwf_tuple (length x) x \<Longrightarrow> umatch tms (deopt x) = match tms x"
  by (simp add: umatch_reopt reopt_deopt)

definition umatch_table :: "Formula.trm list \<Rightarrow> cols \<Rightarrow> event_data list set \<Rightarrow>
    event_data list set" where
  "umatch_table tms cs X =
     Option.these ((\<lambda>x. map_option (\<lambda>f. map (\<lambda>c. the (f c)) cs) (umatch tms x)) ` X)"

definition ueval_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow>
    event_data list \<Rightarrow> bool" where
  "ueval_constraint conf x = (case conf of (t1, p, c, t2) \<Rightarrow>
     eval_constraint0 c (umeval_trm t1 x) (umeval_trm t2 x) = p)"

lemma ueval_constraint_deopt:
  "Formula.fv_trm (fst conf) \<subseteq> {i. i < length x} \<Longrightarrow>
   Formula.fv_trm (snd (snd (snd conf))) \<subseteq> {i. i < length x} \<Longrightarrow>
   ueval_constraint conf (deopt x) = eval_constraint conf x"
  by (cases conf) (simp add: ueval_constraint_def umeval_trm_deopt)

definition uagg_values :: "Formula.trm \<Rightarrow> event_data list set \<Rightarrow> (event_data \<times> enat) set" where
  "uagg_values f G = (let vals = cluster (Some \<circ> umeval_trm f) G in
     (\<lambda>v. case Mapping.lookup vals v of Some S \<Rightarrow> (v, ecard S)) ` Mapping.keys vals)"

definition uagg :: "bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> Formula.trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    event_data list set \<Rightarrow> event_data list set" where
  "uagg g0 \<omega> f k pos rel =
     (if g0 \<and> Set.is_empty rel then {[eval_agg_op \<omega> {}]}
      else (let groups = cluster (Some \<circ> drop k) rel in
        (\<lambda>g. case Mapping.lookup groups g of
                None \<Rightarrow> g
              | Some G \<Rightarrow> take pos g @ eval_agg_op \<omega> (uagg_values f G) # drop pos g)
          ` Mapping.keys groups))"

(*<*)
end
(*>*)
