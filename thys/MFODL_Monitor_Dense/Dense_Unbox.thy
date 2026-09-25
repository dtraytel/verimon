(*<*)
theory Dense_Unbox
  imports Dense_Until_Gen Since_Evt Until_Evt
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
  @{theory MFODL_Monitor_Dense.Dense} and @{theory MFODL_Monitor_Dense.Dense_Aux} continues to say
  what it said, and the executable evaluator instantiates the same definitions at
  @{typ event_data} instead.

  The operations that read a field rather than move it -- the assignment, the time-point and
  time-stamp terms, the match, the constraint and the aggregation -- cannot be generalised,
  because they go through @{const meval_trm}, which reads @{term "the (v ! x)"}.  They get
  unboxed twins here, each proved to agree with the original on hole-free tuples.
\<close>

text \<open>The executable monitor runs at @{typ event_data}, and a table of it is this.\<close>

type_synonym utable = "event_data list set"

subsection \<open>The join, over a bare element type\<close>

definition gindex_step :: "bool list \<Rightarrow> 'b list \<Rightarrow>
    ('b list, 'b list list) mapping \<Rightarrow> ('b list, 'b list list) mapping" where
  "gindex_step msk b m = (let k = dproj msk b in
     (case Mapping.lookup m k of None \<Rightarrow> Mapping.update k [b] m
      | Some l \<Rightarrow> Mapping.update k (b # l) m))"

definition gindex :: "bool list \<Rightarrow> 'b :: ccompare list set \<Rightarrow>
    ('b list, 'b list list) mapping" where
  "gindex msk B = fold (gindex_step msk) (csl B) Mapping.empty"

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
      then (let m = gindex lk A in fold (gprobe_step_l p rk m) (csl B) {})
      else (let m = gindex rk B in fold (gprobe_step p lk m) (csl A) {}))"

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
  @{theory MFODL_Monitor_Dense.Dense}, so the join's correctness theorems there are theorems
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

definition gmulti_join :: "djoin_plan list \<Rightarrow> djoin_plan list \<Rightarrow> 'b :: ccompare list set list \<Rightarrow>
    'b list set" where
  "gmulti_join ps ns us = (case us of [] \<Rightarrow> {}
     | t # r \<Rightarrow> gands_neg ns (gands_pos ps t (take (length ps) r)) (drop (length ps) r))"

lemma gmulti_join_eq: "gmulti_join ps ns (us :: event_data table list) = dmulti_join ps ns us"
  by (simp add: gmulti_join_def dmulti_join_def gands_pos_eq gands_neg_eq empty_table_def
      split: list.splits)

text \<open>What the join computes, over a bare element type.  The proofs are those of
  @{theory MFODL_Monitor_Dense.Dense} with the option gone; they are needed at the element type
  the executable evaluator uses, where an equality with the option instance says nothing.\<close>

lemma ID_ccompare_ed: "ID CCOMPARE(event_data list) \<noteq> None"
  by (simp add: ccompare_list_def ccompare_event_data_def ID_def split: option.splits)

lemma set_csorted_list_of_set_ed:
  "finite (X :: event_data list set) \<Longrightarrow> set (csorted_list_of_set X) = X"
  using ID_ccompare_ed by (subst csorted_list_of_set_split) auto

lemma set_csl_ed: "finite (X :: event_data list set) \<Longrightarrow> set (csl X) = X"
  by (simp add: csl_finite set_csorted_list_of_set_ed)

definition gbucket :: "('b list, 'b list list) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list list" where
  "gbucket m k = (case Mapping.lookup m k of None \<Rightarrow> [] | Some l \<Rightarrow> l)"

lemma gbucket_gindex_step:
  "gbucket (gindex_step msk x m) k = (if dproj msk x = k then x # gbucket m k else gbucket m k)"
  by (auto simp: gbucket_def gindex_step_def Let_def Mapping.lookup_update'
      split: option.splits)

lemma gindex_fold_lookup:
  "set (gbucket (fold (gindex_step msk) xs m) k)
   = {b \<in> set xs. dproj msk b = k} \<union> set (gbucket m k)"
  by (induct xs arbitrary: m) (auto simp: gbucket_gindex_step)

lemma gindex_lookup:
  assumes "set (csl B) = B"
  shows "set (gbucket (gindex msk B) k) = {b \<in> B. dproj msk b = k}"
  using gindex_fold_lookup[of msk "csl B" Mapping.empty k] assms
  by (simp add: gindex_def gbucket_def Mapping.lookup_empty)

lemma gprobe_fold:
  "fold (gprobe_step p lk m) xs acc
   = acc \<union> (\<Union>a \<in> set xs. (\<lambda>b. dmerge p a b) ` set (gbucket m (dproj lk a)))"
  by (induct xs arbitrary: acc)
    (auto simp: gprobe_step_def gbucket_def fold_insert_image split: option.splits)

lemma gprobe_l_fold:
  "fold (gprobe_step_l p rk m) ys acc
   = acc \<union> (\<Union>y \<in> set ys. (\<lambda>x. dmerge p x y) ` set (gbucket m (dproj rk y)))"
  by (induct ys arbitrary: acc)
    (auto simp: gprobe_step_l_def gbucket_def fold_insert_image split: option.splits)

lemma ggen_join_spec:
  assumes cA: "set (csl A) = A" and cB: "set (csl B) = B"
  shows "ggen_join p lk rk A B
       = {dmerge p a b | a b. a \<in> A \<and> b \<in> B \<and> dproj lk a = dproj rk b}"
  by (auto simp: ggen_join_def Let_def gprobe_fold gprobe_l_fold
      gindex_lookup[OF cA] gindex_lookup[OF cB] cA cB) force

subsection \<open>The Since structure, over a bare element type\<close>

text \<open>
  The index algebra of @{theory MFODL_Monitor_Dense.Dense_Aux} -- @{const didx}, @{const didx_union},
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
    (if memL (args_ivl args) 0 then
       (t, gc, msk, data_prev, append_queue (t, X) data_in, table_in \<union> X,
        gidx_upd args (\<lambda>_. didx_union idx_in (didx msk X)), upd_set tuple_in (\<lambda>_. t) X,
        idx_since, tuple_since)
     else
       (let X' = minus_keys X tuple_since;
        tuple_since' = upd_set tuple_since (\<lambda>_. t) X';
        idx_since' = gidx_upd args (\<lambda>_. didx_union idx_since (didx msk X')) in
        (t, gc, msk, append_queue (t, X) data_prev, data_in, table_in, idx_in, tuple_in,
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
    (if \<not> memL (args_ivl args) 0 \<and> \<not> memR (args_ivl args) (t - gc)
     then gjoin_msaux args Y (ggc_msaux args (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))
     else gjoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
       idx_since, tuple_since))"

text \<open>At the option instance, the six operations are the ones whose validity
  @{theory MFODL_Monitor_Dense.Dense_Aux} establishes.\<close>

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
  "gadd_new_table_msaux args X (d :: event_data dmsaux) = dadd_new_table_lz args X d"
  by (cases d rule: dmsaux_cases) (simp add: Let_def gidx_upd_eq)

lemma gresult_msaux_eq: "gresult_msaux args (d :: event_data dmsaux) = dresult_msaux args d"
  by (cases d rule: dmsaux_cases) simp

lemma gjoin_msaux_eq: "gjoin_msaux args Y (d :: event_data dmsaux) = djoin_msaux args Y d"
  by (cases d rule: dmsaux_cases) (simp add: Let_def)

lemma ggc_join_msaux_eq: "ggc_join_msaux args Y (d :: event_data dmsaux) = dgc_join_lz args Y d"
  by (cases d rule: dmsaux_cases) (simp add: dgc_join_lz_def gjoin_msaux_eq ggc_msaux_eq)

subsection \<open>The Until structure, over a bare element type\<close>

text \<open>The generic Until structure lives in @{theory MFODL_Monitor_Dense.Dense_Until_Gen}, where the
  verified dense evaluator runs it too.\<close>

subsection \<open>The closed-left-operand structures, over a bare element type\<close>

text \<open>
  The two structures for a closed left operand -- the Since's sliding window of
  @{theory MFODL_Monitor_Dense.Since_Evt} and the Until's of @{theory MFODL_Monitor_Dense.Until_Evt} -- are queues of tables and a
  multiset of tuples held as a count mapping.  They touch no field, so they generalise as the
  others did.
\<close>

definition gevt_add :: "'b :: ccompare list set \<Rightarrow> ('b list, nat) mapping \<times> 'b list set \<Rightarrow>
    ('b list, nat) mapping \<times> 'b list set" where
  "gevt_add T cc = fold (\<lambda>t (c, s). case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, Set.insert t s)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, s)) (csorted_list_of_set T) cc"

definition gevt_del :: "'b :: ccompare list set \<Rightarrow> ('b list, nat) mapping \<times> 'b list set \<Rightarrow>
    ('b list, nat) mapping \<times> 'b list set" where
  "gevt_del T cc = fold (\<lambda>t (c, s). case Mapping.lookup c t of
       None \<Rightarrow> (c, s)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, Set.remove t s)
                  else (Mapping.update t (k - 1) c, s))) (csorted_list_of_set T) cc"

lemma gevt_add_eq: "gevt_add (T :: event_data table) cc = evt_add T cc"
  by (simp add: gevt_add_def evt_add_def)

lemma gevt_del_eq: "gevt_del (T :: event_data table) cc = evt_del T cc"
  by (simp add: gevt_del_def evt_del_def)

type_synonym 'b gsevtaux = "ts \<times> (ts \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times>
  ('b list, nat) mapping \<times> 'b list set"

function gsevt_move :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'b :: ccompare list set) queue \<Rightarrow>
    (ts \<times> 'b list set) queue \<Rightarrow> ('b list, nat) mapping \<Rightarrow> 'b list set \<Rightarrow>
    (ts \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times>
    ('b list, nat) mapping \<times> 'b list set" where
  "gsevt_move args nt pend win cnt cur =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cnt, cur)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then (case gevt_add (snd e) (cnt, cur) of (cnt', cur') \<Rightarrow>
                       gsevt_move args nt (tl_queue pend') (append_queue e win) cnt' cur')
               else gsevt_move args nt (tl_queue pend') win cnt cur)
         else (pend', win, cnt, cur)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, pend, win, cnt, cur). length (linearize pend))")
     (fastforce split: prod.splits)+

declare gsevt_move.simps[simp del]

function gsevt_expire :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'b :: ccompare list set) queue \<Rightarrow>
    ('b list, nat) mapping \<Rightarrow> 'b list set \<Rightarrow>
    (ts \<times> 'b list set) queue \<times> ('b list, nat) mapping \<times> 'b list set" where
  "gsevt_expire args nt win cnt cur =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cnt, cur)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cnt, cur)
         else (case gevt_del (snd e) (cnt, cur) of (cnt', cur') \<Rightarrow>
                 gsevt_expire args nt (tl_queue win') cnt' cur')))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, win, cnt, cur). length (linearize win))")
     (fastforce split: prod.splits)+

declare gsevt_expire.simps[simp del]

definition ginit_sevt :: "args \<Rightarrow> 'b gsevtaux" where
  "ginit_sevt args = (0, empty_queue, empty_queue, Mapping.empty, {})"

definition gadd_new_ts_sevt :: "args \<Rightarrow> ts \<Rightarrow> 'b :: ccompare gsevtaux \<Rightarrow> 'b gsevtaux" where
  "gadd_new_ts_sevt args nt aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (case gsevt_move args nt pend win cnt cur of (pend', win', cnt', cur') \<Rightarrow>
      (case gsevt_expire args nt win' cnt' cur' of (win'', cnt'', cur'') \<Rightarrow>
        (nt, pend', win'', cnt'', cur''))))"

definition gjoin_sevt :: "args \<Rightarrow> 'b list set \<Rightarrow> 'b gsevtaux \<Rightarrow> 'b gsevtaux" where
  "gjoin_sevt args X aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, Mapping.empty, {})))"

definition gadd_new_table_sevt :: "args \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b gsevtaux \<Rightarrow>
    'b gsevtaux" where
  "gadd_new_table_sevt args X aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (case gevt_add X (cnt, cur) of (cnt', cur') \<Rightarrow>
              (t, pend, append_queue (t, X) win, cnt', cur'))
      else (t, append_queue (t, X) pend, win, cnt, cur)))"

definition gresult_sevt :: "args \<Rightarrow> 'b gsevtaux \<Rightarrow> 'b list set" where
  "gresult_sevt args aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow> cur)"

lemma gsevt_move_eq:
  "gsevt_move args nt (pend :: (ts \<times> event_data table) queue) win cnt cur
   = sevt_move args nt pend win cnt cur"
  by (induct args nt pend win cnt cur rule: gsevt_move.induct)
    (simp add: gsevt_move.simps sevt_move.simps gevt_add_eq split: prod.splits option.splits)

lemma gsevt_expire_eq:
  "gsevt_expire args nt (win :: (ts \<times> event_data table) queue) cnt cur
   = sevt_expire args nt win cnt cur"
  by (induct args nt win cnt cur rule: gsevt_expire.induct)
    (simp add: gsevt_expire.simps sevt_expire.simps gevt_del_eq split: prod.splits option.splits)

lemma ginit_sevt_eq: "ginit_sevt args = (init_sevt args :: sevtaux)"
  by (simp add: ginit_sevt_def init_sevt_def)

lemma gadd_new_ts_sevt_eq:
  "gadd_new_ts_sevt args nt (aux :: sevtaux) = add_new_ts_sevt args nt aux"
  by (simp add: gadd_new_ts_sevt_def add_new_ts_sevt_def gsevt_move_eq gsevt_expire_eq
      split: prod.splits)

lemma gjoin_sevt_eq: "gjoin_sevt args X (aux :: sevtaux) = join_sevt args X aux"
  by (simp add: gjoin_sevt_def join_sevt_def split: prod.splits)

lemma gadd_new_table_sevt_eq:
  "gadd_new_table_sevt args X (aux :: sevtaux) = add_new_table_sevt args X aux"
  by (simp add: gadd_new_table_sevt_def add_new_table_sevt_def gevt_add_eq split: prod.splits)

lemma gresult_sevt_eq: "gresult_sevt args (aux :: sevtaux) = result_sevt args aux"
  by (simp add: gresult_sevt_def result_sevt_def split: prod.splits)

type_synonym 'b gevt_entry = "ts \<times> 'b list set \<times> bool"

type_synonym 'b gevtaux = "ts queue \<times> 'b gevt_entry queue \<times> 'b gevt_entry queue \<times> nat \<times> bool \<times>
  ('b list, nat) mapping \<times> 'b list set \<times> 'b list set list"

function gevt_extend :: "args \<Rightarrow> ts \<Rightarrow> 'b :: ccompare gevt_entry queue \<Rightarrow> 'b gevt_entry queue \<Rightarrow>
    bool \<Rightarrow> ('b list, nat) mapping \<Rightarrow> 'b list set \<Rightarrow>
    'b gevt_entry queue \<times> 'b gevt_entry queue \<times> bool \<times> ('b list, nat) mapping \<times> 'b list set" where
  "gevt_extend args ts0 win rest bend cnt cur =
     (if \<not> bend then (win, rest, bend, cnt, cur)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cnt, cur)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then (case gevt_add (fst (snd e)) (cnt, cur) of (cnt', cur') \<Rightarrow>
                         gevt_extend args ts0 (append_queue e win) (tl_queue rest')
                           (snd (snd e)) cnt' cur')
                 else (win, rest', bend, cnt, cur))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, ts0, win, rest, bend, cnt, cur). length (linearize rest))")
     (fastforce split: prod.splits)+

declare gevt_extend.simps[simp del]

definition ginit_evt :: "args \<Rightarrow> 'b gevtaux" where
  "ginit_evt args = (empty_queue, empty_queue, empty_queue, 0, True, Mapping.empty, {}, [])"

definition glength_evt :: "args \<Rightarrow> 'b gevtaux \<Rightarrow> nat" where
  "glength_evt args aux = (case aux of (nts, win, rest, len, bend, cnt, cur, dn) \<Rightarrow>
     length dn + len)"

definition gevt_step :: "args \<Rightarrow> ts \<Rightarrow> 'b :: ccompare gevtaux \<Rightarrow> 'b gevtaux" where
  "gevt_step args ts0 aux = (case aux of (nts, win, rest, len, bend, cnt, cur, dn) \<Rightarrow>
     (case gevt_extend args ts0 win rest bend cnt cur of (win, rest, bend, cnt, cur) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow>
             (case safe_hd rest of
                (None, rest') \<Rightarrow>
                  (tl_queue nts, win', rest', len - 1, bend, cnt, cur, {} # dn)
              | (Some uu, rest') \<Rightarrow>
                  (tl_queue nts, win', tl_queue rest', len - 1, bend, cnt, cur, {} # dn))
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                (cnt', cur') = gevt_del (fst (snd e)) (cnt, cur);
                bend' = (if Queue.is_empty win'' then True else bend)
            in (tl_queue nts, win'', rest, len - 1, bend', cnt', cur', cur # dn)))))"

function gevt_shift :: "args \<Rightarrow> ts \<Rightarrow> 'b :: ccompare gevtaux \<Rightarrow> 'b gevtaux" where
  "gevt_shift args nt aux = (case aux of (nts, win, rest, len, bend, cnt, cur, dn) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> (nts', win, rest, len, bend, cnt, cur, dn)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then (nts', win, rest, len, bend, cnt, cur, dn)
         else gevt_shift args nt (gevt_step args ts0 (nts', win, rest, len, bend, cnt, cur, dn)))))"
  by pat_completeness auto
termination
proof -
  have step: "\<And>args t nts win rest len bend cnt cur dn.
    (case gevt_step args t (nts, win, rest, len, bend, cnt, cur, dn) of
      (nts, win, rest, len, bend, cnt, cur, dn) \<Rightarrow> len) = len - 1"
    by (simp add: gevt_step_def Let_def split: prod.split option.split)
  show ?thesis
    by (relation "measure (\<lambda>(args, nt, (nts, win, rest, len, bend, cnt, cur, dn)). len)")
      (auto simp: step)
qed

declare gevt_shift.simps[simp del]

definition gadd_new_evt :: "args \<Rightarrow> 'b :: ccompare list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    'b gevtaux \<Rightarrow> 'b gevtaux" where
  "gadd_new_evt args rel1 rel2 nt aux =
     (case gevt_shift args nt aux of (nts, win, rest, len, bend, cnt, cur, dn) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in (append_queue nt nts, win, append_queue (nt, rel2, b) rest,
            len + 1, bend, cnt, cur, dn)))"

definition geval_evt :: "args \<Rightarrow> ts \<Rightarrow> 'b :: ccompare gevtaux \<Rightarrow> 'b list set list \<times> 'b gevtaux" where
  "geval_evt args nt aux =
     (case gevt_shift args nt aux of (nts, win, rest, len, bend, cnt, cur, dn) \<Rightarrow>
       (rev dn, (nts, win, rest, len, bend, cnt, cur, [])))"

lemma gevt_extend_eq:
  "gevt_extend args ts0 (win :: evt_entry queue) rest bend cnt cur
   = evt_extend args ts0 win rest bend cnt cur"
  by (induct args ts0 win rest bend cnt cur rule: gevt_extend.induct)
    (subst gevt_extend.simps, subst evt_extend.simps,
     auto simp: gevt_add_eq split: prod.splits option.splits)

lemma ginit_evt_eq: "ginit_evt args = (init_evt args :: evtaux)"
  by (simp add: ginit_evt_def init_evt_def)

lemma gevt_step_eq: "gevt_step args ts0 (aux :: evtaux) = evt_step args ts0 aux"
  by (simp add: gevt_step_def evt_step_def gevt_extend_eq gevt_del_eq Let_def
      split: prod.splits option.splits)

lemma gevt_shift_eq: "gevt_shift args nt (aux :: evtaux) = evt_shift args nt aux"
  by (induct args nt aux rule: gevt_shift.induct)
    (simp add: gevt_shift.simps evt_shift.simps gevt_step_eq split: prod.splits option.splits)

lemma gadd_new_evt_eq:
  "gadd_new_evt args rel1 rel2 nt (aux :: evtaux) = add_new_evt args rel1 rel2 nt aux"
  by (simp add: gadd_new_evt_def add_new_evt_def gevt_shift_eq Let_def split: prod.splits)

lemma geval_evt_eq: "geval_evt args nt (aux :: evtaux) = eval_evt args nt aux"
  by (simp add: geval_evt_def eval_evt_def gevt_shift_eq split: prod.splits)

lemma glength_evt_eq: "glength_evt args (aux :: evtaux) = length_evt args aux"
  by (simp add: glength_evt_def length_evt_def split: prod.splits)

subsection \<open>The trigger structure over short tuples\<close>

text \<open>
  The kernel's trigger structure of @{theory MFODL_Monitor_Devel.Optimized_Trigger} is already
  generic in the element type; what ties it to the wide representation is narrower than it
  looks.  Its queues, its two mappings and the shift it performs on them only ever test
  membership and look keys up, so they carry over unchanged.  Three things do not.

  The first is the semi-join that decides which of the right operand's tuples the left one
  admits.  The kernel projects with @{const proj_tuple}, which blanks the columns outside the
  left operand's rather than dropping them; over short tuples the projection is @{const dproj}
  and the operand it is compared against is short too.  The three cases of the kernel's
  @{const proj_tuple_in_join_optim} survive: where the left operand has the node's columns the
  projection is the identity, where it has none the whole table is taken or dropped on one test
  of the empty tuple, and otherwise each tuple is projected.

  The second is the mask.  The kernel stores one mask for each operand over the node's frame;
  over short tuples the right operand's is all of the frame, so only the left one is kept.

  The third is the result at an empty window, where the kernel returns the wildcard tuple -- the
  one tuple with every column blank -- to say that every valuation satisfies the node.  A short
  tuple cannot say that, so the result is split in two: @{term gresult_mmtaux} returns the union
  of the three sets, which is the kernel's answer on a non-empty window, and
  @{term gmmtaux_empty} says whether the window is empty, so that a node which can face an empty
  one recognises the case rather than reading a wrong table.  The standalone trigger cannot face
  it -- its interval contains zero, so the update always appends to the window -- and reads the
  result directly; the conjunction with a trigger can, and treats the empty window as the
  identity on its other operand, which is what the kernel's join with the wildcard tuple does.
\<close>

type_synonym 'b gmmtaux = "
  ts \<times> nat \<times> nat \<times> nat \<times>
  bool list \<times>
  (ts \<times> 'b list set \<times> 'b list set) queue \<times>
  (ts \<times> 'b list set) queue \<times>
  (('b list, ts) mapping) \<times>
  'b list set \<times>
  (('b list, nat) mapping) \<times>
  'b list set \<times>
  'b list set"

definition gsemi_join :: "bool list \<Rightarrow> bool \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set" where
  "gsemi_join msk pos r l =
     (if \<forall>i \<in> set msk. i then (if pos then r \<inter> l else r - l)
      else if \<forall>i \<in> set msk. \<not> i then (if pos = ([] \<in> l) then r else {})
      else dsemi msk pos r l)"

definition ginit_mmtaux :: "args \<Rightarrow> bool list \<Rightarrow> 'b gmmtaux" where
  "ginit_mmtaux args msk = (0, 0, 0, 0, msk, empty_queue, empty_queue,
     Mapping.empty, {}, Mapping.empty, {}, {})"

definition gupdate_mmtaux' :: "args \<Rightarrow> ts \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) queue \<Rightarrow> (ts \<times> 'b list set) queue \<Rightarrow>
    (('b list, ts) mapping) \<Rightarrow> 'b list set \<Rightarrow> (('b list, nat) mapping) \<Rightarrow> 'b list set \<Rightarrow>
    'b list set \<Rightarrow>
    (nat \<times> nat \<times> (ts \<times> 'b list set \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times>
     (('b list, ts) mapping) \<times> 'b list set \<times> (('b list, nat) mapping) \<times> 'b list set \<times>
     'b list set)" where
  "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tuple_in_once
     tuple_in_once_keys tuple_since_hist hist_sat since_sat = (
    let (_, data_prev', move, tuple_in_once', tuple_in_once_keys') = shift_end'
      (flip_int_less_lower (args_ivl args)) nt fst
      (empty_queue :: (ts \<times> 'b list set \<times> 'b list set) queue,
       data_prev, tuple_in_once, tuple_in_once_keys);
    move_len = length move;
    idx_mid' = idx_mid + move_len;
    (data_in', drop) = takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in;
    move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move;
    drop_prev_len = move_len - length move';
    idx_oldest' = idx_oldest + length drop + drop_prev_len;
    data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in';
    (tuple_since_hist', hist_sat', idx_move, since_sat') =
      fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
        let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
            hist_sat = hist_sat \<inter> r;
            since_sat = since_sat \<inter> r
        in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
            hist_sat, idx_move + 1,
            since_sat \<union> gsemi_join msk (args_pos args) r l))
      move (tuple_since_hist, hist_sat, idx_mid, since_sat);
    tuple_since_hist'' = (if idx_mid' = idx_oldest' then Mapping.empty else tuple_since_hist');
    since_sat'' = (if idx_mid' = idx_oldest' then {} else since_sat');
    hist_sat'' = (case fst (safe_hd data_in'') of None \<Rightarrow> {}
      | Some db \<Rightarrow> hist_sat' \<union> {tuple \<in> snd db.
          case Mapping.lookup tuple_since_hist'' tuple of
            Some idx \<Rightarrow> idx \<le> idx_oldest' | None \<Rightarrow> False})
    in
    (idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys',
     tuple_since_hist'', hist_sat'', since_sat''))"

definition gupdate_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> 'b gmmtaux \<Rightarrow>
    'b gmmtaux" where
  "gupdate_mmtaux args nt l r = (\<lambda>(cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in,
      tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat).
    (let (idx_mid', idx_oldest', data_prev', data_in', tuple_in_once', tuple_in_once_keys',
          tuple_since_hist', hist_sat', since_sat') =
       gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tuple_in_once
         tuple_in_once_keys tuple_since_hist hist_sat since_sat
     in (if mem (args_ivl args) 0
       then (let tuple_since_hist'' = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist' in
         (nt, idx_next + 1, idx_mid' + 1, idx_oldest', msk, data_prev',
          append_queue (nt, r) data_in', tuple_in_once', tuple_in_once_keys',
          upd_set tuple_since_hist'' (\<lambda>_. idx_mid') (r - Mapping.keys tuple_since_hist''),
          (if Queue.is_empty data_in' then r else hist_sat' \<inter> r),
          (since_sat' \<inter> r) \<union> gsemi_join msk (args_pos args) r l))
       else
         (nt, idx_next + 1, idx_mid', idx_oldest', msk,
          append_queue (nt, l, r) data_prev', data_in',
          upd_set tuple_in_once' (\<lambda>_. nt) l, tuple_in_once_keys' \<union> l,
          tuple_since_hist', hist_sat', since_sat'))))"

definition gresult_mmtaux :: "args \<Rightarrow> 'b gmmtaux \<Rightarrow> 'b list set" where
  "gresult_mmtaux args = (\<lambda>(cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in,
      tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat).
    tuple_in_once_keys \<union> hist_sat \<union> since_sat)"

definition gmmtaux_empty :: "'b gmmtaux \<Rightarrow> bool" where
  "gmmtaux_empty = (\<lambda>(cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in,
      tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat).
    Queue.is_empty data_in)"

subsection \<open>The match structures over short tuples\<close>

text \<open>
  The two match structures are lists of tables indexed by a time stamp and, for the past one, by
  a marked regular expression, so they carry over to short tuples on their own.  The derivative
  operations that fill them do not, in two places.

  The first is the join against an atom.  The kernel's lax epsilon joins the guard -- a table over
  the node's columns -- with an atom's table, whose columns are a subset of them; over wide tuples
  that is @{const join}, over short ones it is the semi-join against the atom's mask, and the
  masks are computed once, at compile time, one per atom.  Where both sides are results of the lax
  epsilon they are both over the node's columns, so the join is an intersection.

  The second is the unit table that the two strict epsilons return at a
  @{term "Regex.Skip 0"} and at a star: the tuple with every column blank, which stands for every
  valuation.  A short tuple cannot stand for every valuation.  It does not have to: as the
  well-formedness argument for the match nodes observes, that table is a table over the node's
  columns only because the safety condition forces those columns to be empty where it arises -- a star or
  an empty skip that could match the empty word while the node still binds a variable would make
  the formula unsafe.  With no columns the unit table is the one empty tuple, which is what the
  operations below return.

  An atom's table is read with @{text gnth}, the empty table past the end of the list.  A
  well-formed node never reads past it; reading it totally is what makes the operations commute
  with putting the option back on the fields for every argument, well-formed or not, which is the
  form in which the short-tuple evaluator is related to the boxed one.
\<close>

definition gnth :: "'b list set list \<Rightarrow> nat \<Rightarrow> 'b list set" where
  "gnth xs i = (if i < length xs then xs ! i else {})"

lemma gnth_nth[simp]: "i < length xs \<Longrightarrow> gnth xs i = xs ! i"
  by (simp add: gnth_def)

definition glookup :: "(mregex, 'b list set) mapping \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "glookup = Mapping.lookup_default {}"

lift_definition gmrtabulate :: "mregex list \<Rightarrow> (mregex \<Rightarrow> 'b list set) \<Rightarrow>
    (mregex, 'b list set) mapping"
  is "\<lambda>ks f. map_of (List.map_filter (\<lambda>k. let fk = f k in if fk = {} then None else Some (k, fk)) ks)" .

text \<open>The lifted definition on its own would build the function-backed mapping, which the
  mapping operations cannot look a key up in; it needs the same tree code equation the kernel's
  tabulation has.\<close>

lemma gmrtabulate_rbt_code[code]: "gmrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of
     None \<Rightarrow> Code.abort (STR ''gmrtabulate RBT_Mapping: ccompare = None'') (\<lambda>_. gmrtabulate xs f)
   | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload
       (List.map_filter (\<lambda>k. let fk = f k in if fk = {} then None else Some (k, fk)) xs)))"
  unfolding gmrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

fun geps_lax :: "bool list list \<Rightarrow> 'b list set \<Rightarrow> 'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "geps_lax msks guard \<phi>s (MSkip n) = (if n = 0 then guard else {})"
| "geps_lax msks guard \<phi>s (MTestPos i) = dsemi (msks ! i) True guard (gnth \<phi>s i)"
| "geps_lax msks guard \<phi>s (MTestNeg i) = dsemi (msks ! i) False guard (gnth \<phi>s i)"
| "geps_lax msks guard \<phi>s (MPlus r s) = geps_lax msks guard \<phi>s r \<union> geps_lax msks guard \<phi>s s"
| "geps_lax msks guard \<phi>s (MTimes r s) = geps_lax msks guard \<phi>s r \<inter> geps_lax msks guard \<phi>s s"
| "geps_lax msks guard \<phi>s (MStar r) = guard"

fun greps_strict :: "bool list list \<Rightarrow> 'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "greps_strict msks \<phi>s (MSkip m) = (if m = 0 then {[]} else {})"
| "greps_strict msks \<phi>s (MTestPos i) = gnth \<phi>s i"
| "greps_strict msks \<phi>s (MTestNeg i) = (if gnth \<phi>s i = {} then {[]} else {})"
| "greps_strict msks \<phi>s (MPlus r s) = greps_strict msks \<phi>s r \<union> greps_strict msks \<phi>s s"
| "greps_strict msks \<phi>s (MTimes r s) = geps_lax msks (greps_strict msks \<phi>s r) \<phi>s s"
| "greps_strict msks \<phi>s (MStar r) = {[]}"

fun gleps_strict :: "bool list list \<Rightarrow> 'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "gleps_strict msks \<phi>s (MSkip m) = (if m = 0 then {[]} else {})"
| "gleps_strict msks \<phi>s (MTestPos i) = gnth \<phi>s i"
| "gleps_strict msks \<phi>s (MTestNeg i) = (if gnth \<phi>s i = {} then {[]} else {})"
| "gleps_strict msks \<phi>s (MPlus r s) = gleps_strict msks \<phi>s r \<union> gleps_strict msks \<phi>s s"
| "gleps_strict msks \<phi>s (MTimes r s) = geps_lax msks (gleps_strict msks \<phi>s s) \<phi>s r"
| "gleps_strict msks \<phi>s (MStar r) = {[]}"

fun grdelta :: "bool list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'b list set) mapping \<Rightarrow>
    'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "grdelta msks \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> glookup X (\<kappa> (MSkip m)))"
| "grdelta msks \<kappa> X \<phi>s (MTestPos i) = {}"
| "grdelta msks \<kappa> X \<phi>s (MTestNeg i) = {}"
| "grdelta msks \<kappa> X \<phi>s (MPlus r s) = grdelta msks \<kappa> X \<phi>s r \<union> grdelta msks \<kappa> X \<phi>s s"
| "grdelta msks \<kappa> X \<phi>s (MTimes r s) =
     grdelta msks (\<lambda>t. \<kappa> (MTimes r t)) X \<phi>s s \<union> geps_lax msks (grdelta msks \<kappa> X \<phi>s r) \<phi>s s"
| "grdelta msks \<kappa> X \<phi>s (MStar r) = grdelta msks (\<lambda>t. \<kappa> (MTimes (MStar r) t)) X \<phi>s r"

fun gldelta :: "bool list list \<Rightarrow> (mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'b list set) mapping \<Rightarrow>
    'b list set list \<Rightarrow> mregex \<Rightarrow> 'b list set" where
  "gldelta msks \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> glookup X (\<kappa> (MSkip m)))"
| "gldelta msks \<kappa> X \<phi>s (MTestPos i) = {}"
| "gldelta msks \<kappa> X \<phi>s (MTestNeg i) = {}"
| "gldelta msks \<kappa> X \<phi>s (MPlus r s) = gldelta msks \<kappa> X \<phi>s r \<union> gldelta msks \<kappa> X \<phi>s s"
| "gldelta msks \<kappa> X \<phi>s (MTimes r s) =
     gldelta msks (\<lambda>t. \<kappa> (MTimes t s)) X \<phi>s r \<union> geps_lax msks (gldelta msks \<kappa> X \<phi>s s) \<phi>s r"
| "gldelta msks \<kappa> X \<phi>s (MStar r) = gldelta msks (\<lambda>t. \<kappa> (MTimes t (MStar r))) X \<phi>s r"

type_synonym 'b gmrdaux = "(ts \<times> (mregex, 'b list set) mapping) list"
type_synonym 'b gmldaux = "(ts \<times> 'b list set list \<times> 'b list set) list"

definition gupdate_matchP :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> 'b list set list \<Rightarrow>
    ts \<Rightarrow> 'b gmrdaux \<Rightarrow> 'b list set \<times> 'b gmrdaux" where
  "gupdate_matchP msks I mr mrs rels nt aux =
    (let aux = (case [(t, gmrtabulate mrs (\<lambda>mr.
        grdelta msks id rel rels mr \<union> (if t = nt then greps_strict msks rels mr else {}))).
      (t, rel) \<leftarrow> aux, memR I (nt - t)]
      of [] \<Rightarrow> [(nt, gmrtabulate mrs (greps_strict msks rels))]
      | x # aux' \<Rightarrow> (if fst x = nt then x # aux'
                    else (nt, gmrtabulate mrs (greps_strict msks rels)) # x # aux'))
    in (foldr (\<union>) [glookup rel mr. (t, rel) \<leftarrow> aux, memL I (nt - t)] {}, aux))"

definition gupdate_matchF_base :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow>
    'b list set list \<Rightarrow> ts \<Rightarrow> 'b gmldaux \<times> (mregex, 'b list set) mapping" where
  "gupdate_matchF_base msks I mr mrs rels nt =
     (let X = gmrtabulate mrs (gleps_strict msks rels)
      in ([(nt, rels, if memL I 0 then glookup X mr else {})], X))"

definition gupdate_matchF_step :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> ts \<Rightarrow>
    ts \<times> 'b list set list \<times> 'b list set \<Rightarrow> 'b gmldaux \<times> (mregex, 'b list set) mapping \<Rightarrow>
    'b gmldaux \<times> (mregex, 'b list set) mapping" where
  "gupdate_matchF_step msks I mr mrs nt = (\<lambda>(t, rels', rel) (aux', X).
     (let Y = gmrtabulate mrs (gldelta msks id X rels')
      in ((t, rels', if mem I (nt - t) then rel \<union> glookup Y mr else rel) # aux', Y)))"

definition gupdate_matchF :: "bool list list \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> 'b list set list \<Rightarrow>
    ts \<Rightarrow> 'b gmldaux \<Rightarrow> 'b gmldaux" where
  "gupdate_matchF msks I mr mrs rels nt aux =
     fst (foldr (gupdate_matchF_step msks I mr mrs nt) aux
       (gupdate_matchF_base msks I mr mrs rels nt))"

fun geval_matchF :: "\<I> \<Rightarrow> mregex \<Rightarrow> ts \<Rightarrow> 'b gmldaux \<Rightarrow> 'b list set list \<times> 'b gmldaux" where
  "geval_matchF I mr nt [] = ([], [])"
| "geval_matchF I mr nt ((t, rels, rel) # aux) = (if \<not> memR I (nt - t)
    then (let (xs, aux) = geval_matchF I mr nt aux in (rel # xs, aux))
    else ([], (t, rels, rel) # aux))"

subsection \<open>The operations that read a field\<close>

text \<open>
  These cannot be generalised, because they look inside a field.  Their twins over short tuples
  are in @{theory MFODL_Monitor_Dense.Dense_Utuple}, and the verified evaluator's versions are
  those twins read through @{const deopt}, so the agreement is by definition; what remains is
  the direction the executable monitor's compiler uses, from the kernel's tuples down.
\<close>

lemma reopt_deopt: "dwf_tuple n x \<Longrightarrow> reopt (deopt x) = x"
  by (auto simp: deopt_def reopt_def dwf_tuple_def list_eq_iff_nth_eq)

lemma uassign1_deopt_dassign1: "uassign1 p t (deopt x) = deopt (dassign1 p t x)"
  by (simp add: dassign1_def)

lemma umtrm_deopt: "umtrm mt x = deopt_table (dmtrm mt x)"
  by (cases mt) (simp_all add: deopt_table_def deopt_def unit_table_def empty_table_def)

lemma umatch_deopt: "dwf_tuple (length x) x \<Longrightarrow> umatch tms (deopt x) = match tms x"
  by (simp add: umatch_reopt reopt_deopt)

subsection \<open>The aggregation structure over short tuples\<close>

text \<open>
  An aggregation over a Since or an Until is fused into the temporal operator's arguments, and
  the kernel's structure keeps the aggregate up to date as tuples enter and leave the window
  instead of recomputing it from the window at every time point.  The structure is a mapping
  from the group tuple to whatever the aggregation needs: a count, a count and a sum, or the
  sorted multiset of the values for the rank aggregations.

  Only three things in it read a tuple.  The group key is the kernel's @{term "drop (length tys) t"},
  and over short tuples it is the same @{const drop}: safety makes the bound variables the first
  columns of the operand's frame, so the group is the suffix.  The value is
  @{term "meval_trm f t"}, which over short tuples is @{const umeval_trm} of the term reindexed
  to the operand's frame -- the same term the non-incremental @{const uagg} evaluates.  And the
  result writes the aggregate into the group tuple: over wide tuples by overwriting the column
  of the result variable, over short ones by inserting it at the position that variable has
  among the node's columns.

  Everything else -- the three aggregate kinds, the treelists of the rank aggregations, the
  types they are restricted to -- is about the values and carries over unchanged, so this
  transcribes @{theory MFODL_Monitor_Devel.Optimized_Agg} with those three replacements and
  reuses the rest of it.
\<close>

record daggargs =
  dgg_g0 :: bool
  dgg_op :: "ty Formula.agg_op"
  dgg_trm :: Formula.trm
  dgg_k :: nat
  dgg_p :: nat

type_synonym 'a dagg_map = "(event_data list, 'a) mapping"

datatype daggaux = DCntAux "nat dagg_map" | DSumAux "(nat \<times> integer) dagg_map"
  | DRankAux "list_aux dagg_map \<times> type"

text \<open>
  The second component of @{term "dgg_op args"} is the aggregation's \<^emph>\<open>result\<close> type, not
  the type of the values it aggregates.  For @{const Formula.Agg_Min}, @{const Formula.Agg_Max}
  and @{const Formula.Agg_Sum} the two coincide, but @{const Formula.Agg_Avg} and
  @{const Formula.Agg_Med} always return a float, so they arrive here as @{const TFloat} whatever
  their values are, and admitting them on @{const TInt} admits nothing at all.  The value type is
  therefore not available at initialisation.  Both are admitted on the float result type instead,
  and the insertion rejects a non-integer value at the first tuple it meets, which drops the
  structure and falls back to the generic evaluation of the aggregation.  That fallback is what
  keeps this sound: addition of floats is not associative, so an incremental sum must never see
  one -- which is why the accumulator is an @{typ integer} and the insertion accepts
  @{const EInt} alone.
\<close>

definition dinit_maggaux :: "daggargs \<Rightarrow> bool \<times> daggaux" where
  "dinit_maggaux args = (case (fst (dgg_op args), snd (dgg_op args)) of
      (Formula.Agg_Cnt, _) \<Rightarrow> (True, DCntAux Mapping.empty)
    | (Formula.Agg_Sum, TInt) \<Rightarrow> (True, DSumAux Mapping.empty)
    | (Formula.Agg_Min, TInt) \<Rightarrow> (True, DRankAux (Mapping.empty, IntT))
    | (Formula.Agg_Max, TInt) \<Rightarrow> (True, DRankAux (Mapping.empty, IntT))
    | (Formula.Agg_Avg, TInt) \<Rightarrow> (True, DSumAux Mapping.empty)
    | (Formula.Agg_Avg, TFloat) \<Rightarrow> (True, DSumAux Mapping.empty)
    | (Formula.Agg_Med, TFloat) \<Rightarrow> (True, DRankAux (Mapping.empty, IntT))
    | (Formula.Agg_Min, TString) \<Rightarrow> (True, DRankAux (Mapping.empty, StringT))
    | (Formula.Agg_Max, TString) \<Rightarrow> (True, DRankAux (Mapping.empty, StringT))
    | _ \<Rightarrow> (False, DCntAux Mapping.empty))"

fun dinsert_cnt :: "daggargs \<Rightarrow> event_data list \<Rightarrow> bool \<times> nat dagg_map \<Rightarrow> bool \<times> nat dagg_map" where
  "dinsert_cnt args t (v, m) =
     (if v then (v, (let g = drop (dgg_k args) t in case Mapping.lookup m g of
        Some i \<Rightarrow> Mapping.update g (i + 1) m | None \<Rightarrow> Mapping.update g 1 m))
      else (v, m))"

fun ddelete_cnt :: "daggargs \<Rightarrow> event_data list \<Rightarrow> bool \<times> nat dagg_map \<Rightarrow> bool \<times> nat dagg_map" where
  "ddelete_cnt args t (v, m) =
     (if v then (v, (let g = drop (dgg_k args) t in case Mapping.lookup m g of
        Some i \<Rightarrow> (if i = 1 then Mapping.delete g m else Mapping.update g (i - 1) m)
      | None \<Rightarrow> m))
      else (v, m))"

fun dinsert_sum :: "daggargs \<Rightarrow> event_data list \<Rightarrow> bool \<times> (nat \<times> integer) dagg_map \<Rightarrow>
    bool \<times> (nat \<times> integer) dagg_map" where
  "dinsert_sum args t (v, m) =
     (if v then (let g = drop (dgg_k args) t; e = umeval_trm (dgg_trm args) t in
        case (Mapping.lookup m g, e) of
          (Some (cnt, s), EInt i) \<Rightarrow> (True, Mapping.update g (cnt + 1, s + i) m)
        | (None, EInt i) \<Rightarrow> (True, Mapping.update g (1, i) m)
        | _ \<Rightarrow> (False, Mapping.empty))
      else (v, m))"

fun ddelete_sum :: "daggargs \<Rightarrow> event_data list \<Rightarrow> bool \<times> (nat \<times> integer) dagg_map \<Rightarrow>
    bool \<times> (nat \<times> integer) dagg_map" where
  "ddelete_sum args t (v, m) =
     (if v then (let g = drop (dgg_k args) t; e = umeval_trm (dgg_trm args) t in
        case (Mapping.lookup m g, e) of
          (Some (cnt, s), EInt i) \<Rightarrow> (True, (if cnt = 1 then Mapping.delete g m
             else Mapping.update g (cnt - 1, s - i) m))
        | _ \<Rightarrow> (False, Mapping.empty))
      else (v, m))"

fun dinsert_rank :: "daggargs \<Rightarrow> type \<Rightarrow> event_data list \<Rightarrow> bool \<times> list_aux dagg_map \<Rightarrow>
    bool \<times> list_aux dagg_map" where
  "dinsert_rank args ty t (v, m) =
     (if v then (let g = drop (dgg_k args) t; e = umeval_trm (dgg_trm args) t;
        (v', l') = (case (Mapping.lookup m g, e, ty) of
            (Some (LInt s), EInt c, IntT) \<Rightarrow> (True, LInt (insert_treelist c s))
          | (Some (LString s), EString c, StringT) \<Rightarrow> (True, LString (insert_treelist c s))
          | (None, EInt c, IntT) \<Rightarrow> (True, LInt (insert_treelist c empty_treelist))
          | (None, EString c, StringT) \<Rightarrow> (True, LString (insert_treelist c empty_treelist))
          | _ \<Rightarrow> (False, LInt empty_treelist))
        in (v', (if v' then Mapping.update g l' m else Mapping.empty)))
      else (v, m))"

fun ddelete_rank :: "daggargs \<Rightarrow> type \<Rightarrow> event_data list \<Rightarrow> bool \<times> list_aux dagg_map \<Rightarrow>
    bool \<times> list_aux dagg_map" where
  "ddelete_rank args ty t (v, m) =
     (if v then (let g = drop (dgg_k args) t; e = umeval_trm (dgg_trm args) t;
        (v', m') = (case (Mapping.lookup m g, e, ty) of
            (Some (LString s), EString c, StringT) \<Rightarrow> (True, let l' = remove_treelist c s in
               if l' = empty_treelist then Mapping.delete g m else Mapping.update g (LString l') m)
          | (Some (LInt s), EInt c, IntT) \<Rightarrow> (True, let l' = remove_treelist c s in
               if l' = empty_treelist then Mapping.delete g m else Mapping.update g (LInt l') m)
          | (None, EString c, StringT) \<Rightarrow> (True, m)
          | (None, EInt c, IntT) \<Rightarrow> (True, m)
          | _ \<Rightarrow> (False, Mapping.empty))
        in (v', m'))
      else (v, m))"

text \<open>The kernel folds its update over the table with @{const Finite_Set.fold}, which the code
  generator needs a commutativity witness for, one per aggregate kind.  Folding the sorted list
  of the table instead needs none and generates the same loop; the two agree because the update
  is commutative, which is what those witnesses say.\<close>

fun dinsert_maggaux :: "daggargs \<Rightarrow> utable \<Rightarrow> daggaux \<Rightarrow> bool \<times> daggaux" where
  "dinsert_maggaux args X aux = (let xs = csorted_list_of_set X in case aux of
     DCntAux m \<Rightarrow> (case fold (dinsert_cnt args) xs (True, m) of (v, m') \<Rightarrow> (v, DCntAux m'))
   | DSumAux m \<Rightarrow> (case fold (dinsert_sum args) xs (True, m) of (v, m') \<Rightarrow> (v, DSumAux m'))
   | DRankAux (m, ty) \<Rightarrow> (case fold (dinsert_rank args ty) xs (True, m) of (v, m') \<Rightarrow>
       (v, DRankAux (m', ty))))"

fun ddelete_maggaux :: "daggargs \<Rightarrow> utable \<Rightarrow> daggaux \<Rightarrow> bool \<times> daggaux" where
  "ddelete_maggaux args X aux = (let xs = csorted_list_of_set X in case aux of
     DCntAux m \<Rightarrow> (case fold (ddelete_cnt args) xs (True, m) of (v, m') \<Rightarrow> (v, DCntAux m'))
   | DSumAux m \<Rightarrow> (case fold (ddelete_sum args) xs (True, m) of (v, m') \<Rightarrow> (v, DSumAux m'))
   | DRankAux (m, ty) \<Rightarrow> (case fold (ddelete_rank args ty) xs (True, m) of (v, m') \<Rightarrow>
       (v, DRankAux (m', ty))))"

text \<open>The result writes the aggregate into the group tuple at the position the node's columns
  give @{term y}; with no group variables the tuple is the aggregate alone.\<close>

definition dmap_result :: "nat \<Rightarrow> ('a \<Rightarrow> event_data) \<Rightarrow> 'a dagg_map \<Rightarrow> utable" where
  "dmap_result p f m = (\<lambda>g. case Mapping.lookup m g of
      Some i \<Rightarrow> take p g @ f i # drop p g | None \<Rightarrow> g) ` Mapping.keys m"

fun dresult_maggaux :: "daggargs \<Rightarrow> daggaux \<Rightarrow> utable" where
  "dresult_maggaux args aux = (let g0 = dgg_g0 args; \<omega> = dgg_op args; p = dgg_p args in
    (case aux of
      DCntAux m \<Rightarrow> (if g0 \<and> Mapping.keys m = {} then {[eval_agg_op \<omega> {}]}
        else dmap_result p (\<lambda>k. EInt (integer_of_int k)) m)
    | DSumAux m \<Rightarrow> (if g0 \<and> Mapping.keys m = {} then {[eval_agg_op \<omega> {}]}
        else (case fst \<omega> of
            Formula.Agg_Sum \<Rightarrow> dmap_result p (\<lambda>k. EInt (snd k)) m
          | Formula.Agg_Avg \<Rightarrow> dmap_result p (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) /
              double_of_int (fst k))) m))
    | DRankAux (m, ty) \<Rightarrow> (if g0 \<and> Mapping.keys m = {} then {[eval_agg_op \<omega> {}]}
        else (case fst \<omega> of
            Formula.Agg_Min \<Rightarrow> dmap_result p (\<lambda>k. get_edata_list k 0) m
          | Formula.Agg_Max \<Rightarrow> dmap_result p (\<lambda>k. get_edata_list k (get_length k - 1)) m
          | Formula.Agg_Med \<Rightarrow> dmap_result p (\<lambda>k. let u = get_length k; u' = u div 2 in
              EFloat (if even u
                then (double_of_event_data_agg (get_edata_list k (u' - 1)) +
                      double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
                else double_of_event_data_agg (get_edata_list k u'))) m))))"

text \<open>The structure is dropped when it cannot represent what it is asked to, and then the
  aggregate is recomputed from the window as @{const uagg} does.  That is the kernel's
  arrangement, and the four operations below are its four primed ones.\<close>

definition dinit_maggaux' :: "daggargs \<Rightarrow> daggaux option" where
  "dinit_maggaux' args = (case dinit_maggaux args of (v, aux) \<Rightarrow> if v then Some aux else None)"

fun dinsert_maggaux' :: "daggargs \<Rightarrow> utable \<Rightarrow> daggaux option \<Rightarrow> daggaux option" where
  "dinsert_maggaux' args X None = None"
| "dinsert_maggaux' args X (Some aux) =
     (case dinsert_maggaux args X aux of (v, aux') \<Rightarrow> if v then Some aux' else None)"

fun ddelete_maggaux' :: "daggargs \<Rightarrow> utable \<Rightarrow> daggaux option \<Rightarrow> daggaux option" where
  "ddelete_maggaux' args X None = None"
| "ddelete_maggaux' args X (Some aux) =
     (case ddelete_maggaux args X aux of (v, aux') \<Rightarrow> if v then Some aux' else None)"

definition dagg_fallback :: "daggargs \<Rightarrow> utable \<Rightarrow> utable" where
  "dagg_fallback args X = uagg (dgg_g0 args) (dgg_op args) (dgg_trm args) (dgg_k args)
     (dgg_p args) X"

fun dresult_maggaux' :: "daggargs \<Rightarrow> daggaux option \<Rightarrow> utable \<Rightarrow> utable" where
  "dresult_maggaux' args None X = dagg_fallback args X"
| "dresult_maggaux' args (Some aux) X = dresult_maggaux args aux"

subsection \<open>The aggregating Since over short tuples\<close>

text \<open>
  To keep the aggregate up to date the structure has to say which tuples entered and which left
  its window.  Three of its operations move tuples in or out, and each already computes the set
  that moved; the three below return it alongside the new structure, and the lemma after each
  says that dropping it gives the operation of the previous subsection back.  Nothing is
  duplicated silently: what the aggregating path runs is the same body, proved equal.

  The join is the one whose answer is not a set.  Where the node has no join columns at all it
  either keeps its window or empties it, and emptying it is not a deletion of known tuples but a
  reset of the structure, which @{term None} says.
\<close>

lemma gmsaux_cases:
  fixes s :: "'b gmsaux"
  obtains t gc msk data_prev data_in table_in idx_in tuple_in idx_since tuple_since
  where "s = (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
    idx_since, tuple_since)"
  by (metis prod.collapse)

definition gmsaux_in :: "'b gmsaux \<Rightarrow> 'b list set" where
  "gmsaux_in = (\<lambda>(t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
     idx_since, tuple_since). table_in)"

fun gshift_end_del :: "args \<Rightarrow> ts \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux \<times> 'b list set" where
  "gshift_end_del args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
     (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
     (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
     ((t, gc, msk, data_prev', data_in, table_in - del,
       gidx_upd args (\<lambda>_. didx_minus idx_in (didx msk del)), tuple_in, idx_since, tuple_since),
      del))"

lemma gshift_end_del_fst: "fst (gshift_end_del args nt s) = gshift_end args nt s"
  by (cases s rule: gmsaux_cases) (simp add: Let_def split_beta)

fun gadd_new_ts_msaux'_add :: "args \<Rightarrow> ts \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux \<times> 'b list set" where
  "gadd_new_ts_msaux'_add args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
     data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
     (tuple_in', add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. gvalid_tuple tuple_since (t, as)}))
        move (tuple_in, {}) in
     ((nt, gc, msk, data_prev, data_in, table_in \<union> add,
       gidx_upd args (\<lambda>_. didx_union idx_in (didx msk add)), tuple_in', idx_since, tuple_since),
      add - Mapping.keys tuple_in))"

lemma gadd_new_ts_msaux'_add_fst:
  "fst (gadd_new_ts_msaux'_add args nt s) = gadd_new_ts_msaux' args nt s"
  by (cases s rule: gmsaux_cases) (simp add: Let_def split_beta)

fun gjoin_msaux_del :: "args \<Rightarrow> 'b list set \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux \<times> 'b list set option" where
  "gjoin_msaux_del args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let pos = args_pos args in
     (if \<forall>i \<in> set msk. \<not> i then
        (let take_all = (([] \<in> Y) = pos) in
         ((t, gc, msk, data_prev, data_in,
           if take_all then table_in else {},
           if take_all then idx_in else Mapping.empty,
           if take_all then tuple_in else Mapping.empty,
           if take_all then idx_since else Mapping.empty,
           if take_all then tuple_since else Mapping.empty),
          if take_all then Some {} else None))
      else if \<forall>i \<in> set msk. i then
        (let in_del = (if pos then table_in - Y else table_in \<inter> Y);
         tuple_in' = mapping_delete_set tuple_in in_del;
         tuple_since' = Mapping.filter (\<lambda>as _. (as \<in> Y) = pos) tuple_since in
         ((t, gc, msk, data_prev, data_in, table_in - in_del, Mapping.empty, tuple_in',
           Mapping.empty, tuple_since'), Some in_del))
      else
        (let in_del = dsemi_idx msk (\<not> pos) idx_in Y;
         since_del = dsemi_idx msk (\<not> pos) idx_since Y in
         ((t, gc, msk, data_prev, data_in, table_in - in_del,
           Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_in, mapping_delete_set tuple_in in_del,
           Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_since,
           mapping_delete_set tuple_since since_del), Some in_del))))"

lemma gjoin_msaux_del_fst: "fst (gjoin_msaux_del args Y s) = gjoin_msaux args Y s"
  by (cases s rule: gmsaux_cases)
    (simp only: gjoin_msaux_del.simps gjoin_msaux.simps Let_def if_distrib[of fst] fst_conv)

fun ggc_join_msaux_del :: "args \<Rightarrow> 'b list set \<Rightarrow> 'b gmsaux \<Rightarrow> 'b gmsaux \<times> 'b list set option" where
  "ggc_join_msaux_del args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if \<not> memL (args_ivl args) 0 \<and> \<not> memR (args_ivl args) (t - gc)
     then gjoin_msaux_del args Y (ggc_msaux args (t, gc, msk, data_prev, data_in, table_in,
       idx_in, tuple_in, idx_since, tuple_since))
     else gjoin_msaux_del args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
       idx_since, tuple_since))"

lemma ggc_join_msaux_del_fst: "fst (ggc_join_msaux_del args Y s) = ggc_join_msaux args Y s"
  by (cases s rule: gmsaux_cases)
    (simp del: gjoin_msaux_del.simps gjoin_msaux.simps add: gjoin_msaux_del_fst)

text \<open>The structure the fused node runs, and its five operations.  They are the kernel's, with
  the aggregate maintained on the deltas above; where the aggregation has no structure the
  result falls back to recomputing it from the window, which is what the kernel does too.\<close>

type_synonym dmasaux = "event_data gmsaux \<times> daggaux option"

definition dainit_msaux :: "args \<Rightarrow> daggargs \<Rightarrow> bool list \<Rightarrow> dmasaux" where
  "dainit_msaux args ag msk = (ginit_msaux args msk, dinit_maggaux' ag)"

definition daadd_new_ts_msaux :: "args \<Rightarrow> daggargs \<Rightarrow> ts \<Rightarrow> dmasaux \<Rightarrow> dmasaux" where
  "daadd_new_ts_msaux args ag nt sa = (case sa of (s, a) \<Rightarrow>
     (case gshift_end_del args nt s of (s1, del) \<Rightarrow>
      (case gadd_new_ts_msaux'_add args nt s1 of (s2, add) \<Rightarrow>
        (s2, dinsert_maggaux' ag add (ddelete_maggaux' ag del a)))))"

definition dajoin_msaux :: "args \<Rightarrow> daggargs \<Rightarrow> utable \<Rightarrow> dmasaux \<Rightarrow> dmasaux" where
  "dajoin_msaux args ag Y sa = (case sa of (s, a) \<Rightarrow>
     (case ggc_join_msaux_del args Y s of (s1, d) \<Rightarrow>
       (s1, case d of None \<Rightarrow> dinit_maggaux' ag | Some D \<Rightarrow> ddelete_maggaux' ag D a)))"

definition daadd_new_table_msaux :: "args \<Rightarrow> daggargs \<Rightarrow> utable \<Rightarrow> dmasaux \<Rightarrow> dmasaux" where
  "daadd_new_table_msaux args ag X sa = (case sa of (s, a) \<Rightarrow>
     (gadd_new_table_msaux args X s,
      if memL (args_ivl args) 0 then dinsert_maggaux' ag (X - gmsaux_in s) a else a))"

definition daresult_msaux :: "daggargs \<Rightarrow> dmasaux \<Rightarrow> utable" where
  "daresult_msaux ag sa = (case sa of (s, a) \<Rightarrow> dresult_maggaux' ag a (gmsaux_in s))"

subsection \<open>The aggregating Until over short tuples\<close>

text \<open>
  The Until is the same story with the deltas in different places.  Its window is the front map
  of the deque, and @{term result} is that map's key set; a step drops the time point at the
  front, which deletes the tuples that expired with it and inserts those of the map that becomes
  the front, and adding a time point inserts what it puts at the front.  The kernel interleaves
  the aggregate into the same two functions, and so does this: @{const geval_step_dq} and
  @{const gadd_new_dq} with the aggregate carried alongside, and the verdict of a step read off
  the aggregate rather than off the window.

  One delta is not written out.  What a new time point adds to the front map is exactly what it
  adds to @{term result}, because @{term result} is that map's key set, so the insertion is the
  difference between the two -- which is what the kernel's @{term to_add} computes the long way.
  Since the generic insertion no longer maintains @{term result}
  (@{theory MFODL_Monitor_Dense.Dense_Until_Gen}), the new result is read off the front map.
\<close>

type_synonym dmauaux = "event_data gmuaux \<times> daggaux option"

fun gaeval_step_dq :: "args \<Rightarrow> daggargs \<Rightarrow> dmauaux \<Rightarrow> dmauaux" where
  "gaeval_step_dq args ag ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq,
      tstp_dq, dn), a) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (let m = dq_nth a2_dq 0;
        I = args_ivl args;
        T = dresult_maggaux' ag a result;
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
        tstp_dq = dq_tl tstp_dq;
        to_ins = Mapping.filter (\<lambda>k v. Mapping.lookup m'' k = None) m';
        a' = (if len = 1 then dinit_maggaux' ag
              else dinsert_maggaux' ag (Mapping.keys to_ins) (ddelete_maggaux' ag to_del a)) in
        ((tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, T # dn),
         a')))"

fun gashift_dq :: "args \<Rightarrow> daggargs \<Rightarrow> ts \<Rightarrow> dmauaux \<Rightarrow> dmauaux" where
  "gashift_dq args ag nt ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq,
      tstp_dq, dn), a) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. gaeval_step_dq args ag aux) ((tp, tss', tables, len, maskL, maskR,
      result, a1_map, a2_dq, tstp_dq, dn), a) (linearize tss_queue))"

fun gaeval_dq :: "args \<Rightarrow> daggargs \<Rightarrow> ts \<Rightarrow> dmauaux \<Rightarrow> utable list \<times> dmauaux" where
  "gaeval_dq args ag nt aux =
    (case gashift_dq args ag nt aux of
      ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn), a) \<Rightarrow>
    (rev dn, ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, []), a)))"

definition gainit_dq :: "args \<Rightarrow> daggargs \<Rightarrow> dmauaux" where
  "gainit_dq args ag = (ginit_dq args, dinit_maggaux' ag)"

definition gaadd_new_dq :: "args \<Rightarrow> daggargs \<Rightarrow> bool list \<Rightarrow> utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow>
    dmauaux \<Rightarrow> dmauaux" where
  "gaadd_new_dq args ag msk rel1 rel2 nt aux =
    (case gashift_dq args ag nt aux of
      ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_dq, tstp_dq, dn), a) \<Rightarrow>
     (let I = args_ivl args; pos = args_pos args; inz = memL I 0;
      new_tstp = (if inz then Inr tp else Inl nt);
      tstp_dq = dq_push nt tstp_dq;
      P = (\<lambda>t. memL I (nt - dq_nth tstp_dq (t - (tp - len))));
      (tbl, a2_dq') = fold (guntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
        (csl rel2) ({}, a2_dq);
      result' = Mapping.keys (dq_hd_s a2_dq' Mapping.empty);
      tables = append_queue (tbl, new_tstp) tables;
      a2_dq = dq_push Mapping.empty a2_dq';
      a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
        (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
      tss = append_queue nt tss in
      ((tp + 1, tss, tables, len + 1, maskL, maskR, result', a1_map, a2_dq, tstp_dq, dn),
       dinsert_maggaux' ag (result' - result) a)))"

(*<*)
end
(*>*)
