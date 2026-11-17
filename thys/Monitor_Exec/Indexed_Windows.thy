(*<*)
theory Indexed_Windows
  imports Window_Dispatch Indexed_Tables
begin
(*>*)



section \<open>Indexed Since and Until structures\<close>

text \<open>A window keeps its union as an indexed table, which a join probes directly.  Forgetting
  the indices (@{text isw_abs}) gives @{theory Monitor_Exec.Closed_Left_Windows}.\<close>

subsection \<open>Count set\<close>

type_synonym icntset = "(event_data tuple, nat) mapping \<times> event_data itab"

definition icnt_abs :: "icntset \<Rightarrow> cntset" where
  "icnt_abs cc = (fst cc, iset (snd cc))"

definition icnt_add1 :: "event_data tuple \<Rightarrow> icntset \<Rightarrow> icntset" where
  "icnt_add1 t cc = (case cc of (c, s) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, iins t s)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, s)))"

definition icnt_del1 :: "event_data tuple \<Rightarrow> icntset \<Rightarrow> icntset" where
  "icnt_del1 t cc = (case cc of (c, s) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (c, s)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, idel t s)
                  else (Mapping.update t (k - 1) c, s))))"

definition icnt_add :: "event_data table \<Rightarrow> icntset \<Rightarrow> icntset" where
  "icnt_add T cc = fold icnt_add1 (csl T) cc"

definition icnt_del :: "event_data table \<Rightarrow> icntset \<Rightarrow> icntset" where
  "icnt_del T cc = fold icnt_del1 (csl T) cc"

subsection \<open>Window for closed left operands\<close>

type_synonym iswaux = "ts \<times> (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> icntset"

definition isw_abs :: "iswaux \<Rightarrow> swaux" where
  "isw_abs aux = (case aux of (t, pend, win, cc) \<Rightarrow> (t, pend, win, icnt_abs cc))"

definition isw_emb :: "swaux \<Rightarrow> iswaux" where
  "isw_emb aux = (case aux of (t, pend, win, c, s) \<Rightarrow> (t, pend, win, c, itab s))"

lemma isw_abs_emb[simp]: "isw_abs (isw_emb aux) = aux"
  by (simp add: isw_abs_def isw_emb_def icnt_abs_def split: prod.splits)

function isw_move :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (ts \<times> event_data table) queue \<Rightarrow> icntset \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> icntset" where
  "isw_move args nt pend win cc =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cc)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then isw_move args nt (tl_queue pend') (append_queue e win) (icnt_add (snd e) cc)
               else isw_move args nt (tl_queue pend') win cc)
         else (pend', win, cc)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, pend, win, cc). length (linearize pend))")
     (fastforce split: prod.splits)+

declare isw_move.simps[simp del]

function isw_expire :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> icntset \<Rightarrow>
    (ts \<times> event_data table) queue \<times> icntset" where
  "isw_expire args nt win cc =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cc)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cc)
         else isw_expire args nt (tl_queue win') (icnt_del (snd e) cc)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, win, cc). length (linearize win))")
     (fastforce split: prod.splits)+

declare isw_expire.simps[simp del]

definition isw_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> iswaux \<Rightarrow> iswaux" where
  "isw_add_new_ts args nt aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (case isw_move args nt pend win cc of (pend', win', cc') \<Rightarrow>
      (case isw_expire args nt win' cc' of (win'', cc'') \<Rightarrow> (nt, pend', win'', cc''))))"

definition isw_join :: "args \<Rightarrow> event_data table \<Rightarrow> iswaux \<Rightarrow> iswaux" where
  "isw_join args X aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, Mapping.empty, itab {})))"

definition isw_add_new_table :: "args \<Rightarrow> event_data table \<Rightarrow> iswaux \<Rightarrow> iswaux" where
  "isw_add_new_table args X aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (t, pend, append_queue (t, X) win, icnt_add X cc)
      else (t, append_queue (t, X) pend, win, cc)))"

definition isw_result :: "iswaux \<Rightarrow> event_data itab" where
  "isw_result aux = (case aux of (t, pend, win, cc) \<Rightarrow> snd cc)"

definition isw_ensure :: "bool list list \<Rightarrow> iswaux \<Rightarrow> iswaux" where
  "isw_ensure msks aux = (case aux of (t, pend, win, c, s) \<Rightarrow> (t, pend, win, c, iensure msks s))"

lemma isw_abs_ensure[simp]: "isw_abs (isw_ensure msks aux) = isw_abs aux"
  by (simp add: isw_abs_def isw_ensure_def icnt_abs_def split: prod.splits)

subsection \<open>Since for general left operands\<close>

type_synonym iemsaux = "ts \<times> ts \<times> bool list \<times>
  (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> event_data itab \<times>
  (event_data tuple, event_data table) mapping \<times> (event_data tuple, ts) mapping \<times>
  (event_data tuple, event_data table) mapping \<times> (event_data tuple, ts) mapping"

fun ims_abs :: "iemsaux \<Rightarrow> event_data emsaux" where
  "ims_abs (t, gc, msk, dp, di, ti, ii, tui, is, tus) = (t, gc, msk, dp, di, iset ti, ii, tui, is, tus)"

fun ims_emb :: "event_data emsaux \<Rightarrow> iemsaux" where
  "ims_emb (t, gc, msk, dp, di, ti, ii, tui, is, tus) = (t, gc, msk, dp, di, itab ti, ii, tui, is, tus)"

fun ieshift_end :: "args \<Rightarrow> ts \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "ieshift_end args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
     (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
     (tuple_in, del) = fold_filter_set discard (tuple_in, {}) in
     (t, gc, msk, data_prev', data_in, isub del table_in,
      eidx_upd args (\<lambda>_. eidx_minus idx_in (eidx msk del)), tuple_in, idx_since, tuple_since))"

fun ieadd_new_ts_msaux' :: "args \<Rightarrow> ts \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "ieadd_new_ts_msaux' args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
     data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
     (tuple_in, add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}))
        move (tuple_in, {}) in
     (nt, gc, msk, data_prev, data_in, iadd add table_in,
      eidx_upd args (\<lambda>_. eidx_union idx_in (eidx msk add)), tuple_in, idx_since, tuple_since))"

definition ieadd_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "ieadd_new_ts_msaux args nt daux = ieadd_new_ts_msaux' args nt (ieshift_end args nt daux)"

fun iegc_msaux :: "args \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "iegc_msaux args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
     tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
     (nt, nt, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      eidx_upd args (\<lambda>_. eidx msk (Mapping.keys tuple_since')), tuple_since'))"

fun ieadd_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "ieadd_new_table_msaux args X (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let X' = minus_keys X tuple_since;
     tuple_since' = upd_set tuple_since (\<lambda>_. t) X';
     idx_since' = eidx_upd args (\<lambda>_. eidx_union idx_since (eidx msk X')) in
     (if memL (args_ivl args) 0 then
        (t, gc, msk, data_prev, append_queue (t, X) data_in, iadd X table_in,
         eidx_upd args (\<lambda>_. eidx_union idx_in (eidx msk X)), upd_set tuple_in (\<lambda>_. t) X,
         idx_since', tuple_since')
      else (t, gc, msk, append_queue (t, X) data_prev, data_in, table_in, idx_in, tuple_in,
         idx_since', tuple_since')))"

fun ieadd_new_table_lz :: "args \<Rightarrow> event_data table \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "ieadd_new_table_lz args X (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if memL (args_ivl args) 0 then
       (t, gc, msk, data_prev, append_queue (t, X) data_in, iadd X table_in,
        eidx_upd args (\<lambda>_. eidx_union idx_in (eidx msk X)), upd_set tuple_in (\<lambda>_. t) X,
        idx_since, tuple_since)
     else ieadd_new_table_msaux args X (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))"

fun iejoin_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "iejoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let pos = args_pos args in
     (if \<forall>i \<in> set msk. \<not> i then
        (let take_all = (([] \<in> Y) = pos) in
         (t, gc, msk, data_prev, data_in,
          if take_all then table_in else itab {},
          if take_all then idx_in else Mapping.empty,
          if take_all then tuple_in else Mapping.empty,
          if take_all then idx_since else Mapping.empty,
          if take_all then tuple_since else Mapping.empty))
      else if \<forall>i \<in> set msk. i then
        (let in_del = (if pos then iset table_in - Y else iset table_in \<inter> Y);
         tuple_in' = mapping_delete_set tuple_in in_del;
         tuple_since' = Mapping.filter (\<lambda>as _. (as \<in> Y) = pos) tuple_since in
         (t, gc, msk, data_prev, data_in, isub in_del table_in, Mapping.empty, tuple_in',
          Mapping.empty, tuple_since'))
      else
        (let in_del = esemi_idx msk (\<not> pos) idx_in Y;
         since_del = esemi_idx msk (\<not> pos) idx_since Y in
         (t, gc, msk, data_prev, data_in, isub in_del table_in,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_in, mapping_delete_set tuple_in in_del,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_since,
          mapping_delete_set tuple_since since_del))))"

fun iegc_join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "iegc_join_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc)
     then iejoin_msaux args Y (iegc_msaux args (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))
     else iejoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
       idx_since, tuple_since))"

definition iegc_join_lz :: "args \<Rightarrow> event_data table \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "iegc_join_lz args Y daux =
    (if memL (args_ivl args) 0 then iejoin_msaux args Y daux else iegc_join_msaux args Y daux)"

fun ieresult_msaux :: "iemsaux \<Rightarrow> event_data itab" where
  "ieresult_msaux (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) = table_in"

fun iems_ensure :: "bool list list \<Rightarrow> iemsaux \<Rightarrow> iemsaux" where
  "iems_ensure msks (nt, gc, msk, dp, di, ti, ii, tui, is, tus) =
     (nt, gc, msk, dp, di, iensure msks ti, ii, tui, is, tus)"

subsubsection \<open>Code of the join\<close>

text \<open>The join's code equation is restated as @{thm [source] ejoin_msaux_code} is.\<close>

definition igjoin_idx :: "bool \<Rightarrow> 'k set \<Rightarrow> ('k, 'b list set) mapping \<Rightarrow>
    'b itab \<times> ('b list, 'v) mapping \<Rightarrow> ('k, 'b list set) mapping \<times> 'b itab \<times> ('b list, 'v) mapping" where
  "igjoin_idx pos Y M acc = (mfilter_keys pos Y M,
     (case acc of (A, tm) \<Rightarrow> (isub (set_of_idx (mfilter_keys (\<not> pos) Y M)) A,
        mapping_delete_set tm (set_of_idx (mfilter_keys (\<not> pos) Y M)))))"

lemma fold_idel_buckets:
  "fold (\<lambda>p (A, tm). (isub (snd p) A, mapping_delete_set tm (snd p))) xs (A, tm)
   = (isub (\<Union>(snd ` set xs)) A, mapping_delete_set tm (\<Union>(snd ` set xs)))"
  by (induct xs arbitrary: A tm)
    (auto simp: isub_isub mapping_delete_set_Un[symmetric] mapping_delete_set_empty)

lemma igjoin_idx_code[code]:
  fixes t :: "('k :: ccompare, 'b list set) mapping_rbt"
  shows "igjoin_idx pos Y (RBT_Mapping t) acc = (case ID CCOMPARE('k) of
      None \<Rightarrow> Code.abort (STR ''igjoin_idx RBT_Mapping: ccompare = None'')
        (\<lambda>_. igjoin_idx pos Y (RBT_Mapping t) acc)
    | Some _ \<Rightarrow> (if pos then
        (let D = RBT_Mapping2.fold (\<lambda>k v acc. if k \<in> Y then acc else (k, v) # acc) t [] in
         (foldr (\<lambda>p. Mapping.delete (fst p)) D (RBT_Mapping t),
          foldr (\<lambda>p (A, tm). (isub (snd p) A, mapping_delete_set tm (snd p))) D acc))
      else (mfilter_keys pos Y (RBT_Mapping t),
        (case acc of (A, tm) \<Rightarrow>
          (isub (set_of_idx (mfilter_keys (\<not> pos) Y (RBT_Mapping t))) A,
           mapping_delete_set tm (set_of_idx (mfilter_keys (\<not> pos) Y (RBT_Mapping t))))))))"
proof (cases "ID CCOMPARE('k)")
  case (Some c)
  then have n: "ID CCOMPARE('k) \<noteq> None" by simp
  obtain A tm where acc: "acc = (A, tm)" by (cases acc)
  show ?thesis
    using Some by (simp add: acc igjoin_idx_def mfilter_keys_True_RBT[OF n]
        set_of_idx_mfilter_keys_False_RBT[OF n] fold_idel_buckets
        Let_def entries_fails_fold foldr_conv_fold del: RBT_Mapping_def)
qed simp

declare [[code drop: iejoin_msaux]]

lemma iejoin_msaux_code[code]:
  "iejoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let pos = args_pos args in
     (if \<forall>i \<in> set msk. \<not> i then
        (let take_all = (([] \<in> Y) = pos) in
         (t, gc, msk, data_prev, data_in,
          if take_all then table_in else itab {},
          if take_all then idx_in else Mapping.empty,
          if take_all then tuple_in else Mapping.empty,
          if take_all then idx_since else Mapping.empty,
          if take_all then tuple_since else Mapping.empty))
      else if \<forall>i \<in> set msk. i then
        (let in_del = (if pos then iset table_in - Y else iset table_in \<inter> Y);
         tuple_in' = mapping_delete_set tuple_in in_del;
         tuple_since' = mfilter_keys pos Y tuple_since in
         (t, gc, msk, data_prev, data_in, isub in_del table_in, Mapping.empty, tuple_in',
          Mapping.empty, tuple_since'))
      else
        (let (idx_in', table_in', tuple_in') = igjoin_idx pos Y idx_in (table_in, tuple_in);
             (idx_since', tuple_since') = gjoin_idx1 pos Y idx_since tuple_since in
         (t, gc, msk, data_prev, data_in, table_in', idx_in', tuple_in', idx_since',
          tuple_since'))))"
  by (simp only: iejoin_msaux.simps Let_def igjoin_idx_def gjoin_idx1_def del_buckets1_def
      mfilter_keys_def esemi_idx_def prod.case)

subsection \<open>Until for closed left operands\<close>

type_synonym iuwaux = "ts queue \<times> uw_entry queue \<times> uw_entry queue \<times> nat \<times> bool \<times> icntset \<times>
  event_data itab list"

definition iuw_abs :: "iuwaux \<Rightarrow> uwaux" where
  "iuw_abs aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (nts, win, rest, len, bend, icnt_abs cc, map iset dn))"

definition iuw_emb :: "uwaux \<Rightarrow> iuwaux" where
  "iuw_emb aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (nts, win, rest, len, bend, (fst cc, itab (snd cc)), map itab dn))"

lemma iuw_abs_tuple[simp]:
  "iuw_abs (nts, win, rest, len, bend, cc, dn) = (nts, win, rest, len, bend, icnt_abs cc, map iset dn)"
  by (simp add: iuw_abs_def)

lemma iuw_abs_emb[simp]: "iuw_abs (iuw_emb a) = a"
  by (simp add: iuw_abs_def iuw_emb_def icnt_abs_def comp_def split: prod.splits)

function iuw_extend :: "args \<Rightarrow> ts \<Rightarrow> uw_entry queue \<Rightarrow> uw_entry queue \<Rightarrow> bool \<Rightarrow> icntset \<Rightarrow>
    uw_entry queue \<times> uw_entry queue \<times> bool \<times> icntset" where
  "iuw_extend args ts0 win rest bend cc =
     (if \<not> bend then (win, rest, bend, cc)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cc)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then iuw_extend args ts0 (append_queue e win) (tl_queue rest')
                        (snd (snd e)) (icnt_add (fst (snd e)) cc)
                 else (win, rest', bend, cc))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, ts0, win, rest, bend, cc). length (linearize rest))")
     (fastforce split: prod.splits)+

declare iuw_extend.simps[simp del]

definition iuw_step :: "args \<Rightarrow> ts \<Rightarrow> iuwaux \<Rightarrow> iuwaux" where
  "iuw_step args ts0 aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (case iuw_extend args ts0 win rest bend cc of (win, rest, bend, cc) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow> (tl_queue nts, win', rest, len - 1, bend, cc, itab {} # dn)
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                cc' = icnt_del (fst (snd e)) cc;
                bend' = (if Queue.is_empty win'' then True else bend)
            in (tl_queue nts, win'', rest, len - 1, bend', cc', snd cc # dn)))))"

lemma snd_icnt_abs[simp]: "snd (icnt_abs cc) = iset (snd cc)"
  by (simp add: icnt_abs_def)

function iuw_shift :: "args \<Rightarrow> ts \<Rightarrow> iuwaux \<Rightarrow> iuwaux" where
  "iuw_shift args nt aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> (nts', win, rest, len, bend, cc, dn)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then (nts', win, rest, len, bend, cc, dn)
         else iuw_shift args nt (iuw_step args ts0 (nts', win, rest, len, bend, cc, dn)))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(args, nt, (nts, win, rest, len, bend, cc, dn)). len)")
     (auto simp: iuw_step_def Let_def split: prod.splits option.splits)

declare iuw_shift.simps[simp del]

definition iuw_add_new :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> iuwaux \<Rightarrow> iuwaux" where
  "iuw_add_new args rel1 rel2 nt aux =
     (case iuw_shift args nt aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in (append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn)))"

definition iuw_eval :: "args \<Rightarrow> ts \<Rightarrow> iuwaux \<Rightarrow> event_data itab list \<times> iuwaux" where
  "iuw_eval args nt aux =
     (case iuw_shift args nt aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
       (rev dn, (nts, win, rest, len, bend, cc, [])))"

definition iuw_ensure :: "bool list list \<Rightarrow> iuwaux \<Rightarrow> iuwaux" where
  "iuw_ensure msks aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (nts, win, rest, len, bend, (fst cc, iensure msks (snd cc)), dn))"

lemma iuw_abs_ensure[simp]: "iuw_abs (iuw_ensure msks aux) = iuw_abs aux"
  by (simp add: iuw_abs_def iuw_ensure_def icnt_abs_def split: prod.splits)

subsection \<open>Dispatched Since structures\<close>

text \<open>Only the windows embedded with some masks keep indices (@{text iudsx_emb}).\<close>

datatype iudsaux_x = IUDSX_u udsaux_x | IUDSX_win iswaux | IUDSX_gen iemsaux

fun riu :: "iudsaux_x \<Rightarrow> udsaux_x" where
  "riu (IUDSX_u d) = d"
| "riu (IUDSX_win w) = UDSX_win (isw_abs w)"
| "riu (IUDSX_gen g) = UDSX_gen (ims_abs g)"

definition iudsx_emb :: "bool list list \<Rightarrow> udsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_emb msks d = (if msks = [] then IUDSX_u d else (case d of
       UDSX_win w \<Rightarrow> IUDSX_win (isw_ensure msks (isw_emb w))
     | UDSX_gen g \<Rightarrow> IUDSX_gen (iems_ensure msks (ims_emb g))
     | _ \<Rightarrow> IUDSX_u d))"

fun iudsx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_add_new_ts args nt (IUDSX_u d) = IUDSX_u (udsx_add_new_ts args nt d)"
| "iudsx_add_new_ts args nt (IUDSX_win w) = IUDSX_win (isw_add_new_ts args nt w)"
| "iudsx_add_new_ts args nt (IUDSX_gen g) = IUDSX_gen (ieadd_new_ts_msaux args nt g)"

fun iudsx_join :: "args \<Rightarrow> utable \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_join args X (IUDSX_u d) = IUDSX_u (udsx_join args X d)"
| "iudsx_join args X (IUDSX_win w) = IUDSX_win (isw_join args X w)"
| "iudsx_join args X (IUDSX_gen g) = IUDSX_gen (iegc_join_lz args X g)"

fun iudsx_add_new_table :: "args \<Rightarrow> utable \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_add_new_table args X (IUDSX_u d) = IUDSX_u (udsx_add_new_table args X d)"
| "iudsx_add_new_table args X (IUDSX_win w) = IUDSX_win (isw_add_new_table args X w)"
| "iudsx_add_new_table args X (IUDSX_gen g) = IUDSX_gen (ieadd_new_table_lz args X g)"

fun iudsx_result :: "args \<Rightarrow> iudsaux_x \<Rightarrow> event_data itab" where
  "iudsx_result args (IUDSX_u d) = itab (udsx_result args d)"
| "iudsx_result args (IUDSX_win w) = isw_result w"
| "iudsx_result args (IUDSX_gen g) = ieresult_msaux g"

fun iudsx_ensure :: "bool list list \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_ensure msks (IUDSX_win w) = IUDSX_win (isw_ensure msks w)"
| "iudsx_ensure msks (IUDSX_gen g) = IUDSX_gen (iems_ensure msks g)"
| "iudsx_ensure msks d = d"

subsection \<open>Dispatched Until structures\<close>

datatype iuduaux_x = IUDUX_u uduaux_x | IUDUX_win iuwaux

fun riud :: "iuduaux_x \<Rightarrow> uduaux_x" where
  "riud (IUDUX_u d) = d"
| "riud (IUDUX_win w) = UDUX_win (iuw_abs w)"

definition iudux_emb :: "bool list list \<Rightarrow> uduaux_x \<Rightarrow> iuduaux_x" where
  "iudux_emb msks d = (if msks = [] then IUDUX_u d else (case d of
       UDUX_win w \<Rightarrow> IUDUX_win (iuw_ensure msks (iuw_emb w))
     | _ \<Rightarrow> IUDUX_u d))"

lemma riud_iudux_emb[simp]: "riud (iudux_emb msks d) = d"
  by (cases d) (simp_all add: iudux_emb_def)

fun iudux_add_new :: "args \<Rightarrow> bool list \<Rightarrow> utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> iuduaux_x \<Rightarrow> iuduaux_x" where
  "iudux_add_new args msk rel1 rel2 nt (IUDUX_u d) = IUDUX_u (udux_add_new args msk rel1 rel2 nt d)"
| "iudux_add_new args msk rel1 rel2 nt (IUDUX_win w) = IUDUX_win (iuw_add_new args rel1 rel2 nt w)"

fun iudux_eval :: "args \<Rightarrow> ts \<Rightarrow> iuduaux_x \<Rightarrow> event_data itab list \<times> iuduaux_x" where
  "iudux_eval args nt (IUDUX_u d) = (let (zs, d') = udux_eval args nt d in (map itab zs, IUDUX_u d'))"
| "iudux_eval args nt (IUDUX_win w) = (let (zs, w') = iuw_eval args nt w in (zs, IUDUX_win w'))"

fun iudux_ensure :: "bool list list \<Rightarrow> iuduaux_x \<Rightarrow> iuduaux_x" where
  "iudux_ensure msks (IUDUX_win w) = IUDUX_win (iuw_ensure msks w)"
| "iudux_ensure msks d = d"

lemma riud_ensure[simp]: "riud (iudux_ensure msks d) = riud d"
  by (induct msks d rule: iudux_ensure.induct) simp_all

subsection \<open>Traversal of the Since buffer\<close>

fun iuedsx_eval_since :: "args \<Rightarrow> event_data itab list \<Rightarrow> uebuf2S \<Rightarrow> iudsaux_x \<Rightarrow>
    event_data itab list \<times> uebuf2S \<times> iudsaux_x" where
  "iuedsx_eval_since args rs (xs, ys, ts, skew) aux =
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow>
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
          (if skew \<or> memL (args_ivl args) 0
           then (rev rs, ((mbuf_t_Cons x xs'), mbuf_t_empty, (mbuf_t_Cons t ts'), skew), aux)
           else (let aux' = iudsx_join args x (iudsx_add_new_ts args t aux)
             in (rev (iudsx_result args aux' # rs), (xs', mbuf_t_empty, ts', True), aux')))
        | (None, ts') \<Rightarrow> (rev rs, ((mbuf_t_Cons x xs'), mbuf_t_empty, mbuf_t_empty, skew), aux))
      | (None, xs') \<Rightarrow> (rev rs, (mbuf_t_empty, mbuf_t_empty, ts, skew), aux))
    | (Some y, ys') \<Rightarrow>
      if skew then iuedsx_eval_since args rs (xs, ys', ts, False) (iudsx_add_new_table args y aux)
      else
      (case mbuf_t_cases xs of (Some x1, xs1) \<Rightarrow>
        (case mbuf_t_cases ts of (Some t1, ts1) \<Rightarrow>
          (let aux1 = iudsx_add_new_table args y (iudsx_join args x1 (iudsx_add_new_ts args t1 aux))
           in iuedsx_eval_since args (iudsx_result args aux1 # rs) (xs1, ys', ts1, False) aux1)
        | (None, ts1) \<Rightarrow> (rev rs, ((mbuf_t_Cons x1 xs1), (mbuf_t_Cons y ys'), ts1, skew), aux))
      | (None, xs1) \<Rightarrow> (rev rs, (mbuf_t_empty, (mbuf_t_Cons y ys'), ts, skew), aux)))"

declare iuedsx_eval_since.simps[simp del]

(*<*)
end
(*>*)
