(*<*)
theory Exec_Since
  imports Exec_Tables "MFODL_Logic.Specification"
begin
(*>*)

section \<open>Executable Since structure\<close>

subsection \<open>Index operations\<close>

definition eidx_union :: "('b list, 'b list set) mapping \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "eidx_union = Mapping.combine (\<union>)"

lemma eidx_union_eq: "eidx msk (S \<union> A) = eidx_union (eidx msk S) (eidx msk A)"
proof -
  have "Mapping.lookup (eidx msk (S \<union> A)) k
      = Mapping.lookup (eidx_union (eidx msk S) (eidx msk A)) k" for k
  proof -
    have eS: "k \<notin> eproj msk ` S \<Longrightarrow> {y \<in> S. eproj msk y = k} = {}" by auto
    have eA: "k \<notin> eproj msk ` A \<Longrightarrow> {y \<in> A. eproj msk y = k} = {}" by auto
    have u: "{y \<in> S \<union> A. eproj msk y = k}
        = {y \<in> S. eproj msk y = k} \<union> {y \<in> A. eproj msk y = k}" by auto
    have iU: "(k \<in> eproj msk ` (S \<union> A)) = (k \<in> eproj msk ` S \<or> k \<in> eproj msk ` A)" by auto
    show ?thesis
      by (simp add: eidx_union_def Mapping.lookup_combine lookup_eidx combine_options_def
          u iU eS eA) blast
  qed
  then show ?thesis by (simp add: mapping_eqI)
qed

definition ebucket :: "('b list, 'b list set) mapping \<Rightarrow> 'b list \<Rightarrow> 'b list set" where
  "ebucket d k = (case Mapping.lookup d k of None \<Rightarrow> {} | Some Z \<Rightarrow> Z)"

definition eidx_minus :: "('b list, 'b list set) mapping \<Rightarrow> ('b list, 'b list set) mapping \<Rightarrow>
    ('b list, 'b list set) mapping" where
  "eidx_minus i d = Mapping.filter (\<lambda>k Y. Mapping.lookup d k = None \<or> Y \<noteq> {})
     (Mapping.map_values (\<lambda>k Y. Y - ebucket d k) i)"

lemma eidx_minus_eq: "eidx msk (S - D) = eidx_minus (eidx msk S) (eidx msk D)"
proof -
  have "Mapping.lookup (eidx msk (S - D)) k
      = Mapping.lookup (eidx_minus (eidx msk S) (eidx msk D)) k" for k
  proof -
    have b: "{y \<in> S. eproj msk y = k} - ebucket (eidx msk D) k = {y \<in> S - D. eproj msk y = k}"
      by (auto simp: ebucket_def lookup_eidx split: if_splits)
    show ?thesis
      by (auto simp: eidx_minus_def Mapping.lookup_filter Mapping.lookup_map_values lookup_eidx b
          split: option.splits if_splits intro: rev_image_eqI)
  qed
  then show ?thesis by (simp add: mapping_eqI)
qed

subsection \<open>State and invariant\<close>

definition emsk_args :: "args \<Rightarrow> bool list \<Rightarrow> bool" where
  "emsk_args args msk \<longleftrightarrow> sorted_wrt (<) (args_R args) \<and> sorted_wrt (<) (args_L args) \<and>
     set (args_L args) \<subseteq> set (args_R args) \<and> msk = mrg_left_key (mrg_plan (args_R args) (args_L args))"

text \<open>
  The verified state with its two indexed tables replaced by @{const eidx} indices;
  @{text emsaux_of} recovers the verified state, for the specification only.
\<close>

type_synonym 'a emsaux = "ts \<times> ts \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times> 'a table \<times>
  ('a tuple, 'a table) mapping \<times> ('a tuple, ts) mapping \<times>
  ('a tuple, 'a table) mapping \<times> ('a tuple, ts) mapping"

text \<open>Only the general branch of the join reads the index, so none is kept without join columns
  or with only join columns.\<close>

definition eidx_live :: "args \<Rightarrow> bool" where
  "eidx_live args \<longleftrightarrow> args_L args \<noteq> [] \<and> args_L args \<noteq> args_R args"

definition eidx_upd :: "args \<Rightarrow> (unit \<Rightarrow> ('a tuple, 'a table) mapping) \<Rightarrow>
    ('a tuple, 'a table) mapping" where
  "eidx_upd args w = (if eidx_live args then w () else Mapping.empty)"

fun emsaux_of :: "args \<Rightarrow> 'a emsaux \<Rightarrow> 'a mmsaux" where
  "emsaux_of args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
     (nt, gc, data_prev, data_in, table_in, wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
      wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)"

fun mmsaux_norm :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "mmsaux_norm args (nt, gc, data_prev, data_in, table_in, wf_table_in, tuple_in,
      wf_table_since, tuple_since) =
     (nt, gc, data_prev, data_in, table_in,
      wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
      wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)"

fun emsaux_inv :: "args \<Rightarrow> bool list \<Rightarrow> 'a emsaux \<Rightarrow> bool" where
  "emsaux_inv args msk (nt, gc, m, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) \<longleftrightarrow>
     m = msk \<and> (eidx_live args \<longrightarrow> idx_in = eidx msk (Mapping.keys tuple_in)
       \<and> idx_since = eidx msk (Mapping.keys tuple_since))"

definition valid_emsaux :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> 'a emsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool" where
  "valid_emsaux args msk cur daux ys \<longleftrightarrow>
     valid_mmsaux args cur (emsaux_of args daux) ys \<and> emsaux_inv args msk daux"

subsection \<open>Operations without probing\<close>

definition einit_msaux :: "args \<Rightarrow> bool list \<Rightarrow> 'a emsaux" where
  "einit_msaux args msk = (0, 0, msk, empty_queue, empty_queue, {},
     Mapping.empty, Mapping.empty, Mapping.empty, Mapping.empty)"

fun eshift_end :: "args \<Rightarrow> ts \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "eshift_end args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
     (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
     (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
     (t, gc, msk, data_prev', data_in, table_in - del,
      eidx_upd args (\<lambda>_. eidx_minus idx_in (eidx msk del)), tuple_in, idx_since, tuple_since))"

fun eadd_new_ts_msaux' :: "args \<Rightarrow> ts \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "eadd_new_ts_msaux' args nt (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let I = args_ivl args;
     (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
     data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
     (tuple_in, add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}))
        move (tuple_in, {}) in
     (nt, gc, msk, data_prev, data_in, table_in \<union> add,
      eidx_upd args (\<lambda>_. eidx_union idx_in (eidx msk add)), tuple_in, idx_since, tuple_since))"

definition eadd_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "eadd_new_ts_msaux args nt daux = eadd_new_ts_msaux' args nt (eshift_end args nt daux)"

fun egc_msaux :: "args \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "egc_msaux args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
     tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
     (nt, nt, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      eidx_upd args (\<lambda>_. eidx msk (Mapping.keys tuple_since')), tuple_since'))"

fun eadd_new_table_msaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "eadd_new_table_msaux args X (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (let X' = minus_keys X tuple_since;
     tuple_since' = upd_set tuple_since (\<lambda>_. t) X';
     idx_since' = eidx_upd args (\<lambda>_. eidx_union idx_since (eidx msk X')) in
     (if memL (args_ivl args) 0 then
        (t, gc, msk, data_prev, append_queue (t, X) data_in, table_in \<union> X,
         eidx_upd args (\<lambda>_. eidx_union idx_in (eidx msk X)), upd_set tuple_in (\<lambda>_. t) X,
         idx_since', tuple_since')
      else (t, gc, msk, append_queue (t, X) data_prev, data_in, table_in, idx_in, tuple_in,
         idx_since', tuple_since')))"

fun eresult_msaux :: "args \<Rightarrow> 'a emsaux \<Rightarrow> 'a table" where
  "eresult_msaux args (nt, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) = table_in"

subsection \<open>Join\<close>

fun ejoin_msaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "ejoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
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
        (let in_del = esemi_idx msk (\<not> pos) idx_in Y;
         since_del = esemi_idx msk (\<not> pos) idx_since Y in
         (t, gc, msk, data_prev, data_in, table_in - in_del,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_in, mapping_delete_set tuple_in in_del,
          Mapping.filter (\<lambda>k _. (k \<in> Y) = pos) idx_since,
          mapping_delete_set tuple_since since_del))))"

fun egc_join_msaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "egc_join_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc)
     then ejoin_msaux args Y (egc_msaux args (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))
     else ejoin_msaux args Y (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
       idx_since, tuple_since))"

subsection \<open>Intervals containing zero\<close>

text \<open>
  With zero in the interval, @{text data_prev} stays empty and nothing reads @{text tuple_since}
  or @{text idx_since}, so they are not maintained; validity holds for some choice of them.
\<close>

fun eset_since :: "ts \<Rightarrow> ('a tuple, 'a table) mapping \<Rightarrow> ('a tuple, ts) mapping \<Rightarrow> 'a emsaux \<Rightarrow>
    'a emsaux" where
  "eset_since gc' is ts (t, gc, msk, dp, di, ti, ii, tui, idxs, tus) =
     (t, gc', msk, dp, di, ti, ii, tui, is, ts)"

fun eprev_of :: "'a emsaux \<Rightarrow> (ts \<times> 'a table) queue" where
  "eprev_of (t, gc, msk, dp, di, ti, ii, tui, idxs, tus) = dp"

fun eadd_new_table_lz :: "args \<Rightarrow> 'a table \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "eadd_new_table_lz args X (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
      idx_since, tuple_since) =
    (if memL (args_ivl args) 0 then
       (t, gc, msk, data_prev, append_queue (t, X) data_in, table_in \<union> X,
        eidx_upd args (\<lambda>_. eidx_union idx_in (eidx msk X)), upd_set tuple_in (\<lambda>_. t) X,
        idx_since, tuple_since)
     else eadd_new_table_msaux args X (t, gc, msk, data_prev, data_in, table_in, idx_in,
       tuple_in, idx_since, tuple_since))"

definition egc_join_lz :: "args \<Rightarrow> 'a table \<Rightarrow> 'a emsaux \<Rightarrow> 'a emsaux" where
  "egc_join_lz args Y daux =
    (if memL (args_ivl args) 0 then ejoin_msaux args Y daux else egc_join_msaux args Y daux)"

definition valid_emsaux_lz :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> 'a emsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool"
  where
  "valid_emsaux_lz args msk cur daux ys \<longleftrightarrow> (if memL (args_ivl args) 0
     then linearize (eprev_of daux) = [] \<and>
       (\<exists>gc is ts. valid_emsaux args msk cur (eset_since gc is ts daux) ys)
     else valid_emsaux args msk cur daux ys)"

subsection \<open>Validity over ascending columns\<close>

definition emsk :: "cols \<Rightarrow> cols \<Rightarrow> bool list" where
  "emsk cs_R cs_L = mrg_left_key (mrg_plan cs_R cs_L)"

definition esaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data emsaux \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "esaux' kR cR cL args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, rel) \<in> set auxlist. table kR rel) \<and>
     valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur daux (eauxlist kR cR auxlist)"

end
(*>*)
