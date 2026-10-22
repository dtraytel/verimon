(*<*)
theory Frame_Aux
  imports Frame "MFODL_Logic.Specification"
begin
(*>*)



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

text \<open>
  The mask and the arguments describe the same frame: both column lists are ascending, the left
  one's columns are among the right one's, and the mask marks them.  This is what @{const eargs}
  sets up.
\<close>

definition emsk_args :: "args \<Rightarrow> bool list \<Rightarrow> bool" where
  "emsk_args args msk \<longleftrightarrow> sorted_wrt (<) (args_R args) \<and> sorted_wrt (<) (args_L args) \<and>
     set (args_L args) \<subseteq> set (args_R args) \<and> msk = mrg_left_key (mrg_plan (args_R args) (args_L args))"

subsection \<open>The executable Since structure\<close>

text \<open>
  The state is the verified one with the two indexed tables replaced by @{const eidx} indices,
  and the mask carried along.  Everything else -- the two queues, the window's table, and the two
  mappings that carry the timestamps -- is kept verbatim.

  The verified state a executable state stands for is recovered by \<open>emsaux_of\<close> below.  It is a
  specification device only: it rebuilds the two indexed tables from the keys of the mappings,
  which the generated code never does.
\<close>

type_synonym 'a emsaux = "ts \<times> ts \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times> 'a table \<times>
  ('a tuple, 'a table) mapping \<times> ('a tuple, ts) mapping \<times>
  ('a tuple, 'a table) mapping \<times> ('a tuple, ts) mapping"

text \<open>
  The index is consulted only by the general branch of the join.  Where the verified structure
  falls back on the plain key set -- no join columns, or all columns join columns -- the executable
  structure keeps no index at all.
\<close>

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

subsection \<open>The operations that do not probe\<close>

text \<open>
  All but the join leave the probe alone, so each is the verified operation with the index
  maintenance put in place of the indexed table's.  The window's entry and exit are the only
  places where the index changes without the join: a table enters or leaves in one piece, so the
  index is combined with, or reduced by, the index of that table.
\<close>

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

subsection \<open>The join\<close>

text \<open>
  The three branches are the verified ones, read at the ascending frame.  Without join columns the mask is
  all-false, the executable projection of every stored tuple is the empty tuple, and the whole window
  stands or falls with @{term \<open>[] \<in> Y\<close>}.  When every column is a join column the mask is
  all-true, the executable projection is the identity, and the probe table is compared with the stored
  tables directly.  Otherwise the index decides: a bucket's key is what the probe table holds, so
  the surviving tuples are the union of the surviving buckets, and the index of the survivors is
  the restriction of the index.
\<close>

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

subsection \<open>A window that starts at the current time point\<close>

text \<open>
  The two mappings that record since when a tuple has been seen, @{text tuple_since} and its
  index @{text idx_since}, are read at one place only: when a time point moves from
  @{text data_prev}, the part of the window not yet old enough to count, into @{text data_in}.
  When the interval contains zero no time point is ever too young, the insertion puts every
  table into @{text data_in} directly, and @{text data_prev} stays empty -- so the two mappings,
  and the garbage collection that prunes them, are bookkeeping that nothing reads.  The
  operations below skip them in that case.

  Their validity is the verified one for \<^emph>\<open>some\<close> choice of the two mappings and of the time of
  the last collection, @{text eset_since}; the operations that touch them are the only ones
  that change, and on the fields they do not touch they agree with the verified ones.
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

section \<open>The executable Since structure over ascending columns\<close>

text \<open>
  The executable structure is valid for the reordering of the kernel's auxiliary list.
\<close>

definition emsk :: "cols \<Rightarrow> cols \<Rightarrow> bool list" where
  "emsk cs_R cs_L = mrg_left_key (mrg_plan cs_R cs_L)"

definition esaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data emsaux \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "esaux' kR cR cL args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, rel) \<in> set auxlist. table kR rel) \<and>
     valid_emsaux_lz (eargs cR cL args) (emsk cR cL) cur daux (eauxlist kR cR auxlist)"

definition euntil_elem_step_dq :: "('a tuple, nat) mapping \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow> ts + tp \<Rightarrow> 'a tuple \<Rightarrow> 'a until_acc_dq \<Rightarrow> 'a until_acc_dq" where
  "euntil_elem_step_dq a1_map msk pos tp len inz P d as acc =
    (let acc' = (if inz then until_step_dq P d (tp - len) (tp, as) acc else acc) in
     case Mapping.lookup a1_map (eproj msk as) of
        None \<Rightarrow> (if \<not>pos then until_step_dq P d (tp - len) (tp - len, as) acc' else acc')
      | Some tp' \<Rightarrow> until_step_dq P d (tp - len) (if pos then (max (tp - len) tp', as)
          else (max (tp - len) (tp' + 1), as)) acc')"

definition eadd_new_dq :: "args \<Rightarrow> bool list \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
    event_data mmuaux_dq \<Rightarrow> event_data mmuaux_dq" where
  "eadd_new_dq args msk rel1 rel2 nt aux =
    (let (tp, tss, tables, len, result, a1_map, a2_dq, tstp_dq, dn) = shift_dq args nt aux;
     I = args_ivl args; pos = args_pos args; inz = memL I 0;
     new_tstp = (if inz then Inr tp else Inl nt);
     tstp_dq = dq_push nt tstp_dq;
     P = (\<lambda>t. memL I (nt - dq_nth tstp_dq (t - (tp - len))));
     (tbl, a2_dq', result') = fold (euntil_elem_step_dq a1_map msk pos tp len inz P new_tstp)
       (csl rel2) ({}, a2_dq, result);
     tables = append_queue (tbl, new_tstp) tables;
     a2_dq = dq_push Mapping.empty a2_dq';
     a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
       (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
     tss = append_queue nt tss in
     (tp + 1, tss, tables, len + 1, result', a1_map, a2_dq, tstp_dq, dn))"

subsection \<open>The executable Until structure's validity\<close>

definition evalid_muaux :: "args \<Rightarrow> bool list \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow> event_data muaux \<Rightarrow>
    bool" where
  "evalid_muaux args msk cur daux auxlist \<longleftrightarrow> valid_muaux_dq args cur (MU_dq daux) auxlist"

section \<open>The executable Until structure over ascending columns\<close>

definition euaux' :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data mmuaux_dq \<Rightarrow>
    event_data muaux \<Rightarrow> bool" where
  "euaux' kL cL kR cR args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, a1, a2) \<in> set auxlist. table kL a1 \<and> table kR a2) \<and>
     evalid_muaux (eargs cR cL args) (emsk cR cL) cur daux (eauxlist3 kL cL kR cR auxlist)"

section \<open>The match structures over ascending columns\<close>

text \<open>
  The regular-expression nodes need no executable operations of their own.  Every table a match node
  handles lives over the node's own columns or over an atom's, and the reordering turns the
  kernel's operations into the very same operations over the ascending columns: the joins are
  @{thm [source] etabc_join_sub}, the unions are @{thm [source] etabc_Un_img}.  The one thing
  that does not come for free is that the guards really are tables over the node's columns: that
  is the regular expression's safety condition, and the lemmas below carry it.
\<close>

text \<open>The atoms' tables, reordered each at its own columns.\<close>

definition etabcs :: "cols list \<Rightarrow> cols list \<Rightarrow> 'b list set list \<Rightarrow> 'b list set list" where
  "etabcs kss css rels = map (\<lambda>i. etabc (kss ! i) (css ! i) (rels ! i)) [0..<length rels]"

definition wf_atoms :: "cols \<Rightarrow> cols list \<Rightarrow> cols list \<Rightarrow> 'b list set list \<Rightarrow> bool" where
  "wf_atoms ks kss css rels \<longleftrightarrow> length kss = length rels \<and> length css = length rels \<and>
     (\<forall>i < length rels. eframe (kss ! i) (css ! i) \<and> set (kss ! i) \<subseteq> set ks \<and> table (kss ! i) (rels ! i))"

locale eregex_frame =
  fixes ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list"
  assumes fK: "eframe ks cs" and lc: "length css = length \<psi>s"
    and fa: "\<And>i. i < length \<psi>s \<Longrightarrow> eframe (Formula.fv_list (\<psi>s ! i)) (css ! i)"
    and sub: "\<And>i. i < length \<psi>s \<Longrightarrow> Formula.fv (\<psi>s ! i) \<subseteq> set ks"
begin

abbreviation (input) wfrels :: "event_data table list \<Rightarrow> bool" where
  "wfrels rels \<equiv> list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel \<and> finite rel) \<psi>s rels"

abbreviation (input) erels :: "event_data table list \<Rightarrow> event_data table list" where
  "erels rels \<equiv> etabcs (map Formula.fv_list \<psi>s) css rels"

lemma lr: "wfrels rels \<Longrightarrow> length \<psi>s = length rels"
  by (simp add: list_all2_lengthD)

end

subsection \<open>The past-match structure\<close>

text \<open>
  A past-match structure is a list of tabulations indexed by a time stamp; the executable one is the
  same list with every entry reordered.  Since a tabulation is only ever read through
  @{const lookup}, the relation below says just that, and adds the invariant the derivatives
  need: every entry is a table over the node's columns.
\<close>

definition emrd_rel :: "cols \<Rightarrow> cols \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> bool" where
  "emrd_rel ks cs = list_all2 (\<lambda>(t, X) (t', X'). t = t' \<and>
     (\<forall>ms. table ks (lookup X ms)) \<and> (\<forall>ms. lookup X' ms = etabc ks cs (lookup X ms)))"

locale ematchP_frame = eregex_frame ks cs \<psi>s css
  for ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list" +
  fixes rels :: "event_data table list" and mrs :: "mregex list"
  assumes ops: "list_all2 (\<lambda>\<psi> rel. table (Formula.fv_list \<psi>) rel \<and> finite rel) \<psi>s rels"
    and d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set ks = fv_regex (from_mregex ms \<psi>s)"
begin

abbreviation (input) "kss \<equiv> map Formula.fv_list \<psi>s"

end

subsection \<open>The future-match structure\<close>

text \<open>
  A future-match structure keeps, per time stamp, the operands' tables at that time point and the
  result accumulated for it so far.  The executable one keeps the same list with both reordered.
\<close>

definition emld_rel :: "cols \<Rightarrow> cols \<Rightarrow> ty Formula.formula list \<Rightarrow> cols list \<Rightarrow>
    event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> bool" where
  "emld_rel ks cs \<psi>s css = list_all2 (\<lambda>(t, rls, rel) (t', drls, drel). t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table (Formula.fv_list \<psi>) r \<and> finite r) \<psi>s rls \<and>
     drls = etabcs (map Formula.fv_list \<psi>s) css rls \<and> drel = etabc ks cs rel)"

locale ematchF_frame = eregex_frame ks cs \<psi>s css
  for ks cs :: cols and \<psi>s :: "ty Formula.formula list" and css :: "cols list" +
  fixes mrs :: "mregex list"
  assumes d: "distinct mrs"
    and mrsok: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
       Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<psi>s) \<and> ok (length \<psi>s) ms \<and>
       set ks = fv_regex (from_mregex ms \<psi>s)"
begin

abbreviation (input) "kss \<equiv> map Formula.fv_list \<psi>s"

end

section \<open>The Release structure's auxiliary list\<close>

text \<open>The native release keeps, for each pending time point, the tables of the tuples waiting to
  be released and of the tuples still alive, both over the columns of the right operand
  (@{const update_release}). The executable one keeps their short forms; the join with the left
  operand's table, whose columns are among the right operand's, is a membership test of a
  projection (@{const esemi}).\<close>

definition eupdate_release :: "args \<Rightarrow> bool list \<Rightarrow> 'b list set \<Rightarrow> 'b list set \<Rightarrow> ts \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> (ts \<times> 'b list set \<times> 'b list set) list" where
  "eupdate_release args msk rel1 rel2 nt aux =
    map (\<lambda>(t, a1, a2). if memR (args_ivl args) (nt - t)
      then (t, esemi msk (\<not> args_pos args) (a1 \<inter> rel2) rel1, a2 - (a1 - rel2))
      else (t, a1, a2)) aux @
    [(nt, esemi msk (\<not> args_pos args) rel2 rel1, rel2)]"

end
(*>*)
