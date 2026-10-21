(*<*)
theory IWindow
  imports Window_Dispatch ITable
begin
(*>*)

section \<open>Since and Until structures with indexed results\<close>

text \<open>
  The Since structure of a closed left operand keeps the union of its window incrementally, as a
  count per tuple and the set of tuples whose count is positive.  Below that set is an indexed
  table (@{typ "event_data itab"}): a tuple whose count becomes positive is inserted into it and
  into each of its indices, a tuple whose count drops to zero is removed from both.  The window
  hands its union out as it is, so a join of the window's result probes the indices instead of
  building one at every time point.  Which indices the set carries is up to the window's
  consumer, who asks for them (@{text isw_ensure}).  Forgetting the indices
  (@{text isw_abs}) maps every operation to the one of @{theory MFODL_Monitor_Exec.Window}, so the
  window's proofs apply unchanged.
\<close>

subsection \<open>The count set\<close>

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

lemma icnt_abs_add1: "icnt_abs (icnt_add1 t cc) = cnt_add1 t (icnt_abs cc)"
  by (cases cc) (simp add: icnt_abs_def icnt_add1_def cnt_add1_def split: option.splits)

lemma icnt_abs_del1: "icnt_abs (icnt_del1 t cc) = cnt_del1 t (icnt_abs cc)"
  by (cases cc) (simp add: icnt_abs_def icnt_del1_def cnt_del1_def split: option.splits)

lemma icnt_abs_fold_add1: "icnt_abs (fold icnt_add1 xs cc) = fold cnt_add1 xs (icnt_abs cc)"
  by (induct xs arbitrary: cc) (simp_all add: icnt_abs_add1)

lemma icnt_abs_fold_del1: "icnt_abs (fold icnt_del1 xs cc) = fold cnt_del1 xs (icnt_abs cc)"
  by (induct xs arbitrary: cc) (simp_all add: icnt_abs_del1)

lemma icnt_abs_add: "icnt_abs (icnt_add T cc) = cnt_add T (icnt_abs cc)"
  by (simp add: icnt_add_def cnt_add_def icnt_abs_fold_add1)

lemma icnt_abs_del: "icnt_abs (icnt_del T cc) = cnt_del T (icnt_abs cc)"
  by (simp add: icnt_del_def cnt_del_def icnt_abs_fold_del1)

subsection \<open>The window\<close>

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

lemma isw_move_abs:
  "isw_move args nt pend win cc = (pend', win', cc') \<Longrightarrow>
     sw_move args nt pend win (icnt_abs cc) = (pend', win', icnt_abs cc')"
proof (induct args nt pend win cc arbitrary: pend' win' cc' rule: isw_move.induct)
  case (1 args nt pend win cc)
  obtain eo pq where h: "safe_hd pend = (eo, pq)" by (cases "safe_hd pend")
  show ?case
  proof (cases eo)
    case None
    then show ?thesis using 1(3) by (simp add: sw_move.simps[of args nt pend] isw_move.simps[of args nt pend] h)
  next
    case (Some e)
    then show ?thesis
      using 1(1)[OF h[symmetric] Some] 1(2)[OF h[symmetric] Some] 1(3)
      by (simp add: sw_move.simps[of args nt pend] isw_move.simps[of args nt pend] h icnt_abs_add
          split: if_splits)
  qed
qed

lemma isw_expire_abs:
  "isw_expire args nt win cc = (win', cc') \<Longrightarrow>
     sw_expire args nt win (icnt_abs cc) = (win', icnt_abs cc')"
proof (induct args nt win cc arbitrary: win' cc' rule: isw_expire.induct)
  case (1 args nt win cc)
  show ?case
    using 1 by (subst sw_expire.simps, subst (asm) isw_expire.simps)
      (auto simp: icnt_abs_del split: prod.splits option.splits if_splits)
qed

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

lemma isw_abs_add_new_ts: "isw_abs (isw_add_new_ts args nt aux) = sw_add_new_ts args nt (isw_abs aux)"
  by (auto simp: isw_abs_def isw_add_new_ts_def sw_add_new_ts_def
      dest!: isw_move_abs isw_expire_abs split: prod.splits)

lemma isw_abs_join: "isw_abs (isw_join args X aux) = sw_join args X (isw_abs aux)"
  by (simp add: isw_abs_def isw_join_def sw_join_def icnt_abs_def split: prod.splits)

lemma isw_abs_add_new_table:
  "isw_abs (isw_add_new_table args X aux) = sw_add_new_table args X (isw_abs aux)"
  by (simp add: isw_abs_def isw_add_new_table_def sw_add_new_table_def icnt_abs_add split: prod.splits)

lemma iset_isw_result: "iset (isw_result aux) = sw_result args (isw_abs aux)"
  by (simp add: isw_abs_def isw_result_def sw_result_def icnt_abs_def split: prod.splits)

lemma isw_abs_ensure[simp]: "isw_abs (isw_ensure msks aux) = isw_abs aux"
  by (simp add: isw_abs_def isw_ensure_def icnt_abs_def split: prod.splits)

subsection \<open>The Since structure of a general left operand\<close>

text \<open>The structure of a general left operand keeps the tuples whose Since holds now in a table
  of its own (@{text table_in}).  That table becomes an indexed one: the tuples entering and
  leaving it at a step update its indices by their own index (@{const iadd}, @{const isub}), and
  the structure's result is the table itself.\<close>

type_synonym iemsaux = "ts \<times> ts \<times> bool list \<times>
  (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> event_data itab \<times>
  (event_data tuple, event_data table) mapping \<times> (event_data tuple, ts) mapping \<times>
  (event_data tuple, event_data table) mapping \<times> (event_data tuple, ts) mapping"

fun ims_abs :: "iemsaux \<Rightarrow> event_data emsaux" where
  "ims_abs (t, gc, msk, dp, di, ti, ii, tui, is, tus) = (t, gc, msk, dp, di, iset ti, ii, tui, is, tus)"

fun ims_emb :: "event_data emsaux \<Rightarrow> iemsaux" where
  "ims_emb (t, gc, msk, dp, di, ti, ii, tui, is, tus) = (t, gc, msk, dp, di, itab ti, ii, tui, is, tus)"

lemma ims_abs_emb[simp]: "ims_abs (ims_emb a) = a"
  by (cases a rule: emsaux_cases) simp

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

lemma iemsaux_cases:
  fixes daux :: iemsaux
  obtains t gc msk data_prev data_in table_in idx_in tuple_in idx_since tuple_since
  where "daux = (t, gc, msk, data_prev, data_in, table_in, idx_in, tuple_in,
    idx_since, tuple_since)"
  by (metis prod.collapse)

lemma ims_abs_shift_end: "ims_abs (ieshift_end args nt a) = eshift_end args nt (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def fold_filter_set_def split: prod.splits)

lemma ims_abs_add_new_ts': "ims_abs (ieadd_new_ts_msaux' args nt a) = eadd_new_ts_msaux' args nt (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def split: prod.splits)

lemma ims_abs_add_new_ts: "ims_abs (ieadd_new_ts_msaux args nt a) = eadd_new_ts_msaux args nt (ims_abs a)"
  by (simp add: ieadd_new_ts_msaux_def eadd_new_ts_msaux_def ims_abs_shift_end ims_abs_add_new_ts')

lemma ims_abs_gc: "ims_abs (iegc_msaux args a) = egc_msaux args (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def)

lemma ims_abs_add_new_table_msaux:
  "ims_abs (ieadd_new_table_msaux args X a) = eadd_new_table_msaux args X (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def)

lemma ims_abs_add_new_table_lz:
  "ims_abs (ieadd_new_table_lz args X a) = eadd_new_table_lz args X (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp add: Let_def)

lemma ims_abs_join: "ims_abs (iejoin_msaux args Y a) = ejoin_msaux args Y (ims_abs a)"
  by (cases a rule: iemsaux_cases) (auto simp: Let_def)

lemma ims_abs_gc_join: "ims_abs (iegc_join_msaux args Y a) = egc_join_msaux args Y (ims_abs a)"
  by (cases a rule: iemsaux_cases) (simp only: iegc_join_msaux.simps egc_join_msaux.simps ims_abs.simps
      if_distrib[of "ims_abs"] ims_abs_join ims_abs_gc)

lemma ims_abs_gc_join_lz: "ims_abs (iegc_join_lz args Y a) = egc_join_lz args Y (ims_abs a)"
  by (simp add: iegc_join_lz_def egc_join_lz_def ims_abs_join ims_abs_gc_join)

lemma iset_ieresult: "iset (ieresult_msaux a) = eresult_msaux args (ims_abs a)"
  by (cases a rule: iemsaux_cases) simp

lemma ims_abs_ensure[simp]: "ims_abs (iems_ensure msks a) = ims_abs a"
  by (cases a rule: iemsaux_cases) simp

subsection \<open>The Until structure for a closed left operand\<close>

text \<open>The window of the Until structure for a closed left operand keeps the union of its entries
  as the Since window does, and its answers are that union at the time point's departure; with
  the union indexed, so are the answers.\<close>

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

lemma iuw_extend_abs:
  "uw_extend args ts0 win rest bend (icnt_abs cc) =
     (case iuw_extend args ts0 win rest bend cc of (w, r, b, c) \<Rightarrow> (w, r, b, icnt_abs c))"
proof (induct args ts0 win rest bend cc rule: iuw_extend.induct)
  case (1 args ts0 win rest bend cc)
  show ?case
    by (subst uw_extend.simps, subst iuw_extend.simps)
      (use 1 in \<open>auto simp: icnt_abs_add split: prod.splits option.splits\<close>)
qed

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

lemma iuw_abs_step: "iuw_abs (iuw_step args ts0 aux) = uw_step args ts0 (iuw_abs aux)"
proof -
  obtain nts win rest len bend cc dn where a: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux) auto
  obtain win1 rest1 bend1 cc1 where x: "iuw_extend args ts0 win rest bend cc = (win1, rest1, bend1, cc1)"
    by (cases "iuw_extend args ts0 win rest bend cc") auto
  have u: "uw_extend args ts0 win rest bend (icnt_abs cc) = (win1, rest1, bend1, icnt_abs cc1)"
    by (simp add: iuw_extend_abs x)
  obtain eo w' where h: "safe_hd win1 = (eo, w')" by (cases "safe_hd win1")
  show ?thesis
    by (cases eo) (simp_all add: a x u h iuw_abs_def iuw_step_def uw_step_def Let_def icnt_abs_del)
qed

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

lemma iuw_abs_shift: "iuw_abs (iuw_shift args nt aux) = uw_shift args nt (iuw_abs aux)"
proof (induct args nt aux rule: iuw_shift.induct)
  case (1 args nt aux)
  obtain nts win rest len bend cc dn where a: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux) auto
  obtain to nts' where h: "safe_hd nts = (to, nts')" by (cases "safe_hd nts")
  show ?case
  proof (cases to)
    case None
    then show ?thesis
      by (subst iuw_shift.simps, subst uw_shift.simps) (simp add: a h)
  next
    case (Some ts0)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - ts0) \<or> len = 0")
      case True
      then show ?thesis using Some
        by (subst iuw_shift.simps, subst uw_shift.simps) (simp add: a h)
    next
      case False
      note IH = 1[OF a[symmetric] refl refl refl refl refl h[symmetric] Some False]
      show ?thesis using Some False IH[unfolded iuw_abs_step]
        by (subst iuw_shift.simps, subst uw_shift.simps)
          (simp add: a h)
    qed
  qed
qed

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

lemma iuw_abs_add_new: "iuw_abs (iuw_add_new args rel1 rel2 nt aux) = uw_add_new args rel1 rel2 nt (iuw_abs aux)"
  using iuw_abs_shift[of args nt aux]
  by (auto simp: iuw_add_new_def uw_add_new_def iuw_abs_def Let_def split: prod.splits)

lemma iuw_eval_abs: "iuw_eval args nt aux = (zs, aux') \<Longrightarrow>
    uw_eval args nt (iuw_abs aux) = (map iset zs, iuw_abs aux')"
  using iuw_abs_shift[of args nt aux]
  by (auto simp: iuw_eval_def uw_eval_def iuw_abs_def rev_map split: prod.splits)

lemma iuw_abs_ensure[simp]: "iuw_abs (iuw_ensure msks aux) = iuw_abs aux"
  by (simp add: iuw_abs_def iuw_ensure_def icnt_abs_def split: prod.splits)

subsection \<open>The dispatched Since structures\<close>

text \<open>The aggregating structures are kept as they are; their result is a table without
  indices.  The general structure also starts out as it is, and becomes the indexed one when its
  consumer first asks for an index: until then, indexing its table would only cost.\<close>

datatype iudsaux_x = IUDSX_u udsaux_x | IUDSX_win iswaux | IUDSX_gen iemsaux

fun riu :: "iudsaux_x \<Rightarrow> udsaux_x" where
  "riu (IUDSX_u d) = d"
| "riu (IUDSX_win w) = UDSX_win (isw_abs w)"
| "riu (IUDSX_gen g) = UDSX_gen (ims_abs g)"

fun iudsx_emb :: "udsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_emb (UDSX_win w) = IUDSX_win (isw_emb w)"
| "iudsx_emb d = IUDSX_u d"

lemma riu_iudsx_emb[simp]: "riu (iudsx_emb d) = d"
  by (cases d) simp_all

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
| "iudsx_ensure msks (IUDSX_u (UDSX_gen g)) =
     (if msks = [] then IUDSX_u (UDSX_gen g) else IUDSX_gen (iems_ensure msks (ims_emb g)))"
| "iudsx_ensure msks d = d"

lemma riu_add_new_ts[simp]: "riu (iudsx_add_new_ts args nt d) = udsx_add_new_ts args nt (riu d)"
  by (cases d) (simp_all add: isw_abs_add_new_ts ims_abs_add_new_ts)

lemma riu_join[simp]: "riu (iudsx_join args X d) = udsx_join args X (riu d)"
  by (cases d) (simp_all add: isw_abs_join ims_abs_gc_join_lz)

lemma riu_add_new_table[simp]: "riu (iudsx_add_new_table args X d) = udsx_add_new_table args X (riu d)"
  by (cases d) (simp_all add: isw_abs_add_new_table ims_abs_add_new_table_lz)

lemma iset_iudsx_result[simp]: "iset (iudsx_result args d) = udsx_result args (riu d)"
  by (cases d) (simp_all add: iset_isw_result iset_ieresult)

lemma riu_ensure[simp]: "riu (iudsx_ensure msks d) = riu d"
  by (induct msks d rule: iudsx_ensure.induct) simp_all

subsection \<open>The dispatched Until structures\<close>

text \<open>Likewise, only the window of a closed left operand has indexed answers, and it becomes
  indexed when its consumer first asks for an index.\<close>

datatype iuduaux_x = IUDUX_u uduaux_x | IUDUX_win iuwaux

fun riud :: "iuduaux_x \<Rightarrow> uduaux_x" where
  "riud (IUDUX_u d) = d"
| "riud (IUDUX_win w) = UDUX_win (iuw_abs w)"

definition iudux_emb :: "uduaux_x \<Rightarrow> iuduaux_x" where
  "iudux_emb d = IUDUX_u d"

lemma riud_iudux_emb[simp]: "riud (iudux_emb d) = d"
  by (simp add: iudux_emb_def)

fun iudux_add_new :: "args \<Rightarrow> bool list \<Rightarrow> utable \<Rightarrow> utable \<Rightarrow> ts \<Rightarrow> iuduaux_x \<Rightarrow> iuduaux_x" where
  "iudux_add_new args msk rel1 rel2 nt (IUDUX_u d) = IUDUX_u (udux_add_new args msk rel1 rel2 nt d)"
| "iudux_add_new args msk rel1 rel2 nt (IUDUX_win w) = IUDUX_win (iuw_add_new args rel1 rel2 nt w)"

fun iudux_eval :: "args \<Rightarrow> ts \<Rightarrow> iuduaux_x \<Rightarrow> event_data itab list \<times> iuduaux_x" where
  "iudux_eval args nt (IUDUX_u d) = (let (zs, d') = udux_eval args nt d in (map itab zs, IUDUX_u d'))"
| "iudux_eval args nt (IUDUX_win w) = (let (zs, w') = iuw_eval args nt w in (zs, IUDUX_win w'))"

fun iudux_ensure :: "bool list list \<Rightarrow> iuduaux_x \<Rightarrow> iuduaux_x" where
  "iudux_ensure msks (IUDUX_win w) = IUDUX_win (iuw_ensure msks w)"
| "iudux_ensure msks (IUDUX_u (UDUX_win w)) =
     (if msks = [] then IUDUX_u (UDUX_win w) else IUDUX_win (iuw_ensure msks (iuw_emb w)))"
| "iudux_ensure msks d = d"

lemma riud_add_new: "udux_add_new args msk rel1 rel2 nt (riud d) = riud (iudux_add_new args msk rel1 rel2 nt d)"
  by (cases d) (simp_all add: iuw_abs_add_new)

lemma riud_eval:
  "udux_eval args nt (riud d) = (case iudux_eval args nt d of (zs, d') \<Rightarrow> (map iset zs, riud d'))"
proof (cases d)
  case (IUDUX_win w)
  then show ?thesis
    using iuw_eval_abs[of args nt w] by (cases "iuw_eval args nt w") simp
qed (simp add: comp_def split: prod.splits)

lemma riud_ensure[simp]: "riud (iudux_ensure msks d) = riud d"
  by (induct msks d rule: iudux_ensure.induct) simp_all

subsection \<open>The Since buffer's traversal\<close>

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

lemma iuedsx_eval_since_abs:
  "uedsx_eval_since args (map iset rs) buf (riu aux) =
     (case iuedsx_eval_since args rs buf aux of (zs, b, a) \<Rightarrow> (map iset zs, b, riu a))"
proof (induct args rs buf aux rule: iuedsx_eval_since.induct)
  case (1 args rs xs ys ts skew aux)
  obtain y ys' where y: "mbuf_t_cases ys = (y, ys')" by (cases "mbuf_t_cases ys")
  obtain x xs' where x: "mbuf_t_cases xs = (x, xs')" by (cases "mbuf_t_cases xs")
  obtain t ts' where t: "mbuf_t_cases ts = (t, ts')" by (cases "mbuf_t_cases ts")
  note simps = uedsx_eval_since.simps[of args _ xs ys ts skew]
    iuedsx_eval_since.simps[of args _ xs ys ts skew]
  show ?case
  proof (cases y)
    case None
    then show ?thesis
      unfolding simps using x y t by (cases x; cases t) (simp_all add: rev_map Let_def)
  next
    case Y: (Some y1)
    show ?thesis
    proof (cases skew)
      case True
      have IH: "uedsx_eval_since args (map iset rs) (xs, ys', ts, False)
          (udsx_add_new_table args y1 (riu aux)) =
        (case iuedsx_eval_since args rs (xs, ys', ts, False) (iudsx_add_new_table args y1 aux) of
          (zs, b, a) \<Rightarrow> (map iset zs, b, riu a))"
        using 1(1)[OF y[symmetric] Y True] by simp
      show ?thesis
        unfolding simps using y Y True IH by simp
    next
      case False
      show ?thesis
      proof (cases x)
        case None
        then show ?thesis unfolding simps using x y Y False by (simp add: rev_map)
      next
        case X: (Some x1)
        show ?thesis
        proof (cases t)
          case None
          then show ?thesis unfolding simps using x y t Y X False by (simp add: rev_map)
        next
          case T: (Some t1)
          let ?a = "iudsx_add_new_table args y1 (iudsx_join args x1 (iudsx_add_new_ts args t1 aux))"
          have IH: "uedsx_eval_since args (map iset (iudsx_result args ?a # rs)) (xs', ys', ts', False)
              (riu ?a) =
            (case iuedsx_eval_since args (iudsx_result args ?a # rs) (xs', ys', ts', False) ?a of
              (zs, b, a) \<Rightarrow> (map iset zs, b, riu a))"
            by (rule 1(2)[OF y[symmetric] Y False x[symmetric] X t[symmetric] T refl])
          show ?thesis
            unfolding simps using x y t Y X T False IH by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed
(*<*)
end
(*>*)
