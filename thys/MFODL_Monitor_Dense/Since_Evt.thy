(*<*)
theory Since_Evt
  imports Table_Evt "MFODL_Monitor_Devel.Optimized_Until_Deque"
begin
(*>*)

section \<open>Since with a closed left operand, over the pure window union\<close>

text \<open>
  @{text "ONCE"} and @{text "HISTORICALLY"} produce a Since whose left operand is closed, and
  then the general Since structure carries a mapping from every tuple currently in the window to
  the count of tables it occurs in, which @{const Table_Evt.evt_add} and
  @{const Table_Evt.evt_del} maintain; the mapping degenerates to a plain window union, as here.
  A table whose timestamp has not yet reached the interval is not part of the union yet, so the
  table waits in a second queue until its timestamp is old enough.

  Definitions only, no proofs.
\<close>

type_synonym sevtaux = "ts \<times> (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times>
  (event_data tuple, nat) mapping \<times> event_data table"

text \<open>Tables whose timestamp has become old enough enter the window, unless they are already too
old to be in it at all.\<close>

function sevt_move :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (event_data tuple, nat) mapping \<Rightarrow> event_data table \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times>
    (event_data tuple, nat) mapping \<times> event_data table" where
  "sevt_move args nt pend win cnt cur =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cnt, cur)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then (case evt_add (snd e) (cnt, cur) of (cnt', cur') \<Rightarrow>
                       sevt_move args nt (tl_queue pend') (append_queue e win) cnt' cur')
               else sevt_move args nt (tl_queue pend') win cnt cur)
         else (pend', win, cnt, cur)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, pend, win, cnt, cur). length (linearize pend))")
     (fastforce split: prod.splits)+

declare sevt_move.simps[simp del]

text \<open>Tables whose timestamp has fallen out of the interval leave the window.\<close>

function sevt_expire :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (event_data tuple, nat) mapping \<Rightarrow> event_data table \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (event_data tuple, nat) mapping \<times> event_data table" where
  "sevt_expire args nt win cnt cur =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cnt, cur)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cnt, cur)
         else (case evt_del (snd e) (cnt, cur) of (cnt', cur') \<Rightarrow>
                 sevt_expire args nt (tl_queue win') cnt' cur')))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, win, cnt, cur). length (linearize win))")
     (fastforce split: prod.splits)+

declare sevt_expire.simps[simp del]

subsection \<open>Operations\<close>

definition init_sevt :: "args \<Rightarrow> sevtaux" where
  "init_sevt args = (0, empty_queue, empty_queue, Mapping.empty, {})"

definition add_new_ts_sevt :: "args \<Rightarrow> ts \<Rightarrow> sevtaux \<Rightarrow> sevtaux" where
  "add_new_ts_sevt args nt aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (case sevt_move args nt pend win cnt cur of (pend', win', cnt', cur') \<Rightarrow>
      (case sevt_expire args nt win' cnt' cur' of (win'', cnt'', cur'') \<Rightarrow>
        (nt, pend', win'', cnt'', cur''))))"

text \<open>A closed left operand that fails cuts off everything before the current time point.\<close>

definition join_sevt :: "args \<Rightarrow> event_data table \<Rightarrow> sevtaux \<Rightarrow> sevtaux" where
  "join_sevt args X aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, Mapping.empty, {})))"

definition add_new_table_sevt :: "args \<Rightarrow> event_data table \<Rightarrow> sevtaux \<Rightarrow> sevtaux" where
  "add_new_table_sevt args X aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (case evt_add X (cnt, cur) of (cnt', cur') \<Rightarrow>
              (t, pend, append_queue (t, X) win, cnt', cur'))
      else (t, append_queue (t, X) pend, win, cnt, cur)))"

definition result_sevt :: "args \<Rightarrow> sevtaux \<Rightarrow> event_data table" where
  "result_sevt args aux = (case aux of (t, pend, win, cnt, cur) \<Rightarrow> cur)"

definition sevt_applies :: "args \<Rightarrow> bool" where
  "sevt_applies args \<longleftrightarrow> args_agg args = None \<and> args_L args = []"

(*<*)
end
(*>*)