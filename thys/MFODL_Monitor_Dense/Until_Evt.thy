(*<*)
theory Until_Evt
  imports Table_Evt "MFODL_Monitor_Devel.Optimized_Until_Deque"
begin
(*>*)

section \<open>Until with a closed left operand, over the pure window union\<close>

text \<open>
  @{text "EVENTUALLY I \<phi>"} is rewritten by the front end into @{text "Until TT I \<phi>"}, and
  @{text "ALWAYS"}, @{text "ONCE"} and @{text "HISTORICALLY"} likewise produce an Until or a
  Since whose left operand is closed.  The general structure then carries a mapping from tuples
  to the last time point at which the left operand held, one such mapping per time point in the
  window.  When the left operand is closed it holds either for every valuation or for none, so
  ``the left operand held throughout @{text "[i, j)"}'' is a property of time points alone, and
  the answer at @{text i} is simply the union of the right operand's tables over a contiguous
  run of time points.

  Both ends of that run move to the right as @{text i} advances: the far end because a later
  @{text i} has a later timestamp and so admits later @{text j}, and the blocking end because
  the first time point at which the left operand fails can only move forward.  A sliding window
  whose ends both advance needs no per-time-point mapping.  This structure keeps the union of
  the window as a count for every tuple, so that adding or removing a table costs one update
  per tuple of that table, and keeps the answer itself as a set that changes only when a count
  reaches or leaves zero.

  Definitions only, no proofs.
\<close>

type_synonym evt_entry = "ts \<times> event_data table \<times> bool"

type_synonym evtaux = "ts queue \<times> evt_entry queue \<times> evt_entry queue \<times> nat \<times> bool \<times>
  (event_data tuple, nat) mapping \<times> event_data table \<times> event_data table list"

text \<open>The window is extended one time point at a time, and stops at the first one whose
timestamp is out of range or at the one after which the left operand fails.\<close>

function evt_extend :: "args \<Rightarrow> ts \<Rightarrow> evt_entry queue \<Rightarrow> evt_entry queue \<Rightarrow> bool \<Rightarrow>
    (event_data tuple, nat) mapping \<Rightarrow> event_data table \<Rightarrow>
    evt_entry queue \<times> evt_entry queue \<times> bool \<times> (event_data tuple, nat) mapping \<times> event_data table" where
  "evt_extend args ts0 win rest bend cnt cur =
     (if \<not> bend then (win, rest, bend, cnt, cur)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cnt, cur)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then (case evt_add (fst (snd e)) (cnt, cur) of (cnt', cur') \<Rightarrow>
                         evt_extend args ts0 (append_queue e win) (tl_queue rest')
                           (snd (snd e)) cnt' cur')
                 else (win, rest', bend, cnt, cur))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, ts0, win, rest, bend, cnt, cur). length (linearize rest))")
     (fastforce split: prod.splits)+

declare evt_extend.simps[simp del]

subsection \<open>Operations\<close>

definition init_evt :: "args \<Rightarrow> evtaux" where
  "init_evt args = (empty_queue, empty_queue, empty_queue, 0, True, Mapping.empty, {}, [])"

definition length_evt :: "args \<Rightarrow> evtaux \<Rightarrow> nat" where
  "length_evt args aux = (case aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
     length done + len)"

text \<open>One time point leaves the structure: the window is extended as far as its timestamp
  allows, the union of the window is the verdict, and the time point itself is dropped.\<close>

definition evt_step :: "args \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> evtaux" where
  "evt_step args ts0 aux = (case aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
     (case evt_extend args ts0 win rest bend cnt cur of (win, rest, bend, cnt, cur) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow>
             (case safe_hd rest of
                (None, rest') \<Rightarrow>
                  (tl_queue nts, win', rest', len - 1, bend, cnt, cur, {} # done)
              | (Some _, rest') \<Rightarrow>
                  (tl_queue nts, win', tl_queue rest', len - 1, bend, cnt, cur, {} # done))
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                (cnt', cur') = evt_del (fst (snd e)) (cnt, cur);
                bend' = (if Queue.is_empty win'' then True else bend)
            in (tl_queue nts, win'', rest, len - 1, bend', cnt', cur', cur # done)))))"

text \<open>A time point leaves the structure as soon as no later one can contribute to it.\<close>

function evt_shift :: "args \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> evtaux" where
  "evt_shift args nt aux = (case aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> (nts', win, rest, len, bend, cnt, cur, done)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then (nts', win, rest, len, bend, cnt, cur, done)
         else evt_shift args nt (evt_step args ts0 (nts', win, rest, len, bend, cnt, cur, done)))))"
  by pat_completeness auto
termination
proof -
  have len: "fst (snd (snd (snd (evt_step args ts0 (nts, win, rest, len, bend, cnt, cur, dn))))) = len - 1"
    for args ts0 nts win rest len bend cnt cur dn
    by (simp add: evt_step_def Let_def split: prod.split option.split)
  show ?thesis
    by (relation "measure (\<lambda>(args, nt, (nts, win, rest, len, bend, cnt, cur, done)). len)")
      (auto simp: len case_prod_beta)
qed

declare evt_shift.simps[simp del]

definition add_new_evt :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> evtaux" where
  "add_new_evt args rel1 rel2 nt aux =
     (case evt_shift args nt aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in (append_queue nt nts, win, append_queue (nt, rel2, b) rest,
            len + 1, bend, cnt, cur, done)))"

definition eval_evt :: "args \<Rightarrow> ts \<Rightarrow> evtaux \<Rightarrow> event_data table list \<times> evtaux" where
  "eval_evt args nt aux =
     (case evt_shift args nt aux of (nts, win, rest, len, bend, cnt, cur, done) \<Rightarrow>
       (rev done, (nts, win, rest, len, bend, cnt, cur, [])))"

text \<open>The structure applies when the left operand is closed, the interval starts at zero so that
every time point of the window contributes, and there is no aggregation.\<close>

definition evt_applies :: "args \<Rightarrow> bool" where
  "evt_applies args \<longleftrightarrow> args_agg args = None \<and> args_L args = [] \<and> memL (args_ivl args) 0"

(*<*)
end
(*>*)