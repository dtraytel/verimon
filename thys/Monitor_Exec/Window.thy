(*<*)
theory Window
  imports Tuple_Fields "Monitor_Impl.Optimized_Until_Deque" "Monitor_Impl.Optimized_Trigger"
begin
(*>*)



section \<open>The closed-left-operand structures, verified\<close>

text \<open>
  @{text "ONCE I \<phi>"} is @{text "TT SINCE I \<phi>"} and @{text "EVENTUALLY I \<phi>"} is
  @{text "TT UNTIL I \<phi>"}: the left operand is closed, so it holds either for every valuation or
  for none, and ``the left operand held throughout'' is a property of time points alone.  The
  general structures keep a mapping from tuples to time points for the left operand; with a closed
  left operand the answer is the union of the right operand's tables over a contiguous run of time
  points, and both ends of that run only ever move forward.  So a sliding window suffices: the
  tables of the run in a queue, the union of the run as a count per tuple, and the answer as the
  set of tuples whose count is positive.

  This theory defines these two structures for the verified executable evaluator and proves them
  against the abstract specification the kernel's own structures meet: the assumptions of the
  locales @{locale msaux} and @{locale muaux}, specialised to a closed left operand.  The verified
  executable evaluator picks them for a closed left operand, and the simulation theorem covers the
  choice.
\<close>

subsection \<open>A multiset of tuples as a count mapping\<close>

text \<open>
  A window's union is kept incrementally: a count per tuple, and the set of tuples whose count
  is positive.  Adding a table increments the count of each of its tuples; removing it decrements
  them.  The invariant relates the pair to a count function.
\<close>

type_synonym cntset = "(event_data tuple, nat) mapping \<times> event_data table"

definition cnt_add1 :: "event_data tuple \<Rightarrow> cntset \<Rightarrow> cntset" where
  "cnt_add1 t cc = (case cc of (c, s) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (Mapping.update t 1 c, Set.insert t s)
     | Some k \<Rightarrow> (Mapping.update t (k + 1) c, s)))"

definition cnt_del1 :: "event_data tuple \<Rightarrow> cntset \<Rightarrow> cntset" where
  "cnt_del1 t cc = (case cc of (c, s) \<Rightarrow> (case Mapping.lookup c t of
       None \<Rightarrow> (c, s)
     | Some k \<Rightarrow> (if k \<le> 1 then (Mapping.delete t c, Set.remove t s)
                  else (Mapping.update t (k - 1) c, s))))"

definition cnt_add :: "event_data table \<Rightarrow> cntset \<Rightarrow> cntset" where
  "cnt_add T cc = fold cnt_add1 (csl T) cc"

definition cnt_del :: "event_data table \<Rightarrow> cntset \<Rightarrow> cntset" where
  "cnt_del T cc = fold cnt_del1 (csl T) cc"

definition cnt_rep :: "(event_data tuple \<Rightarrow> nat) \<Rightarrow> cntset \<Rightarrow> bool" where
  "cnt_rep f cc \<longleftrightarrow>
     (\<forall>x. Mapping.lookup (fst cc) x = (if f x = 0 then None else Some (f x))) \<and>
     snd cc = {x. 0 < f x}"

lemma lookup_delete_if:
  "Mapping.lookup (Mapping.delete t c) x = (if x = t then None else Mapping.lookup c x)"
  by (cases "x = t") simp_all

lemma cnt_rep_add1:
  assumes "cnt_rep f cc"
  shows "cnt_rep (f(t := f t + 1)) (cnt_add1 t cc)"
proof (cases cc)
  case (Pair c s)
  have L: "\<And>x. Mapping.lookup c x = (if f x = 0 then None else Some (f x))"
    and S: "s = {x. 0 < f x}" using assms Pair by (auto simp: cnt_rep_def)
  show ?thesis
  proof (cases "Mapping.lookup c t")
    case None
    then have ft: "f t = 0" using L[of t] by (auto split: if_splits)
    show ?thesis unfolding cnt_rep_def cnt_add1_def Pair None
      by (auto simp: Mapping.lookup_update' L S ft)
  next
    case (Some k)
    then have ft: "f t = k" and k: "k \<noteq> 0" using L[of t] by (auto split: if_splits)
    show ?thesis unfolding cnt_rep_def cnt_add1_def Pair Some
      by (auto simp: Mapping.lookup_update' L S ft k)
  qed
qed

lemma cnt_rep_fold_add1:
  "cnt_rep f cc \<Longrightarrow> distinct xs \<Longrightarrow>
     cnt_rep (\<lambda>x. if x \<in> set xs then f x + 1 else f x) (fold cnt_add1 xs cc)"
proof (induct xs arbitrary: f cc)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have r: "cnt_rep (f(x := f x + 1)) (cnt_add1 x cc)" by (rule cnt_rep_add1[OF Cons.prems(1)])
  have "cnt_rep (\<lambda>y. if y \<in> set xs then (f(x := f x + 1)) y + 1 else (f(x := f x + 1)) y)
      (fold cnt_add1 xs (cnt_add1 x cc))"
    by (rule Cons.hyps[OF r]) (use Cons.prems(2) in simp)
  moreover have "(\<lambda>y. if y \<in> set xs then (f(x := f x + 1)) y + 1 else (f(x := f x + 1)) y)
      = (\<lambda>y. if y \<in> set (x # xs) then f y + 1 else f y)"
    using Cons.prems(2) by (auto simp: fun_eq_iff)
  ultimately show ?case by simp
qed

lemma csorted_list_of_set_etuple:
  "finite (X :: event_data table) \<Longrightarrow>
     set (csorted_list_of_set X) = X \<and> distinct (csorted_list_of_set X)"
  using ID_ccompare_etuple_dq by (subst csorted_list_of_set_split) auto

lemma cnt_rep_add:
  assumes "cnt_rep f cc" and "finite T"
  shows "cnt_rep (\<lambda>x. if x \<in> T then f x + 1 else f x) (cnt_add T cc)"
  using cnt_rep_fold_add1[OF assms(1), of "csorted_list_of_set T"]
    csorted_list_of_set_etuple[OF assms(2)]
  unfolding cnt_add_def csl_finite[OF assms(2)] by simp

text \<open>The count function of a list of tables: how many of them contain a tuple.\<close>

definition cnt_of :: "event_data table list \<Rightarrow> event_data tuple \<Rightarrow> nat" where
  "cnt_of Ts x = length (filter (\<lambda>T. x \<in> T) Ts)"

abbreviation cnt_inv :: "event_data table list \<Rightarrow> cntset \<Rightarrow> bool" where
  "cnt_inv Ts cc \<equiv> cnt_rep (cnt_of Ts) cc"

text \<open>The tables of a list at one timestamp.\<close>

definition tbls_at :: "ts \<Rightarrow> (ts \<times> event_data table) list \<Rightarrow> event_data table" where
  "tbls_at u es = \<Union> {rel. (u, rel) \<in> set es}"

lemma tbls_at_Nil[simp]: "tbls_at u [] = {}"
  by (simp add: tbls_at_def)

subsection \<open>The Since structure for a closed left operand\<close>

text \<open>
  Two queues of tables, oldest first: the ones whose timestamp is not yet old enough to be in
  the window, and the window itself; and the window's union as a count set.  For Since a non-zero
  left bound delays a table's entry into the window rather than excluding it, so a table waits in
  the first queue until it is old enough, enters the window, and leaves it when it is too old.
  Both queues are sorted and every table of the window is older than every waiting one.
\<close>

type_synonym swaux = "ts \<times> (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> cntset"

function sw_move :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> cntset" where
  "sw_move args nt pend win cc =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cc)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then sw_move args nt (tl_queue pend') (append_queue e win) (cnt_add (snd e) cc)
               else sw_move args nt (tl_queue pend') win cc)
         else (pend', win, cc)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, pend, win, cc). length (linearize pend))")
     (fastforce split: prod.splits)+

declare sw_move.simps[simp del]

function sw_expire :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow>
    (ts \<times> event_data table) queue \<times> cntset" where
  "sw_expire args nt win cc =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cc)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cc)
         else sw_expire args nt (tl_queue win') (cnt_del (snd e) cc)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, nt, win, cc). length (linearize win))")
     (fastforce split: prod.splits)+

declare sw_expire.simps[simp del]

definition sw_init :: "args \<Rightarrow> swaux" where
  "sw_init args = (0, empty_queue, empty_queue, Mapping.empty, {})"

definition sw_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> swaux \<Rightarrow> swaux" where
  "sw_add_new_ts args nt aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (case sw_move args nt pend win cc of (pend', win', cc') \<Rightarrow>
      (case sw_expire args nt win' cc' of (win'', cc'') \<Rightarrow> (nt, pend', win'', cc''))))"

text \<open>A closed left operand that fails cuts off everything before the current time point.\<close>

definition sw_join :: "args \<Rightarrow> event_data table \<Rightarrow> swaux \<Rightarrow> swaux" where
  "sw_join args X aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, Mapping.empty, {})))"

definition sw_add_new_table :: "args \<Rightarrow> event_data table \<Rightarrow> swaux \<Rightarrow> swaux" where
  "sw_add_new_table args X aux = (case aux of (t, pend, win, cc) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (t, pend, append_queue (t, X) win, cnt_add X cc)
      else (t, append_queue (t, X) pend, win, cc)))"

definition sw_result :: "args \<Rightarrow> swaux \<Rightarrow> event_data table" where
  "sw_result args aux = (case aux of (t, pend, win, cc) \<Rightarrow> snd cc)"

subsubsection \<open>Validity\<close>

text \<open>
  The structure is valid for the abstract auxiliary list when: the waiting queue holds the
  entries whose timestamp is not yet in the interval's range, the window holds the ones that are,
  both sorted, the window older than the waiting queue; the count set is the window's; and, at
  every timestamp, the tables of the two queues together are the tables of the auxiliary list.
  The auxiliary list is in turn required to hold only entries within the interval's right bound,
  which is what the kernel's shift guarantees.
\<close>

definition sw_inv :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) list \<Rightarrow>
    (ts \<times> event_data table) list \<Rightarrow> bool" where
  "sw_inv args cur pl wl \<longleftrightarrow>
     sorted_wrt (\<lambda>e e'. fst e \<le> fst e') pl \<and> sorted_wrt (\<lambda>e e'. fst e \<le> fst e') wl \<and>
     (\<forall>e \<in> set pl. fst e \<le> cur \<and> \<not> memL (args_ivl args) (cur - fst e) \<and> finite (snd e)) \<and>
     (\<forall>e \<in> set wl. fst e \<le> cur \<and> memL (args_ivl args) (cur - fst e) \<and>
        memR (args_ivl args) (cur - fst e) \<and> finite (snd e)) \<and>
     (\<forall>e \<in> set wl. \<forall>e' \<in> set pl. fst e \<le> fst e')"

definition valid_sw :: "args \<Rightarrow> ts \<Rightarrow> swaux \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_sw args cur aux auxlist \<longleftrightarrow> (case aux of (t, pend, win, cc) \<Rightarrow>
     t = cur \<and> sw_inv args cur (linearize pend) (linearize win) \<and>
     cnt_inv (map snd (linearize win)) cc \<and>
     (\<forall>u. tbls_at u (linearize pend @ linearize win) = tbls_at u auxlist) \<and>
     (\<forall>e \<in> set auxlist. fst e \<le> cur \<and> memR (args_ivl args) (cur - fst e) \<and>
        table (args_R args) (snd e)))"

subsection \<open>The Until structure for a closed left operand\<close>

text \<open>
  One entry per pending time point, oldest first, holding the time point's timestamp, the right
  operand's table and whether the left operand held: the entries already in the window of the
  oldest pending time point, and the rest.  The window is extended lazily, one entry at a time,
  and stops at the first entry out of the interval's range or at the one after which the left
  operand fails; both ends only move forward.  When the oldest time point can no longer be
  affected by the future, its answer is the window's union, and the window slides.  The answers
  accumulate, newest first, until the evaluator reads them.
\<close>

type_synonym uw_entry = "ts \<times> event_data table \<times> bool"

type_synonym uwaux = "ts queue \<times> uw_entry queue \<times> uw_entry queue \<times> nat \<times> bool \<times> cntset \<times>
  event_data table list"

function uw_extend :: "args \<Rightarrow> ts \<Rightarrow> uw_entry queue \<Rightarrow> uw_entry queue \<Rightarrow> bool \<Rightarrow> cntset \<Rightarrow>
    uw_entry queue \<times> uw_entry queue \<times> bool \<times> cntset" where
  "uw_extend args ts0 win rest bend cc =
     (if \<not> bend then (win, rest, bend, cc)
      else (case safe_hd rest of
              (None, rest') \<Rightarrow> (win, rest', bend, cc)
            | (Some e, rest') \<Rightarrow>
                (if memR (args_ivl args) (fst e - ts0)
                 then uw_extend args ts0 (append_queue e win) (tl_queue rest')
                        (snd (snd e)) (cnt_add (fst (snd e)) cc)
                 else (win, rest', bend, cc))))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, ts0, win, rest, bend, cc). length (linearize rest))")
     (fastforce split: prod.splits)+

declare uw_extend.simps[simp del]

definition uw_init :: "args \<Rightarrow> uwaux" where
  "uw_init args = (empty_queue, empty_queue, empty_queue, 0, True, (Mapping.empty, {}), [])"

text \<open>The oldest pending time point leaves: its window is extended as far as its timestamp
  allows, the window's union is its answer, and its own entry is dropped from the window.\<close>

definition uw_step :: "args \<Rightarrow> ts \<Rightarrow> uwaux \<Rightarrow> uwaux" where
  "uw_step args ts0 aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (case uw_extend args ts0 win rest bend cc of (win, rest, bend, cc) \<Rightarrow>
        (case safe_hd win of
           (None, win') \<Rightarrow> (tl_queue nts, win', rest, len - 1, bend, cc, {} # dn)
         | (Some e, win') \<Rightarrow>
           (let win'' = tl_queue win';
                cc' = cnt_del (fst (snd e)) cc;
                bend' = (if Queue.is_empty win'' then True else bend)
            in (tl_queue nts, win'', rest, len - 1, bend', cc', snd cc # dn)))))"

function uw_shift :: "args \<Rightarrow> ts \<Rightarrow> uwaux \<Rightarrow> uwaux" where
  "uw_shift args nt aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (case safe_hd nts of
        (None, nts') \<Rightarrow> (nts', win, rest, len, bend, cc, dn)
      | (Some ts0, nts') \<Rightarrow>
        (if memR (args_ivl args) (nt - ts0) \<or> len = 0
         then (nts', win, rest, len, bend, cc, dn)
         else uw_shift args nt (uw_step args ts0 (nts', win, rest, len, bend, cc, dn)))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(args, nt, (nts, win, rest, len, bend, cc, dn)). len)")
     (auto simp: uw_step_def Let_def split: prod.splits option.splits)

declare uw_shift.simps[simp del]

definition uw_add_new :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> uwaux \<Rightarrow> uwaux" where
  "uw_add_new args rel1 rel2 nt aux =
     (case uw_shift args nt aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
       (let b = (if args_pos args then \<not> Set.is_empty rel1 else Set.is_empty rel1)
        in (append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn)))"

definition uw_eval :: "args \<Rightarrow> ts \<Rightarrow> uwaux \<Rightarrow> event_data table list \<times> uwaux" where
  "uw_eval args nt aux =
     (case uw_shift args nt aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
       (rev dn, (nts, win, rest, len, bend, cc, [])))"

subsubsection \<open>The abstract auxiliary list of a run of entries\<close>

text \<open>
  The kernel's auxiliary list holds, for each pending time point, the accumulated left operand
  and the accumulated answer.  With a closed left operand the first is the unit table or empty
  according to whether the left operand held at every pending time point from this one on, and
  the second is the union of the right operand's tables over the run that starts at this time
  point and stops at the first one out of range or the first one after which the left operand
  fails.
\<close>

definition uw_a1 :: "args \<Rightarrow> bool list \<Rightarrow> event_data table" where
  "uw_a1 args bs = (if (\<forall>b \<in> set bs. b) = args_pos args then unit_table else {})"

fun uw_a2 :: "\<I> \<Rightarrow> ts \<Rightarrow> uw_entry list \<Rightarrow> event_data table" where
  "uw_a2 I t0 [] = {}"
| "uw_a2 I t0 ((t, R, b) # es) =
     (if memR I (t - t0) then R \<union> (if b then uw_a2 I t0 es else {}) else {})"

fun uw_abs :: "args \<Rightarrow> uw_entry list \<Rightarrow> event_data muaux" where
  "uw_abs args [] = []"
| "uw_abs args ((t, R, b) # es) =
     (t, uw_a1 args (b # map (snd \<circ> snd) es), uw_a2 (args_ivl args) t ((t, R, b) # es)) # uw_abs args es"

lemma length_uw_abs[simp]: "length (uw_abs args es) = length es"
  by (induct es rule: uw_abs.induct) simp_all

text \<open>The abstract list of the expired entries is what the kernel's evaluation pops.\<close>

subsubsection \<open>Extending the window\<close>

text \<open>The entries the extension adds: from the rest, while in range from the window's start and
  while the left operand keeps holding.\<close>

fun uw_ext :: "\<I> \<Rightarrow> ts \<Rightarrow> bool \<Rightarrow> uw_entry list \<Rightarrow> uw_entry list" where
  "uw_ext I ts0 False rl = []"
| "uw_ext I ts0 True [] = []"
| "uw_ext I ts0 True (e # rl) =
     (if memR I (fst e - ts0) then e # uw_ext I ts0 (snd (snd e)) rl else [])"

subsubsection \<open>The window invariant\<close>

text \<open>
  Relative to a start timestamp: every entry of the window is in range from it, every entry
  but the last saw the left operand hold, and the flag says whether the last one did (or the
  window is empty).
\<close>

definition uw_win :: "\<I> \<Rightarrow> ts \<Rightarrow> uw_entry list \<Rightarrow> bool \<Rightarrow> bool" where
  "uw_win I ts0 wl bend \<longleftrightarrow>
     (\<forall>e \<in> set wl. memR I (fst e - ts0)) \<and>
     (\<forall>e \<in> set (butlast wl). snd (snd e)) \<and>
     bend = (wl = [] \<or> snd (snd (last wl)))"

subsubsection \<open>Validity\<close>

text \<open>
  The pending entries are the window followed by the rest; the pending timestamps are theirs,
  sorted; the count set is the window's; the window invariant holds relative to the oldest
  pending timestamp.  The abstract auxiliary list is the abstract list of the expired entries,
  whose answers are in the accumulator, followed by the abstract list of the pending ones.
\<close>

fun uw_es :: "uwaux \<Rightarrow> uw_entry list" where
  "uw_es (nts, win, rest, len, bend, cc, dn) = linearize win @ linearize rest"

definition valid_uw :: "args \<Rightarrow> ts \<Rightarrow> uwaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_uw args cur aux auxlist \<longleftrightarrow> (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow>
     (let es = linearize win @ linearize rest in
      linearize nts = map fst es \<and> len = length es \<and>
      sorted_wrt (\<lambda>e e'. fst e \<le> fst e') es \<and>
      (\<forall>e \<in> set es. fst e \<le> cur \<and> table (args_R args) (fst (snd e)) \<and>
         finite (fst (snd e))) \<and>
      cnt_inv (map (fst \<circ> snd) (linearize win)) cc \<and>
      uw_win (args_ivl args) (case es of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) (linearize win) bend \<and>
      (\<exists>ex. auxlist = ex @ uw_abs args es \<and> map proj_thd ex = rev dn \<and>
         (\<forall>e \<in> set ex. \<not> memR (args_ivl args) (cur - fst e)))))"

fun uw_len :: "uwaux \<Rightarrow> nat" where
  "uw_len (nts, win, rest, len, bend, cc, dn) = len"

end
(*>*)
