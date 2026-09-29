(*<*)
theory Dense_Win
  imports "MFODL_Monitor_Devel.Optimized_Until_Deque" "MFODL_Monitor_Devel.Optimized_Trigger"
begin
(*>*)

section \<open>The closed-left-operand windows\<close>

text \<open>
  @{text "ONCE I \<phi>"} is @{text "TT SINCE I \<phi>"} and @{text "EVENTUALLY I \<phi>"} is
  @{text "TT UNTIL I \<phi>"}: the left operand is closed, so it holds either for every valuation or
  for none, and ``the left operand held throughout'' is a property of time points alone.  The
  general structures keep a mapping from tuples to time points for the left operand; with a closed
  left operand the answer is the union of the right operand's tables over a contiguous run of time
  points, and both ends of that run only ever move forward.  So a sliding window suffices: the
  tables of the run in a queue, the union of the run as a count per tuple, and the answer as the
  set of tuples whose count is positive.

  This theory defines these structures and proves them against the assumptions of the kernel's
  locales @{locale msaux} and @{locale muaux}, for a closed left operand.
\<close>

subsection \<open>A multiset of tuples as a count mapping\<close>

text \<open>
  A window's union is kept incrementally: a count per tuple, and the set of tuples whose count
  is positive.  Adding a table increments the count of each of its tuples; removing it decrements
  them.  The two operations are defined pointwise, for any table; the code folds the single-tuple
  steps over the tuples of a red-black tree.
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
  "cnt_add T cc = (case cc of (c, s) \<Rightarrow>
     (Mapping.Mapping (\<lambda>x. if x \<in> T then Some (case Mapping.lookup c x of None \<Rightarrow> 1 | Some k \<Rightarrow> k + 1)
        else Mapping.lookup c x),
      s \<union> {x \<in> T. Mapping.lookup c x = None}))"

definition cnt_del :: "event_data table \<Rightarrow> cntset \<Rightarrow> cntset" where
  "cnt_del T cc = (case cc of (c, s) \<Rightarrow>
     (Mapping.Mapping (\<lambda>x. if x \<in> T then (case Mapping.lookup c x of None \<Rightarrow> None
          | Some k \<Rightarrow> if k \<le> 1 then None else Some (k - 1))
        else Mapping.lookup c x),
      {x \<in> s. \<not> (x \<in> T \<and> (\<exists>k. Mapping.lookup c x = Some k \<and> k \<le> 1))}))"

lemma lookup_Mapping: "Mapping.lookup (Mapping.Mapping f) = f"
  by (rule Mapping.lookup.abs_eq)

lemma cnt_add1_eq: "cnt_add1 t cc = cnt_add {t} cc"
  by (cases cc)
    (auto simp: cnt_add1_def cnt_add_def lookup_Mapping lookup_update' fun_eq_iff
      intro!: mapping_eqI split: option.splits)

lemma cnt_del1_eq: "cnt_del1 t cc = cnt_del {t} cc"
  by (cases cc)
    (auto simp: cnt_del1_def cnt_del_def lookup_Mapping lookup_update' fun_eq_iff
      intro!: mapping_eqI split: option.splits)

lemma cnt_add_insert: "t \<notin> A \<Longrightarrow> cnt_add A (cnt_add {t} cc) = cnt_add (Set.insert t A) cc"
  by (cases cc) (auto simp: cnt_add_def lookup_Mapping intro!: mapping_eqI split: option.splits)

lemma cnt_del_insert: "t \<notin> A \<Longrightarrow> cnt_del A (cnt_del {t} cc) = cnt_del (Set.insert t A) cc"
  by (cases cc) (auto simp: cnt_del_def lookup_Mapping intro!: mapping_eqI split: option.splits)

lemma fold_cnt_add1: "distinct xs \<Longrightarrow> fold cnt_add1 xs cc = cnt_add (set xs) cc"
proof (induction xs arbitrary: cc)
  case Nil
  then show ?case
    by (cases cc) (simp add: cnt_add_def lookup_Mapping mapping_eqI)
next
  case (Cons x xs)
  then show ?case
    by (simp add: cnt_add1_eq cnt_add_insert)
qed

lemma fold_cnt_del1: "distinct xs \<Longrightarrow> fold cnt_del1 xs cc = cnt_del (set xs) cc"
proof (induction xs arbitrary: cc)
  case Nil
  then show ?case
    by (cases cc) (simp add: cnt_del_def lookup_Mapping mapping_eqI)
next
  case (Cons x xs)
  then show ?case
    by (simp add: cnt_del1_eq cnt_del_insert)
qed

lemma cnt_add_code[code]:
  "cnt_add (RBT_set t) cc = fold cnt_add1 (RBT_Set2.keys t) cc"
  "cnt_add (DList_set d) cc = Code.abort (STR ''cnt_add: not a tree'') (\<lambda>_. cnt_add (DList_set d) cc)"
  "cnt_add (Set_Monad xs) cc = Code.abort (STR ''cnt_add: not a tree'') (\<lambda>_. cnt_add (Set_Monad xs) cc)"
  "cnt_add (Collect_set P) cc = Code.abort (STR ''cnt_add: not a tree'') (\<lambda>_. cnt_add (Collect_set P) cc)"
  "cnt_add (Complement Q) cc = Code.abort (STR ''cnt_add: not a tree'') (\<lambda>_. cnt_add (Complement Q) cc)"
  using fold_cnt_add1[of "RBT_Set2.keys t" cc]
  by (simp_all add: RBT_set_conv_keys[OF ID_ccompare_etuple_dq] ID_ccompare_etuple_dq)

lemma cnt_del_code[code]:
  "cnt_del (RBT_set t) cc = fold cnt_del1 (RBT_Set2.keys t) cc"
  "cnt_del (DList_set d) cc = Code.abort (STR ''cnt_del: not a tree'') (\<lambda>_. cnt_del (DList_set d) cc)"
  "cnt_del (Set_Monad xs) cc = Code.abort (STR ''cnt_del: not a tree'') (\<lambda>_. cnt_del (Set_Monad xs) cc)"
  "cnt_del (Collect_set P) cc = Code.abort (STR ''cnt_del: not a tree'') (\<lambda>_. cnt_del (Collect_set P) cc)"
  "cnt_del (Complement Q) cc = Code.abort (STR ''cnt_del: not a tree'') (\<lambda>_. cnt_del (Complement Q) cc)"
  using fold_cnt_del1[of "RBT_Set2.keys t" cc]
  by (simp_all add: RBT_set_conv_keys[OF ID_ccompare_etuple_dq] ID_ccompare_etuple_dq)

text \<open>The invariant relates the pair to a count function.\<close>

definition cnt_rep :: "(event_data tuple \<Rightarrow> nat) \<Rightarrow> cntset \<Rightarrow> bool" where
  "cnt_rep f cc \<longleftrightarrow>
     (\<forall>x. Mapping.lookup (fst cc) x = (if f x = 0 then None else Some (f x))) \<and>
     snd cc = {x. 0 < f x}"

lemma cnt_rep_empty: "cnt_rep (\<lambda>_. 0) (Mapping.empty, {})"
  by (simp add: cnt_rep_def)

lemma cnt_rep_add:
  "cnt_rep f cc \<Longrightarrow> cnt_rep (\<lambda>x. if x \<in> T then f x + 1 else f x) (cnt_add T cc)"
  by (cases cc) (auto simp: cnt_rep_def cnt_add_def lookup_Mapping split: if_splits)

lemma cnt_rep_del:
  "cnt_rep f cc \<Longrightarrow> cnt_rep (\<lambda>x. if x \<in> T then f x - 1 else f x) (cnt_del T cc)"
  by (cases cc) (auto simp: cnt_rep_def cnt_del_def lookup_Mapping split: if_splits)

text \<open>The count function of a list of tables: how many of them contain a tuple.\<close>

definition cnt_of :: "event_data table list \<Rightarrow> event_data tuple \<Rightarrow> nat" where
  "cnt_of Ts x = length (filter (\<lambda>T. x \<in> T) Ts)"

lemma cnt_of_Nil: "cnt_of [] = (\<lambda>_. 0)"
  by (simp add: cnt_of_def fun_eq_iff)

lemma cnt_of_Cons: "cnt_of (T # Ts) = (\<lambda>x. if x \<in> T then cnt_of Ts x + 1 else cnt_of Ts x)"
  by (simp add: cnt_of_def fun_eq_iff)

lemma cnt_of_snoc: "cnt_of (Ts @ [T]) = (\<lambda>x. if x \<in> T then cnt_of Ts x + 1 else cnt_of Ts x)"
  by (simp add: cnt_of_def fun_eq_iff)

lemma cnt_of_tl: "cnt_of Ts = (\<lambda>x. if x \<in> T then cnt_of (T # Ts) x - 1 else cnt_of (T # Ts) x)"
  by (simp add: cnt_of_def fun_eq_iff)

abbreviation cnt_inv :: "event_data table list \<Rightarrow> cntset \<Rightarrow> bool" where
  "cnt_inv Ts cc \<equiv> cnt_rep (cnt_of Ts) cc"

lemma cnt_inv_empty: "cnt_inv [] (Mapping.empty, {})"
  unfolding cnt_of_Nil by (rule cnt_rep_empty)

lemma cnt_inv_snoc: "cnt_inv Ts cc \<Longrightarrow> cnt_inv (Ts @ [T]) (cnt_add T cc)"
  unfolding cnt_of_snoc by (rule cnt_rep_add)

lemma cnt_inv_tl: "cnt_inv (T # Ts) cc \<Longrightarrow> cnt_inv Ts (cnt_del T cc)"
  by (subst cnt_of_tl[of Ts T]) (rule cnt_rep_del)

lemma cnt_inv_adds: "cnt_inv Ts cc \<Longrightarrow> cnt_inv (Ts @ Us) (fold cnt_add Us cc)"
proof (induct Us arbitrary: Ts cc)
  case (Cons U Us)
  have "cnt_inv (Ts @ [U]) (cnt_add U cc)"
    by (rule cnt_inv_snoc[OF Cons.prems])
  then have "cnt_inv ((Ts @ [U]) @ Us) (fold cnt_add Us (cnt_add U cc))"
    by (rule Cons.hyps)
  then show ?case
    by simp
qed simp

lemma cnt_inv_dels: "cnt_inv (Us @ Ts) cc \<Longrightarrow> cnt_inv Ts (fold cnt_del Us cc)"
proof (induct Us arbitrary: cc)
  case (Cons U Us)
  have "cnt_inv (Us @ Ts) (cnt_del U cc)"
    by (rule cnt_inv_tl) (use Cons.prems in simp)
  then have "cnt_inv Ts (fold cnt_del Us (cnt_del U cc))"
    by (rule Cons.hyps)
  then show ?case
    by simp
qed simp

lemma cnt_inv_set: "cnt_inv Ts cc \<Longrightarrow> snd cc = \<Union> (set Ts)"
  by (auto simp: cnt_rep_def cnt_of_def filter_empty_conv)

subsection \<open>Two facts about the closed left operand\<close>

lemma not_memR_mono: "cur \<le> nt \<Longrightarrow> \<not> memR I (cur - a) \<Longrightarrow> \<not> memR I (nt - a)"
  using memR_antimono[of I "nt - a" "cur - a"] diff_le_mono by blast

lemma memR_mono_ts: "t0 \<le> t \<Longrightarrow> memR I (nt - t0) \<Longrightarrow> memR I (nt - t)"
  using memR_antimono[of I "nt - t0" "nt - t"] diff_le_mono2 by blast

lemma check_before_fst: "check_before I nt e \<longleftrightarrow> \<not> memR I (nt - fst e)"
  by (cases e) simp

text \<open>Joining a table with a table over no columns keeps it or empties it, depending only on
  whether that table is empty and on the polarity.\<close>

lemma join_closed:
  assumes "table [] rel1"
  shows "join R rel pos [] rel1 = (if (rel1 \<noteq> {}) = pos then rel else {})"
proof -
  have j: "join1 R [] (x, []) = Some x" for x :: "'a tuple"
    by (simp add: join1.simps restrict_def)
  from assms consider "rel1 = {}" | "rel1 = {[]}"
    by (auto simp: table_empty_vars_iff empty_table_def unit_table_def)
  then show ?thesis
    by cases (cases pos; simp add: join_True_code join_False_code j)+
qed

text \<open>The tables of a list at one timestamp.\<close>

definition tbls_at :: "ts \<Rightarrow> (ts \<times> event_data table) list \<Rightarrow> event_data table" where
  "tbls_at u es = \<Union> {rel. (u, rel) \<in> set es}"

lemma in_tbls_at: "x \<in> tbls_at u es \<longleftrightarrow> (\<exists>rel. (u, rel) \<in> set es \<and> x \<in> rel)"
  by (auto simp: tbls_at_def)

lemma tbls_at_Nil[simp]: "tbls_at u [] = {}"
  by (simp add: tbls_at_def)

lemma tbls_at_Cons: "tbls_at u ((t, rel) # es) = (if t = u then rel \<union> tbls_at u es else tbls_at u es)"
  by (auto simp: tbls_at_def)

lemma tbls_at_append: "tbls_at u (xs @ ys) = tbls_at u xs \<union> tbls_at u ys"
  by (auto simp: tbls_at_def)

lemma tbls_at_filter: "tbls_at u (filter (\<lambda>e. P (fst e)) es) = (if P u then tbls_at u es else {})"
  by (auto simp: tbls_at_def)

lemma tbls_at_map_empty: "tbls_at u (map (\<lambda>(t, rel). (t, {})) es) = {}"
  by (auto simp: tbls_at_def)

lemma foldr_Un_set: "foldr (\<union>) ys {} = \<Union> (set ys)"
  by (induct ys) auto

lemma set_filter_comp:
  "set [rel. (t, rel) \<leftarrow> xs, P t] = {rel. \<exists>t. (t, rel) \<in> set xs \<and> P t}"
proof (induct xs)
  case (Cons e xs)
  obtain t rel where e: "e = (t, rel)" by (cases e)
  show ?case unfolding e using Cons by (cases "P t") auto
qed simp

lemma foldr_Un_filter:
  "foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, P t] {} = \<Union> {rel. \<exists>t. (t, rel) \<in> set xs \<and> P t}"
  unfolding foldr_Un_set set_filter_comp ..

text \<open>A predicate on timestamps that only fails further to the right cuts a sorted list into a
  prefix and a suffix, so the two scans coincide with the two filters.\<close>

lemma takeWhile_antitone:
  assumes s: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') xs"
    and a: "\<And>e e'. fst e \<le> fst e' \<Longrightarrow> P e' \<Longrightarrow> P e"
  shows "takeWhile P xs = filter P xs \<and> dropWhile P xs = filter (\<lambda>e. \<not> P e) xs"
  using s
proof (induct xs)
  case (Cons x xs)
  then have IH: "takeWhile P xs = filter P xs" "dropWhile P xs = filter (\<lambda>e. \<not> P e) xs"
    and le: "\<forall>e \<in> set xs. fst x \<le> fst e" by simp_all
  show ?case
  proof (cases "P x")
    case True
    then show ?thesis using IH by simp
  next
    case False
    have "\<forall>e \<in> set xs. \<not> P e" using le a[of x] False by blast
    then show ?thesis using False by (simp add: filter_empty_conv filter_id_conv)
  qed
qed simp

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

subsubsection \<open>What the two scans do to the queues\<close>

lemma sw_move_rep:
  "linearize pend = pl \<Longrightarrow> sw_move args nt pend win cc = (pend', win', cc') \<Longrightarrow>
     linearize pend' = dropWhile (\<lambda>e. memL (args_ivl args) (nt - fst e)) pl \<and>
     linearize win' = linearize win @ filter (\<lambda>e. memR (args_ivl args) (nt - fst e))
       (takeWhile (\<lambda>e. memL (args_ivl args) (nt - fst e)) pl) \<and>
     cc' = fold cnt_add (map snd (filter (\<lambda>e. memR (args_ivl args) (nt - fst e))
       (takeWhile (\<lambda>e. memL (args_ivl args) (nt - fst e)) pl))) cc"
proof (induct pl arbitrary: pend win cc pend' win' cc')
  case Nil
  obtain ho pend0 where sh: "safe_hd pend = (ho, pend0)" by (cases "safe_hd pend")
  have "ho = None" and "linearize pend0 = []"
    using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  then show ?case using Nil(2) by (subst (asm) sw_move.simps) (simp add: sh)
next
  case (Cons e rest)
  obtain ho pend0 where sh: "safe_hd pend = (ho, pend0)" by (cases "safe_hd pend")
  have l0: "linearize pend0 = e # rest" using safe_hd_rep[OF sh] Cons(2) by simp
  have ho: "ho = Some e" using safe_hd_rep[OF sh] l0 by (cases ho) auto
  have lt: "linearize (tl_queue pend0) = rest" by (simp add: tl_queue_rep l0)
  show ?case
  proof (cases "memL (args_ivl args) (nt - fst e)")
    case True
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - fst e)")
      case r: True
      have "sw_move args nt (tl_queue pend0) (append_queue e win) (cnt_add (snd e) cc)
          = (pend', win', cc')"
        using Cons(3) by (subst (asm) sw_move.simps) (simp add: sh ho True r)
      from Cons(1)[OF lt this] show ?thesis using True r by (simp add: append_queue_rep)
    next
      case r: False
      have "sw_move args nt (tl_queue pend0) win cc = (pend', win', cc')"
        using Cons(3) by (subst (asm) sw_move.simps) (simp add: sh ho True r)
      from Cons(1)[OF lt this] show ?thesis using True r by simp
    qed
  next
    case False
    have "(pend0, win, cc) = (pend', win', cc')"
      using Cons(3) by (subst (asm) sw_move.simps) (simp add: sh ho False)
    then show ?thesis using False l0 by simp
  qed
qed

lemma sw_expire_rep:
  "linearize win = wl \<Longrightarrow> sw_expire args nt win cc = (win', cc') \<Longrightarrow>
     linearize win' = dropWhile (\<lambda>e. \<not> memR (args_ivl args) (nt - fst e)) wl \<and>
     cc' = fold cnt_del (map snd (takeWhile (\<lambda>e. \<not> memR (args_ivl args) (nt - fst e)) wl)) cc"
proof (induct wl arbitrary: win cc win' cc')
  case Nil
  obtain ho win0 where sh: "safe_hd win = (ho, win0)" by (cases "safe_hd win")
  have "ho = None" and "linearize win0 = []"
    using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  then show ?case using Nil(2) by (subst (asm) sw_expire.simps) (simp add: sh)
next
  case (Cons e rest)
  obtain ho win0 where sh: "safe_hd win = (ho, win0)" by (cases "safe_hd win")
  have l0: "linearize win0 = e # rest" using safe_hd_rep[OF sh] Cons(2) by simp
  have ho: "ho = Some e" using safe_hd_rep[OF sh] l0 by (cases ho) auto
  have lt: "linearize (tl_queue win0) = rest" by (simp add: tl_queue_rep l0)
  show ?case
  proof (cases "memR (args_ivl args) (nt - fst e)")
    case True
    have "(win0, cc) = (win', cc')"
      using Cons(3) by (subst (asm) sw_expire.simps) (simp add: sh ho True)
    then show ?thesis using True l0 by simp
  next
    case False
    have "sw_expire args nt (tl_queue win0) (cnt_del (snd e) cc) = (win', cc')"
      using Cons(3) by (subst (asm) sw_expire.simps) (simp add: sh ho False)
    from Cons(1)[OF lt this] show ?thesis using False by simp
  qed
qed

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
     (\<forall>e \<in> set pl. fst e \<le> cur \<and> \<not> memL (args_ivl args) (cur - fst e)) \<and>
     (\<forall>e \<in> set wl. fst e \<le> cur \<and> memL (args_ivl args) (cur - fst e) \<and>
        memR (args_ivl args) (cur - fst e)) \<and>
     (\<forall>e \<in> set wl. \<forall>e' \<in> set pl. fst e \<le> fst e')"

definition valid_sw :: "args \<Rightarrow> ts \<Rightarrow> swaux \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_sw args cur aux auxlist \<longleftrightarrow> (case aux of (t, pend, win, cc) \<Rightarrow>
     t = cur \<and> sw_inv args cur (linearize pend) (linearize win) \<and>
     cnt_inv (map snd (linearize win)) cc \<and>
     (\<forall>u. tbls_at u (linearize pend @ linearize win) = tbls_at u auxlist) \<and>
     (\<forall>e \<in> set auxlist. fst e \<le> cur \<and> memR (args_ivl args) (cur - fst e) \<and>
        table (args_R args) (snd e)))"

lemma valid_sw_init: "valid_sw args 0 (sw_init args) []"
  by (simp add: valid_sw_def sw_init_def sw_inv_def empty_queue_rep cnt_inv_empty)

lemma valid_sw_add_new_ts:
  assumes v: "valid_sw args cur aux auxlist" and nt: "cur \<le> nt"
  shows "valid_sw args nt (sw_add_new_ts args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  obtain t pend win cc where aux: "aux = (t, pend, win, cc)" by (cases aux)
  define pl where "pl = linearize pend"
  define wl where "wl = linearize win"
  let ?I = "args_ivl args"
  let ?P = "\<lambda>e. memL ?I (nt - fst e)"
  let ?Q = "\<lambda>e. memR ?I (nt - fst e)"
  have tc: "t = cur" and inv: "sw_inv args cur pl wl" and cnt: "cnt_inv (map snd wl) cc"
    and at: "\<And>u. tbls_at u (pl @ wl) = tbls_at u auxlist"
    and al: "\<forall>e \<in> set auxlist. fst e \<le> cur \<and> memR ?I (cur - fst e) \<and>
        table (args_R args) (snd e)"
    using v unfolding valid_sw_def aux pl_def wl_def by auto
  have spl: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') pl"
    and swl: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') wl"
    and ipl: "\<forall>e \<in> set pl. fst e \<le> cur \<and> \<not> memL ?I (cur - fst e)"
    and iwl: "\<forall>e \<in> set wl. fst e \<le> cur \<and> memL ?I (cur - fst e) \<and> memR ?I (cur - fst e)"
    and ord: "\<forall>e \<in> set wl. \<forall>e' \<in> set pl. fst e \<le> fst e'"
    using inv unfolding sw_inv_def by auto
  have Pa: "\<And>e e'. fst e \<le> fst e' \<Longrightarrow> ?P e' \<Longrightarrow> ?P e"
    by (rule memL_mono) (auto intro: diff_le_mono2)
  have Qa: "\<And>e e'. fst e \<le> fst e' \<Longrightarrow> \<not> ?Q e' \<Longrightarrow> \<not> ?Q e"
    using memR_antimono[of ?I "nt - fst _" "nt - fst _"] by (auto intro: diff_le_mono2)
  obtain pend1 win1 cc1 where mv: "sw_move args nt pend win cc = (pend1, win1, cc1)"
    by (cases "sw_move args nt pend win cc")
  obtain win2 cc2 where ex: "sw_expire args nt win1 cc1 = (win2, cc2)"
    by (cases "sw_expire args nt win1 cc1")
  have res: "sw_add_new_ts args nt aux = (nt, pend1, win2, cc2)"
    by (simp add: sw_add_new_ts_def aux mv ex)
  note mvr = sw_move_rep[OF pl_def[symmetric] mv]
  have tfdf: "takeWhile ?P pl = filter ?P pl \<and> dropWhile ?P pl = filter (\<lambda>e. \<not> ?P e) pl"
    by (rule takeWhile_antitone[OF spl]) (rule Pa)
  have tf: "takeWhile ?P pl = filter ?P pl" and df: "dropWhile ?P pl = filter (\<lambda>e. \<not> ?P e) pl"
    using tfdf by simp_all
  define mvd where "mvd = filter ?Q (filter ?P pl)"
  have p1: "linearize pend1 = filter (\<lambda>e. \<not> ?P e) pl" using mvr df by simp
  have w1: "linearize win1 = wl @ mvd" using mvr unfolding tf mvd_def wl_def by simp
  have c1: "cc1 = fold cnt_add (map snd mvd) cc" using mvr unfolding tf mvd_def by simp
  have smvd: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') mvd"
    unfolding mvd_def by (intro sorted_wrt_filter spl)
  have mvd_sub: "set mvd \<subseteq> set pl" unfolding mvd_def by auto
  have sw1: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') (wl @ mvd)"
    unfolding sorted_wrt_append using swl smvd ord mvd_sub by blast
  note exr = sw_expire_rep[OF w1 ex]
  have tfdf2: "takeWhile (\<lambda>e. \<not> ?Q e) (wl @ mvd) = filter (\<lambda>e. \<not> ?Q e) (wl @ mvd) \<and>
      dropWhile (\<lambda>e. \<not> ?Q e) (wl @ mvd) = filter (\<lambda>e. \<not> \<not> ?Q e) (wl @ mvd)"
    by (rule takeWhile_antitone[OF sw1]) (rule Qa)
  have tf2: "takeWhile (\<lambda>e. \<not> ?Q e) (wl @ mvd) = filter (\<lambda>e. \<not> ?Q e) (wl @ mvd)"
    and df2: "dropWhile (\<lambda>e. \<not> ?Q e) (wl @ mvd) = filter ?Q (wl @ mvd)"
    using tfdf2 by simp_all
  have fmvd: "filter ?Q mvd = mvd" unfolding mvd_def by (simp add: filter_id_conv)
  have w2: "linearize win2 = filter ?Q wl @ mvd"
    using exr[unfolded df2] by (simp add: fmvd)
  have c2: "cc2 = fold cnt_del (map snd (filter (\<lambda>e. \<not> ?Q e) (wl @ mvd))) cc1"
    using exr[unfolded tf2] by simp
  \<comment> \<open>the count set\<close>
  have cnt1: "cnt_inv (map snd (wl @ mvd)) cc1"
    unfolding c1 using cnt_inv_adds[OF cnt] by simp
  have split: "map snd (wl @ mvd) = map snd (filter (\<lambda>e. \<not> ?Q e) (wl @ mvd))
      @ map snd (filter ?Q (wl @ mvd))"
    unfolding tf2[symmetric] df2[symmetric] by (simp add: map_append[symmetric] del: map_append)
  have cnt2: "cnt_inv (map snd (filter ?Q (wl @ mvd))) cc2"
    unfolding c2 by (rule cnt_inv_dels) (use cnt1[unfolded split] in auto)
  have cnt2': "cnt_inv (map snd (linearize win2)) cc2"
    using cnt2 unfolding w2 by (simp add: fmvd)
  \<comment> \<open>the invariant on the queues\<close>
  have ord2: "\<forall>e \<in> set (filter ?Q wl). \<forall>e' \<in> set mvd. fst e \<le> fst e'"
  proof (intro ballI)
    fix e e' assume "e \<in> set (filter ?Q wl)" and "e' \<in> set mvd"
    then have "e \<in> set wl" and "e' \<in> set pl" using mvd_sub by auto
    then show "fst e \<le> fst e'" using ord by blast
  qed
  have inv': "sw_inv args nt (linearize pend1) (linearize win2)"
    unfolding sw_inv_def p1 w2
  proof (intro conjI)
    show "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') (filter (\<lambda>e. \<not> ?P e) pl)"
      by (intro sorted_wrt_filter spl)
    show "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') (filter ?Q wl @ mvd)"
      unfolding sorted_wrt_append using sorted_wrt_filter[OF swl, of ?Q] smvd ord2 by blast
    show "\<forall>e \<in> set (filter (\<lambda>e. \<not> ?P e) pl). fst e \<le> nt \<and> \<not> memL ?I (nt - fst e)"
      using ipl nt by auto
    show "\<forall>e \<in> set (filter ?Q wl @ mvd).
        fst e \<le> nt \<and> memL ?I (nt - fst e) \<and> memR ?I (nt - fst e)"
    proof
      fix e assume e: "e \<in> set (filter ?Q wl @ mvd)"
      have Qe: "?Q e" using e unfolding mvd_def by auto
      show "fst e \<le> nt \<and> memL ?I (nt - fst e) \<and> memR ?I (nt - fst e)"
      proof (cases "e \<in> set wl")
        case True
        then have "memL ?I (cur - fst e)" "fst e \<le> cur" using iwl by auto
        moreover have "cur - fst e \<le> nt - fst e" using nt by simp
        ultimately show ?thesis using Qe nt by auto
      next
        case False
        then have "e \<in> set mvd" using e by auto
        then show ?thesis using ipl nt unfolding mvd_def by auto
      qed
    qed
    show "\<forall>e \<in> set (filter ?Q wl @ mvd). \<forall>e' \<in> set (filter (\<lambda>e. \<not> ?P e) pl). fst e \<le> fst e'"
    proof (intro ballI)
      fix e e' assume e: "e \<in> set (filter ?Q wl @ mvd)" and e': "e' \<in> set (filter (\<lambda>e. \<not> ?P e) pl)"
      show "fst e \<le> fst e'"
      proof (cases "e \<in> set wl")
        case True
        then show ?thesis using ord e' by auto
      next
        case False
        then have em: "e \<in> set mvd" using e by auto
        then have "?P e" unfolding mvd_def by auto
        moreover have "\<not> ?P e'" using e' by auto
        ultimately show ?thesis using Pa[of e' e] linear[of "fst e'" "fst e"] by blast
      qed
    qed
  qed
  \<comment> \<open>the tables at every timestamp\<close>
  have at': "\<And>u. tbls_at u (linearize pend1 @ linearize win2)
      = tbls_at u (filter (\<lambda>(t, rel). memR ?I (nt - t)) auxlist)"
  proof -
    fix u
    have A: "tbls_at u (filter (\<lambda>(t, rel). memR ?I (nt - t)) auxlist)
        = (if memR ?I (nt - u) then tbls_at u auxlist else {})"
      by (auto simp: tbls_at_def)
    have B: "tbls_at u (filter (\<lambda>e. \<not> ?P e) pl) = (if memL ?I (nt - u) then {} else tbls_at u pl)"
      by (auto simp: tbls_at_def)
    have C: "tbls_at u (filter ?Q wl) = (if memR ?I (nt - u) then tbls_at u wl else {})"
      by (auto simp: tbls_at_def)
    have D: "tbls_at u mvd = (if memR ?I (nt - u) \<and> memL ?I (nt - u) then tbls_at u pl else {})"
      by (auto simp: mvd_def tbls_at_def)
    show "tbls_at u (linearize pend1 @ linearize win2)
        = tbls_at u (filter (\<lambda>(t, rel). memR ?I (nt - t)) auxlist)"
    proof (cases "memR ?I (nt - u)")
      case True
      then show ?thesis unfolding p1 w2 tbls_at_append A B C D at[symmetric]
        by (cases "memL ?I (nt - u)") auto
    next
      case False
      then have "memL ?I (nt - u)" by (rule not_memR_imp_memL)
      then show ?thesis unfolding p1 w2 tbls_at_append A B C D using False by simp
    qed
  qed
  have al': "\<forall>e \<in> set (filter (\<lambda>(t, rel). memR ?I (nt - t)) auxlist).
      fst e \<le> nt \<and> memR ?I (nt - fst e) \<and> table (args_R args) (snd e)"
    using al nt by auto
  show ?thesis unfolding res valid_sw_def prod.case
  proof (intro conjI)
    show "nt = nt" by (rule refl)
    show "sw_inv args nt (linearize pend1) (linearize win2)" by (rule inv')
    show "cnt_inv (map snd (linearize win2)) cc2" by (rule cnt2')
    show "\<forall>u. tbls_at u (linearize pend1 @ linearize win2)
        = tbls_at u (filter (\<lambda>(t, rel). memR ?I (nt - t)) auxlist)" using at' by blast
    show "\<forall>e \<in> set (filter (\<lambda>(t, rel). memR ?I (nt - t)) auxlist).
        fst e \<le> nt \<and> memR ?I (nt - fst e) \<and> table (args_R args) (snd e)"
      by (rule al')
  qed
qed

lemma valid_sw_join:
  assumes v: "valid_sw args cur aux auxlist"
    and t1: "table [] rel1" and X: "(X = {}) = (rel1 = {})"
  shows "valid_sw args cur (sw_join args X aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) [] rel1)) auxlist)"
proof -
  obtain t pend win cc where aux: "aux = (t, pend, win, cc)" by (cases aux)
  have al: "\<forall>e \<in> set auxlist. fst e \<le> cur \<and> memR (args_ivl args) (cur - fst e) \<and>
      table (args_R args) (snd e)"
    using v unfolding valid_sw_def aux by auto
  have jc: "\<And>e. join (args_R args) (snd e) (args_pos args) [] rel1
      = (if (rel1 \<noteq> {}) = args_pos args then snd e else {})"
    by (rule join_closed[OF t1])
  show ?thesis
  proof (cases "(rel1 \<noteq> {}) = args_pos args")
    case True
    have m: "map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) [] rel1)) auxlist = auxlist"
    proof (rule map_idI)
      fix x assume x: "x \<in> set auxlist"
      show "(case x of (t, rel) \<Rightarrow> (t, join (args_R args) rel (args_pos args) [] rel1)) = x"
        using jc[of x] True by (cases x) simp
    qed
    have "sw_join args X aux = aux"
      using True X by (auto simp: sw_join_def aux)
    then show ?thesis using v unfolding m by simp
  next
    case False
    have m: "map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) [] rel1)) auxlist
        = map (\<lambda>(t, rel). (t, {})) auxlist"
    proof (rule map_cong[OF refl])
      fix x assume x: "x \<in> set auxlist"
      show "(case x of (t, rel) \<Rightarrow> (t, join (args_R args) rel (args_pos args) [] rel1)) = (case x of (t, rel) \<Rightarrow> (t, {}))"
        using jc[of x] False by (cases x) simp
    qed
    have "sw_join args X aux = (t, empty_queue, empty_queue, Mapping.empty, {})"
      using False X by (auto simp: sw_join_def aux)
    then show ?thesis using v unfolding m valid_sw_def aux
      by (auto simp: sw_inv_def empty_queue_rep cnt_inv_empty tbls_at_map_empty table_def)
  qed
qed

lemma valid_sw_add_new_table:
  assumes v: "valid_sw args cur aux auxlist"
    and t2: "table (args_R args) rel2"
  shows "valid_sw args cur (sw_add_new_table args rel2 aux)
    (case auxlist of [] \<Rightarrow> [(cur, rel2)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
    (is "valid_sw args cur _ ?al")
proof -
  obtain t pend win cc where aux: "aux = (t, pend, win, cc)" by (cases aux)
  define pl where "pl = linearize pend"
  define wl where "wl = linearize win"
  let ?I = "args_ivl args"
  have tc: "t = cur" and inv: "sw_inv args cur pl wl" and cnt: "cnt_inv (map snd wl) cc"
    and at: "\<And>u. tbls_at u (pl @ wl) = tbls_at u auxlist"
    and al: "\<forall>e \<in> set auxlist. fst e \<le> cur \<and> memR ?I (cur - fst e) \<and>
        table (args_R args) (snd e)"
    using v unfolding valid_sw_def aux pl_def wl_def by auto
  have spl: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') pl"
    and swl: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') wl"
    and ipl: "\<forall>e \<in> set pl. fst e \<le> cur \<and> \<not> memL ?I (cur - fst e)"
    and iwl: "\<forall>e \<in> set wl. fst e \<le> cur \<and> memL ?I (cur - fst e) \<and> memR ?I (cur - fst e)"
    and ord: "\<forall>e \<in> set wl. \<forall>e' \<in> set pl. fst e \<le> fst e'"
    using inv unfolding sw_inv_def by auto
  have at_al: "\<And>u. tbls_at u ?al = (if u = cur then rel2 \<union> tbls_at u auxlist else tbls_at u auxlist)"
    by (cases auxlist) (auto simp: tbls_at_Cons split: prod.splits)
  have al': "\<forall>e \<in> set ?al. fst e \<le> cur \<and> memR ?I (cur - fst e) \<and>
      table (args_R args) (snd e)"
    using al t2 by (cases auxlist) (auto simp: table_def split: prod.splits)
  show ?thesis
  proof (cases "memL ?I 0")
    case True
    have res: "sw_add_new_table args rel2 aux = (cur, pend, append_queue (cur, rel2) win, cnt_add rel2 cc)"
      by (simp add: sw_add_new_table_def aux True tc)
    have pl_Nil: "pl = []"
    proof (rule ccontr)
      assume "pl \<noteq> []"
      then obtain e where "e \<in> set pl" by (cases pl) auto
      then show False using ipl memL_mono[OF True, of "cur - fst e"] by auto
    qed
    have w': "linearize (append_queue (cur, rel2) win) = wl @ [(cur, rel2)]"
      by (simp add: append_queue_rep wl_def)
    have inv': "sw_inv args cur pl (wl @ [(cur, rel2)])"
      unfolding sw_inv_def pl_Nil sorted_wrt_append using swl iwl True by auto
    have cnt': "cnt_inv (map snd (wl @ [(cur, rel2)])) (cnt_add rel2 cc)"
      using cnt_inv_snoc[OF cnt] by simp
    have at': "\<And>u. tbls_at u (pl @ wl @ [(cur, rel2)]) = tbls_at u ?al"
      unfolding at_al at[symmetric] by (auto simp: tbls_at_append tbls_at_Cons)
    show ?thesis unfolding res valid_sw_def using inv' cnt' at' al'
      by (simp add: pl_def[symmetric] w')
  next
    case False
    have res: "sw_add_new_table args rel2 aux = (cur, append_queue (cur, rel2) pend, win, cc)"
      by (simp add: sw_add_new_table_def aux False tc)
    have p': "linearize (append_queue (cur, rel2) pend) = pl @ [(cur, rel2)]"
      by (simp add: append_queue_rep pl_def)
    have inv': "sw_inv args cur (pl @ [(cur, rel2)]) wl"
      unfolding sw_inv_def sorted_wrt_append using spl swl ipl iwl ord False by auto
    have at': "\<And>u. tbls_at u ((pl @ [(cur, rel2)]) @ wl) = tbls_at u ?al"
      unfolding at_al at[symmetric] by (auto simp: tbls_at_append tbls_at_Cons)
    show ?thesis unfolding res valid_sw_def using inv' cnt at' al'
      by (simp add: wl_def[symmetric] p')
  qed
qed

lemma valid_sw_result:
  assumes v: "valid_sw args cur aux auxlist"
  shows "sw_result args aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
proof -
  obtain t pend win cc where aux: "aux = (t, pend, win, cc)" by (cases aux)
  define pl where "pl = linearize pend"
  define wl where "wl = linearize win"
  let ?I = "args_ivl args"
  have inv: "sw_inv args cur pl wl" and cnt: "cnt_inv (map snd wl) cc"
    and at: "\<And>u. tbls_at u (pl @ wl) = tbls_at u auxlist"
    using v unfolding valid_sw_def aux pl_def wl_def by auto
  have ipl: "\<forall>e \<in> set pl. \<not> memL ?I (cur - fst e)"
    and iwl: "\<forall>e \<in> set wl. memL ?I (cur - fst e)"
    using inv unfolding sw_inv_def by auto
  have r: "sw_result args aux = \<Union> (set (map snd wl))"
    using cnt_inv_set[OF cnt] by (simp add: sw_result_def aux)
  have "\<Union> (set (map snd wl)) = \<Union> {rel. \<exists>t. (t, rel) \<in> set auxlist \<and> memL ?I (cur - t)}"
  proof (intro set_eqI iffI)
    fix x assume "x \<in> \<Union> (set (map snd wl))"
    then obtain u rel where e: "(u, rel) \<in> set wl" and xr: "x \<in> rel" by auto
    then have "memL ?I (cur - u)" using iwl by auto
    moreover have "x \<in> tbls_at u auxlist"
      using at[of u, symmetric] e xr by (auto simp: in_tbls_at)
    ultimately show "x \<in> \<Union> {rel. \<exists>t. (t, rel) \<in> set auxlist \<and> memL ?I (cur - t)}"
      by (auto simp: in_tbls_at)
  next
    fix x assume "x \<in> \<Union> {rel. \<exists>t. (t, rel) \<in> set auxlist \<and> memL ?I (cur - t)}"
    then obtain u rel where e: "(u, rel) \<in> set auxlist" and m: "memL ?I (cur - u)" and xr: "x \<in> rel"
      by auto
    have "x \<in> tbls_at u (pl @ wl)" using at[of u] e xr by (auto simp: in_tbls_at)
    then obtain rel' where "(u, rel') \<in> set pl \<or> (u, rel') \<in> set wl" and "x \<in> rel'"
      by (auto simp: in_tbls_at)
    then have "(u, rel') \<in> set wl" using ipl m by fastforce
    then show "x \<in> \<Union> (set (map snd wl))" using \<open>x \<in> rel'\<close> by force
  qed
  then show ?thesis unfolding r foldr_Un_filter .
qed

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

definition uw_length :: "args \<Rightarrow> uwaux \<Rightarrow> nat" where
  "uw_length args aux = (case aux of (nts, win, rest, len, bend, cc, dn) \<Rightarrow> length dn + len)"

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
     (auto simp: uw_step_def split: prod.splits option.splits)

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

text \<open>Appending an entry to a run extends every answer by the new table exactly when the new
  timestamp is in range from the run's start and the left operand held throughout the run.\<close>

lemma uw_a2_snoc:
  assumes "\<forall>e \<in> set es. fst e \<le> nt"
  shows "uw_a2 I t0 (es @ [(nt, R, b)])
    = uw_a2 I t0 es \<union> (if memR I (nt - t0) \<and> (\<forall>e \<in> set es. snd (snd e)) then R else {})"
  using assms
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain t R' b' where e: "e = (t, R', b')" by (cases e)
  have tnt: "t \<le> nt" using Cons.prems e by simp
  show ?case
  proof (cases "memR I (t - t0)")
    case True
    then show ?thesis using Cons unfolding e by (auto simp: Un_assoc)
  next
    case False
    have "\<not> memR I (nt - t0)"
      using False tnt memR_antimono[of I "nt - t0" "t - t0"] diff_le_mono by blast
    then show ?thesis using False unfolding e by simp
  qed
qed

lemma uw_a1_snoc:
  assumes t1: "table [] rel1"
    and b: "b = ((rel1 \<noteq> {}) = args_pos args)"
  shows "(if args_pos args then uw_a1 args bs \<inter> rel1 else uw_a1 args bs \<union> rel1)
    = uw_a1 args (bs @ [b])"
proof -
  from t1 consider "rel1 = {}" | "rel1 = unit_table"
    by (auto simp: table_empty_vars_iff empty_table_def)
  then show ?thesis
    by cases (auto simp: b uw_a1_def unit_table_def)
qed

lemma uw_abs_snoc:
  assumes ts: "\<forall>e \<in> set es. fst e \<le> nt"
    and tbl: "\<forall>e \<in> set es. table (args_R args) (fst (snd e))"
    and t1: "table [] rel1" and t2: "table (args_R args) rel2"
    and inz: "memL (args_ivl args) 0" and L: "args_L args = []"
    and b: "b = ((rel1 \<noteq> {}) = args_pos args)"
  shows "update_until args rel1 rel2 nt (uw_abs args es) = uw_abs args (es @ [(nt, rel2, b)])"
  using ts tbl
proof (induct es)
  case Nil
  have a1: "uw_a1 args [b] = rel1"
  proof -
    have r1: "rel1 = {} \<or> rel1 = unit_table"
      using t1 by (auto simp: table_empty_vars_iff empty_table_def)
    have ne: "unit_table \<noteq> {}" by (simp add: unit_table_def)
    from r1 show ?thesis unfolding b uw_a1_def using ne by (cases "args_pos args") auto
  qed
  show ?case using inz by (simp add: update_until_def a1 empty_table_def)
next
  case (Cons e es)
  obtain t R b' where e: "e = (t, R, b')" by (cases e)
  note IH = Cons(1) and ts = Cons(2)[unfolded e] and tbl = Cons(3)[unfolded e]
  let ?I = "args_ivl args"
  have tnt: "t \<le> nt" using ts by simp
  have upd: "update_until args rel1 rel2 nt (uw_abs args ((t, R, b') # es))
      = (t, if args_pos args then uw_a1 args (b' # map (snd \<circ> snd) es) \<inter> rel1
            else uw_a1 args (b' # map (snd \<circ> snd) es) \<union> rel1,
         if mem ?I (nt - t) then uw_a2 ?I t ((t, R, b') # es) \<union>
            join (args_R args) rel2 (args_pos args) (args_L args) (uw_a1 args (b' # map (snd \<circ> snd) es))
         else uw_a2 ?I t ((t, R, b') # es))
        # update_until args rel1 rel2 nt (uw_abs args es)"
    by (simp add: update_until_def)
  have a1: "(if args_pos args then uw_a1 args (b' # map (snd \<circ> snd) es) \<inter> rel1
      else uw_a1 args (b' # map (snd \<circ> snd) es) \<union> rel1)
      = uw_a1 args ((b' # map (snd \<circ> snd) es) @ [b])"
    by (rule uw_a1_snoc[OF t1 b])
  have jc: "join (args_R args) rel2 (args_pos args) (args_L args) (uw_a1 args (b' # map (snd \<circ> snd) es))
      = (if b' \<and> (\<forall>e \<in> set es. snd (snd e)) then rel2 else {})"
  proof -
    have "table [] (uw_a1 args (b' # map (snd \<circ> snd) es))"
      by (auto simp: uw_a1_def)
    from join_closed[OF this, of "args_R args" rel2 "args_pos args"] show ?thesis
      by (cases "args_pos args") (auto simp: L uw_a1_def unit_table_def)
  qed
  have mem: "mem ?I (nt - t) = memR ?I (nt - t)" using memL_mono[OF inz] by auto
  have a2: "uw_a2 ?I t (es @ [(nt, rel2, b)])
      = uw_a2 ?I t es \<union> (if memR ?I (nt - t) \<and> (\<forall>e \<in> set es. snd (snd e)) then rel2 else {})"
    using uw_a2_snoc[of es nt ?I t rel2 b] ts by simp
  have IH': "update_until args rel1 rel2 nt (uw_abs args es) = uw_abs args (es @ [(nt, rel2, b)])"
    by (rule IH) (use ts tbl in auto)
  show ?case unfolding e upd a1 IH' mem jc
    by (cases b'; cases "memR ?I (nt - t)"; cases "\<forall>e \<in> set es. snd (snd e)")
      (simp_all add: a2 Un_ac)
qed

subsubsection \<open>Extending the window\<close>

text \<open>The entries the extension adds: from the rest, while in range from the window's start and
  while the left operand keeps holding.\<close>

fun uw_ext :: "\<I> \<Rightarrow> ts \<Rightarrow> bool \<Rightarrow> uw_entry list \<Rightarrow> uw_entry list" where
  "uw_ext I ts0 False rl = []"
| "uw_ext I ts0 True [] = []"
| "uw_ext I ts0 True (e # rl) =
     (if memR I (fst e - ts0) then e # uw_ext I ts0 (snd (snd e)) rl else [])"

lemma uw_ext_prefix: "\<exists>sfx. rl = uw_ext I ts0 bend rl @ sfx"
  by (induct I ts0 bend rl rule: uw_ext.induct) (auto simp: fun_eq_iff)

lemma uw_ext_range: "e \<in> set (uw_ext I ts0 bend rl) \<Longrightarrow> memR I (fst e - ts0)"
  by (induct I ts0 bend rl rule: uw_ext.induct) (auto split: if_splits)

lemma uw_ext_bend: "uw_ext I ts0 False rl = []"
  by simp

lemma uw_extend_rep:
  "linearize rest = rl \<Longrightarrow> uw_extend args ts0 win rest bend cc = (win', rest', bend', cc') \<Longrightarrow>
     linearize win' = linearize win @ uw_ext (args_ivl args) ts0 bend rl \<and>
     linearize rest' = drop (length (uw_ext (args_ivl args) ts0 bend rl)) rl \<and>
     bend' = (if uw_ext (args_ivl args) ts0 bend rl = [] then bend
              else snd (snd (last (uw_ext (args_ivl args) ts0 bend rl)))) \<and>
     cc' = fold cnt_add (map (fst \<circ> snd) (uw_ext (args_ivl args) ts0 bend rl)) cc \<and>
     (bend' \<longrightarrow> linearize rest' = [] \<or> \<not> memR (args_ivl args) (fst (hd (linearize rest')) - ts0))"
proof (induct rl arbitrary: win rest bend cc win' rest' bend' cc')
  case Nil
  obtain ho rest0 where sh: "safe_hd rest = (ho, rest0)" by (cases "safe_hd rest")
  have ho: "ho = None" and l0: "linearize rest0 = []"
    using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  show ?case
  proof (cases bend)
    case False
    then have "(win, rest, bend, cc) = (win', rest', bend', cc')"
      using Nil(2) by (subst (asm) uw_extend.simps) simp
    then show ?thesis using False Nil(1) by simp
  next
    case True
    then have "(win, rest0, bend, cc) = (win', rest', bend', cc')"
      using Nil(2) by (subst (asm) uw_extend.simps) (simp add: sh ho)
    then show ?thesis using True l0 by simp
  qed
next
  case (Cons e rl)
  show ?case
  proof (cases bend)
    case False
    then show ?thesis using Cons(2,3) by (subst (asm) uw_extend.simps) simp
  next
    case True
    obtain ho rest0 where sh: "safe_hd rest = (ho, rest0)" by (cases "safe_hd rest")
    have l0: "linearize rest0 = e # rl" using safe_hd_rep[OF sh] Cons(2) by simp
    have ho: "ho = Some e" using safe_hd_rep[OF sh] l0 by (cases ho) auto
    have lt: "linearize (tl_queue rest0) = rl" by (simp add: tl_queue_rep l0)
    show ?thesis
    proof (cases "memR (args_ivl args) (fst e - ts0)")
      case r: True
      have "uw_extend args ts0 (append_queue e win) (tl_queue rest0) (snd (snd e))
          (cnt_add (fst (snd e)) cc) = (win', rest', bend', cc')"
        using Cons(3) by (subst (asm) uw_extend.simps) (simp add: True sh ho r)
      from Cons(1)[OF lt this] show ?thesis using True r
        by (auto simp: append_queue_rep)
    next
      case r: False
      have "(win, rest0, bend, cc) = (win', rest', bend', cc')"
        using Cons(3) by (subst (asm) uw_extend.simps) (simp add: True sh ho r)
      then show ?thesis using True r l0 by simp
    qed
  qed
qed

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

lemma uw_win_Nil: "uw_win I ts0 [] True"
  by (simp add: uw_win_def)

lemma uw_a2_ext_True:
  "uw_a2 I ts0 rl = \<Union> (set (map (fst \<circ> snd) (uw_ext I ts0 True rl)))"
proof (induct rl)
  case (Cons e rl)
  obtain t R b where e: "e = (t, R, b)" by (cases e)
  show ?case unfolding e using Cons by (cases b; cases "memR I (t - ts0)") auto
qed simp

text \<open>After the extension the window is the whole run the answer is the union of.\<close>

lemma uw_win_a2:
  assumes w: "uw_win I ts0 wl bend"
  shows "uw_a2 I ts0 (wl @ rl) = \<Union> (set (map (fst \<circ> snd) (wl @ uw_ext I ts0 bend rl)))"
  using w
proof (induct wl)
  case Nil
  then have "bend" by (simp add: uw_win_def)
  then show ?case by (simp add: uw_a2_ext_True)
next
  case (Cons e wl)
  obtain t R b where e: "e = (t, R, b)" by (cases e)
  have r: "memR I (t - ts0)" using Cons.prems unfolding e uw_win_def by simp
  show ?case
  proof (cases wl)
    case Nil
    then have "bend = b" using Cons.prems unfolding e uw_win_def by simp
    then show ?thesis unfolding e Nil using r
      by (cases b) (simp_all add: uw_a2_ext_True)
  next
    case (Cons e' wl')
    have b: "b" using Cons.prems unfolding e Cons uw_win_def by simp
    have w': "uw_win I ts0 wl bend" using Cons.prems unfolding e Cons uw_win_def by simp
    show ?thesis unfolding e using r b Cons.hyps[OF w'] by simp
  qed
qed

lemma uw_win_extend:
  assumes w: "uw_win I ts0 wl bend"
  shows "uw_win I ts0 (wl @ uw_ext I ts0 bend rl)
    (if uw_ext I ts0 bend rl = [] then bend else snd (snd (last (uw_ext I ts0 bend rl))))"
proof (cases "uw_ext I ts0 bend rl = []")
  case True
  then show ?thesis using w by simp
next
  case False
  define ex where "ex = uw_ext I ts0 bend rl"
  have bend: "bend" using False by (cases bend) simp_all
  have ex: "\<forall>e \<in> set (butlast ex). snd (snd e)"
    unfolding ex_def using bend
  proof (induct I ts0 bend rl rule: uw_ext.induct)
    case (3 I ts0 e rl)
    show ?case
    proof (cases "memR I (fst e - ts0)")
      case True
      show ?thesis
      proof (cases "uw_ext I ts0 (snd (snd e)) rl = []")
        case True
        then show ?thesis using \<open>memR I (fst e - ts0)\<close> by simp
      next
        case False
        then have b: "snd (snd e)" by (cases "snd (snd e)") simp_all
        then show ?thesis using True 3(1)[OF True b] False by simp
      qed
    qed simp
  qed simp_all
  have wl_last: "\<forall>e \<in> set wl. snd (snd e)"
    using w bend unfolding uw_win_def by (cases wl rule: rev_cases) auto
  show ?thesis using w ex wl_last False uw_ext_range[of _ I ts0 bend rl]
    unfolding uw_win_def ex_def[symmetric] by (auto simp: butlast_append)
qed

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
      (\<forall>e \<in> set es. fst e \<le> cur \<and> table (args_R args) (fst (snd e))) \<and>
      cnt_inv (map (fst \<circ> snd) (linearize win)) cc \<and>
      uw_win (args_ivl args) (case es of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) (linearize win) bend \<and>
      (\<exists>ex. auxlist = ex @ uw_abs args es \<and> map proj_thd ex = rev dn \<and>
         (\<forall>e \<in> set ex. \<not> memR (args_ivl args) (cur - fst e)))))"

lemma valid_uw_init: "valid_uw args 0 (uw_init args) []"
  by (simp add: valid_uw_def uw_init_def empty_queue_rep cnt_inv_empty uw_win_Nil)

lemma valid_uw_length:
  "valid_uw args cur aux auxlist \<Longrightarrow> uw_length args aux = length auxlist"
  by (auto simp: valid_uw_def uw_length_def split: prod.splits)
    (metis length_map length_rev)

text \<open>One step: the oldest pending time point's answer is its abstract entry's.\<close>

lemma valid_uw_step:
  assumes v: "valid_uw args cur aux auxlist"
    and aux: "aux = (nts, win, rest, len, bend, cc, dn)"
    and ne: "len \<noteq> 0" and hd: "safe_hd nts = (Some ts0, nts')"
    and old: "\<not> memR (args_ivl args) (cur' - ts0)" and cc': "cur \<le> cur'"
  shows "valid_uw args cur' (uw_step args ts0 (nts', win, rest, len, bend, cc, dn)) auxlist \<and>
    set (uw_es (uw_step args ts0 (nts', win, rest, len, bend, cc, dn))) \<subseteq> set (uw_es aux)"
proof -
  let ?I = "args_ivl args"
  define es where "es = linearize win @ linearize rest"
  have nl: "linearize nts = map fst es" and lenes: "len = length es"
    and srt: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') es"
    and wf: "\<forall>e \<in> set es. fst e \<le> cur \<and> table (args_R args) (fst (snd e))"
    and cnt: "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
    and wi: "uw_win ?I (case es of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) (linearize win) bend"
    using v unfolding valid_uw_def aux es_def by auto
  obtain ex where al: "auxlist = ex @ uw_abs args es" and exd: "map proj_thd ex = rev dn"
    and exo: "\<forall>e \<in> set ex. \<not> memR ?I (cur - fst e)"
    using v unfolding valid_uw_def aux es_def by auto
  have es_ne: "es \<noteq> []" using ne lenes by simp
  then obtain e0 es' where es: "es = e0 # es'" by (cases es) auto
  have nts': "linearize nts' = map fst es" and ts0: "ts0 = fst e0"
    using safe_hd_rep[OF hd] nl es by auto
  have wi': "uw_win ?I ts0 (linearize win) bend" using wi unfolding es ts0 by simp
  obtain win1 rest1 bend1 cc1 where ext: "uw_extend args ts0 win rest bend cc = (win1, rest1, bend1, cc1)"
    by (cases "uw_extend args ts0 win rest bend cc")
  define ex1 where "ex1 = uw_ext ?I ts0 bend (linearize rest)"
  have er: "linearize win1 = linearize win @ ex1 \<and>
     linearize rest1 = drop (length ex1) (linearize rest) \<and>
     bend1 = (if ex1 = [] then bend else snd (snd (last ex1))) \<and>
     cc1 = fold cnt_add (map (fst \<circ> snd) ex1) cc \<and>
     (bend1 \<longrightarrow> linearize rest1 = [] \<or> \<not> memR ?I (fst (hd (linearize rest1)) - ts0))"
    using uw_extend_rep[OF refl ext] unfolding ex1_def .
  have w1: "linearize win1 = linearize win @ ex1"
    and r1: "linearize rest1 = drop (length ex1) (linearize rest)"
    and b1: "bend1 = (if ex1 = [] then bend else snd (snd (last ex1)))"
    and c1: "cc1 = fold cnt_add (map (fst \<circ> snd) ex1) cc"
    using er by blast+
  obtain sfx where sfx: "linearize rest = ex1 @ sfx"
    using uw_ext_prefix[of "linearize rest" ?I ts0 bend] unfolding ex1_def by blast
  have ex1_pre: "linearize rest = ex1 @ drop (length ex1) (linearize rest)"
    using sfx by simp
  have es1: "linearize win1 @ linearize rest1 = es"
    unfolding w1 r1 es_def using ex1_pre by simp
  have sub1: "set ex1 \<subseteq> set (linearize rest)" using sfx by simp
  have cnt1: "cnt_inv (map (fst \<circ> snd) (linearize win1)) cc1"
    unfolding w1 c1 map_append by (rule cnt_inv_adds[OF cnt])
  have wi1: "uw_win ?I ts0 (linearize win1) bend1"
    unfolding w1 b1 ex1_def by (rule uw_win_extend[OF wi'])
  \<comment> \<open>the window is not empty\<close>
  have w1_ne: "linearize win1 \<noteq> []"
  proof (cases "linearize win")
    case Nil
    then have bend: "bend" using wi' by (simp add: uw_win_def)
    have "linearize rest = es" using Nil es_def by simp
    then have "uw_ext ?I ts0 bend (linearize rest) \<noteq> []"
      unfolding es ts0 using bend by simp
    then show ?thesis unfolding w1 ex1_def by simp
  qed (simp add: w1)
  then obtain e1 wl1 where wl1: "linearize win1 = e1 # wl1" by (cases "linearize win1") auto
  have e1: "e1 = e0" using es1 wl1 es by simp
  obtain ho win2 where sh2: "safe_hd win1 = (ho, win2)" by (cases "safe_hd win1")
  have lw2: "linearize win2 = e1 # wl1" using safe_hd_rep[OF sh2] wl1 by simp
  have ho: "ho = Some e1" using safe_hd_rep[OF sh2] lw2 by (cases ho) auto
  have lw3: "linearize (tl_queue win2) = wl1" by (simp add: tl_queue_rep lw2)
  \<comment> \<open>the answer\<close>
  have ans: "snd cc1 = uw_a2 ?I ts0 es"
    using cnt_inv_set[OF cnt1] uw_win_a2[OF wi', of "linearize rest"]
    unfolding w1 ex1_def es_def by simp
  have abs0: "uw_abs args es = (ts0, uw_a1 args (map (snd \<circ> snd) es), uw_a2 ?I ts0 es) # uw_abs args es'"
    unfolding es ts0 by (cases e0) simp
  \<comment> \<open>the result\<close>
  define res where "res = (tl_queue nts', tl_queue win2, rest1, len - 1,
     if Queue.is_empty (tl_queue win2) then True else bend1, cnt_del (fst (snd e1)) cc1, snd cc1 # dn)"
  have step: "uw_step args ts0 (nts', win, rest, len, bend, cc, dn) = res"
    unfolding uw_step_def res_def by (simp add: ext sh2 ho)
  have es'_eq: "wl1 @ linearize rest1 = es'" using es1 wl1 es by simp
  have nts'': "linearize (tl_queue nts') = map fst es'"
    by (simp add: tl_queue_rep nts' es)
  have cnt2: "cnt_inv (map (fst \<circ> snd) wl1) (cnt_del (fst (snd e1)) cc1)"
    using cnt_inv_tl[OF cnt1[unfolded wl1, simplified]] by simp
  have wi2: "uw_win ?I (case es' of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) wl1
      (if Queue.is_empty (tl_queue win2) then True else bend1)"
  proof (cases wl1)
    case Nil
    then show ?thesis by (simp add: is_empty_alt lw3 uw_win_Nil)
  next
    case (Cons e2 wl2)
    have ne2: "\<not> Queue.is_empty (tl_queue win2)" by (simp add: is_empty_alt lw3 Cons)
    have es'2: "es' = e2 # (wl2 @ linearize rest1)" using es'_eq Cons by simp
    have r: "\<forall>e \<in> set wl1. memR ?I (fst e - ts0)" and bl: "\<forall>e \<in> set (butlast wl1). snd (snd e)"
      and bd: "bend1 = (wl1 = [] \<or> snd (snd (last wl1)))"
      using wi1 unfolding uw_win_def wl1 by (simp_all add: Cons)
    have le: "ts0 \<le> fst e2" using srt unfolding es es'2 ts0 by simp
    have r': "\<forall>e \<in> set wl1. memR ?I (fst e - fst e2)"
      using r le memR_mono_ts by blast
    show ?thesis unfolding es'2 using ne2 r' bl bd by (simp add: uw_win_def)
  qed
  have sub: "set (uw_es res) \<subseteq> set (uw_es aux)"
    unfolding res_def aux uw_es.simps lw3 es'_eq es_def[symmetric] es by auto
  have "valid_uw args cur' res auxlist" unfolding res_def valid_uw_def
  proof (simp only: prod.case Let_def lw3, intro conjI)
    show "linearize (tl_queue nts') = map fst (wl1 @ linearize rest1)"
      unfolding es'_eq nts'' ..
    show "len - 1 = length (wl1 @ linearize rest1)" unfolding es'_eq lenes es by simp
    show "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') (wl1 @ linearize rest1)"
      unfolding es'_eq using srt es by simp
    show "\<forall>e \<in> set (wl1 @ linearize rest1). fst e \<le> cur' \<and>
        table (args_R args) (fst (snd e))"
      unfolding es'_eq using wf cc' es by auto
    show "cnt_inv (map (fst \<circ> snd) wl1) (cnt_del (fst (snd e1)) cc1)" by (rule cnt2)
    show "uw_win ?I (case wl1 @ linearize rest1 of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) wl1
        (if Queue.is_empty (tl_queue win2) then True else bend1)"
      unfolding es'_eq by (rule wi2)
    show "\<exists>ex. auxlist = ex @ uw_abs args (wl1 @ linearize rest1) \<and>
        map proj_thd ex = rev (snd cc1 # dn) \<and> (\<forall>e \<in> set ex. \<not> memR ?I (cur' - fst e))"
    proof (intro exI[of _ "ex @ [(ts0, uw_a1 args (map (snd \<circ> snd) es), uw_a2 ?I ts0 es)]"] conjI)
      show "auxlist = (ex @ [(ts0, uw_a1 args (map (snd \<circ> snd) es), uw_a2 ?I ts0 es)])
          @ uw_abs args (wl1 @ linearize rest1)"
        unfolding es'_eq al abs0 by simp
      show "map proj_thd (ex @ [(ts0, uw_a1 args (map (snd \<circ> snd) es), uw_a2 ?I ts0 es)])
          = rev (snd cc1 # dn)" unfolding ans[symmetric] using exd by simp
      show "\<forall>e \<in> set (ex @ [(ts0, uw_a1 args (map (snd \<circ> snd) es), uw_a2 ?I ts0 es)]).
          \<not> memR ?I (cur' - fst e)"
        using exo old not_memR_mono[OF cc'] by auto
    qed
  qed
  then show ?thesis using sub unfolding step by simp
qed

lemma valid_uw_mono:
  assumes v: "valid_uw args cur aux auxlist" and cn: "cur \<le> nt"
  shows "valid_uw args nt aux auxlist"
proof -
  obtain nts win rest len bend cc dn where aux: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux)
  define es where "es = linearize win @ linearize rest"
  have c1: "linearize nts = map fst es" and c2: "len = length es"
    and c3: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') es"
    and c4: "\<forall>e \<in> set es. fst e \<le> cur \<and> table (args_R args) (fst (snd e))"
    and c5: "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
    and c6: "uw_win (args_ivl args) (case es of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) (linearize win) bend"
    using v unfolding valid_uw_def aux es_def by auto
  obtain ex where c7: "auxlist = ex @ uw_abs args es" and c8: "map proj_thd ex = rev dn"
    and c9: "\<forall>e \<in> set ex. \<not> memR (args_ivl args) (cur - fst e)"
    using v unfolding valid_uw_def aux es_def by auto
  have c4': "\<forall>e \<in> set es. fst e \<le> nt \<and> table (args_R args) (fst (snd e))" using c4 cn by auto
  have c9': "\<forall>e \<in> set ex. \<not> memR (args_ivl args) (nt - fst e)"
    using c9 not_memR_mono[OF cn] by blast
  show ?thesis unfolding valid_uw_def aux
  proof (simp only: prod.case Let_def, intro conjI)
    show "linearize nts = map fst (linearize win @ linearize rest)" using c1 by (simp add: es_def)
    show "len = length (linearize win @ linearize rest)" using c2 by (simp add: es_def)
    show "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') (linearize win @ linearize rest)"
      using c3 by (simp add: es_def)
    show "\<forall>e \<in> set (linearize win @ linearize rest). fst e \<le> nt \<and>
        table (args_R args) (fst (snd e))"
      using c4' by (simp add: es_def)
    show "cnt_inv (map (fst \<circ> snd) (linearize win)) cc" by (rule c5)
    show "uw_win (args_ivl args) (case linearize win @ linearize rest of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e)
        (linearize win) bend" using c6 by (simp add: es_def)
    show "\<exists>ex. auxlist = ex @ uw_abs args (linearize win @ linearize rest) \<and>
        map proj_thd ex = rev dn \<and> (\<forall>e \<in> set ex. \<not> memR (args_ivl args) (nt - fst e))"
      using c7 c8 c9' unfolding es_def by blast
  qed
qed

fun uw_len :: "uwaux \<Rightarrow> nat" where
  "uw_len (nts, win, rest, len, bend, cc, dn) = len"

lemma uw_len_step: "uw_len (uw_step args ts0 (nts, win, rest, len, bend, cc, dn)) = len - 1"
  by (simp add: uw_step_def split: prod.splits option.splits)

text \<open>The shift pops the pending time points that no later one can affect, in order.\<close>

lemma valid_uw_shift:
  assumes v: "valid_uw args cur aux auxlist" and cn: "cur \<le> nt"
  shows "valid_uw args nt (uw_shift args nt aux) auxlist \<and>
    (\<forall>e \<in> set (uw_es (uw_shift args nt aux)). memR (args_ivl args) (nt - fst e)) \<and>
    set (uw_es (uw_shift args nt aux)) \<subseteq> set (uw_es aux)"
  using v cn
proof (induct "uw_len aux" arbitrary: aux cur rule: less_induct)
  case less
  note IH = less.hyps and v = less.prems(1) and cn = less.prems(2)
  let ?I = "args_ivl args"
  obtain nts win rest len bend cc dn where aux: "aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases aux)
  define es where "es = linearize win @ linearize rest"
  have nl: "linearize nts = map fst es" and lenes: "len = length es"
    and srt: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') es"
    using v unfolding valid_uw_def aux es_def by auto
  obtain ho nts' where sh: "safe_hd nts = (ho, nts')" by (cases "safe_hd nts")
  have nts': "linearize nts' = linearize nts" using safe_hd_rep[OF sh] by simp
  have v': "valid_uw args nt aux auxlist" by (rule valid_uw_mono[OF v cn])
  have v'': "valid_uw args nt (nts', win, rest, len, bend, cc, dn) auxlist"
    using v' unfolding valid_uw_def aux by (simp add: nts')
  show ?case
  proof (cases ho)
    case None
    then have "es = []" using safe_hd_rep[OF sh] nl by (auto split: option.splits)
    moreover have "uw_shift args nt aux = (nts', win, rest, len, bend, cc, dn)"
      using None by (subst uw_shift.simps) (simp add: aux sh)
    ultimately show ?thesis using v'' unfolding aux es_def by simp
  next
    case (Some ts0)
    have ts0: "ts0 = hd (linearize nts)" using safe_hd_rep[OF sh] Some by auto
    have es_ne: "es \<noteq> []" using safe_hd_rep[OF sh] Some nl by auto
    have ts0': "ts0 = fst (hd es)" using ts0 nl es_ne by (simp add: hd_map)
    show ?thesis
    proof (cases "memR ?I (nt - ts0) \<or> len = 0")
      case True
      have len_ne: "len \<noteq> 0" using lenes es_ne by simp
      have r: "memR ?I (nt - ts0)" using True len_ne by simp
      have "uw_shift args nt aux = (nts', win, rest, len, bend, cc, dn)"
        using Some True by (subst uw_shift.simps) (simp add: aux sh)
      moreover have "\<forall>e \<in> set es. memR ?I (nt - fst e)"
      proof
        fix e assume "e \<in> set es"
        then have "ts0 \<le> fst e" using srt es_ne ts0' by (cases es) auto
        then show "memR ?I (nt - fst e)" using r memR_mono_ts by blast
      qed
      ultimately show ?thesis using v'' unfolding aux es_def by simp
    next
      case False
      have len_ne: "len \<noteq> 0" and old: "\<not> memR ?I (nt - ts0)" using False by auto
      have sh': "safe_hd nts = (Some ts0, nts')" using sh Some by simp
      let ?st = "uw_step args ts0 (nts', win, rest, len, bend, cc, dn)"
      have st: "valid_uw args nt ?st auxlist" and sub: "set (uw_es ?st) \<subseteq> set (uw_es aux)"
        using valid_uw_step[OF v aux len_ne sh' old cn] by simp_all
      have lt: "uw_len ?st < uw_len aux" unfolding aux uw_len_step using len_ne by simp
      have eq: "uw_shift args nt aux = uw_shift args nt ?st"
        using Some False by (subst uw_shift.simps) (simp add: aux sh)
      show ?thesis unfolding eq using IH[OF lt st order_refl] sub by auto
    qed
  qed
qed

lemma valid_uw_add_new:
  assumes v: "valid_uw args cur aux auxlist"
    and t1: "table [] rel1" and X: "(X = {}) = (rel1 = {})"
    and t2: "table (args_R args) rel2"
    and inz: "memL (args_ivl args) 0" and L: "args_L args = []" and cn: "cur \<le> nt"
  shows "valid_uw args nt (uw_add_new args X rel2 nt aux) (update_until args rel1 rel2 nt auxlist)"
proof -
  let ?I = "args_ivl args"
  obtain nts win rest len bend cc dn where sft: "uw_shift args nt aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uw_shift args nt aux")
  have vs: "valid_uw args nt (nts, win, rest, len, bend, cc, dn) auxlist"
    using valid_uw_shift[OF v cn] sft by simp
  define es where "es = linearize win @ linearize rest"
  have nl: "linearize nts = map fst es" and lenes: "len = length es"
    and srt: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') es"
    and wf: "\<forall>e \<in> set es. fst e \<le> nt \<and> table (args_R args) (fst (snd e))"
    and cnt: "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
    and wi: "uw_win ?I (case es of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) (linearize win) bend"
    using vs unfolding valid_uw_def es_def by auto
  obtain ex where al: "auxlist = ex @ uw_abs args es" and exd: "map proj_thd ex = rev dn"
    and exo: "\<forall>e \<in> set ex. \<not> memR ?I (nt - fst e)"
    using vs unfolding valid_uw_def es_def by auto
  define b where "b = (if args_pos args then \<not> Set.is_empty X else Set.is_empty X)"
  have b: "b = ((rel1 \<noteq> {}) = args_pos args)" unfolding b_def Set.is_empty_iff using X by auto
  have res: "uw_add_new args X rel2 nt aux
      = (append_queue nt nts, win, append_queue (nt, rel2, b) rest, len + 1, bend, cc, dn)"
    unfolding uw_add_new_def sft b_def by simp
  have upd: "update_until args rel1 rel2 nt auxlist
      = map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if args_pos args then a1 \<inter> rel1 else a1 \<union> rel1,
            if mem ?I (nt - t) then a2 \<union> join (args_R args) rel2 (args_pos args) (args_L args) a1 else a2)) ex
        @ update_until args rel1 rel2 nt (uw_abs args es)"
    unfolding al update_until_def by simp
  have abs': "update_until args rel1 rel2 nt (uw_abs args es) = uw_abs args (es @ [(nt, rel2, b)])"
    by (rule uw_abs_snoc[OF _ _ t1 t2 inz L b]) (use wf in auto)
  have es': "linearize win @ linearize (append_queue (nt, rel2, b) rest) = es @ [(nt, rel2, b)]"
    by (simp add: append_queue_rep es_def)
  show ?thesis unfolding res valid_uw_def
  proof (simp only: prod.case Let_def es', intro conjI)
    show "linearize (append_queue nt nts) = map fst (es @ [(nt, rel2, b)])"
      by (simp add: append_queue_rep nl)
    show "len + 1 = length (es @ [(nt, rel2, b)])" by (simp add: lenes)
    show "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') (es @ [(nt, rel2, b)])"
      unfolding sorted_wrt_append using srt wf by auto
    show "\<forall>e \<in> set (es @ [(nt, rel2, b)]). fst e \<le> nt \<and>
        table (args_R args) (fst (snd e))"
      using wf t2 by auto
    show "cnt_inv (map (fst \<circ> snd) (linearize win)) cc" by (rule cnt)
    show "uw_win ?I (case es @ [(nt, rel2, b)] of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) (linearize win) bend"
    proof (cases es)
      case Nil
      then have "linearize win = []" using es_def by simp
      then show ?thesis using wi Nil by (simp add: uw_win_def)
    next
      case Cons
      then show ?thesis using wi by simp
    qed
    show "\<exists>ex'. update_until args rel1 rel2 nt auxlist = ex' @ uw_abs args (es @ [(nt, rel2, b)]) \<and>
        map proj_thd ex' = rev dn \<and> (\<forall>e \<in> set ex'. \<not> memR ?I (nt - fst e))"
    proof (intro exI conjI)
      let ?ex = "map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if args_pos args then a1 \<inter> rel1 else a1 \<union> rel1,
            if mem ?I (nt - t) then a2 \<union> join (args_R args) rel2 (args_pos args) (args_L args) a1 else a2)) ex"
      show "update_until args rel1 rel2 nt auxlist = ?ex @ uw_abs args (es @ [(nt, rel2, b)])"
        unfolding upd abs' ..
      show "map proj_thd ?ex = rev dn"
        unfolding exd[symmetric] map_map
        by (intro map_cong[OF refl]) (use exo in \<open>auto split: prod.splits\<close>)
      show "\<forall>e \<in> set ?ex. \<not> memR ?I (nt - fst e)" using exo by (auto split: prod.splits)
    qed
  qed
qed

lemma valid_uw_eval:
  assumes v: "valid_uw args cur aux auxlist" and cn: "cur \<le> nt"
    and ev: "uw_eval args nt aux = (res, aux')"
    and eu: "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_uw args cur aux' auxlist' \<and> res = res'"
proof -
  let ?I = "args_ivl args"
  obtain nts win rest len bend cc dn where sft: "uw_shift args nt aux = (nts, win, rest, len, bend, cc, dn)"
    by (cases "uw_shift args nt aux")
  have vs: "valid_uw args nt (nts, win, rest, len, bend, cc, dn) auxlist"
    and inr: "\<forall>e \<in> set (linearize win @ linearize rest). memR ?I (nt - fst e)"
    and sub: "set (linearize win @ linearize rest) \<subseteq> set (uw_es aux)"
    using valid_uw_shift[OF v cn] sft by simp_all
  define es where "es = linearize win @ linearize rest"
  have nl: "linearize nts = map fst es" and lenes: "len = length es"
    and srt: "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') es"
    and wf: "\<forall>e \<in> set es. fst e \<le> nt \<and> table (args_R args) (fst (snd e))"
    and cnt: "cnt_inv (map (fst \<circ> snd) (linearize win)) cc"
    and wi: "uw_win ?I (case es of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e) (linearize win) bend"
    using vs unfolding valid_uw_def es_def by auto
  obtain ex where al: "auxlist = ex @ uw_abs args es" and exd: "map proj_thd ex = rev dn"
    and exo: "\<forall>e \<in> set ex. \<not> memR ?I (nt - fst e)"
    using vs unfolding valid_uw_def es_def by auto
  have wf0: "\<forall>e \<in> set (uw_es aux). fst e \<le> cur"
    using v unfolding valid_uw_def by (cases aux) auto
  have wf': "\<forall>e \<in> set es. fst e \<le> cur \<and> table (args_R args) (fst (snd e))"
    using wf wf0 sub unfolding es_def by auto
  have r: "res = rev dn" and a': "aux' = (nts, win, rest, len, bend, cc, [])"
    using ev unfolding uw_eval_def sft by simp_all
  have tw1: "takeWhile (check_before ?I nt) ex = ex"
    using exo by (simp add: check_before_fst)
  have tw2: "takeWhile (check_before ?I nt) (uw_abs args es) = []"
    using inr[folded es_def] by (cases es) (auto simp: check_before_fst split: prod.splits)
  have tw: "takeWhile (check_before ?I nt) auxlist = ex"
    unfolding al takeWhile_append tw1 tw2 by simp
  have res': "res' = rev dn" unfolding eval_until_res[OF eu] tw exd ..
  have lr: "length res' = length ex" unfolding res' exd[symmetric] by simp
  have al': "auxlist' = uw_abs args es"
    unfolding eval_until_auxlist'[OF eu] al lr by simp
  have "valid_uw args cur aux' auxlist'"
    unfolding a' al'[unfolded es_def] valid_uw_def
  proof (simp only: prod.case Let_def, intro conjI)
    show "linearize nts = map fst (linearize win @ linearize rest)" using nl by (simp add: es_def)
    show "len = length (linearize win @ linearize rest)" using lenes by (simp add: es_def)
    show "sorted_wrt (\<lambda>e e'. fst e \<le> fst e') (linearize win @ linearize rest)"
      using srt by (simp add: es_def)
    show "\<forall>e \<in> set (linearize win @ linearize rest). fst e \<le> cur \<and>
        table (args_R args) (fst (snd e))"
      using wf' by (simp add: es_def)
    show "cnt_inv (map (fst \<circ> snd) (linearize win)) cc" by (rule cnt)
    show "uw_win ?I (case linearize win @ linearize rest of [] \<Rightarrow> 0 | e # _ \<Rightarrow> fst e)
        (linearize win) bend" using wi by (simp add: es_def)
    show "\<exists>ex. uw_abs args (linearize win @ linearize rest)
        = ex @ uw_abs args (linearize win @ linearize rest) \<and>
        map proj_thd ex = rev [] \<and> (\<forall>e \<in> set ex. \<not> memR ?I (cur - fst e))"
      by (intro exI[of _ "[]"]) simp
  qed
  then show ?thesis using r res' by simp
qed

(*<*)
end
(*>*)
