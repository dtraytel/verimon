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

(*<*)
end
(*>*)
