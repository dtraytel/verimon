(*<*)
theory IWindow
  imports Window_Dispatch ITable
begin
(*>*)

section \<open>The Since window with an indexed union\<close>

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
  show ?case
    using 1 by (subst sw_move.simps, subst (asm) isw_move.simps)
      (auto simp: icnt_abs_add split: prod.splits option.splits if_splits)
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

subsection \<open>The dispatched Since structures\<close>

text \<open>The structures other than the window of a closed left operand are kept as they are; their
  result is a table without indices.\<close>

datatype iudsaux_x = IUDSX_u udsaux_x | IUDSX_win iswaux

fun riu :: "iudsaux_x \<Rightarrow> udsaux_x" where
  "riu (IUDSX_u d) = d"
| "riu (IUDSX_win w) = UDSX_win (isw_abs w)"

fun iudsx_emb :: "udsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_emb (UDSX_win w) = IUDSX_win (isw_emb w)"
| "iudsx_emb d = IUDSX_u d"

lemma riu_iudsx_emb[simp]: "riu (iudsx_emb d) = d"
  by (cases d) simp_all

fun iudsx_add_new_ts :: "args \<Rightarrow> ts \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_add_new_ts args nt (IUDSX_u d) = IUDSX_u (udsx_add_new_ts args nt d)"
| "iudsx_add_new_ts args nt (IUDSX_win w) = IUDSX_win (isw_add_new_ts args nt w)"

fun iudsx_join :: "args \<Rightarrow> utable \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_join args X (IUDSX_u d) = IUDSX_u (udsx_join args X d)"
| "iudsx_join args X (IUDSX_win w) = IUDSX_win (isw_join args X w)"

fun iudsx_add_new_table :: "args \<Rightarrow> utable \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_add_new_table args X (IUDSX_u d) = IUDSX_u (udsx_add_new_table args X d)"
| "iudsx_add_new_table args X (IUDSX_win w) = IUDSX_win (isw_add_new_table args X w)"

fun iudsx_result :: "args \<Rightarrow> iudsaux_x \<Rightarrow> event_data itab" where
  "iudsx_result args (IUDSX_u d) = itab (udsx_result args d)"
| "iudsx_result args (IUDSX_win w) = isw_result w"

fun iudsx_ensure :: "bool list list \<Rightarrow> iudsaux_x \<Rightarrow> iudsaux_x" where
  "iudsx_ensure msks (IUDSX_win w) = IUDSX_win (isw_ensure msks w)"
| "iudsx_ensure msks d = d"

lemma riu_add_new_ts[simp]: "riu (iudsx_add_new_ts args nt d) = udsx_add_new_ts args nt (riu d)"
  by (cases d) (simp_all add: isw_abs_add_new_ts)

lemma riu_join[simp]: "riu (iudsx_join args X d) = udsx_join args X (riu d)"
  by (cases d) (simp_all add: isw_abs_join)

lemma riu_add_new_table[simp]: "riu (iudsx_add_new_table args X d) = udsx_add_new_table args X (riu d)"
  by (cases d) (simp_all add: isw_abs_add_new_table)

lemma iset_iudsx_result[simp]: "iset (iudsx_result args d) = udsx_result args (riu d)"
  by (cases d) (simp_all add: iset_isw_result)

lemma riu_ensure[simp]: "riu (iudsx_ensure msks d) = riu d"
  by (cases d) simp_all

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
