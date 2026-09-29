(*<*)
theory Dense_Win_Agg
  imports Dense_Win "MFODL_Monitor_Devel.Optimized_Agg_Temporal"
begin
(*>*)

section \<open>The closed-left Since window with the aggregation fused in\<close>

text \<open>
  The kernel folds an aggregation over a Since into the Since node (@{const args_agg}), and its
  structure keeps the aggregate incrementally (@{typ aggaux}): a count, a sum or a rank tree per
  group, updated as tuples enter and leave the union.  The count set of the sliding window makes
  those entries and exits explicit: a table added contributes the tuples not yet in the union, a
  table removed takes out the tuples it was the last to hold.  This theory pairs the count set
  with the kernel's structure and feeds it exactly those tuples.  The structure is optional, as in
  the kernel: once an operation reports that it cannot maintain the aggregate it is dropped, and
  the result is computed from the union directly.
\<close>

subsection \<open>The count set with the aggregate\<close>

type_synonym acntset = "cntset \<times> aggaux option"

definition cnt_leave :: "event_data table \<Rightarrow> cntset \<Rightarrow> event_data table" where
  "cnt_leave T cc = Set.filter (\<lambda>x. Mapping.lookup (fst cc) x = Some 1) T"

definition acnt_add :: "aggargs \<Rightarrow> event_data table \<Rightarrow> acntset \<Rightarrow> acntset" where
  "acnt_add ag T ca = (case ca of (cc, ax) \<Rightarrow>
     (cnt_add T cc, insert_maggaux' ag (T - snd cc) ax))"

definition acnt_del :: "aggargs \<Rightarrow> event_data table \<Rightarrow> acntset \<Rightarrow> acntset" where
  "acnt_del ag T ca = (case ca of (cc, ax) \<Rightarrow>
     (cnt_del T cc, delete_maggaux' ag (cnt_leave T cc) ax))"

text \<open>The aggregate is valid for the support of a count set that represents some count
  function.\<close>

definition acnt_ok :: "aggargs \<Rightarrow> acntset \<Rightarrow> bool" where
  "acnt_ok ag ca \<longleftrightarrow> (case ca of (cc, ax) \<Rightarrow> (\<exists>f. cnt_rep f cc) \<and> valid_maggaux' ag ax (snd cc))"

lemma valid_maggaux'_insert:
  assumes "valid_maggaux' ag ax X" and "X \<inter> Y = {}"
  shows "valid_maggaux' ag (insert_maggaux' ag Y ax) (X \<union> Y)"
proof (cases ax)
  case (Some a)
  show ?thesis
  proof (cases "finite Y")
    case True
    then show ?thesis
      using valid_insert_maggaux[of ag a X Y] assms Some
      by (auto split: prod.splits simp del: insert_maggaux.simps)
  qed (use Some in \<open>auto split: prod.splits simp del: insert_maggaux.simps\<close>)
qed simp

lemma valid_maggaux'_delete:
  assumes "valid_maggaux' ag ax X" and "Y \<subseteq> X"
  shows "valid_maggaux' ag (delete_maggaux' ag Y ax) (X - Y)"
proof (cases ax)
  case (Some a)
  then show ?thesis
    using valid_delete_maggaux[of ag a X Y] assms
    by (auto split: prod.splits simp del: delete_maggaux.simps)
qed simp

lemma valid_maggaux'_init: "valid_maggaux' ag (init_maggaux' ag) {}"
  using valid_init_maggaux[of ag] by (auto split: prod.splits simp del: init_maggaux.simps)

lemma cnt_rep_snd_add: "cnt_rep f cc \<Longrightarrow> snd (cnt_add T cc) = snd cc \<union> T"
  using cnt_rep_add[of f cc T] unfolding cnt_rep_def by auto

lemma cnt_leave_rep: "cnt_rep f cc \<Longrightarrow> cnt_leave T cc = {x \<in> T. f x = 1}"
  unfolding cnt_leave_def cnt_rep_def by (auto split: if_splits)

lemma cnt_rep_snd_del: "cnt_rep f cc \<Longrightarrow> snd (cnt_del T cc) = snd cc - cnt_leave T cc"
  using cnt_rep_del[of f cc T] cnt_leave_rep[of f cc T] unfolding cnt_rep_def by auto

lemma cnt_leave_sub: "cnt_rep f cc \<Longrightarrow> cnt_leave T cc \<subseteq> snd cc"
  using cnt_leave_rep[of f cc T] unfolding cnt_rep_def by auto

lemma acnt_ok_add: "acnt_ok ag ca \<Longrightarrow> acnt_ok ag (acnt_add ag T ca)"
proof -
  assume ok: "acnt_ok ag ca"
  obtain cc ax where ca: "ca = (cc, ax)" by (cases ca)
  obtain f where cr: "cnt_rep f cc" and v: "valid_maggaux' ag ax (snd cc)"
    using ok by (auto simp: acnt_ok_def ca)
  have "valid_maggaux' ag (insert_maggaux' ag (T - snd cc) ax) (snd cc \<union> (T - snd cc))"
    by (rule valid_maggaux'_insert[OF v]) auto
  moreover have "snd cc \<union> (T - snd cc) = snd (cnt_add T cc)" using cnt_rep_snd_add[OF cr] by auto
  ultimately show ?thesis using cnt_rep_add[OF cr]
    by (auto simp: acnt_ok_def acnt_add_def ca)
qed

lemma acnt_ok_del: "acnt_ok ag ca \<Longrightarrow> acnt_ok ag (acnt_del ag T ca)"
proof -
  assume ok: "acnt_ok ag ca"
  obtain cc ax where ca: "ca = (cc, ax)" by (cases ca)
  obtain f where cr: "cnt_rep f cc" and v: "valid_maggaux' ag ax (snd cc)"
    using ok by (auto simp: acnt_ok_def ca)
  have "valid_maggaux' ag (delete_maggaux' ag (cnt_leave T cc) ax) (snd cc - cnt_leave T cc)"
    by (rule valid_maggaux'_delete[OF v cnt_leave_sub[OF cr]])
  then show ?thesis using cnt_rep_del[OF cr] cnt_rep_snd_del[OF cr]
    by (auto simp: acnt_ok_def acnt_del_def ca)
qed

lemma fst_acnt_add[simp]: "fst (acnt_add ag T ca) = cnt_add T (fst ca)"
  by (simp add: acnt_add_def split: prod.splits)

lemma fst_acnt_del[simp]: "fst (acnt_del ag T ca) = cnt_del T (fst ca)"
  by (simp add: acnt_del_def split: prod.splits)

subsection \<open>The two scans, with the aggregate\<close>

text \<open>The scans of @{const sw_move} and @{const sw_expire}, with @{const acnt_add} and
  @{const acnt_del} for @{const cnt_add} and @{const cnt_del}.\<close>

function swa_move :: "aggargs \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (ts \<times> event_data table) queue \<Rightarrow> acntset \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> acntset" where
  "swa_move ag args nt pend win ca =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, ca)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then swa_move ag args nt (tl_queue pend') (append_queue e win) (acnt_add ag (snd e) ca)
               else swa_move ag args nt (tl_queue pend') win ca)
         else (pend', win, ca)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(ag, args, nt, pend, win, ca). length (linearize pend))")
     (fastforce split: prod.splits)+

declare swa_move.simps[simp del]

function swa_expire :: "aggargs \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> acntset \<Rightarrow>
    (ts \<times> event_data table) queue \<times> acntset" where
  "swa_expire ag args nt win ca =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', ca)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', ca)
         else swa_expire ag args nt (tl_queue win') (acnt_del ag (snd e) ca)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(ag, args, nt, win, ca). length (linearize win))")
     (fastforce split: prod.splits)+

declare swa_expire.simps[simp del]

lemma swa_move_eq:
  "swa_move ag args nt pend win ca = (pend', win', ca') \<Longrightarrow>
   sw_move args nt pend win (fst ca) = (pend', win', fst ca') \<and> (acnt_ok ag ca \<longrightarrow> acnt_ok ag ca')"
proof (induct ag args nt pend win ca arbitrary: pend' win' ca' rule: swa_move.induct)
  case (1 ag args nt pend win ca)
  obtain ho p0 where sh: "safe_hd pend = (ho, p0)" by (cases "safe_hd pend")
  show ?case
  proof (cases ho)
    case None
    with 1(3) sh show ?thesis
      by (subst sw_move.simps) (subst (asm) swa_move.simps, simp)
  next
    case (Some e)
    show ?thesis
    proof (cases "memL (args_ivl args) (nt - fst e)")
      case L: True
      show ?thesis
      proof (cases "memR (args_ivl args) (nt - fst e)")
        case True
        have "swa_move ag args nt (tl_queue p0) (append_queue e win) (acnt_add ag (snd e) ca)
            = (pend', win', ca')"
          using 1(3) sh Some L True by (subst (asm) swa_move.simps) simp
        from 1(1)[OF sh[symmetric] Some L True this] show ?thesis
          using sh Some L True by (subst sw_move.simps) (simp add: acnt_ok_add)
      next
        case False
        have "swa_move ag args nt (tl_queue p0) win ca = (pend', win', ca')"
          using 1(3) sh Some L False by (subst (asm) swa_move.simps) simp
        from 1(2)[OF sh[symmetric] Some L False this] show ?thesis
          using sh Some L False by (subst sw_move.simps) simp
      qed
    next
      case False
      with 1(3) sh Some show ?thesis
        by (subst sw_move.simps) (subst (asm) swa_move.simps, simp)
    qed
  qed
qed

lemma swa_expire_eq:
  "swa_expire ag args nt win ca = (win', ca') \<Longrightarrow>
   sw_expire args nt win (fst ca) = (win', fst ca') \<and> (acnt_ok ag ca \<longrightarrow> acnt_ok ag ca')"
proof (induct ag args nt win ca arbitrary: win' ca' rule: swa_expire.induct)
  case (1 ag args nt win ca)
  obtain ho w0 where sh: "safe_hd win = (ho, w0)" by (cases "safe_hd win")
  show ?case
  proof (cases ho)
    case None
    with 1(2) sh show ?thesis
      by (subst sw_expire.simps) (subst (asm) swa_expire.simps, simp)
  next
    case (Some e)
    show ?thesis
    proof (cases "memR (args_ivl args) (nt - fst e)")
      case True
      with 1(2) sh Some show ?thesis
        by (subst sw_expire.simps) (subst (asm) swa_expire.simps, simp)
    next
      case False
      have "swa_expire ag args nt (tl_queue w0) (acnt_del ag (snd e) ca) = (win', ca')"
        using 1(2) sh Some False by (subst (asm) swa_expire.simps) simp
      from 1(1)[OF sh[symmetric] Some False this] show ?thesis
        using sh Some False by (subst sw_expire.simps) (simp add: acnt_ok_del)
    qed
  qed
qed

subsection \<open>The window\<close>

type_synonym swaaux = "ts \<times> (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> acntset"

fun swa_sw :: "swaaux \<Rightarrow> swaux" where
  "swa_sw (t, pend, win, ca) = (t, pend, win, fst ca)"

fun swa_ca :: "swaaux \<Rightarrow> acntset" where
  "swa_ca (t, pend, win, ca) = ca"

definition valid_swa :: "aggargs \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> swaaux \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_swa ag args cur aux auxlist \<longleftrightarrow>
     valid_sw args cur (swa_sw aux) auxlist \<and> acnt_ok ag (swa_ca aux)"

definition swa_init :: "aggargs \<Rightarrow> args \<Rightarrow> swaaux" where
  "swa_init ag args = (0, empty_queue, empty_queue, ((Mapping.empty, {}), init_maggaux' ag))"

definition swa_add_new_ts :: "aggargs \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> swaaux \<Rightarrow> swaaux" where
  "swa_add_new_ts ag args nt aux = (case aux of (t, pend, win, ca) \<Rightarrow>
     (case swa_move ag args nt pend win ca of (pend', win', ca') \<Rightarrow>
      (case swa_expire ag args nt win' ca' of (win'', ca'') \<Rightarrow> (nt, pend', win'', ca''))))"

definition swa_join :: "aggargs \<Rightarrow> args \<Rightarrow> event_data table \<Rightarrow> swaaux \<Rightarrow> swaaux" where
  "swa_join ag args X aux = (case aux of (t, pend, win, ca) \<Rightarrow>
     (if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then aux
      else (t, empty_queue, empty_queue, ((Mapping.empty, {}), init_maggaux' ag))))"

definition swa_add_new_table :: "aggargs \<Rightarrow> args \<Rightarrow> event_data table \<Rightarrow> swaaux \<Rightarrow> swaaux" where
  "swa_add_new_table ag args X aux = (case aux of (t, pend, win, ca) \<Rightarrow>
     (if memL (args_ivl args) 0
      then (t, pend, append_queue (t, X) win, acnt_add ag X ca)
      else (t, append_queue (t, X) pend, win, ca)))"

definition swa_result :: "aggargs \<Rightarrow> args \<Rightarrow> swaaux \<Rightarrow> event_data table" where
  "swa_result ag args aux = (case aux of (t, pend, win, (cc, ax)) \<Rightarrow>
     (case result_maggaux' ag ax of Some r \<Rightarrow> r | None \<Rightarrow> eval_aggargs ag (snd cc)))"

lemma acnt_ok_empty: "acnt_ok ag ((Mapping.empty, {}), init_maggaux' ag)"
  using cnt_rep_empty valid_maggaux'_init by (auto simp: acnt_ok_def)

lemma valid_swa_init: "valid_swa ag args 0 (swa_init ag args) []"
  using valid_sw_init[of args] acnt_ok_empty[of ag]
  by (simp add: valid_swa_def swa_init_def sw_init_def)

lemma valid_swa_add_new_ts:
  assumes "valid_swa ag args cur aux auxlist" and "cur \<le> nt"
  shows "valid_swa ag args nt (swa_add_new_ts ag args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  obtain t pend win ca where aux: "aux = (t, pend, win, ca)" by (cases aux)
  obtain pend' win' ca' where m: "swa_move ag args nt pend win ca = (pend', win', ca')"
    by (cases "swa_move ag args nt pend win ca")
  obtain win'' ca'' where e: "swa_expire ag args nt win' ca' = (win'', ca'')"
    by (cases "swa_expire ag args nt win' ca'")
  have "swa_sw (swa_add_new_ts ag args nt aux) = sw_add_new_ts args nt (swa_sw aux)"
    using swa_move_eq[OF m] swa_expire_eq[OF e]
    by (simp add: swa_add_new_ts_def sw_add_new_ts_def aux m e)
  moreover have "acnt_ok ag (swa_ca (swa_add_new_ts ag args nt aux))"
    using swa_move_eq[OF m] swa_expire_eq[OF e] assms(1)
    by (simp add: swa_add_new_ts_def valid_swa_def aux m e)
  ultimately show ?thesis
    using valid_sw_add_new_ts[OF _ assms(2)] assms(1) by (simp add: valid_swa_def)
qed

lemma valid_swa_join:
  assumes "valid_swa ag args cur aux auxlist"
    and "table [] rel1" and "(X = {}) = (rel1 = {})"
  shows "valid_swa ag args cur (swa_join ag args X aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) [] rel1)) auxlist)"
proof -
  obtain t pend win ca where aux: "aux = (t, pend, win, ca)" by (cases aux)
  have "swa_sw (swa_join ag args X aux) = sw_join args X (swa_sw aux)"
    by (simp add: swa_join_def sw_join_def aux)
  moreover have "acnt_ok ag (swa_ca (swa_join ag args X aux))"
    using assms(1) acnt_ok_empty[of ag] by (simp add: swa_join_def valid_swa_def aux)
  ultimately show ?thesis
    using valid_sw_join[OF _ assms(2,3)] assms(1) by (simp add: valid_swa_def)
qed

lemma valid_swa_add_new_table:
  assumes "valid_swa ag args cur aux auxlist" and "table (args_R args) rel2"
  shows "valid_swa ag args cur (swa_add_new_table ag args rel2 aux)
    (case auxlist of
      [] => [(cur, rel2)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
proof -
  obtain t pend win ca where aux: "aux = (t, pend, win, ca)" by (cases aux)
  have "swa_sw (swa_add_new_table ag args rel2 aux) = sw_add_new_table args rel2 (swa_sw aux)"
    by (simp add: swa_add_new_table_def sw_add_new_table_def aux)
  moreover have "acnt_ok ag (swa_ca (swa_add_new_table ag args rel2 aux))"
    using assms(1) by (simp add: swa_add_new_table_def valid_swa_def aux acnt_ok_add)
  ultimately show ?thesis
    using valid_sw_add_new_table[OF _ assms(2)] assms(1) by (simp add: valid_swa_def)
qed

lemma valid_swa_result:
  assumes "valid_swa ag args cur aux auxlist"
  shows "swa_result ag args aux =
    eval_aggargs ag (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  obtain t pend win cc ax where aux: "aux = (t, pend, win, (cc, ax))" by (cases aux) auto
  have sw: "sw_result args (swa_sw aux) = snd cc" by (simp add: sw_result_def aux)
  have r: "sw_result args (swa_sw aux) =
      foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
    using assms by (intro valid_sw_result) (simp add: valid_swa_def)
  have v: "valid_maggaux' ag ax (snd cc)" using assms by (simp add: valid_swa_def acnt_ok_def aux)
  show ?thesis
  proof (cases ax)
    case (Some a)
    then show ?thesis using v valid_result_maggaux[of ag a "snd cc"] sw r
      by (simp add: swa_result_def aux)
  qed (use sw r in \<open>simp add: swa_result_def aux\<close>)
qed

(*<*)
end
(*>*)
