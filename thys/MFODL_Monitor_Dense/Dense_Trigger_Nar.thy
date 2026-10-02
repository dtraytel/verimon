(*<*)
theory Dense_Trigger_Nar
  imports Dense_Unbox
begin
(*>*)

section \<open>The kernel's trigger structure at the ascending frame\<close>

text \<open>A table is used throughout with the two properties every theorem about the dense
  representation needs of it: it is well formed over its columns, and it is finite.\<close>

abbreviation (input) ftable :: "nat list \<Rightarrow> 'a table \<Rightarrow> bool" where
  "ftable A X \<equiv> table A X \<and> finite X"

text \<open>
  The trigger node of the dense evaluator keeps its window over the right operand's ascending
  columns and the left operand's tuples over the left operand's ascending columns.  The kernel's
  structure does the same over arbitrary column lists, so at the arguments @{const dargs} the
  two hold the same objects.  They differ only in the mask the dense structure stores, which
  replaces the kernel's projection of a right tuple to the left operand's columns by
  @{const dproj}.  @{term tmm} drops the mask, and the update and the read commute with it.
\<close>

subsection \<open>The kernel's state of a dense state\<close>

fun tmm :: "'a gmmtaux \<Rightarrow> 'a mmtaux" where
  "tmm (cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tuple_in_once,
      tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) =
    (cur, idx_next, idx_mid, idx_oldest, data_prev, data_in, tuple_in_once,
     tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"

fun tmsk :: "'a gmmtaux \<Rightarrow> bool list" where
  "tmsk (cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tuple_in_once,
      tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) = msk"

subsection \<open>The semi-join\<close>

text \<open>Through the mask the semi-join is the kernel's on every right table over the right
  operand's columns.\<close>

lemma gsemi_join_eq:
  assumes dm: "dmsk_args args msk" and r: "table (args_R args) r"
  shows "gsemi_join msk pos r l = proj_tuple_in_join_optim pos r (args_R args) l (args_L args)"
proof -
  have len: "\<And>as. as \<in> r \<Longrightarrow> length as = length (args_R args)"
    using r by (auto simp: table_def wf_tuple_def)
  show ?thesis
  proof (cases "args_L args = args_R args")
    case True
    then have a: "\<forall>i \<in> set msk. i" using dmsk_args_full[OF dm] by simp
    show ?thesis
      unfolding gsemi_join_def proj_tuple_in_join_optim.simps if_P[OF a] if_P[OF True] ..
  next
    case False
    then have nt: "\<not> (\<forall>i \<in> set msk. i)" using dmsk_args_full[OF dm] by simp
    show ?thesis
    proof (cases "args_L args = []")
      case True
      then have a: "\<forall>i \<in> set msk. \<not> i" using dmsk_args_empty[OF dm] by simp
      show ?thesis
        unfolding gsemi_join_def proj_tuple_in_join_optim.simps if_not_P[OF nt] if_P[OF a]
          if_not_P[OF False] if_P[OF True] ..
    next
      case L: False
      then have nf: "\<not> (\<forall>i \<in> set msk. \<not> i)" using dmsk_args_empty[OF dm] by simp
      show ?thesis
        unfolding gsemi_join_def proj_tuple_in_join_optim.simps if_not_P[OF nt] if_not_P[OF nf]
          if_not_P[OF False] if_not_P[OF L]
        by (auto simp: dsemi_def proj_tuple_in_join_def dmsk_args_dproj[OF dm len])
    qed
  qed
qed

subsection \<open>The update\<close>

text \<open>The two updates differ in one argument of one fold: the semi-join applied to the tables
  that leave the front of the window.  @{term tupd} is either update with that semi-join as a
  parameter, and its fold @{term tfold} is named so that the two can be compared on the tables
  the fold actually visits.\<close>

definition tfold :: "('b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set) \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) list \<Rightarrow> ('b list, nat) mapping \<times> 'b list set \<times> nat \<times> 'b list set \<Rightarrow>
    ('b list, nat) mapping \<times> 'b list set \<times> nat \<times> 'b list set" where
  "tfold semi move init = fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
        let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
            hist_sat = hist_sat \<inter> r;
            since_sat = since_sat \<inter> r
        in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
            hist_sat, idx_move + 1,
            since_sat \<union> semi r l))
      move init"

definition tupd :: "('b list set \<Rightarrow> 'b list set \<Rightarrow> 'b list set) \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (ts \<times> 'b list set \<times> 'b list set) queue \<Rightarrow> (ts \<times> 'b list set) queue \<Rightarrow>
    (('b list, ts) mapping) \<Rightarrow> 'b list set \<Rightarrow> (('b list, nat) mapping) \<Rightarrow> 'b list set \<Rightarrow>
    'b list set \<Rightarrow>
    (nat \<times> nat \<times> (ts \<times> 'b list set \<times> 'b list set) queue \<times> (ts \<times> 'b list set) queue \<times>
     (('b list, ts) mapping) \<times> 'b list set \<times> (('b list, nat) mapping) \<times> 'b list set \<times>
     'b list set)" where
  "tupd semi args nt idx_mid idx_oldest data_prev data_in tuple_in_once
     tuple_in_once_keys tuple_since_hist hist_sat since_sat = (
    let (_, data_prev', move, tuple_in_once', tuple_in_once_keys') = shift_end'
      (flip_int_less_lower (args_ivl args)) nt fst
      (empty_queue :: (ts \<times> 'b list set \<times> 'b list set) queue,
       data_prev, tuple_in_once, tuple_in_once_keys);
    move_len = length move;
    idx_mid' = idx_mid + move_len;
    (data_in', drop) = takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in;
    move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move;
    drop_prev_len = move_len - length move';
    idx_oldest' = idx_oldest + length drop + drop_prev_len;
    data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in';
    (tuple_since_hist', hist_sat', idx_move, since_sat') =
      tfold semi move (tuple_since_hist, hist_sat, idx_mid, since_sat);
    tuple_since_hist'' = (if idx_mid' = idx_oldest' then Mapping.empty else tuple_since_hist');
    since_sat'' = (if idx_mid' = idx_oldest' then {} else since_sat');
    hist_sat'' = (case fst (safe_hd data_in'') of None \<Rightarrow> {}
      | Some db \<Rightarrow> hist_sat' \<union> {tuple \<in> snd db.
          case Mapping.lookup tuple_since_hist'' tuple of
            Some idx \<Rightarrow> idx \<le> idx_oldest' | None \<Rightarrow> False})
    in
    (idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys',
     tuple_since_hist'', hist_sat'', since_sat''))"

lemma gupdate_mmtaux'_tupd:
  "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
    = tupd (gsemi_join msk (args_pos args)) args nt idx_mid idx_oldest data_prev data_in tio keys
        tsh hs ss"
  unfolding gupdate_mmtaux'_def tupd_def tfold_def ..

lemma update_nmtaux'_tupd:
  "update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tio keys tsh hs ss
    = tupd (\<lambda>r l. proj_tuple_in_join_optim (args_pos args) r (args_R args) l (args_L args))
        args nt idx_mid idx_oldest data_prev data_in tio keys tsh hs ss"
  unfolding update_nmtaux'_def tupd_def tfold_def ..

lemma tfold_cong:
  "(\<And>t l r. (t, l, r) \<in> set move \<Longrightarrow> semi1 r l = semi2 r l) \<Longrightarrow>
    tfold semi1 move init = tfold semi2 move init"
  unfolding tfold_def by (rule fold_cong) auto

lemma shift_end'_move:
  assumes "shift_end' I nt f (q0, dp, ti, tk) = (a, b, mv, c, d)"
  shows "set mv \<subseteq> set (linearize dp)"
proof -
  obtain x y where td: "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) dp = (x, y)"
    by (cases "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) dp")
  have "mv = y" using assms
    by (auto simp: Let_def td simp del: takedropWhile_queue.simps dropWhile_queue.simps
        split: prod.splits)
  moreover have "y = takeWhile (\<lambda>(t, _). \<not> memR I (nt - t)) (linearize dp)"
    using takedropWhile_queue_snd[of "\<lambda>(t, _). \<not> memR I (nt - t)" dp] td by simp
  ultimately show ?thesis by (auto dest: set_takeWhileD)
qed

lemma tupd_cong:
  fixes data_prev :: "(ts \<times> 'a list set \<times> 'a list set) queue"
  assumes s: "\<And>t l r. (t, l, r) \<in> set (linearize data_prev) \<Longrightarrow> semi1 r l = semi2 r l"
  shows "tupd semi1 args nt idx_mid idx_oldest data_prev data_in tio keys tsh hs ss
    = tupd semi2 args nt idx_mid idx_oldest data_prev data_in tio keys tsh hs ss"
proof -
  obtain a b mv c d where se: "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
      (empty_queue :: (ts \<times> 'a list set \<times> 'a list set) queue, data_prev, tio, keys) = (a, b, mv, c, d)"
    by (metis prod_cases5)
  have tf: "tfold semi1 mv init = tfold semi2 mv init" for init
    using shift_end'_move[OF se] s by (intro tfold_cong) auto
  show ?thesis unfolding tupd_def Let_def se prod.case tf ..
qed

lemma gupdate_mmtaux'_eq:
  assumes dm: "dmsk_args args msk"
    and wf: "\<forall>(t, l, r) \<in> set (linearize data_prev). table (args_R args) r"
  shows "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
    = update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tio keys tsh hs ss"
  unfolding gupdate_mmtaux'_tupd update_nmtaux'_tupd
  by (rule tupd_cong) (use wf gsemi_join_eq[OF dm] in fastforce)

lemma dmsk_args_distinct_R: "dmsk_args args msk \<Longrightarrow> distinct (args_R args)"
  by (simp add: dmsk_args_def strict_sorted_iff)

lemma gsemi_join_eq':
  assumes dm: "dmsk_args args msk" and r: "table (args_R args) r"
  shows "gsemi_join msk pos r l = {as \<in> r. proj_tuple_in_join pos (args_L args) (args_R args) as l}"
  unfolding gsemi_join_eq[OF dm r] by (rule proj_tuple_in_join_optim_equiv[OF r dmsk_args_distinct_R[OF dm]])

lemma gupdate_mmtaux_tmm:
  assumes dm: "dmsk_args args msk" and m: "tmsk ax = msk"
    and wf: "\<forall>(t, l, r) \<in> set (linearize (mmtaux_data_prev (tmm ax))). table (args_R args) r"
    and r: "table (args_R args) r"
  shows "tmm (gupdate_mmtaux args nt l r ax) = update_nmtaux args nt l r (tmm ax)"
    and "tmsk (gupdate_mmtaux args nt l r ax) = msk"
proof -
  obtain cur idx_next idx_mid idx_oldest msk' data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (cases ax rule: tmm.cases)
  have m': "msk' = msk" using m unfolding ax by simp
  have dp: "\<forall>(t, l, r) \<in> set (linearize data_prev). table (args_R args) r"
    using wf unfolding ax by simp
  have u: "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
      = update_nmtaux' args nt idx_mid idx_oldest data_prev data_in tio keys tsh hs ss"
    by (rule gupdate_mmtaux'_eq[OF dm dp])
  note g = gsemi_join_eq'[OF dm r, of "args_pos args" l]
  show "tmm (gupdate_mmtaux args nt l r ax) = update_nmtaux args nt l r (tmm ax)"
    unfolding ax m' by (simp add: gupdate_mmtaux_def update_nmtaux_def u g Let_def
        split: prod.splits)
  show "tmsk (gupdate_mmtaux args nt l r ax) = msk"
    unfolding ax m' by (simp add: gupdate_mmtaux_def Let_def split: prod.splits)
qed

subsection \<open>Initialisation and the read\<close>

lemma tmm_ginit: "tmm (ginit_mmtaux args msk) = init_mmtaux args"
  by (simp add: ginit_mmtaux_def init_mmtaux_def)

lemma tmsk_ginit: "tmsk (ginit_mmtaux args msk) = msk"
  by (simp add: ginit_mmtaux_def)

lemma gresult_mmtaux_tmm:
  assumes ne: "\<not> gmmtaux_empty ax"
  shows "gresult_mmtaux args ax = snd (result_nmtaux args (tmm ax))"
  using ne by (cases ax rule: tmm.cases) (simp add: gmmtaux_empty_def gresult_mmtaux_def)

text \<open>With the interval containing zero the window is never empty after a step: the update
  appends the right operand's table to it.\<close>

lemma gupdate_mmtaux_not_empty:
  assumes m0: "mem (args_ivl args) 0"
  shows "\<not> gmmtaux_empty (gupdate_mmtaux args nt l r ax)"
proof -
  obtain cur idx_next idx_mid idx_oldest msk' data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (cases ax rule: tmm.cases)
  show ?thesis using m0 unfolding ax
    by (simp add: gmmtaux_empty_def gupdate_mmtaux_def Let_def Queue.is_empty_alt
        append_queue_rep split: prod.splits)
qed

subsection \<open>The auxiliary list a dense trigger structure stands for\<close>

text \<open>
  The evaluator's trigger node is related to the kernel's abstract auxiliary list through the
  kernel's own validity of the state without the mask.  Both the standalone trigger and the fused
  And-Trigger use this relation; the side condition @{term tok} is the kernel's on the operand
  frames, which the standalone node meets by its interval and the fused one by its two operand
  frames agreeing.
\<close>

definition tok :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> bool" where
  "tok cR cL args \<longleftrightarrow> mem (args_ivl args) 0 \<or> (cL = cR \<and> args_pos args)"

lemma tok_mem0: "mem (args_ivl args) 0 \<Longrightarrow> tok cR cL args"
  by (simp add: tok_def)

lemma trigger_args_dargs: "tok cR cL args \<Longrightarrow> trigger_args (dargs cR cL args) = dargs cR cL args"
  by (auto simp: tok_def trigger_args_def dargs_def init_args_def)

lemma trigger_lhs_dargs: "tok cR cL args \<Longrightarrow> trigger_lhs (dargs cR cL args) l = l"
  by (auto simp: tok_def trigger_lhs_def)

lemma map_trigger_lhs_dargs:
  "tok cR cL args \<Longrightarrow> map (\<lambda>(t, l, r). (t, trigger_lhs (dargs cR cL args) l, r)) xs = xs"
  by (induct xs) (auto simp: trigger_lhs_dargs)

definition dtaux :: "cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data gmmtaux \<Rightarrow>
    event_data mtaux \<Rightarrow> bool" where
  "dtaux kL cL kR cR args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r) \<and> tok cR cL args \<and>
     tmsk daux = dmsk cR cL \<and>
     valid_mmtaux (dargs cR cL args) cur (tmm daux) (dauxlist3 kL cL kR cR auxlist)"

lemma dtaux_valid_nmtaux:
  assumes v: "dtaux kL cL kR cR args cur daux auxlist"
  shows "valid_nmtaux (dargs cR cL args) cur (tmm daux) (dauxlist3 kL cL kR cR auxlist)"
proof -
  have ok: "tok cR cL args" using v by (simp add: dtaux_def)
  show ?thesis
    using v unfolding dtaux_def valid_mmtaux_def trigger_args_dargs[OF ok]
      map_trigger_lhs_dargs[OF ok] by blast
qed

lemma valid_nmtaux_data_prev:
  assumes "valid_nmtaux args cur aux auxlist"
  shows "\<forall>(t, l, r) \<in> set (linearize (mmtaux_data_prev aux)). table (args_R args) r"
proof -
  obtain mt idx_next idx_mid idx_oldest data_prev data_in tio keys tsh hs ss
    where ax: "aux = (mt, idx_next, idx_mid, idx_oldest, data_prev, data_in, tio, keys, tsh, hs, ss)"
    by (metis prod.collapse)
  have "\<forall>as \<in> \<Union>(relR ` (set (linearize data_prev))). wf_tuple (args_R args) as"
    using assms unfolding ax valid_nmtaux_def prod.case by (elim conjE) assumption
  then show ?thesis unfolding ax by (fastforce simp: relR_def table_def)
qed

lemma dtaux_init:
  assumes fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and ok: "tok cR cL args"
  shows "dtaux kL cL kR cR args 0 (ginit_mmtaux (dargs cR cL args) (dmsk cR cL)) []"
proof -
  have sub': "set cL \<subseteq> set cR" by (rule dframe_sub[OF fR fL sub])
  have "valid_mmtaux (init_args (args_ivl args) (length cR) cL cR (args_pos args) None) 0
      (init_mmtaux (init_args (args_ivl args) (length cR) cL cR (args_pos args) None)) []"
    using valid_init_mmtaux[of "args_ivl args" cL cR "args_pos args" "length cR" None]
      sub' ok dframeD(4)[OF fL] dframeD(4)[OF fR] by (auto simp: tok_def Let_def)
  then show ?thesis using ok
    by (simp add: dtaux_def dargs_def dauxlist3_def tmm_ginit tmsk_ginit)
qed

lemma dtaux_update:
  assumes v: "dtaux kL cL kR cR args cur daux auxlist" and nt: "cur \<le> nt"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and tl: "table kL l" and tr: "table kR r"
  shows "dtaux kL cL kR cR args nt
      (gupdate_mmtaux (dargs cR cL args) nt (dtabc kL cL l) (dtabc kR cR r) daux)
      (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist @ [(nt, l, r)])"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r"
    and ok: "tok cR cL args" and m: "tmsk daux = dmsk cR cL"
    and d: "valid_mmtaux (dargs cR cL args) cur (tmm daux) (dauxlist3 kL cL kR cR auxlist)"
    using v by (auto simp: dtaux_def)
  have dm: "dmsk_args (dargs cR cL args) (dmsk cR cL)"
    unfolding dmsk_def
    by (rule dmsk_args_dargs[OF dframeD(2)[OF fR] dframeD(2)[OF fL] dframe_sub[OF fR fL sub]])
  have tl': "table (args_L (dargs cR cL args)) (dtabc kL cL l)" by (simp add: table_dtabc)
  have tr': "table (args_R (dargs cR cL args)) (dtabc kR cR r)" by (simp add: table_dtabc)
  have wf: "\<forall>(t, l, r) \<in> set (linearize (mmtaux_data_prev (tmm daux))).
      table (args_R (dargs cR cL args)) r"
    by (rule valid_nmtaux_data_prev[OF dtaux_valid_nmtaux[OF v]])
  have u: "update_mmtaux (dargs cR cL args) nt (dtabc kL cL l) (dtabc kR cR r) (tmm daux)
      = tmm (gupdate_mmtaux (dargs cR cL args) nt (dtabc kL cL l) (dtabc kR cR r) daux)"
    unfolding update_mmtaux_def trigger_args_dargs[OF ok] trigger_lhs_dargs[OF ok]
    by (rule gupdate_mmtaux_tmm(1)[OF dm m wf tr', symmetric])
  have m': "tmsk (gupdate_mmtaux (dargs cR cL args) nt (dtabc kL cL l) (dtabc kR cR r) daux)
      = dmsk cR cL"
    by (rule gupdate_mmtaux_tmm(2)[OF dm m wf tr'])
  have "valid_mmtaux (dargs cR cL args) nt
      (update_mmtaux (dargs cR cL args) nt (dtabc kL cL l) (dtabc kR cR r) (tmm daux))
      (filter (\<lambda>(t, _). memR (args_ivl (dargs cR cL args)) (nt - t))
         (dauxlist3 kL cL kR cR auxlist) @ [(nt, dtabc kL cL l, dtabc kR cR r)])"
    by (rule valid_update_mmtaux[OF nt tl' tr' d])
  then show ?thesis
    using w tl tr ok m'
      dauxlist3_filter_append[where P = "\<lambda>t. memR (args_ivl args) (nt - t)" and kL = kL
        and cL = cL and kR = kR and cR = cR and auxlist = auxlist and nt = nt and l = l and r = r]
    by (auto simp: dtaux_def u)
qed

lemma dtaux_window:
  assumes v: "dtaux kL cL kR cR args cur daux auxlist"
  shows "gmmtaux_empty daux \<longleftrightarrow> filter (\<lambda>(t, _). mem (args_ivl args) (cur - t)) auxlist = []"
proof -
  obtain cur' idx_next idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
    where ax: "daux = (cur', idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (cases daux rule: tmm.cases)
  have mp0: "cur = cur' \<and> map (\<lambda>(t, l, r). (t, r))
      (auxlist_data_in (dargs cR cL args) cur' (dauxlist3 kL cL kR cR auxlist))
    = linearize data_in"
    using dtaux_valid_nmtaux[OF v] unfolding ax tmm.simps valid_nmtaux_def prod.case
    by (elim conjE) (intro conjI; assumption)
  then have mp: "map (\<lambda>(t, l, r). (t, r))
      (auxlist_data_in (dargs cR cL args) cur (dauxlist3 kL cL kR cR auxlist))
    = linearize data_in" by simp
  have adi: "auxlist_data_in (dargs cR cL args) cur (dauxlist3 kL cL kR cR auxlist)
      = dauxlist3 kL cL kR cR (filter (\<lambda>(t, _). mem (args_ivl args) (cur - t)) auxlist)"
    by (simp add: auxlist_data_in_def dauxlist3_def filter_map split_def comp_def)
  show ?thesis using mp unfolding adi ax
    by (auto simp: gmmtaux_empty_def Queue.is_empty_alt dauxlist3_def)
qed

lemma dtaux_result:
  assumes v: "dtaux kL cL kR cR args cur daux auxlist" and ne: "\<not> gmmtaux_empty daux"
    and fR: "dframe kR cR" and fL: "dframe kL cL" and sub: "set kL \<subseteq> set kR"
    and aL: "args_L args = kL" and aR: "args_R args = kR"
  shows "gresult_mmtaux (dargs cR cL args) daux = dtabc kR cR (snd (trigger_results args cur auxlist))"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table kL l \<and> table kR r" and ok: "tok cR cL args"
    and d: "valid_mmtaux (dargs cR cL args) cur (tmm daux) (dauxlist3 kL cL kR cR auxlist)"
    using v by (auto simp: dtaux_def)
  have fl: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)"
    using dtaux_window[OF v] ne by (auto simp: split_def)
  have f1: "fst (trigger_results args cur auxlist) = kR" using fl aR by simp
  have f2: "fst (trigger_results (dargs cR cL args) cur (dauxlist3 kL cL kR cR auxlist)) = cR"
    using fl length_filter_dauxlist3[of "\<lambda>t. mem (args_ivl args) (cur - t)" kL cL kR cR auxlist]
    by simp
  have "gresult_mmtaux (dargs cR cL args) daux = snd (result_nmtaux (dargs cR cL args) (tmm daux))"
    by (rule gresult_mmtaux_tmm[OF ne])
  also have "result_nmtaux (dargs cR cL args) (tmm daux)
      = trigger_results (dargs cR cL args) cur (dauxlist3 kL cL kR cR auxlist)"
    using valid_result_mmtaux[OF d] by (simp add: result_mmtaux_def trigger_args_dargs[OF ok])
  also have "snd \<dots> = dtabc kR cR (snd (trigger_results args cur auxlist))"
    using dtabc_trigger_results(2)[OF fR fL sub aL aR w, of cur] unfolding f1 f2 .
  finally show ?thesis .
qed

lemma dtaux_result_empty:
  assumes v: "dtaux kL cL kR cR args cur daux auxlist" and e: "gmmtaux_empty daux"
  shows "trigger_results args cur auxlist = ([], unit_table)"
  using dtaux_window[OF v] e by (simp add: split_def)

subsection \<open>The read is a finite table\<close>

text \<open>The read of the trigger structure is a finite table over the right operand's columns.
  With an interval containing zero that is immediate, because the window then always holds the
  latest time point and the read is contained in its right table.  Without it a safe trigger has
  the same columns on both sides, and the read is contained in the union of the window's
  tables -- which is what the weakened form below states.\<close>

lemma ftable_trigger_results:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable L l \<and> ftable R r"
    and ne: "auxlist \<noteq> []" and m0: "mem (args_ivl args) 0"
    and lst: "fst (last auxlist) = cur" and aR: "args_R args = R"
  shows "ftable R (snd (trigger_results args cur auxlist))"
    and "fst (trigger_results args cur auxlist) = R"
proof -
  have kl: "length auxlist - 1 < length auxlist" using ne by simp
  obtain l0 r0 where a0: "auxlist ! (length auxlist - 1) = (cur, l0, r0)"
    using lst ne by (cases "auxlist ! (length auxlist - 1)") (simp add: last_conv_nth)
  have mem0: "auxlist ! (length auxlist - 1) \<in> set auxlist" using kl by (rule nth_mem)
  have tr0: "ftable R r0" using wf mem0 a0 by force
  have mm: "mem (args_ivl args) (cur - cur)" using m0 by simp
  have m: "(cur, l0, r0) \<in> set auxlist" using mem0 a0 by simp
  have fl: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist \<noteq> []"
  proof
    assume e: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []"
    have "\<forall>x \<in> set auxlist. \<not> (case x of (t, _, _) \<Rightarrow> mem (args_ivl args) (cur - t))"
      using e unfolding filter_empty_conv by simp
    from this[rule_format, OF m] show False using mm by simp
  qed
  have tb: "table R (snd (trigger_results args cur auxlist))"
    using fl aR by (auto simp: table_def)
  have sub: "snd (trigger_results args cur auxlist) \<subseteq> r0"
  proof
    fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
    have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
        mem (args_ivl args) (cur - t) \<longrightarrow>
        (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
           join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
             (restrict (args_L args) (args_R args) tu)))"
      using tu fl by simp
    have "{length auxlist - 1<..<length auxlist} = {}" using ne by auto
    then show "tu \<in> r0" using H[rule_format, of "length auxlist - 1"] kl a0 mm by simp
  qed
  have fin: "finite (snd (trigger_results args cur auxlist))"
    by (rule finite_subset[OF sub]) (use tr0 in simp)
  show "ftable R (snd (trigger_results args cur auxlist))" using tb fin by simp
  show "fst (trigger_results args cur auxlist) = R" using fl aR by simp
qed

lemma ftable_trigger_results_weak:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable L l \<and> ftable R r"
    and ne: "auxlist \<noteq> []" and lst: "fst (last auxlist) = cur"
    and aL: "args_L args = L" and aR: "args_R args = R" and dR: "distinct R"
    and wkc: "mem (args_ivl args) 0 \<or> (args_pos args \<and> set L = set R)"
  shows "ftable (fst (trigger_results args cur auxlist)) (snd (trigger_results args cur auxlist)) \<and>
    (fst (trigger_results args cur auxlist) = R \<or> fst (trigger_results args cur auxlist) = [])"
proof (cases "mem (args_ivl args) 0")
  case True
  show ?thesis using ftable_trigger_results[OF wf ne True lst aR] by simp
next
  case False
  then have pos: "args_pos args" and LR: "set L = set R" using wkc by auto
  show ?thesis
  proof (cases "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []")
    case True
    then show ?thesis by (simp add: table_def unit_table_def wf_tuple_def)
  next
    case False
    then obtain x where x: "x \<in> set auxlist"
      and px: "case x of (t, _, _) \<Rightarrow> mem (args_ivl args) (cur - t)"
      by (auto simp: filter_empty_conv)
    obtain t0 l0 r0 where x0: "x = (t0, l0, r0)" by (cases x)
    have mm: "mem (args_ivl args) (cur - t0)" using px x0 by simp
    obtain i0 where i0: "i0 < length auxlist" and xi: "auxlist ! i0 = (t0, l0, r0)"
      using x x0 by (auto simp: in_set_conv_nth)
    have fl: "0 < length (filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist)"
      using False by simp
    have tr0: "ftable R r0" using wf x x0 by force
    have tb: "table R (snd (trigger_results args cur auxlist))"
      using fl aR by (auto simp: table_def)
    have sub: "snd (trigger_results args cur auxlist)
        \<subseteq> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
    proof
      fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
      have wt: "wf_tuple R tu" using tu fl aR by simp
      have pj: "restrict R L (restrict (args_L args) (args_R args) tu) = tu"
        using restrict_restrict[of R L R tu] restrict_idle[OF dR wt] aL aR LR by simp
      have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
          mem (args_ivl args) (cur - t) \<longrightarrow>
          (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
             join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
               (restrict (args_L args) (args_R args) tu)))"
        using tu fl by simp
      have step: "tu \<in> r0 \<or> (\<exists>j \<in> {i0<..<length auxlist}.
          join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
            (restrict (args_L args) (args_R args) tu))"
        using H[rule_format, of i0] i0 xi mm by simp
      show "tu \<in> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
        using step pos by (auto intro: image_eqI[where f = "restrict R L", OF pj[symmetric]])
    qed
    have finl: "finite (\<Union>j \<in> {0..<length auxlist}. restrict R L ` (fst \<circ> snd) (auxlist ! j))"
    proof (rule finite_UN_I[OF finite_atLeastLessThan])
      fix j assume "j \<in> {0..<length auxlist}"
      then have m: "auxlist ! j \<in> set auxlist" by simp
      obtain vj lj rj where e: "auxlist ! j = (vj, lj, rj)" by (cases "auxlist ! j")
      show "finite (restrict R L ` (fst \<circ> snd) (auxlist ! j))" using wf m unfolding e by force
    qed
    have fin: "finite (snd (trigger_results args cur auxlist))"
      by (rule finite_subset[OF sub]) (use tr0 finl in simp)
    show ?thesis using tb fin fl aR by simp
  qed
qed

(*<*)
end
(*>*)