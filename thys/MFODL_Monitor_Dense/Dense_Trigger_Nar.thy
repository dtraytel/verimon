(*<*)
theory Dense_Trigger_Nar
  imports Dense_Unbox
begin
(*>*)

section \<open>The kernel's trigger structure at the narrow left frame\<close>

text \<open>A table is used throughout with the two properties every theorem about the dense
  representation needs of it: it is well formed over the node's columns, and it is finite.\<close>

abbreviation (input) ftable :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> bool" where
  "ftable n A X \<equiv> table n A X \<and> finite X"

text \<open>
  The trigger node of the dense evaluator keeps its window over the right operand's frame, and
  the left operand's tuples at the left operand's own frame -- narrow, without the columns the
  right operand has and the left one does not.  The kernel's own structure keeps the left tuples
  widened to the right operand's frame, with those columns blank.  This theory relates the two:
  @{term tmm} below widens a narrow state into a kernel state, and the update and the read
  commute with it on a state that is narrow.

  The material is here, rather than in the downstream Dense\_Unbox\_Eval theory where the rest of
  the naturality of the structures lives, because the evaluator's own trigger node carries the
  narrow structure and so needs these lemmas upstream of itself.  The queue functor the widening
  map is stated over is defined here for the same reason.
\<close>

subsection \<open>Mapping a queue\<close>

lift_definition map_queue :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a queue \<Rightarrow> 'b queue" is
  "\<lambda>f (fs, ls). (map f fs, map f ls)"
  by (auto simp: queue_invariant_def split: list.splits)

lemma linearize_map_queue[simp]: "linearize (map_queue f q) = map f (linearize q)"
  by transfer (auto simp: rev_map split: prod.splits)

lemma map_queue_empty[simp]: "map_queue f empty_queue = empty_queue"
  by transfer simp

lemma is_empty_map_queue[simp]: "Queue.is_empty (map_queue f q) = Queue.is_empty q"
  by transfer (auto split: prod.splits list.splits)

lemma append_queue_map_queue[simp]:
  "append_queue (f x) (map_queue f q) = map_queue f (append_queue x q)"
  by transfer (auto split: prod.splits)

lemma prepend_queue_map_queue[simp]:
  "prepend_queue (f x) (map_queue f q) = map_queue f (prepend_queue x q)"
  by transfer (auto simp: queue_invariant_def split: prod.splits list.splits)

lemma safe_hd_map_queue[simp]:
  "safe_hd (map_queue f q) = map_prod (map_option f) (map_queue f) (safe_hd q)"
proof (transfer, goal_cases)
  case (1 f q)
  then show ?case
    by (cases q rule: safe_hd_t.cases)
      (simp_all add: Let_def rev_map hd_map queue_invariant_def hd_append)
qed

lemma tl_queue_map_queue[simp]: "tl_queue (map_queue f q) = map_queue f (tl_queue q)"
proof (transfer, goal_cases)
  case (1 f q)
  then show ?case
    by (cases q rule: tl_queue_t.cases) (simp_all add: rev_map map_tl queue_invariant_def)
qed

lemma dropWhile_queue_map_queue:
  "dropWhile_queue P (map_queue f q) = map_queue f (dropWhile_queue (\<lambda>x. P (f x)) q)"
proof (induct "\<lambda>x. P (f x)" q rule: dropWhile_queue.induct)
  case (1 q)
  then show ?case
    by (subst dropWhile_queue.simps, subst (2) dropWhile_queue.simps)
      (auto split: prod.splits option.splits simp del: dropWhile_queue.simps)
qed

lemma takeWhile_queue_map_queue:
  "takeWhile_queue P (map_queue f q)
   = map_prod (map_queue f) (map_queue f) (takeWhile_queue (\<lambda>x. P (f x)) q)"
proof (induct "\<lambda>x. P (f x)" q rule: takeWhile_queue.induct)
  case (1 q)
  then show ?case
    by (subst takeWhile_queue.simps, subst (2) takeWhile_queue.simps)
      (auto simp: Let_def split: prod.splits option.splits simp del: takeWhile_queue.simps)
qed

lemma map_queue_inj: "map_queue reopt q = map_queue reopt q' \<longleftrightarrow> q = q'"
  by transfer (auto simp: inj_map_eq_map inj_reopt split: prod.splits)

text \<open>The queue scan that both drops and returns the dropped prefix, mapped.\<close>

lemma takedropWhile_queue_map_queue:
  "takedropWhile_queue P (map_queue f q)
   = map_prod (map_queue f) (map f) (takedropWhile_queue (\<lambda>x. P (f x)) q)"
proof (induct "\<lambda>x. P (f x)" q rule: takedropWhile_queue.induct)
  case (1 q)
  then show ?case
    by (subst takedropWhile_queue.simps, subst (2) takedropWhile_queue.simps)
      (auto split: prod.splits option.splits simp del: takedropWhile_queue.simps)
qed

subsection \<open>The widening map\<close>

text \<open>
  @{theory MFODL_Monitor_Dense.Dense_Unbox}'s generic @{typ "'b gmmtaux"} is already stated over a
  bare element type, at the two shapes the file's own text works out: the left operand's tuples
  stay at their own frame (narrow, the width of the mask's true positions) throughout the window,
  and only the probe compares them against a projection of the right operand's frame (full
  width).  What is proved here is that this generic structure, at the short element type, stands
  for the kernel's own @{typ "event_data option mmtaux"} exactly as this theory's other
  structures do: by a widening map on the state
  (@{term tmm} below) under which the two step and read the same, no invariant required beyond
  the two frames' widths.  The naturality reaches the update at the interval containing zero,
  which is the only case a standalone trigger node ever takes.
\<close>

text \<open>
  The kernel keeps the left operand's tuples at the frame of the right one, with the columns
  outside the left operand's blank; the dense structure keeps them narrow.  The two differ by
  @{const dwiden} at the mask, in the left tables of the queue, in the keys of the mapping that
  records when a left tuple last held (@{const wkeys}) and in the set of those keys.  Everything
  else is the same object, and the two masks the kernel stores are the dense mask and the
  all-true one.  @{term tmm} is a specification device: the generated code never builds it.
\<close>

fun tmm :: "'a option gmmtaux \<Rightarrow> 'a mmtaux" where
  "tmm (cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tuple_in_once,
      tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) =
    (cur, idx_next, idx_mid, idx_oldest, msk, replicate (length msk) True,
     map_queue (\<lambda>(t, l, r). (t, dwiden msk ` l, r)) data_prev, data_in,
     wkeys msk tuple_in_once, dwiden msk ` tuple_in_once_keys, tuple_since_hist, hist_sat,
     since_sat)"

text \<open>The dense state is narrow: its left tuples have the width of the mask's true positions,
  its right ones the width of the mask, and its mask is the given one.\<close>

fun tnar :: "bool list \<Rightarrow> 'a option gmmtaux \<Rightarrow> bool" where
  "tnar msk (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tuple_in_once,
      tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) \<longleftrightarrow>
    msk' = msk \<and>
    (\<forall>(t, l, r) \<in> set (linearize data_prev).
       (\<forall>y \<in> l. dnarrow_tuple msk y) \<and> (\<forall>x \<in> r. length x = length msk)) \<and>
    (\<forall>k \<in> Mapping.keys tuple_in_once. dnarrow_tuple msk k) \<and>
    (\<forall>y \<in> tuple_in_once_keys. dnarrow_tuple msk y)"

subsection \<open>Widened keys\<close>

lemma wkeys_empty[simp]: "wkeys msk Mapping.empty = Mapping.empty"
  by transfer simp

lemma wkeys_filter:
  "Mapping.filter P (wkeys msk m) = wkeys msk (Mapping.filter (\<lambda>k v. P (dwiden msk k) v) m)"
  by (intro mapping_eqI) (auto simp: Mapping.lookup_filter lookup_wkeys split: option.splits)

lemma wkeys_upd_set:
  assumes X: "\<And>y. y \<in> X \<Longrightarrow> dnarrow_tuple msk y"
  shows "upd_set (wkeys msk m) f (dwiden msk ` X) = wkeys msk (upd_set m (f \<circ> dwiden msk) X)"
proof (intro mapping_eqI)
  fix k
  show "Mapping.lookup (upd_set (wkeys msk m) f (dwiden msk ` X)) k
      = Mapping.lookup (wkeys msk (upd_set m (f \<circ> dwiden msk) X)) k"
  proof (cases "k = dwiden msk (dproj msk k)")
    case True
    then show ?thesis
      by (simp add: Mapping_lookup_upd_set lookup_wkeys dwiden_image_iff[OF X True])
  next
    case False
    then show ?thesis
      by (simp add: Mapping_lookup_upd_set lookup_wkeys dwiden_image_not[OF X False])
  qed
qed

lemma Mapping_filter_cong:
  assumes "\<And>k v. Mapping.lookup m k = Some v \<Longrightarrow> P k v = Q k v"
  shows "Mapping.filter P m = Mapping.filter Q m"
  using assms by (intro mapping_eqI) (auto simp: Mapping.lookup_filter split: option.splits)

lemma filter_cond_wkeys:
  assumes l: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y" and y: "dnarrow_tuple msk y"
  shows "(dwiden msk y \<in> dwiden msk ` l \<and> Mapping.lookup (wkeys msk m) (dwiden msk y) = Some t)
       = (y \<in> l \<and> Mapping.lookup m y = Some t)"
  by (simp add: lookup_wkeys_dwiden[OF y]
      dwiden_image_iff[OF l dwiden_dproj_dwiden[OF y, symmetric]] dproj_dwiden[OF y])

subsection \<open>The semi-join\<close>

lemma dwiden_all_true: "length y = length msk \<Longrightarrow> \<forall>b \<in> set msk. b \<Longrightarrow> dwiden msk y = y"
  by (induct msk y rule: dwiden.induct) auto

lemma dwiden_all_false: "\<forall>b \<in> set msk. \<not> b \<Longrightarrow> dwiden msk [] = replicate (length msk) None"
  by (induct msk) auto

lemma dproj_all_true: "length y = length msk \<Longrightarrow> \<forall>b \<in> set msk. b \<Longrightarrow> dproj msk y = y"
  by (induct msk y rule: dproj.induct) auto

lemma dproj_all_false: "\<forall>b \<in> set msk. \<not> b \<Longrightarrow> dproj msk y = []"
  by (induct msk y rule: dproj.induct) auto

lemma gsemi_join_dsemi:
  assumes r: "\<And>x. x \<in> r \<Longrightarrow> length x = length msk"
  shows "gsemi_join msk pos r l = dsemi msk pos r l"
proof (cases "\<forall>i \<in> set msk. i")
  case True
  then show ?thesis using r by (auto simp: gsemi_join_def dsemi_def dproj_all_true)
next
  case False
  then show ?thesis by (auto simp: gsemi_join_def dsemi_def dproj_all_false)
qed

lemma proj_tuple_in_join_dsemi:
  assumes r: "\<And>x. x \<in> r \<Longrightarrow> length x = length msk"
    and l: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y"
  shows "{as \<in> r. proj_tuple_in_join pos msk as (dwiden msk ` l)} = dsemi msk pos r l"
proof -
  have "proj_tuple_in_join pos msk as (dwiden msk ` l) = ((dproj msk as \<in> l) = pos)"
    if "as \<in> r" for as
    using proj_tuple_dwiden_image_iff[OF r[OF that] l] by (auto simp: proj_tuple_in_join_def)
  then show ?thesis by (auto simp: dsemi_def)
qed

lemma proj_tuple_in_join_optim_dsemi:
  assumes r: "\<And>x. x \<in> r \<Longrightarrow> length x = length msk"
    and l: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y"
  shows "proj_tuple_in_join_optim pos r (replicate (length msk) True) (dwiden msk ` l) msk
     = dsemi msk pos r l"
proof (cases "msk = replicate (length msk) True")
  case True
  then have all: "\<forall>b \<in> set msk. b" by (metis in_set_replicate)
  have "dwiden msk ` l = l"
    using l all by (auto simp: dwiden_all_true filter_id_conv intro!: image_cong[OF refl])
  then show ?thesis
    using True r all by (auto simp: dsemi_def dproj_all_true)
next
  case False
  note ne = False
  show ?thesis
  proof (cases "\<forall>b \<in> set msk. \<not> b")
    case True
    have ln: "\<And>y. y \<in> l \<Longrightarrow> y = []" using l True by (auto simp: filter_empty_conv)
    have "(replicate (length msk) None \<in> dwiden msk ` l) = ([] \<in> l)"
      using ln by (auto simp: dwiden_all_false[OF True, symmetric])
    then show ?thesis
      using ne True by (auto simp: dsemi_def dproj_all_false Let_def)
  next
    case False
    then have nf: "(\<forall>b \<in> set msk. \<not> b) = False" by simp
    show ?thesis
      using ne by (simp add: nf proj_tuple_in_join_dsemi[OF r l])
  qed
qed

subsection \<open>The expiry of the left operand's records\<close>

text \<open>The fold that drops, from the mapping of last occurrences and its key set, the left tuples
  of the time points that leave the interval, is natural in the widening.\<close>

abbreviation (input) temb :: "bool list \<Rightarrow> ts \<times> 'a table \<times> 'a table \<Rightarrow>
    ts \<times> 'a table \<times> 'a table" where
  "temb msk \<equiv> (\<lambda>(t, l, r). (t, dwiden msk ` l, r))"

lemma dwiden_in_image_iff:
  assumes l: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y" and y: "dnarrow_tuple msk y"
  shows "(dwiden msk y \<in> dwiden msk ` l) = (y \<in> l)"
  by (simp add: dwiden_image_iff[OF l dwiden_dproj_dwiden[OF y, symmetric]] dproj_dwiden[OF y])

lemma Collect_image_pred: "{x \<in> f ` A. P x} = f ` {a \<in> A. P (f a)}"
  by auto

lemma fold_filter_once_tmm:
  assumes ds: "\<And>t l r. (t, l, r) \<in> set ds \<Longrightarrow> \<forall>y \<in> l. dnarrow_tuple msk y"
    and tio: "\<And>k. k \<in> Mapping.keys tio \<Longrightarrow> dnarrow_tuple msk k"
    and keys: "\<And>y. y \<in> keys \<Longrightarrow> dnarrow_tuple msk y"
  shows "fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in,
       {as \<in> tuple_in_keys. filter_cond' (fst X) tuple_in t as}))
      (map (temb msk) ds) (wkeys msk tio, dwiden msk ` keys)
    = map_prod (wkeys msk) (image (dwiden msk)) (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in,
       {as \<in> tuple_in_keys. filter_cond' (fst X) tuple_in t as})) ds (tio, keys))"
  using assms
proof (induction ds arbitrary: tio keys)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  obtain t l r where d: "d = (t, l, r)" by (cases d) auto
  have ln: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y" using Cons.prems(1)[of t l r] by (simp add: d id_def)
  have f1: "Mapping.filter (filter_cond (dwiden msk ` l) (wkeys msk tio) t) (wkeys msk tio)
      = wkeys msk (Mapping.filter (filter_cond l tio t) tio)"
    unfolding wkeys_filter
    by (intro arg_cong[where f = "wkeys msk"] Mapping_filter_cong)
      (simp add: dwiden_in_image_iff[OF ln Cons.prems(2)[OF Mapping_keys_intro]]
        lookup_wkeys_dwiden[OF Cons.prems(2)[OF Mapping_keys_intro]])
  have f2: "{as \<in> dwiden msk ` keys. filter_cond' (dwiden msk ` l) (wkeys msk tio) t as}
      = dwiden msk ` {as \<in> keys. filter_cond' l tio t as}"
    unfolding Collect_image_pred
  proof (intro arg_cong[where f = "(`) (dwiden msk)"] Collect_cong)
    fix a
    show "(a \<in> keys \<and> filter_cond' (dwiden msk ` l) (wkeys msk tio) t (dwiden msk a))
        = (a \<in> keys \<and> filter_cond' l tio t a)"
    proof (cases "a \<in> keys")
      case True
      then show ?thesis
        by (simp add: dwiden_in_image_iff[OF ln Cons.prems(3)[OF True]]
            lookup_wkeys_dwiden[OF Cons.prems(3)[OF True]])
    qed simp
  qed
  have k1: "\<And>k. k \<in> Mapping.keys (Mapping.filter (filter_cond l tio t) tio) \<Longrightarrow>
      dnarrow_tuple msk k"
    by (rule Cons.prems(2)) (auto simp: Mapping.keys_dom_lookup Mapping.lookup_filter dom_def
        split: option.splits)
  have k2: "\<And>y. y \<in> {as \<in> keys. filter_cond' l tio t as} \<Longrightarrow> dnarrow_tuple msk y"
    by (rule Cons.prems(3)) simp
  show ?case
    unfolding d list.map fold.simps comp_apply prod.case fst_conv f1 f2
    by (rule Cons.IH[OF _ k1 k2]) (use Cons.prems(1) in \<open>auto simp: d\<close>)
qed

lemma shift_end'_tmm:
  assumes dp: "\<And>t l r. (t, l, r) \<in> set (linearize data_prev) \<Longrightarrow> \<forall>y \<in> l. dnarrow_tuple msk y"
    and tio: "\<And>k. k \<in> Mapping.keys tio \<Longrightarrow> dnarrow_tuple msk k"
    and keys: "\<And>y. y \<in> keys \<Longrightarrow> dnarrow_tuple msk y"
  shows "shift_end' I nt fst (empty_queue, map_queue (temb msk) data_prev, wkeys msk tio,
      dwiden msk ` keys)
    = (case shift_end' I nt fst (empty_queue, data_prev, tio, keys) of
        (q0, dp', move, tio', keys') \<Rightarrow>
          (q0, map_queue (temb msk) dp', map (temb msk) move, wkeys msk tio', dwiden msk ` keys'))"
proof -
  have pe: "(\<lambda>x. (\<lambda>(t, _). \<not> memR I (nt - t)) (temb msk x)) = (\<lambda>(t, _). \<not> memR I (nt - t))"
    by (rule ext) (auto split: prod.splits)
  obtain dp' move where tdq: "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_prev
      = (dp', move)"
    by (cases "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_prev")
  have td: "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) (map_queue (temb msk) data_prev)
      = (map_queue (temb msk) dp', map (temb msk) move)"
    by (simp only: takedropWhile_queue_map_queue pe tdq map_prod_simp)
  have mv: "move = takeWhile (\<lambda>(t, _). \<not> memR I (nt - t)) (linearize data_prev)"
    using takedropWhile_queue_snd[of "\<lambda>(t, _). \<not> memR I (nt - t)" data_prev]
    by (simp add: tdq del: takedropWhile_queue.simps)
  have m: "\<And>t l r. (t, l, r) \<in> set move \<Longrightarrow> \<forall>y \<in> l. dnarrow_tuple msk y"
    using dp by (auto simp: mv dest!: set_takeWhileD)
  show ?thesis
    by (auto simp only: shift_end'.simps Let_def td tdq fold_filter_once_tmm[OF m tio keys]
        map_prod_simp prod.case split: prod.splits)
qed

subsection \<open>The update\<close>

lemma join_mask_all: "join_mask n {0..<n} = replicate n True"
  by (auto simp: join_mask_def intro!: nth_equalityI)

lemma dmsk_args_maskR:
  "dmsk_args args msk \<Longrightarrow> join_mask (args_n args) (args_R args) = replicate (length msk) True"
  by (simp add: dmsk_args_def join_mask_all)

text \<open>The fold over the time points that enter the interval differs between the kernel and the
  dense structure in the semi-join alone, which agree on narrow tables.\<close>

lemma fold_hist_tmm:
  assumes mv: "\<And>t l r. (t, l, r) \<in> set move \<Longrightarrow>
      (\<forall>y \<in> l. dnarrow_tuple msk y) \<and> (\<forall>x \<in> r. length x = length msk)"
  shows "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat = hist_sat \<inter> r;
          since_sat = since_sat \<inter> r
      in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
          hist_sat, idx_move + 1,
          since_sat \<union> proj_tuple_in_join_optim pos r (replicate (length msk) True) l msk))
      (map (temb msk) move) acc
    = fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat = hist_sat \<inter> r;
          since_sat = since_sat \<inter> r
      in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
          hist_sat, idx_move + 1,
          since_sat \<union> gsemi_join msk pos r l)) move acc"
  unfolding fold_map
proof (rule fold_cong[OF refl refl], rule ext)
  fix x acc
  assume x: "x \<in> set move"
  obtain t l r where xe: "x = (t, l, r)" by (cases x)
  have sj: "proj_tuple_in_join_optim pos r (replicate (length msk) True) (dwiden msk ` l) msk
      = gsemi_join msk pos r l"
    using mv[OF x[unfolded xe]]
    by (subst proj_tuple_in_join_optim_dsemi) (auto simp: gsemi_join_dsemi)
  show "((\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat = hist_sat \<inter> r; since_sat = since_sat \<inter> r
      in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
          hist_sat, idx_move + 1,
          since_sat \<union> proj_tuple_in_join_optim pos r (replicate (length msk) True) l msk))
      \<circ> temb msk) x acc
    = (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat = hist_sat \<inter> r; since_sat = since_sat \<inter> r
      in (upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
          hist_sat, idx_move + 1, since_sat \<union> gsemi_join msk pos r l)) x acc"
    by (cases acc) (simp add: xe sj del: proj_tuple_in_join_optim.simps)
qed

lemma fold_append_r_temb:
  "fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) (map (temb msk) move) data_in
   = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move data_in"
  unfolding fold_map by (rule fold_cong[OF refl refl]) (auto split: prod.splits)

lemma filter_temb:
  "filter (\<lambda>(t, _). P t) (map (temb msk) move) = map (temb msk) (filter (\<lambda>(t, _). P t) move)"
  by (induct move) (auto split: prod.splits)

lemma update_mmtaux'_tmm:
  assumes dm: "dmsk_args args msk"
    and dp: "\<And>t l r. (t, l, r) \<in> set (linearize data_prev) \<Longrightarrow>
      (\<forall>y \<in> l. dnarrow_tuple msk y) \<and> (\<forall>x \<in> r. length x = length msk)"
    and tio: "\<And>k. k \<in> Mapping.keys tio \<Longrightarrow> dnarrow_tuple msk k"
    and keys: "\<And>y. y \<in> keys \<Longrightarrow> dnarrow_tuple msk y"
  shows "update_mmtaux' args nt idx_mid idx_oldest msk (replicate (length msk) True)
      (map_queue (temb msk) data_prev) data_in (wkeys msk tio) (dwiden msk ` keys)
      tuple_since_hist hist_sat since_sat
    = (case gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat of
        (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss') \<Rightarrow>
          (idx_mid', idx_oldest', map_queue (temb msk) data_prev', data_in', wkeys msk tio',
           dwiden msk ` keys', tsh', hs', ss'))"
proof -
  obtain q0 dp' move tio' keys' where se:
    "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> 'a table \<times> 'a table) queue, data_prev, tio, keys)
      = (q0, dp', move, tio', keys')"
    by (cases "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> 'a table \<times> 'a table) queue, data_prev, tio, keys)") auto
  have dpl: "\<And>t l r. (t, l, r) \<in> set (linearize data_prev) \<Longrightarrow> \<forall>y \<in> l. dnarrow_tuple msk y"
    using dp by blast
  have se': "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
      (empty_queue :: (ts \<times> 'a table \<times> 'a table) queue,
       map_queue (temb msk) data_prev, wkeys msk tio, dwiden msk ` keys)
    = (q0, map_queue (temb msk) dp', map (temb msk) move, wkeys msk tio', dwiden msk ` keys')"
    by (simp only: shift_end'_tmm[OF dpl tio keys] se prod.case)
  have mv: "set move \<subseteq> set (linearize data_prev)"
    using se by (auto simp add: shift_end'.simps Let_def takedropWhile_queue_snd case_prod_beta
        simp del: takedropWhile_queue.simps dest: set_takeWhileD)
  have mvm: "\<And>t l r. (t, l, r) \<in> set move \<Longrightarrow>
      (\<forall>y \<in> l. dnarrow_tuple msk y) \<and> (\<forall>x \<in> r. length x = length msk)"
    by (rule dp[OF subsetD[OF mv]])
  obtain di' drop where td:
    "takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in = (di', drop)"
    by (cases "takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in") auto
  obtain tsh' hs' idx ss' where fh:
    "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
       (upd_set (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist) (\<lambda>_. idx_move)
          (r - Mapping.keys (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist)),
        hist_sat \<inter> r, idx_move + 1, since_sat \<inter> r \<union> gsemi_join msk (args_pos args) r l))
       move (tuple_since_hist, hist_sat, idx_mid, since_sat) = (tsh', hs', idx, ss')"
    by (cases "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
       (upd_set (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist) (\<lambda>_. idx_move)
          (r - Mapping.keys (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist)),
        hist_sat \<inter> r, idx_move + 1, since_sat \<inter> r \<union> gsemi_join msk (args_pos args) r l))
       move (tuple_since_hist, hist_sat, idx_mid, since_sat)") auto
  show ?thesis
    by (simp only: update_mmtaux'_def gupdate_mmtaux'_def Let_def se se' prod.case
      dmsk_args_maskL[OF dm] dmsk_args_maskR[OF dm] filter_temb length_map fold_append_r_temb
      fold_hist_tmm[OF mvm, unfolded Let_def] td fh)
qed

text \<open>Both branches of @{const update_mmtaux} widen.  The one at an interval containing zero is
  the only one a standalone trigger node ever takes; the other, which records the left operand's
  tuples in the queue and in the mapping of last occurrences, is the one the And-Trigger node
  needs, and it widens by @{thm [source] wkeys_upd_set}.\<close>

lemma update_mmtaux_tmm:
  assumes dm: "dmsk_args args msk"
    and adp: "\<And>t l r. (t, l, r) \<in> set (linearize data_prev) \<Longrightarrow>
      (\<forall>y \<in> l. dnarrow_tuple msk y) \<and> (\<forall>x \<in> r. length x = length msk)"
    and atio: "\<And>k. k \<in> Mapping.keys tio \<Longrightarrow> dnarrow_tuple msk k"
    and akeys: "\<And>y. y \<in> keys \<Longrightarrow> dnarrow_tuple msk y"
    and lw: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y" and rw: "\<And>x. x \<in> r \<Longrightarrow> length x = length msk"
  shows "update_mmtaux args nt (dwiden msk ` l) r
      (cur, idx_next, idx_mid, idx_oldest, msk, replicate (length msk) True,
       map_queue (temb msk) data_prev, data_in, wkeys msk tio, dwiden msk ` keys,
       tuple_since_hist, hist_sat, since_sat)
    = tmm (gupdate_mmtaux args nt l r
        (cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tio, keys,
         tuple_since_hist, hist_sat, since_sat))"
proof -
  obtain idx_mid' idx_oldest' data_prev' data_in' tio' keys' tsh' hs' ss' where g:
    "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat
      = (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss')"
    by (metis surj_pair)
  have u0: "update_mmtaux' args nt idx_mid idx_oldest msk (replicate (length msk) True)
      (map_queue (temb msk) data_prev) data_in (wkeys msk tio) (dwiden msk ` keys)
      tuple_since_hist hist_sat since_sat
    = (case gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat of
        (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss') \<Rightarrow>
          (idx_mid', idx_oldest', map_queue (temb msk) data_prev', data_in', wkeys msk tio',
           dwiden msk ` keys', tsh', hs', ss'))"
    by (rule update_mmtaux'_tmm[OF dm adp atio akeys])
  have u: "update_mmtaux' args nt idx_mid idx_oldest msk (replicate (length msk) True)
      (map_queue (temb msk) data_prev) data_in (wkeys msk tio) (dwiden msk ` keys)
      tuple_since_hist hist_sat since_sat
    = (idx_mid', idx_oldest', map_queue (temb msk) data_prev', data_in', wkeys msk tio',
       dwiden msk ` keys', tsh', hs', ss')"
    unfolding u0 g by simp
  note pj = proj_tuple_in_join_dsemi[OF rw lw]
  have sj: "{as \<in> r. proj_tuple_in_join (args_pos args) msk as (dwiden msk ` l)}
      = gsemi_join msk (args_pos args) r l"
    by (simp only: pj gsemi_join_dsemi[OF rw])
  have wk: "upd_set (wkeys msk tio') (\<lambda>_. nt) (dwiden msk ` l)
      = wkeys msk (upd_set tio' (\<lambda>_. nt) l)"
    using wkeys_upd_set[OF lw, where f = "\<lambda>_. nt" and m = tio'] by (simp add: comp_def)
  have aq: "append_queue (nt, dwiden msk ` l, r) (map_queue (temb msk) data_prev')
      = map_queue (temb msk) (append_queue (nt, l, r) data_prev')"
    using append_queue_map_queue[of "temb msk" "(nt, l, r)" data_prev'] by simp
  show ?thesis
    unfolding update_mmtaux_def gupdate_mmtaux_def Let_def prod.case u g
      dmsk_args_maskL[OF dm] dmsk_args_maskR[OF dm] sj
    by (simp add: wk aq image_Un)
qed

subsection \<open>The invariant the standalone trigger keeps\<close>

text \<open>
  With @{term "mem (args_ivl args) 0"} the update never takes the branch that records a left
  tuple: the queue of the time points still outside the interval and the mapping of last
  occurrences stay at their initial, empty values throughout.  That is what makes the widening
  map's hypotheses free, and it is also what makes the read of the result agree, since the set
  of keys the kernel unions into its answer is the empty one on both sides.
\<close>

text \<open>The queue scans on the empty queue, which the state's left-hand half stays at.\<close>

lemma safe_hd_empty_queue[simp]: "safe_hd empty_queue = (None, empty_queue)"
  by transfer simp

lemma dropWhile_queue_empty_queue[simp]: "dropWhile_queue P empty_queue = empty_queue"
  by (subst dropWhile_queue.simps) simp

lemma takedropWhile_queue_empty_queue[simp]:
  "takedropWhile_queue P empty_queue = (empty_queue, [])"
  by (subst takedropWhile_queue.simps) simp

fun tvoid :: "bool list \<Rightarrow> 'a gmmtaux \<Rightarrow> bool" where
  "tvoid msk (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tuple_in_once,
      tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) \<longleftrightarrow>
    msk' = msk \<and> data_prev = empty_queue \<and> tuple_in_once = Mapping.empty \<and>
    tuple_in_once_keys = {}"

lemma tvoid_tnar: "tvoid msk ax \<Longrightarrow> tnar msk ax"
  by (cases ax rule: tmm.cases) (simp add: empty_queue_rep)

lemma tvoid_ginit: "tvoid msk (ginit_mmtaux args msk)"
  by (simp add: ginit_mmtaux_def)

text \<open>@{const shift_end'} only drops from the three arguments the trigger's update hands it in
  the places the standalone node keeps empty, so it keeps them empty.\<close>

lemma gupdate_mmtaux'_void:
  "case gupdate_mmtaux' args nt idx_mid idx_oldest msk empty_queue data_in Mapping.empty {}
      tuple_since_hist hist_sat since_sat of
     (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss') \<Rightarrow>
       data_prev' = empty_queue \<and> tio' = Mapping.empty \<and> keys' = {}"
  by (simp add: gupdate_mmtaux'_def Let_def shift_end'.simps split: prod.splits)

lemma gupdate_mmtaux_tvoid:
  assumes m0: "mem (args_ivl args) 0" and v: "tvoid msk ax"
  shows "tvoid msk (gupdate_mmtaux args nt l r ax)"
proof -
  obtain cur idx_next idx_mid idx_oldest msk' data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (metis surj_pair)
  have m: "msk' = msk" and dp: "data_prev = empty_queue" and tio: "tio = Mapping.empty"
    and keys: "keys = {}" using v ax by simp_all
  show ?thesis unfolding ax m dp tio keys
    using gupdate_mmtaux'_void[of args nt idx_mid idx_oldest msk data_in tsh hs ss] m0
    by (simp add: gupdate_mmtaux_def Let_def split: prod.splits)
qed

text \<open>
  The And-Trigger node's interval need not contain zero, and then the update does record a left
  tuple: the state stays narrow rather than void.  Narrowness is preserved for a simpler reason
  than voidness -- the scan the update opens with only drops from the three places narrowness
  constrains, and what the step then adds is the operands' own tables.
\<close>

lemma fold_filter_once_shrink:
  "case fold (\<lambda>(t, X) (tio, keys).
        (Mapping.filter (filter_cond (to_table X) tio t) tio,
         {as \<in> keys. filter_cond' (to_table X) tio t as})) xs (tio, keys) of
     (tio', keys') \<Rightarrow> Mapping.keys tio' \<subseteq> Mapping.keys tio \<and> keys' \<subseteq> keys"
proof (induct xs arbitrary: tio keys)
  case (Cons x xs)
  obtain t X where x: "x = (t, X)" by (cases x)
  show ?case
    using Cons[of "Mapping.filter (filter_cond (to_table X) tio t) tio"
        "{as \<in> keys. filter_cond' (to_table X) tio t as}"] keys_filter
    by (fastforce simp: x split: prod.splits)
qed simp

lemma shift_end'_sub:
  assumes se: "shift_end' I nt to_table (q, data_in, tio, keys) = (q0, di', move, tio', keys')"
  shows "set (linearize di') \<subseteq> set (linearize data_in) \<and> set move \<subseteq> set (linearize data_in) \<and>
    Mapping.keys tio' \<subseteq> Mapping.keys tio \<and> keys' \<subseteq> keys"
proof -
  obtain di'' mv where td: "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_in = (di'', mv)"
    by (cases "takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_in")
  have l1: "set (linearize di'') \<subseteq> set (linearize data_in)"
    using takedropWhile_queue_fst[of "\<lambda>(t, _). \<not> memR I (nt - t)" data_in]
    by (auto simp: td dropWhile_queue_rep
        simp del: takedropWhile_queue.simps dropWhile_queue.simps dest: set_dropWhileD)
  have l2: "set mv \<subseteq> set (linearize data_in)"
    using takedropWhile_queue_snd[of "\<lambda>(t, _). \<not> memR I (nt - t)" data_in]
    by (auto simp: td simp del: takedropWhile_queue.simps dest: set_takeWhileD)
  obtain tio'' keys'' where fo:
    "fold (\<lambda>(t, X) (tio, keys). (Mapping.filter (filter_cond (to_table X) tio t) tio,
        {as \<in> keys. filter_cond' (to_table X) tio t as})) mv (tio, keys) = (tio'', keys'')"
    by (cases "fold (\<lambda>(t, X) (tio, keys). (Mapping.filter (filter_cond (to_table X) tio t) tio,
        {as \<in> keys. filter_cond' (to_table X) tio t as})) mv (tio, keys)")
  have l34: "Mapping.keys tio'' \<subseteq> Mapping.keys tio \<and> keys'' \<subseteq> keys"
    using fold_filter_once_shrink[where to_table = to_table and xs = mv and tio = tio
        and keys = keys, unfolded fo prod.case] .
  have s: "shift_end' I nt to_table (q, data_in, tio, keys)
      = (dropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) q, di'', mv, tio'', keys'')"
    by (simp only: shift_end'.simps Let_def td fo prod.case)
  show ?thesis using l1 l2 l34 se[unfolded s] by auto
qed

lemma shift_end'_tnar:
  fixes data_prev :: "(ts \<times> 'b table \<times> 'b table) queue"
  assumes dp: "\<forall>(t, a, b) \<in> set (linearize data_prev).
      (\<forall>y \<in> a. dnarrow_tuple msk y) \<and> (\<forall>x \<in> b. length x = length msk)"
    and tio: "\<forall>k \<in> Mapping.keys tio. dnarrow_tuple msk k"
    and keys: "\<forall>y \<in> keys. dnarrow_tuple msk y"
    and se: "shift_end' I nt fst (q, data_prev, tio, keys) = (q0, dp', move, tio', keys')"
  shows "(\<forall>(t, a, b) \<in> set (linearize dp').
        (\<forall>y \<in> a. dnarrow_tuple msk y) \<and> (\<forall>x \<in> b. length x = length msk)) \<and>
      (\<forall>k \<in> Mapping.keys tio'. dnarrow_tuple msk k) \<and> (\<forall>y \<in> keys'. dnarrow_tuple msk y)"
  using shift_end'_sub[OF se] dp tio keys by fastforce

text \<open>The update's scan is the only thing that touches the three places the invariants below
  constrain; these read the scan's three answers off the update's state.\<close>

lemma gupdate_mmtaux'_shift:
  fixes data_prev :: "(ts \<times> 'b table \<times> 'b table) queue"
  assumes se: "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
      (empty_queue :: (ts \<times> 'b table \<times> 'b table) queue, data_prev, tio, keys)
    = (q0, dp', move, tio2, keys2)"
    and g: "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat
      = (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss')"
  shows "data_prev' = dp' \<and> tio' = tio2 \<and> keys' = keys2"
proof -
  obtain di' drop where td:
    "takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in = (di', drop)"
    by (cases "takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in") auto
  obtain tsh' hs' idx ss' where fh:
    "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
       (upd_set (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist) (\<lambda>_. idx_move)
          (r - Mapping.keys (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist)),
        hist_sat \<inter> r, idx_move + 1, since_sat \<inter> r \<union> gsemi_join msk (args_pos args) r l))
       move (tuple_since_hist, hist_sat, idx_mid, since_sat) = (tsh', hs', idx, ss')"
    by (cases "fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
       (upd_set (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist) (\<lambda>_. idx_move)
          (r - Mapping.keys (Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist)),
        hist_sat \<inter> r, idx_move + 1, since_sat \<inter> r \<union> gsemi_join msk (args_pos args) r l))
       move (tuple_since_hist, hist_sat, idx_mid, since_sat)") auto
  show ?thesis
    using g[unfolded gupdate_mmtaux'_def Let_def se td fh prod.case] by simp
qed

text \<open>The update's scan keeps the three places narrowness constrains narrow, and the branch the
  And-Trigger node takes then adds the operands' own tuples, which the node's mask fits.\<close>

lemma gupdate_mmtaux'_tnar:
  fixes data_prev :: "(ts \<times> 'b table \<times> 'b table) queue"
  assumes dp: "\<forall>(t, a, b) \<in> set (linearize data_prev).
      (\<forall>y \<in> a. dnarrow_tuple msk y) \<and> (\<forall>x \<in> b. length x = length msk)"
    and tio: "\<forall>k \<in> Mapping.keys tio. dnarrow_tuple msk k"
    and keys: "\<forall>y \<in> keys. dnarrow_tuple msk y"
  shows "case gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat of
      (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss') \<Rightarrow>
        (\<forall>(t, a, b) \<in> set (linearize data_prev').
           (\<forall>y \<in> a. dnarrow_tuple msk y) \<and> (\<forall>x \<in> b. length x = length msk)) \<and>
        (\<forall>k \<in> Mapping.keys tio'. dnarrow_tuple msk k) \<and> (\<forall>y \<in> keys'. dnarrow_tuple msk y)"
proof -
  obtain q0 dp' move tio2 keys2 where se:
    "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> 'b table \<times> 'b table) queue, data_prev, tio, keys)
      = (q0, dp', move, tio2, keys2)"
    by (cases "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> 'b table \<times> 'b table) queue, data_prev, tio, keys)") auto
  obtain im io dpp dii tt kk t1 t2 t3 where g:
    "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat = (im, io, dpp, dii, tt, kk, t1, t2, t3)"
    by (metis surj_pair)
  show ?thesis unfolding g prod.case
    using shift_end'_tnar[OF dp tio keys se] gupdate_mmtaux'_shift[OF se g] by simp
qed

lemma gupdate_mmtaux'_keys_sub:
  fixes data_prev :: "(ts \<times> 'b table \<times> 'b table) queue"
  shows "case gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat of
      (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss') \<Rightarrow> keys' \<subseteq> keys"
proof -
  obtain q0 dp' move tio2 keys2 where se:
    "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> 'b table \<times> 'b table) queue, data_prev, tio, keys)
      = (q0, dp', move, tio2, keys2)"
    by (cases "shift_end' (flip_int_less_lower (args_ivl args)) nt fst
        (empty_queue :: (ts \<times> 'b table \<times> 'b table) queue, data_prev, tio, keys)") auto
  obtain im io dpp dii tt kk t1 t2 t3 where g:
    "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys
        tuple_since_hist hist_sat since_sat = (im, io, dpp, dii, tt, kk, t1, t2, t3)"
    by (metis surj_pair)
  show ?thesis unfolding g prod.case
    using shift_end'_sub[OF se] gupdate_mmtaux'_shift[OF se g] by simp
qed
lemma gupdate_mmtaux_tnar:
  assumes v: "tnar msk ax"
    and lw: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y" and rw: "\<And>x. x \<in> r \<Longrightarrow> length x = length msk"
  shows "tnar msk (gupdate_mmtaux args nt l r ax)"
proof -
  obtain cur idx_next idx_mid idx_oldest msk' data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (metis surj_pair)
  have m: "msk' = msk"
    and adp: "\<forall>(t, a, b) \<in> set (linearize data_prev).
       (\<forall>y \<in> a. dnarrow_tuple msk y) \<and> (\<forall>x \<in> b. length x = length msk)"
    and atio: "\<forall>k \<in> Mapping.keys tio. dnarrow_tuple msk k"
    and akeys: "\<forall>y \<in> keys. dnarrow_tuple msk y"
    using v unfolding ax by simp_all
  obtain idx_mid' idx_oldest' data_prev' data_in' tio' keys' tsh' hs' ss' where g:
    "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
      = (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss')"
    by (metis surj_pair)
  have n: "(\<forall>(t, a, b) \<in> set (linearize data_prev').
        (\<forall>y \<in> a. dnarrow_tuple msk y) \<and> (\<forall>x \<in> b. length x = length msk)) \<and>
      (\<forall>k \<in> Mapping.keys tio'. dnarrow_tuple msk k) \<and> (\<forall>y \<in> keys'. dnarrow_tuple msk y)"
    using gupdate_mmtaux'_tnar[OF adp atio akeys, where args = args and nt = nt
        and idx_mid = idx_mid and idx_oldest = idx_oldest and data_in = data_in
        and tuple_since_hist = tsh and hist_sat = hs and since_sat = ss]
    unfolding g prod.case .
  show ?thesis
    unfolding ax m gupdate_mmtaux_def Let_def prod.case g
    using n lw rw by (auto simp: append_queue_rep Mapping_upd_set_keys)
qed

subsection \<open>The invariant the fused And-Trigger keeps\<close>

text \<open>
  The And-Trigger node's state does record left tuples, so the read of the widened state unions
  in their widening rather than the tuples themselves.  The two agree exactly when the widening
  map is the identity on what is stored, and that is the second invariant the node keeps.  It
  holds vacuously while the set of recorded keys is empty, which is the standalone trigger's
  case, and it holds outright when the two operand frames coincide, which is what the safety of
  a trigger whose interval misses zero forces.
\<close>

fun tfix :: "'a option gmmtaux \<Rightarrow> bool" where
  "tfix (cur, idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tuple_in_once,
      tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) \<longleftrightarrow>
    (\<forall>y \<in> tuple_in_once_keys. dwiden msk y = y)"

lemma tvoid_tfix: "tvoid msk ax \<Longrightarrow> tfix ax"
  by (cases ax rule: tmm.cases) simp

lemma tfix_ginit: "tfix (ginit_mmtaux args msk)"
  by (simp add: ginit_mmtaux_def)

lemma dwiden_all: "\<forall>b \<in> set msk. b \<Longrightarrow> length y = length msk \<Longrightarrow> dwiden msk y = y"
  by (induct msk y rule: dwiden.induct) auto

lemma gupdate_mmtaux_tfix:
  assumes n: "tnar msk ax" and v: "tfix ax"
    and lw: "mem (args_ivl args) 0 \<or> (\<forall>y \<in> l. dwiden msk y = y)"
  shows "tfix (gupdate_mmtaux args nt l r ax)"
proof -
  obtain cur idx_next idx_mid idx_oldest msk' data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (metis surj_pair)
  have m: "msk' = msk" using n unfolding ax by simp
  have akeys: "\<forall>y \<in> keys. dwiden msk y = y" using v unfolding ax m by simp
  obtain idx_mid' idx_oldest' data_prev' data_in' tio' keys' tsh' hs' ss' where g:
    "gupdate_mmtaux' args nt idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
      = (idx_mid', idx_oldest', data_prev', data_in', tio', keys', tsh', hs', ss')"
    by (metis surj_pair)
  have ks: "keys' \<subseteq> keys"
    using gupdate_mmtaux'_keys_sub[where args = args and nt = nt and idx_mid = idx_mid
        and idx_oldest = idx_oldest and msk = msk and data_prev = data_prev
        and data_in = data_in and tio = tio and keys = keys and tuple_since_hist = tsh
        and hist_sat = hs and since_sat = ss]
    unfolding g prod.case .
  show ?thesis
    unfolding ax m gupdate_mmtaux_def Let_def prod.case g
    using akeys ks lw by auto
qed

text \<open>The two reads of the structure.  On a non-empty window the kernel's read unions in the
  widened keys, which the second invariant leaves alone; on an empty one it answers the full
  table, which the dense node turns into the absence of a constraint.\<close>

lemma result_mmtaux_tmm:
  assumes v: "tfix ax" and ne: "\<not> gmmtaux_empty ax"
  shows "snd (result_mmtaux args (tmm ax)) = gresult_mmtaux args ax"
  using assms
  by (cases ax rule: tmm.cases) (auto simp: gmmtaux_empty_def gresult_mmtaux_def)

lemma result_mmtaux_empty:
  assumes e: "gmmtaux_empty ax"
  shows "result_mmtaux args (tmm ax) = ({}, {replicate (args_n args) None})"
  using e by (cases ax rule: tmm.cases) (simp add: gmmtaux_empty_def)

lemma init_mmtaux_tmm:
  assumes dm: "dmsk_args args msk"
  shows "tmm (ginit_mmtaux args msk) = init_mmtaux args"
  by (simp add: ginit_mmtaux_def init_mmtaux_def dmsk_args_maskL[OF dm] dmsk_args_maskR[OF dm])

text \<open>The update, packaged at the state rather than its components: this is the form the
  evaluator's trigger node uses.\<close>

lemma update_mmtaux_tmm':
  assumes dm: "dmsk_args args msk" and v: "tnar msk ax"
    and lw: "\<And>y. y \<in> l \<Longrightarrow> dnarrow_tuple msk y" and rw: "\<And>x. x \<in> r \<Longrightarrow> length x = length msk"
  shows "update_mmtaux args nt (dwiden msk ` l) r (tmm ax) = tmm (gupdate_mmtaux args nt l r ax)"
proof -
  obtain cur idx_next idx_mid idx_oldest msk' data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (metis surj_pair)
  have m: "msk' = msk"
    and adp: "\<And>t a b. (t, a, b) \<in> set (linearize data_prev) \<Longrightarrow>
       (\<forall>y \<in> a. dnarrow_tuple msk y) \<and> (\<forall>x \<in> b. length x = length msk)"
    and atio: "\<And>k. k \<in> Mapping.keys tio \<Longrightarrow> dnarrow_tuple msk k"
    and akeys: "\<And>y. y \<in> keys \<Longrightarrow> dnarrow_tuple msk y"
    using v unfolding ax by auto
  show ?thesis unfolding ax m tmm.simps
    by (rule update_mmtaux_tmm[OF dm adp atio akeys lw rw])
qed

text \<open>With the interval containing zero the window is never empty after a step: the update
  appends the right operand's table to it.\<close>

lemma gupdate_mmtaux_not_empty:
  assumes m0: "mem (args_ivl args) 0"
  shows "\<not> gmmtaux_empty (gupdate_mmtaux args nt l r ax)"
proof -
  obtain cur idx_next idx_mid idx_oldest msk' data_prev data_in tio keys tsh hs ss
    where ax: "ax = (cur, idx_next, idx_mid, idx_oldest, msk', data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (metis surj_pair)
  show ?thesis using m0 unfolding ax
    by (simp add: gmmtaux_empty_def gupdate_mmtaux_def Let_def Queue.is_empty_alt
        append_queue_rep split: prod.splits)
qed

text \<open>The read of the trigger structure is a finite table over the right operand's columns.
  With an interval containing zero that is immediate, because the window then always holds the
  latest time point and the read is contained in its right table.  Without it a safe trigger has
  the same free variables on both sides, and the read is contained in the union of the window's
  tables -- which is what the weakened form below states, with the reported column set only
  bounded rather than fixed.\<close>

lemma ftable_trigger_results:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable n L l \<and> ftable n R r"
    and ne: "auxlist \<noteq> []" and m0: "mem (args_ivl args) 0"
    and lst: "fst (last auxlist) = cur"
    and an: "args_n args = n" and aR: "args_R args = R"
  shows "ftable n R (snd (trigger_results args cur auxlist))"
    and "fst (trigger_results args cur auxlist) = R"
proof -
  have kl: "length auxlist - 1 < length auxlist" using ne by simp
  obtain l0 r0 where a0: "auxlist ! (length auxlist - 1) = (cur, l0, r0)"
    using lst ne by (cases "auxlist ! (length auxlist - 1)") (simp add: last_conv_nth)
  have mem0: "auxlist ! (length auxlist - 1) \<in> set auxlist" using kl by (rule nth_mem)
  have tr0: "ftable n R r0" using wf mem0 a0 by force
  have mm: "mem (args_ivl args) (cur - cur)" using m0 by simp
  have m: "(cur, l0, r0) \<in> set auxlist" using mem0 a0 by simp
  have fl: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist \<noteq> []"
  proof
    assume e: "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []"
    have "\<forall>x \<in> set auxlist. \<not> (case x of (t, _, _) \<Rightarrow> mem (args_ivl args) (cur - t))"
      using e unfolding filter_empty_conv by simp
    from this[rule_format, OF m] show False using mm by simp
  qed
  have tb: "table n R (snd (trigger_results args cur auxlist))"
    using fl an aR by (auto simp: table_def)
  have sub: "snd (trigger_results args cur auxlist) \<subseteq> r0"
  proof
    fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
    have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
        mem (args_ivl args) (cur - t) \<longrightarrow>
        (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
           join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
             (proj_tuple (join_mask (args_n args) (args_L args)) tu)))"
      using tu fl by simp
    have "{length auxlist - 1<..<length auxlist} = {}" using ne by auto
    then show "tu \<in> r0" using H[rule_format, of "length auxlist - 1"] kl a0 mm by simp
  qed
  have fin: "finite (snd (trigger_results args cur auxlist))"
    by (rule finite_subset[OF sub]) (use tr0 in simp)
  show "ftable n R (snd (trigger_results args cur auxlist))" using tb fin by simp
  show "fst (trigger_results args cur auxlist) = R" using fl aR by simp
qed


lemma ftable_trigger_results_weak:
  fixes args :: args
  assumes wf: "\<forall>(t, l, r) \<in> set auxlist. ftable n L l \<and> ftable n R r"
    and ne: "auxlist \<noteq> []" and lst: "fst (last auxlist) = cur"
    and an: "args_n args = n" and aL: "args_L args = L" and aR: "args_R args = R"
    and wkc: "mem (args_ivl args) 0 \<or> (args_pos args \<and> L = R)"
  shows "ftable n (fst (trigger_results args cur auxlist))
      (snd (trigger_results args cur auxlist)) \<and>
    fst (trigger_results args cur auxlist) \<subseteq> R"
proof (cases "mem (args_ivl args) 0")
  case True
  show ?thesis using ftable_trigger_results[OF wf ne True lst an aR] by simp
next
  case False
  then have pos: "args_pos args" and LR: "L = R" using wkc by auto
  show ?thesis
  proof (cases "filter (\<lambda>(t, _, _). mem (args_ivl args) (cur - t)) auxlist = []")
    case True
    then show ?thesis by (simp add: table_def wf_tuple_def an)
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
    have tr0: "ftable n R r0" using wf x x0 by force
    have tb: "table n R (snd (trigger_results args cur auxlist))"
      using fl an aR by (auto simp: table_def)
    have sub: "snd (trigger_results args cur auxlist)
        \<subseteq> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. (fst \<circ> snd) (auxlist ! j))"
    proof
      fix tu assume tu: "tu \<in> snd (trigger_results args cur auxlist)"
      have wt: "wf_tuple n R tu" using tu fl an aR by simp
      have pj: "proj_tuple (join_mask (args_n args) (args_L args)) tu = tu"
        using wf_tuple_proj_idle[OF wt] an aL LR by simp
      have H: "\<forall>i \<in> {0..<length auxlist}. case auxlist ! i of (t, l, r) \<Rightarrow>
          mem (args_ivl args) (cur - t) \<longrightarrow>
          (tu \<in> r \<or> (\<exists>j \<in> {i<..<length auxlist}.
             join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
               (proj_tuple (join_mask (args_n args) (args_L args)) tu)))"
        using tu fl by simp
      have jc: "\<And>t. join_cond (args_pos args) t
          (proj_tuple (join_mask (args_n args) (args_L args)) tu) = (tu \<in> t)"
        using pos pj by simp
      have step: "tu \<in> r0 \<or> (\<exists>j \<in> {i0<..<length auxlist}.
          join_cond (args_pos args) ((fst \<circ> snd) (auxlist ! j))
            (proj_tuple (join_mask (args_n args) (args_L args)) tu))"
        using H[rule_format, of i0] i0 xi mm by simp
      show "tu \<in> r0 \<union> (\<Union>j \<in> {0..<length auxlist}. (fst \<circ> snd) (auxlist ! j))"
        using step unfolding jc by auto
    qed
    have finl: "finite (\<Union>j \<in> {0..<length auxlist}. (fst \<circ> snd) (auxlist ! j))"
    proof (rule finite_UN_I[OF finite_atLeastLessThan])
      fix j assume "j \<in> {0..<length auxlist}"
      then have m: "auxlist ! j \<in> set auxlist" by simp
      obtain vj lj rj where e: "auxlist ! j = (vj, lj, rj)" by (cases "auxlist ! j")
      show "finite ((fst \<circ> snd) (auxlist ! j))" using wf m unfolding e by force
    qed
    have fin: "finite (snd (trigger_results args cur auxlist))"
      by (rule finite_subset[OF sub]) (use tr0 finl in simp)
    show ?thesis using tb fin fl aR by simp
  qed
qed

subsection \<open>The auxiliary list a narrow trigger structure stands for\<close>

text \<open>
  The evaluator's trigger node carries the narrow structure, and is related to the kernel's
  abstract auxiliary list through the kernel's own validity of the widened state.  The
  hypotheses of the widening map are kept as part of the relation, as the invariants
  @{const tnar} and @{const tfix}, which the initial state has and the update preserves.  Both
  the standalone trigger and the fused And-Trigger use this relation; they differ only in the
  side condition @{term tok}, which the standalone node meets by its interval and the fused one
  by its two operand frames agreeing.
\<close>

definition tok :: "cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> bool" where
  "tok cs_R cs_L args \<longleftrightarrow> mem (args_ivl args) 0 \<or> (cs_L = cs_R \<and> args_pos args)"

lemma tok_mem0: "mem (args_ivl args) 0 \<Longrightarrow> tok cs_R cs_L args"
  by (simp add: tok_def)

lemma tok_weak:
  "tok cs_R cs_L args \<Longrightarrow> mem (args_ivl args) 0 \<or> (args_pos args \<and> set cs_L = set cs_R)"
  by (auto simp: tok_def)

lemma dmsk_all:
  assumes s: "sorted_wrt (<) cs"
  shows "\<forall>b \<in> set (dmsk cs cs). b"
proof (rule ballI)
  have l: "length (dmsk cs cs) = length cs"
    unfolding dmsk_def by (rule length_mrg_left_key[OF s s order.refl])
  fix b assume "b \<in> set (dmsk cs cs)"
  then obtain i where i: "i < length (dmsk cs cs)" and bi: "b = dmsk cs cs ! i"
    by (auto simp: in_set_conv_nth)
  show "b" using nth_mrg_left_key[OF s s order.refl, of i] i l
    unfolding bi dmsk_def by simp
qed

definition dtaux :: "nat \<Rightarrow> cols \<Rightarrow> cols \<Rightarrow> args \<Rightarrow> ts \<Rightarrow> event_data option gmmtaux \<Rightarrow>
    event_data mtaux \<Rightarrow> bool" where
  "dtaux n cs_R cs_L args cur daux auxlist \<longleftrightarrow>
     (\<forall>(t, l, r) \<in> set auxlist. table n (set cs_L) l \<and> table n (set cs_R) r) \<and>
     tnar (dmsk cs_R cs_L) daux \<and> tfix daux \<and>
     valid_mmtaux (dargs cs_R cs_L args) cur (tmm daux) (dauxlist3 n cs_R auxlist)"

lemma dtaux_init:
  assumes s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and sub: "set cs_L \<subseteq> set cs_R" and ok: "tok cs_R cs_L args"
  shows "dtaux n cs_R cs_L args 0 (ginit_mmtaux (dargs cs_R cs_L args) (dmsk cs_R cs_L)) []"
proof -
  have sub': "cpos cs_R (set cs_L) \<subseteq> {0..<length cs_R}"
    by (auto simp: cpos_def)
  have dm: "dmsk_args (dargs cs_R cs_L args) (dmsk cs_R cs_L)"
    unfolding dmsk_def by (rule dmsk_args_dargs[OF s_R s_L sub])
  have "valid_mmtaux (dargs cs_R cs_L args) 0 (init_mmtaux (dargs cs_R cs_L args)) []"
    using valid_init_mmtaux[where I = "args_ivl args" and n = "length cs_R"
        and L = "cpos cs_R (set cs_L)" and R = "{0..<length cs_R}"
        and pos = "args_pos args" and agg = None]
      ok sub'
    by (auto simp: dargs_def Let_def tok_def cpos_all)
  then show ?thesis
    by (simp add: dtaux_def dauxlist3_def tvoid_tnar[OF tvoid_ginit] tfix_ginit
        init_mmtaux_tmm[OF dm])
qed

lemma dtaux_update:
  assumes v: "dtaux n cs_R cs_L args cur daux auxlist" and nt: "cur \<le> nt"
    and s_R: "sorted_wrt (<) cs_R" and s_L: "sorted_wrt (<) cs_L"
    and b: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and ok: "tok cs_R cs_L args"
    and tl: "table n (set cs_L) l" and tr: "table n (set cs_R) r"
  shows "dtaux n cs_R cs_L args nt
      (gupdate_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_L l) (dtabc n cs_R r) daux)
      (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist @ [(nt, l, r)])"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table n (set cs_L) l \<and> table n (set cs_R) r"
    and vn: "tnar (dmsk cs_R cs_L) daux" and vf: "tfix daux"
    and d: "valid_mmtaux (dargs cs_R cs_L args) cur (tmm daux) (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: dtaux_def)
  have b_L: "\<forall>c \<in> set cs_L. c < n" using sub b by auto
  have dm: "dmsk_args (dargs cs_R cs_L args) (dmsk cs_R cs_L)"
    unfolding dmsk_def by (rule dmsk_args_dargs[OF s_R s_L sub])
  have lf: "length (filter id (dmsk cs_R cs_L)) = length cs_L"
    unfolding dmsk_def by (rule length_filter_mrg_left_key[OF s_R s_L sub])
  have ln: "length (dmsk cs_R cs_L) = length cs_R"
    unfolding dmsk_def by (rule length_mrg_left_key[OF s_R s_L sub])
  have lw: "\<And>y. y \<in> dtabc n cs_L l \<Longrightarrow> dnarrow_tuple (dmsk cs_R cs_L) y"
    unfolding lf using dwf_tuple_dtabc[OF s_L b_L tl] by (simp add: dwf_tuple_def)
  have rw: "\<And>x. x \<in> dtabc n cs_R r \<Longrightarrow> length x = length (dmsk cs_R cs_L)"
    unfolding ln using dwf_tuple_dtabc[OF s_R b tr] by (simp add: dwf_tuple_def)
  have wi: "dwiden (dmsk cs_R cs_L) ` dtabc n cs_L l = dtabc n cs_R l"
    unfolding dmsk_def by (rule dwiden_image_dtabc[OF s_R s_L sub b tl])
  have u0: "update_mmtaux (dargs cs_R cs_L args) nt (dwiden (dmsk cs_R cs_L) ` dtabc n cs_L l)
        (dtabc n cs_R r) (tmm daux)
      = tmm (gupdate_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_L l) (dtabc n cs_R r) daux)"
    by (rule update_mmtaux_tmm'[OF dm vn]) (use lw rw in auto)
  have u: "update_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_R l) (dtabc n cs_R r) (tmm daux)
      = tmm (gupdate_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_L l) (dtabc n cs_R r) daux)"
    using u0 by (simp only: wi)
  have tl': "table (args_n (dargs cs_R cs_L args)) (args_L (dargs cs_R cs_L args))
      (dtabc n cs_R l)"
    using table_dtabc_cpos[OF s_R b sub tl] by simp
  have tr': "table (args_n (dargs cs_R cs_L args)) (args_R (dargs cs_R cs_L args))
      (dtabc n cs_R r)"
    using table_dtabc_cpos[OF s_R b order.refl tr] by (simp add: cpos_all)
  have tn: "tnar (dmsk cs_R cs_L)
      (gupdate_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_L l) (dtabc n cs_R r) daux)"
    by (rule gupdate_mmtaux_tnar[OF vn lw rw])
  have fx: "tfix (gupdate_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_L l) (dtabc n cs_R r) daux)"
  proof (rule gupdate_mmtaux_tfix[OF vn vf])
    show "mem (args_ivl (dargs cs_R cs_L args)) 0 \<or>
        (\<forall>y \<in> dtabc n cs_L l. dwiden (dmsk cs_R cs_L) y = y)"
    proof (cases "mem (args_ivl args) 0")
      case False
      then have e: "cs_L = cs_R" using ok by (simp add: tok_def)
      have ly: "\<And>y. y \<in> dtabc n cs_L l \<Longrightarrow> length y = length (dmsk cs_R cs_L)"
        using lw lf ln e by simp
      show ?thesis using ly dmsk_all[OF s_R] by (auto simp: e intro: dwiden_all)
    qed simp
  qed
  have "valid_mmtaux (dargs cs_R cs_L args) nt
      (update_mmtaux (dargs cs_R cs_L args) nt (dtabc n cs_R l) (dtabc n cs_R r) (tmm daux))
      (filter (\<lambda>(t, _). memR (args_ivl (dargs cs_R cs_L args)) (nt - t))
         (dauxlist3 n cs_R auxlist) @ [(nt, dtabc n cs_R l, dtabc n cs_R r)])"
    by (rule valid_update_mmtaux[OF nt tl' tr' d])
  then show ?thesis
    using w tl tr tn fx
    by (auto simp: dtaux_def dauxlist3_filter_append u)
qed

lemma dtaux_result:
  assumes v: "dtaux n cs_R cs_L args cur daux auxlist" and ne: "\<not> gmmtaux_empty daux"
    and s: "sorted_wrt (<) cs_R" and b: "\<forall>c \<in> set cs_R. c < n" and sub: "set cs_L \<subseteq> set cs_R"
    and an: "args_n args = n" and aL: "args_L args = set cs_L" and aR: "args_R args = set cs_R"
  shows "gresult_mmtaux (dargs cs_R cs_L args) daux
       = dtabc n cs_R (snd (trigger_results args cur auxlist))"
proof -
  have w: "\<forall>(t, l, r) \<in> set auxlist. table n (set cs_L) l \<and> table n (set cs_R) r"
    and vf: "tfix daux"
    and d: "valid_mmtaux (dargs cs_R cs_L args) cur (tmm daux) (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: dtaux_def)
  have res: "result_mmtaux (dargs cs_R cs_L args) (tmm daux)
      = trigger_results (dargs cs_R cs_L args) cur (dauxlist3 n cs_R auxlist)"
    by (rule valid_result_mmtaux[OF d])
  show ?thesis
    unfolding result_mmtaux_tmm[OF vf ne, symmetric] res
    by (rule dtabc_trigger_results[OF s b sub an aL aR w])
qed

text \<open>With an empty window the kernel's read is the full table, and that is decided by the
  timestamps alone, so it is the same read at the node's own frame.\<close>

lemma dtaux_window:
  assumes v: "dtaux n cs_R cs_L args cur daux auxlist"
  shows "gmmtaux_empty daux \<longleftrightarrow> filter (\<lambda>(t, _). mem (args_ivl args) (cur - t)) auxlist = []"
proof -
  have d: "valid_mmtaux (dargs cs_R cs_L args) cur (tmm daux) (dauxlist3 n cs_R auxlist)"
    using v by (auto simp: dtaux_def)
  obtain cur' idx_next idx_mid idx_oldest msk data_prev data_in tio keys tsh hs ss
    where ax: "daux = (cur', idx_next, idx_mid, idx_oldest, msk, data_prev, data_in, tio, keys,
      tsh, hs, ss)"
    by (metis surj_pair)
  have mp: "map (\<lambda>(t, l, r). (t, r))
      (auxlist_data_in (dargs cs_R cs_L args) cur (dauxlist3 n cs_R auxlist))
    = linearize data_in"
    using d unfolding ax tmm.simps valid_mmtaux_def prod.case by blast
  have adi: "auxlist_data_in (dargs cs_R cs_L args) cur (dauxlist3 n cs_R auxlist)
      = dauxlist3 n cs_R (filter (\<lambda>(t, _). mem (args_ivl args) (cur - t)) auxlist)"
    by (simp add: auxlist_data_in_def dauxlist3_def filter_map split_def comp_def)
  show ?thesis using mp unfolding adi ax
    by (auto simp: gmmtaux_empty_def Queue.is_empty_alt dauxlist3_def)
qed

lemma dtaux_result_empty:
  assumes v: "dtaux n cs_R cs_L args cur daux auxlist" and e: "gmmtaux_empty daux"
  shows "trigger_results args cur auxlist = ({}, {replicate (args_n args) None})"
  using dtaux_window[OF v] e by (simp add: split_def)

(*<*)
end
(*>*)
