(*<*)
theory Since_Agg
  imports Window Frame_Aux Agg_Gen
begin
(*>*)

section \<open>The Since window with the aggregation fused in\<close>

text \<open>
  The kernel folds an aggregation over a Since into the Since node (@{const args_agg}) and its
  structure keeps the aggregate incrementally, in @{typ aggaux}: a count, a sum or a rank tree
  per group, updated as tuples enter and leave.  The executable evaluator unfuses the two, a
  @{text EAgg} node over a @{text ESince} whose window reports the plain union, and recomputes
  the aggregate from the union at every time point.  This theory fuses them again for the
  window: the count set already makes a tuple's entry into and exit from the union explicit, and
  those are exactly the events the kernel's incremental structure takes.

  The executable aggregation @{const uagg} is stated on the window's own tuples, which list the
  operand's columns in ascending order.  The kernel's @{const eval_agg}, and hence
  @{const valid_maggaux}, reads its tuples over an arbitrary column list, so the window's tuples
  are themselves tuples of the kernel at the ascending column list of the operand, and the first
  lemma below says that the executable aggregation is the kernel's there, with the result column
  moved from the front, where the kernel puts it, to its place in the ascending order -- an
  instance of @{thm [source] uagg_eval_agg}.
\<close>

subsection \<open>The executable aggregation as the kernel's\<close>

text \<open>The parameters of a @{text EAgg} node: @{text g0}, the operator, the term, the number of
  bound variables and the position of the result column.\<close>

type_synonym eaggp = "bool \<times> ty Formula.agg_op \<times> Formula.trm \<times> nat \<times> nat"

fun eagg_p :: "eaggp \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eagg_p (g0, \<omega>, f, k, pos) = uagg g0 \<omega> f k pos"

text \<open>What the parameters must satisfy at a window over tuples of width @{text w}.\<close>

fun eagg_ok :: "eaggp \<Rightarrow> nat \<Rightarrow> bool" where
  "eagg_ok (g0, \<omega>, f, k, pos) w \<longleftrightarrow>
     k \<le> w \<and> pos \<le> w - k \<and> Formula.fv_trm f \<subseteq> {0..<w} \<and> (g0 \<longrightarrow> w = k)"

text \<open>The kernel's frame: the group columns are all of the result's columns but the result
  column, and the term reads the tuple at those columns.\<close>

fun eagg_gcols :: "eaggp \<Rightarrow> nat \<Rightarrow> cols" where
  "eagg_gcols (g0, \<omega>, f, k, pos) w = [0..<pos] @ [Suc pos..<Suc (w - k)]"

text \<open>The parameters the compiler builds from a fused node's aggregation are well formed at the
  width of the node's operand.\<close>

lemma ins_pos_le: "ins_pos cs y \<le> length cs"
  by (simp add: ins_pos_def)

lemma eagg_ok_agg:
  assumes "Formula.fv_trm f \<subseteq> set (agg_cols k g)" and "g0 \<Longrightarrow> g = []"
  shows "eagg_ok (g0, \<omega>, reindex_trm (agg_cols k g) f, k, ins_pos g y) (length (agg_cols k g))"
  using fv_reindex_trm[OF assms(1)] assms(2) ins_pos_le[of g y] by auto

fun shift_trm :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
  "shift_trm b (Formula.Var x) = Formula.Var (if x < b then x else Suc x)"
| "shift_trm b (Formula.Const c) = Formula.Const c"
| "shift_trm b (Formula.Plus a c) = Formula.Plus (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.Minus a c) = Formula.Minus (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.UMinus a) = Formula.UMinus (shift_trm b a)"
| "shift_trm b (Formula.Mult a c) = Formula.Mult (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.Div a c) = Formula.Div (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.Mod a c) = Formula.Mod (shift_trm b a) (shift_trm b c)"
| "shift_trm b (Formula.F2i a) = Formula.F2i (shift_trm b a)"
| "shift_trm b (Formula.I2f a) = Formula.I2f (shift_trm b a)"

fun eagg_ccols :: "eaggp \<Rightarrow> nat \<Rightarrow> cols" where
  "eagg_ccols (g0, \<omega>, f, k, pos) w = agg_cols k (eagg_gcols (g0, \<omega>, f, k, pos) w)"

fun eagg_args :: "eaggp \<Rightarrow> nat \<Rightarrow> aggargs" where
  "eagg_args (g0, \<omega>, f, k, pos) w =
     \<lparr>aggargs_cols = eagg_ccols (g0, \<omega>, f, k, pos) w, aggargs_n = Suc (w - k),
      aggargs_g0 = g0, aggargs_y = pos, aggargs_\<omega> = \<omega>, aggargs_tys = replicate k Formula.TInt,
      aggargs_f = shift_trm (k + pos) f\<rparr>"

lemma fv_shift_trm:
  "Formula.fv_trm (shift_trm b f) = (\<lambda>x. if x < b then x else Suc x) ` Formula.fv_trm f"
  by (induct f) auto

lemma map_add_upt': "map (\<lambda>c. c + k) [a..<b] = [a + k..<b + k]"
  by (induct b) auto

lemma upt_split: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  using upt_add_eq_append[of a b "c - b"] by simp

lemma agg_cols_eagg_gcols:
  assumes "k \<le> w" and "pos \<le> w - k"
  shows "agg_cols k (eagg_gcols (g0, \<omega>, f, k, pos) w) = [0..<k + pos] @ [Suc (k + pos)..<Suc w]"
proof -
  have 1: "map (\<lambda>c. c + k) [0..<pos] = [k..<k + pos]" by (simp add: map_add_upt' add.commute)
  have 2: "map (\<lambda>c. c + k) [Suc pos..<Suc (w - k)] = [Suc (k + pos)..<Suc w]"
    using assms by (simp add: map_add_upt' add.commute del: upt_Suc)
  have 3: "[0..<k] @ [k..<k + pos] = [0..<k + pos]" by (rule upt_split) simp_all
  show ?thesis unfolding eagg_gcols.simps map_append 1 2 append_assoc[symmetric] 3 ..
qed

lemma col_pos_append:
  "col_pos (xs @ ys) c = (if c \<in> set xs then col_pos xs c else length xs + col_pos ys c)"
  by (induct xs) auto

lemma col_pos_upt: "a \<le> c \<Longrightarrow> c < b \<Longrightarrow> col_pos [a..<b] c = c - a"
  by (induct "b - a" arbitrary: a) (auto simp: upt_conv_Cons)

lemma col_pos_shift:
  "x < w \<Longrightarrow> b \<le> w \<Longrightarrow>
   col_pos ([0..<b] @ [Suc b..<Suc w]) (if x < b then x else Suc x) = x"
  by (auto simp: col_pos_append col_pos_upt)

lemma reindex_shift_trm:
  "Formula.fv_trm f \<subseteq> {0..<w} \<Longrightarrow> b \<le> w \<Longrightarrow>
   reindex_trm ([0..<b] @ [Suc b..<Suc w]) (shift_trm b f) = f"
  by (induct f) (simp_all add: col_pos_shift del: upt_Suc)

lemma ins_pos_eagg_gcols: "ins_pos ([0..<pos] @ [Suc pos..<Suc m]) pos = pos"
proof -
  have "filter (\<lambda>c. c < pos) [0..<pos] = [0..<pos]" by (rule filter_True) simp
  moreover have "filter (\<lambda>c. c < pos) [Suc pos..<Suc m] = []"
    by (rule filter_False) (auto simp del: upt_Suc)
  ultimately show ?thesis by (simp add: ins_pos_def del: upt_Suc)
qed

lemma sorted_wrt_eagg_gcols: "sorted_wrt (<) ([0..<pos] @ [Suc pos..<Suc m])"
  by (auto simp: sorted_wrt_append simp del: upt_Suc)

lemma merge_cols_eagg_gcols:
  assumes "pos \<le> m"
  shows "merge_cols ([0..<pos] @ [Suc pos..<Suc m]) [pos] = [0..<Suc m]"
proof -
  have nin: "pos \<notin> set ([0..<pos] @ [Suc pos..<Suc m])" by (auto simp del: upt_Suc)
  have "[0..<pos] @ pos # [Suc pos..<Suc m] = [0..<pos] @ [pos..<Suc m]"
    using assms by (simp add: upt_conv_Cons del: upt_Suc)
  also have "\<dots> = [0..<Suc m]" using assms by (intro upt_split) simp_all
  finally show ?thesis
    unfolding merge_cols_single[OF sorted_wrt_eagg_gcols nin] ins_pos_eagg_gcols
    by (simp del: upt_Suc)
qed

lemma shift_cols_agg_cols: "shift_cols k (agg_cols k G) = G"
proof -
  have "filter (\<lambda>x. k \<le> x) (agg_cols k G) = map (\<lambda>c. c + k) G"
    by (auto simp: filter_empty_conv intro: filter_True)
  then show ?thesis by (simp add: shift_cols_def comp_def)
qed

lemma eagg_ccols_props:
  assumes "eagg_ok p w"
  shows "sorted_wrt (<) (eagg_ccols p w)" "distinct (eagg_ccols p w)"
    "length (eagg_ccols p w) = w"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p)
  have kw: "k \<le> w" and pw: "pos \<le> w - k" using assms by (auto simp: p)
  have kpw: "k + pos \<le> w" using kw pw by arith
  have cc: "eagg_ccols p w = [0..<k + pos] @ [Suc (k + pos)..<Suc w]"
    unfolding p eagg_ccols.simps by (rule agg_cols_eagg_gcols[OF kw pw])
  show s: "sorted_wrt (<) (eagg_ccols p w)" unfolding cc
    by (auto simp: sorted_wrt_append simp del: upt_Suc)
  show "distinct (eagg_ccols p w)" using s by (simp add: strict_sorted_iff)
  show "length (eagg_ccols p w) = w" unfolding cc using kpw by (simp del: upt_Suc)
qed

abbreviation ewf_table :: "nat \<Rightarrow> 'b list set \<Rightarrow> bool" where
  "ewf_table w T \<equiv> \<forall>x \<in> T. length x = w"

text \<open>The kernel reads a window's tuple at the frame: its group key is the tuple's suffix after
  the bound columns, and the shifted term evaluates to the term on the tuple.\<close>

lemma agg_key_dagg:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and t: "length t = w"
  shows "agg_key k (eagg_ccols (g0, \<omega>, f, k, pos) w) t = drop k t"
proof -
  let ?cc = "eagg_ccols (g0, \<omega>, f, k, pos) w"
  note P = eagg_ccols_props[OF ok]
  have kw: "k \<le> w" using ok by simp
  have f: "filter (\<lambda>x. k \<le> x) ?cc = drop k ?cc"
    by (auto simp: filter_empty_conv intro: filter_True)
  have wt: "wf_tuple ?cc t" using t P(3) by (simp add: wf_tuple_def)
  show ?thesis unfolding agg_key_def f
  proof (rule nth_equalityI)
    show "length (restrict (drop k ?cc) ?cc t) = length (drop k t)" using P(3) t by simp
  next
    fix i assume "i < length (restrict (drop k ?cc) ?cc t)"
    then have i: "i < w - k" using P(3) by simp
    have ki: "k + i < length ?cc" using i kw P(3) by linarith
    have "restrict (drop k ?cc) ?cc t ! i = tup_get ?cc t (drop k ?cc ! i)"
      by (rule nth_restrict) (use i P(3) in simp)
    also have "drop k ?cc ! i = ?cc ! (k + i)" by (rule nth_drop) (use kw P(3) in simp)
    also have "tup_get ?cc t (?cc ! (k + i)) = t ! (k + i)" by (rule tup_get_nth[OF P(2) wt ki])
    also have "\<dots> = drop k t ! i" using kw t by simp
    finally show "restrict (drop k ?cc) ?cc t ! i = drop k t ! i" .
  qed
qed

lemma meval_shift_dagg:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and t: "length t = w"
  shows "meval_trm (eagg_ccols (g0, \<omega>, f, k, pos) w) (shift_trm (k + pos) f) t = umeval_trm f t"
proof -
  let ?cc = "eagg_ccols (g0, \<omega>, f, k, pos) w"
  note P = eagg_ccols_props[OF ok]
  have kw: "k \<le> w" and pw: "pos \<le> w - k" and fv: "Formula.fv_trm f \<subseteq> {0..<w}" using ok by auto
  have kpw: "k + pos \<le> w" using kw pw by arith
  have cc: "?cc = [0..<k + pos] @ [Suc (k + pos)..<Suc w]"
    unfolding eagg_ccols.simps by (rule agg_cols_eagg_gcols[OF kw pw])
  have fv': "Formula.fv_trm (shift_trm (k + pos) f) \<subseteq> set ?cc"
    unfolding cc fv_shift_trm using fv kpw by (auto simp del: upt_Suc)
  have r: "reindex_trm ?cc (shift_trm (k + pos) f) = f"
    unfolding cc by (rule reindex_shift_trm[OF fv kpw])
  have i: "restrict ?cc ?cc t = t" using t P by (simp add: restrict_idle wf_tuple_def)
  show ?thesis using umeval_trm_reindex[OF fv', of ?cc t] unfolding r i ..
qed

text \<open>The kernel puts the result column in front of the group key; the executable order puts it at
  its place among the group's columns.\<close>

definition slot :: "nat \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "slot p x = take p (tl x) @ hd x # drop p (tl x)"

lemma restrict_slot:
  assumes g: "length g = m" and p: "p \<le> m"
  shows "restrict [0..<Suc m] (p # [0..<p] @ [Suc p..<Suc m]) (v # g) = slot p (v # g)"
proof (rule nth_equalityI)
  let ?G = "p # [0..<p] @ [Suc p..<Suc m]"
  have d: "distinct ?G" by (auto simp del: upt_Suc)
  have l: "length ?G = Suc m" using p by (simp del: upt_Suc)
  have wt: "wf_tuple ?G (v # g)" using g l by (simp add: wf_tuple_def del: upt_Suc)
  show "length (restrict [0..<Suc m] ?G (v # g)) = length (slot p (v # g))"
    using g p by (simp add: slot_def del: upt_Suc)
  fix i assume "i < length (restrict [0..<Suc m] ?G (v # g))"
  then have i: "i < Suc m" by (simp del: upt_Suc)
  have nr: "restrict [0..<Suc m] ?G (v # g) ! i = tup_get ?G (v # g) i"
    using i by (simp add: nth_restrict del: upt_Suc)
  consider (eq) "i = p" | (lt) "i < p" | (gt) "p < i" by linarith
  then show "restrict [0..<Suc m] ?G (v # g) ! i = slot p (v # g) ! i"
  proof cases
    case eq
    have "?G ! 0 = i" using eq by simp
    then show ?thesis unfolding nr using tup_get_nth[OF d wt, of 0] l eq g p
      by (simp add: slot_def nth_append del: upt_Suc)
  next
    case lt
    have "?G ! Suc i = i" using lt by (simp add: nth_append del: upt_Suc)
    then show ?thesis unfolding nr using tup_get_nth[OF d wt, of "Suc i"] l lt g p i
      by (simp add: slot_def nth_append del: upt_Suc)
  next
    case gt
    have "?G ! i = i" using gt i p
      by (cases i) (auto simp: nth_append simp del: upt_Suc)
    then show ?thesis unfolding nr using tup_get_nth[OF d wt, of i] l gt g p i
      by (cases i) (auto simp: slot_def nth_append nth_Cons' min_def simp del: upt_Suc)
  qed
qed

lemma length_filter_eagg_ccols:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w"
  shows "length (filter (\<lambda>x. k \<le> x) (eagg_ccols (g0, \<omega>, f, k, pos) w)) = w - k"
proof -
  have "filter (\<lambda>x. k \<le> x) (eagg_ccols (g0, \<omega>, f, k, pos) w) = drop k (eagg_ccols (g0, \<omega>, f, k, pos) w)"
    by (auto simp: filter_empty_conv intro: filter_True)
  then show ?thesis using eagg_ccols_props(3)[OF ok] by simp
qed

lemma eval_agg_shape:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w"
    and x: "x \<in> eval_agg (eagg_ccols (g0, \<omega>, f, k, pos) w) g0 \<omega> (replicate k Formula.TInt) f' D"
  shows "\<exists>v g. x = v # g \<and> length g = w - k"
proof (cases "g0 \<and> D = empty_table")
  case True
  then have "w - k = 0" using ok by simp
  then show ?thesis using x True by (simp add: eval_agg_def singleton_table_def)
next
  case False
  let ?cc = "eagg_ccols (g0, \<omega>, f, k, pos) w"
  obtain d v where "x = v # agg_key k ?cc d"
    using x False by (auto simp: eval_agg_def Let_def simp del: eagg_ccols.simps)
  moreover have "length (agg_key k ?cc d) = w - k"
    using length_filter_eagg_ccols[OF ok] by (simp add: agg_key_def del: eagg_ccols.simps)
  ultimately show ?thesis by blast
qed

text \<open>The executable aggregation is the kernel's aggregation at the ascending frame, with the result
  column moved into place.\<close>

lemma eagg_p_eval_aggargs:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and D: "ewf_table w D"
  shows "eagg_p (g0, \<omega>, f, k, pos) D = slot pos ` eval_aggargs (eagg_args (g0, \<omega>, f, k, pos) w) D"
proof -
  let ?p = "(g0, \<omega>, f, k, pos)"
  define G where "G = eagg_gcols ?p w"
  define cc where "cc = agg_cols k G"
  have kw: "k \<le> w" and pw: "pos \<le> w - k" and fv: "Formula.fv_trm f \<subseteq> {0..<w}"
    and g0: "g0 \<Longrightarrow> w = k" using ok by auto
  have kpw: "k + pos \<le> w" using kw pw by arith
  have ccd: "cc = eagg_ccols ?p w" by (simp add: cc_def G_def)
  note P = eagg_ccols_props[OF ok, folded ccd]
  have ccE: "cc = [0..<k + pos] @ [Suc (k + pos)..<Suc w]"
    unfolding cc_def G_def by (rule agg_cols_eagg_gcols[OF kw pw])
  have GE: "G = [0..<pos] @ [Suc pos..<Suc (w - k)]" by (simp add: G_def)
  have fr: "eframe cc (agg_cols k G)" using P by (simp add: eframe_def cc_def[symmetric])
  have tb: "table cc D" using D P(3) by (simp add: table_def wf_tuple_def)
  have yg: "pos \<notin> set G" unfolding GE by (auto simp del: upt_Suc)
  have fv': "Formula.fv_trm (shift_trm (k + pos) f) \<subseteq> set cc"
    unfolding ccE fv_shift_trm using fv kpw by (auto simp del: upt_Suc)
  have g0': "g0 \<Longrightarrow> G = []" unfolding GE using g0 pw by simp
  note uea = uagg_eval_agg[of cc "replicate k Formula.TInt" G D "shift_trm (k + pos) f" pos g0 \<omega>,
      simplified length_replicate, OF fr tb fv' yg g0']
  have 1: "reindex_trm (agg_cols k G) (shift_trm (k + pos) f) = f"
    unfolding cc_def[symmetric] ccE by (rule reindex_shift_trm[OF fv kpw])
  have 2: "ins_pos G pos = pos" unfolding GE by (rule ins_pos_eagg_gcols)
  have 3: "etabc cc (agg_cols k G) D = D"
    using tb P(2) unfolding cc_def[symmetric]
    by (force simp: etabc_def table_def restrict_idle)
  have 4: "shift_cols k cc = G" unfolding cc_def by (rule shift_cols_agg_cols)
  have 5: "merge_cols G [pos] = [0..<Suc (w - k)]" unfolding GE by (rule merge_cols_eagg_gcols[OF pw])
  define E where "E = eval_agg cc g0 \<omega> (replicate k Formula.TInt) (shift_trm (k + pos) f) D"
  have main: "uagg g0 \<omega> f k pos D = etabc (pos # G) [0..<Suc (w - k)] E"
    using uea unfolding 1 2 3 4 5 E_def .
  have "etabc (pos # G) [0..<Suc (w - k)] E = slot pos ` E"
    unfolding etabc_def
  proof (rule image_cong[OF refl])
    fix x assume "x \<in> E"
    then obtain v g where x: "x = v # g" and lg: "length g = w - k"
      using eval_agg_shape[OF ok, of x] unfolding E_def ccd by blast
    show "restrict [0..<Suc (w - k)] (pos # G) x = slot pos x"
      unfolding x GE by (rule restrict_slot[OF lg pw])
  qed
  then show ?thesis using main unfolding E_def ccd
    by (simp add: eval_aggargs_def del: eagg_ccols.simps)
qed

subsection \<open>The aggregate alongside the count set\<close>

text \<open>
  The count set makes a tuple's entry into and exit from the window's union explicit: a table
  added contributes the tuples not yet in the union, a table removed takes out the tuples it was
  the last to hold.  Those are the insertions and deletions the kernel's incremental structure
  takes.  The structure is optional, as in the kernel: @{const None} once an operation reports
  that it cannot maintain the aggregate, and then the result is computed from the union
  directly.  The kernel's operations are named @{text kag_} here: the window keeps the
  structure of the next subsection, which they serve as the specification of.
\<close>

definition cnt_enter :: "event_data table \<Rightarrow> cntset \<Rightarrow> event_data table" where
  "cnt_enter T cc = T - snd cc"

definition cnt_leave :: "event_data table \<Rightarrow> cntset \<Rightarrow> event_data table" where
  "cnt_leave T cc = Set.filter (\<lambda>x. Mapping.lookup (fst cc) x = Some 1) T"

definition kag_init :: "eaggp \<Rightarrow> nat \<Rightarrow> aggaux option" where
  "kag_init p w = init_maggaux' (eagg_args p w)"

definition kag_ins :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "kag_ins p w T cc ax = insert_maggaux' (eagg_args p w) (cnt_enter T cc) ax"

definition kag_del :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "kag_del p w T cc ax = delete_maggaux' (eagg_args p w) (cnt_leave T cc) ax"

definition kag_inv :: "eaggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> bool" where
  "kag_inv p w cc ax \<longleftrightarrow> valid_maggaux' (eagg_args p w) ax (snd cc)"

lemma cnt_rep_snd_add: "cnt_rep f cc \<Longrightarrow> finite T \<Longrightarrow> snd (cnt_add T cc) = snd cc \<union> T"
  using cnt_rep_add[of f cc T] unfolding cnt_rep_def by auto

lemma cnt_leave_rep: "cnt_rep f cc \<Longrightarrow> cnt_leave T cc = {x \<in> T. f x = 1}"
  unfolding cnt_leave_def cnt_rep_def by (auto split: if_splits)

lemma cnt_rep_snd_del: "cnt_rep f cc \<Longrightarrow> finite T \<Longrightarrow> snd (cnt_del T cc) = snd cc - cnt_leave T cc"
  using cnt_rep_del[of f cc T] cnt_leave_rep[of f cc T] unfolding cnt_rep_def by auto

lemma cnt_leave_sub: assumes "cnt_rep f cc" shows "cnt_leave T cc \<subseteq> snd cc"
  using assms unfolding cnt_leave_rep[OF assms] cnt_rep_def by auto

lemma kag_inv_init: "kag_inv p w (Mapping.empty, {}) (kag_init p w)"
  using valid_init_maggaux[of "eagg_args p w"]
  by (auto simp: kag_inv_def kag_init_def split: prod.splits)

lemma kag_inv_ins:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and inv: "kag_inv p w cc ax"
  shows "kag_inv p w (cnt_add T cc) (kag_ins p w T cc ax)"
proof (cases ax)
  case None
  then show ?thesis by (simp add: kag_inv_def kag_ins_def)
next
  case (Some a)
  let ?X = "snd cc" and ?Y = "cnt_enter T cc"
  have v: "valid_maggaux (eagg_args p w) a ?X" using inv by (simp add: kag_inv_def Some)
  have fY: "finite ?Y" using fT by (simp add: cnt_enter_def)
  have dj: "?X \<inter> ?Y = {}" by (auto simp: cnt_enter_def)
  have XY: "?X \<union> ?Y = snd (cnt_add T cc)"
    unfolding cnt_rep_snd_add[OF cr fT] cnt_enter_def by auto
  show ?thesis
    using valid_insert_maggaux[OF v fY dj] unfolding XY
    by (auto simp: kag_inv_def kag_ins_def Some split: prod.splits)
qed

lemma kag_inv_del:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and inv: "kag_inv p w cc ax"
  shows "kag_inv p w (cnt_del T cc) (kag_del p w T cc ax)"
proof (cases ax)
  case None
  then show ?thesis by (simp add: kag_inv_def kag_del_def)
next
  case (Some a)
  let ?X = "snd cc" and ?Y = "cnt_leave T cc"
  have v: "valid_maggaux (eagg_args p w) a ?X" using inv by (simp add: kag_inv_def Some)
  have sub: "?Y \<subseteq> ?X" by (rule cnt_leave_sub[OF cr])
  have XY: "?X - ?Y = snd (cnt_del T cc)" unfolding cnt_rep_snd_del[OF cr fT] ..
  show ?thesis
    using valid_delete_maggaux[OF v sub] unfolding XY
    by (auto simp: kag_inv_def kag_del_def Some split: prod.splits)
qed

subsection \<open>The aggregate over the window's own tuples\<close>

text \<open>
  The kernel's structure keys a group by @{const agg_key}, which at the ascending frame is the
  tuple's suffix after the bound columns, and reads the value by the shifted term, which there
  is the term itself.  The structure @{typ "event_data gagg"} of
  @{theory MFODL_Monitor_Exec.Agg_Gen} reads both off the tuple directly, and
  @{text Rk} maps it to the kernel's.  The kernel's steps are the steps below under
  @{text Rk}, and so are the folds, the initial structure and the result.
\<close>

fun Rk :: "event_data gagg \<Rightarrow> aggaux" where
  "Rk (GCnt m) = CntAux m"
| "Rk (GSum m) = SumAux m"
| "Rk (GRank m ty) = RankAux (m, ty)"

lemma insert_cnt_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
  shows "insert_cnt args t = gi_cnt k t"
  using assms by (intro ext) (auto simp: Let_def)

lemma delete_cnt_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
  shows "delete_cnt args t = gd_cnt k t"
  using assms by (intro ext) (auto simp: Let_def)

lemma insert_sum_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "insert_sum args t = gi_sum k ev t"
  using assms by (intro ext) (auto simp: Let_def)

lemma delete_sum_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "delete_sum args t = gd_sum k ev t"
  using assms by (intro ext) (auto simp: Let_def)

lemma insert_rank_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "insert_rank args ty t = gi_rank k ev ty t"
  using assms by (intro ext) (auto simp: Let_def)

lemma delete_rank_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "delete_rank args ty t = gd_rank k ev ty t"
  using assms by (intro ext) (auto simp: Let_def)

lemma fold_set_list:
  assumes F: "comp_fun_commute_on UNIV F" and d: "distinct xs"
  shows "Finite_Set.fold F b (set xs) = fold F xs b"
proof -
  have "Finite_Set.fold F b (set xs) = fold F (remdups xs) b"
    by (rule comp_fun_commute_on.fold_set_fold_remdups[OF F]) simp
  then show ?thesis by (simp only: distinct_remdups_id[OF d])
qed

lemma cfc_insert_cnt: "comp_fun_commute_on UNIV (insert_cnt args)"
  using insert_cnt_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_insert_sum: "comp_fun_commute_on UNIV (insert_sum args)"
  using insert_sum_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_insert_rank: "comp_fun_commute_on UNIV (insert_rank args ty)"
  using insert_rank_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_cnt: "comp_fun_commute_on UNIV (delete_cnt args)"
  using delete_cnt_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_sum: "comp_fun_commute_on UNIV (delete_sum args)"
  using delete_sum_comm by unfold_locales (auto simp: fun_eq_iff)
lemma cfc_delete_rank: "comp_fun_commute_on UNIV (delete_rank args ty)"
  using delete_rank_comm by unfold_locales (auto simp: fun_eq_iff)

lemma insert_maggaux'_Rk_gen:
  assumes d: "distinct xs"
    and tup: "\<And>t. t \<in> set xs \<Longrightarrow> agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t \<and>
       meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "insert_maggaux' args (set xs) (map_option Rk ax) = map_option Rk (gins k ev xs ax)"
proof -
  have c: "fold (insert_cnt args) xs s' = fold (gi_cnt k) xs s'" for s'
    by (rule fold_cong) (simp_all add: insert_cnt_Rk tup)
  have sm: "fold (insert_sum args) xs s' = fold (gi_sum k ev) xs s'" for s'
    by (rule fold_cong) (simp_all add: insert_sum_Rk tup)
  have r: "fold (insert_rank args ty) xs s' = fold (gi_rank k ev ty) xs s'" for ty s'
    by (rule fold_cong) (simp_all add: insert_rank_Rk tup)
  have fc: "fold (gstep_ins k ev) xs (Some (GCnt m)) =
      (case fold (gi_cnt k) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GCnt m') else None)" for m
    by (rule fold_flag) (simp_all add: gstep_ins_def)
  have fs: "fold (gstep_ins k ev) xs (Some (GSum m)) =
      (case fold (gi_sum k ev) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GSum m') else None)" for m
    by (rule fold_flag) (simp_all add: gstep_ins_def)
  have fr: "fold (gstep_ins k ev) xs (Some (GRank m ty)) =
      (case fold (gi_rank k ev ty) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GRank m' ty) else None)"
    for m ty
    by (rule fold_flag[where C = "\<lambda>m. GRank m ty"]) (simp_all add: gstep_ins_def)
  show ?thesis
  proof (cases ax)
    case (Some a)
    show ?thesis
    proof (cases a)
      case (GCnt m)
      show ?thesis
        unfolding Some GCnt gins_def fc
        by (simp add: fold_set_list[OF cfc_insert_cnt d] c split: prod.splits)
    next
      case (GSum m)
      show ?thesis
        unfolding Some GSum gins_def fs
        by (simp add: fold_set_list[OF cfc_insert_sum d] sm split: prod.splits)
    next
      case (GRank m ty)
      show ?thesis
        unfolding Some GRank gins_def fr
        by (simp add: fold_set_list[OF cfc_insert_rank d] r split: prod.splits)
    qed
  qed simp
qed

lemma delete_maggaux'_Rk_gen:
  assumes d: "distinct xs"
    and tup: "\<And>t. t \<in> set xs \<Longrightarrow> agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t \<and>
       meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "delete_maggaux' args (set xs) (map_option Rk ax) = map_option Rk (gdel k ev xs ax)"
proof -
  have c: "fold (delete_cnt args) xs s' = fold (gd_cnt k) xs s'" for s'
    by (rule fold_cong) (simp_all add: delete_cnt_Rk tup)
  have sm: "fold (delete_sum args) xs s' = fold (gd_sum k ev) xs s'" for s'
    by (rule fold_cong) (simp_all add: delete_sum_Rk tup)
  have r: "fold (delete_rank args ty) xs s' = fold (gd_rank k ev ty) xs s'" for ty s'
    by (rule fold_cong) (simp_all add: delete_rank_Rk tup)
  have fc: "fold (gstep_del k ev) xs (Some (GCnt m)) =
      (case fold (gd_cnt k) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GCnt m') else None)" for m
    by (rule fold_flag) (simp_all add: gstep_del_def)
  have fs: "fold (gstep_del k ev) xs (Some (GSum m)) =
      (case fold (gd_sum k ev) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GSum m') else None)" for m
    by (rule fold_flag) (simp_all add: gstep_del_def)
  have fr: "fold (gstep_del k ev) xs (Some (GRank m ty)) =
      (case fold (gd_rank k ev ty) xs (True, m) of (v, m') \<Rightarrow> if v then Some (GRank m' ty) else None)"
    for m ty
    by (rule fold_flag[where C = "\<lambda>m. GRank m ty"]) (simp_all add: gstep_del_def)
  show ?thesis
  proof (cases ax)
    case (Some a)
    show ?thesis
    proof (cases a)
      case (GCnt m)
      show ?thesis
        unfolding Some GCnt gdel_def fc
        by (simp add: fold_set_list[OF cfc_delete_cnt d] c split: prod.splits)
    next
      case (GSum m)
      show ?thesis
        unfolding Some GSum gdel_def fs
        by (simp add: fold_set_list[OF cfc_delete_sum d] sm split: prod.splits)
    next
      case (GRank m ty)
      show ?thesis
        unfolding Some GRank gdel_def fr
        by (simp add: fold_set_list[OF cfc_delete_rank d] r split: prod.splits)
    qed
  qed simp
qed

lemma init_maggaux'_Rk:
  "init_maggaux' (eagg_args (g0, \<omega>, f, k, pos) w) = map_option Rk (ginit \<omega>)"
  by (simp add: ginit_def split: prod.splits Formula.agg_type.splits ty.splits)

lemma gmr_slot: "gmr p id f m = slot p ` get_map_result m f"
  unfolding gmr_def get_map_result_def image_image
  by (intro image_cong refl) (auto simp: slot_def Mapping.keys_dom_lookup split: option.splits)

lemma slot_singleton_table: "slot p ` singleton_table x = {[x]}"
  by (simp add: singleton_table_def slot_def)

lemma result_maggaux_Rk:
  assumes v: "valid_maggaux (eagg_args (g0, \<omega>, f, k, pos) w) (Rk a) X"
  shows "gres g0 \<omega> pos id a = slot pos ` result_maggaux (eagg_args (g0, \<omega>, f, k, pos) w) (Rk a)"
proof (cases a)
  case (GCnt m)
  then show ?thesis by (simp add: gmr_slot slot_singleton_table)
next
  case (GSum m)
  have "fst \<omega> = Formula.Agg_Sum \<or> fst \<omega> = Formula.Agg_Avg"
    using v by (simp add: GSum Let_def del: valid_aggmap_def)
  then show ?thesis using GSum by (auto simp: gmr_slot slot_singleton_table case_prod_beta)
next
  case (GRank m ty)
  have "fst \<omega> = Formula.Agg_Min \<or> fst \<omega> = Formula.Agg_Max \<or> fst \<omega> = Formula.Agg_Med"
    using v by (simp add: GRank Let_def del: valid_aggmap_def)
  then show ?thesis using GRank by (auto simp: gmr_slot slot_singleton_table)
qed

text \<open>The window's aggregate: the structure over the window's own tuples, fed with the sorted
  list of what enters and what leaves, and read with the result column filled in.  Its
  invariant is the kernel's, under @{const Rk}.\<close>

type_synonym egagg = "event_data gagg"

definition ag_init :: "eaggp \<Rightarrow> nat \<Rightarrow> 'b gagg option" where
  "ag_init p w = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ginit \<omega>)"

definition ag_ins :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> egagg option" where
  "ag_ins p w T cc ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gins k (umeval_trm f) (filter (\<lambda>t. t \<notin> snd cc) (csl T)) ax)"

definition ag_del :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> egagg option" where
  "ag_del p w T cc ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gdel k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup (fst cc) t = Some 1) (csl T)) ax)"

definition ag_res :: "eaggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> event_data table" where
  "ag_res p w cc ax = (case ax of
     None \<Rightarrow> eagg_p p (snd cc)
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gres g0 \<omega> pos id a))"

definition ag_inv :: "eaggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow> bool" where
  "ag_inv p w cc ax \<longleftrightarrow> kag_inv p w cc (map_option Rk ax)"

lemma csl_etuple:
  "finite (T :: event_data table) \<Longrightarrow> set (csl T) = T \<and> distinct (csl T)"
  using csorted_list_of_set_etuple by (simp add: csl_finite)

lemma ag_ins_Rk:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and fT: "finite T" and T: "ewf_table w T"
  shows "map_option Rk (ag_ins (g0, \<omega>, f, k, pos) w T cc ax)
    = kag_ins (g0, \<omega>, f, k, pos) w T cc (map_option Rk ax)"
proof -
  let ?xs = "filter (\<lambda>t. t \<notin> snd cc) (csl T)"
  have s: "set ?xs = cnt_enter T cc" and d: "distinct ?xs"
    using csl_etuple[OF fT] by (auto simp: cnt_enter_def)
  have tup: "t \<in> set ?xs \<Longrightarrow> agg_key (length (aggargs_tys (eagg_args (g0, \<omega>, f, k, pos) w)))
      (aggargs_cols (eagg_args (g0, \<omega>, f, k, pos) w)) t = drop k t \<and>
     meval_trm (aggargs_cols (eagg_args (g0, \<omega>, f, k, pos) w))
      (aggargs_f (eagg_args (g0, \<omega>, f, k, pos) w)) t = umeval_trm f t" for t
    using T csl_etuple[OF fT] agg_key_dagg[OF ok] meval_shift_dagg[OF ok]
    by (simp del: eagg_ccols.simps)
  show ?thesis
    unfolding ag_ins_def kag_ins_def prod.case
    using insert_maggaux'_Rk_gen[OF d tup, of ax] unfolding s by simp
qed

lemma ag_del_Rk:
  assumes ok: "eagg_ok (g0, \<omega>, f, k, pos) w" and fT: "finite T" and T: "ewf_table w T"
  shows "map_option Rk (ag_del (g0, \<omega>, f, k, pos) w T cc ax)
    = kag_del (g0, \<omega>, f, k, pos) w T cc (map_option Rk ax)"
proof -
  let ?xs = "filter (\<lambda>t. Mapping.lookup (fst cc) t = Some 1) (csl T)"
  have s: "set ?xs = cnt_leave T cc" and d: "distinct ?xs"
    using csl_etuple[OF fT] by (auto simp: cnt_leave_def)
  have tup: "t \<in> set ?xs \<Longrightarrow> agg_key (length (aggargs_tys (eagg_args (g0, \<omega>, f, k, pos) w)))
      (aggargs_cols (eagg_args (g0, \<omega>, f, k, pos) w)) t = drop k t \<and>
     meval_trm (aggargs_cols (eagg_args (g0, \<omega>, f, k, pos) w))
      (aggargs_f (eagg_args (g0, \<omega>, f, k, pos) w)) t = umeval_trm f t" for t
    using T csl_etuple[OF fT] agg_key_dagg[OF ok] meval_shift_dagg[OF ok]
    by (simp del: eagg_ccols.simps)
  show ?thesis
    unfolding ag_del_def kag_del_def prod.case
    using delete_maggaux'_Rk_gen[OF d tup, of ax] unfolding s by simp
qed

lemma ag_inv_init: "ag_inv p w (Mapping.empty, {}) (ag_init p w)"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p)
  show ?thesis
    using kag_inv_init[of p w] unfolding kag_init_def p init_maggaux'_Rk
    by (simp add: ag_inv_def ag_init_def)
qed

lemma ag_inv_ins:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and ok: "eagg_ok p w"
    and T: "ewf_table w T" and S: "ewf_table w (snd cc)" and inv: "ag_inv p w cc ax"
  shows "ag_inv p w (cnt_add T cc) (ag_ins p w T cc ax)"
proof -
  obtain g0 \<omega> f' k pos where p: "p = (g0, \<omega>, f', k, pos)" by (cases p)
  show ?thesis
    using kag_inv_ins[OF cr fT inv[unfolded ag_inv_def]]
    unfolding ag_inv_def p ag_ins_Rk[OF ok[unfolded p] fT T] .
qed

lemma ag_inv_del:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and ok: "eagg_ok p w"
    and T: "ewf_table w T" and S: "ewf_table w (snd cc)" and inv: "ag_inv p w cc ax"
  shows "ag_inv p w (cnt_del T cc) (ag_del p w T cc ax)"
proof -
  obtain g0 \<omega> f' k pos where p: "p = (g0, \<omega>, f', k, pos)" by (cases p)
  show ?thesis
    using kag_inv_del[OF cr fT inv[unfolded ag_inv_def]]
    unfolding ag_inv_def p ag_del_Rk[OF ok[unfolded p] fT T] .
qed

lemma ag_res_inv:
  assumes inv: "ag_inv p w cc ax" and ok: "eagg_ok p w" and S: "ewf_table w (snd cc)"
  shows "ag_res p w cc ax = eagg_p p (snd cc)"
proof (cases ax)
  case None
  then show ?thesis by (simp add: ag_res_def)
next
  case (Some a)
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p)
  have v: "valid_maggaux (eagg_args p w) (Rk a) (snd cc)"
    using inv by (simp add: ag_inv_def kag_inv_def Some)
  have "ag_res p w cc ax = slot pos ` result_maggaux (eagg_args p w) (Rk a)"
    using result_maggaux_Rk[OF v[unfolded p]] by (simp add: ag_res_def Some p)
  also have "\<dots> = slot pos ` eval_aggargs (eagg_args p w) (snd cc)"
    by (simp only: valid_result_maggaux[OF v])
  also have "\<dots> = eagg_p p (snd cc)"
    unfolding p by (rule eagg_p_eval_aggargs[OF ok[unfolded p] S, symmetric])
  finally show ?thesis .
qed

subsection \<open>The window, with the aggregate\<close>

text \<open>
  The window of @{theory MFODL_Monitor_Exec.Window} again, with the aggregate carried along:
  the two scans update it with every table that enters or leaves, the reset on a failed left
  operand starts it afresh, and the result is the aggregate's rather than the union.  The
  structure's validity is the window's, at a frame whose columns are all of the node's, together
  with the aggregate's invariant for the window's count set.
\<close>

type_synonym swagg = "swaux \<times> egagg option"

function sa_move :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow> egagg option \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> cntset \<times> egagg option" where
  "sa_move args p nt pend win cc ax =
     (case safe_hd pend of
        (None, pend') \<Rightarrow> (pend', win, cc, ax)
      | (Some e, pend') \<Rightarrow>
        (if memL (args_ivl args) (nt - fst e)
         then (if memR (args_ivl args) (nt - fst e)
               then sa_move args p nt (tl_queue pend') (append_queue e win) (cnt_add (snd e) cc)
                      (ag_ins p (args_n args) (snd e) cc ax)
               else sa_move args p nt (tl_queue pend') win cc ax)
         else (pend', win, cc, ax)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, nt, pend, win, cc, ax). length (linearize pend))")
     (fastforce split: prod.splits)+

declare sa_move.simps[simp del]

function sa_expire :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow>
    egagg option \<Rightarrow> (ts \<times> event_data table) queue \<times> cntset \<times> egagg option" where
  "sa_expire args p nt win cc ax =
     (case safe_hd win of
        (None, win') \<Rightarrow> (win', cc, ax)
      | (Some e, win') \<Rightarrow>
        (if memR (args_ivl args) (nt - fst e) then (win', cc, ax)
         else sa_expire args p nt (tl_queue win') (cnt_del (snd e) cc)
                (ag_del p (args_n args) (snd e) cc ax)))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(args, p, nt, win, cc, ax). length (linearize win))")
     (fastforce split: prod.splits)+

declare sa_expire.simps[simp del]

fun sw_cc :: "swaux \<Rightarrow> cntset" where
  "sw_cc (t, pend, win, cc) = cc"

definition sa_init :: "args \<Rightarrow> eaggp \<Rightarrow> swagg" where
  "sa_init args p = (sw_init args, ag_init p (args_n args))"

definition sa_add_new_ts :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_add_new_ts args p nt aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (case sa_move args p nt pend win cc ax of (pend', win', cc', ax') \<Rightarrow>
      (case sa_expire args p nt win' cc' ax' of (win'', cc'', ax'') \<Rightarrow>
        ((nt, pend', win'', cc''), ax''))))"

definition sa_join :: "args \<Rightarrow> eaggp \<Rightarrow> event_data table \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_join args p X aux = (case aux of (w, ax) \<Rightarrow>
     (sw_join args X w,
      if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then ax
      else ag_init p (args_n args)))"

definition sa_add_new_table :: "args \<Rightarrow> eaggp \<Rightarrow> event_data table \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_add_new_table args p X aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (if memL (args_ivl args) 0
      then ((t, pend, append_queue (t, X) win, cnt_add X cc), ag_ins p (args_n args) X cc ax)
      else ((t, append_queue (t, X) pend, win, cc), ax)))"

definition sa_result :: "args \<Rightarrow> eaggp \<Rightarrow> swagg \<Rightarrow> event_data table" where
  "sa_result args p aux = (case aux of (w, ax) \<Rightarrow> ag_res p (args_n args) (sw_cc w) ax)"

definition valid_sa :: "args \<Rightarrow> eaggp \<Rightarrow> ts \<Rightarrow> swagg \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_sa args p cur aux auxlist \<longleftrightarrow> (case aux of (w, ax) \<Rightarrow>
     valid_sw args cur w auxlist \<and> length (args_R args) = args_n args \<and>
     eagg_ok p (args_n args) \<and> ag_inv p (args_n args) (sw_cc w) ax)"

subsubsection \<open>The scans, and what the window's validity says about its tables\<close>

lemma sa_move_rep:
  assumes "linearize pend = pl" and "sa_move args p nt pend win cc ax = (pend', win', cc', ax')"
  shows "sw_move args nt pend win cc = (pend', win', cc') \<and>
    (cnt_rep f cc \<longrightarrow> eagg_ok p (args_n args) \<longrightarrow>
     (\<forall>e \<in> set pl. finite (snd e) \<and> ewf_table (args_n args) (snd e)) \<longrightarrow>
     ewf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
     ag_inv p (args_n args) cc' ax')"
  using assms
proof (induct pl arbitrary: pend win cc ax pend' win' cc' ax' f)
  case Nil
  obtain ho pend0 where sh: "safe_hd pend = (ho, pend0)" by (cases "safe_hd pend")
  have "ho = None" and "linearize pend0 = []"
    using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  then show ?case using Nil(2) by (subst (asm) sa_move.simps, subst sw_move.simps) (simp add: sh)
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
      have rec: "sa_move args p nt (tl_queue pend0) (append_queue e win) (cnt_add (snd e) cc)
          (ag_ins p (args_n args) (snd e) cc ax) = (pend', win', cc', ax')"
        using Cons(3) by (subst (asm) sa_move.simps) (simp add: sh ho True r)
      note IH = Cons(1)[OF lt rec, of "\<lambda>x. if x \<in> snd e then f x + 1 else f x"]
      have sw: "sw_move args nt pend win cc = (pend', win', cc')"
        using IH by (subst sw_move.simps) (simp add: sh ho True r)
      moreover have "ag_inv p (args_n args) cc' ax'"
        if cr: "cnt_rep f cc" and ok: "eagg_ok p (args_n args)"
          and tb: "\<forall>e \<in> set (e # rest). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
          and S: "ewf_table (args_n args) (snd cc)" and inv: "ag_inv p (args_n args) cc ax"
      proof -
        have fe: "finite (snd e)" and de: "ewf_table (args_n args) (snd e)" using tb by auto
        show ?thesis
          using IH[THEN conjunct2, rule_format, OF cnt_rep_add[OF cr fe] ok _ _
              ag_inv_ins[OF cr fe ok de S inv]] tb S de
          unfolding cnt_rep_snd_add[OF cr fe] by auto
      qed
      ultimately show ?thesis by blast
    next
      case r: False
      have rec: "sa_move args p nt (tl_queue pend0) win cc ax = (pend', win', cc', ax')"
        using Cons(3) by (subst (asm) sa_move.simps) (simp add: sh ho True r)
      note IH = Cons(1)[OF lt rec, of f]
      have "sw_move args nt pend win cc = (pend', win', cc')"
        using IH by (subst sw_move.simps) (simp add: sh ho True r)
      then show ?thesis using IH by auto
    qed
  next
    case False
    have "(pend0, win, cc, ax) = (pend', win', cc', ax')"
      using Cons(3) by (subst (asm) sa_move.simps) (simp add: sh ho False)
    then show ?thesis by (subst sw_move.simps) (simp add: sh ho False)
  qed
qed

lemma sa_expire_rep:
  assumes "linearize win = wl" and "sa_expire args p nt win cc ax = (win', cc', ax')"
  shows "sw_expire args nt win cc = (win', cc') \<and>
    (cnt_rep f cc \<longrightarrow> eagg_ok p (args_n args) \<longrightarrow>
     (\<forall>e \<in> set wl. finite (snd e) \<and> ewf_table (args_n args) (snd e)) \<longrightarrow>
     ewf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
     ag_inv p (args_n args) cc' ax')"
  using assms
proof (induct wl arbitrary: win cc ax win' cc' ax' f)
  case Nil
  obtain ho win0 where sh: "safe_hd win = (ho, win0)" by (cases "safe_hd win")
  have "ho = None" and "linearize win0 = []"
    using safe_hd_rep[OF sh] Nil(1) by (auto split: option.splits)
  then show ?case using Nil(2) by (subst (asm) sa_expire.simps, subst sw_expire.simps) (simp add: sh)
next
  case (Cons e rest)
  obtain ho win0 where sh: "safe_hd win = (ho, win0)" by (cases "safe_hd win")
  have l0: "linearize win0 = e # rest" using safe_hd_rep[OF sh] Cons(2) by simp
  have ho: "ho = Some e" using safe_hd_rep[OF sh] l0 by (cases ho) auto
  have lt: "linearize (tl_queue win0) = rest" by (simp add: tl_queue_rep l0)
  show ?case
  proof (cases "memR (args_ivl args) (nt - fst e)")
    case True
    have "(win0, cc, ax) = (win', cc', ax')"
      using Cons(3) by (subst (asm) sa_expire.simps) (simp add: sh ho True)
    then show ?thesis by (subst sw_expire.simps) (simp add: sh ho True)
  next
    case False
    have rec: "sa_expire args p nt (tl_queue win0) (cnt_del (snd e) cc)
        (ag_del p (args_n args) (snd e) cc ax) = (win', cc', ax')"
      using Cons(3) by (subst (asm) sa_expire.simps) (simp add: sh ho False)
    note IH = Cons(1)[OF lt rec, of "\<lambda>x. if x \<in> snd e then f x - 1 else f x"]
    have sw: "sw_expire args nt win cc = (win', cc')"
      using IH by (subst sw_expire.simps) (simp add: sh ho False)
    moreover have "ag_inv p (args_n args) cc' ax'"
      if cr: "cnt_rep f cc" and ok: "eagg_ok p (args_n args)"
        and tb: "\<forall>e \<in> set (e # rest). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
        and S: "ewf_table (args_n args) (snd cc)" and inv: "ag_inv p (args_n args) cc ax"
    proof -
      have fe: "finite (snd e)" and de: "ewf_table (args_n args) (snd e)" using tb by auto
      show ?thesis
        using IH[THEN conjunct2, rule_format, OF cnt_rep_del[OF cr fe] ok _ _
            ag_inv_del[OF cr fe ok de S inv]] tb S de
        unfolding cnt_rep_snd_del[OF cr fe] by auto
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma valid_sw_tables:
  assumes v: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
  shows "\<forall>e \<in> set (linearize pend @ linearize win). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
    and "ewf_table (args_n args) (snd cc)" and "cnt_rep (cnt_of (map snd (linearize win))) cc"
proof -
  have tb: "\<And>e. e \<in> set (linearize pend @ linearize win) \<Longrightarrow> finite (snd e)"
    using v by (auto simp: valid_sw_def sw_inv_def)
  have at: "\<And>u. tbls_at u (linearize pend @ linearize win) = tbls_at u auxlist"
    using v by (auto simp: valid_sw_def)
  have aux: "\<And>t rel. (t, rel) \<in> set auxlist \<Longrightarrow> table (args_R args) rel"
    using v by (auto simp: valid_sw_def)
  have dwf: "ewf_table (args_n args) (snd e)" if e: "e \<in> set (linearize pend @ linearize win)" for e
  proof
    fix x assume x: "x \<in> snd e"
    obtain u rel where eu: "e = (u, rel)" by (cases e)
    have "x \<in> tbls_at u (linearize pend @ linearize win)" using e x by (auto simp: in_tbls_at eu)
    then obtain rel' where "(u, rel') \<in> set auxlist" "x \<in> rel'" unfolding at by (auto simp: in_tbls_at)
    then show "length x = args_n args" using aux R by (auto simp: table_def wf_tuple_def)
  qed
  show "\<forall>e \<in> set (linearize pend @ linearize win). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
    using tb dwf by auto
  show cr: "cnt_rep (cnt_of (map snd (linearize win))) cc" using v by (auto simp: valid_sw_def)
  show "ewf_table (args_n args) (snd cc)" using cnt_inv_set[OF cr] dwf by auto
qed

subsubsection \<open>Validity\<close>

lemma valid_sa_init: "length (args_R args) = args_n args \<Longrightarrow> eagg_ok p (args_n args) \<Longrightarrow>
  valid_sa args p 0 (sa_init args p) []"
  using valid_sw_init[of args] by (auto simp: valid_sa_def sa_init_def sw_init_def ag_inv_init)

lemma valid_sa_add_new_ts:
  assumes v: "valid_sa args p cur aux auxlist" and nt: "cur \<le> nt"
  shows "valid_sa args p nt (sa_add_new_ts args p nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  obtain pend' win' cc' ax' where m: "sa_move args p nt pend win cc ax = (pend', win', cc', ax')"
    by (cases "sa_move args p nt pend win cc ax")
  obtain win'' cc'' ax'' where x: "sa_expire args p nt win' cc' ax' = (win'', cc'', ax'')"
    by (cases "sa_expire args p nt win' cc' ax'")
  note tbl = valid_sw_tables[OF vsw R]
  note mr = sa_move_rep[OF refl m, of "cnt_of (map snd (linearize win))"]
  have sw1: "sw_move args nt pend win cc = (pend', win', cc')" using mr by simp
  have inv1: "ag_inv p (args_n args) cc' ax'" using mr tbl ok inv by auto
  let ?moved = "filter (\<lambda>e. memR (args_ivl args) (nt - fst e))
    (takeWhile (\<lambda>e. memL (args_ivl args) (nt - fst e)) (linearize pend))"
  have rep: "linearize win' = linearize win @ ?moved" "cc' = fold cnt_add (map snd ?moved) cc"
    using sw_move_rep[OF refl sw1] by simp_all
  have moved: "set ?moved \<subseteq> set (linearize pend)" by (auto dest: set_takeWhileD)
  have tb1: "\<forall>e \<in> set (linearize win'). finite (snd e) \<and> ewf_table (args_n args) (snd e)"
    using tbl(1) moved unfolding rep(1) by auto
  have cr1: "cnt_rep (cnt_of (map snd (linearize win'))) cc'"
  proof -
    have fm: "\<forall>T \<in> set (map snd ?moved). finite T" using tbl(1) by (fastforce dest!: set_takeWhileD)
    show ?thesis unfolding rep using cnt_inv_adds[OF tbl(3) fm] by simp
  qed
  have S1: "ewf_table (args_n args) (snd cc')" using cnt_inv_set[OF cr1] tb1 by auto
  note xr = sa_expire_rep[OF refl x, of "cnt_of (map snd (linearize win'))"]
  have sw2: "sw_expire args nt win' cc' = (win'', cc'')" using xr by simp
  have inv2: "ag_inv p (args_n args) cc'' ax''" using xr cr1 ok tb1 S1 inv1 by auto
  have "sw_add_new_ts args nt (t, pend, win, cc) = (nt, pend', win'', cc'')"
    by (simp add: sw_add_new_ts_def sw1 sw2)
  then show ?thesis
    using valid_sw_add_new_ts[OF vsw nt] R ok inv2
    by (simp add: valid_sa_def sa_add_new_ts_def aux m x)
qed

lemma valid_sa_join:
  assumes v: "valid_sa args p cur aux auxlist"
    and t1: "table [] rel1" and X: "(X = {}) = (rel1 = {})"
  shows "valid_sa args p cur (sa_join args p X aux)
    (map (\<lambda>(t, rel). (t, join (args_R args) rel (args_pos args) [] rel1)) auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  show ?thesis
    using valid_sw_join[OF vsw t1 X] R ok inv ag_inv_init[of p "args_n args"]
    by (auto simp: valid_sa_def sa_join_def sw_join_def aux)
qed

lemma valid_sa_add_new_table:
  assumes v: "valid_sa args p cur aux auxlist"
    and t2: "table (args_R args) rel2" and f2: "finite rel2"
  shows "valid_sa args p cur (sa_add_new_table args p rel2 aux)
    (case auxlist of [] \<Rightarrow> [(cur, rel2)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  note tbl = valid_sw_tables[OF vsw R]
  have d2: "ewf_table (args_n args) rel2" using t2 R by (auto simp: table_def wf_tuple_def)
  have "ag_inv p (args_n args) (cnt_add rel2 cc) (ag_ins p (args_n args) rel2 cc ax)"
    by (rule ag_inv_ins[OF tbl(3) f2 ok d2 tbl(2) inv])
  then show ?thesis
    using valid_sw_add_new_table[OF vsw t2 f2] R ok inv
    by (auto simp: valid_sa_def sa_add_new_table_def sw_add_new_table_def aux)
qed

lemma valid_sa_result:
  assumes v: "valid_sa args p cur aux auxlist"
  shows "sa_result args p aux =
    eagg_p p (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "length (args_R args) = args_n args"
    and ok: "eagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  have "sa_result args p aux = eagg_p p (snd cc)"
    using ag_res_inv[OF inv ok valid_sw_tables(2)[OF vsw R]] by (simp add: sa_result_def aux)
  also have "snd cc = sw_result args (t, pend, win, cc)" by (simp add: sw_result_def)
  finally show ?thesis unfolding valid_sw_result[OF vsw] .
qed

(*<*)
end
(*>*)