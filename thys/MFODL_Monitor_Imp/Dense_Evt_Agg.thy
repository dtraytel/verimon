(*<*)
theory Dense_Evt_Agg
  imports Dense_Evt Dense_Aux
begin
(*>*)

section \<open>The Since window with the aggregation fused in\<close>

text \<open>
  The kernel folds an aggregation over a Since into the Since node (@{const args_agg}) and its
  structure keeps the aggregate incrementally, in @{typ aggaux}: a count, a sum or a rank tree
  per group, updated as tuples enter and leave.  The dense evaluator unfuses the two, a
  @{text DAgg} node over a @{text DSince} whose window reports the plain union, and recomputes
  the aggregate from the union at every time point.  This theory fuses them again for the
  window: the count set already makes a tuple's entry into and exit from the union explicit, and
  those are exactly the events the kernel's incremental structure takes.

  The dense aggregation @{const dagg} is stated on tuples without the result column; the kernel's
  @{const eval_agg}, and hence @{const valid_maggaux}, on tuples with a slot for it.  So the
  fused window feeds the structure the window's tuples widened by that one slot, and the first
  lemma below says that the dense aggregation is the kernel's on the widened tuples, narrowed
  back -- an instance of @{thm [source] dagg_eval_agg} at the dense frame.
\<close>

subsection \<open>The dense aggregation as the kernel's, one column wider\<close>

text \<open>The parameters of a @{text DAgg} node: @{text g0}, the operator, the term, the number of
  bound variables and the position of the result column.\<close>

type_synonym daggp = "bool \<times> ty Formula.agg_op \<times> Formula.trm \<times> nat \<times> nat"

fun dagg_p :: "daggp \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dagg_p (g0, \<omega>, f, k, pos) = dagg g0 \<omega> f k pos"

lemma dsan_dagg_p[simp]: "dsan (dagg_p p X) = dagg_p p X"
  by (cases p) (simp add: dagg_def)

text \<open>What the parameters must satisfy at a window over tuples of width @{text w}.\<close>

fun dagg_ok :: "daggp \<Rightarrow> nat \<Rightarrow> bool" where
  "dagg_ok (g0, \<omega>, f, k, pos) w \<longleftrightarrow>
     k \<le> w \<and> pos \<le> w - k \<and> Formula.fv_trm f \<subseteq> {0..<w} \<and> (g0 \<longrightarrow> w = k)"

text \<open>The kernel's frame: the group columns are all of the result's columns but the result
  column, and the term reads the tuple with the slot skipped.\<close>

fun dagg_gcols :: "daggp \<Rightarrow> nat \<Rightarrow> cols" where
  "dagg_gcols (g0, \<omega>, f, k, pos) w = [0..<pos] @ [Suc pos..<Suc (w - k)]"

text \<open>The parameters the compiler builds from a fused node's aggregation are well formed at the
  width of the node's operand.\<close>

lemma ins_pos_le: "ins_pos cs y \<le> length cs"
  by (simp add: ins_pos_def)

lemma dagg_ok_agg:
  assumes "Formula.fv_trm f \<subseteq> set (agg_cols k g)" and "g0 \<Longrightarrow> g = []"
  shows "dagg_ok (g0, \<omega>, reindex_trm (agg_cols k g) f, k, ins_pos g y) (length (agg_cols k g))"
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

fun dagg_ccols :: "daggp \<Rightarrow> nat \<Rightarrow> cols" where
  "dagg_ccols (g0, \<omega>, f, k, pos) w = agg_cols k (dagg_gcols (g0, \<omega>, f, k, pos) w)"

fun dagg_args :: "daggp \<Rightarrow> nat \<Rightarrow> aggargs" where
  "dagg_args (g0, \<omega>, f, k, pos) w =
     \<lparr>aggargs_cols = set (dagg_ccols (g0, \<omega>, f, k, pos) w), aggargs_n = Suc (w - k),
      aggargs_g0 = g0, aggargs_y = pos, aggargs_\<omega> = \<omega>, aggargs_tys = replicate k Formula.TInt,
      aggargs_f = shift_trm (k + pos) f\<rparr>"

definition dagg_wide :: "daggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "dagg_wide p w D = dtabw (Suc w) (dagg_ccols p w) D"

lemma fv_shift_trm:
  "Formula.fv_trm (shift_trm b f) = (\<lambda>x. if x < b then x else Suc x) ` Formula.fv_trm f"
  by (induct f) auto

lemma map_add_upt': "map (\<lambda>c. c + k) [a..<b] = [a + k..<b + k]"
  by (induct b) auto

lemma upt_split: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  using upt_add_eq_append[of a b "c - b"] by simp

lemma agg_cols_dagg_gcols:
  assumes "k \<le> w" and "pos \<le> w - k"
  shows "agg_cols k (dagg_gcols (g0, \<omega>, f, k, pos) w) = [0..<k + pos] @ [Suc (k + pos)..<Suc w]"
proof -
  have 1: "map (\<lambda>c. c + k) [0..<pos] = [k..<k + pos]" by (simp add: map_add_upt' add.commute)
  have 2: "map (\<lambda>c. c + k) [Suc pos..<Suc (w - k)] = [Suc (k + pos)..<Suc w]"
    using assms by (simp add: map_add_upt' add.commute del: upt_Suc)
  have 3: "[0..<k] @ [k..<k + pos] = [0..<k + pos]" by (rule upt_split) simp_all
  show ?thesis unfolding dagg_gcols.simps map_append 1 2 append_assoc[symmetric] 3 ..
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

lemma ins_pos_dagg_gcols: "ins_pos ([0..<pos] @ [Suc pos..<Suc m]) pos = pos"
proof -
  have "filter (\<lambda>c. c < pos) [0..<pos] = [0..<pos]" by (rule filter_True) simp
  moreover have "filter (\<lambda>c. c < pos) [Suc pos..<Suc m] = []"
    by (rule filter_False) (auto simp del: upt_Suc)
  ultimately show ?thesis by (simp add: ins_pos_def del: upt_Suc)
qed

lemma sorted_wrt_dagg_gcols: "sorted_wrt (<) ([0..<pos] @ [Suc pos..<Suc m])"
  by (auto simp: sorted_wrt_append simp del: upt_Suc)

lemma merge_cols_dagg_gcols:
  assumes "pos \<le> m"
  shows "merge_cols ([0..<pos] @ [Suc pos..<Suc m]) [pos] = [0..<Suc m]"
proof -
  have nin: "pos \<notin> set ([0..<pos] @ [Suc pos..<Suc m])" by (auto simp del: upt_Suc)
  have "[0..<pos] @ pos # [Suc pos..<Suc m] = [0..<pos] @ [pos..<Suc m]"
    using assms by (simp add: upt_conv_Cons del: upt_Suc)
  also have "\<dots> = [0..<Suc m]" using assms by (intro upt_split) simp_all
  finally show ?thesis
    unfolding merge_cols_single[OF sorted_wrt_dagg_gcols nin] ins_pos_dagg_gcols
    by (simp del: upt_Suc)
qed

text \<open>The dense aggregation is the kernel's aggregation at the dense frame, on the tuples
  widened by the result column's slot, with that column narrowed away again.\<close>

lemma dagg_p_eval_aggargs:
  assumes ok: "dagg_ok p w" and D: "\<forall>d \<in> D. dwf_tuple w d"
  shows "dagg_p p D = dtabc (aggargs_n (dagg_args p w)) [0..<aggargs_n (dagg_args p w)]
      (eval_aggargs (dagg_args p w) (dagg_wide p w D))"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p)
  let ?n = "Suc (w - k)"
  define G where "G = dagg_gcols (g0, \<omega>, f, k, pos) w"
  define cc where "cc = agg_cols k G"
  have kw: "k \<le> w" and pw: "pos \<le> w - k" and fv: "Formula.fv_trm f \<subseteq> {0..<w}"
    and g0: "g0 \<Longrightarrow> w = k" using ok by (auto simp: p)
  have kpw: "k + pos \<le> w" using kw pw by arith
  have ccE: "cc = [0..<k + pos] @ [Suc (k + pos)..<Suc w]"
    unfolding cc_def G_def by (rule agg_cols_dagg_gcols[OF kw pw])
  have GE: "G = [0..<pos] @ [Suc pos..<Suc (w - k)]" by (simp add: G_def)
  have sg: "sorted_wrt (<) G" unfolding GE by (rule sorted_wrt_dagg_gcols)
  have bg: "\<forall>c \<in> set G. c < ?n" unfolding GE using pw by (auto simp del: upt_Suc)
  have yn: "pos < ?n" using pw by simp
  have yg: "pos \<notin> set G" unfolding GE by (auto simp del: upt_Suc)
  have scc: "sorted_wrt (<) cc" unfolding ccE by (auto simp: sorted_wrt_append simp del: upt_Suc)
  have bcc: "\<forall>c \<in> set cc. c < Suc w" unfolding ccE using kpw by (auto simp del: upt_Suc)
  have lcc: "length cc = w" unfolding ccE using kpw by (simp del: upt_Suc)
  have dD: "dtable cc D" using D lcc by (simp add: dtable_def)
  have kn: "k + ?n = Suc w" using kw by simp
  have rel: "table (k + ?n) (set (agg_cols k G)) (dtabw (Suc w) cc D)"
    unfolding kn cc_def[symmetric] by (rule table_dtabw[OF scc bcc dD])
  have fv': "Formula.fv_trm (shift_trm (k + pos) f) \<subseteq> set (agg_cols k G)"
    unfolding cc_def[symmetric] ccE fv_shift_trm using fv kpw by (auto simp del: upt_Suc)
  have g0': "g0 \<Longrightarrow> G = []" unfolding GE using g0 pw by simp
  note dea = dagg_eval_agg[of G ?n pos "replicate k Formula.TInt" "dtabw (Suc w) cc D"
      "shift_trm (k + pos) f" g0 \<omega>, simplified length_replicate]
  have 1: "reindex_trm (agg_cols k G) (shift_trm (k + pos) f) = f"
    unfolding cc_def[symmetric] ccE by (rule reindex_shift_trm[OF fv kpw])
  have 2: "ins_pos G pos = pos" unfolding GE by (rule ins_pos_dagg_gcols)
  have 3: "dtabc (Suc w) (agg_cols k G) (dtabw (Suc w) cc D) = D"
    unfolding cc_def[symmetric] by (rule dtabc_dtabw[OF scc bcc dD])
  have 4: "merge_cols G [pos] = [0..<?n]" unfolding GE by (rule merge_cols_dagg_gcols[OF pw])
  have main: "dagg g0 \<omega> f k pos D = dtabc ?n [0..<?n] (eval_agg ?n g0 pos \<omega> (replicate k Formula.TInt)
      (shift_trm (k + pos) f) (dtabw (Suc w) cc D))"
    using dea[OF sg bg yn yg rel fv' g0'] kw by (simp add: 1 2 3 4 del: upt_Suc)
  show ?thesis unfolding p
    by (simp add: eval_aggargs_def dagg_wide_def G_def[symmetric] cc_def[symmetric] main
        del: upt_Suc dagg_gcols.simps)
qed

subsection \<open>The aggregate alongside the count set\<close>

text \<open>
  The count set makes a tuple's entry into and exit from the window's union explicit: a table
  added contributes the tuples not yet in the union, a table removed takes out the tuples it was
  the last to hold.  Those are the insertions and deletions the kernel's incremental structure
  takes, on the widened tuples.  The structure is optional, as in the kernel: @{const None} once
  an operation reports that it cannot maintain the aggregate, and then the result is computed
  from the union directly.
\<close>

abbreviation sa_n :: "daggp \<Rightarrow> nat \<Rightarrow> nat" where "sa_n p w \<equiv> aggargs_n (dagg_args p w)"

abbreviation dwf_table :: "nat \<Rightarrow> event_data table \<Rightarrow> bool" where
  "dwf_table w T \<equiv> \<forall>x \<in> T. dwf_tuple w x"

definition cnt_enter :: "event_data table \<Rightarrow> cntset \<Rightarrow> event_data table" where
  "cnt_enter T cc = T - snd cc"

definition cnt_leave :: "event_data table \<Rightarrow> cntset \<Rightarrow> event_data table" where
  "cnt_leave T cc = Set.filter (\<lambda>x. Mapping.lookup (fst cc) x = Some 1) T"

definition ag_init :: "daggp \<Rightarrow> nat \<Rightarrow> aggaux option" where
  "ag_init p w = init_maggaux' (dagg_args p w)"

definition ag_ins :: "daggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "ag_ins p w T cc ax = insert_maggaux' (dagg_args p w) (dagg_wide p w (cnt_enter T cc)) ax"

definition ag_del :: "daggp \<Rightarrow> nat \<Rightarrow> event_data table \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "ag_del p w T cc ax = delete_maggaux' (dagg_args p w) (dagg_wide p w (cnt_leave T cc)) ax"

text \<open>The kernel structure's result is sanitised on the way out: on the hole-free tables the
  invariant below guarantees that is the identity, and it lets the unboxed evaluator read the
  result without an invariant.\<close>

definition ag_res :: "daggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> event_data table" where
  "ag_res p w cc ax = (case ax of
     None \<Rightarrow> dagg_p p (snd cc)
   | Some a \<Rightarrow> dsan (dtabc (sa_n p w) [0..<sa_n p w] (result_maggaux (dagg_args p w) a)))"

definition ag_inv :: "daggp \<Rightarrow> nat \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow> bool" where
  "ag_inv p w cc ax \<longleftrightarrow> valid_maggaux' (dagg_args p w) ax (dagg_wide p w (snd cc))"

lemma cnt_rep_snd_add: "cnt_rep f cc \<Longrightarrow> finite T \<Longrightarrow> snd (cnt_add T cc) = snd cc \<union> T"
  using cnt_rep_add[of f cc T] unfolding cnt_rep_def by auto

lemma cnt_leave_rep: "cnt_rep f cc \<Longrightarrow> cnt_leave T cc = {x \<in> T. f x = 1}"
  unfolding cnt_leave_def cnt_rep_def by (auto split: if_splits)

lemma cnt_rep_snd_del: "cnt_rep f cc \<Longrightarrow> finite T \<Longrightarrow> snd (cnt_del T cc) = snd cc - cnt_leave T cc"
  using cnt_rep_del[of f cc T] cnt_leave_rep[of f cc T] unfolding cnt_rep_def by auto

lemma cnt_leave_sub: assumes "cnt_rep f cc" shows "cnt_leave T cc \<subseteq> snd cc"
  using assms unfolding cnt_leave_rep[OF assms] cnt_rep_def by auto

lemma dagg_ccols_props:
  assumes "dagg_ok p w"
  shows "sorted_wrt (<) (dagg_ccols p w)" "\<forall>c \<in> set (dagg_ccols p w). c < Suc w"
    "length (dagg_ccols p w) = w"
proof -
  obtain g0 \<omega> f k pos where p: "p = (g0, \<omega>, f, k, pos)" by (cases p)
  have kw: "k \<le> w" and pw: "pos \<le> w - k" using assms by (auto simp: p)
  have kpw: "k + pos \<le> w" using kw pw by arith
  have cc: "dagg_ccols p w = [0..<k + pos] @ [Suc (k + pos)..<Suc w]"
    unfolding p dagg_ccols.simps by (rule agg_cols_dagg_gcols[OF kw pw])
  show "sorted_wrt (<) (dagg_ccols p w)" unfolding cc
    by (auto simp: sorted_wrt_append simp del: upt_Suc)
  show "\<forall>c \<in> set (dagg_ccols p w). c < Suc w" unfolding cc using kpw by (auto simp del: upt_Suc)
  show "length (dagg_ccols p w) = w" unfolding cc using kpw by (simp del: upt_Suc)
qed

lemma dagg_wide_Un: "dagg_wide p w (A \<union> B) = dagg_wide p w A \<union> dagg_wide p w B"
  by (simp add: dagg_wide_def dtabw_def image_Un)

lemma dagg_wide_empty[simp]: "dagg_wide p w {} = {}"
  by (simp add: dagg_wide_def dtabw_def)

lemma dagg_wide_finite: "finite A \<Longrightarrow> finite (dagg_wide p w A)"
  by (simp add: dagg_wide_def dtabw_def)

lemma dagg_wide_mono: "A \<subseteq> B \<Longrightarrow> dagg_wide p w A \<subseteq> dagg_wide p w B"
  by (auto simp: dagg_wide_def dtabw_def)

lemma dagg_wide_inj:
  assumes ok: "dagg_ok p w" and A: "dwf_table w A" and B: "dwf_table w B"
  shows "dagg_wide p w A \<inter> dagg_wide p w B = dagg_wide p w (A \<inter> B)"
    and "dagg_wide p w A - dagg_wide p w B = dagg_wide p w (A - B)"
proof -
  let ?m = "wide_mask (Suc w) (dagg_ccols p w)"
  have lm: "length (filter id ?m) = w"
    using length_filter_wide_mask[OF dagg_ccols_props(1,2)[OF ok]] dagg_ccols_props(3)[OF ok]
    by simp
  have inj: "inj_on (dwiden ?m) {y. dwf_tuple w y}"
    by (rule inj_on_subset[OF inj_on_dwiden]) (auto simp: lm dwf_tuple_def)
  have sA: "A \<subseteq> {y. dwf_tuple w y}" and sB: "B \<subseteq> {y. dwf_tuple w y}" using A B by auto
  show "dagg_wide p w A \<inter> dagg_wide p w B = dagg_wide p w (A \<inter> B)"
    unfolding dagg_wide_def dtabw_def by (rule inj_on_image_Int[OF inj sA sB, symmetric])
  have sAB: "A - B \<subseteq> {y. dwf_tuple w y}" using sA by auto
  show "dagg_wide p w A - dagg_wide p w B = dagg_wide p w (A - B)"
    unfolding dagg_wide_def dtabw_def by (rule inj_on_image_set_diff[OF inj sAB sB, symmetric])
qed

lemma ag_inv_init: "ag_inv p w (Mapping.empty, {}) (ag_init p w)"
  using valid_init_maggaux[of "dagg_args p w"]
  by (auto simp: ag_inv_def ag_init_def split: prod.splits)

lemma ag_inv_ins:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and ok: "dagg_ok p w"
    and T: "dwf_table w T" and S: "dwf_table w (snd cc)" and inv: "ag_inv p w cc ax"
  shows "ag_inv p w (cnt_add T cc) (ag_ins p w T cc ax)"
proof (cases ax)
  case None
  then show ?thesis by (simp add: ag_inv_def ag_ins_def)
next
  case (Some a)
  let ?X = "dagg_wide p w (snd cc)" and ?Y = "dagg_wide p w (cnt_enter T cc)"
  have v: "valid_maggaux (dagg_args p w) a ?X" using inv by (simp add: ag_inv_def Some)
  have fY: "finite ?Y" using fT by (simp add: cnt_enter_def dagg_wide_finite)
  have dj: "?X \<inter> ?Y = {}"
    using dagg_wide_inj(1)[OF ok S, of "cnt_enter T cc"] T by (auto simp: cnt_enter_def)
  have XY: "?X \<union> ?Y = dagg_wide p w (snd (cnt_add T cc))"
    unfolding cnt_rep_snd_add[OF cr fT] dagg_wide_Un[symmetric] cnt_enter_def by simp
  show ?thesis
    using valid_insert_maggaux[OF v fY dj] unfolding XY
    by (auto simp: ag_inv_def ag_ins_def Some split: prod.splits)
qed

lemma ag_inv_del:
  assumes cr: "cnt_rep f cc" and fT: "finite T" and ok: "dagg_ok p w"
    and T: "dwf_table w T" and S: "dwf_table w (snd cc)" and inv: "ag_inv p w cc ax"
  shows "ag_inv p w (cnt_del T cc) (ag_del p w T cc ax)"
proof (cases ax)
  case None
  then show ?thesis by (simp add: ag_inv_def ag_del_def)
next
  case (Some a)
  let ?X = "dagg_wide p w (snd cc)" and ?Y = "dagg_wide p w (cnt_leave T cc)"
  have v: "valid_maggaux (dagg_args p w) a ?X" using inv by (simp add: ag_inv_def Some)
  have sub: "?Y \<subseteq> ?X" by (rule dagg_wide_mono[OF cnt_leave_sub[OF cr]])
  have XY: "?X - ?Y = dagg_wide p w (snd (cnt_del T cc))"
    unfolding cnt_rep_snd_del[OF cr fT]
    by (rule dagg_wide_inj(2)[OF ok S]) (use cnt_leave_sub[OF cr] S in auto)
  show ?thesis
    using valid_delete_maggaux[OF v sub] unfolding XY
    by (auto simp: ag_inv_def ag_del_def Some split: prod.splits)
qed

lemma ag_res_inv:
  assumes inv: "ag_inv p w cc ax" and ok: "dagg_ok p w" and S: "dwf_table w (snd cc)"
  shows "ag_res p w cc ax = dagg_p p (snd cc)"
proof (cases ax)
  case None
  then show ?thesis by (simp add: ag_res_def)
next
  case (Some a)
  have "result_maggaux (dagg_args p w) a = eval_aggargs (dagg_args p w) (dagg_wide p w (snd cc))"
    by (rule valid_result_maggaux) (use inv in \<open>simp add: ag_inv_def Some\<close>)
  then show ?thesis
    unfolding ag_res_def Some option.case by (simp add: dagg_p_eval_aggargs[OF ok S, symmetric])
qed

subsection \<open>The window, with the aggregate\<close>

text \<open>
  The window of @{theory MFODL_Monitor_Imp.Dense_Evt} again, with the aggregate carried along:
  the two scans update it with every table that enters or leaves, the reset on a failed left
  operand starts it afresh, and the result is the aggregate's rather than the union.  The
  structure's validity is the window's, at a frame whose columns are all of the node's, together
  with the aggregate's invariant for the window's count set.
\<close>

type_synonym swagg = "swaux \<times> aggaux option"

function sa_move :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow>
    (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow> aggaux option \<Rightarrow>
    (ts \<times> event_data table) queue \<times> (ts \<times> event_data table) queue \<times> cntset \<times> aggaux option" where
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

function sa_expire :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> (ts \<times> event_data table) queue \<Rightarrow> cntset \<Rightarrow>
    aggaux option \<Rightarrow> (ts \<times> event_data table) queue \<times> cntset \<times> aggaux option" where
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

definition sa_init :: "args \<Rightarrow> daggp \<Rightarrow> swagg" where
  "sa_init args p = (sw_init args, ag_init p (args_n args))"

definition sa_add_new_ts :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_add_new_ts args p nt aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (case sa_move args p nt pend win cc ax of (pend', win', cc', ax') \<Rightarrow>
      (case sa_expire args p nt win' cc' ax' of (win'', cc'', ax'') \<Rightarrow>
        ((nt, pend', win'', cc''), ax''))))"

definition sa_join :: "args \<Rightarrow> daggp \<Rightarrow> event_data table \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_join args p X aux = (case aux of (w, ax) \<Rightarrow>
     (sw_join args X w,
      if (if args_pos args then \<not> Set.is_empty X else Set.is_empty X) then ax
      else ag_init p (args_n args)))"

definition sa_add_new_table :: "args \<Rightarrow> daggp \<Rightarrow> event_data table \<Rightarrow> swagg \<Rightarrow> swagg" where
  "sa_add_new_table args p X aux = (case aux of ((t, pend, win, cc), ax) \<Rightarrow>
     (if memL (args_ivl args) 0
      then ((t, pend, append_queue (t, X) win, cnt_add X cc), ag_ins p (args_n args) X cc ax)
      else ((t, append_queue (t, X) pend, win, cc), ax)))"

definition sa_result :: "args \<Rightarrow> daggp \<Rightarrow> swagg \<Rightarrow> event_data table" where
  "sa_result args p aux = (case aux of (w, ax) \<Rightarrow> ag_res p (args_n args) (sw_cc w) ax)"

definition valid_sa :: "args \<Rightarrow> daggp \<Rightarrow> ts \<Rightarrow> swagg \<Rightarrow> event_data msaux \<Rightarrow> bool" where
  "valid_sa args p cur aux auxlist \<longleftrightarrow> (case aux of (w, ax) \<Rightarrow>
     valid_sw args cur w auxlist \<and> args_R args = {0..<args_n args} \<and>
     dagg_ok p (args_n args) \<and> ag_inv p (args_n args) (sw_cc w) ax)"

subsubsection \<open>The scans, and what the window's validity says about its tables\<close>

lemma sa_move_rep:
  assumes "linearize pend = pl" and "sa_move args p nt pend win cc ax = (pend', win', cc', ax')"
  shows "sw_move args nt pend win cc = (pend', win', cc') \<and>
    (cnt_rep f cc \<longrightarrow> dagg_ok p (args_n args) \<longrightarrow>
     (\<forall>e \<in> set pl. finite (snd e) \<and> dwf_table (args_n args) (snd e)) \<longrightarrow>
     dwf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
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
        if cr: "cnt_rep f cc" and ok: "dagg_ok p (args_n args)"
          and tb: "\<forall>e \<in> set (e # rest). finite (snd e) \<and> dwf_table (args_n args) (snd e)"
          and S: "dwf_table (args_n args) (snd cc)" and inv: "ag_inv p (args_n args) cc ax"
      proof -
        have fe: "finite (snd e)" and de: "dwf_table (args_n args) (snd e)" using tb by auto
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
    (cnt_rep f cc \<longrightarrow> dagg_ok p (args_n args) \<longrightarrow>
     (\<forall>e \<in> set wl. finite (snd e) \<and> dwf_table (args_n args) (snd e)) \<longrightarrow>
     dwf_table (args_n args) (snd cc) \<longrightarrow> ag_inv p (args_n args) cc ax \<longrightarrow>
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
      if cr: "cnt_rep f cc" and ok: "dagg_ok p (args_n args)"
        and tb: "\<forall>e \<in> set (e # rest). finite (snd e) \<and> dwf_table (args_n args) (snd e)"
        and S: "dwf_table (args_n args) (snd cc)" and inv: "ag_inv p (args_n args) cc ax"
    proof -
      have fe: "finite (snd e)" and de: "dwf_table (args_n args) (snd e)" using tb by auto
      show ?thesis
        using IH[THEN conjunct2, rule_format, OF cnt_rep_del[OF cr fe] ok _ _
            ag_inv_del[OF cr fe ok de S inv]] tb S de
        unfolding cnt_rep_snd_del[OF cr fe] by auto
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma wf_tuple_dwf: "wf_tuple n {0..<n} x \<Longrightarrow> dwf_tuple n x"
  by (auto simp: wf_tuple_def dwf_tuple_def)

lemma valid_sw_tables:
  assumes v: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "args_R args = {0..<args_n args}"
  shows "\<forall>e \<in> set (linearize pend @ linearize win). finite (snd e) \<and> dwf_table (args_n args) (snd e)"
    and "dwf_table (args_n args) (snd cc)" and "cnt_rep (cnt_of (map snd (linearize win))) cc"
proof -
  have tb: "\<And>e. e \<in> set (linearize pend @ linearize win) \<Longrightarrow> finite (snd e)"
    using v by (auto simp: valid_sw_def sw_inv_def)
  have at: "\<And>u. tbls_at u (linearize pend @ linearize win) = tbls_at u auxlist"
    using v by (auto simp: valid_sw_def)
  have aux: "\<And>t rel. (t, rel) \<in> set auxlist \<Longrightarrow> table (args_n args) (args_R args) rel"
    using v by (auto simp: valid_sw_def)
  have dwf: "dwf_table (args_n args) (snd e)" if e: "e \<in> set (linearize pend @ linearize win)" for e
  proof
    fix x assume x: "x \<in> snd e"
    obtain u rel where eu: "e = (u, rel)" by (cases e)
    have "x \<in> tbls_at u (linearize pend @ linearize win)" using e x by (auto simp: in_tbls_at eu)
    then obtain rel' where "(u, rel') \<in> set auxlist" "x \<in> rel'" unfolding at by (auto simp: in_tbls_at)
    then show "dwf_tuple (args_n args) x" using aux R by (auto simp: table_def intro: wf_tuple_dwf)
  qed
  show "\<forall>e \<in> set (linearize pend @ linearize win). finite (snd e) \<and> dwf_table (args_n args) (snd e)"
    using tb dwf by auto
  show cr: "cnt_rep (cnt_of (map snd (linearize win))) cc" using v by (auto simp: valid_sw_def)
  show "dwf_table (args_n args) (snd cc)" using cnt_inv_set[OF cr] dwf by auto
qed

subsubsection \<open>Validity\<close>

lemma valid_sa_init: "args_R args = {0..<args_n args} \<Longrightarrow> dagg_ok p (args_n args) \<Longrightarrow>
  valid_sa args p 0 (sa_init args p) []"
  using valid_sw_init[of args] by (auto simp: valid_sa_def sa_init_def sw_init_def ag_inv_init)

lemma valid_sa_add_new_ts:
  assumes v: "valid_sa args p cur aux auxlist" and nt: "cur \<le> nt"
  shows "valid_sa args p nt (sa_add_new_ts args p nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "args_R args = {0..<args_n args}"
    and ok: "dagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
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
  have tb1: "\<forall>e \<in> set (linearize win'). finite (snd e) \<and> dwf_table (args_n args) (snd e)"
    using tbl(1) moved unfolding rep(1) by auto
  have cr1: "cnt_rep (cnt_of (map snd (linearize win'))) cc'"
  proof -
    have fm: "\<forall>T \<in> set (map snd ?moved). finite T" using tbl(1) by (fastforce dest!: set_takeWhileD)
    show ?thesis unfolding rep using cnt_inv_adds[OF tbl(3) fm] by simp
  qed
  have S1: "dwf_table (args_n args) (snd cc')" using cnt_inv_set[OF cr1] tb1 by auto
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
    and t1: "table (args_n args) {} rel1" and X: "(X = {}) = (rel1 = {})"
  shows "valid_sa args p cur (sa_join args p X aux)
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "args_R args = {0..<args_n args}"
    and ok: "dagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  show ?thesis
    using valid_sw_join[OF vsw t1 X] R ok inv ag_inv_init[of p "args_n args"]
    by (auto simp: valid_sa_def sa_join_def sw_join_def aux)
qed

lemma valid_sa_add_new_table:
  assumes v: "valid_sa args p cur aux auxlist"
    and t2: "table (args_n args) (args_R args) rel2" and f2: "finite rel2"
  shows "valid_sa args p cur (sa_add_new_table args p rel2 aux)
    (case auxlist of [] \<Rightarrow> [(cur, rel2)]
     | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "args_R args = {0..<args_n args}"
    and ok: "dagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  note tbl = valid_sw_tables[OF vsw R]
  have d2: "dwf_table (args_n args) rel2" using t2 R by (auto simp: table_def intro: wf_tuple_dwf)
  have "ag_inv p (args_n args) (cnt_add rel2 cc) (ag_ins p (args_n args) rel2 cc ax)"
    by (rule ag_inv_ins[OF tbl(3) f2 ok d2 tbl(2) inv])
  then show ?thesis
    using valid_sw_add_new_table[OF vsw t2 f2] R ok inv
    by (auto simp: valid_sa_def sa_add_new_table_def sw_add_new_table_def aux)
qed

lemma valid_sa_result:
  assumes v: "valid_sa args p cur aux auxlist"
  shows "sa_result args p aux =
    dagg_p p (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  obtain t pend win cc ax where aux: "aux = ((t, pend, win, cc), ax)" by (cases aux) auto
  have vsw: "valid_sw args cur (t, pend, win, cc) auxlist" and R: "args_R args = {0..<args_n args}"
    and ok: "dagg_ok p (args_n args)" and inv: "ag_inv p (args_n args) cc ax"
    using v by (auto simp: valid_sa_def aux)
  have "sa_result args p aux = dagg_p p (snd cc)"
    using ag_res_inv[OF inv ok valid_sw_tables(2)[OF vsw R]] by (simp add: sa_result_def aux)
  also have "snd cc = sw_result args (t, pend, win, cc)" by (simp add: sw_result_def)
  finally show ?thesis unfolding valid_sw_result[OF vsw] .
qed

(*<*)
end
(*>*)
