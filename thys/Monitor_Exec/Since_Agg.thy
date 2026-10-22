(*<*)
theory Since_Agg
  imports Closed_Left_Windows Exec_Since Exec_Agg
begin
(*>*)

section \<open>Since window with fused aggregation\<close>

text \<open>
  The count set exposes the tuples entering and leaving the window's union, which is what the
  kernel's incremental aggregation (@{typ aggaux}) takes, so the aggregate is kept alongside.
\<close>

subsection \<open>Executable aggregation as the kernel's\<close>

subsubsection \<open>Parameters and the kernel's frame\<close>

text \<open>Parameters of an @{text EAgg} node: @{text g0}, operator, term, number of bound variables
  and position of the result column.\<close>

type_synonym eaggp = "bool \<times> ty Formula.agg_op \<times> Formula.trm \<times> nat \<times> nat"

fun eagg_p :: "eaggp \<Rightarrow> event_data table \<Rightarrow> event_data table" where
  "eagg_p (g0, \<omega>, f, k, pos) = uagg g0 \<omega> f k pos"

fun eagg_ok :: "eaggp \<Rightarrow> nat \<Rightarrow> bool" where
  "eagg_ok (g0, \<omega>, f, k, pos) w \<longleftrightarrow>
     k \<le> w \<and> pos \<le> w - k \<and> Formula.fv_trm f \<subseteq> {0..<w} \<and> (g0 \<longrightarrow> w = k)"

fun eagg_gcols :: "eaggp \<Rightarrow> nat \<Rightarrow> cols" where
  "eagg_gcols (g0, \<omega>, f, k, pos) w = [0..<pos] @ [Suc pos..<Suc (w - k)]"

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

subsubsection \<open>Position of the result column\<close>

text \<open>The kernel puts the result column in front of the group key, the executable order among the
  group's columns.\<close>

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

subsection \<open>Aggregate alongside the count set\<close>

text \<open>
  An added table contributes the tuples not yet in the union, a removed one the tuples it was the
  last to hold; the kernel's operations (@{text kag_}) specify the window's.
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

subsection \<open>Aggregate over the window's tuples\<close>

text \<open>
  Under @{text Rk}, the kernel's steps, folds, initial structure and result are those of
  @{typ "event_data gagg"}.
\<close>

fun Rk :: "event_data gagg \<Rightarrow> aggaux" where
  "Rk (GCnt m) = CntAux m"
| "Rk (GSum m) = SumAux m"
| "Rk (GRank m ty) = RankAux (m, ty)"

lemma insert_cnt_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
  shows "insert_cnt args t = gi_cnt k t"
  using assms by (intro ext) (auto simp: Let_def)

lemma insert_sum_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "insert_sum args t = gi_sum k ev t"
  using assms by (intro ext) (auto simp: Let_def)

lemma insert_rank_Rk:
  assumes "agg_key (length (aggargs_tys args)) (aggargs_cols args) t = drop k t"
    and "meval_trm (aggargs_cols args) (aggargs_f args) t = ev t"
  shows "insert_rank args ty t = gi_rank k ev ty t"
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

subsection \<open>Fused window\<close>

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

subsection \<open>Executable fused window\<close>

subsubsection \<open>Count mapping\<close>

text \<open>
  The fused window never hands out the union, so it keeps the count mapping without its key set;
  @{text ucc} recovers the count set.
\<close>

type_synonym ucnt = "(event_data list, nat) mapping"

definition ucnt_add1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> Mapping.update t 1 c
   | Some k \<Rightarrow> Mapping.update t (k + 1) c)"

definition ucnt_del1 :: "event_data list \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del1 t c = (case Mapping.lookup c t of
     None \<Rightarrow> c
   | Some k \<Rightarrow> (if k \<le> 1 then Mapping.delete t c else Mapping.update t (k - 1) c))"

definition ucnt_add :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_add T c = fold ucnt_add1 (csl T) c"

definition ucnt_del :: "event_data list set \<Rightarrow> ucnt \<Rightarrow> ucnt" where
  "ucnt_del T c = fold ucnt_del1 (csl T) c"

fun ucc :: "ucnt \<Rightarrow> cntset" where
  "ucc c = (c, Mapping.keys c)"

declare ucc.simps[simp del]

type_synonym ugagg = "event_data gagg"

definition uag_ins :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_ins p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gins k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = None) (csl T)) ax)"

definition uag_del :: "eaggp \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> ugagg option" where
  "uag_del p w T c ax = (case p of (g0, \<omega>, f, k, pos) \<Rightarrow>
     gdel k (umeval_trm f) (filter (\<lambda>t. Mapping.lookup c t = Some 1) (csl T)) ax)"

lemma ag_del_ucc[simp]: "ag_del p w T (ucc c) ax = uag_del p w T c ax"
  by (cases p) (simp add: ag_del_def uag_del_def ucc.simps)

subsubsection \<open>Guard of the node\<close>

text \<open>
  A constraint on the aggregate's value is carried by the node as a guard, so that the read
  inserts only the groups that pass.
\<close>

type_synonym uconstr = "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"

definition uqok :: "uconstr option \<Rightarrow> event_data list \<Rightarrow> bool" where
  "uqok q = (case q of None \<Rightarrow> (\<lambda>_. True) | Some c \<Rightarrow> ueval_constraint c)"

definition ufilt :: "uconstr option \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "ufilt q X = Set.filter (uqok q) X"

lemma uqok_None[simp]: "uqok None = (\<lambda>_. True)"
  by (simp add: uqok_def)

lemma ufilt_None[simp]: "ufilt None = id"
  by (simp add: ufilt_def fun_eq_iff)

lemma ufilt_idem[simp]: "ufilt q (ufilt q X) = ufilt q X"
  by (auto simp: ufilt_def)

text \<open>The code walks the mapping's entries, key and value together, without lookups.\<close>

definition ugmr :: "(event_data list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> event_data) \<Rightarrow>
    (event_data list, 'b) mapping \<Rightarrow> event_data list set" where
  "ugmr q p f m = Set.filter q (gmr p (\<lambda>x. x) f m)"

lemma fold_insert_filter_image:
  "fold (\<lambda>x A. let v = g x in if q v then Set.insert v A else A) xs A
   = Set.filter q (g ` set xs) \<union> A"
  by (induct xs arbitrary: A) (auto simp: Let_def)

lemma ugmr_code[code]:
  fixes t :: "(event_data list, 'b) mapping_rbt"
  shows "ugmr q p f (RBT_Mapping t) =
    (case ID CCOMPARE(event_data list) of
       None \<Rightarrow> Code.abort (STR ''ugmr RBT_Mapping: ccompare = None'')
                (\<lambda>_. ugmr q p f (RBT_Mapping t))
     | Some _ \<Rightarrow> fold (\<lambda>e A. let v = take p (fst e) @ f (snd e) # drop p (fst e)
                    in if q v then Set.insert v A else A)
                  (RBT_Mapping2.entries t) {})"
proof (cases "ID CCOMPARE(event_data list)")
  case (Some c)
  note comp = ID_ccompare'[OF Some]
  have dist: "distinct (map fst (RBT_Mapping2.entries t))"
    using Some by (transfer fixing: c)
      (simp add: ord.is_rbt_def linorder.distinct_entries[OF comparator.linorder[OF comp]])
  have mo: "map_of (RBT_Mapping2.entries t) (fst e) = Some (snd e)"
    if "e \<in> set (RBT_Mapping2.entries t)" for e
    using dist that by (cases e) simp
  have lk: "Mapping.lookup (RBT_Mapping t) = map_of (RBT_Mapping2.entries t)"
    by (simp add: lookup_Mapping_code(1) Some del: RBT_Mapping_def)
  have ky: "Mapping.keys (RBT_Mapping t) = fst ` set (RBT_Mapping2.entries t)"
    unfolding Mapping.keys_dom_lookup lk by (rule dom_map_of_conv_image_fst)
  have "ugmr q p f (RBT_Mapping t)
      = Set.filter q ((\<lambda>e. take p (fst e) @ f (snd e) # drop p (fst e))
          ` set (RBT_Mapping2.entries t))"
    unfolding ugmr_def gmr_def ky lk image_image
    by (intro arg_cong[of _ _ "Set.filter q"] image_cong[OF refl]) (simp add: mo)
  then show ?thesis using Some by (simp add: fold_insert_filter_image)
qed simp

definition ugres :: "(event_data list \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ty Formula.agg_op \<Rightarrow> nat \<Rightarrow> ugagg \<Rightarrow>
    event_data list set" where
  "ugres q g0 \<omega> p a = Set.filter q (gres g0 \<omega> p (\<lambda>x. x) a)"

lemma ugres_code[code]:
  "ugres q g0 \<omega> p a = (case a of
     GCnt m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else ugmr q p (\<lambda>k. EInt (integer_of_int k)) m)
   | GSum m \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Sum \<Rightarrow> ugmr q p (\<lambda>k. EInt (snd k)) m
       | Formula.Agg_Avg \<Rightarrow> ugmr q p
           (\<lambda>k. EFloat (double_of_event_data (EInt (snd k)) / double_of_int (fst k))) m
       | _ \<Rightarrow> {}))
   | GRank m ty \<Rightarrow> (if g0 \<and> Mapping.is_empty m then Set.filter q {[eval_agg_op \<omega> {}]}
       else (case fst \<omega> of
         Formula.Agg_Min \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k 0) m
       | Formula.Agg_Max \<Rightarrow> ugmr q p (\<lambda>k. get_edata_list k (get_length k - 1)) m
       | Formula.Agg_Med \<Rightarrow> ugmr q p (\<lambda>k. let u = get_length k; u' = u div 2;
           aggval = (if even u
             then (double_of_event_data_agg (get_edata_list k (u' - 1))
                   + double_of_event_data_agg (get_edata_list k u')) / double_of_int 2
             else double_of_event_data_agg (get_edata_list k u'))
           in EFloat aggval) m
       | _ \<Rightarrow> {})))"
  by (cases a) (simp_all add: ugres_def ugmr_def Mapping.is_empty_def
      split: Formula.agg_type.splits)

definition uag_res :: "uconstr option \<Rightarrow> eaggp \<Rightarrow> nat \<Rightarrow> ucnt \<Rightarrow>
    ugagg option \<Rightarrow> event_data list set" where
  "uag_res q p w c ax = ufilt q (case ax of
     None \<Rightarrow> eagg_p p (Mapping.keys c)
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> gres g0 \<omega> pos (\<lambda>x. x) a))"

lemma uag_res_code[code]:
  "uag_res q p w c ax = (case ax of
     None \<Rightarrow> ufilt q (eagg_p p (Mapping.keys c))
   | Some a \<Rightarrow> (case p of (g0, \<omega>, f, k, pos) \<Rightarrow> ugres (uqok q) g0 \<omega> pos a))"
  by (simp add: uag_res_def ugres_def ufilt_def split: option.splits prod.splits)

end
(*>*)
