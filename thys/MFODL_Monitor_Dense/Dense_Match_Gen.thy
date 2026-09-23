(*<*)
theory Dense_Match_Gen
  imports Dense_Aux Dense_Unbox
begin
(*>*)

section \<open>The past-match window over the operands' own frames\<close>

text \<open>
  The dense match node keeps the kernel's window at its own frame: every operand table is widened
  into the node's columns before the kernel's derivatives see it, and the window's tables are
  boxed tuples over those columns.  The window of @{theory MFODL_Monitor_Dense.Dense_Unbox} does
  without the widening -- an operand is probed by the semi-join against its mask -- and is
  polymorphic in the field type, so the short-tuple evaluator can run it over its own tuples.
  This theory shows that it computes, from the operands at their own frames, the narrowing of
  what the kernel computes: the relation @{const dmrd_rel} the dense node already keeps holds of
  it unchanged.

  Two things differ from the kernel's derivatives.  The join against an atom is a semi-join,
  which @{thm [source] dsemi_join} relates to the kernel's join; and the join of two lax epsilons
  is an intersection, which it is because both are tables over the node's columns.  The unit
  table, the tuple with every column blank, is the empty tuple: that is the narrowing of the
  kernel's only when the node has no columns, and a strict epsilon returns it only in that case,
  because it is a table over the node's columns (@{thm [source] table_reps_strict}).
\<close>

definition emb_msk :: "nat option list \<Rightarrow> bool list" where
  "emb_msk p = map (\<lambda>q. q \<noteq> None) p"

lemma emb_msk_emb_plan:
  assumes s1: "sorted_wrt (<) cs" and s2: "sorted_wrt (<) c" and sub: "set c \<subseteq> set cs"
  shows "emb_msk (emb_plan cs c) = dmsk cs c"
  by (rule nth_equalityI)
    (simp_all add: emb_msk_def emb_plan_def dmsk_def length_mrg_left_key[OF s1 s2 sub]
      nth_mrg_left_key[OF s1 s2 sub])

text \<open>At this type the window's lookup and tabulation are the kernel's.\<close>

lemma glookup_lookup: "glookup = (lookup :: (mregex, event_data table) mapping \<Rightarrow> _)"
  by (simp add: glookup_def Monitor.lookup_def empty_table_def)

lemma gmrtabulate_mrtabulate:
  "gmrtabulate xs (f :: mregex \<Rightarrow> event_data table) = mrtabulate xs f"
  by transfer (simp add: empty_table_def)

subsection \<open>The lax epsilon\<close>

lemma dmsk_self:
  assumes s: "sorted_wrt (<) cs"
  shows "\<forall>i \<in> set (dmsk cs cs). i" "length (dmsk cs cs) = length cs"
  using length_mrg_left_key[OF s s subset_refl] nth_mrg_left_key[OF s s subset_refl]
  by (fastforce simp: dmsk_def in_set_conv_nth)+

lemma dtabc_join_same:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and t1: "table n (set cs) A" and t2: "table n (set cs) B"
  shows "dtabc n cs (join A True B) = dtabc n cs A \<inter> dtabc n cs B"
proof -
  have e: "dtabc n cs (join A True B) = dsemi (dmsk cs cs) True (dtabc n cs A) (dtabc n cs B)"
    using dsemi_join[OF s s subset_refl b t1 t2, of True] by (simp add: dmsk_def)
  have l: "\<And>a. a \<in> dtabc n cs A \<Longrightarrow> length a = length (dmsk cs cs)"
    using dtable_dtabc[OF s b t1] dmsk_self(2)[OF s] by (auto simp: dtable_def dwf_tuple_def)
  have p: "\<And>a. a \<in> dtabc n cs A \<Longrightarrow> dproj (dmsk cs cs) a = a"
    using l dproj_all_True[OF dmsk_self(1)[OF s]] by metis
  show ?thesis unfolding e using p by (auto simp: dsemi_def)
qed

lemma dtabc_geps_lax:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and lc: "length css = length \<phi>s"
    and css: "\<And>i. i < length \<phi>s \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
       table n (set (css ! i)) (\<phi>s ! i)"
  shows "ok (length \<phi>s) mr \<Longrightarrow> table n (set cs) guard \<Longrightarrow>
     dtabc n cs (\<epsilon>_lax guard \<phi>s mr)
       = geps_lax (map (dmsk cs) css) (dtabc n cs guard) (map2 (dtabc n) css \<phi>s) mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: dtabc_def empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length \<phi>s" by simp
  have c: "sorted_wrt (<) (css ! i)" "set (css ! i) \<subseteq> set cs" "table n (set (css ! i)) (\<phi>s ! i)"
    using css[OF i] by simp_all
  show ?case using i lc dsemi_join[OF s c(1,2) b MTestPos(2) c(3), of True]
    by (simp add: dmsk_def)
next
  case (MTestNeg i)
  then have i: "i < length \<phi>s" by simp
  have c: "sorted_wrt (<) (css ! i)" "set (css ! i) \<subseteq> set cs" "table n (set (css ! i)) (\<phi>s ! i)"
    using css[OF i] by simp_all
  show ?case using i lc dsemi_join[OF s c(1,2) b MTestNeg(2) c(3), of False]
    by (simp add: dmsk_def)
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have opsA: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)" using css by blast
  have t1: "table n (set cs) (\<epsilon>_lax guard \<phi>s r)" by (rule table_eps_lax[OF opsA o1 MTimes(4)])
  have t2: "table n (set cs) (\<epsilon>_lax guard \<phi>s t)" by (rule table_eps_lax[OF opsA o2 MTimes(4)])
  show ?case using MTimes(1)[OF o1 MTimes(4)] MTimes(2)[OF o2 MTimes(4)]
    by (simp add: dtabc_join_same[OF s b t1 t2])
qed simp

subsection \<open>The strict epsilon and the derivative\<close>

lemma table_unit_table_Nil:
  "table n (set cs) (unit_table n) \<Longrightarrow> \<forall>c \<in> set cs. c < n \<Longrightarrow> cs = []"
  by (cases cs) (auto simp: table_def unit_table_def wf_tuple_def)

lemma sorted_cols_eq:
  "sorted_wrt (<) (xs :: cols) \<Longrightarrow> sorted_wrt (<) ys \<Longrightarrow> set xs = set ys \<Longrightarrow> xs = ys"
  by (metis sorted_distinct_set_unique strict_sorted_iff)

lemma dtabc_Nil_unit_table: "dtabc n [] (unit_table n) = {[]}"
  using dtabc_unit_table[of n] by (simp add: unit_table_def)

lemma dtabc_greps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and ops: "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"
    and lc: "length css = length \<psi>s"
    and css: "\<And>i. i < length \<psi>s \<Longrightarrow> sorted_wrt (<) (css ! i) \<and>
       set (css ! i) = Formula.fv (\<psi>s ! i) \<and> set (css ! i) \<subseteq> set cs"
  shows "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set cs = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     dtabc n cs (r\<epsilon>_strict n rels mr)
       = greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) mr"
proof (induct mr)
  case (MSkip m)
  have "cs = []" using MSkip(3) by simp
  then show ?case by (simp add: dtabc_Nil_unit_table dtabc_empty_iff empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length rels" and i': "i < length \<psi>s" using ops by (simp_all add: list_all2_lengthD)
  have "css ! i = cs" using css[OF i'] MTestPos(3) s by (intro sorted_cols_eq) simp_all
  then show ?case using i lc ops by (simp add: list_all2_lengthD)
next
  case (MTestNeg i)
  then have i: "i < length rels" and i': "i < length \<psi>s" using ops by (simp_all add: list_all2_lengthD)
  have t: "table n (set cs) (r\<epsilon>_strict n rels (MTestNeg i))"
    by (rule table_reps_strict[OF MTestNeg(1,2,3) ops])
  show ?case
  proof (cases "rels ! i = empty_table")
    case True
    then have "cs = []" using t b by (intro table_unit_table_Nil) simp_all
    then show ?thesis using True i i' lc
      by (simp add: dtabc_Nil_unit_table dtabc_empty_iff empty_table_def)
  next
    case False
    then show ?thesis using i i' lc by (simp add: dtabc_empty_iff empty_table_def)
  qed
next
  case (MPlus r t)
  have fvr: "set cs = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set cs = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have lr: "length \<psi>s = length rels" using ops by (simp add: list_all2_lengthD)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr1: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex r \<psi>s)"
    using MTimes(3) by simp
  have fvr: "set cs = fv_regex (from_mregex r \<psi>s)" using MTimes(3,5) by auto
  have tg: "table n (set cs) (r\<epsilon>_strict n rels r)"
    by (rule table_reps_strict[OF sr1 o1 fvr ops])
  have css': "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    using css ops lr by (auto simp: list_all2_conv_all_nth)
  show ?case
    using MTimes(1)[OF sr1 o1 fvr]
    by (simp add: dtabc_geps_lax[OF s b lc[unfolded lr] css' o2[unfolded lr] tg])
next
  case (MStar r)
  have t: "table n (set cs) (r\<epsilon>_strict n rels (MStar r))"
    by (rule table_reps_strict[OF MStar(2,3,4) ops])
  then have "cs = []" using b by (intro table_unit_table_Nil) simp_all
  then show ?case by (simp add: dtabc_Nil_unit_table)
qed

lemma dtabc_grdelta:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and lc: "length css = length \<phi>s"
    and css: "\<And>i. i < length \<phi>s \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
       table n (set (css ! i)) (\<phi>s ! i)"
    and X: "\<And>ms. table n (set cs) (lookup X ms)"
    and dX: "\<And>ms. glookup dX ms = dtabc n cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow>
     dtabc n cs (r\<delta> \<kappa> X \<phi>s mr) = grdelta (map (dmsk cs) css) \<kappa> dX (map2 (dtabc n) css \<phi>s) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) (simp_all add: dtabc_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have opsA: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)" using css by blast
  have tg: "table n (set cs) (r\<delta> \<kappa> X \<phi>s r)" by (rule table_rdelta[OF opsA X o1])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: dtabc_Un_img dtabc_geps_lax[OF s b lc css o2 tg])
qed (simp_all add: dtabc_def empty_table_def)

text \<open>The future window's two operations are the mirror images: the strict epsilon is strict on
  the right of a concatenation, and the derivative steps the left.\<close>

lemma dtabc_gleps_strict:
  fixes \<psi>s :: "ty Formula.formula list" and rels :: "event_data table list"
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and ops: "list_all2 (\<lambda>\<psi> rel. table n (Formula.fv \<psi>) rel) \<psi>s rels"
    and lc: "length css = length \<psi>s"
    and css: "\<And>i. i < length \<psi>s \<Longrightarrow> sorted_wrt (<) (css ! i) \<and>
       set (css ! i) = Formula.fv (\<psi>s ! i) \<and> set (css ! i) \<subseteq> set cs"
  shows "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<psi>s) \<Longrightarrow>
     ok (length \<psi>s) mr \<Longrightarrow> set cs = fv_regex (from_mregex mr \<psi>s) \<Longrightarrow>
     dtabc n cs (l\<epsilon>_strict n rels mr)
       = gleps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) mr"
proof (induct mr)
  case (MSkip m)
  have "cs = []" using MSkip(3) by simp
  then show ?case by (simp add: dtabc_Nil_unit_table dtabc_empty_iff empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length rels" and i': "i < length \<psi>s" using ops by (simp_all add: list_all2_lengthD)
  have "css ! i = cs" using css[OF i'] MTestPos(3) s by (intro sorted_cols_eq) simp_all
  then show ?case using i lc ops by (simp add: list_all2_lengthD)
next
  case (MTestNeg i)
  then have i: "i < length rels" and i': "i < length \<psi>s" using ops by (simp_all add: list_all2_lengthD)
  have t: "table n (set cs) (l\<epsilon>_strict n rels (MTestNeg i))"
    by (rule table_leps_strict[OF MTestNeg(1,2,3) ops])
  show ?case
  proof (cases "rels ! i = empty_table")
    case True
    then have "cs = []" using t b by (intro table_unit_table_Nil) simp_all
    then show ?thesis using True i i' lc
      by (simp add: dtabc_Nil_unit_table dtabc_empty_iff empty_table_def)
  next
    case False
    then show ?thesis using i i' lc by (simp add: dtabc_empty_iff empty_table_def)
  qed
next
  case (MPlus r t)
  have fvr: "set cs = fv_regex (from_mregex r \<psi>s)"
    and fvt: "set cs = fv_regex (from_mregex t \<psi>s)" using MPlus(3,5) by auto
  show ?case
    using MPlus(1)[OF _ _ fvr] MPlus(2)[OF _ _ fvt] MPlus(3,4)
    by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have lr: "length \<psi>s = length rels" using ops by (simp add: list_all2_lengthD)
  have o1: "ok (length \<psi>s) r" and o2: "ok (length \<psi>s) t" using MTimes(4) by simp_all
  have sr2: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex t \<psi>s)"
    using MTimes(3) by simp
  have fvt: "set cs = fv_regex (from_mregex t \<psi>s)" using MTimes(3,5) by auto
  have tg: "table n (set cs) (l\<epsilon>_strict n rels t)"
    by (rule table_leps_strict[OF sr2 o2 fvt ops])
  have css': "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    using css ops lr by (auto simp: list_all2_conv_all_nth)
  show ?case
    using MTimes(2)[OF sr2 o2 fvt]
    by (simp add: dtabc_geps_lax[OF s b lc[unfolded lr] css' o1[unfolded lr] tg])
next
  case (MStar r)
  have t: "table n (set cs) (l\<epsilon>_strict n rels (MStar r))"
    by (rule table_leps_strict[OF MStar(2,3,4) ops])
  then have "cs = []" using b by (intro table_unit_table_Nil) simp_all
  then show ?case by (simp add: dtabc_Nil_unit_table)
qed

lemma dtabc_gldelta:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and lc: "length css = length \<phi>s"
    and css: "\<And>i. i < length \<phi>s \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
       table n (set (css ! i)) (\<phi>s ! i)"
    and X: "\<And>ms. table n (set cs) (lookup X ms)"
    and dX: "\<And>ms. glookup dX ms = dtabc n cs (lookup X ms)"
  shows "ok (length \<phi>s) mr \<Longrightarrow>
     dtabc n cs (l\<delta> \<kappa> X \<phi>s mr) = gldelta (map (dmsk cs) css) \<kappa> dX (map2 (dtabc n) css \<phi>s) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  then show ?case using dX by (cases m) (simp_all add: dtabc_def empty_table_def)
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o1: "ok (length \<phi>s) r" and o2: "ok (length \<phi>s) t" using MTimes(3) by simp_all
  have opsA: "\<forall>i < length \<phi>s. \<exists>B \<subseteq> set cs. table n B (\<phi>s ! i)" using css by blast
  have tg: "table n (set cs) (l\<delta> \<kappa> X \<phi>s t)" by (rule table_ldelta[OF opsA X o2])
  show ?case using MTimes(1)[OF o1] MTimes(2)[OF o2]
    by (simp add: dtabc_Un_img dtabc_geps_lax[OF s b lc css o1 tg])
qed (simp_all add: dtabc_def empty_table_def)

subsection \<open>One firing of the window\<close>

text \<open>The frame of @{locale dmatchP_frame}, with each operand's own columns.\<close>

locale gmatchP_frame = dmatchP_frame n cs \<psi>s rels mrs for n cs \<psi>s rels mrs +
  fixes css :: "cols list"
  assumes lcss: "length css = length \<psi>s"
    and css: "\<And>i. i < length \<psi>s \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) = Formula.fv (\<psi>s ! i)"
begin

abbreviation "gmsks \<equiv> map (dmsk cs) css"
abbreviation "grels \<equiv> map2 (dtabc n) css rels"

lemma css_strict: "i < length \<psi>s \<Longrightarrow>
    sorted_wrt (<) (css ! i) \<and> set (css ! i) = Formula.fv (\<psi>s ! i) \<and> set (css ! i) \<subseteq> set cs"
  using css sub by auto

lemma css_lax: "i < length rels \<Longrightarrow>
    sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and> table n (set (css ! i)) (rels ! i)"
  using css sub ops lr by (auto simp: list_all2_conv_all_nth)

lemma lcss_rels: "length css = length rels"
  using lcss lr by simp

lemma gdtabT: "ms \<in> set mrs \<Longrightarrow> dtabc n cs (r\<epsilon>_strict n rels ms) = greps_strict gmsks grels ms"
  using mrsok by (intro dtabc_greps_strict[OF s b ops lcss css_strict]) auto

lemma gdtabc_lookup_head:
  "glookup (gmrtabulate mrs (greps_strict gmsks grels)) ms
     = dtabc n cs (lookup (mrtabulate mrs (r\<epsilon>_strict n rels)) ms)"
  by (cases "ms \<in> set mrs")
    (simp_all add: glookup_lookup gmrtabulate_mrtabulate lookup_tabulate[OF d] gdtabT
      empty_table_def)

lemma gdmrd_rel_head:
  "dmrd_rel n cs [(nt, mrtabulate mrs (r\<epsilon>_strict n rels))]
     [(nt, gmrtabulate mrs (greps_strict gmsks grels))]"
  using table_lookup_head gdtabc_lookup_head by (simp add: glookup_lookup)

lemma gdmrd_rel_step:
  assumes rel: "dmrd_rel n cs aux daux"
  shows "dmrd_rel n cs
     [(t, mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))).
        (t, X) \<leftarrow> aux, memR I (nt - t)]
     [(t, gmrtabulate mrs (\<lambda>ms. grdelta gmsks id X grels ms
          \<union> (if t = nt then greps_strict gmsks grels ms else {}))).
        (t, X) \<leftarrow> daux, memR I (nt - t)]"
  using rel
proof (induct rule: dmrd_rel_induct)
  case (Cons t X X' aux daux)
  have okms: "\<And>ms. ms \<in> set mrs \<Longrightarrow> ok (length rels) ms" using mrsok lr by auto
  have tD: "\<And>ms. ms \<in> set mrs \<Longrightarrow> table n (set cs) (r\<delta> id X rels ms)"
    using Cons(1) by (intro table_rdelta[OF _ _ okms]) (use opsB in auto)
  have tE: "\<And>ms. table n (set cs)
      (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))) ms)"
    using tD tabT by (auto simp: lookup_tabulate[OF d] table_Un)
  have tX: "\<And>ms. table n (set cs) (lookup X ms)" using Cons(1) by blast
  have dXe: "\<And>ms. glookup X' ms = dtabc n cs (lookup X ms)" using Cons(2) by (simp add: glookup_lookup)
  have dR: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc n cs (r\<delta> id X rels ms) = grdelta gmsks id X' grels ms"
    by (rule dtabc_grdelta[OF s b lcss_rels css_lax tX dXe okms])
  have dD: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc n cs (r\<delta> id X rels ms \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))
        = grdelta gmsks id X' grels ms \<union> (if t = nt then greps_strict gmsks grels ms else {})"
    by (cases "t = nt") (simp_all add: dtabc_Un_img dR gdtabT)
  have dE: "\<And>ms. lookup (mrtabulate mrs (\<lambda>ms. grdelta gmsks id X' grels ms
         \<union> (if t = nt then greps_strict gmsks grels ms else {}))) ms
      = dtabc n cs (lookup (mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms
         \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))) ms)"
    by (rule lookup_mrtabulate_cong[OF d dD])
  show ?case using Cons(4) tE dE by (simp add: gmrtabulate_mrtabulate)
qed simp

lemma dtabc_gupdate_matchP:
  assumes rel: "dmrd_rel n cs aux daux"
  shows "dtabc n cs (fst (update_matchP n I mr mrs rels nt aux))
       = fst (gupdate_matchP gmsks I mr mrs grels nt daux) \<and>
     dmrd_rel n cs (snd (update_matchP n I mr mrs rels nt aux))
       (snd (gupdate_matchP gmsks I mr mrs grels nt daux))"
proof -
  let ?W = "[(t, mrtabulate mrs (\<lambda>ms. r\<delta> id X rels ms
       \<union> (if t = nt then r\<epsilon>_strict n rels ms else {}))). (t, X) \<leftarrow> aux, memR I (nt - t)]"
  let ?D = "[(t, gmrtabulate mrs (\<lambda>ms. grdelta gmsks id X grels ms
       \<union> (if t = nt then greps_strict gmsks grels ms else {}))). (t, X) \<leftarrow> daux, memR I (nt - t)]"
  let ?H = "gmrtabulate mrs (greps_strict gmsks grels)"
  have st: "dmrd_rel n cs ?W ?D" by (rule gdmrd_rel_step[OF rel])
  have both: "dmrd_rel n cs
      (case ?W of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict n rels))]
       | x # w' \<Rightarrow> (if fst x = nt then x # w'
                   else (nt, mrtabulate mrs (r\<epsilon>_strict n rels)) # x # w'))
      (case ?D of [] \<Rightarrow> [(nt, ?H)]
       | x # w' \<Rightarrow> (if fst x = nt then x # w' else (nt, ?H) # x # w'))"
  proof (cases ?W)
    case Nil
    have DN: "?D = []" using dmrd_rel_length[OF st] unfolding Nil by simp
    show ?thesis unfolding Nil DN using gdmrd_rel_head by simp
  next
    case (Cons x w')
    have "length ?D = Suc (length w')" using dmrd_rel_length[OF st] unfolding Cons by simp
    then obtain y d' where D: "?D = y # d'" by (cases ?D) auto
    have rel': "dmrd_rel n cs (x # w') (y # d')" using st unfolding Cons D .
    show ?thesis unfolding Cons D
      using rel' table_lookup_head gdtabc_lookup_head
      by (cases x; cases y) (auto simp: glookup_lookup)
  qed
  have g: "gupdate_matchP gmsks I mr mrs grels nt daux =
      (let aux = (case ?D of [] \<Rightarrow> [(nt, ?H)]
         | x # w' \<Rightarrow> (if fst x = nt then x # w' else (nt, ?H) # x # w'))
       in (foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux, memL I (nt - t)] {}, aux))"
    unfolding gupdate_matchP_def glookup_lookup ..
  show ?thesis
    using both dtabc_foldr_lookup[OF both]
    by (simp add: update_matchP_def g Let_def)
qed

end

section \<open>The future-match window over the operands' own frames\<close>

text \<open>
  The future window keeps, for every time point it has not decided yet, the operands' tables at
  that time point and the result accumulated for it so far.  The dense node keeps the operands at
  their own frames, as the node receives them, and the result at the node's.
\<close>

definition gmld_rel :: "nat \<Rightarrow> cols \<Rightarrow> cols list \<Rightarrow> ty Formula.formula list \<Rightarrow>
    event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> bool" where
  "gmld_rel n cs css \<psi>s = list_all2 (\<lambda>(t, rls, rel) (t', drls, drel). t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table n (Formula.fv \<psi>) r) \<psi>s rls \<and>
     drls = map2 (dtabc n) css rls \<and> drel = dtabc n cs rel)"

lemma gmld_rel_Nil[simp]: "gmld_rel n cs css \<psi>s [] []"
  by (simp add: gmld_rel_def)

lemma gmld_rel_Cons[simp]:
  "gmld_rel n cs css \<psi>s ((t, rls, rel) # aux) ((t', drls, drel) # daux) \<longleftrightarrow> t = t' \<and>
     list_all2 (\<lambda>\<psi> r. table n (Formula.fv \<psi>) r) \<psi>s rls \<and>
     drls = map2 (dtabc n) css rls \<and> drel = dtabc n cs rel \<and> gmld_rel n cs css \<psi>s aux daux"
  by (simp add: gmld_rel_def)

lemma gmld_rel_induct[consumes 1, case_names Nil Cons]:
  assumes "gmld_rel n cs css \<psi>s aux daux"
    and "P [] []"
    and "\<And>t rls rel aux daux. list_all2 (\<lambda>\<psi> r. table n (Formula.fv \<psi>) r) \<psi>s rls \<Longrightarrow>
       gmld_rel n cs css \<psi>s aux daux \<Longrightarrow> P aux daux \<Longrightarrow>
       P ((t, rls, rel) # aux) ((t, map2 (dtabc n) css rls, dtabc n cs rel) # daux)"
  shows "P aux daux"
  using assms(1)[unfolded gmld_rel_def]
  by (induct rule: list_all2_induct) (use assms(2,3) in \<open>auto simp: gmld_rel_def\<close>)

text \<open>Reading the structure hands out the entries that have left the window, narrowed.\<close>

lemma dtabc_geval_matchF:
  assumes "gmld_rel n cs css \<psi>s aux daux"
  shows "fst (geval_matchF I mr nt daux) = map (dtabc n cs) (fst (eval_matchF I mr nt aux)) \<and>
     gmld_rel n cs css \<psi>s (snd (eval_matchF I mr nt aux)) (snd (geval_matchF I mr nt daux))"
  using assms
proof (induct rule: gmld_rel_induct)
  case (Cons t rls rel aux daux)
  obtain ys ax where e: "eval_matchF I mr nt aux = (ys, ax)"
    by (cases "eval_matchF I mr nt aux")
  obtain dys dax where de: "geval_matchF I mr nt daux = (dys, dax)"
    by (cases "geval_matchF I mr nt daux")
  have i1: "dys = map (dtabc n cs) ys" and i2: "gmld_rel n cs css \<psi>s ax dax"
    using Cons(3) unfolding e de by simp_all
  show ?case using Cons(1,2) i1 i2 by (simp add: e de)
qed simp

text \<open>The frame of @{locale dmatchF_frame}, with each operand's own columns.\<close>

locale gmatchF_frame = dmatchF_frame n cs \<psi>s mrs for n cs \<psi>s mrs +
  fixes css :: "cols list"
  assumes lcss: "length css = length \<psi>s"
    and css: "\<And>i. i < length \<psi>s \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) = Formula.fv (\<psi>s ! i)"
begin

abbreviation "fmsks \<equiv> map (dmsk cs) css"

lemma css_strict: "i < length \<psi>s \<Longrightarrow>
    sorted_wrt (<) (css ! i) \<and> set (css ! i) = Formula.fv (\<psi>s ! i) \<and> set (css ! i) \<subseteq> set cs"
  using css sub by auto

lemma css_lax: "wfrels rels \<Longrightarrow> i < length rels \<Longrightarrow>
    sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and> table n (set (css ! i)) (rels ! i)"
proof -
  assume w: "wfrels rels" and i: "i < length rels"
  have i': "i < length \<psi>s" using lr[OF w] i by simp
  show ?thesis using css[OF i'] sub[OF i'] w i' by (auto simp: list_all2_conv_all_nth)
qed

lemma lcss_rels: "wfrels rels \<Longrightarrow> length css = length rels"
  using lcss lr by simp

lemma gdtabL: "wfrels rels \<Longrightarrow> ms \<in> set mrs \<Longrightarrow>
    dtabc n cs (l\<epsilon>_strict n rels ms) = gleps_strict fmsks (map2 (dtabc n) css rels) ms"
  using mrsok by (intro dtabc_gleps_strict[OF s b _ lcss css_strict]) auto

lemma gdtabc_lookup_base:
  "wfrels rels \<Longrightarrow>
     glookup (gmrtabulate mrs (gleps_strict fmsks (map2 (dtabc n) css rels))) ms
       = dtabc n cs (lookup (mrtabulate mrs (l\<epsilon>_strict n rels)) ms)"
  by (cases "ms \<in> set mrs")
    (simp_all add: glookup_lookup gmrtabulate_mrtabulate lookup_tabulate[OF d] gdtabL
      empty_table_def)

lemma gdtabc_lookup_step:
  assumes rls: "wfrels rls" and X: "\<And>ms. table n (set cs) (lookup X ms)"
    and dX: "\<And>ms. glookup dX ms = dtabc n cs (lookup X ms)"
  shows "glookup (gmrtabulate mrs (gldelta fmsks id dX (map2 (dtabc n) css rls))) ms
       = dtabc n cs (lookup (mrtabulate mrs (l\<delta> id X rls)) ms)"
proof -
  have dL: "\<And>ms. ms \<in> set mrs \<Longrightarrow>
      dtabc n cs (l\<delta> id X rls ms) = gldelta fmsks id dX (map2 (dtabc n) css rls) ms"
    by (rule dtabc_gldelta[OF s b lcss_rels[OF rls] css_lax[OF rls] X dX okms[OF _ rls]])
  show ?thesis
    by (cases "ms \<in> set mrs")
      (simp_all add: glookup_lookup gmrtabulate_mrtabulate lookup_tabulate[OF d] dL
        empty_table_def)
qed

lemma gdtabc_matchF_foldr:
  assumes rels: "wfrels rels" and rel: "gmld_rel n cs css \<psi>s aux daux"
  shows "gmld_rel n cs css \<psi>s
       (fst (foldr (update_matchF_step I mr mrs nt) aux
          (update_matchF_base n I mr mrs rels nt)))
       (fst (foldr (gupdate_matchF_step fmsks I mr mrs nt) daux
          (gupdate_matchF_base fmsks I mr mrs (map2 (dtabc n) css rels) nt)))
     \<and> (\<forall>ms. table n (set cs)
          (lookup (snd (foldr (update_matchF_step I mr mrs nt) aux
             (update_matchF_base n I mr mrs rels nt))) ms))
     \<and> (\<forall>ms. glookup (snd (foldr (gupdate_matchF_step fmsks I mr mrs nt) daux
             (gupdate_matchF_base fmsks I mr mrs (map2 (dtabc n) css rels) nt))) ms
          = dtabc n cs (lookup (snd (foldr (update_matchF_step I mr mrs nt) aux
             (update_matchF_base n I mr mrs rels nt))) ms))"
  using rel
proof (induct rule: gmld_rel_induct)
  case Nil
  show ?case
    using rels table_lookup_base[OF rels] gdtabc_lookup_base[OF rels]
    by (simp add: update_matchF_base_def gupdate_matchF_base_def Let_def empty_table_def)
next
  case (Cons t rls rel aux daux)
  let ?G = "gupdate_matchF_base fmsks I mr mrs (map2 (dtabc n) css rels) nt"
  obtain A X where W: "foldr (update_matchF_step I mr mrs nt) aux
      (update_matchF_base n I mr mrs rels nt) = (A, X)"
    by (cases "foldr (update_matchF_step I mr mrs nt) aux
      (update_matchF_base n I mr mrs rels nt)")
  obtain DA DX where D: "foldr (gupdate_matchF_step fmsks I mr mrs nt) daux ?G = (DA, DX)"
    by (cases "foldr (gupdate_matchF_step fmsks I mr mrs nt) daux ?G")
  have IH: "gmld_rel n cs css \<psi>s A DA" and tX: "\<And>ms. table n (set cs) (lookup X ms)"
    and dXe: "\<And>ms. glookup DX ms = dtabc n cs (lookup X ms)"
    using Cons(3) unfolding W D by simp_all
  have tY: "\<forall>ms. table n (set cs) (lookup (mrtabulate mrs (l\<delta> id X rls)) ms)"
    using table_lookup_step[OF Cons(1) tX] by blast
  have dY: "\<forall>ms. glookup (gmrtabulate mrs (gldelta fmsks id DX (map2 (dtabc n) css rls))) ms
      = dtabc n cs (lookup (mrtabulate mrs (l\<delta> id X rls)) ms)"
    using gdtabc_lookup_step[OF Cons(1) tX dXe] by blast
  have E: "foldr (update_matchF_step I mr mrs nt) ((t, rls, rel) # aux)
      (update_matchF_base n I mr mrs rels nt)
      = update_matchF_step I mr mrs nt (t, rls, rel) (A, X)"
    unfolding W[symmetric] by simp
  have DE: "foldr (gupdate_matchF_step fmsks I mr mrs nt)
      ((t, map2 (dtabc n) css rls, dtabc n cs rel) # daux) ?G
      = gupdate_matchF_step fmsks I mr mrs nt (t, map2 (dtabc n) css rls, dtabc n cs rel) (DA, DX)"
    unfolding D[symmetric] by simp
  show ?case unfolding E DE
    using IH tY dY Cons(1)
    by (simp add: update_matchF_step_def gupdate_matchF_step_def Let_def dtabc_Un_img)
qed

lemma dtabc_gupdate_matchF:
  assumes rels: "wfrels rels" and rel: "gmld_rel n cs css \<psi>s aux daux"
  shows "gmld_rel n cs css \<psi>s (update_matchF n I mr mrs rels nt aux)
     (gupdate_matchF fmsks I mr mrs (map2 (dtabc n) css rels) nt daux)"
  using gdtabc_matchF_foldr[OF rels rel] by (simp add: update_matchF_def gupdate_matchF_def)

end

(*<*)
end
(*>*)
