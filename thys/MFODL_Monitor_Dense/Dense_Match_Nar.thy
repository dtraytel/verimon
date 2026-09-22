(*<*)
theory Dense_Match_Nar
  imports Dense_Trigger_Nar "MFODL_Monitor_Devel.Correctness"
begin
(*>*)

section \<open>The kernel's regular-expression operations at the narrow frame\<close>

text \<open>
  The two match nodes of the dense evaluator keep their tables at the node's own frame, and their
  operands' at the operands' frames.  The kernel's derivative operations keep everything at the
  formula's width.  This theory relates the two: each of @{const \<epsilon>_lax}, @{const r\<epsilon>_strict},
  @{const l\<epsilon>_strict}, @{const r\<delta>} and @{const l\<delta>}, narrowed to the node's frame, is the
  corresponding operation of @{theory MFODL_Monitor_Dense.Dense_Unbox} on the narrowed operands.

  Two clauses do not narrow on their own, and they are the two the generic operations were
  written for.  The lax epsilon joins its guard -- a table over the node's frame -- with an
  atom's table, whose frame is a subset of it; that is @{const join} over wide tuples and
  @{const dsemi} against the atom's mask over short ones, which is @{thm [source] dsemi_join}.
  And the two strict epsilons return the unit table at an empty skip and at a star, which stands
  for every valuation and has no short form; the safety condition forces the node's frame to be
  empty wherever it arises, and there the unit table is the one empty tuple.

  The material is here, upstream of the evaluator, for the reason
  @{theory MFODL_Monitor_Dense.Dense_Trigger_Nar} gives for the trigger's: the evaluator's own
  match nodes carry the narrow structures and so need these lemmas before themselves.
\<close>

subsection \<open>The frames a safe regular expression's operations stay in\<close>

text \<open>Every table the operations below build is over the node's frame.  For the lax epsilon that
  is immediate -- it only ever filters its guard -- and it is the fact the intersection clause
  needs in order to be an intersection.\<close>

lemma table_join_sub:
  fixes X Y :: "'a table"
  assumes tX: "table n A X" and tY: "table n B Y" and sub: "B \<subseteq> A"
  shows "table n A (join X b Y)"
  by (rule join_table[of n A X B Y b A]) (use assms in auto)

lemma table_eps_lax:
  assumes ops: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> A. table n B (rels ! i)"
  shows "ok (length rels) mr \<Longrightarrow> table n A guard \<Longrightarrow> table n A (\<epsilon>_lax guard rels mr)"
proof (induct mr)
  case (MSkip m)
  then show ?case by (simp add: table_def empty_table_def)
next
  case (MTestPos i)
  then obtain B where s: "B \<subseteq> A" and t: "table n B (rels ! i)" using ops by auto
  show ?case using table_join_sub[OF _ t s, of guard True] MTestPos(2) by simp
next
  case (MTestNeg i)
  then obtain B where s: "B \<subseteq> A" and t: "table n B (rels ! i)" using ops by auto
  show ?case using table_join_sub[OF _ t s, of guard False] MTestNeg(2) by simp
next
  case (MPlus r s)
  then have "table n A (\<epsilon>_lax guard rels r)" and "table n A (\<epsilon>_lax guard rels s)" by auto
  then show ?case by (auto simp: table_def)
next
  case (MTimes r s)
  then have "table n A (\<epsilon>_lax guard rels r)" and "table n A (\<epsilon>_lax guard rels s)" by auto
  then show ?case using table_join_sub[where A = A and B = A] by simp
next
  case (MStar r)
  then show ?case by simp
qed

text \<open>Over one frame the natural join is the intersection: every tuple of either side is already
  complete on the columns the other tests.\<close>

lemma join_same_frame:
  assumes t1: "table n A T" and t2: "table n A T'"
  shows "join T True T' = T \<inter> T'"
proof -
  have "join T True T' = {a \<in> T. (proj_tuple (join_mask n A) a \<in> T') = True}"
    using join_sub[OF subset_refl t2 t1] by (simp add: proj_tuple_in_join_def join_cond_eq)
  moreover have "proj_tuple (join_mask n A) a = a" if "a \<in> T" for a
    using t1 that by (intro wf_tuple_proj_idle) (simp add: table_def)
  ultimately show ?thesis by auto
qed

subsection \<open>The lax epsilon\<close>

lemma dtabc_eps_lax:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    and len: "length css = length rels"
  shows "ok (length rels) mr \<Longrightarrow> table n (set cs) guard \<Longrightarrow>
    dtabc n cs (\<epsilon>_lax guard rels mr)
      = geps_lax (map (dmsk cs) css) (dtabc n cs guard) (map2 (dtabc n) css rels) mr"
proof (induct mr arbitrary: guard)
  case (MSkip m)
  then show ?case by (simp add: empty_table_def)
next
  case (MTestPos i)
  then have i: "i < length rels" by simp
  note c = css[OF i]
  have l: "dtabc n cs (\<epsilon>_lax guard rels (MTestPos i))
      = dsemi (dmsk cs (css ! i)) True (dtabc n cs guard) (dtabc n (css ! i) (rels ! i))"
    unfolding \<epsilon>_lax.simps dmsk_def
    by (rule dsemi_join[OF s _ _ b, symmetric]) (use c MTestPos(2) in auto)
  have r: "geps_lax (map (dmsk cs) css) (dtabc n cs guard) (map2 (dtabc n) css rels) (MTestPos i)
      = dsemi (dmsk cs (css ! i)) True (dtabc n cs guard) (dtabc n (css ! i) (rels ! i))"
    using i len by simp
  show ?case unfolding l r ..
next
  case (MTestNeg i)
  then have i: "i < length rels" by simp
  note c = css[OF i]
  have l: "dtabc n cs (\<epsilon>_lax guard rels (MTestNeg i))
      = dsemi (dmsk cs (css ! i)) False (dtabc n cs guard) (dtabc n (css ! i) (rels ! i))"
    unfolding \<epsilon>_lax.simps dmsk_def
    by (rule dsemi_join[OF s _ _ b, symmetric]) (use c MTestNeg(2) in auto)
  have r: "geps_lax (map (dmsk cs) css) (dtabc n cs guard) (map2 (dtabc n) css rels) (MTestNeg i)
      = dsemi (dmsk cs (css ! i)) False (dtabc n cs guard) (dtabc n (css ! i) (rels ! i))"
    using i len by simp
  show ?case unfolding l r ..
next
  case (MPlus r t)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r t)
  have o: "\<exists>B \<subseteq> set cs. table n B (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have t1: "table n (set cs) (\<epsilon>_lax guard rels r)"
    using MTimes by (intro table_eps_lax[OF o]) simp_all
  have t2: "table n (set cs) (\<epsilon>_lax guard rels t)"
    using MTimes by (intro table_eps_lax[OF o]) simp_all
  show ?case using MTimes
    by (simp add: join_same_frame[OF t1 t2] dtabc_Int[OF s t1 t2])
next
  case (MStar r)
  then show ?case by simp
qed

subsection \<open>Where the unit table may arise\<close>

text \<open>
  The two strict epsilons return the unit table at an empty skip, at a negative test that fails,
  and at a star.  It is a table over the node's frame only when that frame is empty, and the
  safety condition forces it to be: a star or an empty skip that could match the empty word while
  the node still binds a variable would make the formula unsafe.  Rather than carry the safety
  condition through the narrowing induction, the two predicates below say exactly what the
  induction needs of the regular expression -- that the frame is empty wherever the unit table
  arises, and that an atom read by itself is one at the node's own frame -- and the evaluator
  supplies them from safety downstream.
\<close>

fun mrn_okr :: "cols \<Rightarrow> cols list \<Rightarrow> mregex \<Rightarrow> bool" where
  "mrn_okr cs css (MSkip m) \<longleftrightarrow> (m \<noteq> 0 \<or> cs = [])"
| "mrn_okr cs css (MTestPos i) \<longleftrightarrow> css ! i = cs"
| "mrn_okr cs css (MTestNeg i) \<longleftrightarrow> cs = []"
| "mrn_okr cs css (MPlus r s) \<longleftrightarrow> mrn_okr cs css r \<and> mrn_okr cs css s"
| "mrn_okr cs css (MTimes r s) \<longleftrightarrow> mrn_okr cs css r"
| "mrn_okr cs css (MStar r) \<longleftrightarrow> cs = []"

fun mrn_okl :: "cols \<Rightarrow> cols list \<Rightarrow> mregex \<Rightarrow> bool" where
  "mrn_okl cs css (MSkip m) \<longleftrightarrow> (m \<noteq> 0 \<or> cs = [])"
| "mrn_okl cs css (MTestPos i) \<longleftrightarrow> css ! i = cs"
| "mrn_okl cs css (MTestNeg i) \<longleftrightarrow> cs = []"
| "mrn_okl cs css (MPlus r s) \<longleftrightarrow> mrn_okl cs css r \<and> mrn_okl cs css s"
| "mrn_okl cs css (MTimes r s) \<longleftrightarrow> mrn_okl cs css s"
| "mrn_okl cs css (MStar r) \<longleftrightarrow> cs = []"

lemma table_unit_table: "table n {} (unit_table n)"
  by (simp add: table_def unit_table_def wf_tuple_def)

lemma dtabc_Nil_unit_table: "dtabc n [] (unit_table n) = {[]}"
  using dtabc_unit_table[of n] by (simp add: unit_table_def)

text \<open>Narrowing preserves emptiness in both directions, which is what the negative test needs;
  the fact is @{thm [source] dtabc_empty_iff}, and it is a good simplification here.\<close>

declare dtabc_empty_iff[simp]

subsection \<open>The strict epsilons\<close>

lemma table_reps_strict:
  assumes ops: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (rels ! i)"
    and at: "\<And>i. i < length rels \<Longrightarrow> table n (set (css ! i)) (rels ! i)"
  shows "ok (length rels) mr \<Longrightarrow> mrn_okr cs css mr \<Longrightarrow>
    table n (set cs) (r\<epsilon>_strict n rels mr)"
proof (induct mr)
  case (MSkip m)
  then show ?case by (auto simp: table_def empty_table_def unit_table_def wf_tuple_def)
next
  case (MTestPos i)
  then show ?case using at[of i] by simp
next
  case (MTestNeg i)
  then show ?case by (simp add: table_def empty_table_def unit_table_def wf_tuple_def)
next
  case (MPlus r s)
  then show ?case by (auto simp: table_def)
next
  case (MTimes r s)
  then show ?case by (auto intro!: table_eps_lax[OF ops])
next
  case (MStar r)
  then show ?case by (simp add: table_def unit_table_def wf_tuple_def)
qed

lemma table_leps_strict:
  assumes ops: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (rels ! i)"
    and at: "\<And>i. i < length rels \<Longrightarrow> table n (set (css ! i)) (rels ! i)"
  shows "ok (length rels) mr \<Longrightarrow> mrn_okl cs css mr \<Longrightarrow>
    table n (set cs) (l\<epsilon>_strict n rels mr)"
proof (induct mr)
  case (MSkip m)
  then show ?case by (auto simp: table_def empty_table_def unit_table_def wf_tuple_def)
next
  case (MTestPos i)
  then show ?case using at[of i] by simp
next
  case (MTestNeg i)
  then show ?case by (simp add: table_def empty_table_def unit_table_def wf_tuple_def)
next
  case (MPlus r s)
  then show ?case by (auto simp: table_def)
next
  case (MTimes r s)
  then show ?case by (auto intro!: table_eps_lax[OF ops])
next
  case (MStar r)
  then show ?case by (simp add: table_def unit_table_def wf_tuple_def)
qed

lemma dtabc_reps_strict:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    and len: "length css = length rels"
  shows "ok (length rels) mr \<Longrightarrow> mrn_okr cs css mr \<Longrightarrow>
    dtabc n cs (r\<epsilon>_strict n rels mr)
      = greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (auto simp: empty_table_def dtabc_Nil_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" and e: "css ! i = cs" by simp_all
  have z: "map2 (dtabc n) css rels ! i = dtabc n (css ! i) (rels ! i)" using i len by simp
  show ?case using e by (simp add: z)
next
  case (MTestNeg i)
  then have i: "i < length rels" and e: "cs = []" by simp_all
  have z: "map2 (dtabc n) css rels ! i = dtabc n (css ! i) (rels ! i)" using i len by simp
  show ?case using e
    by (simp add: z empty_table_def dtabc_Nil_unit_table del: dtabc_empty_iff)
      (simp add: dtabc_def)
next
  case (MPlus r s)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r s)
  have o: "\<exists>B \<subseteq> set cs. table n B (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have at: "table n (set (css ! i)) (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have tg: "table n (set cs) (r\<epsilon>_strict n rels r)"
    using MTimes by (intro table_reps_strict[OF o at]) simp_all
  show ?case using MTimes
    by (simp add: dtabc_eps_lax[OF s b css len _ tg])
next
  case (MStar r)
  then show ?case by (simp add: dtabc_Nil_unit_table)
qed

lemma dtabc_leps_strict:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    and len: "length css = length rels"
  shows "ok (length rels) mr \<Longrightarrow> mrn_okl cs css mr \<Longrightarrow>
    dtabc n cs (l\<epsilon>_strict n rels mr)
      = gleps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) mr"
proof (induct mr)
  case (MSkip m)
  then show ?case by (auto simp: empty_table_def dtabc_Nil_unit_table)
next
  case (MTestPos i)
  then have i: "i < length rels" and e: "css ! i = cs" by simp_all
  have z: "map2 (dtabc n) css rels ! i = dtabc n (css ! i) (rels ! i)" using i len by simp
  show ?case using e by (simp add: z)
next
  case (MTestNeg i)
  then have i: "i < length rels" and e: "cs = []" by simp_all
  have z: "map2 (dtabc n) css rels ! i = dtabc n (css ! i) (rels ! i)" using i len by simp
  show ?case using e
    by (simp add: z empty_table_def dtabc_Nil_unit_table del: dtabc_empty_iff)
      (simp add: dtabc_def)
next
  case (MPlus r s)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r s)
  have o: "\<exists>B \<subseteq> set cs. table n B (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have at: "table n (set (css ! i)) (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have tg: "table n (set cs) (l\<epsilon>_strict n rels s)"
    using MTimes by (intro table_leps_strict[OF o at]) simp_all
  show ?case using MTimes
    by (simp add: dtabc_eps_lax[OF s b css len _ tg])
next
  case (MStar r)
  then show ?case by (simp add: dtabc_Nil_unit_table)
qed

subsection \<open>The mapping the two derivatives read\<close>

text \<open>
  Both derivatives read the previous time point's tables out of a mapping keyed by regular
  expression, and the match nodes keep such mappings in their auxiliary structures.  The
  narrowing need not identify the two mappings: it is enough that every key reads the narrowed
  table, which is what the predicate below says.  The tabulation that builds them preserves that,
  because a table is empty exactly when its narrowing is -- the condition under which either
  tabulation drops a key.
\<close>

definition dmapr :: "nat \<Rightarrow> cols \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow>
    (mregex, 'a table) mapping \<Rightarrow> bool" where
  "dmapr n cs X gX \<longleftrightarrow> (\<forall>k. glookup gX k = dtabc n cs (lookup X k))"

lemma dmaprD: "dmapr n cs X gX \<Longrightarrow> glookup gX k = dtabc n cs (lookup X k)"
  by (simp add: dmapr_def)

lemma glookup_gmrtabulate:
  "distinct xs \<Longrightarrow> glookup (gmrtabulate xs f) x = (if x \<in> set xs then f x else {})"
  unfolding glookup_def lookup_default_def
  by transfer (auto simp: Let_def map_filter_def map_of_eq_None_iff o_def image_image
      dest!: map_of_SomeD split: if_splits option.splits)

lemma dmapr_mrtabulate:
  assumes d: "distinct mrs" and g: "\<And>k. k \<in> set mrs \<Longrightarrow> g k = dtabc n cs (f k)"
  shows "dmapr n cs (mrtabulate mrs f) (gmrtabulate mrs g)"
  unfolding dmapr_def
  by (auto simp: glookup_gmrtabulate[OF d] lookup_tabulate[OF d] g)

subsection \<open>The two derivatives\<close>

text \<open>
  The derivatives are the one place where a table from the previous time point enters, and they
  bring it in at the node's own frame -- the mapping's entries are the strict epsilons and the
  previous derivatives, all of them tables over that frame.  Everything else is a union, an
  empty table, or a lax epsilon whose guard is the derivative built so far, so the narrowing
  commutes clause by clause with no side condition on the regular expression: the unit table
  never arises here.
\<close>

lemma table_Un: "table n A X \<Longrightarrow> table n A Y \<Longrightarrow> table n A (X \<union> Y)"
  by (auto simp: table_def)

lemma table_rdelta:
  assumes ops: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (rels ! i)"
    and X: "\<And>k. table n (set cs) (lookup X k)"
  shows "ok (length rels) mr \<Longrightarrow> table n (set cs) (r\<delta> \<kappa> X rels mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  show ?case using X by (cases m) (auto simp: empty_table_def table_def)
next
  case (MTestPos i)
  then show ?case by (simp add: empty_table_def table_def)
next
  case (MTestNeg i)
  then show ?case by (simp add: empty_table_def table_def)
next
  case (MPlus r s)
  then show ?case by (auto intro!: table_Un)
next
  case (MTimes r s)
  then show ?case by (auto intro!: table_Un table_eps_lax[OF ops])
next
  case (MStar r)
  then show ?case by auto
qed

lemma table_ldelta:
  assumes ops: "\<And>i. i < length rels \<Longrightarrow> \<exists>B \<subseteq> set cs. table n B (rels ! i)"
    and X: "\<And>k. table n (set cs) (lookup X k)"
  shows "ok (length rels) mr \<Longrightarrow> table n (set cs) (l\<delta> \<kappa> X rels mr)"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  show ?case using X by (cases m) (auto simp: empty_table_def table_def)
next
  case (MTestPos i)
  then show ?case by (simp add: empty_table_def table_def)
next
  case (MTestNeg i)
  then show ?case by (simp add: empty_table_def table_def)
next
  case (MPlus r s)
  then show ?case by (auto intro!: table_Un)
next
  case (MTimes r s)
  then show ?case by (auto intro!: table_Un table_eps_lax[OF ops])
next
  case (MStar r)
  then show ?case by auto
qed

lemma dtabc_rdelta:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    and len: "length css = length rels"
    and X: "\<And>k. table n (set cs) (lookup X k)"
    and gX: "dmapr n cs X gX"
  shows "ok (length rels) mr \<Longrightarrow>
    dtabc n cs (r\<delta> \<kappa> X rels mr)
      = grdelta (map (dmsk cs) css) \<kappa> gX (map2 (dtabc n) css rels) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  show ?case by (cases m) (simp_all add: empty_table_def dmaprD[OF gX])
next
  case (MTestPos i)
  show ?case by (simp add: empty_table_def)
next
  case (MTestNeg i)
  show ?case by (simp add: empty_table_def)
next
  case (MPlus r s)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r s)
  have o: "\<exists>B \<subseteq> set cs. table n B (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have okr: "ok (length rels) r" using MTimes by simp
  have tg: "table n (set cs) (r\<delta> \<kappa>' X rels r)" for \<kappa>'
    by (rule table_rdelta[OF o X okr])
  show ?case using MTimes
    by (simp add: dtabc_Un_img dtabc_eps_lax[OF s b css len _ tg])
next
  case (MStar r)
  then show ?case by simp
qed

lemma dtabc_ldelta:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    and len: "length css = length rels"
    and X: "\<And>k. table n (set cs) (lookup X k)"
    and gX: "dmapr n cs X gX"
  shows "ok (length rels) mr \<Longrightarrow>
    dtabc n cs (l\<delta> \<kappa> X rels mr)
      = gldelta (map (dmsk cs) css) \<kappa> gX (map2 (dtabc n) css rels) mr"
proof (induct mr arbitrary: \<kappa>)
  case (MSkip m)
  show ?case by (cases m) (simp_all add: empty_table_def dmaprD[OF gX])
next
  case (MTestPos i)
  show ?case by (simp add: empty_table_def)
next
  case (MTestNeg i)
  show ?case by (simp add: empty_table_def)
next
  case (MPlus r s)
  then show ?case by (simp add: dtabc_Un_img)
next
  case (MTimes r s)
  have o: "\<exists>B \<subseteq> set cs. table n B (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have oks: "ok (length rels) s" using MTimes by simp
  have tg: "table n (set cs) (l\<delta> \<kappa>' X rels s)" for \<kappa>'
    by (rule table_ldelta[OF o X oks])
  show ?case using MTimes
    by (simp add: dtabc_Un_img dtabc_eps_lax[OF s b css len _ tg])
next
  case (MStar r)
  then show ?case by simp
qed

subsection \<open>The matchP node's auxiliary structure\<close>

text \<open>
  The past match node keeps one mapping per time point still in the window, and at each step it
  rebuilds every one of them from the previous derivative and, at the current time point, the
  strict epsilon.  The narrowed structure is the same list with every mapping narrowed, which the
  relation below says, and the invariant the derivative needs -- that every entry is a table over
  the node's frame -- travels with it.
\<close>

definition dmtab :: "nat \<Rightarrow> cols \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> bool" where
  "dmtab n cs X \<longleftrightarrow> (\<forall>k. table n (set cs) (lookup X k))"

lemma dmtabD: "dmtab n cs X \<Longrightarrow> table n (set cs) (lookup X k)"
  by (simp add: dmtab_def)

lemma dmtab_mrtabulate:
  assumes d: "distinct mrs" and f: "\<And>k. k \<in> set mrs \<Longrightarrow> table n (set cs) (f k)"
  shows "dmtab n cs (mrtabulate mrs f)"
  using f by (auto simp: dmtab_def lookup_tabulate[OF d] table_def empty_table_def)

fun dmrdaux :: "nat \<Rightarrow> cols \<Rightarrow> 'a mr\<delta>aux \<Rightarrow> 'a mr\<delta>aux \<Rightarrow> bool" where
  "dmrdaux n cs [] gaux \<longleftrightarrow> gaux = []"
| "dmrdaux n cs (x # aux) gaux \<longleftrightarrow> (case gaux of [] \<Rightarrow> False | y # gaux' \<Rightarrow>
     fst y = fst x \<and> dmtab n cs (snd x) \<and> dmapr n cs (snd x) (snd y) \<and>
     dmrdaux n cs aux gaux')"

text \<open>The three shapes the update goes through: rebuilding every entry, prefixing the current
  time point's own tabulation, and reading the window's union out again.\<close>

lemma dmrdaux_map_step:
  assumes a: "dmrdaux n cs aux gaux"
    and F: "\<And>t Y gY. dmtab n cs Y \<Longrightarrow> dmapr n cs Y gY \<Longrightarrow>
      dmtab n cs (F t Y) \<and> dmapr n cs (F t Y) (G t gY)"
  shows "dmrdaux n cs [(t, F t X). (t, X) \<leftarrow> aux, P t] [(t, G t gX). (t, gX) \<leftarrow> gaux, P t]"
  using a
proof (induct aux arbitrary: gaux)
  case Nil
  then show ?case by simp
next
  case (Cons x aux)
  from Cons.prems obtain y gaux' where g: "gaux = y # gaux'"
    and ty: "fst y = fst x" and h1: "dmtab n cs (snd x)" and h2: "dmapr n cs (snd x) (snd y)"
    and tl: "dmrdaux n cs aux gaux'"
    by (cases gaux) auto
  have IH: "dmrdaux n cs [(t, F t X). (t, X) \<leftarrow> aux, P t] [(t, G t gX). (t, gX) \<leftarrow> gaux', P t]"
    by (rule Cons.hyps[OF tl])
  show ?case using F[OF h1 h2] IH ty g by (cases x; cases y) auto
qed

lemma dmrdaux_insert_new:
  assumes a: "dmrdaux n cs A gA" and E: "dmtab n cs E" and gE: "dmapr n cs E gE"
  shows "dmrdaux n cs
      (case A of [] \<Rightarrow> [(nt, E)]
       | x # A' \<Rightarrow> if fst x = nt then x # A' else (nt, E) # x # A')
      (case gA of [] \<Rightarrow> [(nt, gE)]
       | y # gA' \<Rightarrow> if fst y = nt then y # gA' else (nt, gE) # y # gA')"
  using a E gE by (cases A; cases gA) auto

lemma dtabc_foldr_lookup:
  "dmrdaux n cs aux gaux \<Longrightarrow>
    dtabc n cs (foldr (\<union>) [lookup X k. (t, X) \<leftarrow> aux, P t] {})
      = foldr (\<union>) [glookup gX k. (t, gX) \<leftarrow> gaux, P t] {}"
proof (induct aux arbitrary: gaux)
  case Nil
  then show ?case by simp
next
  case (Cons x aux)
  from Cons.prems obtain y gaux' where g: "gaux = y # gaux'"
    and ty: "fst y = fst x" and h2: "dmapr n cs (snd x) (snd y)"
    and tl: "dmrdaux n cs aux gaux'"
    by (cases gaux) auto
  show ?case using Cons.hyps[OF tl] dmaprD[OF h2] ty g
    by (cases x; cases y) (auto simp: dtabc_Un_img)
qed

text \<open>Hence the update itself: the window's union narrows to the generic one, and the new
  auxiliary structure is again related.\<close>

lemma update_matchP_narrow:
  assumes s: "sorted_wrt (<) cs" and b: "\<forall>c \<in> set cs. c < n"
    and css: "\<And>i. i < length rels \<Longrightarrow> sorted_wrt (<) (css ! i) \<and> set (css ! i) \<subseteq> set cs \<and>
      table n (set (css ! i)) (rels ! i)"
    and len: "length css = length rels"
    and d: "distinct mrs"
    and okm: "\<And>m. m \<in> set mrs \<Longrightarrow> ok (length rels) m"
    and okn: "\<And>m. m \<in> set mrs \<Longrightarrow> mrn_okr cs css m"
    and a: "dmrdaux n cs aux gaux"
  shows "dtabc n cs (fst (update_matchP n I mr mrs rels nt aux))
       = fst (gupdate_matchP (map (dmsk cs) css) I mr mrs (map2 (dtabc n) css rels) nt gaux)"
    and "dmrdaux n cs (snd (update_matchP n I mr mrs rels nt aux))
       (snd (gupdate_matchP (map (dmsk cs) css) I mr mrs (map2 (dtabc n) css rels) nt gaux))"
proof -
  have o: "\<exists>B \<subseteq> set cs. table n B (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have at: "table n (set (css ! i)) (rels ! i)" if "i < length rels" for i
    using css[OF that] by blast
  have te: "table n (set cs) (r\<epsilon>_strict n rels k)" if "k \<in> set mrs" for k
    by (rule table_reps_strict[OF o at okm[OF that] okn[OF that]])
  have de: "dtabc n cs (r\<epsilon>_strict n rels k)
      = greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) k" if "k \<in> set mrs" for k
    by (rule dtabc_reps_strict[OF s b css len okm[OF that] okn[OF that]])
  have E: "dmtab n cs (mrtabulate mrs (r\<epsilon>_strict n rels))"
    by (rule dmtab_mrtabulate[OF d]) (simp add: te)
  have gE: "dmapr n cs (mrtabulate mrs (r\<epsilon>_strict n rels))
      (gmrtabulate mrs (greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels)))"
    by (rule dmapr_mrtabulate[OF d]) (simp add: de)
  have step: "dmtab n cs (mrtabulate mrs (\<lambda>m. r\<delta> id Y rels m \<union>
        (if t = nt then r\<epsilon>_strict n rels m else {}))) \<and>
      dmapr n cs (mrtabulate mrs (\<lambda>m. r\<delta> id Y rels m \<union>
        (if t = nt then r\<epsilon>_strict n rels m else {})))
        (gmrtabulate mrs (\<lambda>m. grdelta (map (dmsk cs) css) id gY (map2 (dtabc n) css rels) m \<union>
          (if t = nt then greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) m else {})))"
    if tY: "dmtab n cs Y" and rY: "dmapr n cs Y gY" for t Y gY
  proof
    show "dmtab n cs (mrtabulate mrs (\<lambda>m. r\<delta> id Y rels m \<union>
        (if t = nt then r\<epsilon>_strict n rels m else {})))"
    proof (rule dmtab_mrtabulate[OF d])
      fix k assume k: "k \<in> set mrs"
      have 1: "table n (set cs) (r\<delta> id Y rels k)"
        by (rule table_rdelta[OF o dmtabD[OF tY] okm[OF k]])
      have 2: "table n (set cs) (if t = nt then r\<epsilon>_strict n rels k else {})"
        using te[OF k] by (simp add: table_def)
      show "table n (set cs) (r\<delta> id Y rels k \<union> (if t = nt then r\<epsilon>_strict n rels k else {}))"
        by (rule table_Un[OF 1 2])
    qed
  next
    show "dmapr n cs (mrtabulate mrs (\<lambda>m. r\<delta> id Y rels m \<union>
        (if t = nt then r\<epsilon>_strict n rels m else {})))
        (gmrtabulate mrs (\<lambda>m. grdelta (map (dmsk cs) css) id gY (map2 (dtabc n) css rels) m \<union>
          (if t = nt then greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) m else {})))"
    proof (rule dmapr_mrtabulate[OF d])
      fix k assume k: "k \<in> set mrs"
      show "grdelta (map (dmsk cs) css) id gY (map2 (dtabc n) css rels) k \<union>
          (if t = nt then greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) k else {})
        = dtabc n cs (r\<delta> id Y rels k \<union> (if t = nt then r\<epsilon>_strict n rels k else {}))"
        by (simp add: dtabc_Un_img de[OF k]
            dtabc_rdelta[OF s b css len dmtabD[OF tY] rY okm[OF k]])
    qed
  qed
  have M: "dmrdaux n cs
      [(t, mrtabulate mrs (\<lambda>m. r\<delta> id X rels m \<union>
          (if t = nt then r\<epsilon>_strict n rels m else {}))). (t, X) \<leftarrow> aux, memR I (nt - t)]
      [(t, gmrtabulate mrs (\<lambda>m. grdelta (map (dmsk cs) css) id gX (map2 (dtabc n) css rels) m \<union>
          (if t = nt then greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) m else {}))).
        (t, gX) \<leftarrow> gaux, memR I (nt - t)]"
    by (rule dmrdaux_map_step[OF a, where
          F = "\<lambda>t Y. mrtabulate mrs (\<lambda>m. r\<delta> id Y rels m \<union>
            (if t = nt then r\<epsilon>_strict n rels m else {}))"
          and G = "\<lambda>t gY. gmrtabulate mrs (\<lambda>m. grdelta (map (dmsk cs) css) id gY
            (map2 (dtabc n) css rels) m \<union>
            (if t = nt then greps_strict (map (dmsk cs) css) (map2 (dtabc n) css rels) m
             else {}))"]) (use step in blast)
  note B = dmrdaux_insert_new[OF M E gE, of nt]
  show "dtabc n cs (fst (update_matchP n I mr mrs rels nt aux))
      = fst (gupdate_matchP (map (dmsk cs) css) I mr mrs (map2 (dtabc n) css rels) nt gaux)"
    unfolding update_matchP_def gupdate_matchP_def Let_def fst_conv
    by (rule dtabc_foldr_lookup[OF B])
  show "dmrdaux n cs (snd (update_matchP n I mr mrs rels nt aux))
      (snd (gupdate_matchP (map (dmsk cs) css) I mr mrs (map2 (dtabc n) css rels) nt gaux))"
    unfolding update_matchP_def gupdate_matchP_def Let_def snd_conv
    by (rule B)
qed

(*<*)
end
(*>*)
