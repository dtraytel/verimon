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

lemma dtabc_Un: "dtabc n cs (T \<union> T') = dtabc n cs T \<union> dtabc n cs T'"
  by (simp add: dtabc_def image_Un)

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
  then show ?case by (simp add: dtabc_Un)
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

(*<*)
end
(*>*)
