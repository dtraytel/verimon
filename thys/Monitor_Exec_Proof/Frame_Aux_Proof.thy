(*<*)
theory Frame_Aux_Proof
  imports "Monitor_Exec.Frame_Aux" Frame_Proof "MFODL_Monitor_Proof.Correctness" "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



section \<open>The executable Since and Until structures\<close>

text \<open>
  The temporal structures run over the ascending columns @{term "eargs cs_R cs_L args"}: a stored
  tuple is a tuple over the right operand's columns @{term cs_R}, and the probe table is the left
  operand's, over @{term cs_L}.  The kernel's structures read the probe at a stored tuple by
  restricting the latter to the left operand's columns; over ascending columns that restriction
  is the executable projection at the mask @{term "mrg_left_key (mrg_plan cs_R cs_L)"}, which is a
  single pass over the tuple.  This theory adds an index on that projection and proves the
  resulting structures equal to the verified ones.
\<close>

subsection \<open>The executable index under the semi-join\<close>

text \<open>
  Restricting the index to the surviving keys is the index of the surviving tuples: a bucket
  passes or fails as a whole, because the filter only looks at the key.
\<close>

subsection \<open>Maintaining the index incrementally\<close>

text \<open>
  The structure adds and removes whole tables at a time, so the index is maintained by combining
  it with the index of the added table, and by subtracting the index of the removed one bucket by
  bucket.
\<close>

lemma eidx_empty[simp]: "eidx msk {} = Mapping.empty"
  by (intro mapping_eqI) (simp add: lookup_eidx)

text \<open>Only the buckets that the subtrahend touches are dropped when they empty: a bucket at a key
  the subtrahend does not have is left as it is.  On a clustering, which has no empty buckets, the
  two readings agree; the executable version of the subtraction, which only visits the
  subtrahend's keys, realises this one exactly.\<close>

subsection \<open>The mask of the left operand's columns among the right operand's\<close>

text \<open>
  Both indexed tables are determined by the mapping they index, so normalising them away does not
  leave the invariant.
\<close>

subsection \<open>What the window's entry and exit do to the keys\<close>

text \<open>
  The two folds that move tables out of and into the window report the tuples they removed and
  added.  That report is exactly the difference between the old and the new key set, which is what
  the index has to be reduced by and combined with.
\<close>

subsection \<open>The executable operations are the verified ones\<close>

subsection \<open>The join is the verified join\<close>

text \<open>
  Whichever branch it takes, the executable join filters both mappings by the executable test, and the
  window's table follows the mapping it indexes.  That is the verified join's abstract form
  (@{const join_mmsaux_abs}).
\<close>

subsection \<open>The join's validity\<close>

section \<open>The executable Until structure\<close>

text \<open>
  The Until structure needs far less than the Since one.  Only one of its components mentions
  the left operand: the mapping @{text a1_map} that records, for each tuple over the left
  operand's columns, the last time point at which it held.  The verified structure looks a stored
  tuple's restriction to those columns up in it; the executable one looks up the tuple's executable
  projection, which is the same tuple.  Every other operation is the verified one.
\<close>

text \<open>
  The executable operation is the verified one.  Where @{const add_new_dq} guards the fold with
  @{term \<open>finite rel2\<close>} and falls back on the other structure, this one folds unconditionally:
  every table the evaluator produces is finite.
\<close>

lemma etabc_eq_empty_table[simp]: "etabc ks cs T = empty_table \<longleftrightarrow> T = empty_table"
  by (simp add: etabc_empty_iff empty_table_def)

subsection \<open>The lax epsilon\<close>

subsection \<open>The strict epsilons\<close>

text \<open>
  Unlike the lax one, a strict epsilon does not carry a guard, and its value is a table over the
  node's columns only because the regular expression is safe.  This is the column part of the
  kernel's @{thm [source] qtable_r\<epsilon>_strict} and @{thm [source] qtable_l\<epsilon>_strict}:
  restricted to no valuation at all, a @{const qtable} says only that its table is a finite table
  over its columns.
\<close>

text \<open>A tested atom is moved to the node's column order; the executable one is already in it.\<close>

lemma wf_atoms: "wfrels rels \<Longrightarrow> wf_atoms ks (map Formula.fv_list \<psi>s) css rels"
  using lc fa sub by (auto simp: wf_atoms_def list_all2_conv_all_nth)

end

subsection \<open>The derivatives\<close>

text \<open>
  The two derivatives read the previous firing's tabulation, which the node keeps reordered, and
  join what they find against the atoms through the lax epsilon.  Reordering a tabulation is
  reordering every entry, so the lookups agree; the rest is the lax epsilon again.
\<close>

text \<open>Reordering a tabulation entry by entry is reordering what it tabulates.\<close>

text \<open>Reading a structure is a union of lookups, which the reordering distributes over.\<close>

end

text \<open>Reading the structure hands out the entries that have left the window, reordered.\<close>

end

text \<open>The buffer traversal steps two accumulators in lockstep if every step preserves a relation
  between them; unlike @{thm [source] mbuf2t_take_rel_ts}, the relation does not mention time.\<close>

lemma mbuf2t_take_rel:
  "(\<And>a b t za z'a. a \<in> set xs \<Longrightarrow> b \<in> set ys \<Longrightarrow> R za z'a \<Longrightarrow>
      R (f a b t za) (g (h a) (k b) t z'a)) \<Longrightarrow>
   R z z' \<Longrightarrow>
   mbuf2t_take f z (xs, ys) t0 ts = (w, (xs', ys'), nt, ts') \<Longrightarrow>
   mbuf2t_take g z' (map h xs, map k ys) t0 ts = (w2, buf2, nt2, ts2) \<Longrightarrow>
   R w w2 \<and> buf2 = (map h xs', map k ys') \<and> nt2 = nt \<and> ts2 = ts'"
proof (induct xs arbitrary: ys z z' t0 ts w xs' ys' nt ts' w2 buf2 nt2 ts2)
  case Nil
  then show ?case by (cases ts) auto
next
  case (Cons x xs)
  note IH = Cons.hyps and P = Cons.prems
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using P(2-4) by (cases ts) auto
  next
    case (Cons y ys2)
    note ysC = Cons
    show ?thesis
    proof (cases ts)
      case Nil
      then show ?thesis using P(2-4) ysC by auto
    next
      case (Cons t ts3)
      note tsC = Cons
      have r: "R (f x y t z) (g (h x) (k y) t z')"
        using P(1)[of x y z z' t] P(2) ysC by simp
      show ?thesis
        by (rule IH[OF _ r, of ys2 t ts3]) (use P ysC tsC in auto)
    qed
  qed
qed

(*<*)
end
(*>*)
