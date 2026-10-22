(*<*)
theory Frame_Proof
  imports "Monitor_Exec.Frame" Tuple_Fields_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>A frame that is already ascending is left alone.\<close>

text \<open>The short join is a merge driven by the two column lists: it succeeds exactly when the
  two tuples agree on the shared columns, and then reads each merged column from the side that
  has it.\<close>

subsection \<open>Agreement with the kernel's join\<close>

text \<open>The kernel's join of two tuples reads every column of the result from the side that has
  it.\<close>

text \<open>The short join of two tables is the short form of the kernel's join.\<close>

text \<open>A kernel table read in another order of its columns has the same executable form.\<close>

text \<open>Reading the shared columns out of a short tuple is the same as taking the short form of
  the kernel's restriction.\<close>

text \<open>
  This is the shape the anti-join of @{text "\<phi> AND NOT \<psi>"} takes, and the intersection when the
  two column lists are equal: every tuple of the left operand either has a partner or does not,
  and the test is a membership of its projection.
\<close>

subsection \<open>The short form of a table commutes with intersection, difference and union\<close>

subsection \<open>Equal columns, and a right operand with no columns\<close>

text \<open>The general join's shapes need the right operand's columns among the left's for an
  antijoin; the result frame of a join is the merge of the two.\<close>

text \<open>The join of two short tuples succeeds exactly when they agree on the shared columns, and
  then it is the test-free merge.\<close>

text \<open>Both sides of the size test compute the same table: the pairs that agree on the shared
  columns, merged.\<close>

text \<open>Every shape of the plan computes the short form of the kernel's join.  A negative join
  needs the right operand's columns among the left's, which is what the safety condition of
  @{text "\<phi> AND NOT \<psi>"} provides; the other shapes then arise only for a positive join.\<close>

text \<open>The kernel's multi-way join is the left-to-right fold, read in its own column order.\<close>

text \<open>The re-indexed term read at the short tuple's positions is the original term read at the
  kernel's.\<close>

text \<open>The kernel puts the aggregate in front of the group key; the short tuple has it at the
  one position @{term y} occupies among the group's columns.\<close>

subsection \<open>Selecting a group commutes with the reordering\<close>

subsection \<open>The aggregated values do not change\<close>

subsection \<open>Aggregation over short tuples agrees with the kernel's\<close>

text \<open>
  The executable aggregation takes the group key as a suffix of the short tuple (of length
  @{term "length tys"} before it), and writes the aggregate at the position @{term y} occupies
  among the group's columns.  The kernel's result is over @{term "y # shift_cols (length tys) cs"},
  the executable one over the same columns in ascending order.
\<close>

lemma set_cols:
  assumes "finite A"
  shows "sorted_wrt (<) (set_cols A)" "set (set_cols A) = A"
  using assms unfolding set_cols_def
  by (subst csorted_list_of_set_split;
      auto simp: ccompare_nat_def ID_Some ord_defs strict_sorted_iff)+

lemma set_cols_empty: "set_cols {} = []"
  by (rule set_cols_eqI[symmetric]) simp_all

subsection \<open>Matching a predicate's arguments\<close>

text \<open>The kernel tabulates a match at the predicate's columns in their order of occurrence; the
  executable match reads it off at the same columns in ascending order.\<close>

lemma fold_pred_cols_simple:
  "is_simple_pattern tms m \<Longrightarrow> \<forall>c \<in> set acc. c < m \<Longrightarrow>
     fold (\<lambda>t cs. cols_union cs (Formula.fv_trm_list t)) tms acc = acc @ smp_cols tms"
proof (induct tms m arbitrary: acc rule: is_simple_pattern.induct)
  case (2 y ts x)
  have "y \<notin> set acc" using 2(2,3) by auto
  then have "cols_union acc [y] = acc @ [y]" by (simp add: cols_union_def)
  moreover have "\<forall>c \<in> set (acc @ [y]). c < Suc y" using 2(2,3) by auto
  ultimately show ?case using 2(1)[of "acc @ [y]"] 2(2) by simp
qed simp_all

lemma pred_cols_simple: "is_simple_pattern tms 0 \<Longrightarrow> pred_cols tms = smp_cols tms"
  using fold_pred_cols_simple[of tms 0 "[]"] by (simp add: pred_cols_def)

text \<open>A join whose right operand's columns are among the left one's keeps the left one's columns;
  it commutes with the reordering.\<close>

section \<open>Buffers of reordered tables\<close>

text \<open>
  A buffer never looks inside a tuple: it lines up the tables the operands produce and hands
  matching pairs to the node's operation.  So a buffer of reordered tables behaves as the
  reordering of a buffer of the kernel's.  These are map-fusion lemmas for the kernel's own
  list-level buffers, which is where its verified @{const meval} lives.
\<close>

text \<open>
  The Until node's operation is the one place where the step condition is not uniform in the
  timestamp: the verified structure accepts a new timestamp only at or after the one it is already
  at.  So the accumulator relation is indexed by that timestamp, the step may assume the new one
  is no smaller, and the conclusion says where the accumulator ended up -- at or before the
  timestamp the buffer reports and at or before every timestamp it did not consume.
\<close>

subsection \<open>The multi-way buffer\<close>

text \<open>
  @{const mbufn_take} lines up one table per conjunct, and each conjunct has its own column list,
  so the morphism is a list of reorderings applied slotwise.  The step condition is relational for
  the same reason as @{thm [source] mbuf2t_take_rel_ts}, and it is restricted to tables drawn from
  fixed sets @{term Ss}, one per slot, because the tables the operands produce have to be well
  formed for the multi-way join theorem to apply and the buffer only ever shrinks.
\<close>

subsection \<open>Leftovers of a buffer\<close>

text \<open>A take only ever removes a prefix, so whatever stays in the buffer was already there.\<close>

text \<open>The same two facts for the timestamped take: what it leaves in the buffers is a
  sublist of what it found there, and two runs whose buffers differ by a map on each operand
  step together, consume the same timestamps and leave buffers that differ by the same map.
  The past and future match nodes need them, as the conjunction nodes need the untimed ones.\<close>

subsection \<open>Leftovers of the shift buffer\<close>

lemma mprev_next_sub: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow> set xs' \<subseteq> set xs"
  by (induct I xs ts arbitrary: ys xs' ts' rule: mprev_next.induct)
    (auto split: prod.splits)

section \<open>The unit and empty tables\<close>

text \<open>Hence a negation node, whose operand has no columns at all, only has to look at
  emptiness -- which the reordering preserves in both directions.\<close>

section \<open>The assignment, the time point and the timestamp\<close>

subsection \<open>Assigning a term to a fresh column\<close>

text \<open>
  The kernel's assignment appends the value at the end of its tuple:
  @{thm eval_assignment.simps}.  The short tuple has it at the position the new column occupies
  in the merged column list -- the same insertion the aggregation's output does, at the same
  @{const ins_pos}.
\<close>

section \<open>The verified Trigger structure over ascending columns\<close>

text \<open>
  The trigger's auxiliary list carries two tables per time point, like the Until's, but the
  structure reads its answer off that list rather than accumulating it, so what has to transport
  is @{const trigger_results} itself.  Its \<^emph>\<open>then\<close> branch is a set comprehension over tuples of
  the right operand's columns, and the two conditions it puts on a tuple -- membership in a
  stored right table, and a join against a stored left table -- both commute with the reordering.
\<close>

text \<open>The structure over ascending columns, related to the kernel's through the abstract
  auxiliary list they are both valid for, exactly as for the Since and the Until.\<close>

text \<open>The trigger's buffer traversal, stepped over both column orders at once.  It is
  @{thm [source] mbuf2t_take_rel_ts} without the timestamp bookkeeping.\<close>

text \<open>The index computes the semi-join: a stored tuple's bucket survives the restriction exactly
  when the tuple itself survives the filter.\<close>

end
(*>*)
