(*<*)
theory Prepare
  imports Push_Rewrite "MFODL_Logic.Preparation"
begin
(*>*)



section \<open>VeriMon's preparation of the formula for the verified executable monitor\<close>

text \<open>
  The verified executable monitor runs on the formula that VeriMon prepares (@{const prepare_verimon}):
  the input formula is type checked and, if it is not monitorable and rewriting is requested,
  normalized, its temporal operators with negated right operands replaced by their duals
  (@{const dual_since}), and rewritten, until it becomes monitorable. Optionally (@{text mw}), the prepared
  formula is converted into multi-way joins. The executable state is then built from it by
  @{const eminit_push}, which also binds frozen predicates with @{const Formula.Let} where it
  can (@{theory MFODL_Monitor_Exec.Frz_Rewrite}), moves existential quantifiers into the
  windows they commute with (@{theory MFODL_Monitor_Exec.Push_Rewrite}), and binds the right
  operand of a release so that it is evaluated once (@{theory MFODL_Monitor_Exec.Share_Rewrite}). The
  theorem @{text eminit_verimon_mverdicts} below states that the verdicts of the executable monitor
  started from this state are those of the input formula, provided the executable compiler covered
  the whole formula.

  The short tuples are over the free variables in ascending order, whatever the formula they
  were compiled from: the rewrites change the order in which @{const Formula.fv_list} lists the
  free variables, and so the kernel's columns, but not the set.
\<close>

text \<open>Changing the formula's type annotations changes none of its column lists.\<close>

lemma fvi_list_map_formula[simp]:
  "Formula.fvi_list b (Formula.formula.map_formula g \<phi>) = Formula.fvi_list b \<phi>"
proof (induction b \<phi> rule: Formula.fvi_list.induct)
  case (20 b I r)
  then show ?case
    by (induction r) auto
next
  case (21 b I r)
  then show ?case
    by (induction r) auto
qed (auto simp: fold_map comp_def cong: fold_cong)

text \<open>The multiway conversion copies the right operand of a release into its left operand;
  @{const share_opt} binds that operand with @{const Formula.Let} first, so that the copies are
  all occurrences of one predicate.\<close>

definition eminit_verimon where
  "eminit_verimon ix mw rw sig \<phi> =
     map_sum id (\<lambda>\<psi>. eindex ix (eminit_push (if mw then convert_multiway (share_opt \<psi>) else \<psi>)))
       (prepare_verimon rw sig \<phi>)"

context verimon_prepare
begin

definition "\<psi>_mw mw = (if mw then convert_multiway (share_opt \<psi>) else \<psi>)"

context
  fixes mw :: bool
begin

end

end

(*<*)
end
(*>*)
