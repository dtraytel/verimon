(*<*)
theory Prepare
  imports Push_Rewrite "MFODL_Logic.Preparation"
begin
(*>*)



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

end
(*>*)
