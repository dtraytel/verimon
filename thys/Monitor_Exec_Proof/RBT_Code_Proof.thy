(*<*)
theory RBT_Code_Proof
  imports "Monitor_Exec.RBT_Code" Map_Upd_Code_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



lemma bh_le_g_correct: "bh_le_g t1 t2 \<longleftrightarrow> bheight t1 \<le> bheight t2"
  by (induction t1 t2 rule: bh_le_g.induct) auto

lemma bh_lt_g_correct: "bh_lt_g k t \<longleftrightarrow> integer_of_nat (bheight t) < k"
proof (induction k t rule: bh_lt_g.induct)
  case (3 k l a b r)
  show ?case
  proof (cases "k \<le> 0")
    case True
    have "k \<le> 0" by (rule True)
    also have "(0::integer) \<le> 1 + of_nat (bheight l)"
      by simp
    finally have "k \<le> 1 + of_nat (bheight l)" .
    then show ?thesis using True by (simp add: integer_of_nat_eq_of_nat not_less)
  next
    case False
    then show ?thesis using 3
      by (simp add: integer_of_nat_eq_of_nat less_diff_eq add.commute)
  qed
qed (auto simp: integer_of_nat_eq_of_nat)

end
(*>*)
