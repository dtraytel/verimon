(*<*)
theory Trigger_Window_Proof
  imports "Monitor_Exec.Trigger_Window" Until_Gen_Proof Release_Window_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



subsection \<open>The read is a finite table\<close>

text \<open>The read of the trigger structure is a finite table over the right operand's columns.
  With an interval containing zero that is immediate, because the window then always holds the
  latest time point and the read is contained in its right table.  Without it a safe trigger has
  the same columns on both sides, and the read is contained in the union of the window's
  tables -- which is what the weakened form below states.\<close>

subsection \<open>The summaries\<close>

lemma tw_push:
  "sw_rel tcomp id W X \<Longrightarrow> sw_rel tcomp id (tw_push args msk nt mv W)
     (X @ map (tent args msk) (filter (\<lambda>x. memR (args_ivl args) (nt - fst x)) mv))"
proof (induct mv arbitrary: W X)
  case (Cons y mv)
  obtain t l r where y: "y = (t, l, r)" by (cases y)
  show ?case
  proof (cases "memR (args_ivl args) (nt - t)")
    case True
    have "sw_rel tcomp id (sw_push tcomp id t (esum_of args msk l r) W) (X @ [tent args msk y])"
      unfolding y tent_def fst_conv snd_conv by (rule sw_rel_push[OF sw_assoc_tcomp Cons(2)])
    from Cons(1)[OF this] show ?thesis using True by (simp add: tw_push_def y)
  next
    case False
    then show ?thesis using Cons by (simp add: tw_push_def y)
  qed
qed (simp add: tw_push_def)

end
(*>*)
