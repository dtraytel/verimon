(*<*)
theory Agg_Gen_Proof
  imports "Monitor_Exec.Agg_Gen" Window_Proof Frame_Aux_Proof "Monitor_Impl_Proof.Monitor_Impl_Proof"
begin
(*>*)



text \<open>The kernel's steps carry a flag and keep folding once it is down; the steps here stop at
  the first failure.  The two agree, and a fold of steps that commute with a map @{text R} is
  the map of the fold.  The keys a fold leaves are the ones it started with and the groups of
  the tuples it inserted.\<close>

lemma fold_flag_False:
  assumes "\<And>t m. S t (False, m) = (False, m)"
  shows "fold S xs (False, m) = (False, m)"
  using assms by (induct xs) simp_all

lemma fold_flag:
  assumes F: "\<And>t m. S t (False, m) = (False, m)"
    and N: "\<And>t. St t None = None"
    and C: "\<And>t m. St t (Some (C m)) = (case S t (True, m) of (v, m') \<Rightarrow> if v then Some (C m') else None)"
  shows "fold St xs (Some (C m)) = (case fold S xs (True, m) of (v, m') \<Rightarrow> if v then Some (C m') else None)"
proof (induct xs arbitrary: m)
  case (Cons x xs)
  have NN: "fold St ys None = None" for ys by (induct ys) (simp_all add: N)
  show ?case
  proof (cases "S x (True, m)")
    case (Pair v m')
    then show ?thesis using Cons C by (cases v) (simp_all add: NN fold_flag_False[OF F])
  qed
qed simp

lemma gins_None[simp]: "gins k ev xs None = None"
  by (induct xs) (simp_all add: gins_def gstep_ins_def)

lemma gdel_None[simp]: "gdel k ev xs None = None"
  by (induct xs) (simp_all add: gdel_def gstep_del_def)

lemma fold_gstep_None[simp]:
  "fold (gstep_ins k ev) xs None = None" "fold (gstep_del k ev) xs None = None"
  using gins_None gdel_None by (simp_all add: gins_def gdel_def)

(*<*)
end
(*>*)
