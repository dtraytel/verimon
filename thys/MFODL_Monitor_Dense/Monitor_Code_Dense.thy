(*<*)
theory Monitor_Code_Dense
  imports Dense_Idx_Code Dense_Unbox_Exec "MFODL_Monitor_Devel.Monitor_Code"
begin
(*>*)

text \<open>
  The verified dense evaluator's own code export, entirely within this session: it needs nothing
  from the imperative refinement of the downstream Table\_Imp theory (session
  MFODL\_Monitor\_Imp) and its heap-resident Since/Until, so this theory does not import that
  session at all. @{const udminit_safe} builds the initial state -- compiling the sparse formula
  into the short-tuple one -- and @{const udmstep} performs one step on it, both pure functions
  over the kernel's dense tables. @{const uvdfail_nodes} says whether the compiler covered the
  whole formula; it must be zero for the correctness theorem @{text udeval_Rep} (@{theory
  MFODL_Monitor_Dense.Dense_Unbox_Exec}) to apply, and the front end refuses the formula
  otherwise.

  Nothing else is exported, so the wide-tuple evaluators and the heap-resident dense mode of the
  downstream MFODL\_Monitor\_Imp session are absent from this file entirely, not merely unreachable:
  they are not even theories this session imports.
\<close>

text \<open>@{thm [source] mestate_def} is the kernel's code constructor for its state record, so the
  selectors the export's own dependency closure reaches need their equations stated against it;
  the record's own are about a constructor the code generator does not have.  The same lemma as
  in the downstream Monitor\_Code\_Imp theory (session MFODL\_Monitor\_Imp), needed here for the
  same reason even though this export never calls the wide-tuple monitor itself.\<close>

lemma mstate_sel_code[code]:
  "mstate_i (mestate i j m n t \<zeta>) = i"
  "mstate_j (mestate i j m n t \<zeta>) = j"
  "mstate_m (mestate i j m n t \<zeta>) = m"
  "mstate_n (mestate i j m n t \<zeta>) = n"
  "mstate_t (mestate i j m n t \<zeta>) = linearize t"
  by (simp_all add: mestate_def)

text \<open>The front end builds the tables of a time point itself, sorted, and hands them to
  @{const table_of_list}, which checks the sortedness in linear time and builds the tree in one
  pass.  The monitor over the short tuples reads the same tables with nothing around the fields,
  so it needs the same three entry points at its own tuple type; the bodies are those of
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} and @{theory MFODL_Monitor_Devel.Monitor_Impl}
  with the option gone.\<close>

definition utable_of_list :: "event_data list list \<Rightarrow> utable" where
  "utable_of_list xs = set xs"

lemma utable_of_list_code[code]: "utable_of_list xs = RBT_set (rbt_of_sorted_list xs)"
  by (simp add: utable_of_list_def RBT_set_rbt_of_sorted_list ID_ccompare_ed)

definition uempty_db :: udatabase where "uempty_db = Mapping.empty"

text \<open>And the fold the front end prints a verdict with, at the short tuples.\<close>

definition urbt_fold :: "_ \<Rightarrow> event_data list set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "urbt_fold = RBT_Set2.fold"

definition uinsert_table_into_db :: "string8 \<times> nat \<Rightarrow> utable \<Rightarrow> udatabase \<Rightarrow> udatabase" where
  "uinsert_table_into_db p X db = update_mapping_with (\<lambda>_ tbl _. map ((\<union>) X) tbl) p [X] db"

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval RBT_set Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*the front end's own functions on formulas*)
  convert_multiway mmonitorable_exec type_check
  (*the verified dense monitor's own database, over the short tuples*)
  utable_of_list uempty_db uinsert_table_into_db urbt_fold
  (*the verified dense monitor, over the short tuples*)
  udminit_safe udmstep uvdfail_nodes udmstate_m
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
