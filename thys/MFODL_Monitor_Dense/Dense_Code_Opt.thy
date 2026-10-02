(*<*)
theory Dense_Code_Opt
  imports Dense_Unbox_Exec Dense_Idx_Code "MFODL_Monitor_Devel.Monomorphic_Code"
begin
(*>*)

section \<open>The input tables of the monitor over the short tuples\<close>

text \<open>
  The front end builds the tables of a time point itself, sorted, and hands them to
  @{text utable_of_list}, which checks the sortedness in linear time and builds the tree in one
  pass.  The kernel's tuples are the short tuples, so the three entry points are those of
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} and @{theory MFODL_Monitor_Devel.Monitor_Impl},
  named for the dense monitor.
\<close>

type_synonym udatabase = database

definition utable_of_list :: "event_data list list \<Rightarrow> utable" where
  "utable_of_list xs = set xs"

lemma utable_of_list_code[code]: "utable_of_list xs = RBT_set (rbt_of_sorted_list xs)"
  by (simp add: utable_of_list_def RBT_set_rbt_of_sorted_list ID_ccompare_etuple)

definition uempty_db :: udatabase where "uempty_db = Mapping.empty"

text \<open>And the fold the front end prints a verdict with, at the short tuples.\<close>

definition urbt_fold :: "_ \<Rightarrow> event_data list set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "urbt_fold = RBT_Set2.fold"

definition uinsert_table_into_db :: "string8 \<times> nat \<Rightarrow> utable \<Rightarrow> udatabase \<Rightarrow> udatabase" where
  "uinsert_table_into_db p X db = update_mapping_with (\<lambda>_ tbl _. map ((\<union>) X) tbl) p [X] db"

(*<*)
end
(*>*)
