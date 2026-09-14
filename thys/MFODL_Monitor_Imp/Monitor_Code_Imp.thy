(*<*)
theory Monitor_Code_Imp
  imports Monitor_Imp "MFODL_Monitor_Devel.Monitor_Code"
begin
(*>*)

text \<open>
  The code export of @{theory MFODL_Monitor_Devel.Monitor_Code} extended by the entry points of
  the imperative monitor: @{const minit_safe_imp} builds the initial state, allocating a hash
  table for every Since structure of the fragment, and @{const mstep_imp} performs one step on
  it. Both are heap computations; the generated OCaml represents them as thunks that the front
  end applies once per time point, in order (see @{theory MFODL_Monitor_Devel.Monitor_Imp}).
\<close>

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval empty_db insert_into_db table_of_list insert_table_into_db RBT_set rbt_fold Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*main functions*)
  convert_multiway mmonitorable_exec minit_safe mstep type_check vminit_safe vmstep
  minit_safe_imp mstep_imp
  (*rewrite functions*)
  rewrite_trigger
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
