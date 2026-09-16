(*<*)
theory Monitor_Code_Imp
  imports Monitor_Imp Monitor_Imp2 Dense_Imp "MFODL_Monitor_Devel.Monitor_Code"
begin
(*>*)

text \<open>
  The code export of @{theory MFODL_Monitor_Devel.Monitor_Code} extended by the entry points of
  the imperative monitor: @{const minit_safe_imp} builds the initial state, allocating a hash
  table for every Since structure of the fragment, and @{const mstep_imp} performs one step on
  it. Both are heap computations; the generated OCaml represents them as thunks that the front
  end applies once per time point, in order (see @{theory MFODL_Monitor_Imp.Monitor_Imp}).
\<close>

text \<open>
  Imperative HOL prints the monad's bind as a two-argument lambda applied to one argument,
  @{text "(fun f_ () -> f_ (m ()) ()) f"}, which OCaml compiles as a partial application: two
  closures for every bind.  On the join of @{text "A(x,y) AND (ONCE[0,20] B(y,z))"} that is 104
  million words, a third of everything the join allocates.  Printing it as
  @{text "(fun () -> f (m ()) ())"} leaves one closure, and the placeholders of a printing are
  filled in argument order, so the flipped @{const bind_flip} is what carries it.

  The declaration belongs here rather than next to that definition: this theory merges the
  branch that carries it with the one that carries Imperative HOL's own, and the merge keeps
  the original unless it is superseded in the theory that exports the code.
\<close>

code_printing constant Heap_Monad.bind \<rightharpoonup> (OCaml)
| constant bind_flip \<rightharpoonup> (OCaml) "(fun/ ()/ ->/ (_)/ ((_)/ ())/ ())"

declare bind_flip_code[code]

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval empty_db insert_into_db table_of_list insert_table_into_db RBT_set rbt_fold Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*main functions*)
  convert_multiway mmonitorable_exec minit_safe mstep type_check vminit_safe vmstep
  minit_safe_imp mstep_imp
  (*heap-resident tables, for the micro-benchmark*)
  minit_safe_j mstep_j
  (*tuples without their empty columns*)
  minit_safe_d mstep_d dpure_nodes
  (*heap-resident tables and maps, for the micro-benchmarks*)
  ht_new ht_ins ht_mem ht_of_list ht_to_list
  im_new im_lookup im_update im_delete im_to_list
  (*rewrite functions*)
  rewrite_trigger
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
