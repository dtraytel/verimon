(*<*)
theory Monitor_Code_Imp_Only
  imports Monitor_Code_Imp
begin
(*>*)

text \<open>
  A second, narrower code export, alongside the one of @{theory MFODL_Monitor_Imp.Monitor_Code_Imp}
  that the shipping binary is built from.  That one names both the imperative heap-resident dense
  monitor's entry points and the verified dense evaluator's, in a single OCaml module, because a
  single binary needs both to run either under @{text "-vdense"}.  Naming only the heap-resident
  ones here, with none of @{theory MFODL_Monitor_Dense.Dense_Unbox_Exec}'s in the request list,
  produces a second file whose reachable code is -- and can be checked to be -- exactly this
  session's own: nothing named or reachable from the sibling Monitor\_Code\_Dense theory (session
  MFODL\_Monitor\_Dense) should appear in it beyond the front end the two share, and nothing here
  should be pulled into that file's own export the same way around.

  This file is not linked into the shipping binary: @{text Formula.formula}, @{text event_data}
  and every other datatype the two exports both mention are regenerated independently by each
  \<^verbatim>\<open>export_code\<close> command, so a value built by one file's functions cannot be handed to the
  other's without a conversion layer neither file provides.  It exists so that the two files can
  be read, and diffed against each other and against the combined @{text "verified.ml"}, to
  confirm which code is genuinely session-local and which boolean configuration flags -- if any
  survive -- are reachable from each side on its own.
\<close>

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval RBT_set Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*the front end's own functions on formulas*)
  convert_multiway mmonitorable_exec type_check
  (*the imperative, heap-resident monitor and its database, both over the tuples without their
    empty columns -- no vdense symbol is named, unlike in Monitor_Code_Imp*)
  minit_safe_d mstep_d dfail_nodes
  utable_of_list uempty_db uinsert_table_into_db urbt_fold
  in OCaml module_name Monitor file_prefix "verified_imp"

(*<*)
end
(*>*)
