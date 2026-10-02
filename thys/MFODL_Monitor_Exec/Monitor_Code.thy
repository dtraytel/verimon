(*<*)
theory Monitor_Code
  imports "MFODL_Monitor_Devel.Monomorphic_Code" "MFODL_Monitor_Devel.RBT_set_opt" Mono_Hot Push_Rewrite Prepare "Log_Parser.Log_Code"
    Log_Monitor
begin
(*>*)

text \<open>
  The code export the shipping binary is built from: \<^verbatim>\<open>src/verified.ml\<close> is this theory's
  \<^verbatim>\<open>verified.ocaml\<close>, and @{text "-verified"} runs the verified executable evaluator it contains.
  @{const eminit_verimon} prepares the input formula as VeriMon does -- type checking and, if
  the formula is not monitorable, normalization and rewriting, then the conversion into
  multi-way joins (@{theory MFODL_Monitor_Exec.Prepare}) -- and builds the initial state
  from it with @{const eminit_push}, which binds frozen predicates with @{text LET} where it can
  (@{theory MFODL_Monitor_Exec.Frz_Rewrite}), moves existential quantifiers into the windows they
  commute with (@{theory MFODL_Monitor_Exec.Push_Rewrite}), binds the right operand of a release
  so that it is evaluated once (@{theory MFODL_Monitor_Exec.Share_Rewrite}) and compiles the
  resulting formula into the executable one; @{const emstep} performs one step on it.  All
  of these are pure functions over the tuples.  @{const efail_nodes} says whether the compiler
  covered the whole formula; it must be zero for the correctness theorem
  @{text emonitor_mverdicts_dof} (@{theory MFODL_Monitor_Exec.Compile}) to apply, and the front end refuses the
  formula otherwise.  @{text "-verified"} runs them on the log through @{const vinit},
  @{const vfeed_chunk} and @{const vfinish} (@{theory MFODL_Monitor_Exec.Log_Monitor}): the
  verified log parser, which drops the events of the predicates the formula does not mention,
  the conversion of the entries into the monitor's databases, and the monitor, with the
  theorems @{text verimon_log.vrun_log} and @{text verimon_log.vrun_filtered} (theory
  @{text Log_Monitor_Online}) from the bytes of the log to the verdicts; @{const vpending} tells the driver which part of the input it
  still needs for locating errors.

  The export is entirely within this session.  The code-generator setup it relies on -- the
  monomorphised containers and tree primitives of @{theory MFODL_Monitor_Exec.Tuple_Code}
  and @{theory MFODL_Monitor_Exec.Mono_Sweep}, the rank trees of the aggregations of
  @{theory MFODL_Monitor_Exec.Agg_Code}, the one-descent updates of
  @{theory MFODL_Monitor_Exec.Map_Upd_Code}, the red-black trees' rebalancing of
  @{theory MFODL_Monitor_Exec.RBT_Code}, the copies of
  @{theory MFODL_Monitor_Exec.Mono_Hot} for the generic operations a profile still found
  on the inner loops, and the front end's entry points -- is stated here too.
\<close>

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval RBT_set Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*the front end's own functions on formulas*)
  convert_multiway mmonitorable_exec type_check
  (*the verified executable monitor's own database*)
  utable_of_list uempty_db uinsert_table_into_db urbt_fold
  (*the verified executable monitor, and its initialization with VeriMon's preparation of the formula*)
  eminit_push eminit_verimon prepare_verimon emstep efail_nodes emstate_m
  (*the verified log parser (session Log_Parser), which reads the log in chunks*)
  Log_Exec.einit Log_Exec.efeed_chunk Log_Exec.efinish Log_Exec.O_ITEM Log_Grammar.Entry Log_Grammar.T_AT
  Log_Exec.E_TOKEN Log_Exec.X_ENTRY
  (*the verified monitor on the log: parser, conversion, and executable monitor*)
  Log_Monitor.vinit Log_Monitor.vfeed_chunk Log_Monitor.vfinish Log_Monitor.vpending Log_Monitor.VO_VERDICTS
  Log_Monitor.VE_PARSE Log_Monitor.VI_WF
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
