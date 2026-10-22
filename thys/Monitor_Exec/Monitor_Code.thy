(*<*)
theory Monitor_Code
  imports "Monitor_Impl.Monomorphic_Code" "Monitor_DS.RBT_set_opt" Mono_Hot Push_Rewrite Prepare "Log_Parser.Log_Code" Log_Monitor
begin
(*>*)



text \<open>
  The code-generator setup of the verified executable monitor, which VeriMon's code export
  (session \<^verbatim>\<open>VeriMon_CLI\<close>, theory \<^verbatim>\<open>CLI_Code\<close>) imports from here:
  the monomorphised containers and tree primitives of @{theory Monitor_Exec.Tuple_Code}
  and @{theory Monitor_Exec.Mono_Sweep}, the rank trees of the aggregations of
  @{theory Monitor_Exec.Agg_Code}, the one-descent updates of
  @{theory Monitor_Exec.Map_Upd_Code}, the red-black trees' rebalancing of
  @{theory Monitor_Exec.RBT_Code}, and the copies of
  @{theory Monitor_Exec.Mono_Hot} for the generic operations a profile still found
  on the inner loops.

  The monitor that runs is @{const eminit_verimon} and @{const emstep}:
  @{const eminit_verimon} prepares the input formula as VeriMon does -- type checking and, if
  the formula is not monitorable, normalization and rewriting, then the conversion into
  multi-way joins (@{theory Monitor_Exec.Prepare}) -- and builds the initial state
  from it with @{const eminit_push}, which binds frozen predicates with @{text LET} where it can
  (@{theory Monitor_Exec.Frz_Rewrite}), moves existential quantifiers into the windows they
  commute with (@{theory Monitor_Exec.Push_Rewrite}), binds the right operand of a release
  so that it is evaluated once (@{theory Monitor_Exec.Share_Rewrite}) and compiles the
  resulting formula into the executable one; @{const emstep} performs one step on it.
  @{const efail_nodes} says whether the compiler covered the whole formula; it must be zero
  for the correctness theorem @{text emonitor_mverdicts_dof}
  (@{theory Monitor_Exec.Compile}) to apply, and VeriMon refuses the formula otherwise.
  They run on the log through @{const vinit}, @{const vfeed_chunk} and @{const vfinish}
  (@{theory Monitor_Exec.Log_Monitor}), with the theorems
  @{text verimon_log.vrun_log} and @{text verimon_log.vrun_filtered} (theory
  @{text Log_Monitor_Online}) from the bytes of the log to the verdicts.
\<close>

(*<*)
end
(*>*)
