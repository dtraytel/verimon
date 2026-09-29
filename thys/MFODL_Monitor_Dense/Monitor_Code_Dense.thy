(*<*)
theory Monitor_Code_Dense
  imports Kernel_Code Dense_VeriMon Dense_Mono "Log_Parser.Log_Code" Log_Monitor
begin
(*>*)

text \<open>The merge of the imports brings back the box that @{theory MFODL_Monitor_Dense.Dense_Mono}
  takes out of the preprocessor.\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps @{thms ed_cluster_v_unfold})\<close>

text \<open>
  The code export the shipping binary is built from: \<^verbatim>\<open>src/verified.ml\<close> is this theory's
  \<^verbatim>\<open>verified.ocaml\<close>, and @{text "-verified"} runs the monitor it contains.
  @{const udminit_verimon} prepares the input formula as VeriMon does -- type checking and, if
  the formula is not monitorable, normalization and rewriting, then the conversion into
  multi-way joins -- rewrites it with @{const dense_prep}, which binds frozen predicates with
  @{text LET} where it can (@{theory MFODL_Monitor_Dense.Dense_Frz}), moves existential
  quantifiers into the windows they commute with (@{theory MFODL_Monitor_Dense.Dense_Push}) and
  binds the right operand of a release so that it is evaluated once
  (@{theory MFODL_Monitor_Dense.Dense_Share}), and starts the kernel of
  @{theory MFODL_Monitor_Devel.Monitor_Impl} on the result (@{theory MFODL_Monitor_Dense.Dense_VeriMon}),
  with the window structures of @{theory MFODL_Monitor_Dense.Dense_Maux}.
  It returns the columns of the verdicts' tuples along with the state: the free variables in the
  order in which @{const Formula.fv_list} lists them for the rewritten formula.
  @{const dmstep} performs one step.  @{text "-verified"} runs them on the log through
  @{const vinit}, @{const vfeed_chunk} and @{const vfinish}
  (@{theory MFODL_Monitor_Dense.Log_Monitor}): the verified log parser, which drops the events of
  the predicates the formula does not mention, the conversion of the entries into the monitor's
  databases, and the monitor, with the theorems @{text verimon_log.vrun_log} and
  @{text verimon_log.vrun_filtered} from the bytes of the log to the verdicts; @{const vpending}
  tells the driver which part of the input it still needs for locating errors.

  The code-generator setup -- the monomorphised containers and tree primitives -- is that of
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} and @{theory MFODL_Monitor_Devel.RBT_set_opt},
  with the additions of @{theory MFODL_Monitor_Dense.Kernel_Code}.
\<close>

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval RBT_set Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*the front end's own functions on formulas*)
  convert_multiway mmonitorable_exec type_check
  (*the monitor's databases*)
  table_of_list empty_db insert_table_into_db rbt_fold
  (*the monitor, and its initialization with VeriMon's preparation of the formula*)
  udminit_verimon prepare_verimon dmstep mstate_m
  (*the verified log parser (session Log_Parser), which reads the log in chunks*)
  Log_Exec.einit Log_Exec.efeed_chunk Log_Exec.efinish Log_Exec.O_ITEM Log_Grammar.Entry Log_Grammar.T_AT
  Log_Exec.E_TOKEN Log_Exec.X_ENTRY
  (*the verified monitor on the log: parser, conversion, and monitor*)
  Log_Monitor.vinit Log_Monitor.vfeed_chunk Log_Monitor.vfinish Log_Monitor.vpending Log_Monitor.VO_VERDICTS
  Log_Monitor.VE_PARSE Log_Monitor.VI_WF Log_Monitor.vc_cols
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
