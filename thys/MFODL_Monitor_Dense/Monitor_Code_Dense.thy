(*<*)
theory Monitor_Code_Dense
  imports "MFODL_Monitor_Devel.Monomorphic_Code" "MFODL_Monitor_Devel.RBT_set_opt" Dense_VeriMon
    "Log_Parser.Log_Code" Log_Monitor
begin
(*>*)

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
  @{theory MFODL_Monitor_Devel.Monitor_Impl} on the result (@{theory MFODL_Monitor_Dense.Dense_VeriMon}).
  It returns the columns of the verdicts' tuples along with the state: the free variables in the
  order in which @{const Formula.fv_list} lists them for the rewritten formula.
  @{const mstep} performs one step.  @{text "-verified"} runs them on the log through
  @{const vinit}, @{const vfeed_chunk} and @{const vfinish}
  (@{theory MFODL_Monitor_Dense.Log_Monitor}): the verified log parser, which drops the events of
  the predicates the formula does not mention, the conversion of the entries into the monitor's
  databases, and the monitor, with the theorems @{text verimon_log.vrun_log} and
  @{text verimon_log.vrun_filtered} from the bytes of the log to the verdicts; @{const vpending}
  tells the driver which part of the input it still needs for locating errors.

  The code-generator setup -- the monomorphised containers and tree primitives -- is that of
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} and @{theory MFODL_Monitor_Devel.RBT_set_opt}.
\<close>

text \<open>The initial state is computed by @{const minit0} itself.  It builds its temporal nodes
  through the locales' @{text init_since}, @{text init_until}, @{text init_trigger} and
  @{text init_and_trigger}, whose definitions hold only under the locales' assumptions; the
  interpretations' instances of them are unfolded into the code instead.  The fused
  And-Trigger's is unfolded into the equations of @{const minit0} directly, where the
  preprocessor does not reach it.\<close>

declare default_mmasaux.init_since_def[code_unfold] dq_muaux.init_until_def[code_unfold]
  verimon_maux.init_trigger_def[code_unfold]

lemmas minit0_code_simps = default_maux.minit0.simps[unfolded verimon_maux.init_and_trigger_def]

declare [[code drop: minit0]]
declare minit0_code_simps[code]

text \<open>@{theory MFODL_Monitor_Devel.Monomorphic_Code} replaces the probe of the joins over red-black
  trees by @{const probe_step_key}, which computes the join key once; the probe over other sets
  goes through it too.\<close>

declare probe_step_key[symmetric, code]

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
  udminit_verimon prepare_verimon mstep mstate_m
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
