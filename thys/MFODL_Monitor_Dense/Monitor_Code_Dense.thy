(*<*)
theory Monitor_Code_Dense
  imports "MFODL_Monitor_Devel.Monomorphic_Code" "MFODL_Monitor_Devel.RBT_set_opt" Dense_Mono_Hot Dense_Push Dense_VeriMon "Log_Parser.Log_Code"
    Log_Monitor
begin
(*>*)

text \<open>
  The code export the shipping binary is built from: \<^verbatim>\<open>src/verified.ml\<close> is this theory's
  \<^verbatim>\<open>verified.ocaml\<close>, and @{text "-verified"} runs the verified dense evaluator it contains.
  @{const udminit_verimon} prepares the input formula as VeriMon does -- type checking and, if
  the formula is not monitorable, normalization and rewriting, then the conversion into
  multi-way joins (@{theory MFODL_Monitor_Dense.Dense_VeriMon}) -- and builds the initial state
  from it with @{const udminit_push}, which binds frozen predicates with @{text LET} where it can
  (@{theory MFODL_Monitor_Dense.Dense_Frz}), moves existential quantifiers into the windows they
  commute with (@{theory MFODL_Monitor_Dense.Dense_Push}), binds the right operand of a release
  so that it is evaluated once (@{theory MFODL_Monitor_Dense.Dense_Share}) and compiles the resulting sparse
  formula into the short-tuple one; @{const udmstep} performs one step on it.  All of these are
  pure functions over the short tuples.  @{const uvdfail_nodes} says whether the compiler covered the whole formula; it
  must be zero for the correctness theorem @{text udeval_Rep} (@{theory
  MFODL_Monitor_Dense.Dense_Unbox_Exec}) to apply, and the front end refuses the formula
  otherwise.  @{text "-verified"} runs them on the log through @{const vinit},
  @{const vfeed_chunk} and @{const vfinish} (@{theory MFODL_Monitor_Dense.Log_Monitor}): the
  verified log parser, which drops the events of the predicates the formula does not mention,
  the conversion of the entries into the monitor's databases, and the monitor, with the
  theorems @{text verimon_log.vrun_log} and @{text verimon_log.vrun_filtered} from the bytes
  of the log to the verdicts; @{const vpending} tells the driver which part of the input it
  still needs for locating errors.

  The export is entirely within this session.  The code-generator setup it relies on -- the
  monomorphised containers and tree primitives of @{theory MFODL_Monitor_Dense.Dense_Code_Opt}
  and @{theory MFODL_Monitor_Dense.Dense_Mono_Sweep}, the rank trees of the aggregations of
  @{theory MFODL_Monitor_Dense.Dense_Agg_Code}, the one-descent updates of
  @{theory MFODL_Monitor_Dense.Dense_Map_Upd}, the red-black trees' rebalancing of
  @{theory MFODL_Monitor_Dense.Dense_RBT_Code}, the copies of
  @{theory MFODL_Monitor_Dense.Dense_Mono_Hot} for the generic operations a profile still found
  on the inner loops, and the front end's entry points -- is stated here too.

  The order of the imports matters.  Where a boxed operation of
  @{theory MFODL_Monitor_Dense.Dense_Code_Opt} and its monomorphic copy from the second pass of
  @{theory MFODL_Monitor_Dense.Dense_Mono_Sweep} both rewrite the same term, the code
  preprocessor takes whichever rule the merge of the two branches puts first.  Importing
  @{theory MFODL_Monitor_Devel.Monomorphic_Code} and @{theory MFODL_Monitor_Devel.RBT_set_opt}
  first leaves the monomorphic copies in front, as
  they were when the export was made in session MFODL\_Monitor\_Imp; the other order would
  reinstate the boxed versions of @{const card}, @{const Set.remove}, @{const cluster} and a
  few more.

  A merge also takes the union of the two preprocessor simpsets, so it brings back rules one
  branch deleted: the redirections of the set operations on the wide tuples to their boxes,
  which @{theory MFODL_Monitor_Dense.Dense_Code_Opt} takes out of the preprocessor so that the
  monomorphic copies apply, return with @{theory MFODL_Monitor_Devel.Monomorphic_Code}, and the
  boxes of @{theory MFODL_Monitor_Dense.Dense_Code_Opt} that
  @{theory MFODL_Monitor_Dense.Dense_Mono_Hot} takes out return with
  @{theory MFODL_Monitor_Dense.Log_Monitor}.  Both are taken out again here, after the merge.
\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps
  @{thms ed_union_v_unfold ed_inter_v_unfold ed_minus_v_unfold ed_filter_v_unfold
    ed_image_v_unfold edl_remove_v_unfold edl_csorted_list_of_set_v_unfold
    edl_mfilter_nat_v_unfold})\<close>

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
  (*the verified dense monitor, over the short tuples, and its initialization with VeriMon's
    preparation of the formula*)
  udminit_push udminit_verimon prepare_verimon udmstep uvdfail_nodes udmstate_m
  (*the verified log parser (session Log_Parser), which reads the log in chunks*)
  Log_Exec.einit Log_Exec.efeed_chunk Log_Exec.efinish Log_Exec.O_ITEM Log_Grammar.Entry Log_Grammar.T_AT
  Log_Exec.E_TOKEN Log_Exec.X_ENTRY
  (*the verified monitor on the log: parser, conversion, and dense monitor*)
  Log_Monitor.vinit Log_Monitor.vfeed_chunk Log_Monitor.vfinish Log_Monitor.vpending Log_Monitor.VO_VERDICTS
  Log_Monitor.VE_PARSE Log_Monitor.VI_WF
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
