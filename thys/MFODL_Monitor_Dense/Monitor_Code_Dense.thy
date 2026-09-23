(*<*)
theory Monitor_Code_Dense
  imports "MFODL_Monitor_Devel.Monitor_Code" Dense_Agg_Upkeep Dense_Push
begin
(*>*)

text \<open>
  The code export the shipping binary is built from: \<^verbatim>\<open>src/verified.ml\<close> is this theory's
  \<^verbatim>\<open>verified.ocaml\<close>, and @{text "-verified"} runs the verified dense evaluator it contains.
  @{const udminit_push} builds the initial state -- moving existential quantifiers into the
  windows they commute with (@{theory MFODL_Monitor_Dense.Dense_Push}) and compiling the
  resulting sparse formula into the short-tuple one -- and @{const udmstep} performs one step
  on it, both pure functions over the short tuples.  @{const uvdfail_nodes} says whether the compiler covered the whole formula; it
  must be zero for the correctness theorem @{text udeval_Rep} (@{theory
  MFODL_Monitor_Dense.Dense_Unbox_Exec}) to apply, and the front end refuses the formula
  otherwise.

  The export is entirely within this session.  The code-generator setup it relies on -- the
  monomorphised containers and tree primitives of @{theory MFODL_Monitor_Dense.Dense_Code_Opt}
  and @{theory MFODL_Monitor_Dense.Dense_Mono_Sweep}, the rank trees of the aggregations of
  @{theory MFODL_Monitor_Dense.Dense_Agg_Code} and their windows' one-pass upkeep of
  @{theory MFODL_Monitor_Dense.Dense_Agg_Upkeep}, and the front end's entry
  points -- is stated here too, so nothing of the imperative refinement of session
  MFODL\_Monitor\_Imp, and in particular nothing of its unverified heap-resident dense monitor,
  is imported, let alone reachable.

  The order of the first two imports matters.  Where a boxed operation of
  @{theory MFODL_Monitor_Dense.Dense_Code_Opt} and its monomorphic copy from the second pass of
  @{theory MFODL_Monitor_Dense.Dense_Mono_Sweep} both rewrite the same term, the code
  preprocessor takes whichever rule the merge of the two branches puts first.  Importing
  @{theory MFODL_Monitor_Devel.Monitor_Code} first leaves the monomorphic copies in front, as
  they were when the export was made in session MFODL\_Monitor\_Imp; the other order would
  reinstate the boxed versions of @{const card}, @{const Set.remove}, @{const cluster} and a
  few more.

  A merge also takes the union of the two preprocessor simpsets, so it brings back rules one
  branch deleted: the redirections of the set operations on the wide tuples to their boxes,
  which @{theory MFODL_Monitor_Dense.Dense_Code_Opt} takes out of the preprocessor so that the
  monomorphic copies apply, return with @{theory MFODL_Monitor_Devel.Monitor_Code}.  They are
  taken out again here, after the merge.
\<close>

setup \<open>Code_Preproc.map_pre (fn ctxt => ctxt delsimps
  @{thms ed_union_v_unfold ed_inter_v_unfold ed_minus_v_unfold ed_filter_v_unfold
    ed_image_v_unfold})\<close>

text \<open>@{thm [source] mestate_def} is the kernel's code constructor for its state record, so the
  selectors the export's own dependency closure reaches need their equations stated against it;
  the record's own are about a constructor the code generator does not have.\<close>

lemma mstate_sel_code[code]:
  "mstate_i (mestate i j m n t \<zeta>) = i"
  "mstate_j (mestate i j m n t \<zeta>) = j"
  "mstate_m (mestate i j m n t \<zeta>) = m"
  "mstate_n (mestate i j m n t \<zeta>) = n"
  "mstate_t (mestate i j m n t \<zeta>) = linearize t"
  by (simp_all add: mestate_def)
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
  udminit_push udmstep uvdfail_nodes udmstate_m
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
