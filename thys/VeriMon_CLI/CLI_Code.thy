(*<*)
theory CLI_Code
  imports CLI "MFODL_Parser_Code.MFODL_Lexer_Code" "Monitor_Impl.Monomorphic_Code" "Monitor_Exec.Mono_Hot"
    "Monitor_Exec.Push_Rewrite" "Log_Parser.Log_Code" "Monitor_Exec.Log_Monitor"
begin
(*>*)

section \<open>Code export\<close>

text \<open>
  The code of the program @{text verimon} (\<^verbatim>\<open>src/verimon_code.ml\<close>), with the code setup of
  the monitor's export (below) and the parser's code equations for the lexer
  (@{theory MFODL_Parser_Code.MFODL_Lexer_Code}). The trusted part beyond theirs is
  the code printing of the four functions below on byte strings and integers, each by the OCaml
  function with the same meaning: the strings of bytes of a list of characters, the decimal
  representation of an integer (@{text Verimon_runtime.dec_of_z} in
  \<^verbatim>\<open>src/verimon_runtime.ml\<close>, which is @{text Z.to_string} without its general formatting for
  the integers that fit into an OCaml integer), and the test whether a string begins and ends
  with a double quote. The driver prints the verdicts with @{const verdict_fold}, passing for the
  integers @{text Verimon_runtime.add_dec_of_z}, which appends the same digits to its buffer.

  The natural numbers in the parser's tables are printed as constants
  (@{text "Nat (Z.of_int n)"}, which is a constant since Zarith's @{text Z.of_int} is the
  identity on OCaml's integers), rather than as applications of @{const nat_of_integer}, so that
  the tables are static data, which the OCaml compiler does not compile into code.
\<close>

text \<open>
  The code-generator setup of the verified executable monitor, which this theory imports:
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
  multi-way joins (@{const eminit_verimon}, @{theory Monitor_Exec.Push_Rewrite}) -- and builds the initial state
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

declare [[code drop: str8_of_string bytes_of_string str8_of_integer str8_quoted]]

code_printing
  constant str8_of_string \<rightharpoonup> (OCaml) "(fun cs -> String.of'_seq (List.to'_seq cs))"
| constant bytes_of_string \<rightharpoonup> (OCaml) "(fun cs -> String.of'_seq (List.to'_seq cs))"
| constant str8_of_integer \<rightharpoonup> (OCaml) "Verimon'_runtime.dec'_of'_z"
| constant str8_quoted \<rightharpoonup> (OCaml)
    "(fun s -> let n = String.length s in n > 0 && String.get s 0 = Char.chr 34 && String.get s (n - 1) = Char.chr 34)"

definition natlit :: "integer \<Rightarrow> nat" where
  "natlit k = nat_of_integer k"

text \<open>After the preprocessing of numerals, a literal of type @{typ nat} is
  @{term "nat_of_integer (Code_Numeral.Pos k)"}.\<close>

lemma natlit_Pos[code_unfold]: "nat_of_integer (Code_Numeral.Pos k) = natlit (Code_Numeral.Pos k)"
  by (simp add: natlit_def)

declare [[code drop: natlit]]

code_printing
  constant natlit \<rightharpoonup> (OCaml) "Nat"

text \<open>The signature reader takes sets of the types of fields, which the Containers framework
  implements as lists.\<close>

derive (eq) ceq sty
derive (no) ccompare sty
derive (dlist) set_impl sty

export_code
  integer_of_nat nat_of_integer integer_of_int int_of_integer
  cli_main Done Version NeedFile Run
  c_log c_verbose c_unix c_ignore_errors c_stop_first c_mem c_gc_space_overhead c_gc_minor_heap
  vfeed_chunk vfinish vpending VO_VERDICTS
  verdict_out verdict_fold tp_out log_error LE_LOC
  in OCaml module_name Verimon file_prefix "verimon_code"

(*<*)
end
(*>*)
