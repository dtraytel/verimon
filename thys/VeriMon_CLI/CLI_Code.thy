(*<*)
theory CLI_Code
  imports CLI "MFODL_Parser_Code.MFODL_Lexer_Code" "MFODL_Monitor_Exec.Monitor_Code"
begin
(*>*)

section \<open>Code export\<close>

text \<open>
  The code of the program @{text verimon} (\<^verbatim>\<open>src/verimon_code.ml\<close>), with the code setup of
  the monitor's export (@{theory MFODL_Monitor_Exec.Monitor_Code}) and the parser's code equations
  for the lexer (@{theory MFODL_Parser_Code.MFODL_Lexer_Code}). The trusted part beyond theirs is
  the code printing of the four functions below on byte strings and integers, each by the OCaml
  function with the same meaning: the strings of bytes of a list of characters, the decimal
  representation of an integer, and the test whether a string begins and ends with a double quote.

  The natural numbers in the parser's tables are printed as constants
  (@{text "Nat (Z.of_int n)"}, which is a constant since Zarith's @{text Z.of_int} is the
  identity on OCaml's integers), rather than as applications of @{const nat_of_integer}, so that
  the tables are static data, which the OCaml compiler does not compile into code.
\<close>

declare [[code drop: str8_of_string bytes_of_string str8_of_integer str8_quoted]]

code_printing
  constant str8_of_string \<rightharpoonup> (OCaml) "(fun cs -> String.of'_seq (List.to'_seq cs))"
| constant bytes_of_string \<rightharpoonup> (OCaml) "(fun cs -> String.of'_seq (List.to'_seq cs))"
| constant str8_of_integer \<rightharpoonup> (OCaml) "Z.to'_string"
| constant str8_quoted \<rightharpoonup> (OCaml)
    "(fun s -> let n = String.length s in n > 0 && String.get s 0 = '\"' && String.get s (n - 1) = '\"')"

definition natlit :: "integer \<Rightarrow> nat" where
  "natlit = nat_of_integer"

lemma natlit_numeral[code_unfold]: "(numeral k :: nat) = natlit (numeral k)"
  by (simp add: natlit_def)

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
  c_log c_verbose c_ignore_errors c_stop_first c_mem c_gc_space_overhead c_gc_minor_heap
  vfeed_chunk vfinish vpending VO_VERDICTS
  verdict_out tp_out log_error LE_LOC
  in OCaml module_name Verimon file_prefix "verimon_code"

(*<*)
end
(*>*)
