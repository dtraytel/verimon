(*<*)
theory CLI_Export
  imports CLI "MFODL_Parser_Code.MFODL_Efficient_Lexer" "Monitor_Impl.Monomorphic_Instance" "Monitor_Exec.Monomorphic_Hot_Spots"
    "Monitor_Exec.Exec_Preparation" "Log_Parser.Log_OCaml" "Monitor_Exec.Log_Monitor"
begin
(*>*)

section \<open>Code export of the program\<close>

text \<open>The OCaml code of @{text verimon}. Beyond the imported code setups, the code printings below
  are the trusted part.\<close>

text \<open>The printings rely on OCaml's strings being the byte sequences of their characters, on
  @{text Verimon_runtime.dec_of_z} agreeing with @{text Z.to_string}, and on @{text "Char.chr 34"}
  being the double quote.\<close>

declare [[code drop: str8_of_string bytes_of_string str8_of_integer str8_quoted]]

code_printing
  constant str8_of_string \<rightharpoonup> (OCaml) "(fun cs -> String.of'_seq (List.to'_seq cs))"
| constant bytes_of_string \<rightharpoonup> (OCaml) "(fun cs -> String.of'_seq (List.to'_seq cs))"
| constant str8_of_integer \<rightharpoonup> (OCaml) "Verimon'_runtime.dec'_of'_z"
| constant str8_quoted \<rightharpoonup> (OCaml)
    "(fun s -> let n = String.length s in n > 0 && String.get s 0 = Char.chr 34 && String.get s (n - 1) = Char.chr 34)"

definition natlit :: "integer \<Rightarrow> nat" where
  "natlit k = nat_of_integer k"

text \<open>After preprocessing, a numeral of type @{typ nat} is
  @{term "nat_of_integer (Code_Numeral.Pos k)"}; printed as a constant, it makes the parser's tables
  static data.\<close>

lemma natlit_Pos[code_unfold]: "nat_of_integer (Code_Numeral.Pos k) = natlit (Code_Numeral.Pos k)"
  by (simp add: natlit_def)

declare [[code drop: natlit]]

text \<open>The printing relies on @{text Nat} being the constructor of the generated natural numbers,
  here applied to positive integers only.\<close>

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
