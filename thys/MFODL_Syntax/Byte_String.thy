(*<*)
theory Byte_String
  imports Main
begin
(*>*)

section \<open>Byte strings\<close>

typedef bytes = "UNIV :: char list set" ..

text \<open>The inputs of the monitor are strings of bytes: the log, the formula and signature files,
  and the constants in them. The code generator maps @{typ bytes} to OCaml's strings (theory
  @{text Log_Code}).\<close>

(*<*)
end
(*>*)
