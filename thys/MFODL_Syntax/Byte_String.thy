(*<*)
theory Byte_String
  imports Main
begin
(*>*)

section \<open>Byte strings\<close>

typedef bytes = "UNIV :: char list set" ..

text \<open>The inputs of the monitor: the log, the formula and signature files, and their constants.
  The code generator maps @{typ bytes} to OCaml's strings.\<close>

(*<*)
end
(*>*)
