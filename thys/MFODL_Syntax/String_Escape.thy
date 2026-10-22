(*<*)
theory String_Escape
  imports Main
begin
(*>*)

section \<open>Escaped strings\<close>

text \<open>OCaml's @{text String.escaped}, by which MonPoly's messages show strings: quotes,
  backslashes, the usual control characters, and the other unprintable bytes as decimal
  escapes.\<close>

definition digit_char :: "nat \<Rightarrow> char" where
  "digit_char n = char_of (48 + n)"

definition escaped_char :: "char \<Rightarrow> string" where
  "escaped_char c = (let n = of_char c :: nat in
     if c = CHR 0x22 then [CHR 0x5C, CHR 0x22]
     else if c = CHR 0x5C then [CHR 0x5C, CHR 0x5C]
     else if c = CHR 0x0A then [CHR 0x5C, CHR ''n'']
     else if c = CHR 0x09 then [CHR 0x5C, CHR ''t'']
     else if c = CHR 0x0D then [CHR 0x5C, CHR ''r'']
     else if c = CHR 0x08 then [CHR 0x5C, CHR ''b'']
     else if 32 \<le> n \<and> n \<le> 126 then [c]
     else [CHR 0x5C, digit_char (n div 100), digit_char (n div 10 mod 10), digit_char (n mod 10)])"

definition escaped :: "string \<Rightarrow> string" where
  "escaped s = concat (map escaped_char s)"

(*<*)
end
(*>*)
