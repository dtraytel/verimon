theory MFODL_Efficient_Actions
  imports MFODL_Parser.MFODL_Parser "HOL-Library.Code_Target_Int" "HOL-Library.Code_Abstract_Char"
begin

section \<open>Efficient code for the semantic actions\<close>

text \<open>Code equations proved equal to the definitions. They do not depend on the representation of
  natural numbers in the code, so that both the examples and the monitor use them. The lexer needs
  none: the \<^theory_text>\<open>lexer\<close> command gives it code on evaluated tables.\<close>

text \<open>Character codes as integers, and a comparison instead of a pattern match on a character
  literal, which the code takes apart into its bits.\<close>

lemma digit_val_code [code]: \<open>digit_val c = int_of_integer (integer_of_char c) - 48\<close>
proof -
  have \<open>(of_char c :: integer) = of_nat (of_char c)\<close> by (rule of_nat_of_char[symmetric])
  then show ?thesis unfolding digit_val_def integer_of_char_def by simp
qed

lemma int_of_lexeme_code [code]:
  \<open>int_of_lexeme s = (case s of c # ds \<Rightarrow> if c = CHR ''-'' then - nat_of_digits ds else nat_of_digits s
     | [] \<Rightarrow> 0)\<close>
  unfolding int_of_lexeme_def by (cases s) (auto simp: nat_of_digits_def split: char.split bool.split)

end
