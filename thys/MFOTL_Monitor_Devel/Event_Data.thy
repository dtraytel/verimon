(*<*)
theory Event_Data
  imports
    "HOL-Library.Char_ord"
    Code_Double
    Deriving.Derive
begin
(*>*)

section \<open>Event data\<close>

subsection \<open>8-bit strings\<close>

typedef string8 = "UNIV :: char list set" ..

setup_lifting type_definition_string8

lift_definition empty_string :: string8 is "[]" .
lift_definition string8_literal :: "String.literal \<Rightarrow> string8" is String.explode .
lift_definition literal_string8:: "string8 \<Rightarrow> String.literal" is String.Abs_literal .
declare [[coercion string8_literal]]

instantiation string8 :: "{equal, linorder}"
begin

lift_definition equal_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is HOL.equal .
lift_definition less_eq_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is ord_class.lexordp_eq .
lift_definition less_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is ord_class.lexordp .

instance by intro_classes
    (transfer; auto simp: equal_eq lexordp_conv_lexordp_eq lexordp_eq_linear
      intro: lexordp_eq_refl lexordp_eq_trans lexordp_eq_antisym)+

end

lifting_forget string8.lifting

declare [[code drop: literal_string8 string8_literal  "HOL.equal :: string8 \<Rightarrow> _"
      "(\<le>) :: string8 \<Rightarrow> _" "(<) :: string8 \<Rightarrow> _"
      "Code_Evaluation.term_of :: string8 \<Rightarrow> _"]]

text \<open>The OCaml adaptation relies on OCaml strings being byte sequences that @{text Stdlib} compares
  lexicographically.\<close>

code_printing
  type_constructor string8 \<rightharpoonup> (OCaml) "string"
  | constant "HOL.equal :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Stdlib.(=)"
  | constant "(\<le>) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Stdlib.(<=)"
  | constant "(<) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Stdlib.(<)"
  | constant "empty_string :: string8" \<rightharpoonup> (OCaml) "\"\""
  | constant "string8_literal :: String.literal \<Rightarrow> string8" \<rightharpoonup> (OCaml) "id"
  | constant "literal_string8 :: string8 \<Rightarrow> String.literal" \<rightharpoonup> (OCaml) "id"

text \<open>The Eval adaptation relies on the same for Standard ML strings.\<close>

ML \<open>
structure String8 =
struct
  fun to_term x = @{term Abs_string8} $ HOLogic.mk_string x;
end;
\<close>

code_printing
  type_constructor string8 \<rightharpoonup> (Eval) "string"
  | constant "string8_literal :: String.literal \<Rightarrow> string8" \<rightharpoonup> (Eval) "_"
  | constant "HOL.equal :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "="
  | constant "(\<le>) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<="
  | constant "(<) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<"
  | constant "empty_string :: string8" \<rightharpoonup> (Eval) "\"\""
  | constant "Code_Evaluation.term_of :: string8 \<Rightarrow> term" \<rightharpoonup> (Eval) "String8.to'_term"

derive (eq) ceq string8
derive (linorder) compare string8
derive (compare) ccompare string8

subsection \<open>Division towards zero\<close>

definition div_to_zero :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "div_to_zero x y = (let z = fst (Code_Numeral.divmod_abs x y) in
    if (x < 0) \<noteq> (y < 0) then - z else z)"

definition mod_to_zero :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "mod_to_zero x y = (let z = snd (Code_Numeral.divmod_abs x y) in
    if x < 0 then - z else z)"
subsection \<open>Hash codes\<close>

text \<open>Named constants keep the numerals of the code equations below from being converted from
  their digits at every call.\<close>

definition hc_mask :: integer where "hc_mask = 0xFFFFFFFF"
definition hc_half :: integer where "hc_half = 0x80000000"
definition hc_wrap :: integer where "hc_wrap = 0x100000000"
definition hc_mult :: hashcode where "hc_mult = 33"
definition hc_init :: hashcode where "hc_init = 5381"

lemma bit31_take_bit32: "bit (take_bit 32 (k :: int)) 31 \<longleftrightarrow> 2 ^ 31 \<le> take_bit 32 k"
proof -
  have eq: "take_bit 32 k = 2 ^ 31 * of_bool (bit k 31) + take_bit 31 k"
    using take_bit_Suc_from_most[of 31 k] by simp
  have lt: "0 \<le> take_bit 31 k" "take_bit 31 k < 2 ^ 31"
    by (rule take_bit_nonnegative, rule take_bit_int_less_exp)
  have "bit (take_bit 32 k) 31 \<longleftrightarrow> bit k 31"
    by (simp add: bit_take_bit_iff)
  also have "\<dots> \<longleftrightarrow> 2 ^ 31 \<le> take_bit 32 k"
    unfolding eq using lt by (cases "bit k 31") simp_all
  finally show ?thesis .
qed

lemma bit31_and_mask:
  "bit (Bit_Operations.and (i :: integer) 0xFFFFFFFF) 31 \<longleftrightarrow> 0x80000000 \<le> Bit_Operations.and i 0xFFFFFFFF"
  including integer.lifting
  apply transfer
  using bit31_take_bit32 by (simp add: take_bit_eq_mask mask_eq_exp_minus_1)

lemma hashcode_integer_code [code]:
  "hashcode (i :: integer) = (let i' = Bit_Operations.and i hc_mask in
    Uint32_signed (if hc_half \<le> i' then i' - hc_wrap else i'))"
  unfolding hashcode_integer_def hc_mask_def hc_half_def hc_wrap_def Uint32_code Let_def
    bit31_and_mask by simp

lemma hashcode_list_code [code]:
  "hashcode (xs :: 'a :: hashable list) = foldl (\<lambda>h x. h * hc_mult + hashcode x) hc_init xs"
  by (simp add: hashcode_list_def hc_mult_def hc_init_def)

instantiation string8 :: hashable
begin

definition hashcode_string8 :: "string8 \<Rightarrow> hashcode" where
  "hashcode_string8 s = hashcode (Rep_string8 s)"

definition def_hashmap_size_string8 :: "string8 itself \<Rightarrow> nat" where
  "def_hashmap_size_string8 _ = 10"

instance by intro_classes (simp add: def_hashmap_size_string8_def)

end

instantiation double :: hashable
begin

definition hashcode_double :: "double \<Rightarrow> hashcode" where
  "hashcode_double x = (if is_nan x \<or> is_infinite x then 0 else hashcode (integer_of_double x))"

definition def_hashmap_size_double :: "double itself \<Rightarrow> nat" where
  "def_hashmap_size_double _ = 16"

instance by intro_classes (simp add: def_hashmap_size_double_def)

end

subsection \<open>Event parameters\<close>

datatype event_data = EInt integer | EFloat double | EString string8

derive (eq) ceq event_data
derive ccompare event_data

instantiation event_data :: hashable
begin

primrec hashcode_event_data :: "event_data \<Rightarrow> hashcode" where
  "hashcode_event_data (EInt i) = hashcode i"
| "hashcode_event_data (EFloat x) = hashcode x"
| "hashcode_event_data (EString s) = hashcode s + 1"

definition def_hashmap_size_event_data :: "event_data itself \<Rightarrow> nat" where
  "def_hashmap_size_event_data _ = 16"

instance by intro_classes (simp add: def_hashmap_size_event_data_def)

end

instantiation event_data :: "{ord, plus, minus, uminus, times, divide, modulo}"
begin

fun less_eq_event_data where
  "EInt x \<le> EInt y \<longleftrightarrow> x \<le> y"
| "EFloat x \<le> EFloat y \<longleftrightarrow> x \<le> y"
| "EString x \<le> EString y \<longleftrightarrow> x \<le> y"
| "(_::event_data) \<le> _ \<longleftrightarrow> undefined"

definition less_event_data :: "event_data \<Rightarrow> event_data \<Rightarrow> bool"  where
  "less_event_data x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

fun plus_event_data where
  "EInt x + EInt y = EInt (x + y)"
| "EFloat x + EFloat y = EFloat (x + y)"
| "(_::event_data) + _ = undefined"

fun minus_event_data where
  "EInt x - EInt y = EInt (x - y)"
| "EFloat x - EFloat y = EFloat (x - y)"
| "(_::event_data) - _ = undefined"

fun uminus_event_data where
  "- EInt x = EInt (- x)"
| "- EFloat x = EFloat (- x)"
| "- (_::event_data) = undefined"

fun times_event_data where
  "EInt x * EInt y = EInt (x * y)"
| "EFloat x * EFloat y = EFloat (x * y)"
| "(_::event_data) * _ = undefined"

fun divide_event_data where
  "EInt x div EInt y = EInt (div_to_zero x y)"
| "EFloat x div EFloat y = EFloat (x div y)"
| "(_::event_data) div _ = undefined"

fun modulo_event_data where
  "EInt x mod EInt y = EInt (mod_to_zero x y)"
| "(_::event_data) mod _ = undefined"

instance ..

end

lemma infinite_UNIV_event_data:
  "\<not>finite (UNIV :: event_data set)"
proof -
  define f where "f = (\<lambda>k. EInt k)"
  have inj: "inj_on f (UNIV :: integer set)"
    unfolding f_def by (meson event_data.inject(1) injI)
  show ?thesis using finite_imageD[OF _ inj] 
    by (meson infinite_UNIV_char_0 infinite_iff_countable_subset top_greatest)
qed

instantiation event_data :: card_UNIV begin
definition "finite_UNIV = Phantom(event_data) False"
definition "card_UNIV = Phantom(event_data) 0"
instance by intro_classes (simp_all add: finite_UNIV_event_data_def card_UNIV_event_data_def infinite_UNIV_event_data)
end

primrec integer_of_event_data :: "event_data \<Rightarrow> integer" where
  "integer_of_event_data (EInt _) = undefined"
| "integer_of_event_data (EFloat x) = integer_of_double x"
| "integer_of_event_data (EString _) = undefined"

primrec double_of_event_data :: "event_data \<Rightarrow> double" where
  "double_of_event_data (EInt x) = double_of_integer x"
| "double_of_event_data (EFloat _) = undefined"
| "double_of_event_data (EString _) = undefined"


primrec double_of_event_data_agg :: "event_data \<Rightarrow> double" where
  "double_of_event_data_agg (EInt x) = double_of_integer x"
| "double_of_event_data_agg (EFloat x) = x"
| "double_of_event_data_agg (EString _) = undefined"


(*<*)
end
(*>*)
