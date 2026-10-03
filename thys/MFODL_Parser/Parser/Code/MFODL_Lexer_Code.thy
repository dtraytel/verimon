theory MFODL_Lexer_Code
  imports MFODL_Parser.MFODL_Parser "HOL-Library.Code_Target_Int" "HOL-Library.Code_Abstract_Char"
begin

text \<open>Code equations for the lexer model and the semantic actions, proved equal to their
  definitions. They do not depend on the representation of natural numbers in the code, so that
  both the export of the parser (\<^theory>\<open>MFODL_Parser_Code.MFODL_Parser_Code\<close>, with binary
  naturals) and that of the verified monitor (session \<^verbatim>\<open>VeriMon_CLI\<close>, with Zarith's
  integers) use them.\<close>

section \<open>Code for the lexer\<close>

text \<open>Code equations for the lexer model of \<^theory>\<open>MFODL_Parser.MFODL_Lexer\<close>,
  proved equal to its definitions. With binary naturals the definitions spend
  most of their time in arithmetic: character classes compute character codes
  as naturals, every keyword rule takes a prefix of the input of the keyword's
  length at every position, and the look-ahead of \<^const>\<open>m_unit\<close> and
  \<^const>\<open>m_rat\<close> computes the length of the rest of the input. Here character
  codes are integers, keywords are compared character by character, the
  look-ahead inspects the input after the digits, and only the rules that can
  match an input starting with its first character are tried (a table indexed
  by the character code).\<close>

lemma integer_of_char_nat: \<open>integer_of_char c = integer_of_nat (of_char c)\<close>
  unfolding integer_of_char_def integer_of_nat_eq_of_nat by (rule of_nat_of_char[symmetric])

lemma is_digit_code [code]:
  \<open>is_digit c = (let k = integer_of_char c in 48 \<le> k \<and> k \<le> 57)\<close>
  unfolding is_digit_def in_range_def integer_of_char_nat Let_def
  by (simp add: integer_of_nat_eq_of_nat)

lemma is_letter_code [code]:
  \<open>is_letter c = (let k = integer_of_char c in (97 \<le> k \<and> k \<le> 122) \<or> (65 \<le> k \<and> k \<le> 90))\<close>
  unfolding is_letter_def in_range_def integer_of_char_nat Let_def
  by (simp add: integer_of_nat_eq_of_nat)

fun starts_with :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>starts_with [] _ = True\<close>
| \<open>starts_with (_ # _) [] = False\<close>
| \<open>starts_with (a # k) (b # s) = (a = b \<and> starts_with k s)\<close>

lemma starts_with_iff: \<open>starts_with k s \<longleftrightarrow> take (length k) s = k\<close>
  by (induction k s rule: starts_with.induct) auto

lemma m_fixed_code [code]:
  \<open>m_fixed k s = (if k \<noteq> [] \<and> starts_with k s then Some (length k) else None)\<close>
  unfolding m_fixed_def starts_with_iff ..

lemma count_digits_code [code]:
  \<open>count_digits [] = 0\<close>
  \<open>count_digits (c # s) = (if is_digit c then Suc (count_digits s) else 0)\<close>
  unfolding count_digits_def by simp_all

lemma sign_len_code [code]:
  \<open>sign_len s = (case s of c # _ \<Rightarrow> if c = CHR ''-'' then 1 else 0 | [] \<Rightarrow> 0)\<close>
  unfolding sign_len_def by (cases s) (auto split: char.split bool.split)

lemma drop_count_digits: \<open>drop (count_digits s) s = dropWhile is_digit s\<close>
  unfolding count_digits_def dropWhile_eq_drop ..

lemma nth_less_length_case:
  \<open>(n < length s \<and> P (s ! n)) = (case drop n s of c # _ \<Rightarrow> P c | [] \<Rightarrow> False)\<close>
proof (cases \<open>n < length s\<close>)
  case True
  then have \<open>drop n s = s ! n # drop (Suc n) s\<close> by (rule Cons_nth_drop_Suc[symmetric])
  then show ?thesis using True by simp
qed simp

lemma nth_eq_case:
  \<open>(n < length s \<and> s ! n = c) = (case drop n s of d # _ \<Rightarrow> d = c | [] \<Rightarrow> False)\<close>
  using nth_less_length_case[where P = \<open>\<lambda>x. x = c\<close>] by simp

lemma m_unit_code [code]:
  \<open>m_unit s = (let n = count_digits s in
     if 0 < n \<and> (case dropWhile is_digit s of c # _ \<Rightarrow> is_letter c | [] \<Rightarrow> False)
     then Some (Suc n) else None)\<close>
  unfolding m_unit_def Let_def nth_less_length_case drop_count_digits ..

lemma m_rat_code [code]:
  \<open>m_rat s = (let k = sign_len s; t = drop k s; n = count_digits t; u = dropWhile is_digit t in
     if 0 < n \<and> (case u of c # _ \<Rightarrow> c = CHR ''.'' | [] \<Rightarrow> False)
     then Some (k + n + 1 + count_digits (tl u)) else None)\<close>
proof -
  have d: \<open>drop (k + count_digits (drop k s)) s = dropWhile is_digit (drop k s)\<close> for k
    by (simp add: drop_count_digits[symmetric] add.commute)
  have e: \<open>drop (k + count_digits (drop k s) + 1) s = tl (dropWhile is_digit (drop k s))\<close> for k
    using d[of k] by (simp add: drop_Suc tl_drop[symmetric] drop_drop add.commute)
  show ?thesis
    unfolding m_rat_def Let_def nth_eq_case d e ..
qed

text \<open>Dispatch on the first character: each rule comes with a condition on the
  first character of every input it matches, and only the rules whose
  condition holds are tried.\<close>

definition rule_starts :: \<open>(char \<Rightarrow> bool) list\<close> where
  \<open>rule_starts =
    [is_space] @ map (\<lambda>(k, t) c. c = hd k) keyword_table @
    [is_digit, \<lambda>c. sign_len [c] \<noteq> 0 \<or> is_digit c, \<lambda>c. sign_len [c] \<noteq> 0 \<or> is_digit c,
     \<lambda>c. c = CHR 0x22, \<lambda>c. c = CHR ''r'', is_str_start, \<lambda>c. c = CHR ''('', \<lambda>c. c = CHR ''#'']\<close>

definition starts_ok :: \<open>((string \<Rightarrow> nat option) \<times> action) \<Rightarrow> (char \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>starts_ok r p \<longleftrightarrow> (\<forall>s. fst r s \<noteq> None \<longrightarrow> (\<exists>c s'. s = c # s' \<and> p c))\<close>

lemma count_digits_pos: \<open>0 < count_digits s \<Longrightarrow> \<exists>c s'. s = c # s' \<and> is_digit c\<close>
  by (cases s) (auto simp: count_digits_def split: if_splits)

lemma starts_ok_fixed: \<open>starts_ok (m_fixed k, a) (\<lambda>c. c = hd k)\<close>
  unfolding starts_ok_def m_fixed_def
  by (auto simp: neq_Nil_conv split: if_splits) (metis list.sel(1) take_Suc_Cons neq_Nil_conv take_eq_Nil)

lemma sign_len_Cons: \<open>sign_len (c # s) = sign_len [c]\<close>
  unfolding sign_len_def by (simp split: list.split)

lemma starts_ok_sign:
  assumes \<open>0 < count_digits (drop (sign_len s) s)\<close>
  shows \<open>\<exists>c s'. s = c # s' \<and> (sign_len [c] \<noteq> 0 \<or> is_digit c)\<close>
proof (cases s)
  case Nil
  then show ?thesis using assms by (simp add: count_digits_def)
next
  case (Cons c s')
  have \<open>is_digit c \<or> sign_len [c] \<noteq> 0\<close>
  proof (rule disjCI)
    assume \<open>\<not> sign_len [c] \<noteq> 0\<close>
    then have \<open>sign_len s = 0\<close> unfolding Cons by (simp only: sign_len_Cons[of c s'] not_not)
    then have \<open>0 < count_digits s\<close> using assms by (simp only: drop_0)
    from count_digits_pos[OF this] show \<open>is_digit c\<close> unfolding Cons by blast
  qed
  then show ?thesis unfolding Cons by blast
qed

lemma rules_starts: \<open>list_all2 starts_ok rules rule_starts\<close>
proof -
  have kw: \<open>list_all2 starts_ok (map (\<lambda>(k, t). (m_fixed k, Emit t)) keyword_table)
      (map (\<lambda>(k, t) c. c = hd k) keyword_table)\<close>
    unfolding list_all2_map1 list_all2_map2 by (rule list_all2_refl) (auto intro: starts_ok_fixed)
  have sp: \<open>starts_ok (m_space, Skip) is_space\<close>
    unfolding starts_ok_def m_space_def by (auto split: list.splits if_splits)
  have tl: \<open>list_all2 starts_ok
     [(m_unit, EmitTU), (m_int, Emit INTEGER), (m_rat, Emit RAT), (m_quoted, Emit STR_CST),
      (m_regexp, Emit REGEXP_CST), (m_string, Emit NAME),
      (m_fixed ''(*'', Comment), (m_fixed ''#'', LineComment)]
     [is_digit, \<lambda>c. sign_len [c] \<noteq> 0 \<or> is_digit c, \<lambda>c. sign_len [c] \<noteq> 0 \<or> is_digit c,
      \<lambda>c. c = CHR 0x22, \<lambda>c. c = CHR ''r'', is_str_start, \<lambda>c. c = CHR ''('', \<lambda>c. c = CHR ''#'']\<close>
    using starts_ok_fixed[of \<open>''(*''\<close> Comment] starts_ok_fixed[of \<open>''#''\<close> LineComment]
    unfolding starts_ok_def
    by (auto simp: m_unit_def m_int_def m_rat_def m_quoted_def m_regexp_def m_string_def Let_def
        dest: count_digits_pos starts_ok_sign split: list.splits if_splits)
  show ?thesis unfolding rules_def rule_starts_def
    by (intro list_all2_appendI list.rel_intros(2) list.rel_intros(1) kw sp tl)
qed

definition rules_for :: \<open>char \<Rightarrow> ((string \<Rightarrow> nat option) \<times> action) list\<close> where
  \<open>rules_for c = map fst (filter (\<lambda>(r, p). p c) (zip rules rule_starts))\<close>

lemma best_match_filter:
  \<open>(\<And>x. x \<in> set xs \<Longrightarrow> \<not> Q x \<Longrightarrow> fst (fst x) s = None) \<Longrightarrow>
     best_match b (map fst (filter Q xs)) s = best_match b (map fst xs) s\<close>
proof (induction xs arbitrary: b)
  case (Cons x xs)
  have ih: \<open>best_match b' (map fst (filter Q xs)) s = best_match b' (map fst xs) s\<close> for b'
    using Cons by simp
  obtain m a p where x: \<open>x = ((m, a), p)\<close> by (cases x) auto
  show ?case
  proof (cases \<open>Q x\<close>)
    case True
    then show ?thesis using ih unfolding x by simp
  next
    case False
    then have \<open>m s = None\<close> using Cons.prems[of x] unfolding x by simp
    then show ?thesis using ih False unfolding x by simp
  qed
qed simp

lemma best_match_none: \<open>(\<And>r. r \<in> set rs \<Longrightarrow> fst r s = None) \<Longrightarrow> best_match b rs s = b\<close>
proof (induction rs arbitrary: b)
  case (Cons r rs)
  obtain m a where r: \<open>r = (m, a)\<close> by (cases r)
  have \<open>m s = None\<close> using Cons.prems[of r] unfolding r by simp
  then show ?case using Cons unfolding r by simp
qed simp

lemma rules_Nil: \<open>r \<in> set rules \<Longrightarrow> fst r [] = None\<close>
  using rules_starts unfolding list_all2_conv_all_nth in_set_conv_nth starts_ok_def by fastforce

lemma best_match_rules_for:
  \<open>best_match b rules (c # s) = best_match b (rules_for c) (c # s)\<close>
proof -
  have len: \<open>length rules = length rule_starts\<close> using rules_starts list_all2_lengthD by blast
  have \<open>best_match b (rules_for c) (c # s) = best_match b (map fst (zip rules rule_starts)) (c # s)\<close>
    unfolding rules_for_def
  proof (rule best_match_filter)
    fix x assume x: \<open>x \<in> set (zip rules rule_starts)\<close> and n: \<open>\<not> (case x of (r, p) \<Rightarrow> p c)\<close>
    obtain r p where xr: \<open>x = (r, p)\<close> by (cases x)
    have \<open>starts_ok r p\<close>
      using x rules_starts unfolding xr by (auto simp: list_all2_conv_all_nth in_set_zip)
    then show \<open>fst (fst x) (c # s) = None\<close> using n unfolding xr starts_ok_def by auto
  qed
  then show ?thesis using len by simp
qed

definition rules_tab :: \<open>((string \<Rightarrow> nat option) \<times> action) list iarray\<close> where
  \<open>rules_tab = IArray (map (\<lambda>i. rules_for (char_of i)) [0..<256])\<close>

definition lex_match :: \<open>string \<Rightarrow> (nat \<times> action) option\<close> where
  \<open>lex_match s = best_match None rules s\<close>

lemma lex_match_unfold [code_unfold]: \<open>best_match None rules s = lex_match s\<close>
  unfolding lex_match_def ..

lemma lex_match_code [code]:
  \<open>lex_match s = (case s of [] \<Rightarrow> None
     | c # _ \<Rightarrow> best_match None (IArray.sub' (rules_tab, integer_of_char c)) s)\<close>
proof (cases s)
  case Nil
  then show ?thesis unfolding lex_match_def using best_match_none[OF rules_Nil] by simp
next
  case (Cons c s')
  have \<open>nat_of_integer (integer_of_char c) = of_char c\<close>
    by (simp add: integer_of_char_nat)
  moreover have \<open>of_char c < (256 :: nat)\<close> by (metis of_char_mod_256 mod_less_divisor zero_less_numeral)
  ultimately have \<open>IArray.sub' (rules_tab, integer_of_char c) = rules_for c\<close>
    by (simp add: rules_tab_def)
  then show ?thesis unfolding lex_match_def Cons best_match_rules_for by simp
qed


section \<open>Code for the semantic actions\<close>

text \<open>Integer literals: the character code as an integer, and a comparison
  instead of a pattern match on a character literal, which the code generator
  implements by taking the character apart into its bits.\<close>

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
