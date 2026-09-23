(*<*)
theory Log_Values
  imports Log_Exec
begin
(*>*)

section \<open>Numbers in the log\<close>

text \<open>
  Integers in the log are written as by Zarith's @{text Z.of_string}, on which MonPoly relies: an
  optional sign, then decimal digits, or @{text "0x"}, @{text "0o"} or @{text "0b"} (in either
  case) followed by hexadecimal, octal or binary digits. Unlike @{text Z.of_string}, at least
  one digit is required (Zarith reads the empty string, a lone sign and a lone base prefix as
  0), and underscores are not allowed. Timestamps are the integers that are not negative. The
  specification is on character lists; the functions on byte strings below, from which the code
  is generated, are proved equal to it.
\<close>

subsection \<open>Specification\<close>

definition digit_val :: "nat \<Rightarrow> char \<Rightarrow> nat option" where
  "digit_val b c = (let k = of_char c :: nat in
     if 48 \<le> k \<and> k \<le> 57 \<and> k - 48 < b then Some (k - 48)
     else if 97 \<le> k \<and> k \<le> 102 \<and> k - 87 < b then Some (k - 87)
     else if 65 \<le> k \<and> k \<le> 70 \<and> k - 55 < b then Some (k - 55)
     else None)"

fun digits_val :: "nat \<Rightarrow> nat \<Rightarrow> char list \<Rightarrow> nat option" where
  "digits_val b n [] = Some n"
| "digits_val b n (c # cs) = (case digit_val b c of None \<Rightarrow> None | Some d \<Rightarrow> digits_val b (b * n + d) cs)"

definition nat_of_digits :: "nat \<Rightarrow> char list \<Rightarrow> nat option" where
  "nat_of_digits b cs = (if cs = [] then None else digits_val b 0 cs)"

text \<open>The base prefix, if any, and the digits after it.\<close>

definition base_of :: "char list \<Rightarrow> nat \<times> char list" where
  "base_of cs = (case cs of
     c # x # ds \<Rightarrow> (if c = CHR ''0'' then
         (if x = CHR ''x'' \<or> x = CHR ''X'' then (16, ds)
          else if x = CHR ''o'' \<or> x = CHR ''O'' then (8, ds)
          else if x = CHR ''b'' \<or> x = CHR ''B'' then (2, ds)
          else (10, cs))
       else (10, cs))
   | _ \<Rightarrow> (10, cs))"

definition unsigned_of_string :: "char list \<Rightarrow> nat option" where
  "unsigned_of_string cs = (case base_of cs of (b, ds) \<Rightarrow> nat_of_digits b ds)"

definition int_of_string :: "char list \<Rightarrow> int option" where
  "int_of_string cs = (case cs of
     c # ds \<Rightarrow> (if c = CHR ''-'' then map_option (\<lambda>n. - int n) (unsigned_of_string ds)
       else if c = CHR ''+'' then map_option int (unsigned_of_string ds)
       else map_option int (unsigned_of_string cs))
   | [] \<Rightarrow> None)"

definition nat_of_string :: "char list \<Rightarrow> nat option" where
  "nat_of_string cs = (case int_of_string cs of Some i \<Rightarrow> if 0 \<le> i then Some (nat i) else None | None \<Rightarrow> None)"

subsection \<open>On byte strings\<close>

text \<open>The loops over a byte string @{text s} of length @{text n}, from index @{text i}.\<close>

function bdigits :: "bytes \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> nat option" where
  "bdigits s n b i acc = (if i < n then (case digit_val b (bytes_at s i) of
       None \<Rightarrow> None
     | Some d \<Rightarrow> bdigits s n b (i + 1) (b * acc + d))
   else Some acc)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, b, i, acc). nat_of_integer (n - i))") (auto simp: integer_simps)

declare bdigits.simps[simp del]

definition bnat_of_digits :: "bytes \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> integer \<Rightarrow> nat option" where
  "bnat_of_digits s n b i = (if i < n then bdigits s n b i 0 else None)"

text \<open>The base prefix at index @{text i}: the base and the index of the first digit.\<close>

definition bbase_of :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> nat \<times> integer" where
  "bbase_of s n i = (if i + 1 < n \<and> bytes_at s i = CHR ''0'' then
       (let x = bytes_at s (i + 1) in
        if x = CHR ''x'' \<or> x = CHR ''X'' then (16, i + 2)
        else if x = CHR ''o'' \<or> x = CHR ''O'' then (8, i + 2)
        else if x = CHR ''b'' \<or> x = CHR ''B'' then (2, i + 2)
        else (10, i))
     else (10, i))"

definition bunsigned :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> nat option" where
  "bunsigned s n i = (case bbase_of s n i of (b, j) \<Rightarrow> bnat_of_digits s n b j)"

definition bint_of :: "bytes \<Rightarrow> int option" where
  "bint_of s = (let n = bytes_length s in
     if 0 < n then
       (let c = bytes_at s 0 in
        if c = CHR ''-'' then map_option (\<lambda>n. - int n) (bunsigned s n 1)
        else if c = CHR ''+'' then map_option int (bunsigned s n 1)
        else map_option int (bunsigned s n 0))
     else None)"

definition bnat_of :: "bytes \<Rightarrow> nat option" where
  "bnat_of s = (case bint_of s of Some i \<Rightarrow> if 0 \<le> i then Some (nat i) else None | None \<Rightarrow> None)"

subsection \<open>Correctness\<close>

lemma bdigits_correct:
  assumes "n = bytes_length s" "0 \<le> i" "i \<le> n"
  shows "bdigits s n b i acc = digits_val b acc (drop (nat_of_integer i) (Rep_bytes s))"
  using assms
proof (induction "nat_of_integer (n - i)" arbitrary: i acc)
  case 0
  then have "i = n"
    by (auto simp: integer_simps)
  with 0 show ?case
    by (subst bdigits.simps) (simp add: bytes_length_def)
next
  case (Suc m)
  then have i: "i < n" and m: "m = nat_of_integer (n - (i + 1))"
    by (auto simp: integer_simps)
  have drop: "drop (nat_of_integer i) (Rep_bytes s) = bytes_at s i # drop (nat_of_integer (i + 1)) (Rep_bytes s)"
    using i Suc.prems by (simp add: bytes_at_def nat_of_integer_add1 Cons_nth_drop_Suc nat_of_integer_less_length)
  have "0 \<le> i + 1" "i + 1 \<le> n"
    using i Suc.prems by (auto simp: integer_simps)
  with Suc.hyps(1)[OF m] Suc.prems(1) i drop show ?case
    by (subst bdigits.simps) (auto split: option.splits)
qed

lemma bnat_of_digits_correct:
  assumes "n = bytes_length s" "0 \<le> i" "i \<le> n"
  shows "bnat_of_digits s n b i = nat_of_digits b (drop (nat_of_integer i) (Rep_bytes s))"
  using assms bdigits_correct[OF assms, of b 0]
  by (auto simp: bnat_of_digits_def nat_of_digits_def bytes_length_def integer_simps)

lemma drop_Cons_nth:
  "0 \<le> i \<Longrightarrow> i < bytes_length s \<Longrightarrow>
   drop (nat_of_integer i) (Rep_bytes s) = bytes_at s i # drop (nat_of_integer (i + 1)) (Rep_bytes s)"
  by (simp add: bytes_at_def nat_of_integer_add1 Cons_nth_drop_Suc nat_of_integer_less_length)

lemma bbase_of_correct:
  assumes "n = bytes_length s" "0 \<le> i" "i \<le> n"
  shows "case bbase_of s n i of (b, j) \<Rightarrow> 0 \<le> j \<and> j \<le> n \<and>
    base_of (drop (nat_of_integer i) (Rep_bytes s)) = (b, drop (nat_of_integer j) (Rep_bytes s))"
proof (cases "i + 1 < n \<and> bytes_at s i = CHR ''0''")
  case True
  then have i1: "i + 1 < n" and c: "bytes_at s i = CHR ''0''"
    by auto
  have d: "drop (nat_of_integer i) (Rep_bytes s) =
    bytes_at s i # bytes_at s (i + 1) # drop (nat_of_integer (i + 2)) (Rep_bytes s)"
    using i1 assms drop_Cons_nth[of i s] drop_Cons_nth[of "i + 1" s]
    by (auto simp: integer_simps add.assoc)
  have "0 \<le> i + 2" "i + 2 \<le> n"
    using i1 assms by (auto simp: integer_simps)
  with True assms d show ?thesis
    by (auto simp: bbase_of_def base_of_def Let_def)
next
  case False
  then have "base_of (drop (nat_of_integer i) (Rep_bytes s)) = (10, drop (nat_of_integer i) (Rep_bytes s))"
  proof (cases "i < n")
    case True
    with False have "\<not> (i + 1 < n) \<or> bytes_at s i \<noteq> CHR ''0''"
      by auto
    then show ?thesis
    proof
      assume "\<not> (i + 1 < n)"
      with True assms have "i + 1 = n"
        by (auto simp: integer_simps)
      with True assms have "drop (nat_of_integer i) (Rep_bytes s) = [bytes_at s i]"
        using drop_Cons_nth[of i s] by (auto simp: bytes_length_def integer_simps)
      then show ?thesis
        by (simp add: base_of_def)
    next
      assume "bytes_at s i \<noteq> CHR ''0''"
      with True assms drop_Cons_nth[of i s] show ?thesis
        by (auto simp: base_of_def split: list.splits)
    qed
  next
    case False
    with assms have "drop (nat_of_integer i) (Rep_bytes s) = []"
      by (auto simp: bytes_length_def integer_simps)
    then show ?thesis
      by (simp add: base_of_def)
  qed
  with False assms show ?thesis
    by (auto simp: bbase_of_def)
qed

lemma bunsigned_correct:
  assumes "n = bytes_length s" "0 \<le> i" "i \<le> n"
  shows "bunsigned s n i = unsigned_of_string (drop (nat_of_integer i) (Rep_bytes s))"
  using bbase_of_correct[OF assms] assms bnat_of_digits_correct
  by (auto simp: bunsigned_def unsigned_of_string_def split: prod.splits)

theorem bint_of_correct: "bint_of s = int_of_string (Rep_bytes s)"
proof (cases "Rep_bytes s")
  case (Cons c ds)
  then have n: "0 < bytes_length s" and c: "bytes_at s 0 = c"
    by (auto simp: bytes_length_def bytes_at_def integer_simps)
  have u0: "bunsigned s (bytes_length s) 0 = unsigned_of_string (c # ds)"
    using bunsigned_correct[of "bytes_length s" s 0] Cons by simp
  have "drop (nat_of_integer 1) (Rep_bytes s) = ds"
    using Cons by (simp add: integer_simps)
  then have u1: "bunsigned s (bytes_length s) 1 = unsigned_of_string ds"
    using bunsigned_correct[of "bytes_length s" s 1] n by (simp add: integer_simps)
  show ?thesis
    using n c u0 u1 Cons by (simp add: bint_of_def int_of_string_def Let_def)
next
  case Nil
  then have "\<not> 0 < bytes_length s"
    by (simp add: bytes_length_def integer_simps)
  with Nil show ?thesis
    by (simp add: bint_of_def int_of_string_def)
qed

theorem bnat_of_correct: "bnat_of s = nat_of_string (Rep_bytes s)"
  by (simp add: bnat_of_def nat_of_string_def bint_of_correct)

(*<*)
end
(*>*)
