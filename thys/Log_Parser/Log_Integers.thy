(*<*)
theory Log_Integers
  imports Log_Byte_Parser
begin
(*>*)

section \<open>Integers in the log\<close>

text \<open>Integers as read by Zarith's @{text Z.of_string}, on which MonPoly relies, but with
  at most one sign and a digit required after the sign and the base prefix. Timestamps are the
  nonnegative ones.\<close>

subsection \<open>Specification on character lists\<close>

definition digit_val :: "nat \<Rightarrow> char \<Rightarrow> nat option" where
  "digit_val b c = (let k = of_char c :: nat in
     if 48 \<le> k \<and> k \<le> 57 \<and> k - 48 < b then Some (k - 48)
     else if 97 \<le> k \<and> k \<le> 102 \<and> k - 87 < b then Some (k - 87)
     else if 65 \<le> k \<and> k \<le> 70 \<and> k - 55 < b then Some (k - 55)
     else None)"

fun digits_val :: "nat \<Rightarrow> nat \<Rightarrow> char list \<Rightarrow> nat option" where
  "digits_val b n [] = Some n"
| "digits_val b n (c # cs) = (if c = CHR ''_'' then digits_val b n cs
     else case digit_val b c of None \<Rightarrow> None | Some d \<Rightarrow> digits_val b (b * n + d) cs)"

definition nat_of_digits :: "nat \<Rightarrow> char list \<Rightarrow> nat option" where
  "nat_of_digits b cs = (case cs of [] \<Rightarrow> None | c # _ \<Rightarrow> if c = CHR ''_'' then None else digits_val b 0 cs)"

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

subsection \<open>Conversion of byte strings\<close>

function bdigits :: "bytes \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> nat option" where
  "bdigits s n b i acc = (if i < n then (if bytes_at s i = CHR ''_'' then bdigits s n b (i + 1) acc
     else case digit_val b (bytes_at s i) of
       None \<Rightarrow> None
     | Some d \<Rightarrow> bdigits s n b (i + 1) (b * acc + d))
   else Some acc)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, b, i, acc). nat_of_integer (n - i))") (auto simp: integer_simps)

declare bdigits.simps[simp del]

definition bnat_of_digits :: "bytes \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> integer \<Rightarrow> nat option" where
  "bnat_of_digits s n b i = (if i < n then (if bytes_at s i = CHR ''_'' then None else bdigits s n b i 0)
     else None)"

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

subsection \<open>Correctness on byte strings\<close>

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
proof (cases "i < n")
  case True
  then have "drop (nat_of_integer i) (Rep_bytes s) = bytes_at s i # drop (nat_of_integer (i + 1)) (Rep_bytes s)"
    using assms by (simp add: bytes_at_def nat_of_integer_add1 Cons_nth_drop_Suc nat_of_integer_less_length)
  with True bdigits_correct[OF assms, of b 0] show ?thesis
    by (simp add: bnat_of_digits_def nat_of_digits_def)
next
  case False
  with assms have "drop (nat_of_integer i) (Rep_bytes s) = []"
    by (auto simp: bytes_length_def integer_simps)
  with False show ?thesis
    by (simp add: bnat_of_digits_def nat_of_digits_def)
qed

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

subsection \<open>Code on integers\<close>

subsubsection \<open>Digits\<close>

text \<open>The code computes on integers, as arithmetic on the generated natural numbers allocates. A
  digit not of the base, and the value of digits with one, are -1.\<close>

definition idigit :: "integer \<Rightarrow> char \<Rightarrow> integer" where
  "idigit b c = (case digit_val (nat_of_integer b) c of None \<Rightarrow> -1 | Some d \<Rightarrow> integer_of_nat d)"

lemma idigit_alt: "idigit b c = (let k = integer_of_char c in
     if 48 \<le> k \<and> k \<le> 57 then (if k - 48 < b then k - 48 else -1)
     else if 97 \<le> k \<and> k \<le> 102 then (if k - 87 < b then k - 87 else -1)
     else if 65 \<le> k \<and> k \<le> 70 then (if k - 55 < b then k - 55 else -1)
     else -1)"
proof -
  define k :: nat where "k = of_char c"
  have ic: "integer_of_char c = integer_of_nat k"
    by (simp add: k_def integer_of_char_def integer_of_nat_eq_of_nat of_nat_of_char)
  have le: "numeral n \<le> integer_of_nat k \<longleftrightarrow> numeral n \<le> k"
    "integer_of_nat k \<le> numeral n \<longleftrightarrow> k \<le> numeral n" for n
    by (simp_all add: integer_simps integer_of_nat_eq_of_nat)
  have sub: "numeral n \<le> k \<Longrightarrow> integer_of_nat k - numeral n = integer_of_nat (k - numeral n)" for n
    by (simp add: integer_simps integer_of_nat_eq_of_nat)
  have lt: "integer_of_nat m < b \<longleftrightarrow> m < nat_of_integer b" for m
    by (simp add: integer_simps integer_of_nat_eq_of_nat zless_nat_eq_int_zless)
  show ?thesis
    unfolding idigit_def digit_val_def ic k_def[symmetric] Let_def
    by (simp add: le sub lt)
qed

function idigits :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "idigits s n b i acc = (if i < n then (if bytes_at s i = CHR ''_'' then idigits s n b (i + 1) acc
     else let d = idigit b (bytes_at s i) in
       if d < 0 then -1 else idigits s n b (i + 1) (b * acc + d))
   else acc)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, b, i, acc). nat_of_integer (n - i))") (auto simp: integer_simps)

declare idigits.simps[simp del]

lemma idigits: "idigits s n (integer_of_nat b) i (integer_of_nat acc) =
  (case bdigits s n b i acc of None \<Rightarrow> -1 | Some m \<Rightarrow> integer_of_nat m)"
proof (induction "nat_of_integer (n - i)" arbitrary: i acc)
  case 0
  then have "\<not> i < n"
    by (auto simp: integer_simps)
  then show ?case
    by (simp add: idigits.simps bdigits.simps)
next
  case (Suc m)
  then have i: "i < n" and m: "m = nat_of_integer (n - (i + 1))"
    by (auto simp: integer_simps)
  note IH = Suc.hyps(1)[OF m]
  show ?case
  proof (cases "bytes_at s i = CHR ''_''")
    case True
    with i IH[of acc] show ?thesis
      by (subst idigits.simps, subst bdigits.simps) simp
  next
    case False
    show ?thesis
    proof (cases "digit_val b (bytes_at s i)")
      case None
      then have "idigit (integer_of_nat b) (bytes_at s i) = -1"
        by (simp add: idigit_def)
      with None False i show ?thesis
        by (subst idigits.simps, subst bdigits.simps) simp
    next
      case (Some d)
      then have "idigit (integer_of_nat b) (bytes_at s i) = integer_of_nat d"
        by (simp add: idigit_def)
      moreover have "\<not> integer_of_nat d < 0"
        by (simp add: less_integer.rep_eq)
      moreover have "integer_of_nat b * integer_of_nat acc + integer_of_nat d = integer_of_nat (b * acc + d)"
        by (simp add: integer_of_nat_eq_of_nat)
      ultimately show ?thesis
        using Some False i IH[of "b * acc + d"] by (subst idigits.simps, subst bdigits.simps) (simp add: Let_def)
    qed
  qed
qed

lemma bnat_of_digits_idigits: "bnat_of_digits s n b i = (if i < n then
    (if bytes_at s i = CHR ''_'' then None
     else let r = idigits s n (integer_of_nat b) i 0 in if r < 0 then None else Some (nat_of_integer r))
  else None)"
  using idigits[of s n b i 0]
  by (auto simp: bnat_of_digits_def Let_def integer_simps integer_of_nat_eq_of_nat split: option.splits)

subsubsection \<open>Long numerals\<close>

text \<open>The loop takes time quadratic in the number of digits. For long numerals, the code collects
  the digits and combines neighbouring blocks pairwise, halving their number in each round.\<close>

function bdlist :: "bytes \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> integer \<Rightarrow> nat list option" where
  "bdlist s n b i = (if i < n then (if bytes_at s i = CHR ''_'' then bdlist s n b (i + 1)
     else case digit_val b (bytes_at s i) of
       None \<Rightarrow> None
     | Some d \<Rightarrow> map_option (Cons d) (bdlist s n b (i + 1)))
   else Some [])"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, b, i). nat_of_integer (n - i))") (auto simp: integer_simps)

declare bdlist.simps[simp del]

lemma bdigits_bdlist: "bdigits s n b i acc = map_option (foldl (\<lambda>a d. b * a + d) acc) (bdlist s n b i)"
proof (induction "nat_of_integer (n - i)" arbitrary: i acc)
  case 0
  then have "\<not> i < n"
    by (auto simp: integer_simps)
  then show ?case
    by (simp add: bdigits.simps bdlist.simps)
next
  case (Suc m)
  then have i: "i < n" and m: "m = nat_of_integer (n - (i + 1))"
    by (auto simp: integer_simps)
  note IH = Suc.hyps(1)[OF m]
  show ?case
    using i IH by (subst bdigits.simps, subst bdlist.simps) (auto simp: option.map_comp comp_def split: option.splits)
qed

function icollect :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "icollect s n b i acc = (if i < n then (if bytes_at s i = CHR ''_'' then icollect s n b (i + 1) acc
     else let d = idigit b (bytes_at s i) in
       if d < 0 then None else icollect s n b (i + 1) (d # acc))
   else Some acc)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, b, i, acc). nat_of_integer (n - i))") (auto simp: integer_simps)

declare icollect.simps[simp del]

lemma icollect: "icollect s n (integer_of_nat b) i acc =
  map_option (\<lambda>ds. rev (map integer_of_nat ds) @ acc) (bdlist s n b i)"
proof (induction "nat_of_integer (n - i)" arbitrary: i acc)
  case 0
  then have "\<not> i < n"
    by (auto simp: integer_simps)
  then show ?case
    by (simp add: icollect.simps bdlist.simps)
next
  case (Suc m)
  then have i: "i < n" and m: "m = nat_of_integer (n - (i + 1))"
    by (auto simp: integer_simps)
  note IH = Suc.hyps(1)[OF m]
  show ?case
  proof (cases "bytes_at s i = CHR ''_''")
    case True
    with i IH[of acc] show ?thesis
      by (subst icollect.simps, subst bdlist.simps) simp
  next
    case False
    show ?thesis
    proof (cases "digit_val b (bytes_at s i)")
      case None
      then have "idigit (integer_of_nat b) (bytes_at s i) = -1"
        by (simp add: idigit_def)
      with None False i show ?thesis
        by (subst icollect.simps, subst bdlist.simps) simp
    next
      case (Some d)
      then have "idigit (integer_of_nat b) (bytes_at s i) = integer_of_nat d"
        by (simp add: idigit_def)
      moreover have "\<not> integer_of_nat d < 0"
        by (simp add: less_integer.rep_eq)
      ultimately show ?thesis
        using Some False i IH[of "integer_of_nat d # acc"]
        by (subst icollect.simps, subst bdlist.simps) (simp add: Let_def option.map_comp comp_def)
    qed
  qed
qed

text \<open>Blocks as pairs of a value and a weight, the base to the power of their length.\<close>

definition pvals :: "integer \<Rightarrow> (integer \<times> integer) list \<Rightarrow> integer" where
  "pvals a xs = foldl (\<lambda>a (v, p). a * p + v) a xs"

fun istep :: "(integer \<times> integer) list \<Rightarrow> (integer \<times> integer) list \<Rightarrow> (integer \<times> integer) list" where
  "istep ((v1, p1) # (v2, p2) # xs) acc = istep xs ((v1 * p2 + v2, p1 * p2) # acc)"
| "istep xs acc = rev acc @ xs"

lemma pvals_istep: "pvals a (istep xs acc) = pvals a (rev acc @ xs)"
  by (induction xs acc rule: istep.induct) (simp_all add: pvals_def algebra_simps)

lemma length_istep: "length (istep xs acc) = length acc + (length xs + 1) div 2"
  by (induction xs acc rule: istep.induct) auto

function icombine :: "(integer \<times> integer) list \<Rightarrow> integer" where
  "icombine [] = 0"
| "icombine [(v, p)] = v"
| "icombine (x # y # xs) = icombine (istep (x # y # xs) [])"
  by pat_completeness auto
termination
  by (relation "measure length") (auto simp: length_istep)

lemma icombine: "icombine xs = pvals 0 xs"
proof (induction xs rule: icombine.induct)
  case (3 x y xs)
  then show ?case
    by (simp add: pvals_istep)
qed (simp_all add: pvals_def)

lemma pvals_digits: "pvals a (map (\<lambda>d. (d, b)) ds) = foldl (\<lambda>a d. a * b + d) a ds"
  by (induction ds arbitrary: a) (simp_all add: pvals_def)

lemma foldl_integer_of_nat:
  "foldl (\<lambda>a d. a * integer_of_nat b + d) (integer_of_nat acc) (map integer_of_nat ds) =
   integer_of_nat (foldl (\<lambda>a d. b * a + d) acc ds)"
proof (induction ds arbitrary: acc)
  case (Cons d ds)
  have "integer_of_nat acc * integer_of_nat b + integer_of_nat d = integer_of_nat (b * acc + d)"
    by (simp add: integer_of_nat_eq_of_nat algebra_simps)
  with Cons.IH[of "b * acc + d"] show ?case
    by simp
qed simp

lemma fold_Cons_map: "fold (\<lambda>d acc. f d # acc) xs ys = rev (map f xs) @ ys"
  by (induction xs arbitrary: ys) simp_all

lemma bnat_of_digits_code[code]: "bnat_of_digits s n b i = (if i < n then
    (if bytes_at s i = CHR ''_'' then None
     else if n - i \<le> 256 then
       (let r = idigits s n (integer_of_nat b) i 0 in if r < 0 then None else Some (nat_of_integer r))
     else (case icollect s n (integer_of_nat b) i [] of
       None \<Rightarrow> None
     | Some rds \<Rightarrow> Some (nat_of_integer (icombine (fold (\<lambda>d acc. (d, integer_of_nat b) # acc) rds [])))))
  else None)"
proof -
  have F: "foldl (\<lambda>a d. a * integer_of_nat b + d) 0 (map integer_of_nat ds) =
    integer_of_nat (foldl (\<lambda>a d. b * a + d) 0 ds)" for ds
    using foldl_integer_of_nat[of b 0 ds] by (simp add: integer_of_nat_eq_of_nat)
  have D: "(case icollect s n (integer_of_nat b) i [] of
      None \<Rightarrow> None
    | Some rds \<Rightarrow> Some (nat_of_integer (icombine (fold (\<lambda>d acc. (d, integer_of_nat b) # acc) rds [])))) =
    bdigits s n b i 0"
    by (auto simp: bdigits_bdlist icollect fold_Cons_map rev_map icombine pvals_digits F
        split: option.splits)
  have I: "i < n \<Longrightarrow> bytes_at s i \<noteq> CHR ''_'' \<Longrightarrow>
    (let r = idigits s n (integer_of_nat b) i 0 in if r < 0 then None else Some (nat_of_integer r)) =
    bdigits s n b i 0"
    using bnat_of_digits_idigits[of s n b i] by (simp add: bnat_of_digits_def)
  show ?thesis
    unfolding bnat_of_digits_def by (simp add: D I)
qed

subsubsection \<open>Fused conversion\<close>

text \<open>The conversion of fields as one function on integers, without the generated natural numbers.\<close>

definition inat_of_digits :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer option" where
  "inat_of_digits s n b i = (if i < n then
    (if bytes_at s i = CHR ''_'' then None
     else if n - i \<le> 256 then (let r = idigits s n b i 0 in if r < 0 then None else Some r)
     else (case icollect s n b i [] of
       None \<Rightarrow> None
     | Some rds \<Rightarrow> Some (icombine (fold (\<lambda>d acc. (d, b) # acc) rds []))))
  else None)"

lemma inat_of_digits: "inat_of_digits s n (integer_of_nat b) i = map_option integer_of_nat (bnat_of_digits s n b i)"
proof -
  have F: "foldl (\<lambda>a d. a * integer_of_nat b + d) 0 (map integer_of_nat ds) =
    integer_of_nat (foldl (\<lambda>a d. b * a + d) 0 ds)" for ds
    using foldl_integer_of_nat[of b 0 ds] by (simp add: integer_of_nat_eq_of_nat)
  have D: "(case icollect s n (integer_of_nat b) i [] of
      None \<Rightarrow> None
    | Some rds \<Rightarrow> Some (icombine (fold (\<lambda>d acc. (d, integer_of_nat b) # acc) rds []))) =
    map_option integer_of_nat (bdigits s n b i 0)"
    by (auto simp: bdigits_bdlist icollect fold_Cons_map rev_map icombine pvals_digits F
        split: option.splits)
  have I: "(let r = idigits s n (integer_of_nat b) i 0 in if r < 0 then None else Some r) =
    map_option integer_of_nat (bdigits s n b i 0)"
    using idigits[of s n b i 0] by (auto simp: Let_def integer_of_nat_eq_of_nat split: option.splits)
  show ?thesis
    unfolding inat_of_digits_def bnat_of_digits_def by (simp add: D I)
qed

definition ibbase_of :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<times> integer" where
  "ibbase_of s n i = (case bbase_of s n i of (b, j) \<Rightarrow> (integer_of_nat b, j))"

lemma ibbase_of_code[code]: "ibbase_of s n i = (if i + 1 < n \<and> bytes_at s i = CHR ''0'' then
       (let x = bytes_at s (i + 1) in
        if x = CHR ''x'' \<or> x = CHR ''X'' then (16, i + 2)
        else if x = CHR ''o'' \<or> x = CHR ''O'' then (8, i + 2)
        else if x = CHR ''b'' \<or> x = CHR ''B'' then (2, i + 2)
        else (10, i))
     else (10, i))"
  by (simp add: ibbase_of_def bbase_of_def Let_def integer_of_nat_eq_of_nat)

definition ibint_of :: "bytes \<Rightarrow> integer option" where
  "ibint_of s = map_option integer_of_int (bint_of s)"

lemma ibunsigned: "(case ibbase_of s n i of (b, j) \<Rightarrow> inat_of_digits s n b j) =
  map_option integer_of_nat (bunsigned s n i)"
  by (simp add: ibbase_of_def bunsigned_def inat_of_digits split: prod.splits)

subsubsection \<open>Short decimal numerals\<close>

text \<open>Most numerals in logs are short and decimal. A loop specialised to base 10 needs fewer
  operations on integers per digit.\<close>

function ddigits :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
  "ddigits s n i acc = (if i < n then (let c = bytes_at s i in
     if CHR ''0'' \<le> c \<and> c \<le> CHR ''9'' then ddigits s n (i + 1) (acc * 10 + (integer_of_char c - 48))
     else if c = CHR ''_'' then ddigits s n (i + 1) acc
     else -1)
   else acc)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, n, i, acc). nat_of_integer (n - i))") (auto simp: integer_simps)

declare ddigits.simps[simp del]

lemma idigit_10: "idigit 10 c = (if CHR ''0'' \<le> c \<and> c \<le> CHR ''9'' then integer_of_char c - 48 else -1)"
proof -
  have k: "integer_of_char c = integer_of_nat (of_char c)"
    by (simp add: integer_of_char_def integer_of_nat_eq_of_nat of_nat_of_char)
  show ?thesis
    unfolding idigit_alt k Let_def less_eq_char_def
    by (auto simp: integer_simps integer_of_nat_eq_of_nat)
qed

lemma ddigits: "ddigits s n i acc = idigits s n 10 i acc"
proof (induction "nat_of_integer (n - i)" arbitrary: i acc)
  case 0
  then have "\<not> i < n"
    by (auto simp: integer_simps)
  then show ?case
    by (simp add: ddigits.simps idigits.simps)
next
  case (Suc m)
  then have i: "i < n" and m: "m = nat_of_integer (n - (i + 1))"
    by (auto simp: integer_simps)
  note IH = Suc.hyps(1)[OF m]
  have k: "integer_of_char c = integer_of_nat (of_char c)" for c
    by (simp add: integer_of_char_def integer_of_nat_eq_of_nat of_nat_of_char)
  have "CHR ''_'' \<noteq> bytes_at s i \<and> 48 \<le> integer_of_char (bytes_at s i)"
    if "CHR ''0'' \<le> bytes_at s i" "bytes_at s i \<le> CHR ''9''"
    using that unfolding k by (auto simp: less_eq_char_def integer_simps integer_of_nat_eq_of_nat dest: sym)
  with i IH show ?case
    by (subst ddigits.simps, subst idigits.simps) (auto simp: Let_def idigit_10 mult.commute)
qed

definition iunsigned :: "bytes \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer option" where
  "iunsigned s n i = (case ibbase_of s n i of (b, j) \<Rightarrow> inat_of_digits s n b j)"

lemma iunsigned_code: "iunsigned s n i =
    (if i < n \<and> n - i \<le> 256 \<and> CHR ''1'' \<le> bytes_at s i \<and> bytes_at s i \<le> CHR ''9'' then
      (let r = ddigits s n i 0 in if r < 0 then None else Some r)
    else (case ibbase_of s n i of (b, j) \<Rightarrow> inat_of_digits s n b j))"
proof (cases "i < n \<and> n - i \<le> 256 \<and> CHR ''1'' \<le> bytes_at s i \<and> bytes_at s i \<le> CHR ''9''")
  case True
  then have "bytes_at s i \<noteq> CHR ''0''" "bytes_at s i \<noteq> CHR ''_''" "CHR ''0'' \<le> bytes_at s i"
    by (auto simp: less_eq_char_def dest: sym)
  with True show ?thesis
    by (simp add: iunsigned_def ibbase_of_code inat_of_digits_def ddigits)
next
  case False
  then show ?thesis
    by (simp only: if_False iunsigned_def)
qed

lemma ibint_of_code: "ibint_of s = (let n = bytes_length s in
     if 0 < n then
       (let c = bytes_at s 0 in
        if c = CHR ''-'' then map_option uminus (iunsigned s n 1)
        else if c = CHR ''+'' then iunsigned s n 1
        else iunsigned s n 0)
     else None)"
  unfolding iunsigned_def ibunsigned
  by (simp add: ibint_of_def bint_of_def Let_def option.map_comp comp_def integer_of_nat_eq_of_nat)

(*<*)
end
(*>*)
