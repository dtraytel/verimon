(*<*)
theory Preliminaries
  imports
    Interval
    Trace
    "HOL-Library.Simps_Case_Conv"
    "HOL-Library.Mapping"
begin
(*>*)


section \<open> Preliminary lemmas \<close>

unbundle lattice_syntax \<comment> \<open> enable notation \<close>


subsection \<open> Lists \<close>

lemma foldr_union: "foldr (\<union>) Xs {} = \<Union>(set Xs)"
  by (induction Xs) auto

lemma list_all2_replicate[simp]: "list_all2 R (replicate m x) xs \<longleftrightarrow> length xs = m \<and> (\<forall>i < m. R x (xs ! i))"
  by (auto simp: list_all2_conv_all_nth)

lemma list_all2_replicate2[simp]: "list_all2 R xs (replicate m x) \<longleftrightarrow> length xs = m \<and> (\<forall>i < m. R (xs ! i) x)"
  by (auto simp: list_all2_conv_all_nth)

primrec tabulate :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "tabulate f x 0 = []"
| "tabulate f x (Suc n) = f x # tabulate f (Suc x) n"

lemma tabulate_alt: "tabulate f x n = map f [x ..< x + n]"
  by (induct n arbitrary: x) (auto simp: not_le Suc_le_eq upt_rec)

lemma length_tabulate[simp]: "length (tabulate f x n) = n"
  by (induction n arbitrary: x) simp_all

lemma map_tabulate[simp]: "map f (tabulate g x n) = tabulate (\<lambda>x. f (g x)) x n"
  by (induction n arbitrary: x) simp_all

lemma nth_tabulate[simp]: "k < n \<Longrightarrow> tabulate f x n ! k = f (x + k)"
proof (induction n arbitrary: x k)
  case (Suc n)
  then show ?case by (cases k) simp_all
qed simp


subsection \<open> Logic and sets \<close>

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast


subsection \<open> Finiteness and cardinality \<close>


subsection \<open> Orders \<close>

lemma drop_filter_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memR I (mt - t)) xs = drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memR I (mt - t)) xs = drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
    using Cons
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). memR I (mt - t)) xs)"
      by auto
    moreover have "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = (drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). memR I (mt - t)) xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)")
      case 0
      then show ?thesis using IH by auto
    next
      case (Suc nat)
      then have drop_IH: "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = drop nat xs"
        using filter_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR I (mt - t)) db")
        case True
        then have "(length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) = 0"
          using True mem
          by (simp add: prod.case_eq_if)
        then have "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x#xs"
          using mem
          by auto
        moreover have "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = x#xs"
          using True mem
          by auto
        ultimately show ?thesis
          by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). \<not>memR I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). \<not>memR I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(2) j_props
          by auto
        ultimately have "((\<lambda>(t, _). \<not>memR I (mt - t)) x)" using memR_antimono by auto
        then show ?thesis using mem by auto
      qed
    qed
  qed
qed

lemma take_filter_not_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
    using Cons
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)"
      by auto
    moreover have "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x#(take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)"
      by auto
    then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) (x#xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)")
      case 0
      then show ?thesis by auto
    next
      case (Suc nat)
      then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x # (take nat xs)"
        using takeWhile_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR I (mt - t)) db")
        case True
        then have "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = []"
          using filter_IH
          by (simp add: case_prod_beta')
        then show ?thesis using takeWhile_IH by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). \<not>memR I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). \<not>memR I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(2) j_props
          by auto
        ultimately have "((\<lambda>(t, _). \<not>memR I (mt - t)) x)" using memR_antimono by auto
        then show ?thesis using not_mem by auto
      qed
    qed
  qed
qed


subsection \<open> Intervals and traces \<close>

unbundle no lattice_syntax \<comment> \<open> disable notation \<close>

(*<*)
end
(*>*)