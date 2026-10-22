(*<*)
theory Preliminaries
  imports
    Interval
    Trace
    "HOL-Library.Simps_Case_Conv"
    "HOL-Library.Mapping"
    "HOL-Library.While_Combinator"
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

lemma list_all2_diag:
  assumes "\<And>i. list_all2 (\<lambda>k X. Q i k X) ks xs"
  shows "list_all2 (\<lambda>k X. Q k k X) ks xs"
proof -
  have "length ks = length xs"
    using assms by (rule list_all2_lengthD)
  with assms show ?thesis
    by (auto simp: list_all2_conv_all_nth)
qed

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

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_list_length_diff1: "xs \<noteq> [] \<Longrightarrow> [] \<notin> set xs \<Longrightarrow>
  size_list (\<lambda>xs. length xs - Suc 0) xs < size_list length xs"
proof (induct xs)
  case (Cons x xs)
  then show ?case
    by (cases xs) auto
qed simp

lemma size_list_cong: "xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> size_list f xs = size_list g ys"
  by (induct xs arbitrary: ys) auto

lemma last_filter: "xs \<noteq> [] \<Longrightarrow> P (last xs) \<Longrightarrow> filter P xs \<noteq> [] \<and> last (filter P xs) = last xs"
  by (induction xs) (auto split: if_splits)

lemma filter_imp: "(\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> length (filter P xs) \<le> length (filter Q xs)"
  by (metis (mono_tags, lifting) filter_cong filter_filter length_filter_le)

lemma filter_take_drop:
  assumes "filter P xs = take n xs"
  shows "filter (\<lambda>x. \<not> P x) xs = drop n xs"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "P a")
    case True
    with Cons.prems obtain m where "n = Suc m" "filter P xs = take m xs"
      by (cases n) auto
    with Cons.IH True show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases n)
      case 0
      with Cons.prems False have "\<forall>x\<in>set xs. \<not> P x"
        by (simp add: filter_empty_conv)
      with False 0 show ?thesis by simp
    next
      case (Suc m)
      with Cons.prems False have "filter P xs = a # take m xs" by simp
      then have "a \<in> set (filter P xs)" by simp
      with False show ?thesis by simp
    qed
  qed
qed

lemma drop_last: "length xs \<ge> 1 \<Longrightarrow> drop (length xs - 1) xs = [last xs]"
  by (cases xs rule: rev_cases) simp_all

lemma list_length_eq_split:
  assumes "list = xs @ [x] @ xs'"
  and "length list = length lista"
  shows "\<exists>ys y ys'. lista = ys @ [y] @ ys' \<and> length xs = length ys \<and> length xs' = length ys'"
proof -
  have length_eq: "length xs = length list - length xs' - 1" using assms by auto
  then have s1: "lista = take (length xs) lista @ drop (length list - length xs' - 1) lista" by auto
  have "length lista \<ge> length xs + 1" using assms by auto
  then have "drop (length list - length xs' - 1) lista \<noteq> []" using length_eq assms(2) by auto 
  then obtain b xc where xc_def: "drop (length list - length xs' - 1) lista = [b] @ xc" by (metis append_Cons append_Nil list.exhaust)
  then have "lista = take (length xs) lista @ [b] @ xc" using s1 by auto
  then obtain xb' where split_list_1: "lista = xb' @ [b] @ xc" "length xb' = length xs" "length xc = length xs'"
    using xc_def  by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 add_diff_cancel_left' assms(1) assms(2) diff_add_inverse2 diff_diff_left length_append length_drop list.size(3) length_Cons plus_1_eq_Suc)
  then show ?thesis by metis
qed

lemma list_all2_in_setE: "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<And>y. y \<in> set ys \<Longrightarrow> P x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fastforce simp: list_all2_iff set_zip in_set_conv_nth)

lemma take_takeWhile: "n \<le> length ys \<Longrightarrow>
  (\<And>y. y \<in> set (take n ys) \<Longrightarrow> P y) \<Longrightarrow>
  (\<And>y. y \<in> set (drop n ys) \<Longrightarrow> \<not>P y) \<Longrightarrow>
  take n ys = takeWhile P ys"
proof (induction ys arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases n) simp_all
qed

lemma fold_pair_fst: "fst (fold (\<lambda> a (x, y). (f1 a x, f2 a x y)) as (x, y)) = fold (\<lambda> a (x). (f1 a x)) as (x)"
proof (induction as arbitrary: rule: rev_induct)
  case (snoc a as)
  then show ?case
    by (simp add: split_beta)
qed (auto)

lemma drop_is_Cons_take: "drop n xs = y # ys \<Longrightarrow> take (Suc n) xs = take n xs @ [y]"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases n) simp_all
qed

lemma list_all_split: "list_all (\<lambda>(x, y). f x y \<and> g x y) xs \<longleftrightarrow> list_all (\<lambda>(x, y). f x y) xs \<and> list_all (\<lambda>(x, y). g x y) xs"
  by (induction xs) auto

lemma list_all2_weaken: "list_all2 f xs ys \<Longrightarrow>
  (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x y \<Longrightarrow> f' x y) \<Longrightarrow> list_all2 f' xs ys"
  by (induction xs ys rule: list_all2_induct) auto

lemma hd_le_set: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd xs \<le> x"
  by (cases xs) auto

lemma list_appendE: "xs = ys @ zs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  (x \<in> set ys \<Longrightarrow> P) \<Longrightarrow> (x \<in> set zs \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma fold_eq:
  assumes commute_f: "comp_fun_commute f"
  and comm_f: "\<And>x y. f x y = f y x"
  shows "foldl f y0 xs = fold f xs y0"
  using assms by (induction xs arbitrary: y0) auto

lemma length_fold: "length xs = fold (\<lambda> _ n. n + 1) xs 0"
  by (induction xs) (auto simp:fold_commute_apply)

lemma cmp_comm: 
  assumes commute_f: "comp_fun_commute f"
  shows "(f t1 ^^ n1 \<circ> f t2 ^^ n2) y0 = (f t2 ^^ n2 \<circ> f t1 ^^ n1) y0" 
proof(induction n1)
case 0
  then show ?case by auto
next
  case (Suc n)
  have *: "comp_fun_commute_on UNIV f" using commute_f by (simp add: comp_fun_commute_def')
  have aux1: "f t1 ((f t1 ^^ n) y0) = (f t1 ^^ n) (f t1 y0)" by (induction n) auto
  moreover have "f t1 ((f t2 ^^ n2) ((f t1 ^^ n) y0)) = (f t2 ^^ n2) ((f t1 ^^ n) (f t1 y0))" 
    using aux1 comp_fun_commute_on.fun_left_comm[OF *, of t1 t2] by(induction n2; auto; metis)
  ultimately show ?case using Suc by auto
qed

lemma fn_comm_power: "fa \<circ> tr = tr \<circ> fr \<Longrightarrow> fa ^^ n \<circ> tr = tr \<circ> fr ^^ n"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "fa ^^ Suc n \<circ> tr = fa \<circ> (fa ^^ n \<circ> tr)" by (simp only: funpow.simps(2) comp_assoc)
  also have "\<dots> = (fa \<circ> tr) \<circ> fr ^^ n" by (simp only: Suc.hyps[OF Suc.prems] comp_assoc)
  also have "\<dots> = tr \<circ> fr ^^ Suc n" by (simp only: Suc.prems funpow.simps(2) comp_assoc)
  finally show ?case .
qed

lemmas fn_comm_power' =
  ext [THEN fn_comm_power, THEN fun_cong, unfolded o_def]

lemma foldr_max_upper: "x \<in> set l \<Longrightarrow> f x \<le> foldr max (map f l) (0 :: enat)"
  by (induct l) (auto simp: le_max_iff_disj)


subsection \<open> Logic and sets \<close>

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma rtranclp_False: "(\<lambda>i j. False)\<^sup>*\<^sup>* = (=)"
proof -
  have "(\<lambda>i j. False)\<^sup>*\<^sup>* i j \<Longrightarrow> i = j" for i j :: 'a
    by (induct i j rule: rtranclp.induct) auto
  then show ?thesis
    by (auto intro: exI[of _ 0])
qed

lemma image_snd: "(a, b) \<in> X \<Longrightarrow> b \<in> snd ` X"
  by force

lemma filter_insert:
  "Set.filter p (Set.insert x X) = (if p x then Set.insert x (Set.filter p X) else (Set.filter p X))"
  by auto


subsection \<open> Finiteness and cardinality \<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

lemma ecard_image: "inj_on f A \<Longrightarrow> ecard (f ` A) = ecard A"
  unfolding ecard_def by (auto simp: card_image dest: finite_imageD)

lemma finite_fst: assumes "finite  {(x,f x) | x. P x}" shows "finite {x . P x}"
proof -
  have  fstSet: " fst ` {(x, f x) |x. P x} = {x . P x}" by (auto simp add: image_iff)
  show ?thesis using assms fstSet finite_image_iff[of fst "{(x,f x) | x. P x}"] by (auto simp add: inj_on_def)
qed


subsection \<open> Orders \<close>

lemma Max_Un_absorb:
  assumes "finite X" "X \<noteq> {}" "finite Y" "(\<And>x y. y \<in> Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<le> x)"
  shows "Max (X \<union> Y) = Max X"
proof -
  have Max_X_in_X: "Max X \<in> X"
    using Max_in[OF assms(1,2)] .
  have Max_X_in_XY: "Max X \<in> X \<union> Y"
    using Max_in[OF assms(1,2)] by auto
  have fin: "finite (X \<union> Y)"
    using assms(1,3) by auto
  have Y_le_Max_X: "\<And>y. y \<in> Y \<Longrightarrow> y \<le> Max X"
    using assms(4)[OF _ Max_X_in_X] .
  have XY_le_Max_X: "\<And>y. y \<in> X \<union> Y \<Longrightarrow> y \<le> Max X"
    using Max_ge[OF assms(1)] Y_le_Max_X by auto
  show ?thesis
    using Max_eqI[OF fin XY_le_Max_X Max_X_in_XY] by auto
qed

lemma max_cases: "(max a b = a \<Longrightarrow> P) \<Longrightarrow> (max a b = b \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis max_def)

context linorder
begin

lemma sorted_foldl_min:
  assumes "sorted (x # xs)"
  shows "foldl min x xs = (x # xs) ! 0"
  using assms by(induction xs) auto

lemma sorted_foldl_max:
  assumes "sorted (x # xs)"
  and "length (x # xs) = n"
  shows "foldl max x xs = (x # xs) ! (n - 1)"
  using assms by(induction xs arbitrary:x n) auto

end

lemma sorted_takeWhile_filter:
  assumes s: "List.sorted (map fst xs)" and m: "\<And>t t'. t \<le> t' \<Longrightarrow> Q t' \<Longrightarrow> Q t"
  shows "takeWhile (\<lambda>x. Q (fst x)) xs = filter (\<lambda>x. Q (fst x)) xs \<and>
    dropWhile (\<lambda>x. Q (fst x)) xs = filter (\<lambda>x. \<not> Q (fst x)) xs"
  using s
proof (induct xs)
  case (Cons x xs)
  have s': "List.sorted (map fst xs)" and le: "\<forall>y \<in> set xs. fst x \<le> fst y" using Cons(2) by auto
  show ?case
  proof (cases "Q (fst x)")
    case True then show ?thesis using Cons(1)[OF s'] by simp
  next
    case False
    have "\<forall>y \<in> set xs. \<not> Q (fst y)" using False le m by blast
    then show ?thesis using False by (simp add: filter_id_conv)
  qed
qed simp

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

lemma take_filter_mem:
  assumes "\<forall>db \<in> set xs. memR I (mt - fst db)"
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). mem I (mt - t)) xs = take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). mem I (mt - t)) xs = take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) xs"
    using Cons
    by auto
  from Cons(2) have x_memR: "((\<lambda>(t, _). memR I (mt - t)) x)" by auto
  show ?case
  proof (cases "(\<lambda>(t, _). mem I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). mem I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). mem I (mt - t)) xs)"
      by auto
    moreover have "take (length (filter (\<lambda>(t, _). mem I (mt - t)) (x#xs))) (x#xs) = x#(take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). mem I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). mem I (mt - t)) xs)"
      by auto
    then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). mem I (mt - t)) (x#xs))) (x#xs) = take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) (x#xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). mem I (mt - t)) xs)")
      case 0
      then show ?thesis by auto
    next
      case (Suc nat)
      then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). mem I (mt - t)) (x#xs))) (x#xs) = x # (take nat xs)"
        using takeWhile_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>mem I (mt - t)) db")
        case True
        then have "filter (\<lambda>(t, _). mem I (mt - t)) (x#xs) = []"
          using filter_IH
          by (simp add: case_prod_beta')
        then show ?thesis using takeWhile_IH by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). mem I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). mem I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(3) j_props
          by auto
        ultimately have "((\<lambda>(t, _). mem I (mt - t)) x)" using x_memR by auto
        then show ?thesis using not_mem by auto
      qed
    qed
  qed
qed

lemma dropWhile_filter:
  "sorted (map fst xs) \<Longrightarrow>
  dropWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). memR I (nt - t)) xs"
  by (induction xs) (auto 0 3 intro!: filter_id_conv[THEN iffD2, symmetric])

lemma dropWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow>
  dropWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memL I (nt - t)) xs"
  by (induction xs)
    (auto 0 3 simp: memL_mono diff_le_mono intro!: filter_id_conv[THEN iffD2, symmetric])

lemma takeWhile_filter:
  "sorted (map fst xs) \<Longrightarrow>
  takeWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memR I (nt - t)) xs"
  by (induction xs)
    (auto 0 3 simp: memR_antimono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma takeWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow>
  takeWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). memL I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memL_mono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma sorted_dropWhile_filter: "sorted xs \<Longrightarrow> dropWhile (\<lambda>t. \<not> memR I (nt - t)) xs =
  filter (\<lambda>t. memR I (nt - t)) xs"
proof (induction xs)
  case (Cons x xs)
  then show ?case
  proof (cases "\<not> memR I (nt - x)")
    case False
    then have neg: "memR I (nt - x)"
      by auto
    with Cons have "\<And>z. z \<in> set xs \<Longrightarrow> memR I (nt - z)"
      by (auto simp: diff_le_mono2)
    with False show ?thesis
      using filter_empty_conv by auto
  qed auto
qed auto


subsection \<open> Partial maps \<close>

definition "pred_mapping Q = pred_fun (\<lambda>_. True) (pred_option Q)"
definition "rel_mapping Q = rel_fun (=) (rel_option Q)"

lemma pred_mapping_alt: "pred_mapping Q P = (\<forall>p \<in> dom P. Q (the (P p)))"
  unfolding pred_mapping_def pred_fun_def option.pred_set dom_def
  by (force split: option.splits)

lemma rel_mapping_alt: "rel_mapping Q P P' = (dom P = dom P' \<and> (\<forall>p \<in> dom P. Q (the (P p)) (the (P' p))))"
  unfolding rel_mapping_def rel_fun_def rel_option_iff dom_def
  by (force split: option.splits)

lemma rel_mapping_reflp: "reflp Q \<Longrightarrow> rel_mapping Q P P"
  by (auto simp: rel_mapping_alt reflp_def)

lemma rel_mapping_map_upd[simp]: "Q x y \<Longrightarrow> rel_mapping Q P P' \<Longrightarrow> rel_mapping Q (P(p \<mapsto> x)) (P'(p \<mapsto> y))"
  by (auto simp: rel_mapping_alt)

lemma rel_mapping_order_refl: "rel_mapping (\<le>) (x::'a \<rightharpoonup> 'b::order) x"
  by (intro rel_mapping_reflp reflpI order_refl)

lemma rel_mapping_le_map_upd[simp]: "(x::'a::order) \<le> y \<Longrightarrow> rel_mapping (\<le>) (P(p \<mapsto> x)) (P(p \<mapsto> y))"
  by (simp add: rel_mapping_order_refl)

lemma pred_mapping_map_upd[simp]: "Q x \<Longrightarrow> pred_mapping Q P \<Longrightarrow> pred_mapping Q (P(p \<mapsto> x))"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_fun_upd[simp]: "(case x of Some x \<Rightarrow> Q x | _ \<Rightarrow> True) \<Longrightarrow> pred_mapping Q P \<Longrightarrow> pred_mapping Q (P(p := x))"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_empty[simp]: "pred_mapping Q Map.empty"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_mono: "pred_mapping Q P \<Longrightarrow> Q \<le> R \<Longrightarrow> pred_mapping R P"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_mono_strong: "pred_mapping Q P \<Longrightarrow>
  (\<And>p. p \<in> dom P \<Longrightarrow> Q (the (P p)) \<Longrightarrow> R (the (P p))) \<Longrightarrow> pred_mapping R P"
  by (auto simp: pred_mapping_alt)

abbreviation range_mapping :: "nat \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> nat option) \<Rightarrow> bool" where
  "range_mapping i j P \<equiv> pred_mapping (\<lambda>x. i \<le> x \<and> x \<le> j) P"

lemma range_mapping_relax:
  "range_mapping i j P \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<ge> j \<Longrightarrow> range_mapping i' j' P"
  by (auto simp: pred_mapping_alt dom_def set_eq_iff split: option.splits)

lemma pred_mapping_le:
  "pred_mapping ((\<le>) i) P1 \<Longrightarrow> rel_mapping (\<le>) P1 P2 
  \<Longrightarrow> pred_mapping ((\<le>) (i :: nat)) P2"
  by (force simp: rel_mapping_alt pred_mapping_alt dom_def set_eq_iff)

lemma range_mapping_to_pred_mapping: "range_mapping a j P \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P"
  by(auto simp add: pred_mapping_alt)

definition max_mapping :: "('b \<Rightarrow> 'a option) \<Rightarrow> ('b \<Rightarrow> 'a option) \<Rightarrow> 'b \<Rightarrow> ('a :: linorder) option" 
  where "max_mapping P P' x = (case (P x, P' x) of
    (None, None) \<Rightarrow> None
  | (Some x, None) \<Rightarrow> None
  | (None, Some x) \<Rightarrow> None
  | (Some x, Some y) \<Rightarrow> Some (max x y))"

definition Max_mapping :: "('b \<Rightarrow> 'a option) set \<Rightarrow> 'b \<Rightarrow> ('a :: linorder) option" where
  "Max_mapping Ps x = (if (\<forall>P \<in> Ps. P x \<noteq> None) then Some (Max ((\<lambda>P. the (P x)) ` Ps)) else None)"

lemma dom_max_mapping[simp]: "dom (max_mapping P1 P2) = dom P1 \<inter> dom P2"
  unfolding max_mapping_def by (auto split: option.splits)

lemma dom_Max_mapping[simp]: "dom (Max_mapping X) = (\<Inter>P \<in> X. dom P)"
  unfolding Max_mapping_def by (auto split: if_splits)

lemma Max_mapping_coboundedI:
  assumes "finite X" "\<forall>Q \<in> X. dom Q = dom P" "P \<in> X"
  shows "rel_mapping (\<le>) P (Max_mapping X)"
  unfolding rel_mapping_alt
proof (intro conjI ballI)
  from assms(3) have "X \<noteq> {}" by auto
  then show "dom P = dom (Max_mapping X)" using assms(2) by auto
next
  fix p
  assume "p \<in> dom P"
  with assms show "the (P p) \<le> the (Max_mapping X p)"
    by (force simp add: Max_mapping_def intro!: Max.coboundedI imageI)
qed

lemma range_mapping_max_mapping[simp]:
  "range_mapping i j1 P1 \<Longrightarrow> range_mapping i j2 P2 
  \<Longrightarrow> range_mapping i (max j1 j2) (max_mapping P1 P2)"
  by (auto simp: pred_mapping_alt dom_def set_eq_iff max_mapping_def split: option.splits)

lemma range_mapping_Max_mapping[simp]:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<forall>x\<in>X. range_mapping i (j x) (P x) 
  \<Longrightarrow> range_mapping i (Max (j ` X)) (Max_mapping (P ` X))"
  by (force simp: pred_mapping_alt Max_mapping_def dom_def image_iff
      intro!: Max_ge_iff[THEN iffD2] split: if_splits)

lemma max_mapping_cobounded1: "dom P1 \<subseteq> dom P2 \<Longrightarrow> rel_mapping (\<le>) P1 (max_mapping P1 P2)"
  unfolding max_mapping_def rel_mapping_alt by (auto simp: dom_def split: option.splits)

lemma max_mapping_cobounded2: "dom P2 \<subseteq> dom P1 \<Longrightarrow> rel_mapping (\<le>) P2 (max_mapping P1 P2)"
  unfolding max_mapping_def rel_mapping_alt by (auto simp: dom_def split: option.splits)

lemma max_mapping_fun_upd2[simp]:
  "(max_mapping P1 (P2(p := y)))(p \<mapsto> x) = (max_mapping P1 P2)(p \<mapsto> x)"
  by (auto simp: max_mapping_def)

lemma rel_mapping_max_mapping_fun_upd: "dom P2 \<subseteq> dom P1 \<Longrightarrow> p \<in> dom P2 \<Longrightarrow> the (P2 p) \<le> y 
  \<Longrightarrow> rel_mapping (\<le>) P2 ((max_mapping P1 P2)(p \<mapsto> y))"
  by (auto simp: rel_mapping_alt max_mapping_def split: option.splits)

lemma pred_mapping_max_mapping:
  "pred_mapping (\<lambda>x. x\<le>j1) P1 \<Longrightarrow> pred_mapping (\<lambda>x. x\<le>j2) P2 
  \<Longrightarrow> pred_mapping (\<lambda>x. x\<le>(max j1 j2)) (max_mapping P1 P2)"
proof -
  assume P1: "pred_mapping (\<lambda>x. x\<le>j1) P1" and P2: "pred_mapping (\<lambda>x. x\<le>j2) P2"
  show "pred_mapping (\<lambda>x. x\<le>(max j1 j2)) (max_mapping P1 P2)"
    unfolding pred_mapping_alt
  proof
    fix p assume "p \<in> dom (max_mapping P1 P2)"
    then obtain x y where xy: "P1 p = Some x" "P2 p = Some y"
      by auto
    with P1 P2 have "x \<le> j1" "y \<le> j2"
      by (force simp: pred_mapping_alt)+
    moreover from xy have "max_mapping P1 P2 p = Some (max x y)"
      by (simp add: max_mapping_def)
    ultimately show "the (max_mapping P1 P2 p) \<le> max j1 j2"
      by (metis max.mono option.sel)
  qed
qed


subsection \<open> Intervals and traces \<close>

unbundle no lattice_syntax \<comment> \<open> disable notation \<close>

text \<open>The largest time difference in a bounded interval: one less than the first one outside it.
  A past operator at @{term i} looks at time points @{term k} with @{term "\<tau> \<sigma> i - \<tau> \<sigma> k"} at most
  this far.\<close>

definition ivl_ub :: "\<I> \<Rightarrow> enat" where
  "ivl_ub I = (if bounded I then enat ((LEAST t. \<not> memR I t) - 1) else \<infinity>)"

lemma memR_le_ivl_ub: "memR I t \<Longrightarrow> enat t \<le> ivl_ub I"
proof (cases "bounded I")
  case True
  then obtain m where m: "\<not> memR I m"
    by (auto simp: bounded_memR)
  assume t: "memR I t"
  have "\<not> memR I (LEAST t. \<not> memR I t)"
    using m by (rule LeastI)
  then have "t < (LEAST t. \<not> memR I t)"
    using t memR_antimono by (metis not_less)
  then show ?thesis
    using True by (simp add: ivl_ub_def)
qed (simp add: ivl_ub_def)

text \<open>The upper bound is computed by searching for the first time difference outside the
  interval; the search is linear in the bound, and runs once per operator at initialisation.\<close>

lemma while_option_Suc_Least:
  assumes "\<not> P m" "\<forall>t<k. P t" "k \<le> m"
  shows "while_option P Suc k = Some (LEAST t. \<not> P t)"
  using assms(2,3)
proof (induction "m - k" arbitrary: k)
  case 0
  then have "k = m"
    by simp
  with assms(1) 0(2) show ?case
    by (subst while_option_unfold) (auto intro!: Least_equality[symmetric] simp: not_less[symmetric])
next
  case (Suc x)
  show ?case
  proof (cases "P k")
    case True
    have "while_option P Suc (Suc k) = Some (LEAST t. \<not> P t)"
      by (rule Suc.hyps(1)) (use Suc.hyps(2) Suc.prems True in \<open>auto simp: less_Suc_eq\<close>)
    with True show ?thesis
      by (subst while_option_unfold) simp
  next
    case False
    with Suc.prems(1) show ?thesis
      by (subst while_option_unfold) (auto intro!: Least_equality[symmetric] simp: not_less[symmetric])
  qed
qed

lemma ivl_ub_code[code]:
  "ivl_ub I = (if bounded I then enat (the (while_option (memR I) Suc 0) - 1) else \<infinity>)"
proof (cases "bounded I")
  case True
  then obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then have "while_option (memR I) Suc 0 = Some (LEAST t. \<not> memR I t)"
    by (rule while_option_Suc_Least) simp_all
  with True show ?thesis
    by (simp add: ivl_ub_def)
qed (simp add: ivl_ub_def)

lemma interval_geq:
  fixes i j :: nat
  assumes "memL I a"
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
  assumes "j \<le> k"
  assumes "a \<le> (\<tau> \<sigma> i - \<tau> \<sigma> k)"
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  from assms(3) assms(4) have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" by auto
  then have "(\<tau> \<sigma> i - \<tau> \<sigma> j) \<ge> (\<tau> \<sigma> i - \<tau> \<sigma> k)" by linarith
  then have "memR I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    using assms(1) assms(2) assms(4)
    by auto
  thus ?thesis by auto
qed

lemma interval_leq:
  fixes i j :: nat
  assumes "memL I a"
  assumes "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  assumes "k \<le> j"
  assumes "a \<le> (\<tau> \<sigma> k - \<tau> \<sigma> i)"
  shows "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
proof -
  from assms(3) assms(4) have "\<tau> \<sigma> j \<ge> \<tau> \<sigma> k" by auto
  then have "(\<tau> \<sigma> j - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> k - \<tau> \<sigma> i)" by linarith
  with assms(1) assms(2) assms(4) have "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> memL I (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
  thus ?thesis by auto
qed

lemma tau_win:
  assumes "j \<le> k"
  shows "enat (\<tau> \<sigma> i) \<le> enat (\<tau> \<sigma> k) + enat (\<tau> \<sigma> i - \<tau> \<sigma> j)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k"
    using assms by simp
  then have "\<tau> \<sigma> i \<le> \<tau> \<sigma> k + (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    by arith
  then show ?thesis
    by simp
qed

(*<*)
end
(*>*)